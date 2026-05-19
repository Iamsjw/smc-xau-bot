"""
SMC + XAUUSD Trading Bot v4
============================
Candle data : Twelve Data API (OHLC, free 800/day)
Volume proxy: candle range + body strength (no free API gives real gold volume)
Trade exec  : Deriv WebSocket → MT5 STD Demo (0.01 lots)
Timeframe   : 1 minute

Railway Variables required:
  DERIV_API_TOKEN  → place trades on your MT5 demo
  MT5_LOGIN        → your Deriv MT5 login number
  TWELVE_DATA_KEY  → candle data from twelvedata.com
"""

import json, time, threading, logging, os
import requests
from datetime import datetime, timezone, timedelta
from collections import deque

import pandas as pd
import numpy as np
import websocket
from flask import Flask, jsonify

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s [%(levelname)s] %(message)s",
                    datefmt="%H:%M:%S")
log = logging.getLogger(__name__)

# ══════════════════════════════════════════════════════════════
#  CREDENTIALS
# ══════════════════════════════════════════════════════════════
DERIV_TOKEN  = os.environ.get("DERIV_API_TOKEN", "")
MT5_LOGIN    = os.environ.get("MT5_LOGIN", "")
TD_KEY       = os.environ.get("TWELVE_DATA_KEY", "")
DERIV_APP_ID = "1089"
DERIV_WS     = f"wss://ws.binaryws.com/websockets/v3?app_id={DERIV_APP_ID}"
TD_BASE      = "https://api.twelvedata.com"
IST          = timezone(timedelta(hours=5, minutes=30))

# ══════════════════════════════════════════════════════════════
#  CONFIG
# ══════════════════════════════════════════════════════════════
CFG = {
    # EMA — matches your Pine Script
    "fast_ema"        : 14,
    "slow_ema"        : 140,
    "htf_ema"         : 50,

    # Risk
    "atr_len"         : 14,
    "sl_atr_mult"     : 2.0,
    "rr_ratio"        : 3.0,

    # Structure
    "swing_len"       : 3,
    "choch_window"    : 5,
    "sweep_window"    : 10,

    # Volume proxy settings
    # Since no free API gives real gold volume, we use:
    # range proxy  = candle (high-low) > N-bar average × multiplier
    # body proxy   = candle body > N-bar avg body × body_mult
    # BOTH must pass for volume to be "high"
    "use_volume"      : True,
    "vol_lookback"    : 20,       # bars for rolling average
    "range_mult"      : 1.1,      # range must be 1.1x average
    "body_mult"       : 1.0,      # body must be 1.0x average (at least avg)

    # Other filters
    "use_htf_bias"    : True,
    "use_local_trend" : True,
    "use_engulf"      : True,

    # Trade
    "mt5_symbol"      : "XAUUSD",
    "lot_size"        : 0.01,

    # Data
    "td_symbol"       : "XAU/USD",
    "candle_limit"    : 300,
    "htf_limit"       : 100,
    "check_every_sec" : 60,
}

# ══════════════════════════════════════════════════════════════
#  STATE
# ══════════════════════════════════════════════════════════════
candles_1m   = deque(maxlen=CFG["candle_limit"])
candles_1h   = deque(maxlen=CFG["htf_limit"])
trade_active = False
api_calls    = {"count": 0, "reset_date": None}
bot_status   = {
    "running"    : False,
    "last_check" : "—",
    "last_signal": "—",
    "kill_zone"  : "—",
    "candles_1m" : 0,
    "error"      : "—",
    "api_calls"  : "0/800",
    "volume_info": "—",
}
st = {
    "bull_sweep_bar": -999, "bear_sweep_bar": -999,
    "bull_choch_bar": -999, "bear_choch_bar": -999,
    "asian_high": None,     "asian_low": None,
    "last_sh": None,        "last_sl": None,
}

# ══════════════════════════════════════════════════════════════
#  TIME HELPERS
# ══════════════════════════════════════════════════════════════
def ist_now(): return datetime.now(IST)

def is_kz():
    t = ist_now().hour * 100 + ist_now().minute
    return (1230 <= t <= 1530) or (1730 <= t <= 2030)

def kz_name():
    t = ist_now().hour * 100 + ist_now().minute
    if 1230 <= t <= 1530: return "🟡 London  12:30–15:30 IST"
    if 1730 <= t <= 2030: return "🔵 NY      17:30–20:30 IST"
    return "⚫ Outside kill zone"

def track_call():
    today = ist_now().date()
    if api_calls["reset_date"] != today:
        api_calls["count"]      = 0
        api_calls["reset_date"] = today
    api_calls["count"] += 1
    bot_status["api_calls"] = f"{api_calls['count']}/800"

def to_df(q):
    df = pd.DataFrame(list(q))
    if df.empty: return df
    df = df.rename(columns={"o":"open","h":"high","l":"low","c":"close","v":"volume"})
    for col in ["open","high","low","close","volume"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    return df.reset_index(drop=True)

# ══════════════════════════════════════════════════════════════
#  INDICATORS
# ══════════════════════════════════════════════════════════════
def ema(s, p): return s.ewm(span=p, adjust=False).mean()

def calc_atr(df, p):
    h, l, pc = df["high"], df["low"], df["close"].shift(1)
    return pd.concat(
        [h-l, (h-pc).abs(), (l-pc).abs()], axis=1
    ).max(axis=1).ewm(span=p, adjust=False).mean()

def pvt_h(s, n):
    v, r = s.values, np.nan
    for i in range(n, len(v)-n):
        if (all(v[i] >= v[i-j] for j in range(1, n+1)) and
                all(v[i] >= v[i+j] for j in range(1, n+1))):
            r = v[i]
    return r

def pvt_l(s, n):
    v, r = s.values, np.nan
    for i in range(n, len(v)-n):
        if (all(v[i] <= v[i-j] for j in range(1, n+1)) and
                all(v[i] <= v[i+j] for j in range(1, n+1))):
            r = v[i]
    return r

# ══════════════════════════════════════════════════════════════
#  VOLUME PROXY — works without real volume data
#
#  For XAUUSD (OTC market), no free API provides real volume.
#  We use two candle-based proxies that professional algo
#  traders use for gold:
#
#  1. Range proxy  → wide candle = high market activity
#  2. Body proxy   → strong body = directional conviction
#
#  Both must be above their rolling averages for "high volume"
# ══════════════════════════════════════════════════════════════
def check_volume(df):
    lb = CFG["vol_lookback"]

    # Candle range (high - low)
    candle_range = df["high"] - df["low"]
    avg_range    = candle_range.rolling(lb).mean()
    cur_range    = float(candle_range.iloc[-1])
    av_range     = float(avg_range.iloc[-1]) if not pd.isna(avg_range.iloc[-1]) else cur_range

    # Candle body (abs close - open)
    candle_body  = (df["close"] - df["open"]).abs()
    avg_body     = candle_body.rolling(lb).mean()
    cur_body     = float(candle_body.iloc[-1])
    av_body      = float(avg_body.iloc[-1]) if not pd.isna(avg_body.iloc[-1]) else cur_body

    range_ok = cur_range > av_range * CFG["range_mult"]
    body_ok  = cur_body  > av_body  * CFG["body_mult"]
    high_vol = range_ok and body_ok

    info = (f"range={cur_range:.2f}(avg {av_range:.2f}) {'✅' if range_ok else '❌'} | "
            f"body={cur_body:.2f}(avg {av_body:.2f}) {'✅' if body_ok else '❌'} | "
            f"vol={'HIGH ✅' if high_vol else 'LOW ❌'}")
    log.info(f"📊 {info}")
    bot_status["volume_info"] = info
    return high_vol

# ══════════════════════════════════════════════════════════════
#  TWELVE DATA — FETCH CANDLES
# ══════════════════════════════════════════════════════════════
def td_fetch(interval, outputsize, target_deque):
    if not TD_KEY:
        log.warning("⚠️  TWELVE_DATA_KEY not set"); return

    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : interval,
        "outputsize": outputsize,
        "apikey"    : TD_KEY,
        "order"     : "ASC",
    }
    try:
        track_call()
        resp = requests.get(f"{TD_BASE}/time_series", params=params, timeout=10)
        data = resp.json()

        if data.get("status") == "error":
            log.error(f"Twelve Data: {data.get('message')}"); return

        values = data.get("values", [])
        if not values:
            log.warning("Twelve Data: no values returned"); return

        target_deque.clear()
        for bar in values:
            target_deque.append({
                "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
                "o"    : float(bar["open"]),
                "h"    : float(bar["high"]),
                "l"    : float(bar["low"]),
                "c"    : float(bar["close"]),
                "v"    : 0.0,  # not used — volume proxy used instead
            })
        log.info(f"📊 Twelve Data: {len(target_deque)} {interval} candles loaded")

    except Exception as e:
        log.error(f"Twelve Data fetch error: {e}")


def td_fetch_latest():
    if not TD_KEY: return
    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : "1min",
        "outputsize": 2,
        "apikey"    : TD_KEY,
        "order"     : "ASC",
    }
    try:
        track_call()
        resp   = requests.get(f"{TD_BASE}/time_series", params=params, timeout=10)
        values = resp.json().get("values", [])
        if not values: return

        bar = values[-2] if len(values) >= 2 else values[-1]
        candle = {
            "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
            "o"    : float(bar["open"]),
            "h"    : float(bar["high"]),
            "l"    : float(bar["low"]),
            "c"    : float(bar["close"]),
            "v"    : 0.0,
        }
        if not candles_1m or candles_1m[-1]["epoch"] != candle["epoch"]:
            candles_1m.append(candle)
            log.info(f"🕐 1m | close={candle['c']:.2f} "
                     f"range={candle['h']-candle['l']:.2f}")

    except Exception as e:
        log.error(f"Latest candle error: {e}")

# ══════════════════════════════════════════════════════════════
#  STRATEGY
# ══════════════════════════════════════════════════════════════
def run_strategy():
    global trade_active
    df = to_df(candles_1m)
    if len(df) < CFG["slow_ema"] + 20:
        log.info(f"⏳ Warming up: {len(df)}/{CFG['slow_ema']+20}"); return None

    df1h = to_df(candles_1h)
    i    = len(df) - 1

    # EMAs
    fast_v = float(ema(df["close"], CFG["fast_ema"]).iloc[-1])
    slow_v = float(ema(df["close"], CFG["slow_ema"]).iloc[-1])
    bull_t = fast_v > slow_v

    # HTF bias
    bull_b = bear_b = True
    if CFG["use_htf_bias"] and len(df1h) >= CFG["htf_ema"]:
        hv     = float(ema(df1h["close"], CFG["htf_ema"]).iloc[-1])
        cc     = float(df["close"].iloc[-1])
        bull_b = cc > hv
        bear_b = cc < hv

    # ATR
    atr_v = float(calc_atr(df, CFG["atr_len"]).iloc[-1])

    # Volume proxy
    high_v = check_volume(df) if CFG["use_volume"] else True

    # PDH / PDL
    n   = len(df)
    pdh = float(df["high"].iloc[-1440:-720].max()) if n >= 1440 \
          else float(df["high"].iloc[:max(1, n//2)].max())
    pdl = float(df["low"].iloc[-1440:-720].min())  if n >= 1440 \
          else float(df["low"].iloc[:max(1, n//2)].min())

    # Swing H/L
    sw  = CFG["swing_len"]
    lsh = pvt_h(df["high"], sw) if len(df) >= sw*2+5 else st["last_sh"]
    lsl = pvt_l(df["low"],  sw) if len(df) >= sw*2+5 else st["last_sl"]
    st["last_sh"] = lsh; st["last_sl"] = lsl

    c, o = float(df["close"].iloc[-1]), float(df["open"].iloc[-1])
    h, l = float(df["high"].iloc[-1]),  float(df["low"].iloc[-1])
    ph   = float(df["high"].iloc[-2])
    pl   = float(df["low"].iloc[-2])
    po   = float(df["open"].iloc[-2])
    pc   = float(df["close"].iloc[-2])

    # Sweeps
    sb = be = False
    if st["asian_low"]  and l < st["asian_low"]:  sb = True
    if st["asian_high"] and h > st["asian_high"]: be = True
    if l < pdl: sb = True
    if h > pdh: be = True
    if lsl and not np.isnan(lsl) and l < lsl and c > lsl: sb = True
    if lsh and not np.isnan(lsh) and h > lsh and c < lsh: be = True

    if sb: st["bull_sweep_bar"] = i; log.info("🔍 Bull sweep")
    if be: st["bear_sweep_bar"] = i; log.info("🔍 Bear sweep")

    rbs = (i - st["bull_sweep_bar"]) <= CFG["sweep_window"]
    rbe = (i - st["bear_sweep_bar"]) <= CFG["sweep_window"]

    # CHoCH
    bc  = rbe and c > ph and c > o
    brc = rbs and c < pl and c < o
    if bc:  st["bull_choch_bar"] = i; log.info("🔄 Bull CHoCH")
    if brc: st["bear_choch_bar"] = i; log.info("🔄 Bear CHoCH")

    rbc  = (i - st["bull_choch_bar"]) <= CFG["choch_window"]
    rbrc = (i - st["bear_choch_bar"]) <= CFG["choch_window"]

    # Engulfing
    body = abs(c-o); rng = h-l
    be_l = c > o and c > po and o < pc and body > rng * 0.5
    be_s = c < o and c < po and o > pc and body > rng * 0.5

    # Apply toggleable filters
    htfl = bull_b  if CFG["use_htf_bias"]    else True
    htfs = bear_b  if CFG["use_htf_bias"]    else True
    trl  = bull_t  if CFG["use_local_trend"] else True
    trs  = (not bull_t) if CFG["use_local_trend"] else True
    el   = be_l    if CFG["use_engulf"]      else True
    es   = be_s    if CFG["use_engulf"]      else True
    vok  = high_v  if CFG["use_volume"]      else True

    long_ok  = htfl and trl and vok and rbs and rbc  and el  and not trade_active
    short_ok = htfs and trs and vok and rbe and rbrc and es  and not trade_active

    log.info(
        f"⏳ htf:{'B✅' if bull_b else 'b❌'} "
        f"trend:{'B✅' if bull_t else 'b❌'} "
        f"vol:{'✅' if vok else '❌'} "
        f"bs:{'✅' if rbs else '❌'} "
        f"be:{'✅' if rbe else '❌'} "
        f"bc:{'✅' if rbc else '❌'} "
        f"brc:{'✅' if rbrc else '❌'} "
        f"el:{'✅' if be_l else '❌'} "
        f"es:{'✅' if be_s else '❌'}"
    )

    if long_ok:
        sl = l - atr_v * CFG["sl_atr_mult"]
        tp = c + abs(c-sl) * CFG["rr_ratio"]
        log.info(f"🚀 LONG entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f} atr:{atr_v:.2f}")
        return {"action":"BUY", "entry":c, "sl":sl, "tp":tp}

    if short_ok:
        sl = h + atr_v * CFG["sl_atr_mult"]
        tp = c - abs(sl-c) * CFG["rr_ratio"]
        log.info(f"🔻 SHORT entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f} atr:{atr_v:.2f}")
        return {"action":"SELL", "entry":c, "sl":sl, "tp":tp}

    return None

# ══════════════════════════════════════════════════════════════
#  PLACE TRADE — Deriv → MT5 STD Demo
# ══════════════════════════════════════════════════════════════
def place_trade(signal):
    global trade_active
    result = {}; done = threading.Event()
    otype  = 0 if signal["action"] == "BUY" else 1

    def on_open(ws):
        ws.send(json.dumps({"authorize": DERIV_TOKEN}))

    def on_message(ws, msg):
        global trade_active
        d = json.loads(msg); mt = d.get("msg_type")

        if mt == "authorize":
            if "error" in d:
                log.error(f"Auth: {d['error']['message']}")
                result["status"] = "auth_error"
                ws.close(); done.set(); return

            ws.send(json.dumps({
                "mt5_new_order": 1,
                "login"        : int(MT5_LOGIN),
                "symbol"       : CFG["mt5_symbol"],
                "volume"       : CFG["lot_size"],
                "order_type"   : otype,
                "price"        : signal["entry"],
                "stop_loss"    : round(signal["sl"], 2),
                "take_profit"  : round(signal["tp"], 2),
                "comment"      : "SMC+XAU v4",
            }))
            log.info(f"📤 {signal['action']} 0.01 lots | "
                     f"entry:{signal['entry']:.2f} "
                     f"sl:{signal['sl']:.2f} tp:{signal['tp']:.2f}")

        elif mt == "mt5_new_order":
            if "error" in d:
                log.error(f"MT5: {d['error']['message']}")
                result["status"] = "error"
                result["detail"] = d["error"]["message"]
            else:
                oid = d.get("mt5_new_order", {}).get("order", "—")
                log.info(f"✅ Trade placed! Order:{oid}")
                result["status"] = "placed"
                result["order"]  = oid
                trade_active     = True
                bot_status["last_signal"] = (
                    f"{signal['action']} @ {signal['entry']:.2f} | "
                    f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} | "
                    f"0.01 lots [{ist_now().strftime('%H:%M IST')}]"
                )
            ws.close(); done.set()

        elif mt == "error":
            result["status"] = "ws_error"
            ws.close(); done.set()

    def on_error(ws, e):
        result["status"] = "ws_error"; done.set()

    ws = websocket.WebSocketApp(
        DERIV_WS, on_open=on_open,
        on_message=on_message, on_error=on_error
    )
    threading.Thread(target=ws.run_forever, daemon=True).start()
    done.wait(20)
    return result

# ══════════════════════════════════════════════════════════════
#  BOT LOOP
# ══════════════════════════════════════════════════════════════
def bot_loop():
    log.info("🤖 SMC+XAU Bot v4 starting...")
    log.info(f"Twelve Data : {'✅' if TD_KEY else '❌ Add TWELVE_DATA_KEY'}")
    log.info(f"Deriv token : {'✅' if DERIV_TOKEN else '❌ Add DERIV_API_TOKEN'}")
    log.info(f"MT5 login   : {MT5_LOGIN or '❌ Add MT5_LOGIN'}")

    # Initial load — 2 API calls
    td_fetch("1min", CFG["candle_limit"], candles_1m)
    td_fetch("1h",   CFG["htf_limit"],    candles_1h)

    bot_status["running"]    = True
    bot_status["candles_1m"] = len(candles_1m)
    log.info(f"✅ Ready | {len(candles_1m)} × 1m | {len(candles_1h)} × 1H")

    while True:
        try:
            td_fetch_latest()
            bot_status["candles_1m"] = len(candles_1m)

            now = ist_now(); kz = kz_name()
            bot_status["kill_zone"]  = kz
            bot_status["last_check"] = now.strftime("%H:%M:%S IST")

            log.info(f"\n{'='*55}")
            log.info(f"⏰ {now.strftime('%H:%M IST')} | {kz} | "
                     f"calls={api_calls.get('count',0)}/800")

            if not is_kz():
                log.info("💤 Outside kill zone")
                time.sleep(CFG["check_every_sec"])
                continue

            sig = run_strategy()

            if sig:
                if DERIV_TOKEN and MT5_LOGIN:
                    log.info(f"🎯 {sig['action']} — placing trade...")
                    res = place_trade(sig)
                    log.info(f"📋 {res}")
                    bot_status["error"] = str(res.get("detail", "—"))
                else:
                    missing = []
                    if not DERIV_TOKEN: missing.append("DERIV_API_TOKEN")
                    if not MT5_LOGIN:   missing.append("MT5_LOGIN")
                    log.info(f"🎯 DRY RUN {sig['action']} @ {sig['entry']:.2f} "
                             f"[Missing: {', '.join(missing)}]")
                    bot_status["last_signal"] = (
                        f"DRY {sig['action']} @ {sig['entry']:.2f}"
                    )

            # Refresh 1H candles at top of every hour
            if now.minute == 0:
                td_fetch("1h", CFG["htf_limit"], candles_1h)
                log.info("🔄 1H candles refreshed")

        except Exception as e:
            log.error(f"❌ {e}", exc_info=True)
            bot_status["error"] = str(e)

        time.sleep(CFG["check_every_sec"])

# ══════════════════════════════════════════════════════════════
#  FLASK STATUS PAGE
# ══════════════════════════════════════════════════════════════
flask_app = Flask(__name__)

@flask_app.route("/")
def status():
    rows = [
        ("Status",       "✅ Running" if bot_status["running"] else "⏳ Starting", "#3fb950"),
        ("IST Time",     ist_now().strftime("%H:%M:%S"),                           "#e3b341"),
        ("Kill Zone",    kz_name(),                                                "#e6edf3"),
        ("Last Check",   bot_status["last_check"],                                 "#e6edf3"),
        ("1m Candles",   str(bot_status["candles_1m"]),                            "#e6edf3"),
        ("API Calls",    bot_status["api_calls"],                                  "#e3b341"),
        ("Volume",       bot_status["volume_info"],                                "#e6edf3"),
        ("Last Signal",  bot_status["last_signal"],                                "#58a6ff"),
        ("Trade Active", "🔴 YES" if trade_active else "⚪ No",                   "#e6edf3"),
        ("Twelve Data",  "✅ Set" if TD_KEY      else "❌ Add TWELVE_DATA_KEY",    "#e6edf3"),
        ("Deriv Token",  "✅ Set" if DERIV_TOKEN else "❌ Add DERIV_API_TOKEN",    "#e6edf3"),
        ("MT5 Login",    MT5_LOGIN or "❌ Add MT5_LOGIN",                          "#e6edf3"),
        ("Last Error",   bot_status["error"],                                      "#f85149"),
    ]

    rows_html = "".join(
        f'<tr>'
        f'<td style="padding:7px 12px;color:#8b949e;'
        f'border-bottom:1px solid #21262d;white-space:nowrap">{lbl}</td>'
        f'<td style="padding:7px 12px;color:{col};'
        f'border-bottom:1px solid #21262d;word-break:break-all">{val}</td>'
        f'</tr>'
        for lbl, val, col in rows
    )

    return f"""<html>
    <head><meta http-equiv="refresh" content="30"><title>SMC Bot v4</title></head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;
                 padding:30px;max-width:700px">
    <h2 style="color:#58a6ff">🤖 SMC+XAUUSD Bot v4</h2>
    <p style="color:#484f58;margin-top:-12px">
      0.01 lots · Deriv MT5 STD Demo · 1m · Volume proxy
    </p>
    <table style="border-collapse:collapse;width:100%">{rows_html}</table>
    <br>
    <p style="color:#484f58;font-size:12px;line-height:1.9">
      🟡 London kill zone: 12:30–15:30 IST<br>
      🔵 NY kill zone: 17:30–20:30 IST<br>
      Volume proxy: range × body (no free API gives real gold volume)<br>
      Page auto-refreshes every 30s
    </p>
    </body></html>""", 200

@flask_app.route("/api/status")
def api_s():
    return jsonify({
        **bot_status,
        "kz"         : is_kz(),
        "ist"        : ist_now().strftime("%H:%M:%S"),
        "trade_active": trade_active,
    })

# ══════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    threading.Thread(target=bot_loop, daemon=True).start()
    port = int(os.environ.get("PORT", 5000))
    log.info(f"🌐 Flask on port {port}")
    flask_app.run(host="0.0.0.0", port=port, use_reloader=False)

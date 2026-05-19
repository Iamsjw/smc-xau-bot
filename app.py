"""
SMC + XAUUSD Trading Bot v3
============================
Candle data : Twelve Data API (real tick volume, free 800/day)
Trade exec  : Deriv WebSocket → MT5 STD Demo (0.01 lots)
Timeframe   : 1 minute
Server      : Railway free tier

Railway Environment Variables needed:
  DERIV_API_TOKEN  = your Deriv API token
  MT5_LOGIN        = your Deriv MT5 login number
  TWELVE_DATA_KEY  = your Twelve Data API key (twelvedata.com)
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
DERIV_TOKEN   = os.environ.get("DERIV_API_TOKEN", "")
MT5_LOGIN     = os.environ.get("MT5_LOGIN", "")
TD_KEY        = os.environ.get("TWELVE_DATA_KEY", "")   # Twelve Data API key
DERIV_APP_ID  = "1089"
DERIV_WS      = f"wss://ws.binaryws.com/websockets/v3?app_id={DERIV_APP_ID}"
TD_BASE       = "https://api.twelvedata.com"
IST           = timezone(timedelta(hours=5, minutes=30))

# ══════════════════════════════════════════════════════════════
#  CONFIG — matches Pine Script inputs exactly
# ══════════════════════════════════════════════════════════════
CFG = {
    "fast_ema"       : 14,
    "slow_ema"       : 140,
    "htf_ema"        : 50,
    "atr_len"        : 14,
    "sl_atr_mult"    : 2.0,
    "rr_ratio"       : 3.0,
    "swing_len"      : 3,
    "choch_window"   : 5,
    "sweep_window"   : 10,
    "use_volume"     : True,
    "vol_mult"       : 1.1,
    "use_htf_bias"   : True,
    "use_local_trend": True,
    "use_engulf"     : True,
    "mt5_symbol"     : "XAUUSD",
    "lot_size"       : 0.01,
    "td_symbol"      : "XAU/USD",   # Twelve Data symbol for gold
    "candle_limit"   : 300,
    "htf_limit"      : 100,
    "check_every_sec": 60,
}

# ══════════════════════════════════════════════════════════════
#  STATE
# ══════════════════════════════════════════════════════════════
candles_1m   = deque(maxlen=CFG["candle_limit"])
candles_1h   = deque(maxlen=CFG["htf_limit"])
trade_active = False
api_calls    = {"count": 0, "reset_date": datetime.now(IST).date()}
bot_status   = {
    "running"    : False,
    "last_check" : "—",
    "last_signal": "—",
    "kill_zone"  : "—",
    "candles_1m" : 0,
    "error"      : "—",
    "api_calls"  : 0,
}
st = {
    "bull_sweep_bar": -999, "bear_sweep_bar": -999,
    "bull_choch_bar": -999, "bear_choch_bar": -999,
    "asian_high": None, "asian_low": None,
    "last_sh": None, "last_sl": None,
}

# ══════════════════════════════════════════════════════════════
#  HELPERS
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
    """Track daily API usage, reset counter at midnight IST."""
    today = ist_now().date()
    if api_calls["reset_date"] != today:
        api_calls["count"]      = 0
        api_calls["reset_date"] = today
    api_calls["count"] += 1
    bot_status["api_calls"] = api_calls["count"]
    log.info(f"📡 API call #{api_calls['count']}/800 today")

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
    h,l,pc = df["high"],df["low"],df["close"].shift(1)
    return pd.concat([h-l,(h-pc).abs(),(l-pc).abs()],axis=1).max(axis=1).ewm(span=p,adjust=False).mean()

def pvt_h(s, n):
    v, r = s.values, np.nan
    for i in range(n, len(v)-n):
        if all(v[i]>=v[i-j] for j in range(1,n+1)) and all(v[i]>=v[i+j] for j in range(1,n+1)):
            r = v[i]
    return r

def pvt_l(s, n):
    v, r = s.values, np.nan
    for i in range(n, len(v)-n):
        if all(v[i]<=v[i-j] for j in range(1,n+1)) and all(v[i]<=v[i+j] for j in range(1,n+1)):
            r = v[i]
    return r

# ══════════════════════════════════════════════════════════════
#  TWELVE DATA — FETCH CANDLES (real tick volume)
# ══════════════════════════════════════════════════════════════
def td_fetch(interval, outputsize, target_deque):
    """
    Fetch OHLCV candles from Twelve Data.
    Volume field = tick volume (meaningful, varies per candle).
    interval: '1min' or '1h'
    """
    if not TD_KEY:
        log.warning("⚠️  TWELVE_DATA_KEY not set")
        return

    url    = f"{TD_BASE}/time_series"
    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : interval,
        "outputsize": outputsize,
        "apikey"    : TD_KEY,
        "order"     : "ASC",      # oldest → newest
    }

    try:
        track_call()
        resp = requests.get(url, params=params, timeout=10)
        data = resp.json()

        if data.get("status") == "error":
            log.error(f"Twelve Data error: {data.get('message')}")
            return

        values = data.get("values", [])
        if not values:
            log.warning("Twelve Data: no values returned")
            return

        target_deque.clear()
        for bar in values:
            target_deque.append({
                "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
                "o"    : float(bar["open"]),
                "h"    : float(bar["high"]),
                "l"    : float(bar["low"]),
                "c"    : float(bar["close"]),
                "v"    : float(bar.get("volume", 0)),  # real tick volume ✅
            })

        log.info(f"📊 Twelve Data: {len(target_deque)} {interval} candles "
                 f"| latest vol={list(target_deque)[-1]['v']:.0f}")

    except Exception as e:
        log.error(f"Twelve Data fetch error: {e}")


def td_fetch_latest_1m():
    """Fetch only the last 2 candles to get the most recent closed bar."""
    if not TD_KEY:
        return

    url    = f"{TD_BASE}/time_series"
    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : "1min",
        "outputsize": 2,
        "apikey"    : TD_KEY,
        "order"     : "ASC",
    }

    try:
        track_call()
        resp   = requests.get(url, params=params, timeout=10)
        data   = resp.json()
        values = data.get("values", [])

        if not values:
            return

        # Take second to last = confirmed closed candle
        bar = values[-2] if len(values) >= 2 else values[-1]
        candle = {
            "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
            "o"    : float(bar["open"]),
            "h"    : float(bar["high"]),
            "l"    : float(bar["low"]),
            "c"    : float(bar["close"]),
            "v"    : float(bar.get("volume", 0)),  # ✅ real tick volume
        }

        # Only append if new candle
        if not candles_1m or candles_1m[-1]["epoch"] != candle["epoch"]:
            candles_1m.append(candle)
            log.info(f"🕐 New 1m | close={candle['c']:.2f} "
                     f"vol={candle['v']:.0f} epoch={candle['epoch']}")

    except Exception as e:
        log.error(f"Twelve Data latest 1m error: {e}")

# ══════════════════════════════════════════════════════════════
#  STRATEGY LOGIC
# ══════════════════════════════════════════════════════════════
def run_strategy():
    global trade_active
    df = to_df(candles_1m)
    if len(df) < CFG["slow_ema"] + 10:
        log.info(f"⏳ Warming up: {len(df)}/{CFG['slow_ema']+10} candles")
        return None

    df1h = to_df(candles_1h)
    i    = len(df) - 1

    # EMAs
    bull_t = float(ema(df["close"],CFG["fast_ema"]).iloc[-1]) > \
             float(ema(df["close"],CFG["slow_ema"]).iloc[-1])

    # HTF bias
    bull_b = bear_b = True
    if CFG["use_htf_bias"] and len(df1h) >= CFG["htf_ema"]:
        hv     = float(ema(df1h["close"], CFG["htf_ema"]).iloc[-1])
        cc     = float(df["close"].iloc[-1])
        bull_b = cc > hv
        bear_b = cc < hv

    # ATR
    atr_v = float(calc_atr(df, CFG["atr_len"]).iloc[-1])

    # ── VOLUME — Twelve Data tick volume ──
    high_v = True
    if CFG["use_volume"]:
        cur_vol  = float(df["volume"].iloc[-1])
        avg_vol  = float(df["volume"].rolling(20).mean().iloc[-1])
        avg_vol  = avg_vol if avg_vol > 0 else 1
        high_v   = cur_vol > avg_vol * CFG["vol_mult"]
        log.info(f"📊 vol={cur_vol:.0f} avg={avg_vol:.0f} "
                 f"thr={avg_vol*CFG['vol_mult']:.0f} ok={high_v}")

    # PDH / PDL
    n   = len(df)
    pdh = float(df["high"].iloc[-1440:-720].max()) if n>=1440 else float(df["high"].iloc[:max(1,n//2)].max())
    pdl = float(df["low"].iloc[-1440:-720].min())  if n>=1440 else float(df["low"].iloc[:max(1,n//2)].min())

    # Swing H/L
    sw  = CFG["swing_len"]
    lsh = pvt_h(df["high"], sw) if len(df)>=sw*2+5 else st["last_sh"]
    lsl = pvt_l(df["low"],  sw) if len(df)>=sw*2+5 else st["last_sl"]
    st["last_sh"] = lsh; st["last_sl"] = lsl

    c,o,h,l   = (float(df["close"].iloc[-1]), float(df["open"].iloc[-1]),
                 float(df["high"].iloc[-1]),  float(df["low"].iloc[-1]))
    ph,pl,po,pc = (float(df["high"].iloc[-2]), float(df["low"].iloc[-2]),
                   float(df["open"].iloc[-2]), float(df["close"].iloc[-2]))

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
    be_l = c>o and c>po and o<pc and body>rng*0.5
    be_s = c<o and c<po and o>pc and body>rng*0.5

    # Filters
    htfl = bull_b  if CFG["use_htf_bias"]    else True
    htfs = bear_b  if CFG["use_htf_bias"]    else True
    trl  = bull_t  if CFG["use_local_trend"] else True
    trs  = not bull_t if CFG["use_local_trend"] else True
    el   = be_l    if CFG["use_engulf"]      else True
    es   = be_s    if CFG["use_engulf"]      else True
    vok  = high_v  if CFG["use_volume"]      else True

    long_ok  = htfl and trl and vok and rbs and rbc  and el  and not trade_active
    short_ok = htfs and trs and vok and rbe and rbrc and es  and not trade_active

    log.info(f"⏳ htf:{'B' if bull_b else 'b'} tr:{'B' if bull_t else 'b'} "
             f"vol:{vok} bs:{rbs} be:{rbe} bc:{rbc} brc:{rbrc} "
             f"el:{be_l} es:{be_s}")

    if long_ok:
        sl = l - atr_v*CFG["sl_atr_mult"]
        tp = c + abs(c-sl)*CFG["rr_ratio"]
        log.info(f"🚀 LONG entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
        return {"action":"BUY","entry":c,"sl":sl,"tp":tp,
                "sl_dist":abs(c-sl),"tp_dist":abs(tp-c)}

    if short_ok:
        sl = h + atr_v*CFG["sl_atr_mult"]
        tp = c - abs(sl-c)*CFG["rr_ratio"]
        log.info(f"🔻 SHORT entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
        return {"action":"SELL","entry":c,"sl":sl,"tp":tp,
                "sl_dist":abs(sl-c),"tp_dist":abs(c-tp)}

    return None

# ══════════════════════════════════════════════════════════════
#  PLACE TRADE — Deriv MT5 via WebSocket
# ══════════════════════════════════════════════════════════════
def place_trade(signal):
    global trade_active
    result = {}; done = threading.Event()
    otype  = 0 if signal["action"] == "BUY" else 1

    def on_open(ws): ws.send(json.dumps({"authorize": DERIV_TOKEN}))

    def on_message(ws, msg):
        global trade_active
        d  = json.loads(msg)
        mt = d.get("msg_type")

        if mt == "authorize":
            if "error" in d:
                log.error(f"Auth error: {d['error']['message']}")
                result["status"] = "auth_error"; ws.close(); done.set(); return

            ws.send(json.dumps({
                "mt5_new_order": 1,
                "login"        : int(MT5_LOGIN),
                "symbol"       : CFG["mt5_symbol"],
                "volume"       : CFG["lot_size"],
                "order_type"   : otype,
                "price"        : signal["entry"],
                "stop_loss"    : round(signal["sl"], 2),
                "take_profit"  : round(signal["tp"], 2),
                "comment"      : "SMC+XAU Bot v3",
            }))
            log.info(f"📤 MT5 order: {signal['action']} "
                     f"0.01 lots @ {signal['entry']:.2f} "
                     f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f}")

        elif mt == "mt5_new_order":
            if "error" in d:
                log.error(f"MT5 error: {d['error']['message']}")
                result["status"] = "error"
                result["detail"] = d["error"]["message"]
            else:
                oid = d.get("mt5_new_order",{}).get("order","—")
                log.info(f"✅ Trade placed! Order ID: {oid}")
                result["status"] = "placed"; result["order"] = oid
                trade_active = True
                bot_status["last_signal"] = (
                    f"{signal['action']} @ {signal['entry']:.2f} "
                    f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} "
                    f"[{ist_now().strftime('%H:%M IST')}]"
                )
            ws.close(); done.set()

        elif mt == "error":
            result["status"] = "ws_error"; ws.close(); done.set()

    def on_error(ws, e):
        result["status"] = "ws_error"; done.set()

    websocket.WebSocketApp(DERIV_WS, on_open=on_open,
                           on_message=on_message,
                           on_error=on_error).run_forever()
    done.wait(20)
    return result

# ══════════════════════════════════════════════════════════════
#  BOT LOOP
# ══════════════════════════════════════════════════════════════
def bot_loop():
    log.info("🤖 SMC+XAU Bot v3 starting...")
    log.info(f"Twelve Data key: {'✅ Set' if TD_KEY else '❌ Missing'}")
    log.info(f"Deriv token    : {'✅ Set' if DERIV_TOKEN else '❌ Missing'}")
    log.info(f"MT5 login      : {MT5_LOGIN or '❌ Missing'}")

    # Initial candle load — uses 2 API calls
    td_fetch("1min", CFG["candle_limit"], candles_1m)
    td_fetch("1h",   CFG["htf_limit"],    candles_1h)

    bot_status["running"]    = True
    bot_status["candles_1m"] = len(candles_1m)
    log.info(f"✅ Ready | {len(candles_1m)} × 1m | {len(candles_1h)} × 1H")

    while True:
        try:
            # Always fetch latest candle (1 API call)
            td_fetch_latest_1m()
            bot_status["candles_1m"] = len(candles_1m)

            now = ist_now(); kz = kz_name()
            bot_status["kill_zone"]  = kz
            bot_status["last_check"] = now.strftime("%H:%M:%S IST")

            log.info(f"\n{'='*55}")
            log.info(f"⏰ {now.strftime('%H:%M IST')} | {kz}")
            log.info(f"📦 {len(candles_1m)} × 1m | trade={trade_active} "
                     f"| calls={api_calls['count']}/800")

            if not is_kz():
                log.info("💤 Outside kill zone — waiting")
                time.sleep(CFG["check_every_sec"])
                continue

            sig = run_strategy()

            if sig:
                if DERIV_TOKEN and MT5_LOGIN:
                    log.info(f"🎯 {sig['action']} — placing trade on MT5...")
                    res = place_trade(sig)
                    log.info(f"📋 Result: {res}")
                    bot_status["error"] = str(res.get("detail","—"))
                else:
                    missing = []
                    if not DERIV_TOKEN: missing.append("DERIV_API_TOKEN")
                    if not MT5_LOGIN:   missing.append("MT5_LOGIN")
                    log.info(f"🎯 DRY RUN {sig['action']} @ {sig['entry']:.2f} "
                             f"| Missing: {', '.join(missing)}")
                    bot_status["last_signal"] = (
                        f"DRY {sig['action']} @ {sig['entry']:.2f}"
                    )

            # Refresh 1H candles every hour (1 API call)
            if now.minute == 0:
                td_fetch("1h", CFG["htf_limit"], candles_1h)
                log.info("🔄 1H candles refreshed")

        except Exception as e:
            log.error(f"❌ Loop error: {e}", exc_info=True)
            bot_status["error"] = str(e)

        time.sleep(CFG["check_every_sec"])

# ══════════════════════════════════════════════════════════════
#  FLASK STATUS PAGE
# ══════════════════════════════════════════════════════════════
app = Flask(__name__)

@app.route("/")
def status():
    ist   = ist_now().strftime("%H:%M:%S")
    kz    = kz_name()
    run   = "✅ Running" if bot_status["running"] else "⏳ Starting..."
    tok   = "✅ Set" if DERIV_TOKEN else "❌ Add DERIV_API_TOKEN"
    login = MT5_LOGIN or "❌ Add MT5_LOGIN"
    tdkey = "✅ Set" if TD_KEY else "❌ Add TWELVE_DATA_KEY"
    calls = f"{bot_status['api_calls']}/800 today"

    rows = [
        ("Status",       run,                          "#3fb950"),
        ("IST Time",     ist,                          "#e3b341"),
        ("Kill Zone",    kz,                           "#e6edf3"),
        ("Last Check",   bot_status["last_check"],     "#e6edf3"),
        ("1m Candles",   str(bot_status["candles_1m"]),"#e6edf3"),
        ("API Calls",    calls,                        "#e3b341"),
        ("Last Signal",  bot_status["last_signal"],    "#58a6ff"),
        ("Trade Active", "🔴 YES" if trade_active else "⚪ No", "#e6edf3"),
        ("Twelve Data",  tdkey,                        "#e6edf3"),
        ("Deriv Token",  tok,                          "#e6edf3"),
        ("MT5 Login",    login,                        "#e6edf3"),
        ("Last Error",   bot_status["error"],          "#f85149"),
    ]

    table_html = "".join(
        f'<tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">{label}</td>'
        f'<td style="padding:7px 12px;color:{color};border-bottom:1px solid #21262d">{val}</td></tr>'
        for label, val, color in rows
    )

    return f"""<html>
    <head><meta http-equiv="refresh" content="30"><title>SMC Bot v3</title></head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;padding:30px;max-width:620px">
    <h2 style="color:#58a6ff">🤖 SMC+XAUUSD Bot v3</h2>
    <p style="color:#484f58;margin-top:-12px">
      0.01 lots · MT5 STD Demo · 1m · Twelve Data volume
    </p>
    <table style="border-collapse:collapse;width:100%">{table_html}</table>
    <br>
    <p style="color:#484f58;font-size:12px;line-height:1.8">
      🟡 London: 12:30–15:30 IST &nbsp;|&nbsp; 🔵 NY: 17:30–20:30 IST<br>
      Volume: Twelve Data tick count (real, varies per candle)<br>
      Auto-refreshes every 30s
    </p>
    </body></html>""", 200

@app.route("/api/status")
def api_status():
    return jsonify({**bot_status,
                    "kz": is_kz(),
                    "ist": ist_now().strftime("%H:%M:%S"),
                    "trade": trade_active,
                    "api_calls": api_calls["count"]})

# ══════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    if not TD_KEY:      log.warning("⚠️  TWELVE_DATA_KEY not set")
    if not DERIV_TOKEN: log.warning("⚠️  DERIV_API_TOKEN not set")
    if not MT5_LOGIN:   log.warning("⚠️  MT5_LOGIN not set")

    threading.Thread(target=bot_loop, daemon=True).start()
    port = int(os.environ.get("PORT", 5000))
    log.info(f"🌐 Flask on port {port}")
    app.run(host="0.0.0.0", port=port, use_reloader=False)

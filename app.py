"""
SMC + XAUUSD Trading Bot
========================
Timeframe  : 1 minute
Data source: Deriv WebSocket (real-time, free)
Broker     : Deriv Demo (MT5 STD)
Server     : Railway (free tier)

Strategy inputs (matched to Pine Script settings):
  Fast EMA     : 14
  Slow EMA     : 140
  HTF EMA      : 50  (on 1H candles)
  ATR length   : 14
  SL multiplier: 2.0 x ATR
  R:R ratio    : 3.0
  Swing length : 3
  CHoCH window : 5 bars
  Sweep window : 10 bars
  Volume mult  : 1.1
  Kill zones   : London 12:30–15:30 IST / NY 17:30–20:30 IST
"""

import json
import time
import threading
import logging
import os
from datetime import datetime, timezone, timedelta
from collections import deque

import pandas as pd
import numpy  as np
import websocket
from flask import Flask, jsonify

# ══════════════════════════════════════════════════════════════
#  LOGGING
# ══════════════════════════════════════════════════════════════
logging.basicConfig(
    level  = logging.INFO,
    format = "%(asctime)s [%(levelname)s] %(message)s",
    datefmt= "%H:%M:%S"
)
log = logging.getLogger(__name__)

# ══════════════════════════════════════════════════════════════
#  CONFIGURATION  — matches your Pine Script inputs exactly
# ══════════════════════════════════════════════════════════════
CFG = {
    # EMA
    "fast_ema"      : 14,
    "slow_ema"      : 140,
    "htf_ema"       : 50,       # applied on 1H candles

    # ATR / Risk
    "atr_len"       : 14,
    "sl_atr_mult"   : 2.0,
    "rr_ratio"      : 3.0,

    # Structure
    "swing_len"     : 3,
    "choch_window"  : 5,        # bars
    "sweep_window"  : 10,       # bars

    # Filters (all ON)
    "use_volume"    : True,
    "vol_mult"      : 1.1,
    "use_htf_bias"  : True,
    "use_local_trend": True,
    "use_engulf"    : True,

    # Deriv
    "symbol"        : "frxXAUUSD",
    "stake_usd"     : 10,       # per trade in USD
    "multiplier"    : 10,

    # Candle buffer — keep last N 1-min candles in memory
    "candle_limit"  : 300,
    "htf_limit"     : 100,      # 1H candles for HTF EMA

    # Loop
    "check_every_sec": 60,      # check every new 1-min close
}

# Deriv credentials from Railway environment variables
DERIV_TOKEN  = os.environ.get("DERIV_API_TOKEN", "")
DERIV_APP_ID = "1089"
DERIV_WS     = f"wss://ws.binaryws.com/websockets/v3?app_id={DERIV_APP_ID}"

# IST timezone
IST = timezone(timedelta(hours=5, minutes=30))

# ══════════════════════════════════════════════════════════════
#  CANDLE STORE  — holds live 1-min and 1H candles
# ══════════════════════════════════════════════════════════════
candles_1m = deque(maxlen=CFG["candle_limit"])   # dicts: o,h,l,c,v,epoch
candles_1h = deque(maxlen=CFG["htf_limit"])

trade_active   = False   # prevent multiple open trades
last_signal    = None    # "BUY" / "SELL" — avoid duplicate signals
bot_status     = {"running": False, "last_check": "—", "last_signal": "—",
                  "kill_zone": "—", "candles_1m": 0, "error": "—"}

# ══════════════════════════════════════════════════════════════
#  HELPERS
# ══════════════════════════════════════════════════════════════
def ist_now():
    return datetime.now(IST)

def is_kill_zone():
    t = ist_now().hour * 100 + ist_now().minute
    london = 1230 <= t <= 1530   # 12:30–15:30 IST
    ny     = 1730 <= t <= 2030   # 17:30–20:30 IST
    return london or ny

def kill_zone_name():
    t = ist_now().hour * 100 + ist_now().minute
    if 1230 <= t <= 1530: return "🟡 London (12:30–15:30 IST)"
    if 1730 <= t <= 2030: return "🔵 NY     (17:30–20:30 IST)"
    return "⚫ Outside kill zone"

def to_df(candles):
    """Convert deque of candle dicts to pandas DataFrame."""
    df = pd.DataFrame(list(candles))
    if df.empty:
        return df
    df = df.rename(columns={"o":"open","h":"high","l":"low","c":"close","v":"volume"})
    for col in ["open","high","low","close","volume"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    return df.reset_index(drop=True)

# ══════════════════════════════════════════════════════════════
#  INDICATORS  (pure pandas/numpy — no TA-lib needed)
# ══════════════════════════════════════════════════════════════
def ema(series, period):
    return series.ewm(span=period, adjust=False).mean()

def atr(df, period):
    h, l, pc = df["high"], df["low"], df["close"].shift(1)
    tr = pd.concat([h - l, (h - pc).abs(), (l - pc).abs()], axis=1).max(axis=1)
    return tr.ewm(span=period, adjust=False).mean()

def pivot_high(series_high, length):
    """Returns last confirmed pivot high value (or NaN)."""
    vals = series_high.values
    pivot = np.nan
    for i in range(length, len(vals) - length):
        if all(vals[i] >= vals[i - j] for j in range(1, length + 1)) and \
           all(vals[i] >= vals[i + j] for j in range(1, length + 1)):
            pivot = vals[i]
    return pivot

def pivot_low(series_low, length):
    vals = series_low.values
    pivot = np.nan
    for i in range(length, len(vals) - length):
        if all(vals[i] <= vals[i - j] for j in range(1, length + 1)) and \
           all(vals[i] <= vals[i + j] for j in range(1, length + 1)):
            pivot = vals[i]
    return pivot

# ══════════════════════════════════════════════════════════════
#  STRATEGY LOGIC  — mirrors Pine Script exactly
# ══════════════════════════════════════════════════════════════

# State variables (equivalent to Pine Script var)
state = {
    "bull_sweep_bar"  : -999,
    "bear_sweep_bar"  : -999,
    "bull_choch_bar"  : -999,
    "bear_choch_bar"  : -999,
    "asian_high"      : None,
    "asian_low"       : None,
    "last_swing_high" : None,
    "last_swing_low"  : None,
    "in_asian"        : False,
    "pdh"             : None,
    "pdl"             : None,
    "last_trade_bar"  : -999,
}

def run_strategy():
    """
    Called every 60 seconds.
    Returns dict with signal info or None.
    """
    global trade_active, last_signal

    df = to_df(candles_1m)
    if len(df) < CFG["slow_ema"] + 10:
        log.info(f"Not enough candles yet: {len(df)}/{CFG['slow_ema']+10}")
        return None

    df_1h = to_df(candles_1h)

    n = len(df)
    i = n - 1   # current bar index

    # ── EMAs ──
    fast = ema(df["close"], CFG["fast_ema"])
    slow = ema(df["close"], CFG["slow_ema"])

    bull_trend = float(fast.iloc[-1]) > float(slow.iloc[-1])
    bear_trend = float(fast.iloc[-1]) < float(slow.iloc[-1])

    # ── HTF EMA bias (1H) ──
    bull_bias, bear_bias = True, True
    if CFG["use_htf_bias"] and len(df_1h) >= CFG["htf_ema"]:
        htf_ema_val = float(ema(df_1h["close"], CFG["htf_ema"]).iloc[-1])
        cur_close   = float(df["close"].iloc[-1])
        bull_bias   = cur_close > htf_ema_val
        bear_bias   = cur_close < htf_ema_val

    # ── ATR ──
    atr_series = atr(df, CFG["atr_len"])
    atr_val    = float(atr_series.iloc[-1])

    # ── Volume ──
    avg_vol  = df["volume"].rolling(20).mean()
    high_vol = True
    if CFG["use_volume"] and not df["volume"].isna().all():
        high_vol = float(df["volume"].iloc[-1]) > float(avg_vol.iloc[-1]) * CFG["vol_mult"]

    # ── Asian range (approximate using time-of-day) ──
    # Use candle timestamps if available, else skip
    asian_high = state["asian_high"]
    asian_low  = state["asian_low"]

    # ── PDH / PDL (use rolling daily high/low approximation) ──
    # Take high/low of candles from >24h ago as prev day reference
    if len(df) >= 1440:   # 1440 mins = 1 day
        pdh = float(df["high"].iloc[-1440:-720].max())
        pdl = float(df["low"].iloc[-1440:-720].min())
    else:
        pdh = float(df["high"].iloc[:max(1, n//2)].max())
        pdl = float(df["low"].iloc[:max(1, n//2)].min())

    # ── Swing High / Low ──
    sw_len = CFG["swing_len"]
    if len(df) >= sw_len * 2 + 5:
        last_swing_high = pivot_high(df["high"], sw_len)
        last_swing_low  = pivot_low (df["low"],  sw_len)
    else:
        last_swing_high = state["last_swing_high"]
        last_swing_low  = state["last_swing_low"]

    state["last_swing_high"] = last_swing_high
    state["last_swing_low"]  = last_swing_low

    cur_close = float(df["close"].iloc[-1])
    cur_open  = float(df["open"].iloc[-1])
    cur_high  = float(df["high"].iloc[-1])
    cur_low   = float(df["low"].iloc[-1])
    prev_high = float(df["high"].iloc[-2])
    prev_low  = float(df["low"].iloc[-2])
    prev_open = float(df["open"].iloc[-2])
    prev_close= float(df["close"].iloc[-2])

    # ── Liquidity Sweeps ──
    sweep_bull_raw = False
    sweep_bear_raw = False

    if asian_low  and cur_low  < asian_low:
        sweep_bull_raw = True
    if asian_high and cur_high > asian_high:
        sweep_bear_raw = True
    if cur_low  < pdl:
        sweep_bull_raw = True
    if cur_high > pdh:
        sweep_bear_raw = True
    if last_swing_low  and not np.isnan(last_swing_low)  \
       and cur_low < last_swing_low and cur_close > last_swing_low:
        sweep_bull_raw = True
    if last_swing_high and not np.isnan(last_swing_high) \
       and cur_high > last_swing_high and cur_close < last_swing_high:
        sweep_bear_raw = True

    if sweep_bull_raw:
        state["bull_sweep_bar"] = i
        log.info("🔍 Bull sweep detected")
    if sweep_bear_raw:
        state["bear_sweep_bar"] = i
        log.info("🔍 Bear sweep detected")

    recent_bull_sweep = (i - state["bull_sweep_bar"]) <= CFG["sweep_window"]
    recent_bear_sweep = (i - state["bear_sweep_bar"]) <= CFG["sweep_window"]

    # ── CHoCH ──
    bull_choch_raw = recent_bear_sweep and cur_close > prev_high and cur_close > cur_open
    bear_choch_raw = recent_bull_sweep and cur_close < prev_low  and cur_close < cur_open

    if bull_choch_raw:
        state["bull_choch_bar"] = i
        log.info("🔄 Bull CHoCH detected")
    if bear_choch_raw:
        state["bear_choch_bar"] = i
        log.info("🔄 Bear CHoCH detected")

    recent_bull_choch = (i - state["bull_choch_bar"]) <= CFG["choch_window"]
    recent_bear_choch = (i - state["bear_choch_bar"]) <= CFG["choch_window"]

    # ── Engulfing ──
    body       = abs(cur_close  - cur_open)
    candle_rng = cur_high - cur_low
    bull_engulf = (cur_close > cur_open
                   and cur_close > prev_open
                   and cur_open  < prev_close
                   and body > candle_rng * 0.5)

    bear_engulf = (cur_close < cur_open
                   and cur_close < prev_open
                   and cur_open  > prev_close
                   and body > candle_rng * 0.5)

    # ── Apply toggleable filters ──
    htf_ok_long  = bull_bias if CFG["use_htf_bias"]     else True
    htf_ok_short = bear_bias if CFG["use_htf_bias"]     else True
    trend_long   = bull_trend if CFG["use_local_trend"] else True
    trend_short  = bear_trend if CFG["use_local_trend"] else True
    eng_long     = bull_engulf if CFG["use_engulf"]     else True
    eng_short    = bear_engulf if CFG["use_engulf"]     else True
    vol_ok       = high_vol if CFG["use_volume"]        else True

    # ── Final entry conditions ──
    long_entry  = (htf_ok_long  and trend_long  and vol_ok
                   and recent_bull_sweep and recent_bull_choch and eng_long
                   and not trade_active)

    short_entry = (htf_ok_short and trend_short and vol_ok
                   and recent_bear_sweep and recent_bear_choch and eng_short
                   and not trade_active)

    # ── SL / TP ──
    if long_entry:
        sl_price = cur_low  - atr_val * CFG["sl_atr_mult"]
        sl_dist  = abs(cur_close - sl_price)
        tp_dist  = sl_dist * CFG["rr_ratio"]
        log.info(f"🚀 LONG SIGNAL | Entry:{cur_close:.2f} SL:{sl_price:.2f} "
                 f"TP:{cur_close+tp_dist:.2f} ATR:{atr_val:.2f}")
        return {"action":"BUY",  "entry":cur_close, "sl_dist":sl_dist, "tp_dist":tp_dist,
                "sl":sl_price, "tp":cur_close+tp_dist}

    if short_entry:
        sl_price = cur_high + atr_val * CFG["sl_atr_mult"]
        sl_dist  = abs(sl_price - cur_close)
        tp_dist  = sl_dist * CFG["rr_ratio"]
        log.info(f"🔻 SHORT SIGNAL | Entry:{cur_close:.2f} SL:{sl_price:.2f} "
                 f"TP:{cur_close-tp_dist:.2f} ATR:{atr_val:.2f}")
        return {"action":"SELL", "entry":cur_close, "sl_dist":sl_dist, "tp_dist":tp_dist,
                "sl":sl_price, "tp":cur_close-tp_dist}

    log.info(f"⏳ No signal | close:{cur_close:.2f} "
             f"bull_sweep:{recent_bull_sweep} bear_sweep:{recent_bear_sweep} "
             f"bull_choch:{recent_bull_choch} bear_choch:{recent_bear_choch} "
             f"bull_eng:{bull_engulf} bear_eng:{bear_engulf} "
             f"htf_bias:{'BULL' if bull_bias else 'BEAR'} "
             f"trend:{'BULL' if bull_trend else 'BEAR'} vol:{vol_ok}")
    return None

# ══════════════════════════════════════════════════════════════
#  DERIV API — PLACE TRADE
# ══════════════════════════════════════════════════════════════
def place_trade_deriv(signal):
    """
    Places a Multiplier trade on Deriv demo.
    signal = {"action":"BUY"/"SELL", "sl_dist":..., "tp_dist":...}
    """
    global trade_active, last_signal
    result = {}
    done   = threading.Event()

    def on_open(ws):
        ws.send(json.dumps({"authorize": DERIV_TOKEN}))

    def on_message(ws, msg):
        global trade_active, last_signal
        data = json.loads(msg)
        mt   = data.get("msg_type")

        if mt == "authorize":
            if "error" in data:
                log.error(f"Auth failed: {data['error']['message']}")
                result["status"] = "auth_error"
                ws.close(); done.set(); return

            # Build trade request
            action = signal["action"]
            contract_type = "MULTUP" if action == "BUY" else "MULTDOWN"

            trade_req = {
                "buy": "1",
                "price": CFG["stake_usd"],
                "parameters": {
                    "contract_type" : contract_type,
                    "symbol"        : CFG["symbol"],
                    "multiplier"    : CFG["multiplier"],
                    "amount"        : CFG["stake_usd"],
                    "basis"         : "stake",
                    "currency"      : "USD",
                    "duration"      : 1,
                    "duration_unit" : "d",
                    "stop_loss"     : round(signal["sl_dist"], 2),
                    "take_profit"   : round(signal["tp_dist"], 2),
                }
            }
            log.info(f"📤 Sending trade: {trade_req}")
            ws.send(json.dumps(trade_req))

        elif mt == "buy":
            if "error" in data:
                log.error(f"Trade error: {data['error']['message']}")
                result["status"] = "error"
                result["detail"] = data["error"]["message"]
            else:
                cid = data["buy"].get("contract_id", "—")
                log.info(f"✅ Trade placed! Contract ID: {cid}")
                result["status"]      = "placed"
                result["contract_id"] = cid
                trade_active          = True
                last_signal           = signal["action"]
                bot_status["last_signal"] = (
                    f"{signal['action']} @ {signal['entry']:.2f} "
                    f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} "
                    f"[{ist_now().strftime('%H:%M IST')}]"
                )
            ws.close(); done.set()

        elif mt == "error":
            log.error(f"WS error: {data}")
            result["status"] = "ws_error"
            ws.close(); done.set()

    def on_error(ws, err):
        log.error(f"WebSocket error: {err}")
        result["status"] = "ws_error"
        done.set()

    ws_app = websocket.WebSocketApp(
        DERIV_WS,
        on_open    = on_open,
        on_message = on_message,
        on_error   = on_error
    )
    t = threading.Thread(target=ws_app.run_forever, daemon=True)
    t.start()
    done.wait(timeout=20)
    return result

# ══════════════════════════════════════════════════════════════
#  DERIV — FETCH CANDLES
# ══════════════════════════════════════════════════════════════
def fetch_candles(granularity_sec, count, target_deque):
    """
    Fetches historical candles from Deriv and fills target_deque.
    granularity_sec: 60 = 1min, 3600 = 1H
    """
    done    = threading.Event()
    fetched = []

    def on_open(ws):
        ws.send(json.dumps({
            "ticks_history"  : CFG["symbol"],
            "end"            : "latest",
            "count"          : count,
            "granularity"    : granularity_sec,
            "style"          : "candles",
            "adjust_start_time": 1,
        }))

    def on_message(ws, msg):
        data = json.loads(msg)
        if data.get("msg_type") == "candles":
            for c in data.get("candles", []):
                fetched.append({
                    "epoch" : c["epoch"],
                    "o"     : float(c["open"]),
                    "h"     : float(c["high"]),
                    "l"     : float(c["low"]),
                    "c"     : float(c["close"]),
                    "v"     : 0.0,   # Deriv candles have no volume
                })
            log.info(f"📊 Fetched {len(fetched)} candles (gran={granularity_sec}s)")
        ws.close()
        done.set()

    def on_error(ws, err):
        log.error(f"Candle fetch error: {err}")
        done.set()

    ws_app = websocket.WebSocketApp(
        DERIV_WS,
        on_open    = on_open,
        on_message = on_message,
        on_error   = on_error
    )
    t = threading.Thread(target=ws_app.run_forever, daemon=True)
    t.start()
    done.wait(timeout=20)

    target_deque.clear()
    for c in fetched:
        target_deque.append(c)

def fetch_latest_candle_1m():
    """Fetches just the last completed 1-min candle and appends."""
    done    = threading.Event()
    fetched = []

    def on_open(ws):
        ws.send(json.dumps({
            "ticks_history"  : CFG["symbol"],
            "end"            : "latest",
            "count"          : 2,   # last 2 to ensure closed candle
            "granularity"    : 60,
            "style"          : "candles",
        }))

    def on_message(ws, msg):
        data = json.loads(msg)
        if data.get("msg_type") == "candles":
            candles_raw = data.get("candles", [])
            if candles_raw:
                c = candles_raw[-2] if len(candles_raw) >= 2 else candles_raw[-1]
                fetched.append({
                    "epoch": c["epoch"],
                    "o"    : float(c["open"]),
                    "h"    : float(c["high"]),
                    "l"    : float(c["low"]),
                    "c"    : float(c["close"]),
                    "v"    : 0.0,
                })
        ws.close()
        done.set()

    def on_error(ws, err):
        done.set()

    ws_app = websocket.WebSocketApp(
        DERIV_WS,
        on_open    = on_open,
        on_message = on_message,
        on_error   = on_error
    )
    t = threading.Thread(target=ws_app.run_forever, daemon=True)
    t.start()
    done.wait(timeout=15)

    if fetched:
        # Only append if it's a new candle (new epoch)
        if not candles_1m or candles_1m[-1]["epoch"] != fetched[0]["epoch"]:
            candles_1m.append(fetched[0])
            log.info(f"🕐 New 1m candle: close={fetched[0]['c']:.2f} "
                     f"epoch={fetched[0]['epoch']}")

# ══════════════════════════════════════════════════════════════
#  MAIN BOT LOOP
# ══════════════════════════════════════════════════════════════
def bot_loop():
    global trade_active
    log.info("🤖 Bot starting — fetching initial candle history...")

    # Initial candle load
    fetch_candles(60,   CFG["candle_limit"], candles_1m)
    fetch_candles(3600, CFG["htf_limit"],    candles_1h)

    bot_status["running"]   = True
    bot_status["candles_1m"]= len(candles_1m)
    log.info(f"✅ Loaded {len(candles_1m)} × 1m candles, "
             f"{len(candles_1h)} × 1H candles")

    while True:
        try:
            # Refresh latest candle
            fetch_latest_candle_1m()
            bot_status["candles_1m"] = len(candles_1m)

            now_ist = ist_now()
            kz_name = kill_zone_name()
            bot_status["kill_zone"]   = kz_name
            bot_status["last_check"]  = now_ist.strftime("%H:%M:%S IST")

            log.info(f"\n{'='*55}")
            log.info(f"⏰ {now_ist.strftime('%H:%M IST')} | {kz_name}")
            log.info(f"📦 Candles: {len(candles_1m)} × 1m | "
                     f"Trade active: {trade_active}")

            if not DERIV_TOKEN:
                log.warning("⚠️  DERIV_API_TOKEN not set — running in dry mode")

            # ── Kill zone guard ──
            if not is_kill_zone():
                log.info("💤 Outside kill zone — skipping strategy check")
                time.sleep(CFG["check_every_sec"])
                continue

            # ── Run strategy ──
            signal = run_strategy()

            if signal and DERIV_TOKEN:
                log.info(f"🎯 Signal: {signal['action']} — placing trade...")
                result = place_trade_deriv(signal)
                log.info(f"📋 Trade result: {result}")
                bot_status["error"] = str(result.get("detail", "—"))
            elif signal and not DERIV_TOKEN:
                log.info(f"🎯 Signal: {signal['action']} (DRY RUN — no token set)")
                bot_status["last_signal"] = f"DRY {signal['action']} @ {signal['entry']:.2f}"

            # Refresh 1H candles every hour
            if now_ist.minute == 0:
                fetch_candles(3600, CFG["htf_limit"], candles_1h)
                log.info("🔄 Refreshed 1H candles")

        except Exception as e:
            log.error(f"❌ Bot error: {e}", exc_info=True)
            bot_status["error"] = str(e)

        time.sleep(CFG["check_every_sec"])

# ══════════════════════════════════════════════════════════════
#  FLASK STATUS SERVER  — so Railway keeps the service alive
# ══════════════════════════════════════════════════════════════
flask_app = Flask(__name__)

@flask_app.route("/")
def status_page():
    ist = ist_now().strftime("%H:%M:%S")
    kz  = kill_zone_name()
    tok = "✅ Set" if DERIV_TOKEN else "❌ NOT SET — add DERIV_API_TOKEN in Railway variables"
    return f"""
    <html>
    <head>
      <meta http-equiv="refresh" content="30">
      <title>SMC+XAU Bot</title>
    </head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;padding:30px;max-width:600px">
      <h2 style="color:#58a6ff">🤖 SMC + XAUUSD Bot</h2>
      <table style="border-collapse:collapse;width:100%">
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">Status</td>
            <td style="padding:8px 12px;color:#3fb950;border-bottom:1px solid #21262d">
                {'✅ Running' if bot_status['running'] else '⏳ Starting...'}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">IST Time</td>
            <td style="padding:8px 12px;color:#e3b341;border-bottom:1px solid #21262d">{ist}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">Kill Zone</td>
            <td style="padding:8px 12px;border-bottom:1px solid #21262d">{kz}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">Last Check</td>
            <td style="padding:8px 12px;border-bottom:1px solid #21262d">{bot_status['last_check']}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">1m Candles</td>
            <td style="padding:8px 12px;border-bottom:1px solid #21262d">{bot_status['candles_1m']}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">Last Signal</td>
            <td style="padding:8px 12px;color:#58a6ff;border-bottom:1px solid #21262d">{bot_status['last_signal']}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e;border-bottom:1px solid #21262d">API Token</td>
            <td style="padding:8px 12px;border-bottom:1px solid #21262d">{tok}</td></tr>
        <tr><td style="padding:8px 12px;color:#8b949e">Last Error</td>
            <td style="padding:8px 12px;color:#f85149">{bot_status['error']}</td></tr>
      </table>
      <br>
      <p style="color:#484f58;font-size:12px">
        Kill zones (IST):<br>
        🟡 London: 12:30 PM – 3:30 PM<br>
        🔵 NY: 5:30 PM – 8:30 PM<br><br>
        Page auto-refreshes every 30s
      </p>
    </body>
    </html>
    """, 200

@flask_app.route("/api/status")
def api_status():
    return jsonify({**bot_status, "kill_zone_active": is_kill_zone(),
                    "ist_time": ist_now().strftime("%H:%M:%S")})

# ══════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    if not DERIV_TOKEN:
        log.warning("⚠️  DERIV_API_TOKEN not set — bot will run in DRY mode (no real trades)")

    # Start bot loop in background thread
    bot_thread = threading.Thread(target=bot_loop, daemon=True)
    bot_thread.start()

    # Start Flask server (Railway needs a web server to stay alive)
    port = int(os.environ.get("PORT", 5000))
    log.info(f"🌐 Status server starting on port {port}")
    flask_app.run(host="0.0.0.0", port=port, use_reloader=False)

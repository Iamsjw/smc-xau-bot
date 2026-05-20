"""
SMC + XAUUSD Trading Bot v6
============================
Full error handling + Telegram alerts for every failure point:

Every minute checks:
  - Candle fetch success/fail
  - Data quality (stale, missing, zero range)
  - API call limit warning (>700/800)
  - Strategy calculation errors
  - WebSocket connection issues
  - MT5 order rejection reasons
  - Deriv auth failures
  - Kill zone entry/exit notifications
  - Bot crash recovery

Railway Variables:
  DERIV_API_TOKEN    → Deriv MT5 trading
  MT5_LOGIN          → Deriv MT5 login number
  TWELVE_DATA_KEY    → Candle data
  TELEGRAM_BOT_TOKEN → @BotFather token
  TELEGRAM_CHAT_ID   → Your chat ID from @userinfobot
"""

import json, time, threading, logging, os, traceback
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
TG_TOKEN     = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TG_CHAT      = os.environ.get("TELEGRAM_CHAT_ID", "")
DERIV_APP_ID = "1089"
DERIV_WS     = f"wss://ws.binaryws.com/websockets/v3?app_id={DERIV_APP_ID}"
TD_BASE      = "https://api.twelvedata.com"
IST          = timezone(timedelta(hours=5, minutes=30))

# ══════════════════════════════════════════════════════════════
#  CONFIG
# ══════════════════════════════════════════════════════════════
CFG = {
    "fast_ema"        : 14,
    "slow_ema"        : 140,
    "htf_ema"         : 50,
    "atr_len"         : 14,
    "sl_atr_mult"     : 2.0,
    "rr_ratio"        : 3.0,
    "swing_len"       : 3,
    "choch_window"    : 5,
    "sweep_window"    : 10,
    "use_volume"      : True,
    "vol_lookback"    : 20,
    "range_mult"      : 1.1,
    "body_mult"       : 1.0,
    "use_htf_bias"    : True,
    "use_local_trend" : True,
    "use_engulf"      : True,
    "mt5_symbol"      : "XAUUSD",
    "lot_size"        : 0.01,
    "td_symbol"       : "XAU/USD",
    "candle_limit"    : 300,
    "htf_limit"       : 100,
    "check_every_sec" : 60,
    "api_warn_limit"  : 700,   # warn when calls exceed this
    "stale_candle_sec": 180,   # alert if no new candle for 3 mins
    "max_retries"     : 3,     # API retry attempts
}

# ══════════════════════════════════════════════════════════════
#  STATE
# ══════════════════════════════════════════════════════════════
candles_1m   = deque(maxlen=CFG["candle_limit"])
candles_1h   = deque(maxlen=CFG["htf_limit"])
trade_active = False
api_calls    = {"count": 0, "reset_date": None}
bot_status   = {
    "running"       : False,
    "last_check"    : "—",
    "last_signal"   : "—",
    "kill_zone"     : "—",
    "candles_1m"    : 0,
    "error"         : "—",
    "api_calls"     : "0/800",
    "volume_info"   : "—",
    "last_alert"    : "—",
    "last_candle_t" : "—",
    "consecutive_errs": 0,
}
st = {
    "bull_sweep_bar" : -999, "bear_sweep_bar" : -999,
    "bull_choch_bar" : -999, "bear_choch_bar" : -999,
    "asian_high"     : None, "asian_low"      : None,
    "last_sh"        : None, "last_sl"        : None,
    "last_bull_alert": 0,    "last_bear_alert": 0,
    "last_candle_epoch": 0,
    "in_kill_zone"   : False,   # track KZ transitions
    "api_warned"     : False,   # track API limit warning
    "td_fail_count"  : 0,       # consecutive TD fetch failures
}

# ══════════════════════════════════════════════════════════════
#  TELEGRAM — CORE SENDER
# ══════════════════════════════════════════════════════════════
def send_telegram(msg, silent=False):
    """
    Core Telegram sender.
    silent=True → no sound notification (for info messages)
    """
    if not TG_TOKEN or not TG_CHAT:
        log.warning("⚠️ Telegram not configured")
        return False
    try:
        resp = requests.post(
            f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
            json={
                "chat_id"             : TG_CHAT,
                "text"                : msg,
                "parse_mode"          : "HTML",
                "disable_notification": silent,
            },
            timeout=8
        )
        if resp.status_code == 200:
            bot_status["last_alert"] = ist_now().strftime("%H:%M:%S IST")
            log.info(f"📱 TG sent: {msg[:50]}...")
            return True
        else:
            log.error(f"TG HTTP {resp.status_code}: {resp.text[:100]}")
            return False
    except requests.exceptions.Timeout:
        log.error("TG send timeout")
        return False
    except Exception as e:
        log.error(f"TG exception: {e}")
        return False

# ══════════════════════════════════════════════════════════════
#  TELEGRAM — TYPED MESSAGES
# ══════════════════════════════════════════════════════════════
def tg_started():
    send_telegram(
        f"🚀 <b>SMC+XAU Bot v6 Started</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📊 XAUUSD · 1m · 0.01 lots\n"
        f"🛑 SL: {CFG['sl_atr_mult']}×ATR  🎯 TP: 1:{CFG['rr_ratio']}\n"
        f"🟡 London : 12:30–15:30 IST\n"
        f"🔵 NY     : 17:30–20:30 IST\n"
        f"⏰ {ist_now().strftime('%H:%M:%S IST')}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"Now monitoring 🔍"
    )

def tg_kz_open(name):
    send_telegram(
        f"⏰ <b>Kill Zone Opened</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{name}\n"
        f"🔍 Strategy checks now active\n"
        f"📊 XAUUSD @ monitoring\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}",
        silent=True
    )

def tg_kz_close(name):
    send_telegram(
        f"🔕 <b>Kill Zone Closed</b>\n"
        f"{name} ended\n"
        f"💤 Bot sleeping until next KZ\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}",
        silent=True
    )

def tg_early_warning(direction, conds, score, price, atr_v):
    met     = [k for k, v in conds.items() if v]
    missing = [k for k, v in conds.items() if not v]
    send_telegram(
        f"🟡 <b>EARLY WARNING — {direction}</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📊 XAUUSD @ <b>{price:.2f}</b>\n"
        f"✅ <b>{score}/7 conditions met</b>\n"
        f"📐 ATR: {atr_v:.2f}\n"
        f"\n✅ <b>Met:</b>\n" + "\n".join(f"  • {c}" for c in met) +
        f"\n\n⏳ <b>Waiting for:</b>\n" + "\n".join(f"  • {c}" for c in missing) +
        f"\n\n⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_setup_forming(direction, conds, score, price, atr_v, est_sl, est_tp):
    met     = [k for k, v in conds.items() if v]
    missing = [k for k, v in conds.items() if not v]
    send_telegram(
        f"🟠 <b>SETUP FORMING — {direction}</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📊 XAUUSD @ <b>{price:.2f}</b>\n"
        f"✅ <b>{score}/7 conditions met</b>\n"
        f"\n✅ <b>Met:</b>\n" + "\n".join(f"  • {c}" for c in met) +
        f"\n\n⏳ <b>Waiting for:</b>\n" + "\n".join(f"  • {c}" for c in missing) +
        f"\n\n💡 <b>Estimated levels:</b>\n"
        f"  🛑 SL: {est_sl:.2f}\n"
        f"  🎯 TP: {est_tp:.2f}\n"
        f"  📐 ATR: {atr_v:.2f}\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_trade_placed(signal):
    send_telegram(
        f"✅ <b>TRADE PLACED</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📌 <b>{signal['action']} XAUUSD</b>\n"
        f"💰 Entry  : <b>{signal['entry']:.2f}</b>\n"
        f"🛑 SL     : <b>{signal['sl']:.2f}</b>\n"
        f"🎯 TP     : <b>{signal['tp']:.2f}</b>\n"
        f"📦 Lots   : <b>0.01</b>\n"
        f"📐 Risk   : {abs(signal['entry']-signal['sl']):.2f} pts\n"
        f"🏆 Reward : {abs(signal['tp']-signal['entry']):.2f} pts\n"
        f"⏰ Time   : {ist_now().strftime('%H:%M IST')}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🤖 SMC+XAU Bot v6"
    )

# ── Error message templates ──
def tg_err_candle_fetch(reason, attempt):
    send_telegram(
        f"⚠️ <b>Candle Fetch Failed</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 Reason  : {reason}\n"
        f"🔄 Attempt : {attempt}/{CFG['max_retries']}\n"
        f"📊 Source  : Twelve Data (XAU/USD)\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}\n"
        f"{'🚨 Max retries reached — strategy paused' if attempt >= CFG['max_retries'] else '⏳ Retrying...'}"
    )

def tg_err_stale_candle():
    send_telegram(
        f"🚨 <b>Stale Candle Data</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"⚠️ No new candle received for {CFG['stale_candle_sec']}s\n"
        f"📊 Last candle: {bot_status['last_candle_t']}\n"
        f"💡 Twelve Data may be rate limited\n"
        f"🔄 Will retry next cycle\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_api_limit():
    send_telegram(
        f"⚠️ <b>API Call Limit Warning</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📡 Used: <b>{api_calls['count']}/800 calls today</b>\n"
        f"⚠️ Approaching daily limit\n"
        f"💡 Resets at midnight IST\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_api_exhausted():
    send_telegram(
        f"🚨 <b>API Limit Reached — Bot Paused</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"📡 Used: <b>{api_calls['count']}/800 calls</b>\n"
        f"🔴 No more candle data available today\n"
        f"⏰ Resets at midnight IST\n"
        f"🕐 {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_no_data():
    send_telegram(
        f"🚨 <b>No Candle Data</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"⚠️ Twelve Data returned empty response\n"
        f"💡 Possible causes:\n"
        f"  • Market closed (weekend)\n"
        f"  • API key issue\n"
        f"  • Network error\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_bad_data(detail):
    send_telegram(
        f"⚠️ <b>Bad Candle Data</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 Issue: {detail}\n"
        f"💡 Strategy skipped this cycle\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}",
        silent=True
    )

def tg_err_auth():
    send_telegram(
        f"🚨 <b>Deriv Auth Failed</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 DERIV_API_TOKEN rejected\n"
        f"💡 Possible causes:\n"
        f"  • Token expired (90-day limit)\n"
        f"  • Wrong token in Railway vars\n"
        f"  • Token deleted on Deriv\n"
        f"🔧 Fix: Deriv → Security → API Token\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_mt5_order(reason):
    # Provide specific guidance for common MT5 errors
    guidance = {
        "invalid login"         : "Check MT5_LOGIN in Railway variables",
        "trade is disabled"     : "Enable trading on your Deriv MT5 account",
        "not enough money"      : "Demo balance too low — reset it on Deriv",
        "market is closed"      : "Market closed — gold trades Mon-Fri only",
        "invalid price"         : "Price moved too fast — will retry next signal",
        "connection timeout"    : "Deriv server timeout — will retry",
        "invalid stops"         : "SL/TP too close to price — ATR may be very small",
        "off quotes"            : "No price quote — market may be closed",
    }.get(reason.lower(), "Check Deriv MT5 account status")

    send_telegram(
        f"❌ <b>MT5 Order Failed</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 Error  : {reason}\n"
        f"💡 Action : {guidance}\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_ws_timeout():
    send_telegram(
        f"⚠️ <b>Deriv WebSocket Timeout</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 No response from Deriv in 20s\n"
        f"💡 Trade may not have been placed\n"
        f"🔄 Check your Deriv account\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_strategy(err_msg):
    send_telegram(
        f"⚠️ <b>Strategy Calculation Error</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 Error: {err_msg[:200]}\n"
        f"💡 Skipping this cycle\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}",
        silent=True
    )

def tg_err_loop_crash(err_msg, tb):
    send_telegram(
        f"🚨 <b>Bot Loop Crash</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔴 Error: {err_msg[:150]}\n"
        f"📋 Trace: {tb[:200]}\n"
        f"🔄 Bot will auto-recover\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

def tg_err_missing_creds():
    missing = []
    if not DERIV_TOKEN: missing.append("DERIV_API_TOKEN")
    if not MT5_LOGIN:   missing.append("MT5_LOGIN")
    if not TD_KEY:      missing.append("TWELVE_DATA_KEY")
    if not TG_TOKEN:    missing.append("TELEGRAM_BOT_TOKEN")
    if not TG_CHAT:     missing.append("TELEGRAM_CHAT_ID")
    if missing:
        send_telegram(
            f"⚠️ <b>Missing Credentials</b>\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"🔴 Not set in Railway variables:\n" +
            "\n".join(f"  • {m}" for m in missing) +
            f"\n\n🔧 Go to Railway → Service → Variables\n"
            f"⏰ {ist_now().strftime('%H:%M IST')}"
        )

def tg_err_consecutive(count):
    send_telegram(
        f"🚨 <b>Repeated Failures — {count} in a row</b>\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"⚠️ Bot has failed {count} consecutive cycles\n"
        f"💡 Check Railway logs for details\n"
        f"🔧 May need manual restart\n"
        f"⏰ {ist_now().strftime('%H:%M IST')}"
    )

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
        st["api_warned"]        = False   # reset warning at midnight
    api_calls["count"] += 1
    bot_status["api_calls"] = f"{api_calls['count']}/800"

    # Warn when approaching limit
    if api_calls["count"] >= CFG["api_warn_limit"] and not st["api_warned"]:
        st["api_warned"] = True
        tg_err_api_limit()

    # Hard stop at 790 to leave buffer
    if api_calls["count"] >= 790:
        tg_err_api_exhausted()
        return False
    return True

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
#  VOLUME PROXY
# ══════════════════════════════════════════════════════════════
def check_volume(df):
    lb           = CFG["vol_lookback"]
    candle_range = df["high"] - df["low"]
    candle_body  = (df["close"] - df["open"]).abs()

    avg_range = candle_range.rolling(lb).mean()
    avg_body  = candle_body.rolling(lb).mean()

    cur_range = float(candle_range.iloc[-1])
    cur_body  = float(candle_body.iloc[-1])
    av_range  = float(avg_range.iloc[-1]) if not pd.isna(avg_range.iloc[-1]) else cur_range
    av_body   = float(avg_body.iloc[-1])  if not pd.isna(avg_body.iloc[-1])  else cur_body

    # Data quality check
    if cur_range == 0:
        tg_err_bad_data("Zero candle range — flat/bad candle")
        return False

    range_ok = cur_range > av_range * CFG["range_mult"]
    body_ok  = cur_body  > av_body  * CFG["body_mult"]
    high_vol = range_ok and body_ok

    info = (f"range={cur_range:.2f}(avg {av_range:.2f}) {'✅' if range_ok else '❌'} | "
            f"body={cur_body:.2f}(avg {av_body:.2f}) {'✅' if body_ok else '❌'} | "
            f"{'HIGH ✅' if high_vol else 'LOW ❌'}")
    log.info(f"📊 {info}")
    bot_status["volume_info"] = info
    return high_vol

# ══════════════════════════════════════════════════════════════
#  TWELVE DATA — WITH RETRY + ERROR ALERTS
# ══════════════════════════════════════════════════════════════
def td_fetch(interval, outputsize, target_deque):
    if not TD_KEY:
        log.warning("⚠️ TWELVE_DATA_KEY not set"); return False

    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : interval,
        "outputsize": outputsize,
        "apikey"    : TD_KEY,
        "order"     : "ASC",
    }

    for attempt in range(1, CFG["max_retries"] + 1):
        try:
            if not track_call():
                return False   # API exhausted

            resp = requests.get(
                f"{TD_BASE}/time_series",
                params=params, timeout=12
            )

            if resp.status_code == 429:
                tg_err_candle_fetch("Rate limited (429)", attempt)
                time.sleep(30 * attempt)
                continue

            if resp.status_code != 200:
                tg_err_candle_fetch(f"HTTP {resp.status_code}", attempt)
                time.sleep(10 * attempt)
                continue

            data   = resp.json()
            status = data.get("status", "")
            code   = data.get("code", 0)

            if status == "error":
                msg = data.get("message", "unknown error")
                if code == 401:
                    tg_err_candle_fetch("Invalid API key (401)", attempt)
                elif code == 429:
                    tg_err_candle_fetch("Rate limit exceeded", attempt)
                else:
                    tg_err_candle_fetch(msg, attempt)
                time.sleep(15 * attempt)
                continue

            values = data.get("values", [])
            if not values:
                tg_err_no_data()
                time.sleep(10)
                continue

            target_deque.clear()
            for bar in values:
                target_deque.append({
                    "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
                    "o"    : float(bar["open"]),
                    "h"    : float(bar["high"]),
                    "l"    : float(bar["low"]),
                    "c"    : float(bar["close"]),
                    "v"    : 0.0,
                })

            st["td_fail_count"] = 0   # reset on success
            log.info(f"📊 {len(target_deque)} {interval} candles loaded")
            return True

        except requests.exceptions.Timeout:
            tg_err_candle_fetch("Request timeout (12s)", attempt)
            time.sleep(10 * attempt)
        except requests.exceptions.ConnectionError:
            tg_err_candle_fetch("Network connection error", attempt)
            time.sleep(15 * attempt)
        except Exception as e:
            tg_err_candle_fetch(str(e)[:100], attempt)
            time.sleep(10 * attempt)

    st["td_fail_count"] += 1
    if st["td_fail_count"] >= 3:
        send_telegram(
            f"🚨 <b>Twelve Data Down — 3 consecutive failures</b>\n"
            f"📊 No candle data available\n"
            f"💡 Check: twelvedata.com status\n"
            f"⏰ {ist_now().strftime('%H:%M IST')}"
        )
    return False


def td_fetch_latest():
    if not TD_KEY: return False

    params = {
        "symbol"    : CFG["td_symbol"],
        "interval"  : "1min",
        "outputsize": 2,
        "apikey"    : TD_KEY,
        "order"     : "ASC",
    }

    try:
        if not track_call():
            return False

        resp   = requests.get(f"{TD_BASE}/time_series", params=params, timeout=12)

        if resp.status_code == 429:
            tg_err_candle_fetch("Rate limited (429)", 1)
            return False

        if resp.status_code != 200:
            tg_err_candle_fetch(f"HTTP {resp.status_code}", 1)
            return False

        data   = resp.json()
        if data.get("status") == "error":
            tg_err_candle_fetch(data.get("message","unknown"), 1)
            return False

        values = data.get("values", [])
        if not values:
            tg_err_no_data()
            return False

        bar    = values[-2] if len(values) >= 2 else values[-1]
        candle = {
            "epoch": int(pd.Timestamp(bar["datetime"]).timestamp()),
            "o"    : float(bar["open"]),
            "h"    : float(bar["high"]),
            "l"    : float(bar["low"]),
            "c"    : float(bar["close"]),
            "v"    : 0.0,
        }

        # Data quality checks
        if candle["h"] < candle["l"]:
            tg_err_bad_data(f"High < Low on candle @ {candle['c']:.2f}")
            return False
        if candle["h"] == candle["l"]:
            tg_err_bad_data("Zero range candle — market may be closed")
            return False

        # Stale candle check
        now_epoch = int(time.time())
        if (now_epoch - candle["epoch"]) > CFG["stale_candle_sec"]:
            tg_err_stale_candle()

        if not candles_1m or candles_1m[-1]["epoch"] != candle["epoch"]:
            candles_1m.append(candle)
            st["last_candle_epoch"]  = candle["epoch"]
            bot_status["last_candle_t"] = datetime.fromtimestamp(
                candle["epoch"], IST).strftime("%H:%M:%S IST")
            log.info(f"🕐 1m close={candle['c']:.2f} "
                     f"range={candle['h']-candle['l']:.2f}")

        st["td_fail_count"] = 0
        return True

    except requests.exceptions.Timeout:
        tg_err_candle_fetch("Latest candle timeout", 1)
        return False
    except Exception as e:
        tg_err_candle_fetch(str(e)[:100], 1)
        return False

# ══════════════════════════════════════════════════════════════
#  STRATEGY
# ══════════════════════════════════════════════════════════════
def run_strategy():
    global trade_active
    try:
        df = to_df(candles_1m)
        if len(df) < CFG["slow_ema"] + 20:
            log.info(f"⏳ Warming up: {len(df)}/{CFG['slow_ema']+20}")
            return None

        # Data quality gate
        if df["close"].isna().any():
            tg_err_bad_data("NaN values in close prices")
            return None
        if (df["high"] - df["low"]).min() < 0:
            tg_err_bad_data("Negative candle range detected")
            return None

        df1h = to_df(candles_1h)
        i    = len(df) - 1

        fast_v = float(ema(df["close"], CFG["fast_ema"]).iloc[-1])
        slow_v = float(ema(df["close"], CFG["slow_ema"]).iloc[-1])
        bull_t = fast_v > slow_v

        bull_b = bear_b = True
        if CFG["use_htf_bias"] and len(df1h) >= CFG["htf_ema"]:
            hv     = float(ema(df1h["close"], CFG["htf_ema"]).iloc[-1])
            cc     = float(df["close"].iloc[-1])
            bull_b = cc > hv
            bear_b = cc < hv

        atr_v  = float(calc_atr(df, CFG["atr_len"]).iloc[-1])

        # ATR sanity check
        if atr_v <= 0 or np.isnan(atr_v):
            tg_err_bad_data(f"Invalid ATR value: {atr_v}")
            return None

        high_v = check_volume(df) if CFG["use_volume"] else True

        n   = len(df)
        pdh = float(df["high"].iloc[-1440:-720].max()) if n >= 1440 \
              else float(df["high"].iloc[:max(1, n//2)].max())
        pdl = float(df["low"].iloc[-1440:-720].min())  if n >= 1440 \
              else float(df["low"].iloc[:max(1, n//2)].min())

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

        bc  = rbe and c > ph and c > o
        brc = rbs and c < pl and c < o
        if bc:  st["bull_choch_bar"] = i; log.info("🔄 Bull CHoCH")
        if brc: st["bear_choch_bar"] = i; log.info("🔄 Bear CHoCH")

        rbc  = (i - st["bull_choch_bar"]) <= CFG["choch_window"]
        rbrc = (i - st["bear_choch_bar"]) <= CFG["choch_window"]

        body = abs(c-o); rng = h-l
        be_l = c > o and c > po and o < pc and body > rng * 0.5
        be_s = c < o and c < po and o > pc and body > rng * 0.5

        long_conds = {
            "HTF Bias (Bull)"  : bull_b,
            "Local Trend (Bull)": bull_t,
            "Kill Zone"        : is_kz(),
            "Volume/Activity"  : high_v,
            "Bull Liq Sweep"   : rbs,
            "Bull CHoCH"       : rbc,
            "Bull Engulfing"   : be_l,
        }
        short_conds = {
            "HTF Bias (Bear)"  : bear_b,
            "Local Trend (Bear)": not bull_t,
            "Kill Zone"        : is_kz(),
            "Volume/Activity"  : high_v,
            "Bear Liq Sweep"   : rbe,
            "Bear CHoCH"       : rbrc,
            "Bear Engulfing"   : be_s,
        }

        total       = 7
        long_score  = sum(long_conds.values())
        short_score = sum(short_conds.values())

        log.info(
            f"⏳ LONG {long_score}/{total} | SHORT {short_score}/{total} | "
            f"htf:{'✅' if bull_b else '❌'} "
            f"tr:{'✅' if bull_t else '❌'} "
            f"vol:{'✅' if high_v else '❌'} "
            f"bs:{'✅' if rbs else '❌'} "
            f"be:{'✅' if rbe else '❌'} "
            f"bc:{'✅' if rbc else '❌'} "
            f"brc:{'✅' if rbrc else '❌'} "
            f"el:{'✅' if be_l else '❌'} "
            f"es:{'✅' if be_s else '❌'}"
        )

        est_long_sl  = l - atr_v * CFG["sl_atr_mult"]
        est_long_tp  = c + abs(c - est_long_sl) * CFG["rr_ratio"]
        est_short_sl = h + atr_v * CFG["sl_atr_mult"]
        est_short_tp = c - abs(est_short_sl - c) * CFG["rr_ratio"]

        # ── Telegram condition alerts ──
        if long_score >= 5 and st["last_bull_alert"] < 60 and not trade_active:
            st["last_bull_alert"] = 60
            tg_early_warning("🟢 LONG", long_conds, long_score, c, atr_v)

        if long_score >= 6 and st["last_bull_alert"] < 80 and not trade_active:
            st["last_bull_alert"] = 80
            tg_setup_forming("🟢 LONG", long_conds, long_score, c,
                             atr_v, est_long_sl, est_long_tp)

        if short_score >= 5 and st["last_bear_alert"] < 60 and not trade_active:
            st["last_bear_alert"] = 60
            tg_early_warning("🔴 SHORT", short_conds, short_score, c, atr_v)

        if short_score >= 6 and st["last_bear_alert"] < 80 and not trade_active:
            st["last_bear_alert"] = 80
            tg_setup_forming("🔴 SHORT", short_conds, short_score, c,
                             atr_v, est_short_sl, est_short_tp)

        if long_score  < 5: st["last_bull_alert"] = 0
        if short_score < 5: st["last_bear_alert"] = 0

        long_ok  = all(long_conds.values())  and not trade_active
        short_ok = all(short_conds.values()) and not trade_active

        if long_ok:
            sl = l - atr_v * CFG["sl_atr_mult"]
            tp = c + abs(c-sl) * CFG["rr_ratio"]
            st["last_bull_alert"] = 100
            return {"action":"BUY", "entry":c, "sl":sl, "tp":tp}

        if short_ok:
            sl = h + atr_v * CFG["sl_atr_mult"]
            tp = c - abs(sl-c) * CFG["rr_ratio"]
            st["last_bear_alert"] = 100
            return {"action":"SELL", "entry":c, "sl":sl, "tp":tp}

        return None

    except Exception as e:
        err = str(e)
        log.error(f"❌ Strategy error: {err}", exc_info=True)
        tg_err_strategy(err)
        return None

# ══════════════════════════════════════════════════════════════
#  PLACE TRADE — Full error handling on every MT5 response
# ══════════════════════════════════════════════════════════════
def place_trade(signal):
    global trade_active
    result = {}; done = threading.Event()
    otype  = 0 if signal["action"] == "BUY" else 1

    def on_open(ws):
        ws.send(json.dumps({"authorize": DERIV_TOKEN}))

    def on_message(ws, msg):
        global trade_active
        try:
            d = json.loads(msg); mt = d.get("msg_type")

            if mt == "authorize":
                if "error" in d:
                    log.error(f"Auth: {d['error']['message']}")
                    result["status"] = "auth_error"
                    tg_err_auth()
                    ws.close(); done.set(); return

                ws.send(json.dumps({
                    "mt5_new_order" : 1,
                    "login"         : int(MT5_LOGIN),
                    "symbol"        : CFG["mt5_symbol"],
                    "volume"        : CFG["lot_size"],
                    "order_type"    : otype,
                    "price"         : signal["entry"],
                    "stop_loss"     : round(signal["sl"], 2),
                    "take_profit"   : round(signal["tp"], 2),
                    "comment"       : "SMC+XAU v6",
                }))
                log.info(f"📤 {signal['action']} 0.01 lots "
                         f"entry:{signal['entry']:.2f} "
                         f"sl:{signal['sl']:.2f} tp:{signal['tp']:.2f}")

            elif mt == "mt5_new_order":
                if "error" in d:
                    err = d["error"]["message"]
                    log.error(f"MT5: {err}")
                    result["status"] = "error"
                    result["detail"] = err
                    tg_err_mt5_order(err)
                else:
                    oid = d.get("mt5_new_order", {}).get("order", "—")
                    log.info(f"✅ Trade placed! Order:{oid}")
                    result["status"] = "placed"
                    result["order"]  = oid
                    trade_active     = True
                    bot_status["last_signal"] = (
                        f"{signal['action']} @ {signal['entry']:.2f} | "
                        f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} | "
                        f"[{ist_now().strftime('%H:%M IST')}]"
                    )
                    tg_trade_placed(signal)
                ws.close(); done.set()

            elif mt == "error":
                err = d.get("error", {}).get("message", "Unknown WS error")
                log.error(f"WS error msg: {err}")
                result["status"] = "ws_error"
                result["detail"] = err
                tg_err_mt5_order(err)
                ws.close(); done.set()

        except json.JSONDecodeError:
            log.error("WS: invalid JSON response")
            ws.close(); done.set()
        except Exception as e:
            log.error(f"WS message handler error: {e}")
            ws.close(); done.set()

    def on_error(ws, e):
        log.error(f"WS error: {e}")
        result["status"] = "ws_error"
        done.set()

    def on_close(ws, code, msg):
        done.set()

    ws = websocket.WebSocketApp(
        DERIV_WS,
        on_open    = on_open,
        on_message = on_message,
        on_error   = on_error,
        on_close   = on_close,
    )
    threading.Thread(target=ws.run_forever, daemon=True).start()
    timed_out = not done.wait(timeout=20)

    if timed_out:
        tg_err_ws_timeout()
        result["status"] = "timeout"

    return result

# ══════════════════════════════════════════════════════════════
#  BOT LOOP
# ══════════════════════════════════════════════════════════════
def bot_loop():
    log.info("🤖 SMC+XAU Bot v6 starting...")

    # Check credentials on startup
    tg_err_missing_creds()

    # Initial candle load
    ok_1m = td_fetch("1min", CFG["candle_limit"], candles_1m)
    ok_1h = td_fetch("1h",   CFG["htf_limit"],    candles_1h)

    if not ok_1m or not ok_1h:
        send_telegram(
            f"🚨 <b>Startup Failed — Cannot load candles</b>\n"
            f"1m data: {'✅' if ok_1m else '❌'}\n"
            f"1H data: {'✅' if ok_1h else '❌'}\n"
            f"Check TWELVE_DATA_KEY in Railway variables\n"
            f"⏰ {ist_now().strftime('%H:%M IST')}"
        )

    bot_status["running"]    = True
    bot_status["candles_1m"] = len(candles_1m)
    log.info(f"✅ {len(candles_1m)} × 1m | {len(candles_1h)} × 1H loaded")

    tg_started()

    while True:
        try:
            # Fetch latest candle
            td_fetch_latest()
            bot_status["candles_1m"] = len(candles_1m)

            now = ist_now(); kz = kz_name()
            bot_status["kill_zone"]  = kz
            bot_status["last_check"] = now.strftime("%H:%M:%S IST")

            log.info(f"\n{'='*55}")
            log.info(f"⏰ {now.strftime('%H:%M IST')} | {kz} | "
                     f"calls={api_calls.get('count',0)}/800")

            # Kill zone transition alerts
            kz_active = is_kz()
            if kz_active and not st["in_kill_zone"]:
                st["in_kill_zone"] = True
                tg_kz_open(kz)
            elif not kz_active and st["in_kill_zone"]:
                st["in_kill_zone"] = False
                tg_kz_close(kz)

            if not kz_active:
                log.info("💤 Outside kill zone")
                bot_status["consecutive_errs"] = 0
                time.sleep(CFG["check_every_sec"])
                continue

            # Run strategy
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
                    log.info(f"🎯 DRY {sig['action']} @ {sig['entry']:.2f} "
                             f"[Missing: {', '.join(missing)}]")
                    bot_status["last_signal"] = \
                        f"DRY {sig['action']} @ {sig['entry']:.2f}"
                    send_telegram(
                        f"⚠️ <b>Signal — No Trade (Missing credentials)</b>\n"
                        f"📌 {sig['action']} @ {sig['entry']:.2f}\n"
                        f"Missing: {', '.join(missing)}\n"
                        f"⏰ {ist_now().strftime('%H:%M IST')}"
                    )

            # Refresh 1H at top of hour
            if now.minute == 0:
                td_fetch("1h", CFG["htf_limit"], candles_1h)
                log.info("🔄 1H refreshed")

            bot_status["consecutive_errs"] = 0

        except Exception as e:
            tb  = traceback.format_exc()
            err = str(e)
            log.error(f"❌ Loop error: {err}\n{tb}")
            bot_status["error"]             = err
            bot_status["consecutive_errs"] += 1

            tg_err_loop_crash(err, tb)

            # Alert on 3+ consecutive crashes
            if bot_status["consecutive_errs"] >= 3:
                tg_err_consecutive(bot_status["consecutive_errs"])

        time.sleep(CFG["check_every_sec"])

# ══════════════════════════════════════════════════════════════
#  FLASK STATUS PAGE
# ══════════════════════════════════════════════════════════════
flask_app = Flask(__name__)

@flask_app.route("/")
def status():
    rows = [
        ("Status",         "✅ Running" if bot_status["running"] else "⏳ Starting", "#3fb950"),
        ("IST Time",       ist_now().strftime("%H:%M:%S"),                           "#e3b341"),
        ("Kill Zone",      kz_name(),                                                "#e6edf3"),
        ("Last Check",     bot_status["last_check"],                                 "#e6edf3"),
        ("Last Candle",    bot_status["last_candle_t"],                              "#e6edf3"),
        ("1m Candles",     str(bot_status["candles_1m"]),                            "#e6edf3"),
        ("API Calls",      bot_status["api_calls"],                                  "#e3b341"),
        ("Volume",         bot_status["volume_info"],                                "#e6edf3"),
        ("Last Signal",    bot_status["last_signal"],                                "#58a6ff"),
        ("Last TG Alert",  bot_status["last_alert"],                                 "#a78bfa"),
        ("Trade Active",   "🔴 YES" if trade_active else "⚪ No",                   "#e6edf3"),
        ("Consec Errors",  str(bot_status["consecutive_errs"]),                      "#f85149" if bot_status["consecutive_errs"] > 0 else "#e6edf3"),
        ("Twelve Data",    "✅" if TD_KEY      else "❌ Add TWELVE_DATA_KEY",        "#e6edf3"),
        ("Deriv Token",    "✅" if DERIV_TOKEN else "❌ Add DERIV_API_TOKEN",        "#e6edf3"),
        ("MT5 Login",      MT5_LOGIN or "❌ Add MT5_LOGIN",                          "#e6edf3"),
        ("Telegram",       "✅" if TG_TOKEN and TG_CHAT else "❌ Add TG vars",       "#e6edf3"),
        ("Last Error",     bot_status["error"],                                      "#f85149"),
    ]
    rows_html = "".join(
        f'<tr><td style="padding:6px 12px;color:#8b949e;border-bottom:1px solid #21262d;white-space:nowrap">{l}</td>'
        f'<td style="padding:6px 12px;color:{c};border-bottom:1px solid #21262d;word-break:break-all">{v}</td></tr>'
        for l, v, c in rows
    )
    return f"""<html>
    <head><meta http-equiv="refresh" content="30"><title>SMC Bot v6</title></head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;
                 padding:30px;max-width:720px">
    <h2 style="color:#58a6ff">🤖 SMC+XAUUSD Bot v6</h2>
    <p style="color:#484f58;margin-top:-12px">
      0.01 lots · MT5 Demo · 1m · Full error handling
    </p>
    <table style="border-collapse:collapse;width:100%">{rows_html}</table>
    <br>
    <p style="color:#484f58;font-size:12px;line-height:1.9">
      🟡 London: 12:30–15:30 IST &nbsp;|&nbsp; 🔵 NY: 17:30–20:30 IST<br>
      Telegram: 🟡60% → 🟠80% → ✅trade → ❌errors<br>
      Auto-refreshes every 30s
    </p>
    </body></html>""", 200

@flask_app.route("/api/status")
def api_s():
    return jsonify({
        **bot_status,
        "kz"          : is_kz(),
        "ist"         : ist_now().strftime("%H:%M:%S"),
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

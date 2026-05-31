"""
SMC + XAUUSD Trading Bot v7
============================
Key improvements over v6:
  - API calls ONLY during kill zones (saves ~1000 calls/day)
  - 5-min warm-up fetch before kill zone opens
  - Hard stop after API limit — no spam, ONE alert only
  - Correct reset at 5:30 AM IST (Twelve Data actual reset)
  - Trade via NEW Deriv OTP flow (old ws.binaryws.com is dead)
  - Deriv account ID + App ID used for MT5 order placement

Daily API usage: ~390/800 calls ✅

Railway Variables needed:
  DERIV_API_TOKEN    → your Deriv PAT token
  DERIV_ACCOUNT_ID   → e.g. DOT92150478 (from developers.deriv.com playground)
  DERIV_APP_ID_NEW   → your registered app ID from developers.deriv.com
  MT5_LOGIN          → your MT5 login number e.g. 6130936
  TWELVE_DATA_KEY    → from twelvedata.com (free)
  TELEGRAM_BOT_TOKEN → from @BotFather
  TELEGRAM_CHAT_ID   → from @userinfobot
"""

import json, time, threading, logging, os, traceback
MAX_SIGNAL_AGE_SEC = 5     # signals older than this are treated as stale/expired
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
DERIV_ACCT    = os.environ.get("DERIV_ACCOUNT_ID", "")    # e.g. DOT92150478
DERIV_APP_ID  = os.environ.get("DERIV_APP_ID_NEW", "")    # from developers.deriv.com
MT5_LOGIN     = os.environ.get("MT5_LOGIN", "")
TD_KEY        = os.environ.get("TWELVE_DATA_KEY", "")
TG_TOKEN      = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TG_CHAT       = os.environ.get("TELEGRAM_CHAT_ID", "")

TD_BASE       = "https://api.twelvedata.com"
DERIV_REST    = "https://api.derivws.com"
IST           = timezone(timedelta(hours=5, minutes=30))

# ══════════════════════════════════════════════════════════════
#  CONFIG
# ══════════════════════════════════════════════════════════════
CFG = {
    # Strategy (matches Pine Script exactly)
    "fast_ema"       : 9,     # faster EMA for momentum (was 14)
    "slow_ema"       : 50,    # less lag than 140 on 1m chart
    "htf_ema"        : 50,
    "atr_len"        : 14,
    "sl_atr_mult"    : 1.5,   # tighter SL — anchored to swing level (was 2.0)
    "rr_ratio"       : 2.5,
    "min_sl_pts"     : 8.0,   # Deriv XAUUSD minimum stop distance
    "swing_len"      : 5,     # stronger swing points, fewer fakes (was 3)
    "choch_window"   : 3,     # CHoCH must be immediate — 3 bars max (was 5)
    "sweep_window"   : 5,     # only trade fresh sweeps — 5 bars max (was 10)
    "min_sweep_atr"  : 0.3,   # sweep must breach level by ≥0.3×ATR (new)
    "use_volume"     : True,
    "vol_lookback"   : 20,
    "range_mult"     : 1.1,
    "body_mult"      : 1.0,
    "use_htf_bias"   : True,
    "use_local_trend": True,
    "use_engulf"     : True,

    # Trade
    "mt5_symbol"     : "XAUUSD",
    "lot_size"       : 0.01,

    # Data
    "td_symbol"      : "XAU/USD",
    "candle_limit"   : 300,
    "htf_limit"      : 100,

    # Timing
    "check_every_sec": 60,
    "warmup_min"     : 5,      # fetch candles N mins before kill zone opens
    "api_warn_at"    : 700,    # warn at this many calls
    "api_hard_stop"  : 790,    # stop all fetching here

    # Kill zones IST (HHMM format)
    "london_open"    : 1230,
    "london_close"   : 1530,
    "ny_open"        : 1730,
    "ny_close"       : 2030,
}

# ══════════════════════════════════════════════════════════════
#  STATE
# ══════════════════════════════════════════════════════════════
candles_1m   = deque(maxlen=CFG["candle_limit"])
candles_1h   = deque(maxlen=CFG["htf_limit"])
trade_active = False

api_calls = {
    "count"     : 0,
    "reset_date": None,   # tracks the 5:30 AM IST cycle date
}

bot_status = {
    "running"        : False,
    "last_check"     : "—",
    "last_signal"    : "—",
    "kill_zone"      : "—",
    "candles_1m"     : 0,
    "error"          : "—",
    "api_calls"      : "0/800",
    "volume_info"    : "—",
    "last_alert"     : "—",
    "last_candle_t"  : "—",
    "consecutive_err": 0,
}

# ── Signal state — polled by MQL5 EA ──────────────────────────
# EA polls GET /signal and reads this dict.
current_signal = {
    "action"      : "NONE",   # "BUY", "SELL", or "NONE"
    "entry"       : 0.0,
    "sl"          : 0.0,
    "tp"          : 0.0,
    "timestamp"   : "—",      # IST time signal was generated
    "signal_epoch": 0,        # UTC Unix timestamp — EA uses this to reject stale signals
    "consumed"    : False,    # EA sets this True after placing trade (via /signal/consumed)
}

st = {
    # Strategy state
    "bull_sweep_bar" : -999, "bear_sweep_bar" : -999,
    "bull_choch_bar" : -999, "bear_choch_bar" : -999,
    "bull_sweep_lvl" : 0.0,  "bear_sweep_lvl" : 0.0,   # swept level for SL anchoring
    "asian_high"     : None, "asian_low"      : None,
    "last_sh"        : None, "last_sl"        : None,
    "last_bull_alert": 0,    "last_bear_alert": 0,
    "last_candle_epoch": 0,
    # Kill zone tracking
    "in_kill_zone"   : False,
    "warmed_up"      : False,   # initial candle load done for current KZ
    # API limit flags
    "api_warned"     : False,
    "api_exhausted"  : False,   # ONE alert only — no spam
    "api_warn_sent"  : False,
}

# ── Enhanced monitoring state ──────────────────────────────────
ea_status = {
    "last_seen"  : "Never",   # IST time EA last polled /signal
    "connected"  : False,     # True if polled within last 10 min
    "poll_count" : 0,         # total /signal calls since start
}

signal_history = []           # last 5 signals [{time, action, entry, sl, tp}]
trade_log      = []           # all closed trades today [{num, action, entry, sl, tp, result, profit, time_open, time_close}]
trade_counter  = 0            # increments on each new trade open

_sched = {
    "heartbeat_date"       : None,   # date of last 9 AM heartbeat
    "summary_date"         : None,   # date of last daily summary
    "reopen_alerted"       : False,  # market reopen alert sent this cycle
    "friday_warned"        : False,  # Friday close warning sent
    "ea_disconnect_alerted": False,  # EA disconnect alert sent
}

# ══════════════════════════════════════════════════════════════
#  TIME HELPERS
# ══════════════════════════════════════════════════════════════
def ist_now():
    return datetime.now(IST)

def t_int():
    """Current IST time as HHMM integer."""
    n = ist_now()
    return n.hour * 100 + n.minute

def is_kz():
    t = t_int()
    return (CFG["london_open"] <= t <= CFG["london_close"]) or \
           (CFG["ny_open"]     <= t <= CFG["ny_close"])

def is_warmup_window():
    """True if within warmup_min minutes BEFORE a kill zone opens."""
    t = t_int()
    wm = CFG["warmup_min"]
    def sub_min(hhmm, mins):
        h, m = divmod(hhmm, 100)
        dt = datetime(2000,1,1,h,m) - timedelta(minutes=mins)
        return dt.hour * 100 + dt.minute
    lon_pre = sub_min(CFG["london_open"], wm)
    ny_pre  = sub_min(CFG["ny_open"],     wm)
    return (lon_pre <= t < CFG["london_open"]) or \
           (ny_pre  <= t < CFG["ny_open"])

def kz_name():
    t = t_int()
    if CFG["london_open"] <= t <= CFG["london_close"]: return "🟡 London  12:30–15:30 IST"
    if CFG["ny_open"]     <= t <= CFG["ny_close"]:     return "🔵 NY      17:30–20:30 IST"
    if is_warmup_window():                              return "⏳ Warming up..."
    return "⚫ Outside kill zone"

def is_market_open():
    """
    Gold/Forex market closes Friday ~22:00 UTC (Sat 03:30 IST)
    and reopens Sunday ~22:00 UTC (Mon 03:30 IST).
    Returns False on Saturday all day and Sunday before 03:30 IST.
    """
    n   = ist_now()
    dow = n.weekday()   # 0=Mon … 4=Fri, 5=Sat, 6=Sun
    t   = n.hour * 100 + n.minute
    if dow == 5:          # Saturday — market fully closed
        return False
    if dow == 6 and t < 330:  # Sunday before 03:30 IST — still closed
        return False
    return True

def kz_countdown():
    """Returns a string showing time until the next kill zone."""
    n = ist_now()
    t = n.hour * 100 + n.minute
    if CFG["london_open"] <= t <= CFG["london_close"]: return "🟡 London active"
    if CFG["ny_open"]     <= t <= CFG["ny_close"]:     return "🔵 NY active"
    def mins_until(hhmm):
        h, m = divmod(hhmm, 100)
        tgt = n.replace(hour=h, minute=m, second=0, microsecond=0)
        if tgt <= n: tgt += timedelta(days=1)
        return int((tgt - n).total_seconds() // 60)
    lm, nm = mins_until(CFG["london_open"]), mins_until(CFG["ny_open"])
    if lm < nm:
        h, m = divmod(lm, 60); return f"⏳ London in {h}h {m}m"
    h, m = divmod(nm, 60);     return f"⏳ NY in {h}h {m}m"

def api_reset_date():
    """
    Twelve Data resets at ~5:30 AM IST daily.
    Returns the 'cycle date' — yesterday if before 5:30, today if after.
    """
    n = ist_now()
    reset_today = n.replace(hour=5, minute=30, second=0, microsecond=0)
    return n.date() if n >= reset_today else (n - timedelta(days=1)).date()

def to_df(q):
    df = pd.DataFrame(list(q))
    if df.empty: return df
    df = df.rename(columns={"o":"open","h":"high","l":"low","c":"close","v":"volume"})
    for col in ["open","high","low","close","volume"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    return df.reset_index(drop=True)

# ══════════════════════════════════════════════════════════════
#  TELEGRAM
# ══════════════════════════════════════════════════════════════
def tg(msg, silent=False):
    if not TG_TOKEN or not TG_CHAT:
        return False
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
            json={"chat_id": TG_CHAT, "text": msg,
                  "parse_mode": "HTML", "disable_notification": silent},
            timeout=8)
        ok = r.status_code == 200
        if ok:
            bot_status["last_alert"] = ist_now().strftime("%H:%M:%S IST")
            log.info(f"📱 TG: {msg[:60]}...")
        return ok
    except Exception as e:
        log.error(f"TG error: {e}")
        return False

def tg_started():
    tg(f"🤖 <b>SMC+XAU Bot Started</b>\n"
       f"<code>────────────────────</code>\n"
       f"Symbol  : XAUUSD · 1m · 0.01 lots\n"
       f"SL      : {CFG['sl_atr_mult']}× ATR  |  TP : 1:{CFG['rr_ratio']}\n"
       f"London  : 12:30 – 15:30 IST\n"
       f"NY      : 17:30 – 20:30 IST\n"
       f"<code>────────────────────</code>\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Bot is live 🟢")

def tg_kz_open(name):
    tg(f"🟢 <b>Kill Zone Open</b>\n"
       f"<code>────────────────────</code>\n"
       f"Session  : {name}\n"
       f"API used : {api_calls['count']} / 800\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Scanning XAUUSD 🔍", silent=True)

def tg_kz_close(name):
    tg(f"🔴 <b>Kill Zone Closed</b>\n"
       f"<code>────────────────────</code>\n"
       f"Session  : {name}\n"
       f"API used : {api_calls['count']} / 800\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Bot sleeping 💤", silent=True)

def tg_warn(direction, conds, score, price, atr_v):
    met     = [k for k,v in conds.items() if v]
    missing = [k for k,v in conds.items() if not v]
    tg(f"🟡 <b>Setup Forming  {direction}</b>\n"
       f"<code>────────────────────</code>\n"
       f"Price  : <b>{price:.2f}</b>  |  Score : {score}/7  |  ATR : {atr_v:.2f}\n"
       f"<code>────────────────────</code>\n"
       f"✅  {', '.join(met)}\n"
       f"⏳  Needs: {', '.join(missing)}\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_setup(direction, conds, score, price, atr_v, est_sl, est_tp):
    met     = [k for k,v in conds.items() if v]
    missing = [k for k,v in conds.items() if not v]
    tg(f"🟠 <b>High-Probability Setup  {direction}</b>\n"
       f"<code>────────────────────</code>\n"
       f"Price  : <b>{price:.2f}</b>  |  Score : <b>{score}/7</b>\n"
       f"Est SL : {est_sl:.2f}  |  Est TP : {est_tp:.2f}\n"
       f"<code>────────────────────</code>\n"
       f"✅  {', '.join(met)}\n"
       f"⏳  Needs: {', '.join(missing)}\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_trade(signal):
    direction = "🟢 LONG" if signal['action'] == "BUY" else "🔴 SHORT"
    risk  = abs(signal['entry'] - signal['sl'])
    rwrd  = abs(signal['tp']    - signal['entry'])
    tg(f"✅ <b>Trade Placed  {direction}</b>\n"
       f"<code>────────────────────</code>\n"
       f"Entry  : <b>{signal['entry']:.2f}</b>\n"
       f"SL     : {signal['sl']:.2f}  ({risk:.2f} pts)\n"
       f"TP     : {signal['tp']:.2f}  ({rwrd:.2f} pts)\n"
       f"Lots   : 0.01\n"
       f"<code>────────────────────</code>\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_err(title, detail, fix=""):
    msg = (f"⚠️ <b>{title}</b>\n"
           f"<code>────────────────────</code>\n"
           f"{detail}\n")
    if fix:
        msg += f"💡 {fix}\n"
    msg += f"⏰ {ist_now().strftime('%H:%M IST')}"
    tg(msg)

def tg_api_warn():
    tg(f"⚠️ <b>API Limit Warning</b>\n"
       f"<code>────────────────────</code>\n"
       f"Used   : <b>{api_calls['count']} / 800</b>\n"
       f"Resets : 05:30 IST daily\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)

def tg_api_exhausted():
    tg(f"🚨 <b>API Limit Reached — Bot Paused</b>\n"
       f"<code>────────────────────</code>\n"
       f"Used   : <b>{api_calls['count']} / 800</b>\n"
       f"Status : No more fetches today\n"
       f"Resets : <b>05:30 IST</b>  |  Auto-resumes\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_missing_creds():
    missing = [k for k,v in {
        "DERIV_API_TOKEN"   : DERIV_TOKEN,
        "DERIV_ACCOUNT_ID"  : DERIV_ACCT,
        "DERIV_APP_ID_NEW"  : DERIV_APP_ID,
        "MT5_LOGIN"         : MT5_LOGIN,
        "TWELVE_DATA_KEY"   : TD_KEY,
        "TELEGRAM_BOT_TOKEN": TG_TOKEN,
        "TELEGRAM_CHAT_ID"  : TG_CHAT,
    }.items() if not v]
    if missing:
        tg(f"⚠️ <b>Missing Environment Variables</b>\n"
           f"<code>────────────────────</code>\n"
           + "\n".join(f"  · {m}" for m in missing) +
           f"\n💡 Railway → Service → Variables")

def tg_heartbeat():
    tg(f"💓 <b>Bot Heartbeat</b>\n"
       f"<code>────────────────────</code>\n"
       f"API     : {api_calls['count']} / 800\n"
       f"Candles : {len(candles_1m)} × 1m\n"
       f"Next KZ : {kz_countdown()}\n"
       f"EA      : {'✅ Connected' if ea_status['connected'] else '❌ Not seen'}\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)

def tg_trade_running(action, entry, sl, tp, trade_num):
    direction = "🟢 LONG" if action == "BUY" else "🔴 SHORT"
    risk  = abs(entry - sl)
    rwrd  = abs(tp - entry)
    rr    = round(rwrd / risk, 1) if risk > 0 else 0
    tg(f"📊 <b>Trade #{trade_num} Running  {direction}</b>\n"
       f"<code>────────────────────</code>\n"
       f"Entry  : <b>{entry:.2f}</b>\n"
       f"SL     : {sl:.2f}  (−{risk:.2f} pts)\n"
       f"TP     : {tp:.2f}  (+{rwrd:.2f} pts)\n"
       f"R:R    : 1 : {rr}  |  Lots : 0.01\n"
       f"<code>────────────────────</code>\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Position active ⏳")

def tg_trade_closed(trade_num, action, entry, sl, tp, result, profit):
    direction = "LONG" if action == "BUY" else "SHORT"
    pnl_sign  = "+" if profit >= 0 else ""
    if result == "TP":
        header  = f"✅ <b>Trade #{trade_num} — Take Profit Hit</b>"
        outcome = "🎯 TP hit"
    elif result == "SL":
        header  = f"❌ <b>Trade #{trade_num} — Stop Loss Hit</b>"
        outcome = "🛑 SL hit"
    else:
        header  = f"🔄 <b>Trade #{trade_num} — Closed</b>"
        outcome = "Manual close"
    tg(f"{header}\n"
       f"<code>────────────────────</code>\n"
       f"Side   : {direction} XAUUSD\n"
       f"Entry  : {entry:.2f}  |  {outcome}\n"
       f"P&amp;L : <b>{pnl_sign}{profit:.2f} USD</b>\n"
       f"<code>────────────────────</code>\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_daily_summary():
    today_str = ist_now().strftime('%d %b %Y')
    if trade_log:
        lines     = []
        total_pnl = 0.0
        wins = losses = 0
        for t in trade_log:
            sign  = "+" if t['profit'] >= 0 else ""
            icon  = "✅" if t['result'] == "TP" else ("❌" if t['result'] == "SL" else "🔄")
            side  = "L" if t['action'] == "BUY" else "S"
            lines.append(f"  {icon} #{t['num']} {side} @ {t['entry']:.2f}  →  {sign}{t['profit']:.2f} USD")
            total_pnl += t['profit']
            if t['result'] == "TP": wins += 1
            elif t['result'] == "SL": losses += 1
        total    = wins + losses
        win_pct  = f"{round(wins/total*100)}%" if total else "—"
        net_sign = "+" if total_pnl >= 0 else ""
        trades_text    = "\n".join(lines)
        summary_footer = (f"\n<code>────────────────────</code>\n"
                          f"Record : {wins}W / {losses}L  ({win_pct})\n"
                          f"Net P&amp;L : <b>{net_sign}{total_pnl:.2f} USD</b>")
    else:
        trades_text    = "  No trades today"
        summary_footer = ""
    tg(f"📋 <b>Daily Summary — {today_str}</b>\n"
       f"<code>────────────────────</code>\n"
       f"API used : {api_calls['count']} / 800\n"
       f"EA       : {'✅ Connected' if ea_status['connected'] else '❌ Check MT5'}\n"
       f"<code>────────────────────</code>\n"
       f"Trades:\n{trades_text}{summary_footer}")

def tg_market_reopen():
    tg(f"🟢 <b>Market Open — New Week</b>\n"
       f"<code>────────────────────</code>\n"
       f"Date    : {ist_now().strftime('%A, %d %b')}\n"
       f"London  : 12:30 IST  |  NY : 17:30 IST\n"
       f"API     : {api_calls['count']} / 800\n"
       f"<code>────────────────────</code>\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Ready 🚀")

def tg_friday_warning():
    tg(f"⏳ <b>Market Closes Today — Friday</b>\n"
       f"<code>────────────────────</code>\n"
       f"Closes  : ~03:30 IST Saturday\n"
       f"API     : {api_calls['count']} / 800 used\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}  |  Weekend mode soon 💤", silent=True)

def tg_ea_disconnect():
    tg(f"⚠️ <b>EA Disconnected</b>\n"
       f"<code>────────────────────</code>\n"
       f"No poll in 10+ minutes\n"
       f"Last seen : {ea_status['last_seen']}\n"
       f"<code>────────────────────</code>\n"
       f"💡 Check MetaTrader 5 is running\n"
       f"💡 EA must be attached to XAUUSD")

# ══════════════════════════════════════════════════════════════
#  API CALL TRACKER — hard stop, no spam
# ══════════════════════════════════════════════════════════════
def track_call():
    """
    Returns True if call is allowed, False if exhausted.
    Resets counter at 5:30 AM IST daily.
    Only sends ONE exhausted alert.
    """
    # Reset check (5:30 AM IST cycle)
    cycle = api_reset_date()
    if api_calls["reset_date"] != cycle:
        api_calls["count"]      = 0
        api_calls["reset_date"] = cycle
        st["api_warned"]        = False
        st["api_warn_sent"]     = False
        st["api_exhausted"]     = False
        log.info("🔄 API call counter reset (5:30 AM IST cycle)")

    # Already exhausted — don't call, don't alert again
    if st["api_exhausted"]:
        return False

    api_calls["count"] += 1
    bot_status["api_calls"] = f"{api_calls['count']}/800"

    # Warning threshold
    if api_calls["count"] >= CFG["api_warn_at"] and not st["api_warn_sent"]:
        st["api_warn_sent"] = True
        tg_api_warn()

    # Hard stop
    if api_calls["count"] >= CFG["api_hard_stop"]:
        st["api_exhausted"] = True
        tg_api_exhausted()   # ← sent ONCE only
        return False

    return True

# ══════════════════════════════════════════════════════════════
#  INDICATORS
# ══════════════════════════════════════════════════════════════
def ema(s, p): return s.ewm(span=p, adjust=False).mean()

def calc_atr(df, p):
    h,l,pc = df["high"],df["low"],df["close"].shift(1)
    return pd.concat([h-l,(h-pc).abs(),(l-pc).abs()],axis=1).max(axis=1)\
             .ewm(span=p,adjust=False).mean()

def pvt_h(s, n):
    v,r = s.values, np.nan
    for i in range(n, len(v)-n):
        if all(v[i]>=v[i-j] for j in range(1,n+1)) and \
           all(v[i]>=v[i+j] for j in range(1,n+1)):
            r = v[i]
    return r

def pvt_l(s, n):
    v,r = s.values, np.nan
    for i in range(n, len(v)-n):
        if all(v[i]<=v[i-j] for j in range(1,n+1)) and \
           all(v[i]<=v[i+j] for j in range(1,n+1)):
            r = v[i]
    return r

def check_volume(df):
    lb  = CFG["vol_lookback"]
    rng = df["high"] - df["low"]
    bdy = (df["close"] - df["open"]).abs()
    cr  = float(rng.iloc[-1])
    ar  = float(rng.rolling(lb).mean().iloc[-1]) or cr
    cb  = float(bdy.iloc[-1])
    ab  = float(bdy.rolling(lb).mean().iloc[-1]) or cb
    if cr == 0:
        return False
    rok = cr > ar * CFG["range_mult"]
    bok = cb > ab * CFG["body_mult"]
    ok  = rok and bok
    info = (f"range={cr:.2f}(avg {ar:.2f}) {'✅' if rok else '❌'} | "
            f"body={cb:.2f}(avg {ab:.2f}) {'✅' if bok else '❌'} | "
            f"{'HIGH ✅' if ok else 'LOW ❌'}")
    log.info(f"📊 {info}")
    bot_status["volume_info"] = info
    return ok

# ══════════════════════════════════════════════════════════════
#  TWELVE DATA — only fetch when allowed
# ══════════════════════════════════════════════════════════════
def td_fetch(interval, outputsize, target_deque):
    if st["api_exhausted"] or not TD_KEY:
        return False
    params = {"symbol":CFG["td_symbol"],"interval":interval,
              "outputsize":outputsize,"apikey":TD_KEY,"order":"ASC"}
    for attempt in range(1, 4):
        try:
            if not track_call():
                return False
            r = requests.get(f"{TD_BASE}/time_series", params=params, timeout=12)
            if r.status_code == 429:
                tg_err("Rate Limited (429)", "Twelve Data rate limit hit", "Wait 60s"); time.sleep(30*attempt); continue
            if r.status_code != 200:
                tg_err(f"API HTTP {r.status_code}", "Twelve Data error", "Check API key"); time.sleep(10*attempt); continue
            d = r.json()
            if d.get("status") == "error":
                tg_err("Twelve Data Error", d.get("message","unknown")); time.sleep(15); continue
            vals = d.get("values",[])
            if not vals:
                tg_err("No Candle Data", "Twelve Data returned empty — market may be closed"); return False
            target_deque.clear()
            for b in vals:
                target_deque.append({"epoch":int(pd.Timestamp(b["datetime"]).timestamp()),
                                     "o":float(b["open"]),"h":float(b["high"]),
                                     "l":float(b["low"]), "c":float(b["close"]),"v":0.0})
            log.info(f"📊 {len(target_deque)} {interval} candles loaded")
            return True
        except requests.exceptions.Timeout:
            tg_err("Candle Fetch Timeout", f"Attempt {attempt}/3"); time.sleep(10*attempt)
        except Exception as e:
            tg_err("Candle Fetch Error", str(e)[:100]); time.sleep(10*attempt)
    return False


def td_fetch_latest():
    """Fetch latest 1m candle — ONLY call this during kill zone or warmup."""
    if st["api_exhausted"] or not TD_KEY:
        return False
    params = {"symbol":CFG["td_symbol"],"interval":"1min",
              "outputsize":2,"apikey":TD_KEY,"order":"ASC"}
    try:
        if not track_call():
            return False
        r    = requests.get(f"{TD_BASE}/time_series", params=params, timeout=12)
        if r.status_code == 429:
            return False
        if r.status_code != 200:
            return False
        vals = r.json().get("values",[])
        if not vals:
            return False
        b = vals[-2] if len(vals)>=2 else vals[-1]
        c = {"epoch":int(pd.Timestamp(b["datetime"]).timestamp()),
             "o":float(b["open"]),"h":float(b["high"]),
             "l":float(b["low"]), "c":float(b["close"]),"v":0.0}
        # Quality checks
        if c["h"] < c["l"]: return False
        if c["h"] == c["l"]:
            tg_err("Bad Candle", "Zero range — market may be closed", silent=True); return False
        if not candles_1m or candles_1m[-1]["epoch"] != c["epoch"]:
            candles_1m.append(c)
            st["last_candle_epoch"] = c["epoch"]
            bot_status["last_candle_t"] = datetime.fromtimestamp(c["epoch"],IST).strftime("%H:%M:%S IST")
            log.info(f"🕐 1m close={c['c']:.2f} range={c['h']-c['l']:.2f}")
        return True
    except Exception as e:
        log.error(f"td_latest error: {e}")
        return False

# ══════════════════════════════════════════════════════════════
#  STRATEGY
# ══════════════════════════════════════════════════════════════
def run_strategy():
    global trade_active
    try:
        df = to_df(candles_1m)
        if len(df) < CFG["slow_ema"] + 20:
            log.info(f"⏳ Warming up: {len(df)}/{CFG['slow_ema']+20}"); return None

        # Data quality
        if df["close"].isna().any(): return None

        df1h = to_df(candles_1h)
        i    = len(df) - 1

        fast_v = float(ema(df["close"],CFG["fast_ema"]).iloc[-1])
        slow_v = float(ema(df["close"],CFG["slow_ema"]).iloc[-1])
        bull_t = fast_v > slow_v

        bull_b = bear_b = True
        if CFG["use_htf_bias"] and len(df1h) >= CFG["htf_ema"]:
            hv     = float(ema(df1h["close"],CFG["htf_ema"]).iloc[-1])
            cc     = float(df["close"].iloc[-1])
            bull_b = cc > hv; bear_b = cc < hv

        atr_v = float(calc_atr(df,CFG["atr_len"]).iloc[-1])
        if atr_v <= 0 or np.isnan(atr_v): return None

        high_v = check_volume(df) if CFG["use_volume"] else True

        n   = len(df)
        pdh = float(df["high"].iloc[-1440:-720].max()) if n>=1440 else float(df["high"].iloc[:max(1,n//2)].max())
        pdl = float(df["low"].iloc[-1440:-720].min())  if n>=1440 else float(df["low"].iloc[:max(1,n//2)].min())

        sw  = CFG["swing_len"]
        lsh = pvt_h(df["high"],sw) if len(df)>=sw*2+5 else st["last_sh"]
        lsl = pvt_l(df["low"], sw) if len(df)>=sw*2+5 else st["last_sl"]
        st["last_sh"]=lsh; st["last_sl"]=lsl

        c,o = float(df["close"].iloc[-1]),float(df["open"].iloc[-1])
        h,l = float(df["high"].iloc[-1]), float(df["low"].iloc[-1])
        ph  = float(df["high"].iloc[-2]); pl  = float(df["low"].iloc[-2])
        po  = float(df["open"].iloc[-2]); pc  = float(df["close"].iloc[-2])

        # ── Sweeps — must breach level by minimum ATR amount (filters tiny fakeouts) ──
        sb = be = False
        min_sw = atr_v * CFG["min_sweep_atr"]
        if st["asian_low"]  and l < st["asian_low"]  and (st["asian_low"]  - l) >= min_sw: sb = True
        if st["asian_high"] and h > st["asian_high"] and (h - st["asian_high"]) >= min_sw: be = True
        if l < pdl and (pdl - l) >= min_sw: sb = True
        if h > pdh and (h - pdh) >= min_sw: be = True
        # Swing sweeps — price must reject back inside the level (wick sweep)
        if lsl and not np.isnan(lsl) and l < lsl and c > lsl and (lsl - l) >= min_sw: sb = True
        if lsh and not np.isnan(lsh) and h > lsh and c < lsh and (h - lsh) >= min_sw: be = True

        # Track the swept level for SL anchoring
        if sb:
            st["bull_sweep_bar"] = i
            st["bull_sweep_lvl"] = lsl if (lsl and not np.isnan(lsl) and l < lsl) else pdl
            log.info(f"🔍 Bull sweep — level={st['bull_sweep_lvl']:.2f}")
        if be:
            st["bear_sweep_bar"] = i
            st["bear_sweep_lvl"] = lsh if (lsh and not np.isnan(lsh) and h > lsh) else pdh
            log.info(f"🔍 Bear sweep — level={st['bear_sweep_lvl']:.2f}")

        rbs = (i - st["bull_sweep_bar"]) <= CFG["sweep_window"]
        rbe = (i - st["bear_sweep_bar"]) <= CFG["sweep_window"]

        bc  = rbe and c > ph and c > o
        brc = rbs and c < pl and c < o
        if bc:  st["bull_choch_bar"] = i; log.info("🔄 Bull CHoCH")
        if brc: st["bear_choch_bar"] = i; log.info("🔄 Bear CHoCH")

        rbc  = (i - st["bull_choch_bar"]) <= CFG["choch_window"]
        rbrc = (i - st["bear_choch_bar"]) <= CFG["choch_window"]

        body = abs(c - o); rng = h - l
        # Stricter engulf: close must go BEYOND prior candle's open (full body engulf)
        be_l = (c > o and c > po and body > rng * 0.5 and c > pc)   # bull: closes above prior open
        be_s = (c < o and c < po and body > rng * 0.5 and c < pc)   # bear: closes below prior open

        long_conds  = {"HTF Bias (Bull)":bull_b,"Local Trend (Bull)":bull_t,
                       "Kill Zone":is_kz(),"Volume":high_v,
                       "Bull Sweep":rbs,"Bull CHoCH":rbc,"Bull Engulf":be_l}
        short_conds = {"HTF Bias (Bear)":bear_b,"Local Trend (Bear)":not bull_t,
                       "Kill Zone":is_kz(),"Volume":high_v,
                       "Bear Sweep":rbe,"Bear CHoCH":rbrc,"Bear Engulf":be_s}

        ls = sum(long_conds.values())
        ss = sum(short_conds.values())

        log.info(f"⏳ LONG {ls}/7 | SHORT {ss}/7 | "
                 f"htf:{'✅' if bull_b else '❌'} tr:{'✅' if bull_t else '❌'} "
                 f"vol:{'✅' if high_v else '❌'} bs:{'✅' if rbs else '❌'} "
                 f"be:{'✅' if rbe else '❌'} bc:{'✅' if rbc else '❌'} "
                 f"brc:{'✅' if rbrc else '❌'} el:{'✅' if be_l else '❌'} "
                 f"es:{'✅' if be_s else '❌'}")

        esl=l-atr_v*CFG["sl_atr_mult"]; etp=c+abs(c-esl)*CFG["rr_ratio"]
        essl=h+atr_v*CFG["sl_atr_mult"]; estp=c-abs(essl-c)*CFG["rr_ratio"]

        # Condition alerts — only SETUP FORMING (6/7+), no early warnings
        if ls>=6 and st["last_bull_alert"]<80 and not trade_active:
            st["last_bull_alert"]=80; tg_setup("🟢 LONG",long_conds,ls,c,atr_v,esl,etp)
        if ss>=6 and st["last_bear_alert"]<80 and not trade_active:
            st["last_bear_alert"]=80; tg_setup("🔴 SHORT",short_conds,ss,c,atr_v,essl,estp)

        if ls<6: st["last_bull_alert"]=0
        if ss<6: st["last_bear_alert"]=0

        if all(long_conds.values()) and not trade_active:
            # ── SL anchored to swept swing low (not current bar low) ──
            sweep_lvl = st.get("bull_sweep_lvl", l)
            sl = sweep_lvl - atr_v * CFG["sl_atr_mult"]
            tp = c + abs(c - sl) * CFG["rr_ratio"]
            min_dist = CFG["min_sl_pts"]
            if (c - sl) < min_dist:
                sl = round(c - min_dist, 2)
                tp = round(c + min_dist * CFG["rr_ratio"], 2)
            sl = round(sl, 2); tp = round(tp, 2)
            st["last_bull_alert"] = 100
            log.info(f"🚀 LONG entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f} risk:{c-sl:.2f}pts")
            sig = {"action": "BUY", "entry": c, "sl": sl, "tp": tp}
            _update_signal(sig)
            return sig

        if all(short_conds.values()) and not trade_active:
            # ── SL anchored to swept swing high (not current bar high + ATR) ──
            sweep_lvl = st.get("bear_sweep_lvl", h)
            sl = sweep_lvl + atr_v * CFG["sl_atr_mult"]
            tp = c - abs(sl - c) * CFG["rr_ratio"]
            min_dist = CFG["min_sl_pts"]
            if (sl - c) < min_dist:
                sl = round(c + min_dist, 2)
                tp = round(c - min_dist * CFG["rr_ratio"], 2)
            sl = round(sl, 2); tp = round(tp, 2)
            st["last_bear_alert"] = 100
            log.info(f"🔻 SHORT entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f} risk:{sl-c:.2f}pts")
            sig = {"action": "SELL", "entry": c, "sl": sl, "tp": tp}
            _update_signal(sig)
            return sig

        # No signal — reset to NONE if previous was consumed
        if current_signal["consumed"]:
            _clear_signal()

        return None

    except Exception as e:
        log.error(f"Strategy error: {e}", exc_info=True)
        tg_err("Strategy Error", str(e)[:150])
        return None

# ══════════════════════════════════════════════════════════════
#  PLACE TRADE — NEW DERIV OTP FLOW
#  Step 1: REST call → get authenticated WebSocket URL
#  Step 2: Connect to that URL → send mt5_new_order
# ══════════════════════════════════════════════════════════════
def get_deriv_ws_url():
    """
    Call Deriv REST API to get an authenticated WebSocket URL.
    Returns the wss:// URL or None on failure.
    """
    if not DERIV_TOKEN or not DERIV_ACCT or not DERIV_APP_ID:
        tg_err("Trade Config Error",
               "Missing DERIV_ACCOUNT_ID or DERIV_APP_ID_NEW in Railway vars",
               "Add them in Railway → Variables")
        return None
    try:
        url  = f"{DERIV_REST}/trading/v1/options/accounts/{DERIV_ACCT}/otp"
        hdrs = {"Authorization": f"Bearer {DERIV_TOKEN}",
                "Deriv-App-ID" : DERIV_APP_ID,
                "Content-Type" : "application/json"}
        r = requests.post(url, headers=hdrs, timeout=10)
        if r.status_code == 401:
            tg_err("Deriv Auth Failed",
                   "DERIV_API_TOKEN rejected",
                   "Check token on developers.deriv.com → API Tokens")
            return None
        if r.status_code == 400:
            tg_err("Deriv Bad Request",
                   f"Invalid account ID: {DERIV_ACCT}",
                   "Check DERIV_ACCOUNT_ID in Railway vars")
            return None
        if r.status_code != 200:
            tg_err(f"Deriv REST Error {r.status_code}", r.text[:100])
            return None
        ws_url = r.json().get("data",{}).get("url")
        if not ws_url:
            tg_err("Deriv OTP Error", "No WebSocket URL in response")
            return None
        log.info(f"✅ Got authenticated WS URL")
        return ws_url
    except Exception as e:
        tg_err("Deriv OTP Request Failed", str(e)[:100])
        return None


def place_trade(signal):
    global trade_active
    result = {}; done = threading.Event()
    otype  = 0 if signal["action"]=="BUY" else 1

    # Step 1 — get authenticated WS URL
    ws_url = get_deriv_ws_url()
    if not ws_url:
        return {"status":"no_ws_url"}

    # Step 2 — connect and place order
    def on_open(ws):
        log.info("🔗 Connected to Deriv WS (new OTP endpoint)")
        # New endpoint is pre-authenticated — send order directly
        ws.send(json.dumps({
            "mt5_new_order" : 1,
            "login"         : int(MT5_LOGIN),
            "symbol"        : CFG["mt5_symbol"],
            "volume"        : CFG["lot_size"],
            "order_type"    : otype,
            "price"         : signal["entry"],
            "stop_loss"     : round(signal["sl"],2),
            "take_profit"   : round(signal["tp"],2),
            "comment"       : "SMC+XAU v7",
        }))
        log.info(f"📤 {signal['action']} 0.01 lots @ {signal['entry']:.2f} "
                 f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f}")

    def on_message(ws, msg):
        global trade_active
        try:
            d  = json.loads(msg)
            mt = d.get("msg_type")

            if mt == "mt5_new_order":
                if "error" in d:
                    err = d["error"]["message"]
                    log.error(f"MT5 error: {err}")
                    result["status"]="error"; result["detail"]=err
                    # Specific guidance
                    guides = {
                        "invalid login"      :"Check MT5_LOGIN in Railway vars",
                        "trade is disabled"  :"Enable trading on Deriv MT5 account",
                        "not enough money"   :"Reset demo balance on Deriv",
                        "market is closed"   :"Gold trades Mon-Fri only",
                        "invalid stops"      :"SL/TP too close — ATR may be small",
                        "off quotes"         :"No price quote — market may be closed",
                    }
                    fix = next((v for k,v in guides.items() if k in err.lower()), "Check Deriv MT5 account")
                    tg_err("MT5 Order Failed", err, fix)
                else:
                    global trade_counter
                    oid = d.get("mt5_new_order",{}).get("order","—")
                    log.info(f"✅ Trade placed! Order: {oid}")
                    result["status"]="placed"; result["order"]=oid
                    trade_active = True
                    trade_counter += 1
                    bot_status["open_trade"] = {
                        "num": trade_counter,
                        "action": signal["action"],
                        "entry": signal["entry"],
                        "sl": signal["sl"],
                        "tp": signal["tp"],
                        "time_open": ist_now().strftime("%H:%M IST"),
                        "open_epoch": int(time.time()),
                        "is_simulated": False
                    }
                    bot_status["last_signal"] = (
                        f"{signal['action']} @ {signal['entry']:.2f} "
                        f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} "
                        f"[{ist_now().strftime('%H:%M IST')}]")
                    tg_trade(signal)
                ws.close(); done.set()

            elif mt == "authorize":
                # Some WS versions still send auth — handle gracefully
                if "error" in d:
                    tg_err("Deriv Auth Failed",
                           d["error"]["message"],
                           "Regenerate token on developers.deriv.com")
                    result["status"]="auth_error"
                    ws.close(); done.set()
                # else: authorized OK, wait for mt5_new_order response

            elif mt == "error":
                err = d.get("error",{}).get("message","unknown")
                log.error(f"WS error msg: {err}")
                tg_err("Deriv WS Error", err)
                result["status"]="ws_error"
                ws.close(); done.set()

        except Exception as e:
            log.error(f"WS handler error: {e}")
            ws.close(); done.set()

    def on_error(ws, e):
        log.error(f"WS error: {e}")
        result["status"]="ws_error"; done.set()

    def on_close(ws, code, msg):
        done.set()

    ws = websocket.WebSocketApp(ws_url,
         on_open=on_open, on_message=on_message,
         on_error=on_error, on_close=on_close)
    threading.Thread(target=ws.run_forever, daemon=True).start()

    timed_out = not done.wait(timeout=20)
    if timed_out:
        tg_err("Deriv WS Timeout", "No response in 20s — trade may not have been placed",
               "Check your Deriv account manually")
        result["status"]="timeout"

    return result


# ══════════════════════════════════════════════════════════════
#  TRADE PERFORMANCE SIMULATOR (TP/SL fallback/dry run)
# ══════════════════════════════════════════════════════════════
def check_active_trade_performance():
    global trade_active
    open_trade = bot_status.get("open_trade")
    if not trade_active or not open_trade:
        return

    is_simulated = open_trade.get("is_simulated", False)
    ea_connected = ea_status.get("connected", False)

    # If the trade is live and the EA is connected, let the EA handle the trade closure
    if not is_simulated and ea_connected:
        return

    if not candles_1m:
        return

    open_epoch = open_trade.get("open_epoch", 0)
    action     = open_trade.get("action")
    entry      = open_trade.get("entry", 0.0)
    sl         = open_trade.get("sl", 0.0)
    tp         = open_trade.get("tp", 0.0)
    trade_num  = open_trade.get("num", 0)

    hit_tp = False
    hit_sl = False
    close_price = 0.0
    hit_time = None

    # Check candles closed after or near the open epoch
    for c in list(candles_1m):
        if c["epoch"] < open_epoch - 30:
            continue

        high = c["h"]
        low  = c["l"]

        if action == "BUY":
            # SL hit check first (conservative)
            if low <= sl:
                hit_sl = True
                close_price = sl
                hit_time = c["epoch"]
                break
            elif high >= tp:
                hit_tp = True
                close_price = tp
                hit_time = c["epoch"]
                break
        elif action == "SELL":
            # SL hit check first (conservative)
            if high >= sl:
                hit_sl = True
                close_price = sl
                hit_time = c["epoch"]
                break
            elif low <= tp:
                hit_tp = True
                close_price = tp
                hit_time = c["epoch"]
                break

    if hit_tp or hit_sl:
        result_str = "TP" if hit_tp else "SL"
        profit = (close_price - entry) if action == "BUY" else (entry - close_price)
        # Lot size is 0.01; XAUUSD contract is 100oz. So 0.01 lots = 1oz.
        # Profit in USD = point change.
        profit = round(profit, 2)

        log.info(f"🔮 Simulated Trade #{trade_num} hit {result_str} at price {close_price:.2f}, profit: {profit:.2f} USD")

        # Update state
        trade_active = False
        bot_status["open_trade"] = {}
        _clear_signal()

        # Log closed trade
        trade_log.append({
            "num"       : trade_num,
            "action"    : action,
            "entry"     : entry,
            "sl"        : sl,
            "tp"        : tp,
            "result"    : result_str,
            "profit"    : profit,
            "time_open" : open_trade.get("time_open", "—"),
            "time_close": datetime.fromtimestamp(hit_time, IST).strftime("%H:%M IST") if hit_time else ist_now().strftime("%H:%M IST"),
        })

        header_prefix = "🔮 [Simulated] " if is_simulated else "⚠️ [EA Offline Fallback] "
        direction = "LONG" if action == "BUY" else "SHORT"
        pnl_sign  = "+" if profit >= 0 else ""
        if result_str == "TP":
            header  = f"{header_prefix}<b>Trade #{trade_num} — Take Profit Hit</b>"
            outcome = "🎯 TP hit"
        else:
            header  = f"{header_prefix}<b>Trade #{trade_num} — Stop Loss Hit</b>"
            outcome = "🛑 SL hit"

        tg(f"{header}\n"
           f"<code>────────────────────</code>\n"
           f"Side   : {direction} XAUUSD\n"
           f"Entry  : {entry:.2f}  |  {outcome}\n"
           f"P&amp;L : <b>{pnl_sign}{profit:.2f} USD</b> (Est)\n"
           f"<code>────────────────────</code>\n"
           f"⏰ {ist_now().strftime('%H:%M IST')}")

        tg(f"🔄 <b>Bot Resumed</b> — watching for next signal\n"
           f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)


# ══════════════════════════════════════════════════════════════
#  BOT LOOP — efficient, KZ-aware
# ══════════════════════════════════════════════════════════════
def bot_loop():
    global trade_active
    log.info("🤖 SMC+XAU Bot v7 starting...")
    tg_missing_creds()

    # Initial candle load (only if in KZ or warmup window)
    # Otherwise defer until first KZ/warmup
    if is_kz() or is_warmup_window():
        td_fetch("1min", CFG["candle_limit"], candles_1m)
        td_fetch("1h",   CFG["htf_limit"],    candles_1h)
        st["warmed_up"] = True

    bot_status["running"]    = True
    bot_status["candles_1m"] = len(candles_1m)
    log.info(f"✅ Bot ready | {len(candles_1m)} × 1m candles | {len(candles_1h)} × 1H candles")
    tg_started()

    _weekend_alerted = False   # track one-time weekend alert

    while True:
        try:
            now = ist_now()

            # ── Weekend / market-closed guard ──────────────────────
            if not is_market_open():
                dow_name = now.strftime("%A")
                log.info(f"🔴 Market closed ({dow_name}) — sleeping 30 min")
                bot_status["kill_zone"]  = f"🔴 Market Closed ({dow_name})"
                bot_status["last_check"] = now.strftime("%H:%M:%S IST")
                if not _weekend_alerted:
                    tg(f"🔴 <b>Market Closed — Weekend</b>\n"
                       f"━━━━━━━━━━━━━━━━\n"
                       f"📅 {dow_name} — Gold market is closed\n"
                       f"💤 Bot sleeping, no signals will be sent\n"
                       f"⏰ Reopens Monday ~03:30 IST\n"
                       f"🤖 SMC+XAU Bot v7", silent=True)
                    _weekend_alerted = True
                time.sleep(1800)   # sleep 30 minutes, check again
                continue
            else:
                _weekend_alerted = False   # reset when market reopens
            # ───────────────────────────────────────────────────────

            # ── Scheduling checks (heartbeat / summary / alerts) ──
            today = now.date()
            ti    = now.hour * 100 + now.minute
            dow   = now.weekday()   # 0=Mon … 4=Fri, 5=Sat, 6=Sun

            # 9 AM heartbeat
            if now.hour == 9 and now.minute < 2 and _sched["heartbeat_date"] != today:
                _sched["heartbeat_date"] = today
                tg_heartbeat()

            # Daily summary after NY closes (20:32 IST)
            if ti >= 2032 and _sched["summary_date"] != today:
                _sched["summary_date"] = today
                tg_daily_summary()

            # Friday close warning at 02:55 IST
            if dow == 4 and ti >= 255 and ti < 340 and not _sched["friday_warned"]:
                _sched["friday_warned"] = True
                tg_friday_warning()
            if dow != 4:
                _sched["friday_warned"] = False

            # Market reopen alert Sunday 03:30+ IST
            if dow == 6 and ti >= 330 and not _sched["reopen_alerted"]:
                _sched["reopen_alerted"] = True
                tg_market_reopen()
            if dow == 0:
                _sched["reopen_alerted"] = False

            # EA disconnect alert — only during kill zone, only once
            if is_kz() and ea_status["last_seen"] != "Never":
                try:
                    ls = datetime.strptime(ea_status["last_seen"], "%H:%M:%S IST")
                    ls = now.replace(hour=ls.hour, minute=ls.minute, second=ls.second)
                    if (now - ls).total_seconds() > 600:
                        ea_status["connected"] = False
                        if not _sched["ea_disconnect_alerted"]:
                            _sched["ea_disconnect_alerted"] = True
                            tg_ea_disconnect()
                    else:
                        ea_status["connected"] = True
                        _sched["ea_disconnect_alerted"] = False
                except Exception:
                    pass
            # ─────────────────────────────────────────────────────

            kz  = kz_name()
            bot_status["kill_zone"]  = kz
            bot_status["last_check"] = now.strftime("%H:%M:%S IST")
            bot_status["candles_1m"] = len(candles_1m)

            log.info(f"\n{'='*55}")
            log.info(f"⏰ {now.strftime('%H:%M IST')} | {kz} | calls={api_calls['count']}/800")

            # ── Kill zone transition alerts ──
            kz_active = is_kz()
            if kz_active and not st["in_kill_zone"]:
                st["in_kill_zone"] = True
                st["warmed_up"]    = True
                tg_kz_open(kz)
            elif not kz_active and st["in_kill_zone"]:
                st["in_kill_zone"] = False
                # Reset alert levels when KZ closes
                st["last_bull_alert"] = 0
                st["last_bear_alert"] = 0
                tg_kz_close(kz)

            # ── Warmup: load candles just before KZ opens ──
            if is_warmup_window() and not st["warmed_up"] and not st["api_exhausted"]:
                log.info("⏳ Warmup — loading candles before kill zone")
                td_fetch("1min", CFG["candle_limit"], candles_1m)
                td_fetch("1h",   CFG["htf_limit"],    candles_1h)
                st["warmed_up"] = True
                bot_status["candles_1m"] = len(candles_1m)

            # Reset warmed_up flag after KZ closes so it loads fresh next time
            if not kz_active and not is_warmup_window():
                st["warmed_up"] = False

            # ── OUTSIDE kill zone — just sleep, NO API calls (unless trade is active) ──
            if not kz_active and not trade_active:
                log.info("💤 Outside kill zone — no API calls")
                time.sleep(CFG["check_every_sec"])
                bot_status["consecutive_err"] = 0
                continue

            # ── INSIDE kill zone or tracking active trade ──
            td_fetch_latest()
            bot_status["candles_1m"] = len(candles_1m)

            # Check performance of any active simulated/offline trade
            check_active_trade_performance()

            # Refresh 1H at top of hour (only if in KZ)
            if kz_active and now.minute == 0:
                td_fetch("1h", CFG["htf_limit"], candles_1h)
                log.info("🔄 1H candles refreshed")

            # Run strategy (only if in KZ)
            if kz_active:
                sig = run_strategy()

                if sig:
                    if DERIV_TOKEN and MT5_LOGIN and DERIV_ACCT and DERIV_APP_ID:
                        log.info(f"🎯 {sig['action']} — placing trade via new OTP flow...")
                        res = place_trade(sig)
                        log.info(f"📋 Result: {res}")
                        bot_status["error"] = str(res.get("detail","—"))
                    else:
                        missing = [k for k,v in {
                            "DERIV_API_TOKEN":DERIV_TOKEN,"MT5_LOGIN":MT5_LOGIN,
                            "DERIV_ACCOUNT_ID":DERIV_ACCT,"DERIV_APP_ID_NEW":DERIV_APP_ID
                        }.items() if not v]
                        log.info(f"🎯 DRY RUN {sig['action']} @ {sig['entry']:.2f} "
                                 f"[Missing: {', '.join(missing)}]")
                        
                        trade_active = True
                        trade_counter += 1
                        bot_status["open_trade"] = {
                            "num": trade_counter,
                            "action": sig["action"],
                            "entry": sig["entry"],
                            "sl": sig["sl"],
                            "tp": sig["tp"],
                            "time_open": ist_now().strftime("%H:%M IST"),
                            "open_epoch": int(time.time()),
                            "is_simulated": True
                        }
                        bot_status["last_signal"] = (
                            f"SIM {sig['action']} @ {sig['entry']:.2f} "
                            f"SL:{sig['sl']:.2f} TP:{sig['tp']:.2f} "
                            f"[{ist_now().strftime('%H:%M IST')}]")
                        
                        tg(f"🔮 <b>Simulated Trade #{trade_counter} Opened (Dry Run)</b>\n"
                           f"<code>────────────────────</code>\n"
                           f"Signal : {sig['action']} @ {sig['entry']:.2f}\n"
                           f"SL     : {sig['sl']:.2f}  |  TP : {sig['tp']:.2f}\n"
                           f"Missing: {', '.join(missing)}\n"
                           f"⏰ {ist_now().strftime('%H:%M IST')}")
                        
                        tg_trade_running(sig["action"], sig["entry"], sig["sl"], sig["tp"], trade_counter)

            bot_status["consecutive_err"] = 0

        except Exception as e:
            tb  = traceback.format_exc()
            err = str(e)
            log.error(f"❌ Loop error: {err}\n{tb}")
            bot_status["error"]            = err
            bot_status["consecutive_err"] = bot_status.get("consecutive_err",0) + 1
            tg(f"🚨 <b>Bot Loop Crash</b>\n🔴 {err[:150]}\n"
               f"📋 {tb[:200]}\n🔄 Auto-recovering\n⏰ {ist_now().strftime('%H:%M IST')}")
            if bot_status["consecutive_err"] >= 3:
                tg(f"🚨 <b>{bot_status['consecutive_err']} consecutive crashes</b>\n"
                   f"Check Railway logs")

        time.sleep(CFG["check_every_sec"])

# ══════════════════════════════════════════════════════════════
#  SIGNAL HELPERS
# ══════════════════════════════════════════════════════════════
def _update_signal(sig):
    """Write a new BUY/SELL signal — called from run_strategy()."""
    current_signal["action"]       = sig["action"]
    current_signal["entry"]        = sig["entry"]
    current_signal["sl"]           = sig["sl"]
    current_signal["tp"]           = sig["tp"]
    current_signal["timestamp"]    = ist_now().strftime("%H:%M:%S IST")
    current_signal["signal_epoch"] = int(time.time())   # UTC epoch for staleness check
    current_signal["consumed"]     = False
    log.info(f"📡 Signal updated → {sig['action']} entry={sig['entry']} sl={sig['sl']} tp={sig['tp']}")
    # Keep last 5 signals in history
    signal_history.append({"time": ist_now().strftime("%H:%M IST"),
                            "action": sig["action"], "entry": sig["entry"],
                            "sl": sig["sl"], "tp": sig["tp"]})
    if len(signal_history) > 5:
        signal_history.pop(0)

def _clear_signal():
    """Reset signal to NONE after EA has consumed it."""
    current_signal["action"]       = "NONE"
    current_signal["entry"]        = 0.0
    current_signal["sl"]           = 0.0
    current_signal["tp"]           = 0.0
    current_signal["timestamp"]    = "—"
    current_signal["signal_epoch"] = 0
    current_signal["consumed"]     = False
    log.info("📡 Signal cleared → NONE")

# ══════════════════════════════════════════════════════════════
#  FLASK STATUS PAGE
# ══════════════════════════════════════════════════════════════
flask_app = Flask(__name__)

@flask_app.route("/")
def status():
    sig_color = "#3fb950" if current_signal["action"]=="BUY" \
                else ("#f85149" if current_signal["action"]=="SELL" else "#484f58")
    sig_text  = (f"{current_signal['action']} @ {current_signal['entry']} "
                 f"SL:{current_signal['sl']} TP:{current_signal['tp']} "
                 f"[{current_signal['timestamp']}] "
                 f"{'✅ Consumed' if current_signal['consumed'] else '⏳ Waiting EA'}"
                 ) if current_signal["action"] != "NONE" else "NONE"
    rows = [
        ("Status",        "✅ Running" if bot_status["running"] else "⏳ Starting", "#3fb950"),
        ("IST Time",      ist_now().strftime("%H:%M:%S"),                           "#e3b341"),
        ("Kill Zone",     kz_name(),                                                "#e6edf3"),
        ("Last Check",    bot_status["last_check"],                                 "#e6edf3"),
        ("Last Candle",   bot_status["last_candle_t"],                              "#e6edf3"),
        ("1m Candles",    str(bot_status["candles_1m"]),                            "#e6edf3"),
        ("API Calls",     bot_status["api_calls"] + (" 🔴 PAUSED" if st.get("api_exhausted") else ""), "#e3b341"),
        ("Volume",        bot_status["volume_info"],                                "#e6edf3"),
        ("EA Signal",     sig_text,                                                 sig_color),
        ("Last Signal",   bot_status["last_signal"],                                "#58a6ff"),
        ("Last TG Alert", bot_status["last_alert"],                                 "#a78bfa"),
        ("Trade Active",  "🔴 YES" if trade_active else "⚪ No",                   "#e6edf3"),
        ("Consec Errors", str(bot_status.get("consecutive_err",0)),                 "#f85149" if bot_status.get("consecutive_err",0)>0 else "#e6edf3"),
        ("Twelve Data",   "✅" if TD_KEY      else "❌ Add TWELVE_DATA_KEY",        "#e6edf3"),
        ("Deriv Token",   "✅" if DERIV_TOKEN else "❌ Add DERIV_API_TOKEN",        "#e6edf3"),
        ("Account ID",    DERIV_ACCT or "❌ Add DERIV_ACCOUNT_ID",                 "#e6edf3"),
        ("App ID",        "✅" if DERIV_APP_ID else "❌ Add DERIV_APP_ID_NEW",      "#e6edf3"),
        ("MT5 Login",     MT5_LOGIN or "❌ Add MT5_LOGIN",                          "#e6edf3"),
        ("Telegram",      "✅" if TG_TOKEN and TG_CHAT else "❌ Add TG vars",       "#e6edf3"),
        ("Last Error",    bot_status["error"],                                      "#f85149"),
        ("── EA ──",      "",                                                         "#21262d"),
        ("EA Last Seen",  ea_status["last_seen"],                                    "#3fb950" if ea_status["connected"] else "#f85149"),
        ("EA Connected",  "✅ Yes" if ea_status["connected"] else "❌ Not seen",    "#3fb950" if ea_status["connected"] else "#f85149"),
        ("EA Poll Count", str(ea_status["poll_count"]),                              "#e6edf3"),
        ("Next KZ",       kz_countdown(),                                            "#e3b341"),
        ("── Signals ──", "",                                                         "#21262d"),
    ] + [(f"Signal {i+1}",
          f"{s['action']} @ {s['entry']} SL:{s['sl']} TP:{s['tp']} [{s['time']}]",
          "#3fb950" if s['action']=="BUY" else "#f85149")
         for i, s in enumerate(signal_history[-5:])] + [
        ("─────────",    "",                                                          "#21262d"),
    ]
    rows_html = "".join(
        f'<tr><td style="padding:6px 12px;color:#8b949e;border-bottom:1px solid #21262d;white-space:nowrap">{l}</td>'
        f'<td style="padding:6px 12px;color:{c};border-bottom:1px solid #21262d;word-break:break-all">{v}</td></tr>'
        for l,v,c in rows)
    return f"""<html>
    <head><meta http-equiv="refresh" content="30"><title>SMC Bot v7</title></head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;padding:30px;max-width:720px">
    <h2 style="color:#58a6ff">🤖 SMC+XAUUSD Bot v7</h2>
    <p style="color:#484f58;margin-top:-12px">0.01 lots · MT5 Demo · 1m · Efficient API</p>
    <table style="border-collapse:collapse;width:100%">{rows_html}</table>
    <br><p style="color:#484f58;font-size:12px;line-height:1.9">
    🟡 London: 12:30–15:30 IST &nbsp;|&nbsp; 🔵 NY: 17:30–20:30 IST<br>
    📡 API calls only during kill zones (~390/800 per day)<br>
    🔄 API resets at 5:30 AM IST daily<br>
    Auto-refreshes every 30s</p>
    </body></html>""", 200

@flask_app.route("/api/status")
@flask_app.route("/status")
def api_s():
    return jsonify({**bot_status,
                    "kz"            : is_kz(),
                    "kz_countdown"  : kz_countdown(),
                    "ist"           : ist_now().strftime("%H:%M:%S"),
                    "trade"         : trade_active,
                    "api_exhausted" : st.get("api_exhausted", False),
                    "ea_last_seen"  : ea_status["last_seen"],
                    "ea_connected"  : ea_status["connected"],
                    "ea_poll_count" : ea_status["poll_count"],
                    "signal_history": signal_history[-5:],
                    })

# ── /signal  — MQL5 EA polls this every tick ──────────────────
@flask_app.route("/signal")
def get_signal():
    """
    Returns the current trading signal as JSON.
    • While a trade is active, always returns NONE — EA should not receive new signals.
    • Auto-expires signals older than MAX_SIGNAL_AGE_SEC.
    """
    global trade_active

    # Track EA connectivity on every poll
    ea_status["last_seen"]   = ist_now().strftime("%H:%M:%S IST")
    ea_status["connected"]   = True
    ea_status["poll_count"] += 1
    _sched["ea_disconnect_alerted"] = False

    # ── KEY FIX: If trade is running, always return NONE to EA ──────
    if trade_active:
        return jsonify({"action": "NONE", "entry": 0.0, "sl": 0.0, "tp": 0.0,
                        "timestamp": "—", "signal_epoch": 0, "consumed": True})

    # Auto-expire stale signals — if signal is older than MAX_SIGNAL_AGE_SEC, clear it
    if current_signal["action"] != "NONE" and current_signal["signal_epoch"] > 0:
        age = int(time.time()) - current_signal["signal_epoch"]
        if age > MAX_SIGNAL_AGE_SEC:
            log.info(f"⏰ Signal expired (age={age}s > {MAX_SIGNAL_AGE_SEC}s) — auto-clearing")
            tg(f"⏰ <b>Stale Signal Discarded</b>\n"
               f"━━━━━━━━━━━━━━━━\n"
               f"📌 {current_signal['action']} @ {current_signal['entry']} was {age}s old\n"
               f"🔴 Too old to execute safely — cleared\n"
               f"⏰ {ist_now().strftime('%H:%M IST')}")
            _clear_signal()

    return jsonify(current_signal)

# ── /signal/consumed  — EA calls after placing trade ──────────
@flask_app.route("/signal/consumed", methods=["POST","GET"])
def mark_consumed():
    """EA calls this after a trade attempt (success or fail). Marks signal consumed."""
    current_signal["consumed"] = True
    log.info("✅ Signal marked consumed by EA")
    return jsonify({"ok": True})

# ── /trade/open  — EA calls this after successfully placing a trade
@flask_app.route("/trade/open", methods=["POST","GET"])
def trade_open():
    """
    EA calls this after a trade is successfully placed.
    Sets trade_active=True so the Python bot stops generating new signals.
    Clears the current signal so EA stops receiving it immediately.
    """
    global trade_active, trade_counter
    action = current_signal["action"]
    entry  = current_signal["entry"]
    sl     = current_signal["sl"]
    tp     = current_signal["tp"]

    # Check if there is an active simulated trade that matches the action
    open_trade = bot_status.get("open_trade", {})
    if open_trade and open_trade.get("is_simulated", False):
        if open_trade.get("action") == action and abs(open_trade.get("entry", 0) - entry) < 0.5:
            # Upgrade simulated trade to live trade because the EA successfully opened it!
            log.info("📌 EA connected and confirmed trade open. Upgrading simulated trade to live.")
            open_trade["is_simulated"] = False
            _clear_signal()
            return jsonify({"ok": True})

    # If already opened (from place_trade), don't duplicate
    if open_trade and not open_trade.get("is_simulated", False):
        if open_trade.get("action") == action and abs(open_trade.get("entry", 0) - entry) < 0.5:
            log.info("📌 Trade already open in state (from place_trade), skipping duplicate open notification")
            _clear_signal()
            return jsonify({"ok": True})

    trade_active  = True
    trade_counter += 1
    trade_num = trade_counter

    # Store open trade info for when it closes
    bot_status["open_trade"] = {
        "num": trade_num, "action": action, "entry": entry,
        "sl": sl, "tp": tp, "time_open": ist_now().strftime("%H:%M IST"),
        "open_epoch": int(time.time()), "is_simulated": False
    }
    bot_status["last_signal"] = (
        f"#{trade_num} {action} @ {entry:.2f} SL:{sl:.2f} TP:{tp:.2f} "
        f"[{ist_now().strftime('%H:%M IST')}]")

    # Clear the signal immediately — EA won't receive it again
    _clear_signal()

    log.info(f"📌 Trade #{trade_num} OPEN reported by EA — trade_active=True")
    # Send running position message
    tg_trade_running(action, entry, sl, tp, trade_num)
    return jsonify({"ok": True})

# ── /trade/close  — EA calls this when a trade is closed ──────
# EA can pass: ?profit=-10.50&result=SL  or  ?profit=10.50&result=TP
@flask_app.route("/trade/close", methods=["POST","GET"])
def trade_close():
    """
    EA calls this when the trade closes (SL/TP hit). Resets trade_active.
    Optional query params:
      profit  : float P&L in account currency (e.g. -10.5 or +10.5)
      result  : "SL" | "TP" | "manual"
    """
    from flask import request as flask_request
    global trade_active

    # Retrieve open trade info
    open_trade = bot_status.get("open_trade", {})
    if not open_trade:
        # The trade might have already been closed by the simulated fallback
        log.info("📌 Trade close requested by EA, but trade is already closed in server state. Skipping.")
        return jsonify({"ok": True, "message": "Already closed"})

    profit_str = flask_request.args.get("profit", "0")
    result_str = flask_request.args.get("result", "closed").upper()
    try:
        profit = float(profit_str)
    except ValueError:
        profit = 0.0

    trade_active = False
    _clear_signal()

    trade_num  = open_trade.get("num", trade_counter)
    action     = open_trade.get("action", "—")
    entry      = open_trade.get("entry", 0.0)
    sl         = open_trade.get("sl", 0.0)
    tp         = open_trade.get("tp", 0.0)
    time_open  = open_trade.get("time_open", "—")

    # Log closed trade
    trade_log.append({
        "num"       : trade_num,
        "action"    : action,
        "entry"     : entry,
        "sl"        : sl,
        "tp"        : tp,
        "result"    : result_str,
        "profit"    : profit,
        "time_open" : time_open,
        "time_close": ist_now().strftime("%H:%M IST"),
    })
    bot_status["open_trade"] = {}

    log.info(f"📌 Trade #{trade_num} CLOSE reported by EA — result={result_str} profit={profit:.2f}")
    tg_trade_closed(trade_num, action, entry, sl, tp, result_str, profit)
    tg(f"🔄 <b>Bot Resumed</b> — watching for next signal\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)
    return jsonify({"ok": True})

if __name__ == "__main__":
    threading.Thread(target=bot_loop, daemon=True).start()
    port = int(os.environ.get("PORT", 5000))
    log.info(f"🌐 Flask on port {port}")
    flask_app.run(host="0.0.0.0", port=port, use_reloader=False)

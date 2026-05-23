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
    "action"    : "NONE",   # "BUY", "SELL", or "NONE"
    "entry"     : 0.0,
    "sl"        : 0.0,
    "tp"        : 0.0,
    "timestamp" : "—",      # IST time signal was generated
    "consumed"  : False,    # EA sets this True after placing trade (via /signal/consumed)
}

st = {
    # Strategy state
    "bull_sweep_bar" : -999, "bear_sweep_bar" : -999,
    "bull_choch_bar" : -999, "bear_choch_bar" : -999,
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
    tg(f"🚀 <b>SMC+XAU Bot v7 Started</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"📊 XAUUSD · 1m · 0.01 lots\n"
       f"🛑 SL: {CFG['sl_atr_mult']}×ATR  🎯 TP: 1:{CFG['rr_ratio']}\n"
       f"🟡 London : 12:30–15:30 IST\n"
       f"🔵 NY     : 17:30–20:30 IST\n"
       f"💡 API calls only during kill zones\n"
       f"⏰ {ist_now().strftime('%H:%M:%S IST')}\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"Monitoring XAUUSD 🔍")

def tg_kz_open(name):
    tg(f"⏰ <b>Kill Zone Open</b> — {name}\n"
       f"🔍 Strategy active\n"
       f"📡 API calls: {api_calls['count']}/800\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)

def tg_kz_close(name):
    tg(f"🔕 <b>Kill Zone Closed</b>\n"
       f"{name}\n"
       f"📡 API calls used today: {api_calls['count']}/800\n"
       f"💤 Bot sleeping\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}", silent=True)

def tg_warn(direction, conds, score, price, atr_v):
    met     = [k for k,v in conds.items() if v]
    missing = [k for k,v in conds.items() if not v]
    tg(f"🟡 <b>EARLY WARNING — {direction}</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"📊 XAUUSD @ <b>{price:.2f}</b>\n"
       f"✅ <b>{score}/7 met</b> · ATR: {atr_v:.2f}\n"
       f"\n✅ Met:\n" + "\n".join(f"  • {c}" for c in met) +
       f"\n\n⏳ Waiting for:\n" + "\n".join(f"  • {c}" for c in missing) +
       f"\n⏰ {ist_now().strftime('%H:%M IST')}")

def tg_setup(direction, conds, score, price, atr_v, est_sl, est_tp):
    met     = [k for k,v in conds.items() if v]
    missing = [k for k,v in conds.items() if not v]
    tg(f"🟠 <b>SETUP FORMING — {direction}</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"📊 XAUUSD @ <b>{price:.2f}</b>\n"
       f"✅ <b>{score}/7 met</b>\n"
       f"\n✅ Met:\n" + "\n".join(f"  • {c}" for c in met) +
       f"\n\n⏳ Waiting for:\n" + "\n".join(f"  • {c}" for c in missing) +
       f"\n\n💡 Est SL: {est_sl:.2f}  TP: {est_tp:.2f}\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_trade(signal):
    tg(f"✅ <b>TRADE PLACED</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"📌 <b>{signal['action']} XAUUSD</b>\n"
       f"💰 Entry : <b>{signal['entry']:.2f}</b>\n"
       f"🛑 SL    : <b>{signal['sl']:.2f}</b>\n"
       f"🎯 TP    : <b>{signal['tp']:.2f}</b>\n"
       f"📦 Lots  : 0.01\n"
       f"📐 Risk  : {abs(signal['entry']-signal['sl']):.2f} pts\n"
       f"🏆 Reward: {abs(signal['tp']-signal['entry']):.2f} pts\n"
       f"⏰ {ist_now().strftime('%H:%M IST')}\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"🤖 SMC+XAU Bot v7")

def tg_err(title, detail, fix=""):
    tg(f"❌ <b>{title}</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"🔴 {detail}\n"
       + (f"💡 {fix}\n" if fix else "") +
       f"⏰ {ist_now().strftime('%H:%M IST')}")

def tg_api_warn():
    tg(f"⚠️ <b>API Limit Warning</b>\n"
       f"📡 Used: <b>{api_calls['count']}/800</b> today\n"
       f"⏰ Resets at 5:30 AM IST\n"
       f"💡 Approaching daily limit", silent=True)

def tg_api_exhausted():
    tg(f"🚨 <b>API Limit Reached — Bot Paused</b>\n"
       f"━━━━━━━━━━━━━━━━\n"
       f"📡 Used: <b>{api_calls['count']}/800</b> calls\n"
       f"🔴 No more candle fetches today\n"
       f"⏰ Resets at <b>5:30 AM IST</b>\n"
       f"💤 Bot will auto-resume after reset")

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
        tg(f"⚠️ <b>Missing Railway Variables</b>\n" +
           "\n".join(f"  • {m}" for m in missing) +
           f"\n🔧 Railway → Service → Variables")

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

        # Sweeps
        sb = be = False
        if st["asian_low"]  and l<st["asian_low"]:  sb=True
        if st["asian_high"] and h>st["asian_high"]: be=True
        if l<pdl: sb=True
        if h>pdh: be=True
        if lsl and not np.isnan(lsl) and l<lsl and c>lsl: sb=True
        if lsh and not np.isnan(lsh) and h>lsh and c<lsh: be=True

        if sb: st["bull_sweep_bar"]=i; log.info("🔍 Bull sweep")
        if be: st["bear_sweep_bar"]=i; log.info("🔍 Bear sweep")

        rbs=(i-st["bull_sweep_bar"])<=CFG["sweep_window"]
        rbe=(i-st["bear_sweep_bar"])<=CFG["sweep_window"]

        bc =rbe and c>ph and c>o; brc=rbs and c<pl and c<o
        if bc:  st["bull_choch_bar"]=i; log.info("🔄 Bull CHoCH")
        if brc: st["bear_choch_bar"]=i; log.info("🔄 Bear CHoCH")

        rbc =(i-st["bull_choch_bar"])<=CFG["choch_window"]
        rbrc=(i-st["bear_choch_bar"])<=CFG["choch_window"]

        body=abs(c-o); rng=h-l
        be_l=c>o and c>po and o<pc and body>rng*0.5
        be_s=c<o and c<po and o>pc and body>rng*0.5

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

        # Condition alerts (only during KZ, only if not spamming)
        if ls>=5 and st["last_bull_alert"]<60 and not trade_active:
            st["last_bull_alert"]=60; tg_warn("🟢 LONG",long_conds,ls,c,atr_v)
        if ls>=6 and st["last_bull_alert"]<80 and not trade_active:
            st["last_bull_alert"]=80; tg_setup("🟢 LONG",long_conds,ls,c,atr_v,esl,etp)
        if ss>=5 and st["last_bear_alert"]<60 and not trade_active:
            st["last_bear_alert"]=60; tg_warn("🔴 SHORT",short_conds,ss,c,atr_v)
        if ss>=6 and st["last_bear_alert"]<80 and not trade_active:
            st["last_bear_alert"]=80; tg_setup("🔴 SHORT",short_conds,ss,c,atr_v,essl,estp)

        if ls<5: st["last_bull_alert"]=0
        if ss<5: st["last_bear_alert"]=0

        if all(long_conds.values()) and not trade_active:
            sl=l-atr_v*CFG["sl_atr_mult"]; tp=c+abs(c-sl)*CFG["rr_ratio"]
            st["last_bull_alert"]=100
            log.info(f"🚀 LONG entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
            sig = {"action":"BUY","entry":c,"sl":round(sl,2),"tp":round(tp,2)}
            _update_signal(sig)
            return sig

        if all(short_conds.values()) and not trade_active:
            sl=h+atr_v*CFG["sl_atr_mult"]; tp=c-abs(sl-c)*CFG["rr_ratio"]
            st["last_bear_alert"]=100
            log.info(f"🔻 SHORT entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
            sig = {"action":"SELL","entry":c,"sl":round(sl,2),"tp":round(tp,2)}
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
                    oid = d.get("mt5_new_order",{}).get("order","—")
                    log.info(f"✅ Trade placed! Order: {oid}")
                    result["status"]="placed"; result["order"]=oid
                    trade_active = True
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

    while True:
        try:
            now = ist_now()
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

            # ── OUTSIDE kill zone — just sleep, NO API calls ──
            if not kz_active:
                log.info("💤 Outside kill zone — no API calls")
                time.sleep(CFG["check_every_sec"])
                bot_status["consecutive_err"] = 0
                continue

            # ── INSIDE kill zone — fetch + strategy ──
            td_fetch_latest()
            bot_status["candles_1m"] = len(candles_1m)

            # Refresh 1H at top of hour
            if now.minute == 0:
                td_fetch("1h", CFG["htf_limit"], candles_1h)
                log.info("🔄 1H candles refreshed")

            # Run strategy
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
                    bot_status["last_signal"] = f"DRY {sig['action']} @ {sig['entry']:.2f}"
                    tg(f"⚠️ <b>Signal — No Trade (Missing credentials)</b>\n"
                       f"📌 {sig['action']} @ {sig['entry']:.2f}\n"
                       f"Missing: {', '.join(missing)}")

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
    current_signal["action"]    = sig["action"]
    current_signal["entry"]     = sig["entry"]
    current_signal["sl"]        = sig["sl"]
    current_signal["tp"]        = sig["tp"]
    current_signal["timestamp"] = ist_now().strftime("%H:%M:%S IST")
    current_signal["consumed"]  = False
    log.info(f"📡 Signal updated → {sig['action']} entry={sig['entry']} sl={sig['sl']} tp={sig['tp']}")

def _clear_signal():
    """Reset signal to NONE after EA has consumed it."""
    current_signal["action"]    = "NONE"
    current_signal["entry"]     = 0.0
    current_signal["sl"]        = 0.0
    current_signal["tp"]        = 0.0
    current_signal["timestamp"] = "—"
    current_signal["consumed"]  = False
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
    return jsonify({**bot_status,"kz":is_kz(),"ist":ist_now().strftime("%H:%M:%S"),
                    "trade":trade_active,"api_exhausted":st.get("api_exhausted",False)})

# ── /signal  — MQL5 EA polls this every tick ──────────────────
@flask_app.route("/signal")
def get_signal():
    """
    Returns the current trading signal as JSON.
    The MQL5 EA calls this URL every tick.
    Response:
      { "action": "BUY"|"SELL"|"NONE",
        "entry": float, "sl": float, "tp": float,
        "timestamp": str, "consumed": bool }
    """
    return jsonify(current_signal)

# ── /signal/consumed  — EA calls after placing trade ──────────
@flask_app.route("/signal/consumed", methods=["POST","GET"])
def mark_consumed():
    """
    EA calls this after successfully placing the trade.
    Marks signal as consumed so bot doesn't re-trigger.
    """
    current_signal["consumed"] = True
    log.info("✅ Signal marked consumed by EA")
    return jsonify({"ok": True})

if __name__ == "__main__":
    threading.Thread(target=bot_loop, daemon=True).start()
    port = int(os.environ.get("PORT", 5000))
    log.info(f"🌐 Flask on port {port}")
    flask_app.run(host="0.0.0.0", port=port, use_reloader=False)

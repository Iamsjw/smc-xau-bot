"""
SMC + XAUUSD Trading Bot v2
============================
Fixes:
  1. Volume → tick_count from Deriv (real proxy, not zero)
  2. Trades → MT5 STD Demo via mt5_new_order (0.01 lots)
  3. MT5_LOGIN → set in Railway Variables tab
"""

import json, time, threading, logging, os
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

# ── Credentials (set in Railway → Service → Variables) ──
DERIV_TOKEN  = os.environ.get("DERIV_API_TOKEN", "")
MT5_LOGIN    = os.environ.get("MT5_LOGIN", "")
DERIV_APP_ID = "1089"
DERIV_WS     = f"wss://ws.binaryws.com/websockets/v3?app_id={DERIV_APP_ID}"
IST          = timezone(timedelta(hours=5, minutes=30))

# ── Strategy config (matches your Pine Script exactly) ──
CFG = {
    "fast_ema": 14, "slow_ema": 140, "htf_ema": 50,
    "atr_len": 14, "sl_atr_mult": 2.0, "rr_ratio": 3.0,
    "swing_len": 3, "choch_window": 5, "sweep_window": 10,
    "use_volume": True, "vol_mult": 1.1,
    "use_htf_bias": True, "use_local_trend": True, "use_engulf": True,
    "mt5_symbol": "XAUUSD",
    "lot_size": 0.01,
    "deriv_symbol": "frxXAUUSD",
    "candle_limit": 300, "htf_limit": 100,
    "check_every_sec": 60,
}

candles_1m   = deque(maxlen=CFG["candle_limit"])
candles_1h   = deque(maxlen=CFG["htf_limit"])
trade_active = False
bot_status   = {"running": False, "last_check": "—", "last_signal": "—",
                "kill_zone": "—", "candles_1m": 0, "error": "—"}
st = {"bull_sweep_bar": -999, "bear_sweep_bar": -999,
      "bull_choch_bar": -999, "bear_choch_bar": -999,
      "asian_high": None, "asian_low": None,
      "last_sh": None, "last_sl": None}

# ── Helpers ──
def ist_now(): return datetime.now(IST)
def is_kz():
    t = ist_now().hour * 100 + ist_now().minute
    return (1230 <= t <= 1530) or (1730 <= t <= 2030)
def kz_name():
    t = ist_now().hour * 100 + ist_now().minute
    if 1230 <= t <= 1530: return "🟡 London  12:30–15:30 IST"
    if 1730 <= t <= 2030: return "🔵 NY      17:30–20:30 IST"
    return "⚫ Outside kill zone"
def to_df(q):
    df = pd.DataFrame(list(q))
    if df.empty: return df
    df = df.rename(columns={"o":"open","h":"high","l":"low","c":"close","v":"volume"})
    for col in ["open","high","low","close","volume"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    return df.reset_index(drop=True)
def ema(s, p): return s.ewm(span=p, adjust=False).mean()
def calc_atr(df, p):
    h,l,pc = df["high"],df["low"],df["close"].shift(1)
    return pd.concat([h-l,(h-pc).abs(),(l-pc).abs()],axis=1).max(axis=1).ewm(span=p,adjust=False).mean()
def pvt_h(s, n):
    v,r=s.values,np.nan
    for i in range(n,len(v)-n):
        if all(v[i]>=v[i-j] for j in range(1,n+1)) and all(v[i]>=v[i+j] for j in range(1,n+1)):
            r=v[i]
    return r
def pvt_l(s, n):
    v,r=s.values,np.nan
    for i in range(n,len(v)-n):
        if all(v[i]<=v[i-j] for j in range(1,n+1)) and all(v[i]<=v[i+j] for j in range(1,n+1)):
            r=v[i]
    return r

# ── Candle fetch (tick_count = real volume proxy) ──
def fetch_candles(gran, count, target):
    done, fetched = threading.Event(), []
    def on_open(ws):
        ws.send(json.dumps({"ticks_history":CFG["deriv_symbol"],"end":"latest",
                            "count":count,"granularity":gran,"style":"candles","adjust_start_time":1}))
    def on_message(ws, msg):
        d = json.loads(msg)
        if d.get("msg_type") == "candles":
            for c in d.get("candles",[]):
                fetched.append({"epoch":c["epoch"],"o":float(c["open"]),"h":float(c["high"]),
                                "l":float(c["low"]),"c":float(c["close"]),
                                "v":float(c.get("tick_count",1))})  # ✅ real tick volume
            log.info(f"📊 {len(fetched)} candles fetched (gran={gran}s)")
        ws.close(); done.set()
    def on_error(ws,e): log.error(f"Fetch err:{e}"); done.set()
    websocket.WebSocketApp(DERIV_WS,on_open=on_open,on_message=on_message,
                           on_error=on_error).run_forever()
    done.wait(20); target.clear()
    for c in fetched: target.append(c)

def fetch_latest():
    done, fetched = threading.Event(), []
    def on_open(ws):
        ws.send(json.dumps({"ticks_history":CFG["deriv_symbol"],"end":"latest",
                            "count":2,"granularity":60,"style":"candles"}))
    def on_message(ws, msg):
        d = json.loads(msg)
        if d.get("msg_type") == "candles":
            raw = d.get("candles",[])
            if raw:
                c = raw[-2] if len(raw)>=2 else raw[-1]
                fetched.append({"epoch":c["epoch"],"o":float(c["open"]),"h":float(c["high"]),
                                "l":float(c["low"]),"c":float(c["close"]),
                                "v":float(c.get("tick_count",1))})  # ✅ real tick volume
        ws.close(); done.set()
    def on_error(ws,e): done.set()
    websocket.WebSocketApp(DERIV_WS,on_open=on_open,on_message=on_message,
                           on_error=on_error).run_forever()
    done.wait(15)
    if fetched and (not candles_1m or candles_1m[-1]["epoch"]!=fetched[0]["epoch"]):
        candles_1m.append(fetched[0])
        log.info(f"🕐 1m candle | close={fetched[0]['c']:.2f} ticks={int(fetched[0]['v'])}")

# ── Strategy ──
def run_strategy():
    global trade_active
    df = to_df(candles_1m)
    if len(df) < CFG["slow_ema"]+10:
        log.info(f"Need more candles: {len(df)}"); return None
    df1h = to_df(candles_1h)
    i = len(df)-1

    fast_v = float(ema(df["close"],CFG["fast_ema"]).iloc[-1])
    slow_v = float(ema(df["close"],CFG["slow_ema"]).iloc[-1])
    bull_t = fast_v > slow_v

    bull_b = bear_b = True
    if CFG["use_htf_bias"] and len(df1h)>=CFG["htf_ema"]:
        hv     = float(ema(df1h["close"],CFG["htf_ema"]).iloc[-1])
        cc     = float(df["close"].iloc[-1])
        bull_b = cc > hv; bear_b = cc < hv

    atr_v = float(calc_atr(df,CFG["atr_len"]).iloc[-1])

    # Volume using tick_count
    avg_v   = df["volume"].rolling(20).mean()
    high_v  = True
    if CFG["use_volume"]:
        cv    = float(df["volume"].iloc[-1])
        av    = float(avg_v.iloc[-1]) if not pd.isna(avg_v.iloc[-1]) else 1
        high_v= cv > av * CFG["vol_mult"]
        log.info(f"📊 ticks={int(cv)} avg={av:.1f} thr={av*CFG['vol_mult']:.1f} ok={high_v}")

    n = len(df)
    pdh = float(df["high"].iloc[-1440:-720].max()) if n>=1440 else float(df["high"].iloc[:max(1,n//2)].max())
    pdl = float(df["low"].iloc[-1440:-720].min())  if n>=1440 else float(df["low"].iloc[:max(1,n//2)].min())

    sw = CFG["swing_len"]
    lsh = pvt_h(df["high"],sw) if len(df)>=sw*2+5 else st["last_sh"]
    lsl = pvt_l(df["low"], sw) if len(df)>=sw*2+5 else st["last_sl"]
    st["last_sh"]=lsh; st["last_sl"]=lsl

    c,o,h,l   = float(df["close"].iloc[-1]),float(df["open"].iloc[-1]),float(df["high"].iloc[-1]),float(df["low"].iloc[-1])
    ph,pl,po,pc=float(df["high"].iloc[-2]),float(df["low"].iloc[-2]),float(df["open"].iloc[-2]),float(df["close"].iloc[-2])

    sb=be=False
    if st["asian_low"]  and l<st["asian_low"]:   sb=True
    if st["asian_high"] and h>st["asian_high"]:  be=True
    if l<pdl: sb=True
    if h>pdh: be=True
    if lsl and not np.isnan(lsl) and l<lsl and c>lsl: sb=True
    if lsh and not np.isnan(lsh) and h>lsh and c<lsh: be=True

    if sb: st["bull_sweep_bar"]=i; log.info("🔍 Bull sweep")
    if be: st["bear_sweep_bar"]=i; log.info("🔍 Bear sweep")

    rbs=(i-st["bull_sweep_bar"])<=CFG["sweep_window"]
    rbe=(i-st["bear_sweep_bar"])<=CFG["sweep_window"]

    bc=rbe and c>ph and c>o; brc=rbs and c<pl and c<o
    if bc:  st["bull_choch_bar"]=i; log.info("🔄 Bull CHoCH")
    if brc: st["bear_choch_bar"]=i; log.info("🔄 Bear CHoCH")

    rbc =(i-st["bull_choch_bar"])<=CFG["choch_window"]
    rbrc=(i-st["bear_choch_bar"])<=CFG["choch_window"]

    body=abs(c-o); rng=h-l
    be_l=c>o and c>po and o<pc and body>rng*0.5
    be_s=c<o and c<po and o>pc and body>rng*0.5

    htfl=bull_b if CFG["use_htf_bias"]    else True
    htfs=bear_b if CFG["use_htf_bias"]    else True
    trl =bull_t if CFG["use_local_trend"] else True
    trs =not bull_t if CFG["use_local_trend"] else True
    el  =be_l  if CFG["use_engulf"]       else True
    es  =be_s  if CFG["use_engulf"]       else True
    vok =high_v if CFG["use_volume"]      else True

    long_ok =(htfl and trl and vok and rbs and rbc  and el  and not trade_active)
    short_ok=(htfs and trs and vok and rbe and rbrc and es  and not trade_active)

    log.info(f"⏳ htf:{'B' if bull_b else 'b'} tr:{'B' if bull_t else 'b'} "
             f"vol:{vok} bs:{rbs} be:{rbe} bc:{rbc} brc:{rbrc} el:{be_l} es:{be_s}")

    if long_ok:
        sl=l-atr_v*CFG["sl_atr_mult"]; tp=c+abs(c-sl)*CFG["rr_ratio"]
        log.info(f"🚀 LONG entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
        return {"action":"BUY","entry":c,"sl":sl,"tp":tp,"sl_dist":abs(c-sl),"tp_dist":abs(tp-c)}
    if short_ok:
        sl=h+atr_v*CFG["sl_atr_mult"]; tp=c-abs(sl-c)*CFG["rr_ratio"]
        log.info(f"🔻 SHORT entry:{c:.2f} sl:{sl:.2f} tp:{tp:.2f}")
        return {"action":"SELL","entry":c,"sl":sl,"tp":tp,"sl_dist":abs(sl-c),"tp_dist":abs(c-tp)}
    return None

# ── Place trade on MT5 STD Demo (0.01 lots) ──
def place_trade(signal):
    global trade_active
    result={}; done=threading.Event()
    otype=0 if signal["action"]=="BUY" else 1

    def on_open(ws): ws.send(json.dumps({"authorize":DERIV_TOKEN}))
    def on_message(ws,msg):
        global trade_active
        d=json.loads(msg); mt=d.get("msg_type")
        if mt=="authorize":
            if "error" in d:
                log.error(f"Auth err:{d['error']['message']}")
                result["status"]="auth_error"; ws.close(); done.set(); return
            # ✅ mt5_new_order → places trade on YOUR MT5 STD Demo account
            ws.send(json.dumps({
                "mt5_new_order":1,
                "login"        :int(MT5_LOGIN),
                "symbol"       :CFG["mt5_symbol"],
                "volume"       :CFG["lot_size"],    # 0.01 lots
                "order_type"   :otype,              # 0=BUY 1=SELL
                "price"        :signal["entry"],
                "stop_loss"    :round(signal["sl"],2),
                "take_profit"  :round(signal["tp"],2),
                "comment"      :"SMC+XAU Bot",
            }))
            log.info(f"📤 MT5 order sent | {signal['action']} 0.01 lots @ {signal['entry']:.2f}")
        elif mt=="mt5_new_order":
            if "error" in d:
                log.error(f"MT5 err:{d['error']['message']}")
                result["status"]="error"; result["detail"]=d["error"]["message"]
            else:
                oid=d.get("mt5_new_order",{}).get("order","—")
                log.info(f"✅ Trade placed on MT5! Order:{oid}")
                result["status"]="placed"; result["order"]=oid
                trade_active=True
                bot_status["last_signal"]=(
                    f"{signal['action']} @ {signal['entry']:.2f} "
                    f"SL:{signal['sl']:.2f} TP:{signal['tp']:.2f} "
                    f"0.01lots [{ist_now().strftime('%H:%M IST')}]"
                )
            ws.close(); done.set()
        elif mt=="error":
            result["status"]="ws_error"; ws.close(); done.set()
    def on_error(ws,e): result["status"]="ws_error"; done.set()

    websocket.WebSocketApp(DERIV_WS,on_open=on_open,on_message=on_message,
                           on_error=on_error).run_forever()
    done.wait(20); return result

# ── Bot loop ──
def bot_loop():
    log.info("🤖 Bot v2 starting...")
    log.info(f"MT5 Login: {MT5_LOGIN or '❌ NOT SET — add MT5_LOGIN in Railway vars'}")
    fetch_candles(60,  CFG["candle_limit"],candles_1m)
    fetch_candles(3600,CFG["htf_limit"],   candles_1h)
    bot_status["running"]=True; bot_status["candles_1m"]=len(candles_1m)
    log.info(f"✅ {len(candles_1m)} × 1m | {len(candles_1h)} × 1H candles loaded")

    while True:
        try:
            fetch_latest()
            bot_status["candles_1m"]=len(candles_1m)
            now=ist_now(); kz=kz_name()
            bot_status["kill_zone"]=kz; bot_status["last_check"]=now.strftime("%H:%M:%S IST")
            log.info(f"\n{'='*55}\n⏰ {now.strftime('%H:%M IST')} | {kz}")
            log.info(f"📦 {len(candles_1m)} × 1m | trade_active={trade_active}")

            if not is_kz():
                log.info("💤 Outside kill zone"); time.sleep(CFG["check_every_sec"]); continue

            sig = run_strategy()
            if sig:
                if DERIV_TOKEN and MT5_LOGIN:
                    log.info(f"🎯 {sig['action']} — placing on MT5...")
                    res=place_trade(sig)
                    log.info(f"📋 {res}"); bot_status["error"]=str(res.get("detail","—"))
                else:
                    log.info(f"🎯 DRY RUN {sig['action']} @ {sig['entry']:.2f}")
                    bot_status["last_signal"]=f"DRY {sig['action']} @ {sig['entry']:.2f}"

            if now.minute==0: fetch_candles(3600,CFG["htf_limit"],candles_1h); log.info("🔄 1H refreshed")

        except Exception as e:
            log.error(f"❌ {e}",exc_info=True); bot_status["error"]=str(e)
        time.sleep(CFG["check_every_sec"])

# ── Flask ──
app = Flask(__name__)

@app.route("/")
def status():
    ist=ist_now().strftime("%H:%M:%S"); kz=kz_name()
    tok="✅ Set" if DERIV_TOKEN else "❌ Add DERIV_API_TOKEN in Railway vars"
    login=MT5_LOGIN if MT5_LOGIN else "❌ Add MT5_LOGIN in Railway vars"
    run="✅ Running" if bot_status["running"] else "⏳ Starting..."
    return f"""<html><head><meta http-equiv="refresh" content="30"><title>SMC Bot</title></head>
    <body style="background:#0d1117;color:#e6edf3;font-family:monospace;padding:30px;max-width:600px">
    <h2 style="color:#58a6ff">🤖 SMC+XAUUSD Bot v2</h2>
    <p style="color:#484f58;margin-top:-12px">0.01 lots · MT5 STD Demo · 1m</p>
    <table style="border-collapse:collapse;width:100%">
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">Status</td><td style="padding:7px 12px;color:#3fb950;border-bottom:1px solid #21262d">{run}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">IST Time</td><td style="padding:7px 12px;color:#e3b341;border-bottom:1px solid #21262d">{ist}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">Kill Zone</td><td style="padding:7px 12px;border-bottom:1px solid #21262d">{kz}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">Last Check</td><td style="padding:7px 12px;border-bottom:1px solid #21262d">{bot_status["last_check"]}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">1m Candles</td><td style="padding:7px 12px;border-bottom:1px solid #21262d">{bot_status["candles_1m"]}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">Last Signal</td><td style="padding:7px 12px;color:#58a6ff;border-bottom:1px solid #21262d">{bot_status["last_signal"]}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">API Token</td><td style="padding:7px 12px;border-bottom:1px solid #21262d">{tok}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e;border-bottom:1px solid #21262d">MT5 Login</td><td style="padding:7px 12px;border-bottom:1px solid #21262d">{login}</td></tr>
    <tr><td style="padding:7px 12px;color:#8b949e">Last Error</td><td style="padding:7px 12px;color:#f85149">{bot_status["error"]}</td></tr>
    </table>
    <br><p style="color:#484f58;font-size:12px">🟡 London 12:30–15:30 IST &nbsp;|&nbsp; 🔵 NY 17:30–20:30 IST<br>Auto-refreshes every 30s</p>
    </body></html>""", 200

@app.route("/api/status")
def api(): return jsonify({**bot_status,"kz":is_kz(),"ist":ist_now().strftime("%H:%M:%S"),"trade":trade_active})

if __name__ == "__main__":
    threading.Thread(target=bot_loop,daemon=True).start()
    port=int(os.environ.get("PORT",5000))
    log.info(f"🌐 Flask on port {port}")
    app.run(host="0.0.0.0",port=port,use_reloader=False)

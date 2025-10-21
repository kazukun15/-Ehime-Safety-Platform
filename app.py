# -*- coding: utf-8 -*-
# 愛媛セーフティ・プラットフォーム v9.9-A8 (ticker: seamless loop)
# - トップの電光掲示板を無限ループ化（シームレス）
# - 速度は 45s（CSSの animation-duration を変更すれば調整可）
# - 既存機能維持：JARTIC点/線、OSMスナップ(0〜10km)、危険交差点ON/OFF、県警速報→位置推定 等
#
# 依存:
#   pip install streamlit pydeck pandas requests httpx beautifulsoup4 rapidfuzz h3 streamlit-autorefresh

import os, re, math, time, json, sqlite3, threading, unicodedata, hashlib
from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor
from io import StringIO

import httpx
import requests
import pandas as pd
import streamlit as st
import pydeck as pdk
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process as rf_process
import h3
from streamlit_autorefresh import st_autorefresh

# === Gemini (optional) ===
try:
    import google.generativeai as genai
    _HAS_GEMINI = True
except Exception:
    _HAS_GEMINI = False

APP_TITLE = "愛媛セーフティ・プラットフォーム"
SUBTITLE = "Save Your Self"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/9.9-A8 (ticker_loop+snap_subpath_0_10km)"
TIMEOUT = 15
TTL_HTML = 600
MAX_WORKERS = 6

EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650
EHIME_BBOX = (132.2, 33.0, 133.7, 34.2)  # (minLon, minLat, maxLon, maxLat)

FUTURE_BUFFER_SCALE = 1.8
ZOOM_LIKE = 10
FANOUT_THRESHOLD = 4
LABEL_SCALE = 1.0
MAX_LABELS = 400

CATEGORY_PATTERNS = [
    ("交通事故", r"交通.*事故|自転車|バス|二輪|乗用|衝突|交差点|国道|県道|人身事故"),
    ("火災",     r"火災|出火|全焼|半焼|延焼"),
    ("死亡事案", r"死亡|死亡事案"),
    ("窃盗",     r"窃盗|万引|盗"),
    ("詐欺",     r"詐欺|還付金|投資詐欺|特殊詐欺"),
    ("事件",     r"威力業務妨害|条例違反|暴行|傷害|脅迫|器物損壊|青少年保護"),
]
CITY_NAMES = [
    "松山市","今治市","新居浜市","西条市","大洲市","伊予市","四国中央市",
    "西予市","東温市","上島町","久万高原町","松前町","砥部町","内子町",
    "伊方町","松野町","鬼北町","愛南町","宇和島市","八幡浜市"
]
MUNI_CENTERS = {
    "松山市":(132.7650,33.8390),"今治市":(133.0000,34.0660),"新居浜市":(133.2830,33.9600),
    "西条市":(133.1830,33.9180),"大洲市":(132.5500,33.5000),"伊予市":(132.7010,33.7550),
    "四国中央市":(133.5500,33.9800),"西予市":(132.5000,33.3660),"東温市":(132.8710,33.7930),
    "上島町":(133.2000,34.2600),"久万高原町":(132.9040,33.5380),"松前町":(132.7110,33.7870),
    "砥部町":(132.7870,33.7350),"内子町":(132.6580,33.5360),"伊方町":(132.3560,33.4880),
    "松野町":(132.7570,33.2260),"鬼北町":(132.8800,33.2280),"愛南町":(132.5660,33.0000),
    "宇和島市":(132.5600,33.2230),"八幡浜市":(132.4230,33.4620),
}

TILESETS: Dict[str, Dict] = {
    "標準":     {"url":"https://tile.openstreetmap.org/{z}/{x}/{y}.png", "max_zoom":19},
    "淡色":     {"url":"https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom":18},
    "地形":     {"url":"https://a.tile.opentopomap.org/{z}/{x}/{y}.png", "max_zoom":17},
    "人道支援": {"url":"https://tile-a.openstreetmap.fr/hot/{z}/{x}/{y}.png", "max_zoom":19},
    "航空写真": {"url":"https://cyberjapandata.gsi.go.jp/xyz/seamlessphoto/{z}/{x}/{y}.jpg", "max_zoom":18},
}

# ----------------------------------------------------------------------------
# UI / CSS
# ----------------------------------------------------------------------------
st.set_page_config(page_title=APP_TITLE, layout="wide")
st.markdown("""
<style>
  :root{ --bg:#0b0f14; --panel:#0f141b; --panel2:#121924; --text:#e8f1ff; --muted:#8aa0b6; --border:#2b3a4d; --a:#007aff; --b:#00b894; }
  @media (prefers-color-scheme: light){ :root{ --bg:#f7fafc; --panel:#ffffff; --panel2:#f1f5f9; --text:#0f2230; --muted:#586b7a; --border:#dfe7ef; --a:#005acb; --b:#009a7a; } }
  html, body, .stApp { background: var(--bg); color: var(--text); }
  .topbar{ position: sticky; top:0; z-index:10; padding:14px 16px; margin:-16px -16px 14px -16px; border-bottom:1px solid var(--border); background:var(--panel); }
  .brand{ display:flex; align-items:center; gap:10px; font-weight:800; font-size:1.05rem; }
  .brand .id{ width:28px; height:28px; border-radius:8px; display:grid; place-items:center; background: linear-gradient(135deg,var(--a),var(--b)); color:#00131a; font-weight:900; }
  .subnote{ color: var(--muted); font-size:.85rem; margin-top:4px}
  .panel { background: var(--panel); border:1px solid var(--border); border-radius: 14px; padding: 10px 12px; }
  .legend { font-size:.95rem; background:var(--panel); border:1px solid var(--border); border-radius:12px; padding:10px 12px;}
  .legend .item { display:inline-flex; align-items:center; margin-right:14px; margin-bottom:6px}
  .dot { width:12px; height:12px; border-radius:50%; display:inline-block; margin-right:6px; border:1px solid #0003}
  .feed-card {background:var(--panel); padding:12px 14px; border-radius:14px; border:1px solid var(--border); margin-bottom:10px;}
  .feed-scroll {max-height:62vh; overflow-y:auto; padding-right:6px}
  @media (max-width: 640px){ .feed-scroll{max-height:48vh} }
  a { color: var(--a); }
  .riskbar{height:10px; border-radius:6px; background:linear-gradient(90deg,#ffd4d4,#ff6b6b,#d90429);}
  .risklbl{display:flex; justify-content:space-between; font-size:.85rem; color: var(--muted); margin-top:4px}
  .hud { position: relative; height:0; }
  .hud-inner { position: relative; top:-36px; left:6px; display:flex; gap:6px; flex-wrap:wrap; }
  .hud .badge { background:rgba(16,20,27,.88); color:#e8f1ff; border:1px solid var(--border); padding:4px 8px; border-radius:10px; font-size:.85rem; }
  @media (prefers-color-scheme: light){ .hud .badge{ background:rgba(255,255,255,.9); color:#0f2230; } }
  .jartic-grad { height: 10px; border-radius:6px; background: linear-gradient(90deg, #3c78c8, #4ec67a, #f0d438, #e63c3c); }
  .redline-sample { height: 0; border-top:4px solid #e60000; width: 80px; border-radius:2px; }

  /* ★ Seamless ticker (loop) */
  .ticker-wrap{ position:sticky; top:58px; z-index:9; margin:-12px -16px 10px -16px;
                background:var(--panel2); border-bottom:1px solid var(--border); overflow:hidden; }
  .ticker{ display:flex; gap:60px; white-space:nowrap; padding:6px 0;
           will-change: transform; animation: ticker-move 45s linear infinite; }
  .ticker:hover{ animation-play-state: paused; }
  .ticker-seq{ display:inline-block; }
  @keyframes ticker-move {
    0%   { transform: translateX(0); }
    100% { transform: translateX(-50%); } /* 2列分のうち半分だけ左へ → 途切れず無限ループ */
  }
  @media (prefers-reduced-motion: reduce){
    .ticker{ animation: none; }
  }
</style>
""", unsafe_allow_html=True)

st.markdown(
    "<div class='topbar'><div class='brand'><div class='id'>ES</div>"
    f"<div><div>{APP_TITLE}</div><div class='subnote'>{SUBTITLE}</div></div>"
    "</div></div>", unsafe_allow_html=True
)

# ----------------------------------------------------------------------------
# Session state
# ----------------------------------------------------------------------------
if "map_choice" not in st.session_state:
    st.session_state.map_choice = "標準"
if "show_jartic_points" not in st.session_state:
    st.session_state.show_jartic_points = True
if "show_snap_lines" not in st.session_state:
    st.session_state.show_snap_lines = True
if "show_hotspots" not in st.session_state:
    st.session_state.show_hotspots = True

# ----------------------------------------------------------------------------
# SQLite cache
# ----------------------------------------------------------------------------
@st.cache_resource
def get_sqlite():
    os.makedirs("data", exist_ok=True)
    conn = sqlite3.connect("data/esp_cache.sqlite", check_same_thread=False)
    with conn:
        conn.execute("CREATE TABLE IF NOT EXISTS geocode_cache(key TEXT PRIMARY KEY, json TEXT, created_at TEXT)")
        conn.execute("CREATE TABLE IF NOT EXISTS llm_cache(key TEXT PRIMARY KEY, json TEXT, created_at TEXT)")
    return conn
_conn = get_sqlite(); _conn_lock = threading.Lock()
def cache_get(table:str, key:str) -> Optional[str]:
    with _conn_lock:
        row = _conn.execute(f"SELECT json FROM {table} WHERE key=?", (key,)).fetchone()
    return row[0] if row else None
def cache_put(table:str, key:str, payload:str):
    with _conn_lock, _conn:
        _conn.execute(f"INSERT OR REPLACE INTO {table} VALUES (?,?,datetime('now'))", (key, payload))

# ----------------------------------------------------------------------------
# 県警速報の取得・解析
# ----------------------------------------------------------------------------
@dataclass
class IncidentItem:
    heading: str
    body: str
    incident_date: Optional[str]

@st.cache_data(ttl=TTL_HTML)
def fetch_ehime_html() -> str:
    headers = {"User-Agent": USER_AGENT}
    for attempt in range(3):
        try:
            with httpx.Client(headers=headers, timeout=TIMEOUT) as client:
                r = client.get(EHIME_POLICE_URL)
                if r.status_code in (429, 503):
                    raise httpx.HTTPStatusError("rate limited", request=None, response=r)
                r.raise_for_status()
                enc = r.encoding or 'utf-8'
                try:
                    r.encoding = r.apparent_encoding or enc
                except Exception:
                    r.encoding = enc
                return r.text
        except Exception:
            time.sleep(0.6 * (attempt + 1))
    try:
        r = requests.get(EHIME_POLICE_URL, headers=headers, timeout=TIMEOUT)
        r.raise_for_status()
        r.encoding = r.apparent_encoding or r.encoding or "utf-8"
        return r.text
    except Exception:
        st.warning("速報ページの取得に失敗しました。空データで表示します。")
        return "<html><body></body></html>"

def parse_items(html: str) -> List[IncidentItem]:
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)
    text = re.sub(r"【愛媛県警からのお願い！】[\s\S]*?(?=■|$)", "", text)
    lines = [ln for ln in text.split("\n") if ln.strip()]
    items, cur = [], None
    for ln in lines:
        if ln.startswith("■"):
            if cur: items.append(cur)
            cur = {"heading": ln.strip(), "body": []}
        else:
            if cur: cur["body"].append(ln.strip())
    if cur: items.append(cur)

    out: List[IncidentItem] = []
    today = datetime.now().date(); cy = today.year
    for b in items:
        h = b.get("heading", ""); body = " ".join(b.get("body", []))
        m = re.search(r"（?(\d{1,2})月(\d{1,2})日", h)
        d = None
        if m:
            mm, dd = int(m.group(1)), int(m.group(2)); y = cy
            try:
                dt = datetime(y, mm, dd).date();  y -= 1 if dt > today else 0
                d = datetime(y, mm, dd).date().isoformat()
            except Exception:
                d = None
        out.append(IncidentItem(h.replace("■", "").strip(), body, d))
    return out

def rule_extract(it: IncidentItem) -> Dict:
    t = it.heading + " " + it.body
    cat = next((name for name, pat in CATEGORY_PATTERNS if re.search(pat, t)), "その他")
    muni = next((c for c in CITY_NAMES if c in t), None)
    hints = ["小学校","中学校","高校","大学","学校","グラウンド","体育館","公園","駅","港","病院","交差点"]
    places: List[str] = []
    for h in hints:
        places += re.findall(rf"([\w\u3040-\u30ff\u4e00-\u9fffA-Za-z0-9]+{h})", t)[:2]
    s = re.sub(r"\s+", " ", it.body).strip()
    s = s[:120] + ("…" if len(s)>120 else "")
    return {"category":cat,"municipality":muni,"place_strings":list(dict.fromkeys(places))[:3],
            "summary": s or it.heading, "date": it.incident_date}

@st.cache_resource
def load_gazetteer(path:str) -> Optional[pd.DataFrame]:
    try:
        df = pd.read_csv(path)
        for c in ("name","type","lon","lat"):
            if c not in df.columns: return None
        df["alt_names"] = df.get("alt_names", "").fillna("")
        return df
    except Exception:
        return None

class GazetteerIndex:
    def __init__(self, df: pd.DataFrame):
        self.df = df.reset_index(drop=True)
        self.keys = (df["name"].astype(str) + " | " + df["alt_names"].astype(str)).tolist()
    def search(self, q:str, min_score:int=78) -> Optional[Tuple[float,float,str]]:
        m = self.df[(self.df["name"].str.contains(q, na=False)) | (self.df["alt_names"].str.contains(q, na=False))]
        if not m.empty:
            r = m.iloc[0]; return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        hit = rf_process.extractOne(q, self.keys, scorer=fuzz.token_set_ratio)
        if hit and hit[1] >= min_score:
            r = self.df.iloc[hit[2]]; return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        return None

def nominatim_geocode(name:str, municipality:Optional[str]) -> Optional[Tuple[float,float]]:
    try:
        q = f"{name} {municipality or ''} 愛媛県 日本".strip()
        headers = {"User-Agent": USER_AGENT}
        params = {"q": q, "format": "jsonv2", "limit": 1}
        for i in range(3):
            r = requests.get("https://nominatim.openstreetmap.org/search", params=params, headers=headers, timeout=TIMEOUT)
            if r.status_code in (429,503):
                time.sleep(0.6 * (i+1)); continue
            r.raise_for_status()
            arr = r.json()
            if isinstance(arr, list) and arr:
                return float(arr[0]["lon"]), float(arr[0]["lat"])  # lon, lat
        return None
    except Exception:
        return None

def _read_gemini_key() -> str:
    try:
        if "gemini" in st.secrets and "API_KEY" in st.secrets["gemini"]:
            return st.secrets["gemini"]["API_KEY"]
    except Exception:
        pass
    return os.getenv("GEMINI_API_KEY", "")

def gemini_candidates(full_text: str, muni_hint: Optional[str]) -> List[Dict]:
    api_key = _read_gemini_key()
    if not (_HAS_GEMINI and api_key):
        return []
    key = hashlib.sha1(f"gem9|{muni_hint or ''}|{full_text}".encode("utf-8")).hexdigest()
    cached = cache_get("llm_cache", key)
    if cached:
        try:
            obj = json.loads(cached)
            return obj.get("candidates", []) if isinstance(obj, dict) else []
        except Exception:
            pass
    try:
        genai.configure(api_key=api_key)
        model = genai.GenerativeModel("gemini-2.5-flash")
        system = ("あなたは日本のガゼッティア補助エージェントです。"
                  "入力の事件・事故テキストから、地名や施設名候補を抽出します。"
                  "出力は {\"candidates\":[{\"name\":str,\"kind\":str,\"confidence\":0..1}]}")
        muni_line = f"市町ヒント: {muni_hint}\n" if muni_hint else ""
        prompt = f"{system}\n\nテキスト:\n{full_text}\n\n{muni_line}JSONのみで応答。"
        resp = model.generate_content(prompt)
        txt = resp.text if hasattr(resp, "text") else str(resp)
        start = txt.find("{"); end = txt.rfind("}")
        if start >=0 and end>start: txt = txt[start:end+1]
        obj = json.loads(txt)
        if isinstance(obj, dict):
            cache_put("llm_cache", key, json.dumps(obj, ensure_ascii=False))
            return obj.get("candidates", [])
    except Exception:
        return []
    return []

# ----------------------------------------------------------------------------
# H3 & helpers
# ----------------------------------------------------------------------------
def h3_cell_from_latlng(lat: float, lon: float, res: int) -> str:
    if hasattr(h3, "geo_to_h3"): return h3.geo_to_h3(lat, lon, res)
    return h3.latlng_to_cell(lat, lon, res)
def h3_latlng_from_cell(cell: str) -> Tuple[float,float]:
    if hasattr(h3, "h3_to_geo"):
        lat, lon = h3.h3_to_geo(cell); return lat, lon
    lat, lon = h3.cell_to_latlng(cell); return lat, lon
def h3_res_from_zoom(zoom_val:int) -> int:
    return {7:5,8:6,9:7,10:8,11:9,12:9,13:10,14:10}.get(zoom_val, 8)
def cluster_points(df: pd.DataFrame, zoom_val:int) -> List[Dict]:
    if df.empty: return []
    res = h3_res_from_zoom(zoom_val)
    groups: Dict[str, List[Dict]] = {}
    for _, r in df.iterrows():
        lon, lat = float(r["lon"]), float(r["lat"])
        cell = h3_cell_from_latlng(lat, lon, res)
        d = r.to_dict(); d["cell"] = cell
        groups.setdefault(cell, []).append(d)
    centers: List[Dict] = []
    for cell, rows in groups.items():
        lat, lon = h3_latlng_from_cell(cell)
        centers.append({"cell":cell, "lon":lon, "lat":lat, "count":len(rows), "rows":rows})
    return centers

def short_summary(s: str, max_len: int = 64) -> str:
    s = re.sub(r"\s+", " ", s or "").strip()
    return (s[:max_len] + ("…" if len(s) > max_len else "")) if s else ""

def make_prediction(category:str, muni:Optional[str]) -> str:
    return {
        "詐欺":"SNSや投資の誘いに注意。送金前に家族や警察へ相談。",
        "交通事故":"夕方や雨天の交差点で増えやすい。横断と右左折に注意。",
        "窃盗":"自転車・車両の施錠と防犯登録。夜間の無施錠放置を避ける。",
        "火災":"乾燥時は屋外火気に配慮。電源周り・喫煙の始末を再確認。",
        "事件":"不審連絡は記録を残し通報。学校・公共施設周辺で意識を。",
        "死亡事案":"詳細は出典で確認。周辺では救急活動に配慮。",
    }.get(category, "同種事案が続く可能性。出典で最新を確認。")

CAT_STYLE = {
    "交通事故": {"color":[220, 60, 60, 235],   "radius":86, "icon":"▲"},
    "火災":     {"color":[245, 130, 50, 235],  "radius":88, "icon":"🔥"},
    "死亡事案": {"color":[170, 120, 240, 235], "radius":92, "icon":"✖"},
    "窃盗":     {"color":[70, 150, 245, 235],  "radius":78, "icon":"🔓"},
    "詐欺":     {"color":[40, 180, 160, 235],  "radius":78, "icon":"⚠"},
    "事件":     {"color":[245, 200, 60, 235],  "radius":82, "icon":"！"},
    "その他":   {"color":[128, 144, 160, 220], "radius":70, "icon":"・"},
}

def make_incident_info_html(c:str, s:str, m:str, pred:str) -> str:
    parts = []
    if c: parts.append(f"<b>{c}</b>")
    if s: parts.append(s)
    if m: parts.append(m)
    if pred: parts.append(f"予測: {pred}")
    parts.append(f"<a href='{EHIME_POLICE_URL}' target='_blank'>出典</a>")
    return "<div style='min-width:240px'>" + "<br/>".join(parts) + "</div>"

def make_jartic_info_html(tlabel:str, total:int, up:int, down:int) -> str:
    return (
        "<div style='min-width:240px'>"
        "<b>JARTIC（5分値）</b><br/>"
        f"時刻: {tlabel}<br/>"
        f"合計: {total} 台/5分<br/>"
        f"上り: {up} / 下り: {down}"
        "</div>"
    )

# ----------------------------------------------------------------------------
# JARTIC Open Traffic (5分値)
# ----------------------------------------------------------------------------
JARTIC_WFS_URL = "https://api.jartic-open-traffic.org/geoserver"

def jst_now() -> datetime:
    return datetime.utcnow() + timedelta(hours=9)

def round_to_5min(d: datetime) -> datetime:
    mm = (d.minute // 5) * 5
    return d.replace(minute=mm, second=0, microsecond=0)

@st.cache_data(ttl=180)
def fetch_jartic_5min(bbox: Tuple[float,float,float,float] = EHIME_BBOX) -> Tuple[Optional[Dict], Optional[str]]:
    # 約20分遅延、5分刻み
    t = round_to_5min(jst_now() - timedelta(minutes=20))
    tcode = t.strftime("%Y%m%d%H%M")
    tlabel = t.strftime("%Y-%m-%d %H:%M (JST)")
    cql = (
        f"道路種別=3 AND 時間コード={tcode} AND "
        f"BBOX(ジオメトリ,{bbox[0]},{bbox[1]},{bbox[2]},{bbox[3]},'EPSG:4326')"
    )
    params = {
        "service": "WFS", "version": "2.0.0", "request": "GetFeature",
        "typeNames": "t_travospublic_measure_5m",
        "srsName": "EPSG:4326", "outputFormat": "application/json",
        "exceptions": "application/json", "cql_filter": cql
    }
    try:
        r = requests.get(JARTIC_WFS_URL, params=params, timeout=TIMEOUT)
        r.raise_for_status()
        return r.json(), tlabel
    except Exception:
        return None, None

def jartic_features_to_points(geojson: Dict, tlabel: str) -> List[Dict]:
    if not geojson or "features" not in geojson: return []
    pts: List[Dict] = []
    for f in geojson["features"]:
        g = f.get("geometry") or {}
        if g.get("type") == "MultiPoint":
            prop = f.get("properties", {}) or {}
            up = sum(filter(None, [
                prop.get("上り・小型交通量"), prop.get("上り・大型交通量"), prop.get("上り・車種判別不能交通量")
            ]))
            down = sum(filter(None, [
                prop.get("下り・小型交通量"), prop.get("下り・大型交通量"), prop.get("下り・車種判別不能交通量")
            ]))
            up = int(up or 0); down = int(down or 0); total = up + down
            for lon, lat in g.get("coordinates", []):
                pts.append({
                    "position":[float(lon), float(lat)],
                    "up": up, "down": down, "total": total,
                    "jt_time": tlabel, "jt_total": total, "jt_up": up, "jt_down": down,
                })
    return pts

def color_from_total(total:int) -> List[int]:
    # 青→緑→黄→赤
    t = min(1.0, max(0.0, total / 600.0))
    if t < 0.33:
        u = t/0.33; r = int(60*(1-u)+60*u); g = int(120*(1-u)+200*u); b = int(200*(1-u)+80*u)
    elif t < 0.66:
        u = (t-0.33)/0.33; r = int(60*(1-u)+240*u); g = int(200*(1-u)+220*u); b = int(80*(1-u)+20*u)
    else:
        u = (t-0.66)/0.34; r = int(240); g = int(220*(1-u)+60*u); b = 20
    return [r,g,b, 230]

def size_from_total(total:int) -> int:
    return 52 + int(min(260, total * 0.9))

# ----------------------------------------------------------------------------
# OSM（Overpass）＆擬似渋滞線（赤）0〜10km：ウェイに沿ったサブパス抽出
# ----------------------------------------------------------------------------
OVERPASS_URL = "https://overpass-api.de/api/interpreter"

@st.cache_data(ttl=600)
def fetch_osm_roads_overpass(bbox: Tuple[float,float,float,float] = EHIME_BBOX) -> List[Dict]:
    minLon, minLat, maxLon, maxLat = bbox
    q = f"""
    [out:json][timeout:25];
    (
      way["highway"~"^(motorway|trunk|primary|secondary|tertiary)$"]({minLat},{minLon},{maxLat},{maxLon});
    );
    out tags geom;
    """
    try:
        r = requests.post(OVERPASS_URL, data={"data": q}, timeout=TIMEOUT)
        r.raise_for_status()
        data = r.json()
        out: List[Dict] = []
        for el in data.get("elements", []):
            if el.get("type") == "way" and "geometry" in el:
                coords = [[pt["lon"], pt["lat"]] for pt in el["geometry"]]
                if len(coords) >= 2:
                    tags = el.get("tags", {}) or {}
                    oneway = str(tags.get("oneway","no")).lower() in ("yes","1","true")
                    out.append({"coords": coords, "oneway": oneway})
        return out
    except Exception:
        return []

def _meters_scale(lat: float) -> Tuple[float,float]:
    return 111320 * math.cos(math.radians(lat)), 110540

def _dist_m(a: Tuple[float,float], b: Tuple[float,float]) -> float:
    (lon1,lat1),(lon2,lat2) = a,b
    kx, ky = _meters_scale((lat1+lat2)/2)
    return math.hypot((lon2-lon1)*kx, (lat2-lat1)*ky)

def _project_to_segment(p: Tuple[float,float], a: Tuple[float,float], b: Tuple[float,float]) -> Tuple[Tuple[float,float], float, float]:
    ax, ay = a; bx, by = b; px, py = p
    kx, ky = _meters_scale((ay+by)/2)
    ax2, ay2, bx2, by2, px2, py2 = ax*kx, ay*ky, bx*kx, by*ky, px*kx, py*ky
    vx, vy = bx2-ax2, by2-ay2; wx, wy = px2-ax2, py2-ay2
    seglen2 = vx*vx + vy*vy
    if seglen2 == 0:
        return a, 0.0, math.hypot(px2-ax2, py2-ay2)
    t = max(0.0, min(1.0, (wx*vx + wy*vy) / seglen2))
    projx2, projy2 = ax2 + t*vx, ay2 + t*vy
    proj = (projx2 / kx, projy2 / ky)
    dist_m = math.hypot(px2-projx2, py2-projy2)
    return proj, t, dist_m

def _nearest_point_on_way(p: Tuple[float,float], way_coords: List[List[float]]) -> Tuple[int, float, Tuple[float,float], float]:
    best = (0, 0.0, tuple(way_coords[0]), float("inf"))
    for i in range(len(way_coords)-1):
        a = tuple(way_coords[i]); b = tuple(way_coords[i+1])
        proj, t, d = _project_to_segment(p, a, b)
        if d < best[3]:
            best = (i, t, proj, d)
    return best

def _subpath_centered_on(way_coords: List[List[float]], seg_idx: int, t: float, length_m: float) -> List[List[float]]:
    if length_m <= 0:
        length_m = 1.0
    half = length_m / 2.0
    a = way_coords[seg_idx]; b = way_coords[seg_idx+1]
    ax, ay = a; bx, by = b
    proj = [ax + (bx-ax)*t, ay + (by-ay)*t]

    back_pts: List[List[float]] = [proj]
    remain = half; i = seg_idx; cur = proj
    while i >= 0 and remain > 0:
        prev = way_coords[i]
        d = _dist_m(tuple(cur), tuple(prev))
        if d >= remain:
            ratio = remain / d if d > 0 else 0
            x = cur[0] + (prev[0]-cur[0]) * ratio
            y = cur[1] + (prev[1]-cur[1]) * ratio
            back_pts.append([x,y]); remain = 0; break
        else:
            back_pts.append(prev); remain -= d; cur = prev; i -= 1

    fwd_pts: List[List[float]] = [proj]
    remain = half; i = seg_idx + 1; cur = proj
    while i < len(way_coords) and remain > 0:
        nxt = way_coords[i]
        d = _dist_m(tuple(cur), tuple(nxt))
        if d >= remain:
            ratio = remain / d if d > 0 else 0
            x = cur[0] + (nxt[0]-cur[0]) * ratio
            y = cur[1] + (nxt[1]-cur[1]) * ratio
            fwd_pts.append([x,y]); remain = 0; break
        else:
            fwd_pts.append(nxt); remain -= d; cur = nxt; i += 1

    back_pts = back_pts[::-1]
    path = back_pts + fwd_pts[1:]
    if len(path) < 2:
        path.append(path[0][:])
    return path

@st.cache_data(ttl=180)
def build_snap_lines(j_points: List[Dict], ways: List[Dict],
                     base_min: int = 0, base_max: int = 10_000, thresh_m: int = 220) -> List[Dict]:
    out: List[Dict] = []
    if not j_points: return out
    RED = [230, 0, 0, 235]
    for jp in j_points:
        lon, lat = jp["position"]; p = (lon, lat)
        total = int(jp.get("total", jp.get("jt_total", 0)))
        length_m = max(base_min, min(base_max, total * 20.0))  # 0〜10km

        best = None
        for wi, way in enumerate(ways):
            coords = way["coords"]
            seg_idx, t, proj, d = _nearest_point_on_way(p, coords)
            if (best is None) or (d < best[0]):
                best = (d, wi, seg_idx, t, proj)

        if best and best[0] <= thresh_m:
            _, wi, seg_idx, t, _ = best
            coords = ways[wi]["coords"]
            path = _subpath_centered_on(coords, seg_idx, t, length_m)
        else:
            kx, _ = _meters_scale(lat)
            half = length_m / 2.0
            dx_deg = half / max(kx, 1e-6)
            p1 = [lon - dx_deg, lat]; p2 = [lon + dx_deg, lat]
            path = [p1, p2]

        width_px = 5 + min(14, (total // 100))
        out.append({
            "path": path, "color": RED, "width": width_px,
            "info_html": make_jartic_info_html(
                jp.get("jt_time"), jp.get("jt_total", 0), jp.get("jt_up", 0), jp.get("jt_down", 0)
            ),
        })
    return out

# ----------------------------------------------------------------------------
# Pipeline: 県警速報→位置推定
# ----------------------------------------------------------------------------
with st.spinner("速報を取得中…"):
    html = fetch_ehime_html()
raw_items = parse_items(html)
extracted: List[Dict] = []
for it in raw_items:
    ex = rule_extract(it); ex["heading"] = it.heading; ex["full_text"] = (it.heading + " " + it.body).strip()
    extracted.append(ex)

gdf = load_gazetteer("data/gazetteer_ehime.csv")
idx = GazetteerIndex(gdf) if gdf is not None else None
def try_gazetteer(name:str, min_score:int=78) -> Optional[Tuple[float,float,str]]:
    return None if not idx else idx.search(name, min_score)

def resolve_loc(ex: Dict) -> Dict:
    muni = ex.get("municipality"); places = ex.get("place_strings") or []
    full_text = ex.get("full_text", "")
    llm_cands = gemini_candidates(full_text, muni)
    cand_names = [c.get("name","") for c in llm_cands if isinstance(c, dict)]
    queries = [q for q in cand_names if q] + places + ([muni] if muni else [])
    for q in queries:
        hit = try_gazetteer(q, 78)
        if hit:
            lon, lat, typ = hit; return {"lon":lon, "lat":lat, "type":typ or "facility"}
    if muni and muni in MUNI_CENTERS:
        lon, lat = MUNI_CENTERS[muni]; return {"lon":lon, "lat":lat, "type":"city"}
    for q in queries:
        ll = nominatim_geocode(q, muni)
        if ll: return {"lon":ll[0], "lat":ll[1], "type":"facility"}
    return {"lon":EHIME_PREF_LON, "lat":EHIME_PREF_LAT, "type":"pref"}

with ThreadPoolExecutor(max_workers=MAX_WORKERS) as exctr:
    results = list(exctr.map(resolve_loc, extracted))

rows: List[Dict] = []
for ex, loc in zip(extracted, results):
    typ = loc.get("type","city")
    base_radius = {"facility":300,"intersection":250,"town":600,"chome":600,"oaza":900,"aza":900,"city":2000,"pref":2500}.get(typ, 1200)
    radius = int(base_radius * FUTURE_BUFFER_SCALE)
    rows.append({
        "lon": float(loc["lon"]), "lat": float(loc["lat"]),
        "category": ex["category"], "summary": short_summary(ex["summary"], 60),
        "municipality": ex.get("municipality") or "",
        "radius_m": radius,
        "pred": make_prediction(ex["category"], ex.get("municipality")),
        "src": EHIME_POLICE_URL,
    })
df = pd.DataFrame(rows)

# 多発交差点（内蔵）
CSV_TEXT = """地点名,緯度,経度,年間最多事故件数,補足
天山交差点,33.8223,132.7758,6,松山市天山町付近（2023年に6件事故）
和泉交差点,33.8216,132.7554,5,松山市和泉町付近（2023年に5件事故）
小坂交差点,33.8266,132.7833,5,松山市枝松地区（2023年に5件事故）
本町5丁目交差点,33.8530,132.7588,4,松山市中心部（2023年に4件事故）
山越交差点,33.8565,132.7592,4,松山市山越（2023年に4件事故）
消防局前交差点,33.8527,132.7588,4,松山市本町6丁目（2023年に4件事故）
大川橋交差点,33.8739,132.7521,4,松山市鴨川町（2023年に4件事故）
久米交差点,33.8143,132.7957,4,松山市久米地区（2023年に4件事故）
"""
hot_df = pd.read_csv(StringIO(CSV_TEXT))
hot_df.rename(columns={"地点名":"name","緯度":"lat","経度":"lon","年間最多事故件数":"count","補足":"note"}, inplace=True)
hot_df["lat"] = hot_df["lat"].astype(float); hot_df["lon"] = hot_df["lon"].astype(float)
hot_df["count"] = hot_df["count"].astype(int)
max_count = int(hot_df["count"].max()) if not hot_df.empty else 1
hot_df["position"] = hot_df.apply(lambda r: [float(r["lon"]), float(r["lat"])], axis=1)
hot_df["weight"] = hot_df["count"].astype(float)
def _cfc(c:int) -> List[int]:
    t = max(0.0, min(1.0, (c-1) / max(1, max_count-1)))
    if t < 0.5:
        u = t/0.5; r = int(255*(1-u)+255*u); g = int(212*(1-u)+107*u); b = int(212*(1-u)+107*u)
    else:
        u = (t-0.5)/0.5; r = int(255*(1-u)+217*u); g = int(107*(1-u)+4*u); b = int(107*(1-u)+41*u)
    return [r,g,b, 190 if c>=5 else 180]
hot_df["rgba"] = hot_df["count"].apply(_cfc)
hot_df["elev"] = hot_df["count"].apply(lambda c: 300 + (c-1)*220)

# ----------------------------------------------------------------------------
# JARTICデータ（prefetch）→ ティッカーにも利用
# ----------------------------------------------------------------------------
gj_prefetch, tlabel_prefetch = fetch_jartic_5min(EHIME_BBOX)
j_points_prefetch: List[Dict] = (jartic_features_to_points(gj_prefetch, tlabel_prefetch)
                                 if (gj_prefetch and tlabel_prefetch) else [])

def build_ticker_items(incidents_df: pd.DataFrame, jpts: List[Dict], tlabel: Optional[str]) -> List[str]:
    items: List[str] = []
    for _, r in incidents_df.head(12).iterrows():
        cat = r.get("category",""); muni = r.get("municipality","") or ""; s = r.get("summary","")
        if s: items.append(f"{muni} {s}")
    if jpts and tlabel:
        top = sorted(jpts, key=lambda p: p.get("total",0), reverse=True)[:8]
        for p in top:
            total, up, down = p.get("total",0), p.get("up",0), p.get("down",0)
            items.append(f"【交通量 {tlabel}】合計{total}台/5分（↑{up} / ↓{down}）")
    return items

def render_ticker_html(lines: List[str]) -> None:
    if not lines: return
    # 同じシーケンスを2回並べて、translateX(-50%) の無限ループで切れ目なく流す
    text = "　｜　".join(lines)
    html = (
        "<div class='ticker-wrap'>"
        "  <div class='ticker'>"
        f"    <span class='ticker-seq'>{text}</span>"
        f"    <span class='ticker-seq' aria-hidden='true'>{text}</span>"
        "  </div>"
        "</div>"
    )
    st.markdown(html, unsafe_allow_html=True)

# ★ ティッカー描画（最上部）
ticker_lines = build_ticker_items(df, j_points_prefetch, tlabel_prefetch)
render_ticker_html(ticker_lines)
# 自動更新（5分ごと）
st_autorefresh(interval=5*60*1000, key="ticker_refresh")

# ----------------------------------------------------------------------------
# Sidebar
# ----------------------------------------------------------------------------
with st.sidebar:
    st.markdown("<div class='panel'>", unsafe_allow_html=True)

    st.markdown("#### 表示期間")
    period = st.select_slider("表示期間を選択",
                              ["当日","過去3日","過去7日","過去30日"],
                              value="過去7日", label_visibility="collapsed")

    st.markdown("#### 表示モード")
    mode_3d = st.radio("2D / 3D", ["2D","3D"], horizontal=True, index=0)
    init_zoom = st.slider("初期ズーム", 8, 17, 11)

    st.markdown("#### JARTIC 交通量 (5分)")
    st.session_state.show_jartic_points = st.checkbox("JARTIC 5分値（点）",
                                                      value=bool(st.session_state.show_jartic_points))
    st.session_state.show_snap_lines   = st.checkbox("JARTIC 5分値（線：OSMスナップ）",
                                                      value=bool(st.session_state.show_snap_lines))
    st.caption("公開API / 約20分遅延。点=断面交通量、線=OSMウェイに沿ったサブパス（赤：0〜10km）。")

    st.markdown("#### 危ない交差点")
    st.session_state.show_hotspots = st.checkbox("ヒートマップ / 3D柱 を表示",
                                                 value=bool(st.session_state.show_hotspots))

    st.markdown("  ")
    st.markdown("#### 地図タイル")
    map_choice = st.selectbox("地図スタイル", list(TILESETS.keys()),
                              index=list(TILESETS.keys()).index(st.session_state.map_choice))
    st.session_state.map_choice = map_choice
    custom_tile = st.text_input("任意タイルURL（透過PNG推奨, {z}/{x}/{y})", "")

    st.markdown("</div>", unsafe_allow_html=True)

# ----------------------------------------------------------------------------
# Columns
# ----------------------------------------------------------------------------
col_map, col_feed = st.columns([7,5], gap="large")

with col_map:
    is_3d = (mode_3d == "3D")

    def build_base_layers(map_choice:str, custom_tile:str) -> List[pdk.Layer]:
        tile = TILESETS.get(map_choice, TILESETS["標準"])
        layers: List[pdk.Layer] = [pdk.Layer(
            "TileLayer", id=f"base-{map_choice}", data=tile["url"],
            min_zoom=0, max_zoom=tile.get("max_zoom",18), tile_size=256, opacity=1.0, refinement="no-overlap"
        )]
        if custom_tile.strip():
            layers.append(pdk.Layer("TileLayer", id="custom-overlay", data=custom_tile.strip(),
                                    min_zoom=0, max_zoom=22, tile_size=256, opacity=0.6, refinement="no-overlap"))
        return layers

    def build_intersection_layers(hot_df: pd.DataFrame, is_3d: bool) -> List[pdk.Layer]:
        if hot_df.empty or not st.session_state.show_hotspots: return []
        if is_3d:
            return [pdk.Layer("ColumnLayer", id="hot-columns", data=hot_df,
                              get_position="position", get_elevation="elev", elevation_scale=1.0,
                              radius=65, get_fill_color="rgba", pickable=True, extruded=True)]
        return [pdk.Layer("HeatmapLayer", id="hot-heatmap", data=hot_df,
                          get_position="position", get_weight="weight",
                          radius_pixels=60, intensity=0.85, threshold=0.05, opacity=0.35)]

    def build_congestion_grid(df: pd.DataFrame, is_3d: bool) -> List[pdk.Layer]:
        if is_3d or df.empty: return []
        acc = df[df["category"]=="交通事故"].copy()
        if acc.empty: return []
        acc["position"] = acc.apply(lambda r: [float(r["lon"]), float(r["lat"])], axis=1)
        acc["weight"] = 1.0
        return [pdk.Layer("GridLayer", id="congestion-grid", data=acc,
                          get_position="position", get_weight="weight",
                          cell_size=200, extruded=False, opacity=0.18, pickable=False,
                          colorRange=[
                              [255,180,180,60],[255,140,140,90],[255,100,100,120],
                              [230,60,60,150],[200,40,40,190],[180,20,20,220],
                          ])]

    def circle_coords(lon: float, lat: float, radius_m: int = 300, n: int = 64) -> List[List[float]]:
        out: List[List[float]] = []
        r_earth = 6378137.0
        dlat = radius_m / r_earth
        dlon = radius_m / (r_earth * math.cos(math.radians(lat)))
        for i in range(n):
            ang = 2 * math.pi * i / n
            lat_i = lat + math.degrees(dlat * math.sin(ang))
            lon_i = lon + math.degrees(dlon * math.cos(math.radians(lat)))
            out.append([lon_i, lat_i])
        out.append(out[0]); return out

    def spiderfy(clon: float, clat: float, n: int, base_px: int = 16, gap_px: int = 8) -> List[Tuple[float,float]]:
        out = []; rpx = base_px
        for k in range(n):
            ang = math.radians(137.5 * k)
            dx = rpx*math.cos(ang); dy = rpx*math.sin(ang)
            dlon = dx / (111320 * math.cos(math.radians(clat))); dlat = dy / 110540
            out.append((clon + dlon, clat + dlat)); rpx += gap_px
        return out

    def build_points_labels_buffers(df: pd.DataFrame) -> Tuple[List[Dict], List[Dict], List[Dict], List[Dict], Dict]:
        centers = cluster_points(df, ZOOM_LIKE)
        points: List[Dict] = []; icon_fg: List[Dict] = []; mini_fg: List[Dict] = []; mini_bg: List[Dict] = []
        features: List[Dict] = []
        for c in centers:
            cnt = c["count"]; clat, clon = c["lat"], c["lon"]
            if cnt <= FANOUT_THRESHOLD:
                offs = spiderfy(clon, clat, cnt)
                for (lon, lat), row in zip(offs, c["rows"]):
                    sty = CAT_STYLE.get(row["category"], CAT_STYLE["その他"])
                    p = {
                        "position":[lon,lat], "color":sty["color"], "radius":sty["radius"],
                        "info_html": make_incident_info_html(
                            row["category"], row.get("summary",""), row.get("municipality",""), row.get("pred","")
                        ),
                        "r":int(row.get("radius_m",600)),
                    }
                    points.append(p)
                    icon_fg.append({"position":[lon,lat], "label":sty["icon"], "tcolor":[255,255,255,235], "offset":[0,-2]})
                    if len(mini_fg) < MAX_LABELS:
                        vtxt = "\n".join(list(row.get("summary","")[:4]))
                        offset_px = int(-14*LABEL_SCALE)
                        mini_bg.append({"position":[lon,lat],"label":vtxt,"tcolor":[0,0,0,220],"offset":[0,offset_px]})
                        mini_fg.append({"position":[lon,lat],"label":vtxt,"tcolor":[255,255,255,235],"offset":[0,offset_px]})
            else:
                points.append({
                    "position":[clon,clat],"color":[100,100,100,210],"radius":70,
                    "info_html": make_incident_info_html("集中","周辺に多数","", ""), "r":0
                })
                icon_fg.append({"position":[clon,clat], "label":"◎", "tcolor":[255,255,255,230], "offset":[0,-2]})
        for p in points:
            if p.get("r",0) > 0:
                lon, lat = p["position"]
                features.append({"type":"Feature","geometry":{"type":"Polygon","coordinates":[circle_coords(lon, lat, int(p["r"]))]},"properties":{}})
        geojson = {"type":"FeatureCollection","features": features}
        return points, icon_fg, mini_fg, mini_bg, geojson

    layers: List[pdk.Layer] = []
    layers += build_base_layers(st.session_state.map_choice, custom_tile)
    layers += build_intersection_layers(hot_df, is_3d)
    layers += build_congestion_grid(df, is_3d)

    points, icon_labels, mini_fg, mini_bg, geojson = build_points_labels_buffers(df)
    layers += [
        pdk.Layer("GeoJsonLayer", id="approx-buffers", data=geojson, pickable=False, stroked=True, filled=True,
                  get_line_width=2, get_line_color=[0,160,220], get_fill_color=[0,160,220,40], auto_highlight=False),
        pdk.Layer("ScatterplotLayer", id="incident-points", data=points, get_position="position", get_fill_color="color", get_radius="radius",
                  pickable=True, radius_min_pixels=3, radius_max_pixels=60),
        pdk.Layer("TextLayer", id="icon-labels", data=icon_labels, get_position="position", get_text="label", get_color="tcolor",
                  get_size=14, get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        pdk.Layer("TextLayer", id="mini-labels-bg", data=mini_bg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*LABEL_SCALE), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        pdk.Layer("TextLayer", id="mini-labels-fg", data=mini_fg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*LABEL_SCALE), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
    ]

    # --- JARTIC（prefetch済みデータを利用） ---
    j_points = j_points_prefetch
    if st.session_state.show_jartic_points and j_points:
        pts_vis = [{
            "position": p["position"],
            "color": color_from_total(p["total"]),
            "radius": size_from_total(p["total"]),
            "info_html": make_jartic_info_html(p["jt_time"], p["jt_total"], p["jt_up"], p["jt_down"]),
        } for p in j_points]
        layers.append(
            pdk.Layer(
                "ScatterplotLayer", id="jartic-5min-points", data=pts_vis,
                get_position="position", get_fill_color="color", get_radius="radius",
                radius_min_pixels=4, radius_max_pixels=200, opacity=0.60, pickable=True
            )
        )

    if st.session_state.show_snap_lines and j_points:
        ways = fetch_osm_roads_overpass(EHIME_BBOX)
        lines = build_snap_lines(j_points, ways)
        if lines:
            layers.append(
                pdk.Layer(
                    "PathLayer", id="jartic-5min-snaplines", data=lines,
                    get_path="path", get_color="color", get_width="width",
                    width_scale=1, width_min_pixels=3, width_units="pixels",
                    opacity=0.98, pickable=True
                )
            )

    deck = pdk.Deck(
        layers=layers,
        initial_view_state=pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON,
                                         zoom=init_zoom, pitch=(45 if is_3d else 0), bearing=0),
        tooltip={"html": "{info_html}",
                 "style": {"backgroundColor":"rgba(10,15,20,.96)","color":"#e6f1ff",
                           "maxWidth":"380px","whiteSpace":"normal","wordBreak":"break-word",
                           "lineHeight":1.4,"fontSize":"12px","padding":"10px 12px",
                           "borderRadius":"12px","border":"1px solid var(--border)"}},
        map_provider=None, map_style=None
    )
    st.pydeck_chart(deck, use_container_width=True, height=640)

    st.markdown(
        "<div class='hud'><div class='hud-inner'>"
        f"<div class='badge'>Zoom: {init_zoom}（初期）</div>"
        "</div></div>", unsafe_allow_html=True
    )

    # 凡例
    legend_items = []
    for k, v in CAT_STYLE.items():
        rgba = f"rgba({v['color'][0]}, {v['color'][1]}, {v['color'][2]}, {v['color'][3]/255:.9f})"
        legend_items.append(f"<span class='item'><span class='dot' style='background:{rgba}'></span>{k}</span>")
    jartic_legend = (
        "<div style='margin-top:10px'>"
        "<div style='font-weight:600;margin-bottom:6px'>JARTIC 交通量（点）</div>"
        "<div class='jartic-grad'></div>"
        "<div class='risklbl'><span>低</span><span>中</span><span>高</span><span>非常に高</span></div>"
        "<div style='height:8px'></div>"
        "<div style='font-weight:600;margin-bottom:6px'>JARTIC 線（擬似）</div>"
        "<div class='redline-sample'></div>"
        "<div class='risklbl'><span>OSMウェイに沿った中心サブパス（赤）: 0〜10km</span><span></span></div>"
        "</div>"
    )
    st.markdown(
        f"<div class='legend'>{''.join(legend_items)}"
        f"<div style='margin-top:10px'><div class='riskbar'></div>"
        f"<div class='risklbl'><span>交差点リスク（低）</span><span>高：最大 {int(hot_df['count'].max()) if not hot_df.empty else 0}件/年</span></div></div>"
        f"{jartic_legend}"
        f"</div>",
        unsafe_allow_html=True,
    )

with col_feed:
    st.markdown("<div class='panel'>", unsafe_allow_html=True)
    st.markdown("#### 速報フィード")
    q = st.text_input("キーワード（市町名や要点）")
    feed = df.copy()
    if q:
        feed = feed[feed.apply(lambda r: q in (r.get("summary") or "") or q in (r.get("municipality") or ""), axis=1)]
    total = len(feed)
    page_size = st.slider("ページ当たり件数", 10, 50, 30, 5)
    pages = max(1, (total + page_size - 1)//page_size)
    page = st.number_input("ページ", 1, pages, 1)
    view = feed.iloc[(page-1)*page_size : page*page_size]

    html_list = ["<div class='feed-scroll'>"]
    for _, r in view.iterrows():
        cat = r.get('category','')
        html_list.append("<div class='feed-card'>")
        html_list.append(f"<div><b>{cat}</b></div>")
        html_list.append(f"<div>{r.get('summary','')}</div>")
        muni = r.get('municipality') or ''
        if muni: html_list.append(f"<div style='color:var(--muted);font-size:.9rem'>{muni}</div>")
        html_list.append(f"<div style='color:#00b894;font-size:.9rem'>予測: {r.get('pred','')}</div>")
        html_list.append(f"<div style='color:var(--muted);font-size:.9rem'><a href='{r.get('src')}' target='_blank'>出典</a></div>")
        html_list.append("</div>")
    html_list.append("</div>")
    st.markdown("\n".join(html_list), unsafe_allow_html=True)
    st.markdown("</div>", unsafe_allow_html=True)

st.caption("地図: OSM/GSI/OpenTopoMap/HOT/GSI航空写真 | JARTIC 5分値（点=量グラデ/線=OSMウェイに沿う 0〜10km） | 交差点ヒート/柱 ON/OFF | 県警速報＋交差点CSV。緊急時は110・119へ。")

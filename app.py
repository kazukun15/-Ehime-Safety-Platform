# -*- coding: utf-8 -*-
# 愛媛セーフティ・プラットフォーム / Ehime Safety Platform  v9.6 (HERE Traffic対応)
# 変更点:
# - TomTom依存を外し、HERE Traffic Flow(JSON)を描画する PathLayer を追加
# - v9.5の機能(速報→位置推定、カテゴリ可視化、交差点ヒート/3D柱、フィード等)を維持
# - サイドバーに「HERE Traffic」をトグル追加（APIキーは HERE_API_KEY）
# - CSSは f-string を使わずに挿入し、中括弧エスケープ問題を根絶
# - 防御的パーサ(here_flow_to_paths)で提示の results[] 形式をそのまま可視化

import os, re, math, time, json, sqlite3, threading, unicodedata, hashlib
from dataclasses import dataclass
from datetime import datetime
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

# === Gemini (optional) ===
try:
    import google.generativeai as genai
    _HAS_GEMINI = True
except Exception:
    _HAS_GEMINI = False

# ----------------------------------------------------------------------------
# Config / Constants
# ----------------------------------------------------------------------------
APP_TITLE = "愛媛セーフティ・プラットフォーム / Ehime Safety Platform"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/9.6 (here-traffic, refactor)"
TIMEOUT = 12
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

# タイル定義（Google Mapsに近い選択肢）
TILESETS: Dict[str, Dict] = {
    "標準":     {"url":"https://tile.openstreetmap.org/{z}/{x}/{y}.png", "max_zoom":19, "thumb":"https://tile.openstreetmap.org/14/14553/6620.png", "copyright":"© OpenStreetMap"},
    "淡色":     {"url":"https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom":18, "thumb":"https://cyberjapandata.gsi.go.jp/xyz/pale/14/14553/6620.png", "copyright":"© GSI"},
    "地形":     {"url":"https://a.tile.opentopomap.org/{z}/{x}/{y}.png", "max_zoom":17, "thumb":"https://a.tile.opentopomap.org/14/14553/6620.png", "copyright":"© OpenTopoMap"},
    "人道支援": {"url":"https://tile-a.openstreetmap.fr/hot/{z}/{x}/{y}.png", "max_zoom":19, "thumb":"https://tile-a.openstreetmap.fr/hot/14/14553/6620.png", "copyright":"© HOT OSM"},
    "航空写真": {"url":"https://cyberjapandata.gsi.go.jp/xyz/seamlessphoto/{z}/{x}/{y}.jpg", "max_zoom":18, "thumb":"https://cyberjapandata.gsi.go.jp/xyz/seamlessphoto/14/14553/6620.jpg", "copyright":"© GSI"},
}

# ----------------------------------------------------------------------------
# Streamlit base UI（CSSは f-string を使わず安全に）
# ----------------------------------------------------------------------------
st.set_page_config(page_title="Ehime Safety Platform", layout="wide")

CSS = """
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
  .risklbl{display:flex; justify-content:space-between; font-size:.85rem; color:var(--muted); margin-top:4px}
  /* レイヤーピッカー */
  .layers-fab { position:fixed; right:18px; bottom:18px; z-index:20; }
  .layers-fab .btn { width:44px; height:44px; border-radius:12px; display:grid; place-items:center; background:var(--panel); border:1px solid var(--border); box-shadow:0 6px 18px rgba(0,0,0,.22); cursor:pointer; }
  .layers-panel { width:min(92vw, 720px); background:var(--panel); color:var(--text); border:1px solid var(--border); border-radius:14px; padding:12px; box-shadow:0 10px 24px rgba(0,0,0,.28); }
  .grid { display:grid; grid-template-columns: repeat(4, minmax(120px, 1fr)); gap:12px; }
  @media (max-width: 740px){ .grid{grid-template-columns: repeat(2, 1fr);} }
  .card { border:1px solid var(--border); border-radius:12px; overflow:hidden; background:var(--panel2); }
  .thumb { width:100%; aspect-ratio: 4/3; object-fit:cover; }
  .label { padding:8px 10px; font-size:.95rem; display:flex; align-items:center; justify-content:space-between; }
  .active { outline:2px solid var(--a); }
  .toggles { display:flex; gap:10px; flex-wrap:wrap; margin-top:8px; }
  .toggle { padding:6px 10px; border-radius:10px; border:1px solid var(--border); background:var(--panel2); }
  .hud { position: relative; height:0; }
  .hud-inner { position: relative; top:-36px; left:6px; display:flex; gap:6px; flex-wrap:wrap; }
  .hud .badge { background:rgba(16,20,27,.88); color:#e8f1ff; border:1px solid var(--border); padding:4px 8px; border-radius:10px; font-size:.85rem; }
  @media (prefers-color-scheme: light){ .hud .badge{ background:rgba(255,255,255,.9); color:#0f2230; } }
</style>
"""

st.markdown(CSS, unsafe_allow_html=True)
HEADER = (
    "<div class='topbar'><div class='brand'><div class='id'>ES</div><div>"
    f"<div>{APP_TITLE}</div><div class='subnote'>今に強い・先を読む。地図で一目、要点は簡潔。</div>"
    "</div></div></div>"
)
st.markdown(HEADER, unsafe_allow_html=True)

# ----------------------------------------------------------------------------
# Session state
# ----------------------------------------------------------------------------
if "map_choice" not in st.session_state:
    st.session_state.map_choice = "標準"
if "show_here_flow" not in st.session_state:
    st.session_state.show_here_flow = True
if "show_hotspots" not in st.session_state:
    st.session_state.show_hotspots = True

# ----------------------------------------------------------------------------
# Secrets / Keys
# ----------------------------------------------------------------------------
@st.cache_resource
def get_sqlite():
    os.makedirs("data", exist_ok=True)
    conn = sqlite3.connect("data/esp_cache.sqlite", check_same_thread=False)
    with conn:
        conn.execute("CREATE TABLE IF NOT EXISTS geocode_cache(key TEXT PRIMARY KEY, json TEXT, created_at TEXT)")
        conn.execute("CREATE TABLE IF NOT EXISTS llm_cache(key TEXT PRIMARY KEY, json TEXT, created_at TEXT)")
    return conn

_conn = get_sqlite()
_conn_lock = threading.Lock()

def cache_get(table:str, key:str) -> Optional[str]:
    with _conn_lock:
        row = _conn.execute(f"SELECT json FROM {table} WHERE key=?", (key,)).fetchone()
    return row[0] if row else None

def cache_put(table:str, key:str, payload:str):
    with _conn_lock, _conn:
        _conn.execute(f"INSERT OR REPLACE INTO {table} VALUES (?,?,datetime('now'))", (key, payload))

# HERE API key

def get_here_key() -> str:
    try:
        if "HERE_API_KEY" in st.secrets and st.secrets["HERE_API_KEY"]:
            return st.secrets["HERE_API_KEY"]
    except Exception:
        pass
    return os.getenv("HERE_API_KEY", "")

# ----------------------------------------------------------------------------
# Data classes / parsing (Ehime Police)
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

# ----------------------------------------------------------------------------
# Extraction / Gazetteer / Geocoding
# ----------------------------------------------------------------------------

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

# Nominatim fallback

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

# Gemini (optional)

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
        system = (
            "あなたは日本のガゼッティア補助エージェントです。"
            "入力の事件・事故テキストから、地名や施設名候補を抽出します。"
            "出力は {\"candidates\":[{\"name\":str,\"kind\":str,\"confidence\":0..1}]}"
        )
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
# H3 helpers & clustering
# ----------------------------------------------------------------------------

def h3_cell_from_latlng(lat: float, lon: float, res: int) -> str:
    if hasattr(h3, "geo_to_h3"): return h3.geo_to_h3(lat, lon, res)
    return h3.latlng_to_cell(lat, lon, res)

def h3_latlng_from_cell(cell: str) -> Tuple[float,float]:
    if hasattr(h3, "h3_to_geo"): lat, lon = h3.h3_to_geo(cell); return lat, lon
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

# ----------------------------------------------------------------------------
# Presentation helpers
# ----------------------------------------------------------------------------

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

# ----------------------------------------------------------------------------
# HERE Traffic Flow: fetch → parse → layer
# ----------------------------------------------------------------------------

def jf_color(jf: float) -> List[int]:
    t = max(0.0, min(1.0, jf / 10.0))
    if t < 0.5:  # 緑→黄
        u = t/0.5
        r = int( 80*(1-u) + 255*u)
        g = int(200*(1-u) + 220*u)
        b = int( 80*(1-u) +   0*u)
    else:        # 黄→赤
        u = (t-0.5)/0.5
        r = int(255*(1-u) + 220*u)
        g = int(220*(1-u) +  40*u)
        b = 0
    return [r, g, b, 220]

@st.cache_data(ttl=120)
def fetch_here_flow(bbox: Tuple[float,float,float,float], here_key: str, units: str = "metric") -> Optional[Dict]:
    if not here_key:
        return None
    # 提示JSONの構造に合わせた簡易取得: 実際は契約バージョンに応じてエンドポイントを調整
    # v7/6.3相当のサンプルAPI（bbox指定）。運用では v8 REST に置き換えてください。
    url = "https://traffic.ls.hereapi.com/traffic/6.3/flow.json"
    params = {
        "apiKey": here_key,
        "bbox": f"{bbox[1]},{bbox[0]};{bbox[3]},{bbox[2]}",
        "responseattributes": "sh,fc",
        "units": units
    }
    try:
        r = requests.get(url, params=params, timeout=10)
        r.raise_for_status()
        return r.json()
    except Exception:
        return None

def here_flow_to_paths(payload: Dict) -> List[Dict]:
    if not payload:
        return []
    paths: List[Dict] = []
    # ユーザ提供例の results[] 形式を優先
    if isinstance(payload.get("results"), list) and payload["results"]:
        for it in payload["results"]:
            loc = it.get("location", {})
            cur = it.get("currentFlow", {})
            jf = float(cur.get("jamFactor", 0))
            width = 6 + int(jf)
            links = ((loc.get("shape") or {}).get("links") or [])
            for link in links:
                pts = link.get("points") or []
                if len(pts) >= 2:
                    path = [[float(p["lng"]), float(p["lat"]) ] for p in pts if "lng" in p and "lat" in p]
                    if len(path) >= 2:
                        paths.append({"path": path, "color": jf_color(jf), "width": width})
        return paths
    # v6.3/7系の RWS/RW/LCS/FIS 構造にもざっくり対応（最小実装）
    try:
        RWS = payload.get("RWS", [])
        for rws in RWS:
            for rw in rws.get("RW", []):
                for fis in rw.get("FIS", []):
                    for fi in fis.get("FI", []):
                        jf = float(((fi.get("CF") or [{}])[0]).get("JF", 0))
                        shp = fi.get("SHP", [])
                        for seg in shp:
                            # SHP は "value": ["lat,lon lat,lon ..."]
                            for v in seg.get("value", []):
                                pts = []
                                for pair in v.split(" "):
                                    if not pair: continue
                                    la, lo = pair.split(",")
                                    pts.append([float(lo), float(la)])
                                if len(pts) >= 2:
                                    paths.append({"path": pts, "color": jf_color(jf), "width": 6 + int(jf)})
    except Exception:
        pass
    return paths

def build_here_flow_layer(paths: List[Dict]) -> Optional[pdk.Layer]:
    if not paths:
        return None
    return pdk.Layer(
        "PathLayer",
        id="here-traffic-flow",
        data=paths,
        get_path="path",
        get_color="color",
        width_scale=1,
        get_width="width",
        pickable=False,
        opacity=0.95
    )

# ----------------------------------------------------------------------------
# Builders (base/heat/grid/points)
# ----------------------------------------------------------------------------

def build_base_layers(map_choice:str, custom_tile:str) -> List[pdk.Layer]:
    tile = TILESETS.get(map_choice, TILESETS["標準"])
    layers: List[pdk.Layer] = [pdk.Layer("TileLayer", id=f"base-{map_choice}", data=tile["url"], min_zoom=0, max_zoom=tile.get("max_zoom",18), tile_size=256, opacity=1.0, refinement="no-overlap")]
    if custom_tile.strip():
        layers.append(pdk.Layer("TileLayer", id="custom-overlay", data=custom_tile.strip(), min_zoom=0, max_zoom=22, tile_size=256, opacity=0.6, refinement="no-overlap"))
    return layers

def grid_color_range() -> List[List[int]]:
    return [
        [255, 180, 180, 60], [255, 140, 140, 90], [255, 100, 100, 120],
        [230, 60, 60, 150], [200, 40, 40, 190], [180, 20, 20, 220],
    ]

def color_from_count_factory(max_count:int):
    def _fn(c:int) -> List[int]:
        t = max(0.0, min(1.0, (c-1) / max(1, max_count-1)))
        if t < 0.5:
            u = t/0.5; r = int(255*(1-u)+255*u); g = int(212*(1-u)+107*u); b = int(212*(1-u)+107*u)
        else:
            u = (t-0.5)/0.5; r = int(255*(1-u)+217*u); g = int(107*(1-u)+4*u); b = int(107*(1-u)+41*u)
        return [r,g,b, 190 if c>=5 else 180]
    return _fn

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
    out.append(out[0])
    return out

def build_intersection_layers(hot_df: pd.DataFrame, is_3d: bool) -> List[pdk.Layer]:
    if hot_df.empty: return []
    if is_3d:
        return [pdk.Layer("ColumnLayer", id="hot-columns", data=hot_df, get_position="position", get_elevation="elev", elevation_scale=1.0, radius=65, get_fill_color="rgba", pickable=True, extruded=True)]
    return [pdk.Layer("HeatmapLayer", id="hot-heatmap", data=hot_df, get_position="position", get_weight="weight", radius_pixels=60, intensity=0.85, threshold=0.05, opacity=0.35, pickable=False)]

def build_congestion_grid(df: pd.DataFrame, is_3d: bool) -> List[pdk.Layer]:
    if is_3d or df.empty: return []
    acc = df[df["category"]=="交通事故"].copy()
    if acc.empty: return []
    acc["position"] = acc.apply(lambda r: [float(r["lon"]), float(r["lat"])], axis=1)
    acc["weight"] = 1.0
    return [pdk.Layer("GridLayer", id="congestion-grid", data=acc, get_position="position", get_weight="weight", cell_size=200, extruded=False, opacity=0.18, pickable=False, aggregation="SUM", colorRange=grid_color_range())]

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
                p = {"position":[lon,lat], "color":sty["color"], "radius":sty["radius"], "c":row["category"],
                     "s":row.get("summary",""), "m":row.get("municipality",""), "pred":row.get("pred",""),
                     "src":row.get("src", EHIME_POLICE_URL), "r":int(row.get("radius_m",600)), "ico":sty["icon"]}
                points.append(p)
                icon_fg.append({"position":[lon,lat], "label":sty["icon"], "tcolor":[255,255,255,235], "offset":[0,-2]})
                if len(mini_fg) < MAX_LABELS:
                    vtxt = (row.get("summary","")[:4])
                    vtxt = "\n".join(list(vtxt))
                    offset_px = int(-14*LABEL_SCALE)
                    mini_bg.append({"position":[lon,lat],"label":vtxt,"tcolor":[0,0,0,220],"offset":[0,offset_px]})
                    mini_fg.append({"position":[lon,lat],"label":vtxt,"tcolor":[255,255,255,235],"offset":[0,offset_px]})
        else:
            points.append({"position":[clon,clat],"color":[100,100,100,210],"radius":70,"c":"集中","s":"周辺に多数","m":"","pred":"","src":EHIME_POLICE_URL,"r":0,"ico":"◎"})
            icon_fg.append({"position":[clon,clat], "label":"◎", "tcolor":[255,255,255,230], "offset":[0,-2]})
    for p in points:
        if p.get("r",0) > 0:
            lon, lat = p["position"]
            features.append({"type":"Feature","geometry":{"type":"Polygon","coordinates":[circle_coords(lon, lat, int(p["r"]))]},"properties":{}})
    geojson = {"type":"FeatureCollection","features": features}
    return points, icon_fg, mini_fg, mini_bg, geojson

# ----------------------------------------------------------------------------
# Data pipeline
# ----------------------------------------------------------------------------
with st.spinner("速報を取得中…"):
    html = fetch_ehime_html()
raw_items = parse_items(html)

extracted: List[Dict] = []
for it in raw_items:
    ex = rule_extract(it)
    ex["heading"] = it.heading
    ex["full_text"] = (it.heading + " " + it.body).strip()
    extracted.append(ex)

# Gazetteer（任意CSV）
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
            lon, lat, typ = hit
            return {"lon":lon, "lat":lat, "type":typ or "facility"}
    if muni and muni in MUNI_CENTERS:
        lon, lat = MUNI_CENTERS[muni]
        return {"lon":lon, "lat":lat, "type":"city"}
    for q in queries:
        ll = nominatim_geocode(q, muni)
        if ll:
            return {"lon":ll[0], "lat":ll[1], "type":"facility"}
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

# 多発交差点（内蔵サンプル）
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
hot_df["lat"] = hot_df["lat"].astype(float)
hot_df["lon"] = hot_df["lon"].astype(float)
hot_df["count"] = hot_df["count"].astype(int)
max_count = int(hot_df["count"].max()) if not hot_df.empty else 1
hot_df["position"] = hot_df.apply(lambda r: [float(r["lon"]), float(r["lat"])], axis=1)
hot_df["weight"] = hot_df["count"].astype(float)
color_from_count = color_from_count_factory(max_count)
hot_df["rgba"] = hot_df["count"].apply(color_from_count)
hot_df["elev"] = hot_df["count"].apply(lambda c: 300 + (c-1)*220)

# ----------------------------------------------------------------------------
# Layout
# ----------------------------------------------------------------------------
col_map, col_feed = st.columns([7,5], gap="large")

with col_map:
    # --- sidebar ---
    with st.sidebar:
        st.markdown("<div class='panel'>", unsafe_allow_html=True)
        st.markdown("#### 表示期間")
        period = st.select_slider("表示期間を選択", ["当日","過去3日","過去7日","過去30日"], value="過去7日", label_visibility="collapsed")
        st.markdown("#### 表示モード")
        mode_3d = st.radio("2D / 3D", ["2D","3D"], horizontal=True, index=0)
        init_zoom = st.slider("初期ズーム", 8, 17, 11)
        st.markdown("#### HERE Traffic")
st.session_state.show_here_flow = st.checkbox("HERE Flow を重ねる", value=bool(st.session_state.show_here_flow))
st.caption("HERE_API_KEY を secrets か環境変数に設定してください。")
st.markdown("#### 危ない交差点")
st.session_state.show_hotspots = st.checkbox("ヒートマップ / 3D柱 を表示", value=bool(st.session_state.show_hotspots))
        st.markdown("#### 任意タイルURL（透過PNG推奨）")
        custom_tile = st.text_input("例: https://…/{z}/{x}/{y}.png", "")
        st.markdown("</div>", unsafe_allow_html=True)

    is_3d = (mode_3d == "3D")

    # --- deck layers ---
    layers: List[pdk.Layer] = []
    layers += build_base_layers(st.session_state.map_choice, custom_tile)
    if st.session_state.show_hotspots:
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

    # HERE Traffic Flow
    here_key = get_here_key()
    if st.session_state.show_here_flow and here_key:
        payload = fetch_here_flow(EHIME_BBOX, here_key)
        paths = here_flow_to_paths(payload or {})
        layer_here = build_here_flow_layer(paths)
        if layer_here:
            layers.append(layer_here)
    elif st.session_state.show_here_flow and not here_key:
        st.info("HERE_API_KEY が未設定です。secrets か環境変数に設定してください。")

    tooltip_html = (
        "<div style='min-width:180px'>"
        "<b>{c}</b><br/>{s}<br/>{m}<br/>予測: {pred}<br/>"
        f"<a href='{EHIME_POLICE_URL}' target='_blank'>出典</a>"
        "</div>"
    )

    deck = pdk.Deck(
        layers=layers,
        initial_view_state=pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=init_zoom, pitch=(45 if is_3d else 0), bearing=0),
        tooltip={
            "html": tooltip_html,
            "style": {"backgroundColor":"rgba(10,15,20,.96)","color":"#e6f1ff","maxWidth":"320px","whiteSpace":"normal","wordBreak":"break-word","lineHeight":1.4,"fontSize":"12px","padding":"10px 12px","borderRadius":"12px","border":"1px solid var(--border)"}
        },
        map_provider=None, map_style=None
    )
    st.pydeck_chart(deck, use_container_width=True, height=620)

    # HUD
    st.markdown("<div class='hud'><div class='hud-inner'>" + f"<div class='badge'>Zoom: {init_zoom}（初期）</div>" + "</div></div>", unsafe_allow_html=True)

    # レイヤピッカー（簡易版）
    st.markdown("<div class='layers-fab'><div class='btn'>🗺️</div></div>", unsafe_allow_html=True)
    with st.expander("地図・レイヤ", expanded=False):
        st.markdown("<div class='layers-panel'>", unsafe_allow_html=True)
        names = list(TILESETS.keys())
        cols = st.columns(4)
        for i, name in enumerate(names):
            with cols[i % 4]:
                thumb = TILESETS[name]["thumb"]
                active = (name == st.session_state.map_choice)
                st.markdown(f"<div class='card{' active' if active else ''}'><img class='thumb' src='{thumb}'/><div class='label'><span>{name}</span>" + ("<span>✓</span>" if active else "") + "</div></div>", unsafe_allow_html=True)
                if st.button(f"{name} に切替", key=f"pick-{name}", use_container_width=True):
                    st.session_state.map_choice = name
                    st.rerun()
        st.caption(
            "地図タイル: " + ", ".join(sorted({TILESETS[n]["copyright"] for n in names}))
            + " / HERE Traffic Flow (要 HERE_API_KEY)"
        )
        st.markdown("</div>", unsafe_allow_html=True)

    # legend
    legend_items = []
    for k, v in CAT_STYLE.items():
        rgba = f"rgba({v['color'][0]}, {v['color'][1]}, {v['color'][2]}, {v['color'][3]/255:.9f})"
        legend_items.append(f"<span class='item'><span class='dot' style='background:{rgba}'></span>{k}</span>")
    st.markdown(
        f"<div class='legend'>{''.join(legend_items)}"
        f"<div style='margin-top:10px'><div class='riskbar'></div>"
        f"<div class='risklbl'><span>交差点リスク（低）</span><span>高：最大 {int(hot_df['count'].max()) if not hot_df.empty else 0}件/年</span></div></div></div>",
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

st.caption("地図: OSM/GSI/OpenTopoMap/HOT/GSI航空写真（APIキー不要） | HERE Traffic Flow（要 HERE_API_KEY） | 情報: 県警速報＋交差点CSV。緊急時は110・119へ。")

# =============================================
# Ehime Safety Platform (ESP) – v3.3 完成版
# ベースマップ: OpenStreetMap / 国土地理院（APIキー不要、無料）
# ・Deck.gl TileLayer で OSM/GSI タイルを直接表示（Mapbox不要）
# ・事故/事件/災害（速報）を円ポリゴンで近似オーバーレイ
# ・Geminiは任意（未設定でもルールベースで可視化）
# =============================================

import os
import re
import json
import math
import time
import hashlib
import sqlite3
import threading
from dataclasses import dataclass
from datetime import datetime
from typing import Dict, List, Optional, Tuple

import requests
import pandas as pd
import streamlit as st
import pydeck as pdk
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process as rf_process

APP_TITLE = "愛媛セーフティ・プラットフォーム（Ehime Safety Platform / ESP）"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/1.3 (civic); contact: localgov"
REQUEST_TIMEOUT = 12
FETCH_TTL_SEC = 300

GEMINI_MODEL = "gemini-2.5-flash"
GEMINI_MAX_TOKENS = 512
GEMINI_TEMPERATURE = 0.2

EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650

SLEEP_RANGE = (0.6, 1.0)

st.set_page_config(page_title="Ehime Safety Platform", layout="wide")
st.markdown(
    """
    <style>
      .big-title {font-size:1.6rem; font-weight:700;}
      .chip {display:inline-block; padding:4px 10px; border-radius:999px; margin:0 6px 6px 0; background:#eceff1; font-size:0.9rem;}
      .chip.on {background:#1e88e5; color:#fff}
      .subtle {color:#666}
      .legend {font-size:0.9rem;}
      .feed-card {background:#11111110; padding:12px 14px; border-radius:12px; border:1px solid #e0e0e0;}
      .stButton>button {border-radius:999px;}
      .metric-box {background:#f7f7f7; border:1px solid #eee; border-radius:10px; padding:8px 10px;}
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(f"<div class='big-title'>🗺️ {APP_TITLE}</div>", unsafe_allow_html=True)

# ------------------ Sidebar ------------------
st.sidebar.header("表示項目")
show_accidents = st.sidebar.checkbox("事故情報", True)
show_crimes = st.sidebar.checkbox("犯罪情報", True)
show_disasters = st.sidebar.checkbox("災害情報(警報等)", True)

st.sidebar.header("ベースマップ（無料・APIキー不要）")
BASEMAP = st.sidebar.selectbox(
    "地図タイル",
    (
        "OSM 標準 (OpenStreetMap)",
        "GSI 淡色 (国土地理院)",
        "GSI 標準 (国土地理院)",
        "GSI 航空写真 (国土地理院)",
    ),
)

st.sidebar.header("解析モード")
use_llm = st.sidebar.checkbox("Gemini解析を有効化", True, help="未設定でもルールベースで表示可能")

st.sidebar.header("データ取得/設定")
if st.sidebar.button("県警速報を再取得（キャッシュ無視）"):
    st.session_state.pop("_fetch_meta", None)
    st.session_state.pop("_incidents_cache", None)
    st.session_state.pop("_analyzed_cache", None)

gazetteer_path = st.sidebar.text_input("ガゼッティアCSVパス", "data/gazetteer_ehime.csv")
use_fuzzy = st.sidebar.checkbox("ゆらぎ対応（ファジーマッチ）", True)
min_fuzzy_score = st.sidebar.slider("最小スコア", 60, 95, 78)

st.sidebar.caption("※参考情報。緊急時は110/119。現地の指示を優先。個人情報は表示しません。")

# ------------------ Utils ------------------

def jst_now_iso() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def content_fingerprint(text: str) -> str:
    return hashlib.blake2s(text.encode("utf-8")).hexdigest()

# ------------------ SQLite Cache ------------------
@st.cache_resource
def get_sqlite():
    os.makedirs("data", exist_ok=True)
    conn = sqlite3.connect("data/esp_cache.sqlite", check_same_thread=False)
    with conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS nlp_cache(
                id TEXT PRIMARY KEY,
                payload TEXT NOT NULL,
                created_at TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS geocode_cache(
                key TEXT PRIMARY KEY,
                lon REAL, lat REAL, type TEXT,
                created_at TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS fetch_meta(
                url TEXT PRIMARY KEY,
                etag TEXT, last_modified TEXT,
                content_hash TEXT,
                fetched_at TEXT NOT NULL
            )
        """)
    return conn

conn = get_sqlite()
conn_lock = threading.Lock()

# ------------------ Cache helpers ------------------

def cache_get_nlp(hid: str) -> Optional[Dict]:
    with conn_lock:
        cur = conn.execute("SELECT payload FROM nlp_cache WHERE id=?", (hid,))
        r = cur.fetchone()
    return json.loads(r[0]) if r else None


def cache_put_nlp(hid: str, payload: Dict) -> None:
    with conn_lock, conn:
        conn.execute(
            "INSERT OR REPLACE INTO nlp_cache(id,payload,created_at) VALUES(?,?,datetime('now'))",
            (hid, json.dumps(payload, ensure_ascii=False)),
        )


def fetch_meta_get(url: str) -> Tuple[Optional[str], Optional[str]]:
    with conn_lock:
        cur = conn.execute("SELECT etag,last_modified FROM fetch_meta WHERE url=?", (url,))
        r = cur.fetchone()
    if r:
        return r[0], r[1]
    return None, None


def fetch_meta_put(url: str, etag: Optional[str], last_modified: Optional[str], content_hash: str) -> None:
    with conn_lock, conn:
        conn.execute(
            "INSERT OR REPLACE INTO fetch_meta(url,etag,last_modified,content_hash,fetched_at) VALUES(?,?,?,?,datetime('now'))",
            (url, etag, last_modified, content_hash),
        )

# ------------------ Fetch & Parse ------------------
@dataclass
class IncidentItem:
    id: str
    source_url: str
    heading: str
    station: Optional[str]
    incident_date: Optional[str]
    body: str
    fetched_at: str


def http_get(url: str) -> str:
    r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=REQUEST_TIMEOUT)
    r.raise_for_status()
    enc = r.apparent_encoding or r.encoding or "utf-8"
    r.encoding = enc
    return r.text


def http_get_conditional(url: str) -> Optional[str]:
    etag, last_mod = fetch_meta_get(url)
    headers = {"User-Agent": USER_AGENT}
    if etag:
        headers["If-None-Match"] = etag
    if last_mod:
        headers["If-Modified-Since"] = last_mod
    r = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
    if r.status_code == 304:
        return None
    r.raise_for_status()
    enc = r.apparent_encoding or r.encoding or "utf-8"
    r.encoding = enc
    txt = r.text
    fetch_meta_put(url, r.headers.get("ETag"), r.headers.get("Last-Modified"), content_fingerprint(txt))
    return txt


def parse_ehime_police_page(html: str) -> List[IncidentItem]:
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)
    text = re.sub(r"【愛媛県警からのお願い！】[\s\S]*?(?=■|$)", "", text)
    lines = [ln for ln in text.split("\n") if ln.strip()]

    blocks, current = [], None
    for ln in lines:
        if ln.startswith("■"):
            if current:
                blocks.append(current)
            current = {"heading": ln.strip(), "body": []}
        else:
            if current:
                current["body"].append(ln.strip())
    if current:
        blocks.append(current)

    out: List[IncidentItem] = []
    today = datetime.now().date(); cy = today.year

    for b in blocks:
        heading = b.get("heading", "")
        body = " ".join(b.get("body", []))[:1600]
        m_date = re.search(r"（?(\d{1,2})月(\d{1,2})日", heading)
        m_station = re.search(r"（\d{1,2}月\d{1,2}日\s*([^\s）]+)）", heading)
        incident_date = None
        if m_date:
            m, d = int(m_date.group(1)), int(m_date.group(2))
            y = cy
            cand = datetime(y, m, d).date()
            if cand > today: y -= 1
            incident_date = datetime(y, m, d).date().isoformat()
        station = m_station.group(1) if m_station else None
        rid = content_fingerprint((heading + " " + body)[:800])
        out.append(IncidentItem(
            id=rid,
            source_url=EHIME_POLICE_URL,
            heading=heading,
            station=station,
            incident_date=incident_date,
            body=body,
            fetched_at=jst_now_iso(),
        ))
    return out

# ------------------ Gemini / Rule-based ------------------
@st.cache_resource
def gemini_client():
    import google.generativeai as genai
    key = os.getenv("GEMINI_API_KEY")
    if not key:
        return None
    genai.configure(api_key=key)
    return genai.GenerativeModel(GEMINI_MODEL)

from concurrent.futures import ThreadPoolExecutor, as_completed

CITY_NAMES = [
    "松山市","今治市","新居浜市","西条市","大洲市","伊予市","四国中央市","西予市","東温市",
    "上島町","久万高原町","松前町","砥部町","内子町","伊方町","松野町","鬼北町","愛南町"
]
CATEGORY_PATTERNS = [
    ("交通事故", r"交通.*事故|自転車|バス|二輪|乗用|衝突|交差点|国道|県道"),
    ("火災", r"火災|出火|全焼|半焼"),
    ("死亡事案", r"死亡|死亡事案"),
    ("窃盗", r"窃盗|万引|盗"),
    ("詐欺", r"詐欺|還付金|投資詐欺|特殊詐欺"),
    ("事件", r"威力業務妨害|条例違反|暴行|傷害|脅迫|器物損壊"),
]
FACILITY_HINT = ["学校","小学校","中学校","高校","大学","グラウンド","体育館","公園","駅","港","病院","交差点"]


def rule_based_extract(it: IncidentItem) -> Dict:
    text = it.heading + " " + it.body
    category = "その他"
    for name, pat in CATEGORY_PATTERNS:
        if re.search(pat, text):
            category = name; break
    muni = None
    for c in CITY_NAMES:
        if c in text:
            muni = c; break
    places = []
    for hint in FACILITY_HINT:
        m = re.findall(rf"([\w\u3040-\u30ff\u4e00-\u9fffA-Za-z0-9]+{hint})", text)
        places.extend(m[:2])
    s = re.sub(r"\s+", " ", it.body)[:140]
    return {
        "category": category,
        "municipality": muni,
        "place_strings": list(dict.fromkeys(places))[:3],
        "road_refs": [],
        "occurred_date": it.incident_date,
        "occurred_time_text": None,
        "summary_ja": s if s else it.heading.replace("■", "").strip(),
        "confidence": 0.3,
        "raw_heading": it.heading,
        "raw_snippet": it.body[:200],
        "source_url": it.source_url,
        "fetched_at": it.fetched_at,
        "id": it.id,
    }


def gemini_analyze_many(items: List[IncidentItem]) -> List[Dict]:
    model = gemini_client()
    if model is None:
        return []
    SYS = "事実のみを application/json で出力。欠測は null。要約は原文準拠で憶測禁止。"

    def one(it: IncidentItem) -> Dict:
        cached = cache_get_nlp(it.id)
        if cached:
            return cached
        user = (
            f"category, municipality, place_strings, road_refs, occurred_date, occurred_time_text, "
            f"summary_ja, confidence, raw_heading, raw_snippet\n"
            f"見出し:{it.heading}\n本文:{it.body}\n推定日:{it.incident_date} 署:{it.station}"
        )
        try:
            import google.generativeai as genai  # lazy import guard
            gen_cfg = {"temperature": GEMINI_TEMPERATURE, "max_output_tokens": GEMINI_MAX_TOKENS, "response_mime_type": "application/json"}
            resp = model.generate_content([
                {"role": "system", "parts": [SYS]},
                {"role": "user", "parts": [user]},
            ], generation_config=gen_cfg)
            txt = (getattr(resp, "text", None) or "").strip()
            data = json.loads(txt) if txt else {}
        except Exception:
            data = {}
        base = rule_based_extract(it)
        merged = {
            "category": data.get("category") or base["category"],
            "municipality": data.get("municipality") or base["municipality"],
            "place_strings": data.get("place_strings") or base["place_strings"],
            "road_refs": data.get("road_refs") or base["road_refs"],
            "occurred_date": data.get("occurred_date") or base["occurred_date"],
            "occurred_time_text": data.get("occurred_time_text") or base["occurred_time_text"],
            "summary_ja": data.get("summary_ja") or base["summary_ja"],
            "confidence": data.get("confidence", 0.6 if data else 0.3),
            "raw_heading": it.heading,
            "raw_snippet": it.body[:200],
            "source_url": it.source_url,
            "fetched_at": it.fetched_at,
            "id": it.id,
        }
        cache_put_nlp(it.id, merged)
        time.sleep(SLEEP_RANGE[0])
        return merged

    out: List[Dict] = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(one, it) for it in items]
        for f in as_completed(futs):
            out.append(f.result())
    return out

# ------------------ Gazetteer / Geocoding ------------------
@st.cache_data(show_spinner=False)
def load_gazetteer(csv_path: str) -> Optional[pd.DataFrame]:
    try:
        df = pd.read_csv(csv_path)
        for col in ["name", "type", "lon", "lat"]:
            if col not in df.columns:
                st.warning("ガゼッティアに必須列がありません: name,type,lon,lat")
                return None
        df["alt_names"] = df.get("alt_names", "").fillna("")
        return df
    except Exception:
        return None

class GazetteerIndex:
    def __init__(self, df: pd.DataFrame):
        self.df = df.reset_index(drop=True)
        self.keys = (df["name"].astype(str) + " | " + df["alt_names"].fillna("").astype(str)).tolist()

    def search(self, q: str, min_score: int = 78) -> Optional[Tuple[float, float, str]]:
        m = self.df[(self.df["name"].str.contains(q, na=False)) | (self.df["alt_names"].str.contains(q, na=False))]
        if not m.empty:
            r = m.iloc[0]
            return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        hit = rf_process.extractOne(q, self.keys, scorer=fuzz.token_set_ratio)
        if hit and hit[1] >= min_score:
            r = self.df.iloc[hit[2]]
            return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        return None

FACILITY_KEYWORDS = FACILITY_HINT

def decide_radius_m(match_type: str) -> int:
    if match_type == "facility":
        return 300
    if match_type == "intersection":
        return 250
    if match_type in ("town", "chome"):
        return 600
    if match_type in ("oaza", "aza"):
        return 900
    if match_type in ("city", "municipality"):
        return 2000
    return 1200


def classify_place(text: str) -> str:
    if any(k in text for k in FACILITY_KEYWORDS):
        return "facility"
    if "交差点" in text:
        return "intersection"
    if text.endswith("町") or text.endswith("丁目"):
        return "town"
    if text.endswith("市") or text.endswith("郡"):
        return "city"
    return "unknown"


def nominatim_geocode(name: str, municipality: Optional[str]) -> Optional[Tuple[float, float]]:
    try:
        q = f"{name} {municipality or ''} 愛媛県 日本".strip()
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": q, "format": "jsonv2", "limit": 1}
        r = requests.get(url, params=params, timeout=10, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        arr = r.json()
        if isinstance(arr, list) and arr:
            lat = float(arr[0]["lat"])  # type: ignore
            lon = float(arr[0]["lon"])  # type: ignore
            return lon, lat
    except Exception:
        return None
    return None


def geocode_with_cache(idx: Optional[GazetteerIndex], key: str, resolver) -> Optional[Tuple[float, float, str]]:
    with conn_lock:
        # inline cache because we already have sqlite
        cur = conn.execute("SELECT lon,lat,type FROM geocode_cache WHERE key=?", (key,))
        r = cur.fetchone()
    if r:
        return float(r[0]), float(r[1]), str(r[2])
    val = resolver()
    if val:
        lon, lat, typ = val
        with conn_lock, conn:
            conn.execute("INSERT OR REPLACE INTO geocode_cache(key,lon,lat,type,created_at) VALUES(?,?,?,?,datetime('now'))",
                         (key, lon, lat, typ))
        return lon, lat, typ
    return None


def circle_coords(lon: float, lat: float, radius_m: int = 300, n: int = 64) -> List[List[float]]:
    coords: List[List[float]] = []
    r_earth = 6378137.0
    dlat = radius_m / r_earth
    dlon = radius_m / (r_earth * math.cos(math.radians(lat)))
    for i in range(n):
        ang = 2 * math.pi * i / n
        lat_i = lat + math.degrees(dlat * math.sin(ang))
        lon_i = lon + math.degrees(dlon * math.cos(math.radians(lat)))
        coords.append([lon_i, lat_i])
    coords.append(coords[0])
    return coords

# ------------------ Pipeline ------------------
@st.cache_data(ttl=FETCH_TTL_SEC)
def load_police_items() -> List[IncidentItem]:
    txt = http_get_conditional(EHIME_POLICE_URL)
    if txt is None:
        txt = http_get(EHIME_POLICE_URL)
    return parse_ehime_police_page(txt)

@st.cache_data(ttl=FETCH_TTL_SEC)
def analyze_items(items: List[IncidentItem], enable_llm: bool) -> pd.DataFrame:
    rows: List[Dict] = []
    if enable_llm:
        new_items = [it for it in items if cache_get_nlp(it.id) is None]
        if new_items:
            _ = gemini_analyze_many(new_items)
        rows = [cache_get_nlp(it.id) or {} for it in items]
    final_rows: List[Dict] = []
    for it, base in zip(items, rows if rows else [{}]*len(items)):
        rb = rule_based_extract(it)
        if not base:
            final_rows.append(rb); continue
        merged = {
            "category": base.get("category") or rb["category"],
            "municipality": base.get("municipality") or rb["municipality"],
            "place_strings": base.get("place_strings") or rb["place_strings"],
            "road_refs": base.get("road_refs") or rb["road_refs"],
            "occurred_date": base.get("occurred_date") or rb["occurred_date"],
            "occurred_time_text": base.get("occurred_time_text") or rb["occurred_time_text"],
            "summary_ja": base.get("summary_ja") or rb["summary_ja"],
            "confidence": base.get("confidence", 0.6),
            "raw_heading": it.heading,
            "raw_snippet": it.body[:200],
            "source_url": it.source_url,
            "fetched_at": it.fetched_at,
            "id": it.id,
        }
        final_rows.append(merged)
    return pd.DataFrame(final_rows)

# ------------------ Run ------------------
with st.spinner("県警速報の取得・解析中..."):
    items = load_police_items()
    an_df = analyze_items(items, enable_llm=use_llm)

# ---- Defensive cols ----
REQUIRED_COLS = {"category":"その他","municipality":None,"place_strings":[],"road_refs":[],
                 "occurred_date":None,"occurred_time_text":None,"summary_ja":None,
                 "confidence":0.4,"raw_heading":None,"raw_snippet":None,
                 "source_url":EHIME_POLICE_URL,"fetched_at":jst_now_iso(),"id":None}
if an_df is None or an_df.empty:
    an_df = pd.DataFrame([{k:v for k,v in REQUIRED_COLS.items()}]).iloc[0:0].copy()
else:
    for col, default in REQUIRED_COLS.items():
        if col not in an_df.columns:
            an_df[col] = default

# ------------------ Basemap: OSM/GSI TileLayer ------------------
TILES = {
    "OSM 標準 (OpenStreetMap)": {
        "url": "https://tile.openstreetmap.org/{z}/{x}/{y}.png",
        "attribution": "© OpenStreetMap contributors",
        "max_zoom": 19,
    },
    "GSI 淡色 (国土地理院)": {
        "url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png",
        "attribution": "地理院タイル（淡色）",
        "max_zoom": 18,
    },
    "GSI 標準 (国土地理院)": {
        "url": "https://cyberjapandata.gsi.go.jp/xyz/std/{z}/{x}/{y}.png",
        "attribution": "地理院タイル（標準）",
        "max_zoom": 18,
    },
    "GSI 航空写真 (国土地理院)": {
        "url": "https://cyberjapandata.gsi.go.jp/xyz/ort/{z}/{x}/{y}.jpg",
        "attribution": "地理院タイル（オルソ画像）",
        "max_zoom": 18,
    },
}

tile_info = TILES[BASEMAP]

# ---- Gazetteer ----
gaz_df = load_gazetteer(gazetteer_path) if gazetteer_path else None
idx = GazetteerIndex(gaz_df) if gaz_df is not None else None

# ---- Build GeoJSON ----
features = []
for _, row in an_df.iterrows():
    cat = row.get("category")
    if cat in ("交通事故", "事件", "窃盗", "詐欺", "死亡事案"):
        if not (show_accidents or show_crimes):
            continue

    municipality: Optional[str] = row.get("municipality")
    places: List[str] = row.get("place_strings") or []

    lonlat_typ: Optional[Tuple[float, float, str]] = None

    if idx is not None:
        for ptxt in places:
            key = f"gaz|{municipality}|{ptxt}"
            def _resolve():
                hit = idx.search(ptxt, min_fuzzy_score if use_fuzzy else 101)
                if hit:
                    lon, lat, typ = hit
                    return lon, lat, typ
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve)
            if lonlat_typ:
                break
        if not lonlat_typ and municipality:
            key = f"gaz|{municipality}"
            def _resolve_city():
                hit = idx.search(municipality, min_fuzzy_score if use_fuzzy else 101)
                if hit:
                    lon, lat, typ = hit
                    return lon, lat, typ
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_city)

    if not lonlat_typ:
        for ptxt in places:
            key = f"osm|{municipality}|{ptxt}"
            def _resolve_osm():
                ll = nominatim_geocode(ptxt, municipality)
                if ll:
                    return ll[0], ll[1], "facility"
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_osm)
            if lonlat_typ:
                break
        if not lonlat_typ and municipality:
            key = f"osm|{municipality}"
            def _resolve_osm_city():
                ll = nominatim_geocode(municipality, None)
                if ll:
                    return ll[0], ll[1], "city"
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_osm_city)

    if not lonlat_typ:
        lonlat_typ = (EHIME_PREF_LON, EHIME_PREF_LAT, "pref")
        radius_m = 5000
    else:
        radius_m = decide_radius_m(lonlat_typ[2])

    lon, lat, mtype = lonlat_typ
    conf = float(row.get("confidence", 0.4) or 0.4)
    color = [255, 140, 0, int(50 + min(160, conf * 160))]

    props = {
        "c": row.get("category", "その他"),
        "s": (row.get("summary_ja") or row.get("raw_heading") or "")[:140],
        "m": municipality,
        "u": row.get("source_url") or EHIME_POLICE_URL,
        "t": row.get("fetched_at"),
        "f": round(conf, 2),
        "r": radius_m,
    }
    features.append({
        "type": "Feature",
        "geometry": {"type": "Polygon", "coordinates": [circle_coords(lon, lat, radius_m)]},
        "properties": {**props, "_fill": color},
    })

geojson = {"type": "FeatureCollection", "features": features}

# ------------------ Render ------------------
col_map, col_feed = st.columns([7, 5], gap="large")

with col_map:
    tile_layer = pdk.Layer(
        "TileLayer",
        data=tile_info["url"],
        min_zoom=0,
        max_zoom=tile_info.get("max_zoom", 18),
        tile_size=256,
        opacity=1.0,
    )
    incident_layer = pdk.Layer(
        "GeoJsonLayer",
        data=geojson,
        pickable=True,
        stroked=True,
        filled=True,
        get_line_width=2,
        get_line_color=[230, 90, 20],
        get_fill_color="properties._fill",
        auto_highlight=True,
    )
    layers = [tile_layer]
    if show_accidents or show_crimes:
        layers.append(incident_layer)
    tooltip = {"html": "<b>{c}</b><br/>{s}<br/><span class='subtle'>{m}</span><br/>半径:{r}m / conf:{f}",
               "style": {"backgroundColor": "#111", "color": "white"}}
    deck = pdk.Deck(
        layers=layers,
        initial_view_state=pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9),
        tooltip=tooltip,
        map_provider=None,  # Mapbox 無効
        map_style=None,
    )
    st.pydeck_chart(deck, use_container_width=True)
    st.caption(f"地図出典: {tile_info['attribution']}")

with col_feed:
    st.subheader("オーバーレイ要約（速報）")
    cats = sorted([c for c in an_df.get("category", pd.Series(dtype=str)).dropna().unique().tolist() if c])
    default_cats = cats if cats else ["交通事故","事件","窃盗","詐欺","死亡事案","火災","その他"]
    cats_filter = st.multiselect("カテゴリ絞込", options=default_cats, default=default_cats)

    feed = an_df.copy()
    if cats_filter and "category" in feed.columns:
        feed = feed[feed["category"].isin(cats_filter)]

    q = st.text_input("キーワード検索（要約/原文/見出し）")
    if q:
        feed = feed[feed.apply(lambda r: (q in (r.get("summary_ja") or "")) or (q in (r.get("raw_snippet") or "")) or (q in (r.get("raw_heading") or "")), axis=1)]

    PAGE_SIZE = 12
    total = len(feed)
    page = st.number_input("ページ", min_value=1, max_value=max(1, (total - 1) // PAGE_SIZE + 1), value=1)
    start = (page - 1) * PAGE_SIZE
    end = start + PAGE_SIZE

    for _, r in feed.iloc[start:end].iterrows():
        st.markdown("<div class='feed-card'>", unsafe_allow_html=True)
        st.markdown(f"**{r.get('category','その他')}**")
        st.caption(r.get("summary_ja") or (r.get("raw_heading") or "要約なし"))
        st.caption(f"{r.get('municipality') or '市町村不明'} / 取得: {r.get('fetched_at')} / conf: {r.get('confidence')}")
        st.link_button("出典を開く", r.get("source_url") or EHIME_POLICE_URL, help="県警ページ")
        st.markdown("</div>", unsafe_allow_html=True)

st.markdown("---")
st.caption("出典: 愛媛県警 事件事故速報 / 地図: OpenStreetMap または 国土地理院タイル。参考情報であり、正確性は保証しません。緊急時は110/119へ。")

# requirements.txt（参考）
# streamlit
# pandas
# pydeck
# requests
# beautifulsoup4
# google-generativeai>=0.8.0
# rapidfuzz

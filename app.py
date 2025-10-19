# =============================================
# Ehime Safety Platform (ESP) – v3 (robust empty-columns fix)
# Streamlit app with defensive guards when DataFrame columns are missing
# (fixes KeyError: 'occurred_date')
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
USER_AGENT = "ESP/1.0 (civic); contact: localgov"
REQUEST_TIMEOUT = 10
FETCH_TTL_SEC = 300  # 5min

GEMINI_MODEL = "gemini-2.5-flash"
GEMINI_MAX_TOKENS = 512
GEMINI_TEMPERATURE = 0.2

EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650

SLEEP_RANGE = (0.6, 1.2)

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
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(f"<div class='big-title'>🗺️ {APP_TITLE}</div>", unsafe_allow_html=True)

st.sidebar.header("表示項目")
show_accidents = st.sidebar.checkbox("事故情報", True)
show_crimes = st.sidebar.checkbox("犯罪情報", True)
show_disasters = st.sidebar.checkbox("災害情報(警報等)", True)

st.sidebar.header("データ取得/設定")
if st.sidebar.button("県警速報を再取得（キャッシュ無視）"):
    st.session_state.pop("_fetch_meta", None)
    st.session_state.pop("_incidents_cache", None)
    st.session_state.pop("_analyzed_cache", None)

gazetteer_path = st.sidebar.text_input("ガゼッティアCSVパス", "data/gazetteer_ehime.csv")
use_fuzzy = st.sidebar.checkbox("ゆらぎ対応（ファジーマッチ）", True)
min_fuzzy_score = st.sidebar.slider("最小スコア", 60, 95, 78)

st.sidebar.caption("※参考情報。緊急時は110/119。現地の指示を優先。個人情報は表示しません。")


def jst_now_iso() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def content_fingerprint(text: str) -> str:
    return hashlib.blake2s(text.encode("utf-8")).hexdigest()

@st.cache_resource
def get_sqlite() -> sqlite3.Connection:
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


def cache_get_geo(key: str) -> Optional[Tuple[float, float, str]]:
    with conn_lock:
        cur = conn.execute("SELECT lon,lat,type FROM geocode_cache WHERE key=?", (key,))
        r = cur.fetchone()
    if r:
        return float(r[0]), float(r[1]), str(r[2])
    return None


def cache_put_geo(key: str, lon: float, lat: float, typ: str) -> None:
    with conn_lock, conn:
        conn.execute(
            "INSERT OR REPLACE INTO geocode_cache(key,lon,lat,type,created_at) VALUES(?,?,?,?,datetime('now'))",
            (key, lon, lat, typ),
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

@dataclass
class IncidentItem:
    id: str
    source_url: str
    heading: str
    station: Optional[str]
    incident_date: Optional[str]
    body: str
    fetched_at: str


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
        body = " ".join(b.get("body", []))[:1200]
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
        rid = content_fingerprint((heading + " " + body)[:600])
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

@st.cache_resource
def gemini_client():
    import google.generativeai as genai
    key = os.getenv("GEMINI_API_KEY")
    if not key:
        st.error("GEMINI_API_KEY が未設定です。環境変数を設定してください。")
        st.stop()
    genai.configure(api_key=key)
    return genai.GenerativeModel(GEMINI_MODEL)

from concurrent.futures import ThreadPoolExecutor, as_completed

def gemini_analyze_many(items: List[IncidentItem]) -> List[Dict]:
    model = gemini_client()
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
        gen_cfg = {
            "temperature": GEMINI_TEMPERATURE,
            "max_output_tokens": GEMINI_MAX_TOKENS,
            "response_mime_type": "application/json",
        }
        try:
            resp = model.generate_content([
                {"role": "system", "parts": [SYS]},
                {"role": "user", "parts": [user]},
            ], generation_config=gen_cfg)
            txt = (resp.text or "").strip()
            data = json.loads(txt) if txt else {}
        except Exception:
            data = {}
        data.setdefault("category", "その他")
        data.setdefault("municipality", None)
        data.setdefault("place_strings", [])
        data.setdefault("road_refs", [])
        data.setdefault("occurred_date", it.incident_date)
        data.setdefault("occurred_time_text", None)
        data.setdefault("summary_ja", None)
        data.setdefault("confidence", 0.4)
        data.setdefault("raw_heading", it.heading)
        data.setdefault("raw_snippet", it.body[:200])
        data["source_url"] = it.source_url
        data["fetched_at"] = it.fetched_at
        data["id"] = it.id
        cache_put_nlp(it.id, data)
        time.sleep(SLEEP_RANGE[0])
        return data

    out: List[Dict] = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(one, it) for it in items]
        for f in as_completed(futs):
            out.append(f.result())
    return out

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

FACILITY_KEYWORDS = [
    "学校", "小学校", "中学校", "高校", "大学", "グラウンド", "体育館", "公園", "港", "病院",
    "交差点", "インター", "IC", "PA", "駅", "温泉"
]

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
    return 800


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
        r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT, headers={"User-Agent": USER_AGENT})
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
    cached = cache_get_geo(key)
    if cached:
        return cached
    val = resolver()
    if val:
        lon, lat, typ = val
        cache_put_geo(key, lon, lat, typ)
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


def fetch_jma_warnings_prefecture(pref_code: str = "38") -> List[Dict]:
    return []

# ------------------ Cached fetch/parse/analyze ------------------
@st.cache_data(ttl=FETCH_TTL_SEC)
def load_police_items() -> List[IncidentItem]:
    txt = http_get_conditional(EHIME_POLICE_URL)
    if txt is None:
        txt = requests.get(EHIME_POLICE_URL, headers={"User-Agent": USER_AGENT}, timeout=REQUEST_TIMEOUT).text
    return parse_ehime_police_page(txt)

@st.cache_data(ttl=FETCH_TTL_SEC)
def analyze_items_cached(items: List[IncidentItem]) -> pd.DataFrame:
    new_items = [it for it in items if cache_get_nlp(it.id) is None]
    if new_items:
        _ = gemini_analyze_many(new_items)
    rows = [cache_get_nlp(it.id) or {} for it in items]
    df = pd.DataFrame(rows)
    return df

# ------------------ Run pipeline ------------------
with st.spinner("県警速報の取得・解析中..."):
    items = load_police_items()
    an_df = analyze_items_cached(items)

# ---- Defensive defaults: ensure required columns exist ----
REQUIRED_COLS: Dict[str, object] = {
    "category": "その他",
    "municipality": None,
    "place_strings": [],
    "road_refs": [],
    "occurred_date": None,
    "occurred_time_text": None,
    "summary_ja": None,
    "confidence": 0.4,
    "raw_heading": None,
    "raw_snippet": None,
    "source_url": EHIME_POLICE_URL,
    "fetched_at": jst_now_iso(),
    "id": None,
}
if an_df is None or an_df.empty:
    # create empty frame with required columns
    an_df = pd.DataFrame([{k: v for k, v in REQUIRED_COLS.items()}]).iloc[0:0].copy()
else:
    for col, default in REQUIRED_COLS.items():
        if col not in an_df.columns:
            an_df[col] = default

# ---- Filters (guard against missing) ----
if "occurred_date" in an_df.columns and not an_df.empty:
    an_df["occurred_date"] = pd.to_datetime(an_df["occurred_date"], errors="coerce")
    min_date = pd.to_datetime(an_df["occurred_date"].min())
    max_date = pd.to_datetime(an_df["occurred_date"].max())
    if pd.notna(min_date) and pd.notna(max_date):
        dr = st.sidebar.date_input("発生日フィルタ", value=(min_date.date(), max_date.date()))
        if isinstance(dr, tuple) and len(dr) == 2:
            d0, d1 = pd.to_datetime(dr[0]), pd.to_datetime(dr[1])
            an_df = an_df[(an_df["occurred_date"] >= d0) & (an_df["occurred_date"] <= d1)]

cats = sorted([c for c in an_df.get("category", pd.Series(dtype=str)).dropna().unique().tolist() if c])
st.write(" ".join([f"<span class='chip on'>{c}</span>" for c in cats]), unsafe_allow_html=True)

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
                    return ll[0], ll[1], classify_place(ptxt)
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
        continue

    lon, lat, mtype = lonlat_typ
    radius_m = decide_radius_m(mtype)
    conf = float(row.get("confidence", 0.4))
    color = [255, 140, 0, int(40 + min(160, conf * 160))]

    props = {
        "c": row.get("category", "その他"),
        "s": (row.get("summary_ja") or "")[:120],
        "m": municipality,
        "u": row.get("source_url"),
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

view_state = pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9)
layer_incidents = pdk.Layer(
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

layers = []
if show_accidents or show_crimes:
    layers.append(layer_incidents)

tooltip = {
    "html": "<b>{c}</b><br/>{s}<br/><span class='subtle'>{m}</span><br/>半径:{r}m / conf:{f}",
    "style": {"backgroundColor": "#111", "color": "white"},
}

deck = pdk.Deck(layers=layers, initial_view_state=view_state, tooltip=tooltip)

col_map, col_feed = st.columns([7, 5], gap="large")
with col_map:
    st.pydeck_chart(deck, use_container_width=True)
    st.markdown(
        """
        <div class='legend'>
          <span class='chip'>凡例</span> 円は「近似範囲」です（ピンポイントではありません）。
          出典URLと取得時刻を必ず確認してください。
        </div>
        """,
        unsafe_allow_html=True,
    )

with col_feed:
    st.subheader("オーバーレイ要約（速報）")
    cats = sorted([c for c in an_df.get("category", pd.Series(dtype=str)).dropna().unique().tolist() if c])
    cats_filter = st.multiselect("カテゴリ絞込", options=cats, default=cats)
    feed = an_df.copy()
    if cats_filter and "category" in feed.columns:
        feed = feed[feed["category"].isin(cats_filter)]

    q = st.text_input("キーワード検索（要約/原文）")
    if q:
        feed = feed[feed.apply(lambda r: (q in (r.get("summary_ja") or "")) or (q in (r.get("raw_snippet") or "")), axis=1)]

    PAGE_SIZE = 12
    total = len(feed)
    page = st.number_input("ページ", min_value=1, max_value=max(1, (total - 1) // PAGE_SIZE + 1), value=1)
    start = (page - 1) * PAGE_SIZE
    end = start + PAGE_SIZE

    for _, r in feed.iloc[start:end].iterrows():
        st.markdown("<div class='feed-card'>", unsafe_allow_html=True)
        st.markdown(f"**{r.get('category','その他')}**")
        st.caption(r.get("summary_ja") or "要約なし")
        st.caption(f"{r.get('municipality') or '市町村不明'} / 取得: {r.get('fetched_at')} / conf: {r.get('confidence')}")
        st.link_button("出典を開く", r.get("source_url") or EHIME_POLICE_URL, help="県警ページ")
        st.markdown("</div>", unsafe_allow_html=True)

st.markdown("---")
st.caption(
    "出典: 愛媛県警 事件事故速報 / Geocoding: Gazetteer→OSM(Nominatim). このアプリは参考情報であり、正確性を保証しません。緊急時は110/119へ。"
)

# requirements.txt (unchanged)
# streamlit
# pandas
# pydeck
# requests
# beautifulsoup4
# google-generativeai>=0.8.0
# rapidfuzz

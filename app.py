# ============================================================
# Ehime Safety Platform (ESP) – v4.0.1
# 修正: Python h3 ライブラリの v3/v4 API 差異で落ちる不具合を解消
#  - h3.geo_to_h3 / h3.h3_to_geo が存在しない環境（v4）でも動作
#  - 互換ヘルパ: latlng_to_cell / cell_to_latlng を自動切替
# そのほかの仕様は v4.0 と同じ（H3クラスタ + スパイダーファンアウト等）
# ============================================================

import os
import re
import json
import math
import time
import hashlib
import sqlite3
import threading
from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple

import requests
import pandas as pd
import streamlit as st
import pydeck as pdk
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process as rf_process
import h3

APP_TITLE = "愛媛セーフティ・プラットフォーム（Ehime Safety Platform / ESP）"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/4.0.1 (civic); contact: localgov"
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
      .big-title {font-size:1.5rem; font-weight:700;}
      .subtle {color:#5f6368}
      .legend {font-size:0.95rem; background:#fafafa; border:1px solid #eee; border-radius:12px; padding:10px 12px;}
      .legend .item {display:inline-flex; align-items:center; margin-right:14px; margin-bottom:6px}
      .dot {width:12px; height:12px; border-radius:50%; display:inline-block; margin-right:6px; border:1px solid #00000022}
      .feed-card {background:#ffffff; padding:12px 14px; border-radius:14px; border:1px solid #e8e8e8; margin-bottom:10px; box-shadow:0 1px 2px rgba(0,0,0,.04)}
      .feed-scroll {max-height:700px; overflow-y:auto; padding-right:6px}
      .stButton>button {border-radius:999px;}
      /* Quick FABs */
      .fab-bar {position:sticky; bottom:12px; display:flex; gap:8px; justify-content:center; padding:6px 8px;}
      .fab {border-radius:999px; border:1px solid #e3e3e3; padding:6px 10px; background:white; box-shadow:0 2px 8px rgba(0,0,0,.08); font-size:0.9rem;}
      .fab.active {box-shadow:0 0 0 2px rgba(0,0,0,.10) inset;}
      @media (max-width: 640px){ .big-title{font-size:1.2rem} .feed-scroll{max-height:50vh} .legend{font-size:.9rem} }
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(f"<div class='big-title'>🗺️ {APP_TITLE}</div>", unsafe_allow_html=True)

# ------------------ Sidebar ------------------
st.sidebar.header("期間")
period = st.sidebar.select_slider("表示期間", ["当日","過去3日","過去7日","過去30日"], value="過去7日")
period_days = {"当日":1, "過去3日":3, "過去7日":7, "過去30日":30}[period]

st.sidebar.header("密度・重なり制御")
zoom_like = st.sidebar.slider("表示密度（ズーム相当）", 7, 14, 10)
fanout_threshold = st.sidebar.slider("スパイダーファンアウト件数閾値", 2, 8, 4)
label_scale = st.sidebar.slider("ラベル倍率", 0.7, 1.6, 1.0, 0.1)

st.sidebar.header("解析モード")
use_llm = st.sidebar.checkbox("Gemini解析を有効化", True)

st.sidebar.header("データ取得/設定")
if st.sidebar.button("県警速報を再取得（キャッシュ無視）"):
    st.session_state.pop("_fetch_meta", None)
    st.session_state.pop("_incidents_cache", None)
    st.session_state.pop("_analyzed_cache", None)

gazetteer_path = st.sidebar.text_input("ガゼッティアCSVパス", "data/gazetteer_ehime.csv")
use_fuzzy = st.sidebar.checkbox("ゆらぎ対応（ファジーマッチ）", True)
min_fuzzy_score = st.sidebar.slider("最小スコア", 60, 95, 78)

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
    if etag: headers["If-None-Match"] = etag
    if last_mod: headers["If-Modified-Since"] = last_mod
    r = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
    if r.status_code == 304: return None
    r.raise_for_status()
    enc = r.apparent_encoding or r.encoding or "utf-8"; r.encoding = enc
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
            if current: blocks.append(current)
            current = {"heading": ln.strip(), "body": []}
        else:
            if current: current["body"].append(ln.strip())
    if current: blocks.append(current)

    out: List[IncidentItem] = []
    today = datetime.now().date(); cy = today.year
    for b in blocks:
        heading = b.get("heading", ""); body = " ".join(b.get("body", []))[:1600]
        m_date = re.search(r"（?(\d{1,2})月(\d{1,2})日", heading)
        m_station = re.search(r"（\d{1,2}月\d{1,2}日\s*([^\s）]+)）", heading)
        incident_date = None
        if m_date:
            m, d = int(m_date.group(1)), int(m_date.group(2)); y = cy
            cand = datetime(y, m, d).date()
            if cand > today: y -= 1
            incident_date = datetime(y, m, d).date().isoformat()
        station = m_station.group(1) if m_station else None
        rid = content_fingerprint((heading + " " + body)[:800])
        out.append(IncidentItem(rid, EHIME_POLICE_URL, heading, station, incident_date, body, jst_now_iso()))
    return out

# ------------------ Gemini / Rule-based ------------------
@st.cache_resource
def gemini_client():
    import google.generativeai as genai
    key = os.getenv("GEMINI_API_KEY")
    if not key: return None
    genai.configure(api_key=key)
    return genai.GenerativeModel(GEMINI_MODEL)

from concurrent.futures import ThreadPoolExecutor, as_completed

CITY_NAMES = ["松山市","今治市","新居浜市","西条市","大洲市","伊予市","四国中央市","西予市","東温市","上島町","久万高原町","松前町","砥部町","内子町","伊方町","松野町","鬼北町","愛南町"]
CATEGORY_PATTERNS = [("交通事故", r"交通.*事故|自転車|バス|二輪|乗用|衝突|交差点|国道|県道|人身事故"),("火災", r"火災|出火|全焼|半焼|延焼"),("死亡事案", r"死亡|死亡事案"),("窃盗", r"窃盗|万引|盗"),("詐欺", r"詐欺|還付金|投資詐欺|特殊詐欺"),("事件", r"威力業務妨害|条例違反|暴行|傷害|脅迫|器物損壊|青少年保護")]
FACILITY_HINT = ["学校","小学校","中学校","高校","大学","グラウンド","体育館","公園","駅","港","病院","交差点"]

def rule_based_extract(it: IncidentItem) -> Dict:
    text = it.heading + " " + it.body
    category = "その他"
    for name, pat in CATEGORY_PATTERNS:
        if re.search(pat, text): category = name; break
    muni = None
    for c in CITY_NAMES:
        if c in text: muni = c; break
    places = []
    for hint in FACILITY_HINT:
        m = re.findall(rf"([\w\u3040-\u30ff\u4e00-\u9fffA-Za-z0-9]+{hint})", text)
        places.extend(m[:2])
    s = re.sub(r"\s+", " ", it.body)[:140]
    return {"category":category,"municipality":muni,"place_strings":list(dict.fromkeys(places))[:3],"road_refs":[],"occurred_date":it.incident_date,"occurred_time_text":None,"summary_ja": s if s else it.heading.replace("■"," ").strip(),"confidence":0.3,"raw_heading":it.heading,"raw_snippet":it.body[:200],"source_url":it.source_url,"fetched_at":it.fetched_at,"id":it.id}

def gemini_analyze_many(items: List[IncidentItem]) -> List[Dict]:
    model = gemini_client()
    if model is None: return []
    SYS = "事実のみを application/json で出力。欠測は null。要約は原文準拠で憶測禁止。"
    def one(it: IncidentItem) -> Dict:
        cached = cache_get_nlp(it.id)
        if cached: return cached
        user = (f"category, municipality, place_strings, road_refs, occurred_date, occurred_time_text, summary_ja, confidence, raw_heading, raw_snippet\n" f"見出し:{it.heading}\n本文:{it.body}\n推定日:{it.incident_date} 署:{it.station}")
        try:
            import google.generativeai as genai
            gen_cfg = {"temperature":GEMINI_TEMPERATURE, "max_output_tokens":GEMINI_MAX_TOKENS, "response_mime_type":"application/json"}
            resp = model.generate_content([{ "role":"system","parts":[SYS]},{"role":"user","parts":[user]}], generation_config=gen_cfg)
            txt = (getattr(resp, "text", None) or "").strip(); data = json.loads(txt) if txt else {}
        except Exception: data = {}
        base = rule_based_extract(it)
        merged = {"category": data.get("category") or base["category"],"municipality": data.get("municipality") or base["municipality"],"place_strings": data.get("place_strings") or base["place_strings"],"road_refs": data.get("road_refs") or base["road_refs"],"occurred_date": data.get("occurred_date") or base["occurred_date"],"occurred_time_text": data.get("occurred_time_text") or base["occurred_time_text"],"summary_ja": data.get("summary_ja") or base["summary_ja"],"confidence": data.get("confidence", 0.6 if data else 0.3),"raw_heading": it.heading,"raw_snippet": it.body[:200],"source_url": it.source_url,"fetched_at": it.fetched_at,"id": it.id}
        cache_put_nlp(it.id, merged); time.sleep(SLEEP_RANGE[0]); return merged
    out: List[Dict] = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(one, it) for it in items]
        for f in as_completed(futs): out.append(f.result())
    return out

# ------------------ Gazetteer / Geocoding ------------------
@st.cache_data(show_spinner=False)
def load_gazetteer(csv_path: str) -> Optional[pd.DataFrame]:
    try:
        df = pd.read_csv(csv_path)
        for col in ["name","type","lon","lat"]:
            if col not in df.columns: st.warning("ガゼッティアに必須列がありません: name,type,lon,lat"); return None
        df["alt_names"] = df.get("alt_names", "").fillna(""); return df
    except Exception: return None

class GazetteerIndex:
    def __init__(self, df: pd.DataFrame):
        self.df = df.reset_index(drop=True)
        self.keys = (df["name"].astype(str) + " | " + df["alt_names"].fillna("").astype(str)).tolist()
    def search(self, q: str, min_score: int = 78) -> Optional[Tuple[float, float, str]]:
        m = self.df[(self.df["name"].str.contains(q, na=False)) | (self.df["alt_names"].str.contains(q, na=False))]
        if not m.empty:
            r = m.iloc[0]; return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        hit = rf_process.extractOne(q, self.keys, scorer=fuzz.token_set_ratio)
        if hit and hit[1] >= min_score:
            r = self.df.iloc[hit[2]]; return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore
        return None

FACILITY_HINT = ["学校","小学校","中学校","高校","大学","グラウンド","体育館","公園","駅","港","病院","交差点"]

def decide_radius_m(match_type: str) -> int:
    if match_type == "facility": return 300
    if match_type == "intersection": return 250
    if match_type in ("town","chome"): return 600
    if match_type in ("oaza","aza"): return 900
    if match_type in ("city","municipality"): return 2000
    return 1200

def nominatim_geocode(name: str, municipality: Optional[str]) -> Optional[Tuple[float, float]]:
    try:
        q = f"{name} {municipality or ''} 愛媛県 日本".strip(); url = "https://nominatim.openstreetmap.org/search"
        params = {"q": q, "format": "jsonv2", "limit": 1}
        r = requests.get(url, params=params, timeout=10, headers={"User-Agent": USER_AGENT}); r.raise_for_status()
        arr = r.json();
        if isinstance(arr, list) and arr:
            lat = float(arr[0]["lat"]); lon = float(arr[0]["lon"]); return lon, lat
    except Exception: return None
    return None

def geocode_with_cache(idx: Optional[GazetteerIndex], key: str, resolver) -> Optional[Tuple[float, float, str]]:
    with conn_lock:
        cur = conn.execute("SELECT lon,lat,type FROM geocode_cache WHERE key=?", (key,)); r = cur.fetchone()
    if r: return float(r[0]), float(r[1]), str(r[2])
    val = resolver()
    if val:
        lon, lat, typ = val
        with conn_lock, conn:
            conn.execute("INSERT OR REPLACE INTO geocode_cache(key,lon,lat,type,created_at) VALUES(?,?,?,?,datetime('now'))", (key, lon, lat, typ))
        return lon, lat, typ
    return None

# ------------------ Helper: テキスト整形 ------------------

def verticalize(text: str, max_lines: int = 4) -> str:
    t = re.sub(r"\s+", "", text or "");
    if not t: return ""
    t = t[:max_lines]; return "\n".join(list(t))

def short_summary(s: str, max_len: int = 60) -> str:
    s = re.sub(r"\s+", " ", s or "").strip();
    return (s[:max_len] + ("…" if len(s) > max_len else "")) if s else ""

# ------------------ H3 互換レイヤ ------------------

def h3_cell_from_latlng(lat: float, lon: float, res: int) -> str:
    # v3: geo_to_h3, v4: latlng_to_cell
    if hasattr(h3, "geo_to_h3"):
        return h3.geo_to_h3(lat, lon, res)  # type: ignore
    return h3.latlng_to_cell(lat, lon, res)  # type: ignore


def h3_latlng_from_cell(cell: str) -> Tuple[float, float]:
    # v3: h3_to_geo -> (lat,lon), v4: cell_to_latlng -> (lat,lon)
    if hasattr(h3, "h3_to_geo"):
        lat, lon = h3.h3_to_geo(cell)  # type: ignore
        return lat, lon
    lat, lon = h3.cell_to_latlng(cell)  # type: ignore
    return lat, lon


def h3_res_from_zoom(zoom_like_val:int) -> int:
    mapping = {7:5, 8:6, 9:7, 10:8, 11:9, 12:9, 13:10, 14:10}
    return mapping.get(zoom_like_val, 8)


def cluster_points(df: pd.DataFrame, zoom_like_val:int) -> List[Dict]:
    res = h3_res_from_zoom(zoom_like_val)
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


def spiderfy(center_lon: float, center_lat: float, n: int, base_px: int = 16, gap_px: int = 8) -> List[Tuple[float,float]]:
    out: List[Tuple[float,float]] = []; rpx = base_px
    for k in range(n):
        ang = math.radians(137.5 * k); dx = rpx*math.cos(ang); dy = rpx*math.sin(ang)
        dlon = dx / (111320 * math.cos(math.radians(center_lat))); dlat = dy / 110540
        out.append((center_lon + dlon, center_lat + dlat)); rpx += gap_px
    return out

# ------------------ Pipeline ------------------
@st.cache_data(ttl=FETCH_TTL_SEC)
def load_police_items() -> List[IncidentItem]:
    txt = http_get_conditional(EHIME_POLICE_URL)
    if txt is None: txt = http_get(EHIME_POLICE_URL)
    return parse_ehime_police_page(txt)

@st.cache_data(ttl=FETCH_TTL_SEC)
def analyze_items(items: List[IncidentItem], enable_llm: bool) -> pd.DataFrame:
    rows: List[Dict] = []
    if enable_llm:
        new_items = [it for it in items if cache_get_nlp(it.id) is None]
        if new_items: _ = gemini_analyze_many(new_items)
        rows = [cache_get_nlp(it.id) or {} for it in items]
    final_rows: List[Dict] = []
    for it, base in zip(items, rows if rows else [{}]*len(items)):
        rb = rule_based_extract(it)
        if not base: final_rows.append(rb); continue
        merged = {"category": base.get("category") or rb["category"],"municipality": base.get("municipality") or rb["municipality"],"place_strings": base.get("place_strings") or rb["place_strings"],"road_refs": base.get("road_refs") or rb["road_refs"],"occurred_date": base.get("occurred_date") or rb["occurred_date"],"occurred_time_text": base.get("occurred_time_text") or rb["occurred_time_text"],"summary_ja": base.get("summary_ja") or rb["summary_ja"],"confidence": base.get("confidence", 0.6),"raw_heading": it.heading,"raw_snippet": it.body[:200],"source_url": it.source_url,"fetched_at": it.fetched_at,"id": it.id}
        final_rows.append(merged)
    return pd.DataFrame(final_rows)

# ------------------ Run ------------------
with st.spinner("県警速報の取得・解析中..."):
    items = load_police_items(); an_df = analyze_items(items, enable_llm=use_llm)

REQUIRED_COLS = {"category":"その他","municipality":None,"place_strings":[],"road_refs":[],"occurred_date":None,"occurred_time_text":None,"summary_ja":None,"confidence":0.4,"raw_heading":None,"raw_snippet":None,"source_url":EHIME_POLICE_URL,"fetched_at":jst_now_iso(),"id":None}
if an_df is None or an_df.empty:
    an_df = pd.DataFrame([{k:v for k,v in REQUIRED_COLS.items()}]).iloc[0:0].copy()
else:
    for col, default in REQUIRED_COLS.items():
        if col not in an_df.columns: an_df[col] = default

# 期間フィルタ
now = datetime.now(); cutoff = (now - timedelta(days=period_days)).date()
if an_df["occurred_date"].notna().any():
    mask = pd.to_datetime(an_df["occurred_date"], errors="coerce").dt.date >= cutoff
else:
    mask = pd.to_datetime(an_df["fetched_at"], errors="coerce").dt.date >= cutoff
an_df = an_df[mask]

# Basemap（日本語 GSI）
TILES = {"GSI 淡色 (国土地理院)": {"url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png","attribution": "地理院タイル（淡色）","max_zoom": 18},"GSI 標準 (国土地理院)": {"url": "https://cyberjapandata.gsi.go.jp/xyz/std/{z}/{x}/{y}.png","attribution": "地理院タイル（標準）","max_zoom": 18}}
BASEMAP = "GSI 淡色 (国土地理院)"; TILE = TILES[BASEMAP]

# Gazetteer
@st.cache_data(show_spinner=False)
def load_gaz(csv_path:str):
    try:
        df = pd.read_csv(csv_path); df["alt_names"] = df.get("alt_names", "").fillna(""); return df
    except Exception: return None

gaz_df = load_gaz(gazetteer_path) if gazetteer_path else None
idx = GazetteerIndex(gaz_df) if gaz_df is not None else None

# カテゴリ配色
CAT_STYLE = {"交通事故": {"color": [235, 87, 87, 220],   "radius": 86},"火災": {"color": [255, 112, 67, 220],  "radius": 88},"死亡事案": {"color": [171, 71, 188, 220],  "radius": 92},"窃盗": {"color": [66, 165, 245, 220],  "radius": 78},"詐欺": {"color": [38, 166, 154, 220],  "radius": 78},"事件": {"color": [255, 202, 40, 220],  "radius": 82},"その他": {"color": [120, 144, 156, 210],  "radius": 70}}

# 位置決定（必ず表示）
rows_geo: List[Dict] = []
for _, row in an_df.iterrows():
    cat = row.get("category") or "その他"; municipality = row.get("municipality"); places: List[str] = row.get("place_strings") or []
    lonlat_typ: Optional[Tuple[float, float, str]] = None
    if idx is not None:
        for ptxt in places:
            key = f"gaz|{municipality}|{ptxt}"
            def _resolve():
                hit = idx.search(ptxt, min_fuzzy_score if use_fuzzy else 101)
                if hit: lon, lat, typ = hit; return lon, lat, typ
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve)
            if lonlat_typ: break
        if not lonlat_typ and municipality:
            key = f"gaz|{municipality}"
            def _resolve_city():
                hit = idx.search(municipality, min_fuzzy_score if use_fuzzy else 101)
                if hit: lon, lat, typ = hit; return lon, lat, typ
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_city)
    if not lonlat_typ and municipality:
        for ptxt in places:
            key = f"osm|{municipality}|{ptxt}"
            def _resolve_osm():
                ll = nominatim_geocode(ptxt, municipality)
                if ll: return ll[0], ll[1], "facility"
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_osm)
            if lonlat_typ: break
        if not lonlat_typ:
            key = f"osm|{municipality}"
            def _resolve_osm_city():
                ll = nominatim_geocode(municipality, None)
                if ll: return ll[0], ll[1], "city"
                return None
            lonlat_typ = geocode_with_cache(idx, key, _resolve_osm_city)
    if not lonlat_typ: lonlat_typ = (EHIME_PREF_LON, EHIME_PREF_LAT, "pref")
    lon, lat, match_type = lonlat_typ
    rows_geo.append({
        "lon": float(lon), "lat": float(lat), "category": cat,
        "summary": short_summary(row.get("summary_ja") or row.get("raw_heading") or "", 60),
        "municipality": municipality, "confidence": float(row.get("confidence", 0.4) or 0.4),
        "radius_m": decide_radius_m(match_type), "source_url": row.get("source_url") or EHIME_POLICE_URL,
    })

geo_df = pd.DataFrame(rows_geo)

# --- クイックトグル（FAB）
active_cats = st.session_state.get("active_cats") or {k: True for k in CAT_STYLE.keys()}
bar_html = ["<div class='fab-bar'>"]
for cname in CAT_STYLE.keys():
    on = active_cats.get(cname, True)
    cls = "fab active" if on else "fab"
    color = f"rgba({CAT_STYLE[cname]['color'][0]}, {CAT_STYLE[cname]['color'][1]}, {CAT_STYLE[cname]['color'][2]}, .9)"
    fg = "#222" if cname not in ("交通事故","火災","死亡事案") else "#fff"
    bar_html.append(f"<button class='{cls}' style='background:{color}; color:{fg}' onclick=\"window.parent.postMessage({{'type':'toggle','cat':'{cname}'}},'*')\">{cname}</button>")
bar_html.append("</div>")
st.markdown("".join(bar_html), unsafe_allow_html=True)

st.components.v1.html("""
<script>
window.addEventListener('message', (e)=>{
  if(!e.data || e.data.type!=='toggle') return;
  const cat = e.data.cat; const url = new URL(window.location);
  const key = 'cat_'+encodeURIComponent(cat); const cur = url.searchParams.get(key);
  url.searchParams.set(key, cur==='0' ? '1' : '0'); window.location.replace(url.toString());
});
</script>
""", height=0)

qs = st.query_params
for cname in list(CAT_STYLE.keys()):
    key = "cat_"+cname
    if key in qs: active_cats[cname] = (qs[key] != "0")
st.session_state["active_cats"] = active_cats
geo_df = geo_df[geo_df["category"].apply(lambda c: active_cats.get(str(c), True))]

# ---- H3クラスタリング ----
centers = cluster_points(geo_df, zoom_like)

# ---- レイヤデータ構築 ----
hex_points = [{"position": [c["lon"], c["lat"]], "count": c["count"]} for c in centers]
points: List[Dict] = []; labels_fg: List[Dict] = []; labels_bg: List[Dict] = []; polys: List[Dict] = []
for c in centers:
    cnt = c["count"]; clat, clon = c["lat"], c["lon"]
    if cnt <= fanout_threshold:
        offs = spiderfy(clon, clat, cnt, base_px=16, gap_px=8)
        for (lon, lat), row in zip(offs, c["rows"]):
            style = CAT_STYLE.get(row["category"], CAT_STYLE["その他"])
            points.append({"position":[lon,lat],"color":style["color"],"radius":style["radius"],"c":row["category"],"s":row["summary"],"m":row.get("municipality"),"f":round(float(row.get("confidence",0.4)),2),"r":int(row.get("radius_m",600))})
            vtxt = verticalize(row["summary"], 4); offset_px = int(-12*label_scale)
            labels_bg.append({"position":[lon,lat],"label":vtxt,"tcolor":[0,0,0,220],"offset":[0,offset_px]})
            labels_fg.append({"position":[lon,lat],"label":vtxt,"tcolor":[255,255,255,235],"offset":[0,offset_px]})
            polys.append({"type":"Feature","geometry":{"type":"Polygon","coordinates":[[[lon,lat]]] },"properties":{"_fill":[255,140,0,0]}})  # dummy; circleは下でまとめる
    else:
        points.append({"position":[clon,clat],"color":[90,90,90,200],"radius":70,"c":f"{cnt}件","s":"周辺に多数の事案","m":"","f":0.0,"r":0})
        labels_bg.append({"position":[clon,clat],"label":str(cnt),"tcolor":[0,0,0,220],"offset":[0,-10]})
        labels_fg.append({"position":[clon,clat],"label":str(cnt),"tcolor":[255,255,255,235],"offset":[0,-10]})

# 近似円（別途作成）
from math import radians, degrees, cos, sin, pi

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

poly_features = []
for p in points:
    if p.get("r",0) > 0:
        poly_features.append({"type":"Feature","geometry":{"type":"Polygon","coordinates":[circle_coords(p["position"][0], p["position"][1], int(p["r"]))]},"properties":{"_fill":[255,140,0,60],"c":p["c"],"s":p["s"],"m":p.get("m"),"r":p.get("r"),"f":p.get("f")}})
geojson = {"type":"FeatureCollection","features": poly_features}

# ------------------ Render ------------------
col_map, col_feed = st.columns([7,5], gap="large")
with col_map:
    tile_layer = pdk.Layer("TileLayer", data=TILE["url"], min_zoom=0, max_zoom=TILE.get("max_zoom",18), tile_size=256, opacity=1.0)
    hex_layer = pdk.Layer("HexagonLayer", data=hex_points, get_position="position", get_elevation_weight="count", elevation_scale=6, elevation_range=[0,1000], extruded=False, radius=500, coverage=0.9, opacity=0.25, pickable=True)
    circle_layer = pdk.Layer("GeoJsonLayer", data=geojson, pickable=True, stroked=True, filled=True, get_line_width=2, get_line_color=[230, 90, 20], get_fill_color="properties._fill", auto_highlight=True)
    marker_layer = pdk.Layer("ScatterplotLayer", data=points, get_position="position", get_fill_color="color", get_radius="radius", pickable=True, radius_min_pixels=3, radius_max_pixels=60)
    text_bg = pdk.Layer("TextLayer", data=labels_bg, get_position="position", get_text="label", get_color="tcolor", get_size=int(12*label_scale), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle")
    text_fg = pdk.Layer("TextLayer", data=labels_fg, get_position="position", get_text="label", get_color="tcolor", get_size=int(12*label_scale), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle")

    layers = [tile_layer, hex_layer, circle_layer, marker_layer, text_bg, text_fg]
    tooltip = {"html": "<b>{c}</b><br/>{s}<br/><span class='subtle'>{m}</span><br/>半径:{r}m / conf:{f}", "style": {"backgroundColor":"#111","color":"white","maxWidth":"280px","whiteSpace":"normal","wordBreak":"break-word","lineHeight":1.35,"fontSize":"13px","padding":"8px 10px","borderRadius":"10px","boxShadow":"0 2px 10px rgba(0,0,0,.25)"}}
    deck = pdk.Deck(layers=layers, initial_view_state=pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9), tooltip=tooltip, map_provider=None, map_style=None)
    st.pydeck_chart(deck, use_container_width=True, height=520)

    # 凡例
    legend_items = []
    for k, v in CAT_STYLE.items():
        col = f"rgba({v['color'][0]}, {v['color'][1]}, {v['color'][2]}, {v['color'][3]/255:.9f})"
        legend_items.append(f"<span class='item'><span class='dot' style='background:{col}'></span>{k}</span>")
    st.markdown(f"<div class='legend'>{''.join(legend_items)}<div class='subtle' style='margin-top:6px'>六角は密度、放射点は近接展開。円は近似範囲。</div></div>", unsafe_allow_html=True)

with col_feed:
    st.subheader("速報フィード（期間・カテゴリ連動）")
    cats_on = [c for c, on in st.session_state.get("active_cats", {}).items() if on]
    feed = an_df[an_df["category"].isin(cats_on)] if cats_on else an_df.iloc[0:0]
    q = st.text_input("キーワード検索（要約/原文/見出し）")
    if q:
        feed = feed[feed.apply(lambda r: (q in (r.get("summary_ja") or "")) or (q in (r.get("raw_snippet") or "")) or (q in (r.get("raw_heading") or "")), axis=1)]
    html = ["<div class='feed-scroll'>"]
    for _, r in feed.iterrows():
        html.append("<div class='feed-card'>")
        html.append(f"<b>{r.get('category','その他')}</b><br>")
        html.append(f"<div class='subtle'>{short_summary(r.get('summary_ja') or (r.get('raw_heading') or '要約なし'), 110)}</div>")
        html.append(f"<div class='subtle'>{r.get('municipality') or '市町村不明'} / 取得: {r.get('fetched_at')} / conf: {r.get('confidence')}</div>")
        src = r.get("source_url") or EHIME_POLICE_URL
        html.append(f"<a href='{src}' target='_blank'>出典を開く</a>")
        html.append("</div>")
    html.append("</div>"); st.markdown("\n".join(html), unsafe_allow_html=True)

st.markdown("---")
st.caption("出典: 愛媛県警 事件事故速報 / 地図: 国土地理院タイル。クラスタはH3、少数はスパイダーファンアウトで重なり解消。要約は原文抜粋で憶測なし。緊急時は110/119へ。")

# requirements 参考
# streamlit
# pandas
# pydeck
# requests
# beautifulsoup4
# rapidfuzz
# h3
# google-generativeai>=0.8.0  # 任意

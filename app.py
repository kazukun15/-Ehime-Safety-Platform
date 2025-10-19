# =============================================
# Ehime Incident/Disaster Map – v2 (Gazetteer + UI polish)
# - Streamlit app
# - Data: Ehime Police "事件事故速報" (scrape)
# - NLP: Google Gemini 2.5 Flash (structured JSON)
# - Gazetteer-first geocoding with fuzzy matching; fallback to Nominatim
# - Modern UI/UX: sidebar filters, chips, cards, confidence color scale
# - Initial map center: Ehime Prefectural Office (~33.8390, 132.7650)
# - GTFS intentionally removed per spec
# ---------------------------------------------
# How to run:
#   pip install -r requirements.txt
#   export GEMINI_API_KEY="..."
#   streamlit run app_v2.py
# ---------------------------------------------

import os
import re
import json
import math
import time
import random
from dataclasses import dataclass
from datetime import datetime
from typing import Dict, List, Optional, Tuple

import requests
import pandas as pd
import streamlit as st
import pydeck as pdk
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process as rf_process

APP_TITLE = "愛媛：事件・事故・災害 マップ (v2)"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "EhimeCivic/1.0; contact: localgov"
REQUEST_TIMEOUT = 15

# Initial center (Ehime Prefectural Government Office vicinity)
EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650

GEMINI_MODEL = "gemini-2.5-flash"
SLEEP_RANGE = (0.8, 1.5)

# -------- Streamlit page config & CSS --------
st.set_page_config(page_title=APP_TITLE, layout="wide")
st.markdown(
    """
    <style>
      :root { --card-bg:#11111110; }
      .big-title {font-size:1.6rem; font-weight:700;}
      .chip {display:inline-block; padding:4px 10px; border-radius:999px; margin:0 6px 6px 0; background:#eceff1; font-size:0.9rem;}
      .chip.on {background:#1e88e5; color:#fff}
      .subtle {color:#666}
      .legend {font-size:0.9rem;}
      .stButton>button {border-radius:999px;}
      .feed-card {background:var(--card-bg); padding:12px 14px; border-radius:12px; border:1px solid #e0e0e0;}
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(f"<div class='big-title'>🗺️ {APP_TITLE}</div>", unsafe_allow_html=True)

# -------- Sidebar controls --------
st.sidebar.header("表示項目")
show_accidents = st.sidebar.checkbox("事故情報", True)
show_crimes = st.sidebar.checkbox("犯罪情報", True)
show_disasters = st.sidebar.checkbox("災害情報(警報等)", True)

st.sidebar.header("取得・プライバシー")
if st.sidebar.button("県警速報を再取得"):
    st.session_state.pop("_incidents_cache", None)
    st.session_state.pop("_analysis_cache", None)

gazetteer_path = st.sidebar.text_input("ガゼッティアCSVパス", "data/gazetteer_ehime.csv")
use_fuzzy = st.sidebar.checkbox("ゆらぎ対応（ファジーマッチ）", True)
min_fuzzy_score = st.sidebar.slider("最小スコア", 60, 95, 78)

st.sidebar.caption("※ 参考情報。緊急時は110/119。現地の指示を優先。個人情報は表示しません。")

# -------- HTTP utils --------

def http_get(url: str) -> str:
    r = requests.get(url, timeout=REQUEST_TIMEOUT, headers={"User-Agent": USER_AGENT})
    r.raise_for_status()
    return r.text

# -------- Scraper: Ehime Police --------
@dataclass
class IncidentItem:
    source_url: str
    heading: str
    station: Optional[str]
    incident_date: Optional[str]
    body: str
    fetched_at: str


def parse_ehime_police_page(html: str) -> List[IncidentItem]:
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text("\n", strip=True)
    lines = [ln for ln in text.split("\n") if ln.strip()]

    blocks: List[Dict] = []
    current = None
    for ln in lines:
        if ln.startswith("■"):
            if current:
                blocks.append(current)
            current = {"heading": ln.strip(), "body_lines": []}
        else:
            if current:
                current["body_lines"].append(ln.strip())
    if current:
        blocks.append(current)

    out: List[IncidentItem] = []
    today = datetime.now().date()
    cy = today.year

    for b in blocks:
        heading = b.get("heading", "")
        body = " ".join(b.get("body_lines", [])).strip()
        m_date = re.search(r"（?(\d{1,2})月(\d{1,2})日", heading)
        m_station = re.search(r"（\d{1,2}月\d{1,2}日\s*([^\s）]+)）", heading)

        incident_date = None
        if m_date:
            m = int(m_date.group(1)); d = int(m_date.group(2))
            y = cy; cand = datetime(y, m, d).date()
            if cand > today: y -= 1
            incident_date = datetime(y, m, d).date().isoformat()

        station = m_station.group(1) if m_station else None
        out.append(IncidentItem(
            source_url=EHIME_POLICE_URL,
            heading=heading,
            station=station,
            incident_date=incident_date,
            body=body,
            fetched_at=datetime.now().astimezone().isoformat(timespec="seconds"),
        ))
    return out

# -------- Gemini (google-generativeai) --------

def gemini_client():
    import google.generativeai as genai
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        st.error("GEMINI_API_KEY が未設定です。環境変数を設定してください。")
        st.stop()
    genai.configure(api_key=api_key)
    return genai.GenerativeModel(GEMINI_MODEL)


def gemini_analyze_items(items: List[IncidentItem]) -> List[Dict]:
    model = gemini_client()
    sys_prompt = (
        "あなたは日本の行政向けNLPアナライザです。与えられた速報テキストから厳密なJSONを返します。"
        "事実の補完は禁止。出力は application/json のみ。欠測は null。"
    )
    results: List[Dict] = []
    for it in items:
        user_prompt = f"""
【出力JSONフィールド】
category: "交通事故"|"火災"|"事件"|"死亡事案"|"窃盗"|"詐欺"|"その他"
municipality: 市町村名 / 不明は null
place_strings: 施設・地名候補の配列
road_refs: 道路参照配列（例: 国道/県道）
occurred_date: YYYY-MM-DD / 不明は null
occurred_time_text: "朝/昼/夜/未明/○時○分頃" 等 / 不明は null
summary_ja: 120字以内の要約（原文準拠・憶測禁止）
confidence: 0.0〜1.0
raw_heading: 見出し
raw_snippet: 重要部分の原文（100〜200字）

【既知メタ】署名:{it.station} 推定日:{it.incident_date} 年範囲:{datetime.now().year}-01-01〜{datetime.now().date().isoformat()}
【入力】見出し:{it.heading}\n本文:{it.body}
"""
        gen_cfg = {
            "temperature": 0.2,
            "top_p": 0.9,
            "top_k": 40,
            "max_output_tokens": 1024,
            "response_mime_type": "application/json",
        }
        try:
            resp = model.generate_content([
                {"role":"system","parts":[sys_prompt]},
                {"role":"user","parts":[user_prompt]},
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

        results.append(data)
        time.sleep(random.uniform(*SLEEP_RANGE))
    return results

# -------- Gazetteer (CSV) --------
@st.cache_data(show_spinner=False)
def load_gazetteer(csv_path: str) -> Optional[pd.DataFrame]:
    try:
        df = pd.read_csv(csv_path)
        # expected columns: name, alt_names, type, lon, lat, area_m2(optional)
        for col in ["name","type","lon","lat"]:
            if col not in df.columns:
                st.warning("ガゼッティアの列が不足しています: name,type,lon,lat は必須")
                return None
        df["alt_names"] = df.get("alt_names", "").fillna("")
        return df
    except Exception:
        return None


def gazetteer_lookup(place: str, gaz: pd.DataFrame, use_fuzzy: bool, min_score: int) -> Optional[Tuple[float,float,str]]:
    # 1) direct substring or exact
    m = gaz[(gaz["name"].str.contains(place, na=False)) | (gaz["alt_names"].str.contains(place, na=False))]
    if not m.empty:
        r = m.iloc[0]
        return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore

    # 2) fuzzy (against name + alt_names concatenated)
    if use_fuzzy:
        choices = (gaz["name"] + " | " + gaz["alt_names"].fillna(""))
        match = rf_process.extractOne(place, choices, scorer=fuzz.token_set_ratio)
        if match and match[1] >= min_score:
            idx = match[2]
            r = gaz.iloc[idx]
            return float(r["lon"]), float(r["lat"]), str(r["type"])  # type: ignore

    return None

# Nominatim fallback (respect rate) — for production, replace with licensed API

def geocode_nominatim(name: str, municipality: Optional[str]) -> Optional[Tuple[float,float]]:
    try:
        q = f"{name} {municipality or ''} 愛媛県 日本".strip()
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": q, "format": "jsonv2", "limit": 1}
        r = requests.get(url, params=params, timeout=15, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        arr = r.json()
        if isinstance(arr, list) and arr:
            lat = float(arr[0]["lat"])  # type: ignore
            lon = float(arr[0]["lon"])  # type: ignore
            return lon, lat
    except Exception:
        return None
    return None

# circle polygon for pydeck

def circle_coords(lon: float, lat: float, radius_m: int = 300, n: int = 64) -> List[List[float]]:
    coords: List[List[float]] = []
    r_earth = 6378137.0
    dlat = radius_m / r_earth
    dlon = radius_m / (r_earth * math.cos(math.radians(lat)))
    for i in range(n):
        ang = 2 * math.pi * i / n
        lat_i = lat + math.degrees(dlat * math.sin(ang))
        lon_i = lon + math.degrees(dlon * math.cos(ang))
        coords.append([lon_i, lat_i])
    coords.append(coords[0])
    return coords

# radius rules

def decide_radius_m(match_type: str) -> int:
    if match_type == "facility":
        return 300
    if match_type == "intersection":
        return 250
    if match_type in ("town","chome"):
        return 600
    if match_type in ("oaza","aza"):
        return 900
    if match_type in ("city","municipality"):
        return 2000
    return 800

# -------- Optional JMA warnings (placeholder) --------

def fetch_jma_warnings_prefecture(pref_code: str = "38") -> List[Dict]:
    try:
        # Placeholder: return [] to avoid unreliable endpoints in MVP
        return []
    except Exception:
        return []

# -------- Data pipeline (cache) --------
@st.cache_data(ttl=300)
def load_incidents() -> List[IncidentItem]:
    html = http_get(EHIME_POLICE_URL)
    return parse_ehime_police_page(html)

@st.cache_data(ttl=300)
def analyze_incidents(items: List[IncidentItem]) -> pd.DataFrame:
    data = gemini_analyze_items(items)
    return pd.DataFrame(data)

# -------- Run pipeline --------
with st.spinner("県警速報の取得・解析中..."):
    items = load_incidents()
    an_df = analyze_incidents(items)

# Sidebar date filter
an_df["occurred_date"] = pd.to_datetime(an_df["occurred_date"], errors="coerce")
min_date = an_df["occurred_date"].min()
max_date = an_df["occurred_date"].max()
if pd.notna(min_date) and pd.notna(max_date):
    dr = st.sidebar.date_input("発生日フィルタ", value=(min_date.date(), max_date.date()))
    if isinstance(dr, tuple) and len(dr) == 2:
        d0, d1 = pd.to_datetime(dr[0]), pd.to_datetime(dr[1])
        an_df = an_df[(an_df["occurred_date"] >= d0) & (an_df["occurred_date"] <= d1)]

# Category chips
cats = sorted([c for c in an_df["category"].dropna().unique().tolist() if c])
st.write(" ".join([f"<span class='chip on'>{c}</span>" for c in cats]), unsafe_allow_html=True)

# Gazetteer load
gaz_df = load_gazetteer(gazetteer_path) if gazetteer_path else None

# ---- Build map features with gazetteer-first geocoding ----
features = []
for _, row in an_df.iterrows():
    if row.get("category") in ("交通事故","事件","窃盗","詐欺","死亡事案"):
        if not (show_accidents or show_crimes):
            continue
    # 災害は別途（JMA）

    municipality: Optional[str] = row.get("municipality")
    places: List[str] = row.get("place_strings") or []

    lonlat: Optional[Tuple[float,float]] = None
    mtype = "unknown"

    # try gazetteer
    if gaz_df is not None:
        for ptxt in places:
            g = gazetteer_lookup(ptxt, gaz_df, use_fuzzy, min_fuzzy_score)
            if g:
                lonlat = (g[0], g[1])
                mtype = g[2]
                break
        if not lonlat and municipality:
            g = gazetteer_lookup(municipality, gaz_df, use_fuzzy, min_fuzzy_score)
            if g:
                lonlat = (g[0], g[1])
                mtype = g[2]

    # fallback to OSM if still missing
    if not lonlat:
        for ptxt in places:
            pt = geocode_nominatim(ptxt, municipality)
            if pt:
                lonlat = pt
                mtype = "facility"
                break
            time.sleep(1.0)
        if not lonlat and municipality:
            pt = geocode_nominatim(municipality, None)
            if pt:
                lonlat = pt
                mtype = "city"
            time.sleep(1.0)

    if not lonlat:
        continue

    lon, lat = lonlat
    radius_m = decide_radius_m(mtype)
    conf = float(row.get("confidence", 0.4))
    color = [255, 140, 0, int(40 + min(160, conf*160))]  # opacity by confidence

    props = {
        "title": row.get("category", "その他"),
        "summary": row.get("summary_ja"),
        "municipality": municipality,
        "source": row.get("source_url"),
        "fetched_at": row.get("fetched_at"),
        "confidence": conf,
        "radius_m": radius_m,
        "match_type": mtype,
        "raw_heading": row.get("raw_heading"),
    }
    features.append({
        "type": "Feature",
        "geometry": {"type": "Polygon", "coordinates": [circle_coords(lon, lat, radius_m)]},
        "properties": {**props, "_fill": color},
    })

geojson = {"type":"FeatureCollection","features":features}

# ---- Map ----
view_state = pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9)
layer_incidents = pdk.Layer(
    "GeoJsonLayer",
    data=geojson,
    pickable=True,
    stroked=True,
    filled=True,
    get_line_width=2,
    get_line_color=[230,90,20],
    get_fill_color="properties._fill",
    auto_highlight=True,
)

layers = []
if show_accidents or show_crimes:
    layers.append(layer_incidents)

tooltip = {"html": "<b>{title}</b><br/>{summary}<br/><span class='subtle'>{municipality}</span><br/>半径:{radius_m}m / conf:{confidence}",
           "style": {"backgroundColor":"#111","color":"white"}}

deck = pdk.Deck(layers=layers, initial_view_state=view_state, tooltip=tooltip)

col_map, col_feed = st.columns([7,5], gap="large")
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
    # quick filters
    cat_filter = st.multiselect("カテゴリ絞込", options=cats, default=cats)

    feed = an_df.copy()
    if cat_filter:
        feed = feed[feed["category"].isin(cat_filter)]

    # Search box for text
    q = st.text_input("キーワード検索（要約/原文）")
    if q:
        feed = feed[feed.apply(lambda r: q in (r.get("summary_ja") or "") or q in (r.get("raw_snippet") or ""), axis=1)]

    # Card renderer
    for _, r in feed.iterrows():
        st.markdown("<div class='feed-card'>", unsafe_allow_html=True)
        st.markdown(f"**{r.get('category','その他')}**")
        st.caption(r.get("summary_ja") or "要約なし")
        st.caption(f"{r.get('municipality') or '市町村不明'} / 取得: {r.get('fetched_at')} / conf: {r.get('confidence')}")
        st.link_button("出典を開く", r.get("source_url"), help="県警ページ")
        st.markdown("</div>", unsafe_allow_html=True)

    if show_disasters:
        st.markdown("---")
        st.subheader("災害情報（警報・注意報）")
        jma = fetch_jma_warnings_prefecture("38")
        if not jma:
            st.caption("JMA警報の取得は未設定です。エンドポイント提供後に実装します。")
        else:
            for w in jma:
                st.write(w)

# Export area
st.markdown("---")
col1, col2 = st.columns(2)
with col1:
    if st.button("解析結果をJSONでダウンロード"):
        js = an_df.to_json(force_ascii=False, orient="records", indent=2)
        st.download_button("download incidents.json", js, file_name="incidents.json", mime="application/json")
with col2:
    st.caption("© Data: 愛媛県警 事件事故速報 / Geocoding: Gazetteer→OSM(Nominatim). このアプリは参考情報です。")

# -------- requirements.txt (reference) --------
# streamlit
# pandas
# pydeck
# requests
# beautifulsoup4
# google-generativeai>=0.8.0
# rapidfuzz

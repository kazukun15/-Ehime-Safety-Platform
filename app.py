# -*- coding: utf-8 -*-
"""
愛媛セーフティ・プラットフォーム (ESP) - Mobile Full Edition (Light Theme)
Version: 12.0
Author: World Class Program Designer
Description: 全機能搭載、地図が見やすいライトテーマUI/UX刷新版
"""

import math
import re
import time
import textwrap
import random
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from io import StringIO
from typing import Dict, List, Optional, Tuple, Any

import requests
import pandas as pd
import pydeck as pdk
import streamlit as st
from bs4 import BeautifulSoup
from streamlit_autorefresh import st_autorefresh

# ==============================================================================
# [Config] 設定
# ==============================================================================
class AppConfig:
    TITLE = "愛媛セーフティ・プラットフォーム"
    SUBTITLE = "Light Theme v12.0"
    USER_AGENT = "ESP/12.0-MobileLight"
    TIMEOUT = 10
    MAX_WORKERS = 4
    
    # 愛媛県中心座標
    EHIME_LAT = 33.8390
    EHIME_LON = 132.7650
    INIT_ZOOM = 9

    # Endpoints
    POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
    JARTIC_URL = "https://api.jartic-open-traffic.org/geoserver"
    OVERPASS_URL = "https://overpass-api.de/api/interpreter"

    # 市町座標データ
    CITY_DATA = {
        "松山市":(132.7650,33.8390),"今治市":(133.0000,34.0660),"新居浜市":(133.2830,33.9600),
        "西条市":(133.1830,33.9180),"大洲市":(132.5500,33.5000),"伊予市":(132.7010,33.7550),
        "四国中央市":(133.5500,33.9800),"西予市":(132.5000,33.3660),"東温市":(132.8710,33.7930),
        "上島町":(133.2000,34.2600),"久万高原町":(132.9040,33.5380),"松前町":(132.7110,33.7870),
        "砥部町":(132.7870,33.7350),"内子町":(132.6580,33.5360),"伊方町":(132.3560,33.4880),
        "松野町":(132.7570,33.2260),"鬼北町":(132.8800,33.2280),"愛南町":(132.5660,33.0000),
        "宇和島市":(132.5600,33.2230),"八幡浜市":(132.4230,33.4620),
    }

    # 地図スタイル設定（配色調整）
    CAT_STYLE = {
        "交通事故": {"color": [230, 50, 50, 255],   "radius": 150, "icon": "💥"},
        "火災":     {"color": [255, 100, 0, 255],   "radius": 150, "icon": "🔥"},
        "死亡事案": {"color": [150, 0, 150, 255],   "radius": 180, "icon": "🙏"},
        "窃盗":     {"color": [0, 120, 220, 255],   "radius": 120, "icon": "🏃"},
        "詐欺":     {"color": [0, 160, 120, 255],   "radius": 120, "icon": "⚠"},
        "事件":     {"color": [220, 180, 0, 255],   "radius": 130, "icon": "⚡"},
        "その他":   {"color": [100, 100, 100, 200], "radius": 100, "icon": "・"},
    }

    TILESETS = {
        "標準":      {"url": "https://tile.openstreetmap.org/{z}/{x}/{y}.png", "max_zoom": 19},
        "淡色":      {"url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom": 18},
        "航空写真":  {"url": "https://cyberjapandata.gsi.go.jp/xyz/seamlessphoto/{z}/{x}/{y}.jpg", "max_zoom": 18},
    }

    # 危険交差点データ
    HOTSPOT_CSV = """地点名,緯度,経度,年間最多事故件数,補足
天山交差点,33.8223,132.7758,6,松山市天山町
和泉交差点,33.8216,132.7554,5,松山市和泉町
小坂交差点,33.8266,132.7833,5,松山市枝松
本町5丁目,33.8530,132.7588,4,松山市本町
山越交差点,33.8565,132.7592,4,松山市山越
消防局前,33.8527,132.7588,4,松山市本町
大川橋,33.8739,132.7521,4,松山市鴨川町
久米交差点,33.8143,132.7957,4,松山市久米"""

# ==============================================================================
# [UI/CSS] ライトテーマ＆スマホ最適化デザイン
# ==============================================================================
def inject_css():
    st.markdown("""
    <style>
      /* カラーパレット定義 (ライトテーマ) */
      :root{
        --bg: #f4f7f9;       /* 全体の背景色：明るいグレー */
        --card: #ffffff;     /* カードの背景色：白 */
        --text: #333333;     /* メインテキスト色：濃いグレー */
        --muted: #666666;    /* サブテキスト色：薄いグレー */
        --accent: #0066cc;   /* アクセントカラー：青 */
        --border: #e0e0e0;   /* ボーダー色 */
      }
      /* 全体の設定 */
      .stApp { background-color: var(--bg); color: var(--text); }
      a { color: var(--accent) !important; text-decoration: none; }
      
      /* タブのスタイル調整：明るく、選択状態を明確に */
      .stTabs [data-baseweb="tab-list"] { gap: 8px; margin-bottom: 12px; }
      .stTabs [data-baseweb="tab"] {
        height: 48px; flex: 1; background-color: #eaeff3; 
        border-radius: 8px; color: var(--muted); font-weight: 600;
        border: 1px solid transparent; transition: all 0.2s;
      }
      .stTabs [data-baseweb="tab"]:hover { background-color: #e0e6ec; }
      .stTabs [data-baseweb="tab"][aria-selected="true"] {
        background-color: var(--accent); color: white; border-color: var(--accent);
      }

      /* ティッカー (無限ループ)：明るい背景で視認性アップ */
      .ticker-wrap {
        width: 100%; overflow: hidden; background: var(--card);
        border-bottom: 1px solid var(--border); border-top: 1px solid var(--border);
        white-space: nowrap; padding: 10px 0; margin-bottom: 12px;
        box-shadow: 0 2px 4px rgba(0,0,0,0.03);
      }
      .ticker { display: inline-block; animation: ticker 45s linear infinite; }
      @keyframes ticker { 0% { transform: translateX(100%); } 100% { transform: translateX(-100%); } }
      .ticker-item { margin-right: 40px; color: var(--text); font-size: 0.9rem; display: inline-flex; align-items: center; }
      .ticker-tag { background: #eaeff3; padding: 2px 8px; border-radius: 12px; font-size: 0.75rem; margin-right: 6px; color: var(--muted); font-weight: bold;}

      /* カードスタイル：白背景＋影で情報を整理 */
      .feed-card {
        background: var(--card); padding: 16px; border-radius: 12px;
        border: 1px solid var(--border); margin-bottom: 12px;
        box-shadow: 0 2px 8px rgba(0,0,0,0.05); transition: transform 0.2s;
      }
      .feed-card:active { transform: scale(0.99); } /* タップ時のフィードバック */
      .feed-header { display: flex; justify-content: space-between; margin-bottom: 8px; align-items: center;}
      .feed-title { font-weight: 700; color: var(--text); display:flex; align-items:center; gap:8px; font-size: 1rem;}
      .feed-loc { font-size: 0.8rem; background: #eaeff3; padding: 4px 10px; border-radius: 12px; color: var(--muted); font-weight: 600;}
      .feed-body { font-size: 0.95rem; line-height: 1.6; color: #444; }
      .feed-link { text-align: right; font-size: 0.85rem; margin-top: 8px; font-weight: 600;}
      
      /* 地図のツールチップもライトテーマに */
      .map-tooltip {
          background: white !important; color: #333 !important;
          box-shadow: 0 2px 8px rgba(0,0,0,0.15) !important;
          border: 1px solid #eee !important;
      }
    </style>
    """, unsafe_allow_html=True)

# ==============================================================================
# [Logic] データ処理・ジオメトリ計算
# ==============================================================================

# --- Helper Logic for Geometry (JARTIC Line Snapping) ---
def _meters_scale(lat: float) -> Tuple[float, float]:
    return 111320 * math.cos(math.radians(lat)), 110540

def _project_point(p: List[float], a: List[float], b: List[float]) -> Tuple[List[float], float]:
    ax, ay = a; bx, by = b; px, py = p
    kx, ky = _meters_scale((ay+by)/2)
    ax2, ay2, bx2, by2, px2, py2 = ax*kx, ay*ky, bx*kx, by*ky, px*kx, py*ky
    vx, vy = bx2-ax2, by2-ay2
    l2 = vx*vx + vy*vy
    if l2 == 0: return a, 999999
    t = max(0.0, min(1.0, ((px2-ax2)*vx + (py2-ay2)*vy) / l2))
    projx2, projy2 = ax2 + t*vx, ay2 + t*vy
    dist = math.hypot(px2-projx2, py2-projy2)
    return [projx2/kx, projy2/ky], dist

def build_snap_lines(jpoints: List[Dict], ways: List[Dict]) -> List[Dict]:
    lines = []
    if not jpoints or not ways: return lines
    for jp in jpoints:
        total = jp.get("total", 0)
        if total < 50: continue
        p = jp["position"]
        length_m = min(3000, total * 5)
        best_dist = 300
        best_proj = None
        best_way_vec = None
        for w in ways:
            coords = w["coords"]
            for i in range(len(coords)-1):
                proj, dist = _project_point(p, coords[i], coords[i+1])
                if dist < best_dist:
                    best_dist = dist
                    best_proj = proj
                    best_way_vec = [coords[i+1][0]-coords[i][0], coords[i+1][1]-coords[i][1]]
        if best_proj and best_way_vec:
            vec_len = math.hypot(best_way_vec[0], best_way_vec[1])
            if vec_len > 0:
                dx = (best_way_vec[0] / vec_len) * (length_m / 111000)
                dy = (best_way_vec[1] / vec_len) * (length_m / 111000)
                lines.append({
                    "path": [best_proj, [best_proj[0]+dx, best_proj[1]+dy]],
                    "color": [255, 50, 50, 200],
                    "width": 5 + min(15, total // 50)
                })
    return lines

# --- Data Fetching ---

@dataclass
class Incident:
    category: str
    summary: str
    municipality: str
    lon: float
    lat: float
    style: Dict
    src: str

def fetch_police_data() -> List[Incident]:
    try:
        r = requests.get(AppConfig.POLICE_URL, headers={"User-Agent": AppConfig.USER_AGENT}, timeout=AppConfig.TIMEOUT)
        r.encoding = r.apparent_encoding or 'utf-8'
        soup = BeautifulSoup(r.text, "html.parser")
        text = soup.get_text("\n", strip=True)
        text = re.sub(r"【愛媛県警からのお願い！】[\s\S]*?(?=■|$)", "", text)
        results = []
        curr_head = ""; curr_body = []
        for line in text.split("\n"):
            if line.startswith("■"):
                if curr_head: results.append(parse_incident(curr_head, " ".join(curr_body)))
                curr_head = line.replace("■", "").strip(); curr_body = []
            elif curr_head: curr_body.append(line.strip())
        if curr_head: results.append(parse_incident(curr_head, " ".join(curr_body)))
        return results
    except: return []

def parse_incident(head: str, body: str) -> Incident:
    full = head + " " + body
    cat = next((k for k in AppConfig.CAT_STYLE if k in full), "その他")
    muni = next((k for k in AppConfig.CITY_DATA if k in full), "愛媛県")
    lon, lat = AppConfig.CITY_DATA.get(muni, (AppConfig.EHIME_LON, AppConfig.EHIME_LAT))
    lon += random.uniform(-0.015, 0.015); lat += random.uniform(-0.015, 0.015)
    return Incident(cat, body[:80]+"..." if len(body)>80 else body, muni, lon, lat, AppConfig.CAT_STYLE.get(cat, AppConfig.CAT_STYLE["その他"]), AppConfig.POLICE_URL)

def fetch_jartic_data() -> List[Dict]:
    now = datetime.utcnow() + timedelta(hours=9) - timedelta(minutes=20)
    mm = (now.minute // 5) * 5
    tcode = now.replace(minute=mm, second=0).strftime("%Y%m%d%H%M")
    cql = f"道路種別=3 AND 時間コード={tcode} AND BBOX(ジオメトリ,132.2,33.0,133.7,34.2,'EPSG:4326')"
    params = {"service":"WFS", "version":"2.0.0", "request":"GetFeature", "typeNames":"t_travospublic_measure_5m", "outputFormat":"application/json", "cql_filter": cql}
    try:
        r = requests.get(AppConfig.JARTIC_URL, params=params, timeout=AppConfig.TIMEOUT)
        if r.status_code!=200: return []
        data = r.json()
        points = []
        for f in data.get("features", []):
            props = f.get("properties", {})
            total = (props.get("上り・小型交通量") or 0) + (props.get("下り・小型交通量") or 0)
            coords = f.get("geometry", {}).get("coordinates", [])
            if coords and total > 0:
                for c in coords: points.append({"position": [c[0], c[1]], "total": int(total)})
        return points
    except: return []

def fetch_osm_simple() -> List[Dict]:
    q = f"""[out:json][timeout:10];way["highway"~"primary|trunk"](33.0,132.2,34.2,133.7);out geom;"""
    try:
        r = requests.post(AppConfig.OVERPASS_URL, data={"data": q}, timeout=5)
        if r.status_code==200:
            return [{"coords": [[p["lon"], p["lat"]] for p in el["geometry"]]} for el in r.json().get("elements", []) if "geometry" in el]
    except: return []
    return []

# ==============================================================================
# [Main] アプリケーション本体
# ==============================================================================

def main():
    # ページ設定：広がりを持たせる
    st.set_page_config(page_title="ESP Mobile", layout="wide", page_icon="🚓")
    inject_css()

    # --- Sidebar (設定) ---
    with st.sidebar:
        st.header("⚙️ 表示設定")
        area_filter = st.multiselect("地域で絞り込み", list(AppConfig.CITY_DATA.keys()))
        st.markdown("---")
        map_style_name = st.selectbox("地図の背景", list(AppConfig.TILESETS.keys()))
        is_3d = st.toggle("3Dモード (交差点)", value=True)
        show_jartic = st.toggle("交通情報 (JARTIC)", value=True)
        show_hotspots = st.toggle("危険交差点表示", value=True)
        st.caption("※3Dモードは地図を傾けると有効になります")

    # --- Data Loading ---
    with st.spinner("最新データを取得中..."):
        with ThreadPoolExecutor(max_workers=AppConfig.MAX_WORKERS) as exe:
            f1 = exe.submit(fetch_police_data)
            f2 = exe.submit(fetch_jartic_data)
            f3 = exe.submit(fetch_osm_simple)
            incidents = f1.result()
            jartic_pts = f2.result() if show_jartic else []
            osm_ways = f3.result() if show_jartic else []

    if area_filter: incidents = [i for i in incidents if i.municipality in area_filter]

    # --- Ticker ---
    ticker_text = ""
    for i in incidents[:7]:
        ticker_text += f"<span class='ticker-item'><span class='ticker-tag'>{i.category}</span>{i.municipality}｜{i.summary[:25]}</span>"
    if show_jartic:
        ticker_text += "<span class='ticker-item' style='color:var(--accent); font-weight:bold;'>【交通】JARTICリアルタイム情報 連携中</span>"
    st.markdown(f"<div class='ticker-wrap'><div class='ticker'>{ticker_text}</div></div>", unsafe_allow_html=True)

    # --- Main Tabs ---
    tab_map, tab_list = st.tabs(["🗺️ マップで見る", "🚨 リストで見る"])

    # === TAB 1: MAP ===
    with tab_map:
        layers = []
        # 1. 背景地図 (TileLayer)
        tile_cfg = AppConfig.TILESETS[map_style_name]
        layers.append(pdk.Layer("TileLayer", data=tile_cfg["url"], min_zoom=0, max_zoom=tile_cfg["max_zoom"], opacity=1.0))

        # 2. 危険交差点 (Hotspots)
        if show_hotspots:
            hot_df = pd.read_csv(StringIO(AppConfig.HOTSPOT_CSV))
            hot_df["val"] = hot_df["年間最多事故件数"].astype(int)
            if is_3d:
                layers.append(pdk.Layer("ColumnLayer", data=hot_df, get_position="[経度, 緯度]", get_elevation="val", elevation_scale=50, radius=100, get_fill_color=[255, 0, 0, 180], extruded=True, pickable=True))
            else:
                layers.append(pdk.Layer("HeatmapLayer", data=hot_df, get_position="[経度, 緯度]", get_weight="val", radius_pixels=60, intensity=2, threshold=0.1))

        # 3. JARTIC (Traffic)
        if show_jartic and jartic_pts:
            layers.append(pdk.Layer("ScatterplotLayer", data=jartic_pts, get_position="position", get_fill_color=[255, 200, 0, 180], get_radius="total", radius_scale=0.5, radius_min_pixels=3, pickable=True))
            if osm_ways:
                snap_lines = build_snap_lines(jartic_pts, osm_ways)
                if snap_lines:
                    layers.append(pdk.Layer("PathLayer", data=snap_lines, get_path="path", get_color="color", get_width="width", width_min_pixels=2, opacity=0.8))

        # 4. 事件・事故 (Incidents)
        if incidents:
            df_inc = pd.DataFrame([asdict(i) for i in incidents])
            df_inc["color"] = df_inc["style"].apply(lambda s: s["color"])
            df_inc["radius"] = df_inc["style"].apply(lambda s: s["radius"])
            df_inc["icon"] = df_inc["style"].apply(lambda s: s["icon"])
            # Tooltip: ライトテーマ用にスタイル調整
            df_inc["tooltip"] = df_inc.apply(lambda r: f"""
                <div style='font-family:sans-serif; padding:4px;'>
                <div style='font-weight:bold; font-size:1.1em; margin-bottom:4px;'>{r['icon']} {r['category']}</div>
                <div style='color:#666; font-size:0.9em; margin-bottom:6px;'>{r['municipality']}</div>
                <div style='line-height:1.4;'>{r['summary'][:40]}</div>
                </div>""".replace("\n", ""), axis=1)

            layers.append(pdk.Layer("ScatterplotLayer", data=df_inc, get_position="[lon, lat]", get_fill_color="color", get_radius="radius", stroked=True, get_line_color=[255,255,255], line_width_min_pixels=2, pickable=True))

        view_state = pdk.ViewState(latitude=AppConfig.EHIME_LAT, longitude=AppConfig.EHIME_LON, zoom=AppConfig.INIT_ZOOM, pitch=45 if is_3d else 0)
        # map_provider=Noneで背景地図を確実に表示
        st.pydeck_chart(pdk.Deck(layers=layers, initial_view_state=view_state, tooltip={"html": "{tooltip}", "style": {"color": "#333", "backgroundColor": "white"}}, map_provider=None), use_container_width=True, height=500)

    # === TAB 2: LIST ===
    with tab_list:
        st.markdown("<div style='margin-bottom:10px;'></div>", unsafe_allow_html=True) # スペーサー
        q = st.text_input("Search", placeholder="🔍 キーワード検索 (例: 事故, 松山市...)")
        view_list = [i for i in incidents if q in (i.summary + i.municipality)] if q else incidents
        
        html_buffer = ""
        for item in view_list:
            card = textwrap.dedent(f"""
                <div class='feed-card'>
                    <div class='feed-header'>
                        <div class='feed-title'><span>{item.style['icon']}</span>{item.category}</div>
                        <div class='feed-loc'>{item.municipality}</div>
                    </div>
                    <div class='feed-body'>{item.summary}</div>
                    <div class='feed-link'><a href='{item.src}' target='_blank'>詳細を確認 &rarr;</a></div>
                </div>
            """)
            html_buffer += card
        
        if not view_list: st.info("該当する情報はありませんでした。")
        else: st.markdown(html_buffer, unsafe_allow_html=True)

    st_autorefresh(interval=5 * 60 * 1000, key="refresh")

if __name__ == "__main__":
    main()

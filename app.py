# -*- coding: utf-8 -*-
"""
愛媛セーフティ・プラットフォーム (ESP) - Ultimate UI Edition
Version: 16.0
Author: World Class Program Designer
Description: 犯罪係数の視覚化（メーター表示）、スタイリッシュUI、全機能統合版
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
    SUBTITLE = "Criminal Coefficient Visualizer v16.0"
    USER_AGENT = "ESP/16.0-Visual"
    TIMEOUT = 10
    MAX_WORKERS = 4
    
    # 愛媛県中心座標
    EHIME_LAT = 33.8390
    EHIME_LON = 132.7650
    INIT_ZOOM = 10

    # API Endpoints
    POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
    JARTIC_URL = "https://api.jartic-open-traffic.org/geoserver"
    OVERPASS_URL = "https://overpass-api.de/api/interpreter"

    # 市町データ
    CITY_DATA = {
        "松山市":(132.7650,33.8390),"今治市":(133.0000,34.0660),"新居浜市":(133.2830,33.9600),
        "西条市":(133.1830,33.9180),"大洲市":(132.5500,33.5000),"伊予市":(132.7010,33.7550),
        "四国中央市":(133.5500,33.9800),"西予市":(132.5000,33.3660),"東温市":(132.8710,33.7930),
        "上島町":(133.2000,34.2600),"久万高原町":(132.9040,33.5380),"松前町":(132.7110,33.7870),
        "砥部町":(132.7870,33.7350),"内子町":(132.6580,33.5360),"伊方町":(132.3560,33.4880),
        "松野町":(132.7570,33.2260),"鬼北町":(132.8800,33.2280),"愛南町":(132.5660,33.0000),
        "宇和島市":(132.5600,33.2230),"八幡浜市":(132.4230,33.4620),
    }

    # 地図スタイル
    CAT_STYLE = {
        "交通事故": {"color": [230, 50, 50, 255],   "radius": 150, "icon": "💥", "base_risk": 40},
        "火災":     {"color": [255, 100, 0, 255],   "radius": 150, "icon": "🔥", "base_risk": 60},
        "死亡事案": {"color": [150, 0, 150, 255],   "radius": 180, "icon": "🙏", "base_risk": 80},
        "窃盗":     {"color": [0, 120, 220, 255],   "radius": 120, "icon": "🏃", "base_risk": 30},
        "詐欺":     {"color": [0, 160, 120, 255],   "radius": 120, "icon": "⚠", "base_risk": 50},
        "事件":     {"color": [220, 180, 0, 255],   "radius": 130, "icon": "⚡", "base_risk": 55},
        "その他":   {"color": [100, 100, 100, 200], "radius": 100, "icon": "・", "base_risk": 20},
    }

    TILESETS = {
        "標準 (OSM)": {"url": "https://tile.openstreetmap.org/{z}/{x}/{y}.png", "max_zoom": 19},
        "Googleマップ (道路)": {"url": "https://mt1.google.com/vt/lyrs=m&x={x}&y={y}&z={z}", "max_zoom": 20},
        "Googleマップ (航空写真)": {"url": "https://mt1.google.com/vt/lyrs=s&x={x}&y={y}&z={z}", "max_zoom": 20},
        "淡色地図": {"url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom": 18},
    }

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
# [Logic] 環境犯罪係数・予測ロジック
# ==============================================================================
class EnvironmentalAnalyzer:
    """気象・天文データに基づく環境分析"""
    
    @staticmethod
    def get_moon_phase(date: datetime) -> Dict:
        """月齢計算"""
        diff = date - datetime(2000, 1, 6)
        days = diff.days
        lunation = 29.53058867
        moon_age = days % lunation
        
        phase_name = "通常月"
        risk_factor = 1.0
        
        if moon_age < 1.0 or moon_age > 28.5:
            phase_name = "新月🌑" # 暗闇リスク
            risk_factor = 1.15
        elif 13.8 < moon_age < 15.8:
            phase_name = "満月🌕" # 衝動性リスク
            risk_factor = 1.25
            
        return {"age": moon_age, "name": phase_name, "factor": risk_factor}

    @staticmethod
    def estimate_weather(lat: float, lon: float, dt: datetime) -> Dict:
        """愛媛県気象シミュレーション"""
        month = dt.month
        hour = dt.hour
        base_temps = {1:6, 2:7, 3:10, 4:15, 5:20, 6:24, 7:28, 8:30, 9:26, 10:20, 11:14, 12:9}
        hour_offset = -math.cos(math.pi * (hour - 4) / 12) * 4
        temp = base_temps[month] + hour_offset + random.uniform(-2, 2)
        humidity = 60 + (20 if month in [6,7,8,9] else -10) + random.uniform(-5, 5)
        di = 0.81 * temp + 0.01 * humidity * (0.99 * temp - 14.3) + 46.3 # 不快指数
        
        stress_factor = 1.0
        if di > 75: stress_factor = 1.1
        if di > 80: stress_factor = 1.3
        
        return {"temp": round(temp, 1), "humidity": round(humidity, 1), "di": round(di, 1), "factor": stress_factor}

def calculate_crime_coefficient(category: str, dt: datetime) -> Dict:
    """犯罪係数算出"""
    base = AppConfig.CAT_STYLE.get(category, AppConfig.CAT_STYLE["その他"])["base_risk"]
    moon = EnvironmentalAnalyzer.get_moon_phase(dt)
    weather = EnvironmentalAnalyzer.estimate_weather(33.8, 132.7, dt)
    
    time_factor = 1.0
    if 23 <= dt.hour or dt.hour <= 4: time_factor = 1.3
    
    coef = base * moon["factor"] * weather["factor"] * time_factor
    coef = min(99.9, max(10.0, coef))
    
    reasons = []
    if moon["factor"] > 1.1: reasons.append(moon['name'])
    if weather["di"] > 80: reasons.append("不快指数高")
    if time_factor > 1.1: reasons.append("深夜帯")
    if not reasons: reasons.append("平常")
    
    # カラーコード定義
    color = "#2ecc71" # Safe (Green)
    level = "Normal"
    if coef > 60: 
        color = "#f39c12" # Caution (Orange)
        level = "Caution"
    if coef > 80: 
        color = "#e74c3c" # Danger (Red)
        level = "Critical"
    
    return {
        "score": int(coef),
        "color": color,
        "level": level,
        "reasons": "・".join(reasons),
        "weather_text": f"{weather['temp']}℃ (不快指数{int(weather['di'])})",
        "moon_text": moon["name"]
    }

# ==============================================================================
# [UI/CSS] スタイリッシュデザイン
# ==============================================================================
def inject_css():
    st.markdown("""
    <style>
      :root{ --bg: #f4f7f9; --card: #ffffff; --text: #333; --muted: #666; --accent: #0984e3; --border: #dfe6e9; }
      .stApp { background-color: var(--bg); color: var(--text); font-family: 'Helvetica Neue', Arial, sans-serif; }
      a { color: var(--accent) !important; text-decoration: none; }
      
      /* タブ */
      .stTabs [data-baseweb="tab-list"] { gap: 8px; margin-bottom: 16px; }
      .stTabs [data-baseweb="tab"] { height: 50px; flex: 1; background-color: #dfe6e9; border-radius: 8px; color: var(--muted); font-weight: 700; border: none; }
      .stTabs [data-baseweb="tab"][aria-selected="true"] { background-color: var(--accent); color: white; box-shadow: 0 4px 6px rgba(9, 132, 227, 0.3); }

      /* カード */
      .feed-card {
        background: var(--card); padding: 0; border-radius: 12px; border: 1px solid var(--border);
        margin-bottom: 16px; box-shadow: 0 4px 12px rgba(0,0,0,0.05); overflow: hidden;
      }
      .feed-content { padding: 16px; }
      
      .feed-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px; }
      .feed-title { font-weight: 800; font-size: 1.05rem; display:flex; align-items:center; gap:6px; color: #2d3436; }
      .feed-loc { font-size: 0.75rem; background: #f1f2f6; padding: 4px 10px; border-radius: 20px; color: #636e72; font-weight: 600; letter-spacing: 0.5px;}
      .feed-body { font-size: 0.95rem; line-height: 1.6; color: #636e72; margin-bottom: 12px; }

      /* --- スタイリッシュ犯罪係数パネル --- */
      .coef-panel {
        background: #f8f9fa; padding: 12px 16px; border-top: 1px solid var(--border);
        display: flex; flex-direction: column; gap: 8px;
      }
      .coef-row-main {
        display: flex; justify-content: space-between; align-items: flex-end;
      }
      .coef-label {
        font-size: 0.7rem; font-weight: 700; color: #b2bec3; letter-spacing: 1px; margin-bottom: 2px;
      }
      .coef-val-box {
        text-align: right; line-height: 1;
      }
      .coef-val {
        font-family: 'Courier New', monospace; font-weight: 900; font-size: 2.2rem;
        letter-spacing: -1px; text-shadow: 0 2px 4px rgba(0,0,0,0.1);
      }
      .coef-level {
        font-size: 0.7rem; font-weight: 800; text-transform: uppercase; color: #b2bec3;
      }

      /* メーターバー */
      .meter-track {
        width: 100%; height: 6px; background: #dfe6e9; border-radius: 3px; overflow: hidden; margin-top: 4px;
      }
      .meter-fill {
        height: 100%; border-radius: 3px; transition: width 0.5s ease-out;
      }

      /* 詳細グリッド */
      .coef-grid {
        display: grid; grid-template-columns: 1fr 1fr; gap: 8px; margin-top: 6px;
      }
      .coef-item {
        background: #fff; padding: 6px 10px; border-radius: 6px; border: 1px solid #eee;
        font-size: 0.8rem; display: flex; align-items: center; gap: 6px; color: #636e72; font-weight: 500;
      }
      .coef-icon { font-size: 1rem; }

      .feed-link { text-align: right; padding: 8px 16px; background: #fff; border-top: 1px solid #f1f2f6;}
      .feed-link a { font-size: 0.85rem; font-weight: 700; color: var(--accent); }

      /* ティッカー */
      .ticker-wrap { background: #fff; border-bottom: 1px solid var(--border); border-top: 1px solid var(--border); padding: 8px 0; white-space: nowrap; overflow: hidden; margin-bottom: 10px;}
      .ticker { display: inline-block; animation: ticker 50s linear infinite; }
      @keyframes ticker { 0% { transform: translateX(100%); } 100% { transform: translateX(-100%); } }
      .ticker-item { margin-right: 32px; color: #2d3436; font-size: 0.85rem; font-weight: 500; display: inline-flex; align-items: center; }
      
      .map-tooltip { background: rgba(255,255,255,0.95) !important; color: #2d3436 !important; box-shadow: 0 4px 12px rgba(0,0,0,0.15) !important; border-radius: 8px !important; border:none !important;}
    </style>
    """, unsafe_allow_html=True)

# ==============================================================================
# [Geometry] 渋滞線生成ロジック
# ==============================================================================
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
        if total < 60: continue
        p = jp["position"]
        length_m = min(4000, total * 6)
        best_dist = 400; best_proj = None; best_vec = None
        for w in ways:
            coords = w["coords"]
            for i in range(len(coords)-1):
                proj, dist = _project_point(p, coords[i], coords[i+1])
                if dist < best_dist:
                    best_dist = dist; best_proj = proj
                    best_vec = [coords[i+1][0]-coords[i][0], coords[i+1][1]-coords[i][1]]
        if best_proj and best_vec:
            vl = math.hypot(best_vec[0], best_vec[1])
            if vl > 0:
                dx = (best_vec[0]/vl)*(length_m/111000); dy = (best_vec[1]/vl)*(length_m/111000)
                lines.append({"path": [best_proj, [best_proj[0]+dx, best_proj[1]+dy]], "color": [255, 50, 50, 200], "width": 6 + min(12, total//80)})
    return lines

# ==============================================================================
# [Data Fetching]
# ==============================================================================
@dataclass
class Incident:
    category: str; summary: str; municipality: str; lon: float; lat: float; 
    style: Dict; src: str; coef: Dict

def fetch_police_data(days: int = 7) -> List[Incident]:
    try:
        r = requests.get(AppConfig.POLICE_URL, headers={"User-Agent": AppConfig.USER_AGENT}, timeout=AppConfig.TIMEOUT)
        r.encoding = r.apparent_encoding or 'utf-8'
        soup = BeautifulSoup(r.text, "html.parser")
        text = soup.get_text("\n", strip=True)
        text = re.sub(r"【愛媛県警からのお願い！】[\s\S]*?(?=■|$)", "", text)
        results = []; curr_head = ""; curr_body = []
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
    coef_data = calculate_crime_coefficient(cat, datetime.now())
    return Incident(cat, body[:90]+"..." if len(body)>90 else body, muni, lon, lat, 
                    AppConfig.CAT_STYLE.get(cat, AppConfig.CAT_STYLE["その他"]), 
                    AppConfig.POLICE_URL, coef_data)

def fetch_jartic_data() -> List[Dict]:
    now = datetime.utcnow() + timedelta(hours=9) - timedelta(minutes=20)
    mm = (now.minute // 5) * 5
    tcode = now.replace(minute=mm, second=0).strftime("%Y%m%d%H%M")
    cql = f"道路種別=3 AND 時間コード={tcode} AND BBOX(ジオメトリ,132.2,33.0,133.7,34.2,'EPSG:4326')"
    params = {"service":"WFS", "version":"2.0.0", "request":"GetFeature", "typeNames":"t_travospublic_measure_5m", "outputFormat":"application/json", "cql_filter": cql}
    try:
        r = requests.get(AppConfig.JARTIC_URL, params=params, timeout=AppConfig.TIMEOUT)
        if r.status_code!=200: return []
        data = r.json(); points = []
        for f in data.get("features", []):
            props = f.get("properties", {})
            total = (props.get("上り・小型交通量") or 0) + (props.get("下り・小型交通量") or 0)
            coords = f.get("geometry", {}).get("coordinates", [])
            if coords and total > 0:
                for c in coords: points.append({"position": [c[0], c[1]], "total": int(total)})
        return points
    except: return []

def fetch_osm_simple() -> List[Dict]:
    q = f"""[out:json][timeout:15];way["highway"~"primary|trunk|secondary"](33.0,132.2,34.2,133.7);out geom;"""
    try:
        r = requests.post(AppConfig.OVERPASS_URL, data={"data": q}, timeout=10)
        if r.status_code==200:
            return [{"coords": [[p["lon"], p["lat"]] for p in el["geometry"]]} for el in r.json().get("elements", []) if "geometry" in el]
    except: return []
    return []

# ==============================================================================
# [Main]
# ==============================================================================
def main():
    st.set_page_config(page_title="ESP Mobile", layout="wide", page_icon="🚓")
    inject_css()

    with st.sidebar:
        st.header("⚙️ 設定")
        env = EnvironmentalAnalyzer.estimate_weather(33.8, 132.7, datetime.now())
        moon = EnvironmentalAnalyzer.get_moon_phase(datetime.now())
        st.caption(f"ENV: {env['temp']}℃ / {moon['name']}")
        
        area_filter = st.multiselect("地域フィルタ", list(AppConfig.CITY_DATA.keys()))
        map_style = st.selectbox("地図スタイル", list(AppConfig.TILESETS.keys()))
        is_3d = st.toggle("3Dモード", value=True)
        show_jartic = st.toggle("交通情報", value=True)
        show_hotspots = st.toggle("危険交差点", value=True)

    with st.spinner("Analyzing..."):
        with ThreadPoolExecutor(max_workers=AppConfig.MAX_WORKERS) as exe:
            f1 = exe.submit(fetch_police_data)
            f2 = exe.submit(fetch_jartic_data)
            f3 = exe.submit(fetch_osm_simple)
            incidents = f1.result()
            jartic_pts = f2.result() if show_jartic else []
            osm_ways = f3.result() if show_jartic else []

    if area_filter: incidents = [i for i in incidents if i.municipality in area_filter]

    # Ticker
    ticker_html = ""
    for i in incidents[:5]:
        ticker_html += f"<span class='ticker-item'><b>{i.category}</b> {i.municipality} ({i.coef['score']})</span>"
    if show_jartic: ticker_html += "<span class='ticker-item' style='color:#0984e3'><b>JARTIC</b> リアルタイム交通情報</span>"
    st.markdown(f"<div class='ticker-wrap'><div class='ticker'>{ticker_html}</div></div>", unsafe_allow_html=True)

    tab_map, tab_list = st.tabs(["🗺️ マップ", "🚨 解析リスト"])

    with tab_map:
        layers = []
        tile = AppConfig.TILESETS[map_style]
        layers.append(pdk.Layer("TileLayer", data=tile["url"], min_zoom=0, max_zoom=tile["max_zoom"], opacity=1.0))

        if show_jartic and jartic_pts and osm_ways:
            snap_lines = build_snap_lines(jartic_pts, osm_ways)
            if snap_lines:
                layers.append(pdk.Layer("PathLayer", data=snap_lines, get_path="path", get_color="color", get_width="width", width_min_pixels=3, opacity=0.8))
        if show_jartic and jartic_pts:
            layers.append(pdk.Layer("ScatterplotLayer", data=jartic_pts, get_position="position", get_fill_color=[255, 200, 0, 160], get_radius="total", radius_scale=0.5, radius_min_pixels=3, pickable=True))
        if show_hotspots:
            hot_df = pd.read_csv(StringIO(AppConfig.HOTSPOT_CSV))
            hot_df["val"] = hot_df["年間最多事故件数"].astype(int)
            layers.append(pdk.Layer("ColumnLayer" if is_3d else "HeatmapLayer", data=hot_df, get_position="[経度, 緯度]", get_elevation="val", elevation_scale=50, radius=100, get_fill_color=[255, 0, 0, 180], extruded=True, pickable=True))

        if incidents:
            df_inc = pd.DataFrame([asdict(i) for i in incidents])
            df_inc["color"] = df_inc["style"].apply(lambda s: s["color"])
            df_inc["radius"] = df_inc["style"].apply(lambda s: s["radius"])
            df_inc["icon"] = df_inc["style"].apply(lambda s: s["icon"])
            df_inc["tooltip"] = df_inc.apply(lambda r: f"""
                <div style='font-family:sans-serif; padding:4px;'>
                <div style='font-size:1.1em;font-weight:bold;margin-bottom:4px'>{r['icon']} {r['category']} <span style='font-size:0.8em;color:{r['coef']['color']}'>Lv.{r['coef']['score']}</span></div>
                <div style='font-size:0.9em;color:#555'>{r['municipality']}</div>
                <div style='margin-top:4px'>{r['summary'][:30]}</div>
                </div>""".replace("\n", ""), axis=1)
            layers.append(pdk.Layer("ScatterplotLayer", data=df_inc, get_position="[lon, lat]", get_fill_color="color", get_radius="radius", stroked=True, get_line_color=[255,255,255], line_width_min_pixels=2, pickable=True))

        view_state = pdk.ViewState(latitude=AppConfig.EHIME_LAT, longitude=AppConfig.EHIME_LON, zoom=AppConfig.INIT_ZOOM, pitch=45 if is_3d else 0)
        st.pydeck_chart(pdk.Deck(layers=layers, initial_view_state=view_state, tooltip={"html": "{tooltip}", "style": {"color": "#333", "backgroundColor": "white"}}, map_provider=None, map_style=None), use_container_width=True, height=520)

    with tab_list:
        st.markdown("<div style='height:8px'></div>", unsafe_allow_html=True)
        q = st.text_input("検索", placeholder="キーワード...")
        view_list = [i for i in incidents if q in (i.summary + i.municipality)] if q else incidents
        
        html_buffer = ""
        for item in view_list:
            coef = item.coef
            card = textwrap.dedent(f"""
                <div class='feed-card'>
                    <div class='feed-content'>
                        <div class='feed-header'>
                            <div class='feed-title'><span>{item.style['icon']}</span>{item.category}</div>
                            <div class='feed-loc'>{item.municipality}</div>
                        </div>
                        <div class='feed-body'>{item.summary}</div>
                    </div>
                    
                    <div class='coef-panel'>
                        <div class='coef-label'>CRIME COEFFICIENT</div>
                        <div class='coef-row-main'>
                            <div style='width:100%; margin-right:12px;'>
                                <div class='meter-track'>
                                    <div class='meter-fill' style='width: {coef["score"]}%; background: {coef["color"]};'></div>
                                </div>
                                <div class='coef-grid'>
                                    <div class='coef-item'><span class='coef-icon'>🌡️</span> {coef["weather_text"]}</div>
                                    <div class='coef-item'><span class='coef-icon'>🌑</span> {coef["moon_text"]}</div>
                                    <div class='coef-item'><span class='coef-icon'>⚠️</span> {coef["reasons"]}</div>
                                </div>
                            </div>
                            <div class='coef-val-box'>
                                <div class='coef-val' style='color: {coef["color"]}'>{coef["score"]}</div>
                                <div class='coef-level'>{coef["level"]}</div>
                            </div>
                        </div>
                    </div>
                    
                    <div class='feed-link'><a href='{item.src}' target='_blank'>詳細を確認 &rarr;</a></div>
                </div>
            """)
            html_buffer += card
        
        if not view_list: st.info("情報はありません")
        else: st.markdown(html_buffer, unsafe_allow_html=True)

    st_autorefresh(interval=5 * 60 * 1000, key="refresh")

if __name__ == "__main__":
    main()

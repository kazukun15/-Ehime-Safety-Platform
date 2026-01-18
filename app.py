# -*- coding: utf-8 -*-
"""
愛媛セーフティ・プラットフォーム (ESP) - Mobile Optimized
Version: 10.1-MobileFix
Description: スマホ最適化（タブレイアウト化）、HTML描画バグ修正、地図表示修正版
"""

import math
import re
import threading
import textwrap
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple, Any

import httpx
import pandas as pd
import pydeck as pdk
import requests
import streamlit as st
from bs4 import BeautifulSoup
from streamlit_autorefresh import st_autorefresh

# ==============================================================================
# [Config & Constants] 設定と定数
# ==============================================================================

class AppConfig:
    TITLE = "愛媛セーフティ・プラットフォーム"
    SUBTITLE = "スマホ対応版 v10.1"
    USER_AGENT = "ESP/10.1-Mobile"
    TIMEOUT = 10
    
    # 座標定数 (愛媛県中心)
    EHIME_LAT = 33.8390
    EHIME_LON = 132.7650
    # 初期ズームレベル（スマホ向けに少し引き気味に調整）
    INIT_ZOOM = 9

    # API Endpoints
    POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
    JARTIC_URL = "https://api.jartic-open-traffic.org/geoserver"
    
    # マップスタイル定義（Mapbox等を使わない標準的な設定）
    CAT_STYLE = {
        "交通事故": {"color": [220, 60, 60, 255],   "radius": 150, "icon": "💥"}, # 赤
        "火災":     {"color": [245, 130, 50, 255],  "radius": 150, "icon": "🔥"}, # オレンジ
        "死亡事案": {"color": [128, 0, 128, 255],   "radius": 180, "icon": "🙏"}, # 紫
        "窃盗":     {"color": [70, 150, 245, 255],  "radius": 120, "icon": "🏃"}, # 青
        "詐欺":     {"color": [40, 180, 160, 255],  "radius": 120, "icon": "⚠"}, # 緑
        "事件":     {"color": [245, 200, 60, 255],  "radius": 130, "icon": "⚡"}, # 黄
        "その他":   {"color": [128, 144, 160, 220], "radius": 100, "icon": "・"}, # グレー
    }

# 自治体データ (簡易ジオコーディング用)
CITY_DATA = {
    "松山市": (132.7650, 33.8390), "今治市": (133.0000, 34.0660), "新居浜市": (133.2830, 33.9600),
    "西条市": (133.1830, 33.9180), "大洲市": (132.5500, 33.5000), "伊予市": (132.7010, 33.7550),
    "四国中央市": (133.5500, 33.9800), "西予市": (132.5000, 33.3660), "東温市": (132.8710, 33.7930),
    "上島町": (133.2000, 34.2600), "久万高原町": (132.9040, 33.5380), "松前町": (132.7110, 33.7870),
    "砥部町": (132.7870, 33.7350), "内子町": (132.6580, 33.5360), "伊方町": (132.3560, 33.4880),
    "松野町": (132.7570, 33.2260), "鬼北町": (132.8800, 33.2280), "愛南町": (132.5660, 33.0000),
    "宇和島市": (132.5600, 33.2230), "八幡浜市": (132.4230, 33.4620),
}
CITY_NAMES = list(CITY_DATA.keys())

# ==============================================================================
# [UI/CSS] スマホ最適化デザイン
# ==============================================================================

def inject_custom_css():
    st.markdown("""
    <style>
      /* ベーススタイル */
      :root{ --bg:#0b0f14; --card:#161b22; --text:#e6edf3; --accent:#2f81f7; }
      .stApp { background-color: var(--bg); color: var(--text); }
      
      /* タブのスタイル調整 */
      .stTabs [data-baseweb="tab-list"] { gap: 8px; }
      .stTabs [data-baseweb="tab"] {
        height: 50px; white-space: pre-wrap; background-color: #21262d; 
        border-radius: 4px; color: #8b949e; flex: 1; justify-content: center;
      }
      .stTabs [data-baseweb="tab"][aria-selected="true"] {
        background-color: var(--accent); color: white;
      }

      /* カードスタイル (スマホで見やすく) */
      .feed-card {
        background: var(--card); padding: 16px; border-radius: 12px; 
        border: 1px solid #30363d; margin-bottom: 12px;
        box-shadow: 0 4px 6px rgba(0,0,0,0.3);
      }
      .feed-header { display:flex; justify-content:space-between; align-items:center; margin-bottom: 8px; }
      .feed-tag { font-weight:bold; font-size:1.0rem; display:flex; align-items:center; gap:6px; }
      .feed-loc { font-size:0.85rem; color:#8b949e; background:#21262d; padding:2px 8px; border-radius:12px; }
      .feed-body { font-size:0.95rem; line-height:1.6; color:#e6edf3; margin-bottom: 8px; }
      .feed-footer { font-size:0.8rem; text-align:right; color:#2f81f7; }
      
      /* 地図上のツールチップ */
      .map-tooltip {
          background: rgba(13, 17, 23, 0.95);
          color: #fff;
          padding: 10px;
          border-radius: 8px;
          border: 1px solid #30363d;
          font-size: 12px;
          max-width: 250px;
      }
    </style>
    """, unsafe_allow_html=True)

# ==============================================================================
# [Logic] データ処理
# ==============================================================================

@dataclass
class IncidentItem:
    heading: str
    body: str

@st.cache_data(ttl=600)
def fetch_ehime_police_data() -> List[IncidentItem]:
    """愛媛県警HPから速報データを取得"""
    headers = {"User-Agent": AppConfig.USER_AGENT}
    try:
        r = requests.get(AppConfig.POLICE_URL, headers=headers, timeout=AppConfig.TIMEOUT)
        r.encoding = r.apparent_encoding or 'utf-8'
        if r.status_code != 200: return []
        
        soup = BeautifulSoup(r.text, "html.parser")
        text = soup.get_text("\n", strip=True)
        # 余計なヘッダー削除
        text = re.sub(r"【愛媛県警からのお願い！】[\s\S]*?(?=■|$)", "", text)
        
        items = []
        curr = None
        for line in text.split("\n"):
            if line.startswith("■"):
                if curr: items.append(curr)
                curr = {"heading": line.replace("■", "").strip(), "body": []}
            elif curr:
                curr["body"].append(line.strip())
        if curr: items.append(curr)
        
        return [IncidentItem(i["heading"], " ".join(i["body"])) for i in items]
    except Exception:
        return []

def process_incidents(items: List[IncidentItem]) -> List[Dict]:
    """生データを解析して座標とメタデータを付与"""
    results = []
    for item in items:
        full_text = item.heading + " " + item.body
        
        # カテゴリ判定
        cat = "その他"
        for key in AppConfig.CAT_STYLE.keys():
            if key in full_text:
                cat = key
                break
        
        # 簡易ジオコーディング（市町名マッチング）
        muni = "愛媛県"
        lon, lat = AppConfig.EHIME_LON, AppConfig.EHIME_LAT
        
        for city_name, coords in CITY_DATA.items():
            if city_name in full_text:
                muni = city_name
                lon, lat = coords
                # 重なり防止のためごくわずかに座標をずらす（ランダム散らし）
                import random
                lon += random.uniform(-0.01, 0.01)
                lat += random.uniform(-0.01, 0.01)
                break
        
        results.append({
            "category": cat,
            "municipality": muni,
            "summary": item.body[:100] + "..." if len(item.body)>100 else item.body,
            "full_text": full_text,
            "lon": lon,
            "lat": lat,
            "style": AppConfig.CAT_STYLE.get(cat, AppConfig.CAT_STYLE["その他"])
        })
    return results

# ==============================================================================
# [Main] アプリケーション
# ==============================================================================

def main():
    st.set_page_config(page_title="ESP Mobile", layout="wide", page_icon="📱")
    inject_custom_css()

    st.markdown(f"### 📱 {AppConfig.TITLE}")

    # データ取得
    with st.spinner("データ更新中..."):
        raw_data = fetch_ehime_police_data()
        incidents = process_incidents(raw_data)

    # UIレイアウト: スマホ向けにタブで切り替え
    tab1, tab2 = st.tabs(["🗺️ マップ (Map)", "🚨 速報リスト (List)"])

    # --- Tab 1: マップ表示 ---
    with tab1:
        # マップデータ作成
        if incidents:
            df = pd.DataFrame(incidents)
            
            # 各行から色情報を抽出
            df["color"] = df["style"].apply(lambda x: x["color"])
            df["radius"] = df["style"].apply(lambda x: x["radius"] * 10) # スマホで見やすく少し大きく
            df["icon"] = df["style"].apply(lambda x: x["icon"])

            # ツールチップ用HTML
            df["tooltip"] = df.apply(lambda row: f"""
                <div class='map-tooltip'>
                    <b>{row['icon']} {row['category']}</b><br>
                    <span style='color:#ccc'>{row['municipality']}</span><br>
                    {row['summary'][:40]}...
                </div>
            """, axis=1)

            # PyDeckレイヤー設定
            layer = pdk.Layer(
                "ScatterplotLayer",
                data=df,
                get_position="[lon, lat]",
                get_fill_color="color",
                get_radius="radius",
                pickable=True,
                stroked=True,
                filled=True,
                line_width_min_pixels=1,
                get_line_color=[255, 255, 255],
            )

            # ビュー設定
            view_state = pdk.ViewState(
                latitude=AppConfig.EHIME_LAT,
                longitude=AppConfig.EHIME_LON,
                zoom=AppConfig.INIT_ZOOM,
                pitch=0,
            )

            # デッキ描画
            # map_provider=None とし、TileLayerを明示的に追加することで「真っ暗」を回避
            st.pydeck_chart(pdk.Deck(
                layers=[
                    pdk.Layer(
                        "TileLayer",
                        data="https://tile.openstreetmap.org/{z}/{x}/{y}.png",
                        id="base-map",
                        min_zoom=0, max_zoom=19,
                    ),
                    layer
                ],
                initial_view_state=view_state,
                tooltip={"html": "{tooltip}"},
                map_provider=None, # プロバイダ無効化 (TileLayerを使用するため)
            ), use_container_width=True, height=500) # スマホ用に縦幅確保
        else:
            st.warning("現在表示できるデータがありません。")

    # --- Tab 2: リスト表示 ---
    with tab2:
        # 検索機能
        search = st.text_input("🔍 キーワード検索", placeholder="例: 事故, 松山市...")
        
        filtered_incidents = incidents
        if search:
            filtered_incidents = [i for i in incidents if search in i["full_text"]]

        st.caption(f"件数: {len(filtered_incidents)}件")
        
        # HTML生成 (textwrap.dedentを使ってインデントを除去し、コードブロック化を防ぐ)
        html_content = ""
        for item in filtered_incidents:
            icon = item["style"]["icon"]
            # インデントを削除して1つの文字列にする
            card_html = textwrap.dedent(f"""
                <div class='feed-card'>
                    <div class='feed-header'>
                        <div class='feed-tag'>
                            <span>{icon}</span>
                            <span>{item['category']}</span>
                        </div>
                        <div class='feed-loc'>{item['municipality']}</div>
                    </div>
                    <div class='feed-body'>
                        {item['summary']}
                    </div>
                    <div class='feed-footer'>
                        <a href='{AppConfig.POLICE_URL}' target='_blank' style='text-decoration:none;'>詳細を確認 &rarr;</a>
                    </div>
                </div>
            """)
            html_content += card_html

        st.markdown(html_content, unsafe_allow_html=True)

    # 自動更新
    st_autorefresh(interval=10 * 60 * 1000, key="auto_update")

if __name__ == "__main__":
    main()

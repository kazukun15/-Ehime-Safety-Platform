# -*- coding: utf-8 -*-
# 愛媛セーフティ・プラットフォーム / Ehime Safety Platform  v7.2
# - デザイン刷新：シビラ/マギ風のネオフューチャーUI（ダーク/ライト自動対応・ネオングラデ・カード・チップ・ミクロインタラクション）
# - カテゴリ別アイコン層を追加（Icon-like TextLayer）。凡例もアイコン＋色チップで視認性向上
# - 機能は v7.1.1 と同じ：県警スクレイプ→近似座標化→pydeck可視化、H3クラスタ、近似円、フィード、ページング
# - 外依存APIキー不要。地図はGSIタイル（日本語）を使用

import os, re, math, time, json, sqlite3, threading, unicodedata
from dataclasses import dataclass
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor

import httpx
import requests
import pandas as pd
import streamlit as st
import pydeck as pdk
from bs4 import BeautifulSoup
from rapidfuzz import fuzz, process as rf_process
import h3

APP_TITLE = "愛媛セーフティ・プラットフォーム / Ehime Safety Platform"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/7.2 (design/neo)"
TIMEOUT = 12
TTL_HTML = 600
MAX_WORKERS = 6

EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650

CITY_NAMES = ["松山市","今治市","新居浜市","西条市","大洲市","伊予市","四国中央市","西予市","東温市","上島町","久万高原町","松前町","砥部町","内子町","伊方町","松野町","鬼北町","愛南町"]
CATEGORY_PATTERNS = [
    ("交通事故", r"交通.*事故|自転車|バス|二輪|乗用|衝突|交差点|国道|県道|人身事故"),
    ("火災",     r"火災|出火|全焼|半焼|延焼"),
    ("死亡事案", r"死亡|死亡事案"),
    ("窃盗",     r"窃盗|万引|盗"),
    ("詐欺",     r"詐欺|還付金|投資詐欺|特殊詐欺"),
    ("事件",     r"威力業務妨害|条例違反|暴行|傷害|脅迫|器物損壊|青少年保護"),
]
FACILITY_HINT = ["学校","小学校","中学校","高校","大学","グラウンド","体育館","公園","駅","港","病院","交差点"]

# ===== Streamlit 基本設定 =====
st.set_page_config(page_title="Ehime Safety Platform", layout="wide")
st.markdown(
    """
    <style>
      :root{
        --bg: #0b0f14;
        --panel: #0f141b;
        --panel-2: #121924;
        --text: #e6f1ff;
        --muted: #8aa0b6;
        --accent: #00e0ff;
        --accent-2: #7cffd9;
        --chip: #1a2230;
        --chip-border: #2b3a4d;
        --glow: 0 0 20px rgba(0,224,255,.25), 0 0 60px rgba(0,224,255,.10);
      }
      @media (prefers-color-scheme: light){
        :root{
          --bg: #f7fafc;
          --panel: #ffffff;
          --panel-2: #f1f5f9;
          --text: #10212f;
          --muted: #516170;
          --accent: #007aff;
          --accent-2: #00b894;
          --chip: #f6f9fc;
          --chip-border: #dfe7ef;
          --glow: 0 0 0 transparent, 0 0 0 transparent;
        }
      }
      html, body, .stApp { background: var(--bg); color: var(--text); }
      /* タイトルバー */
      .topbar{
        position: sticky; top:0; z-index:10;
        padding: 14px 16px; margin: -16px -16px 14px -16px;
        border-bottom: 1px solid var(--chip-border);
        background: linear-gradient(180deg, rgba(0,224,255,.06), transparent 60%), var(--panel);
        box-shadow: var(--glow);
      }
      .brand{
        display:flex; align-items:center; gap:10px; font-weight:800; 
        letter-spacing:.2px; font-size:1.05rem;
      }
      .brand .id{ 
        width:28px; height:28px; border-radius:8px; 
        display:grid; place-items:center; 
        background: linear-gradient(135deg, var(--accent), var(--accent-2));
        color:#00131a; font-weight:900;
      }
      .subnote{ color: var(--muted); font-size:.85rem; margin-top:4px}
      /* チップボタン（カテゴリトグル） */
      .fab-bar { display:flex; flex-wrap:wrap; gap:8px; padding:8px 0 0 0 }
      .chip{
        border-radius:999px; border:1px solid var(--chip-border); 
        padding:6px 10px; background:var(--chip); color:var(--text);
        box-shadow: 0 2px 8px rgba(0,0,0,.08);
        font-size:.9rem; display:inline-flex; align-items:center; gap:8px; cursor:pointer;
      }
      .chip.active{
        border-color: transparent; 
        background: linear-gradient(135deg, rgba(0,224,255,.20), rgba(124,255,217,.10)), var(--chip);
        box-shadow: var(--glow);
      }
      .chip .ico{ font-weight:900; opacity:.9 }
      /* カードフィード */
      .feed-card{
        background: var(--panel);
        border-radius:14px; border:1px solid var(--chip-border);
        margin-bottom:10px; padding:12px 14px; 
        box-shadow: 0 1px 2px rgba(0,0,0,.12);
      }
      .feed-scroll { max-height:62vh; overflow-y:auto; padding-right:6px }
      .feed-title{ font-weight:700; }
      .feed-meta{ color: var(--muted); font-size:.9rem; margin-top:2px }
      .feed-pred{ margin-top:4px; color: var(--accent-2); font-size:.9rem }
      /* 凡例（地図の下） */
      .legend { 
        font-size:.95rem; background:var(--panel); border:1px solid var(--chip-border); 
        border-radius:12px; padding:10px 12px; box-shadow: 0 1px 2px rgba(0,0,0,.15);
      }
      .legend .item { display:inline-flex; align-items:center; margin-right:14px; margin-bottom:6px}
      .dot { width:12px; height:12px; border-radius:50%; display:inline-block; margin-right:6px; border:1px solid #00000022}
      .legend .ic { margin:0 6px 0 8px; opacity:.9; font-weight:800 }
      /* 入力やサイドバー */
      .stSlider > div, .stTextInput>div>div>input { accent-color: var(--accent) }
      .panel {
        background: var(--panel); border:1px solid var(--chip-border); border-radius: 14px; 
        padding: 10px 12px; box-shadow: 0 1px 2px rgba(0,0,0,.15);
      }
      @media (max-width: 640px){ .feed-scroll{max-height:48vh} }
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(
    f"""
    <div class="topbar">
      <div class="brand">
        <div class="id">ES</div>
        <div>
          <div>{APP_TITLE}</div>
          <div class="subnote">今に強い・先を読む。地図で一目、要点は簡潔。</div>
        </div>
      </div>
    </div>
    """, unsafe_allow_html=True
)

# ===== Sidebar =====
with st.sidebar:
    st.markdown("<div class='panel'>", unsafe_allow_html=True)
    st.markdown("#### 表示期間")
    period = st.select_slider("表示期間を選択", ["当日","過去3日","過去7日","過去30日"], value="過去7日", label_visibility="collapsed")
    period_days = {"当日":1, "過去3日":3, "過去7日":7, "過去30日":30}[period]

    st.markdown("#### 表示密度")
    zoom_like = st.slider("表示密度（粗←→細）", 7, 14, 10)
    fanout_threshold = st.slider("スパイダー展開閾値", 2, 8, 4)
    label_scale = st.slider("ラベル倍率", 0.7, 1.6, 1.0, 0.1)

    st.markdown("#### ガゼッティア")
    gazetteer_path = st.text_input("CSVパス", "data/gazetteer_ehime.csv")
    use_fuzzy = st.checkbox("ゆらぎ対応", True)
    min_fuzzy_score = st.slider("最小スコア", 60, 95, 78)
    st.markdown("</div>", unsafe_allow_html=True)

# ====== SQLite cache ======
@st.cache_resource
def get_sqlite():
    os.makedirs("data", exist_ok=True)
    conn = sqlite3.connect("data/esp_cache.sqlite", check_same_thread=False)
    with conn:
        conn.execute("CREATE TABLE IF NOT EXISTS geocode_cache(key TEXT PRIMARY KEY, lon REAL, lat REAL, type TEXT, created_at TEXT)")
    return conn
conn = get_sqlite(); conn_lock = threading.Lock()

def geocode_cache_get(key:str):
    with conn_lock:
        r = conn.execute("SELECT lon,lat,type FROM geocode_cache WHERE key=?", (key,)).fetchone()
    if r: return float(r[0]), float(r[1]), str(r[2])
    return None

def geocode_cache_put(key:str, lon:float, lat:float, typ:str):
    with conn_lock, conn:
        conn.execute("INSERT OR REPLACE INTO geocode_cache VALUES (?,?,?,?,datetime('now'))", (key, lon, lat, typ))

# ===== Helpers =====
def _norm(s: str) -> str:
    s = unicodedata.normalize('NFKC', s or '').strip()
    s = re.sub(r"\s+", " ", s)
    return s

@dataclass
class IncidentItem:
    heading: str
    body: str
    incident_date: Optional[str]

# ===== Fetch & Parse =====
@st.cache_data(ttl=TTL_HTML)
def fetch_ehime_html() -> str:
    headers = {"User-Agent": USER_AGENT}
    last_err = None
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
        except Exception as e:
            last_err = e
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
            except: d = None
        out.append(IncidentItem(h.replace("■", "").strip(), body, d))
    return out

# ===== NLP（軽量ルール） =====
def rule_extract(it: IncidentItem) -> Dict:
    t = it.heading + " " + it.body
    cat = "その他"
    for name, pat in CATEGORY_PATTERNS:
        if re.search(pat, t): cat = name; break
    muni = None
    for c in CITY_NAMES:
        if c in t: muni = c; break
    places = []
    for hint in FACILITY_HINT:
        places += re.findall(rf"([\w\u3040-\u30ff\u4e00-\u9fffA-Za-z0-9]+{hint})", t)[:2]
    s = re.sub(r"\s+", " ", it.body).strip()
    s = s[:120] + ("…" if len(s)>120 else "")
    return {"category":cat,"municipality":muni,"place_strings":list(dict.fromkeys(places))[:3],
            "summary": s or it.heading, "date": it.incident_date}

# ===== Gazetteer =====
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

# ===== Nominatim =====
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
                return float(arr[0]["lon"]), float(arr[0]["lat"])
        return None
    except Exception:
        return None

# ===== H3/Cluster =====
def h3_cell_from_latlng(lat: float, lon: float, res: int) -> str:
    if hasattr(h3, "geo_to_h3"): return h3.geo_to_h3(lat, lon, res)  # v3
    return h3.latlng_to_cell(lat, lon, res)  # v4

def h3_latlng_from_cell(cell: str) -> Tuple[float,float]:
    if hasattr(h3, "h3_to_geo"): lat, lon = h3.h3_to_geo(cell); return lat, lon  # v3
    lat, lon = h3.cell_to_latlng(cell); return lat, lon  # v4

def h3_res_from_zoom(zoom_val:int) -> int:
    return {7:5,8:6,9:7,10:8,11:9,12:9,13:10,14:10}.get(zoom_val, 8)

def cluster_points(df: pd.DataFrame, zoom_val:int) -> List[Dict]:
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

# ===== Text helpers / Prediction =====
def short_summary(s: str, max_len: int = 64) -> str:
    s = re.sub(r"\s+", " ", s or "").strip()
    return (s[:max_len] + ("…" if len(s) > max_len else "")) if s else ""

def make_prediction(category:str, muni:Optional[str]) -> str:
    if category == "詐欺":       return "SNSや投資の誘いに注意。送金前に家族や警察へ相談。"
    if category == "交通事故":   return "夕方や雨天の交差点で増えやすい。横断と右左折に注意。"
    if category == "窃盗":       return "自転車・車両の施錠と防犯登録。夜間の無施錠放置を避ける。"
    if category == "火災":       return "乾燥時は屋外火気に配慮。電源周り・喫煙の始末を再確認。"
    if category == "事件":       return "不審連絡は記録を残し通報。学校・公共施設周辺で意識を。"
    if category == "死亡事案":   return "詳細は出典で確認。周辺では救急活動に配慮。"
    return "同種事案が続く可能性。出典で最新を確認。"

# ===== Pipeline =====
with st.spinner("速報を取得中…"):
    html = fetch_ehime_html()
raw_items = parse_items(html)

extracted: List[Dict] = []
for it in raw_items:
    ex = rule_extract(it)
    ex["heading"] = it.heading
    extracted.append(ex)

gdf = load_gazetteer(gazetteer_path)
idx = GazetteerIndex(gdf) if gdf is not None else None

def resolve_one(ex: Dict) -> Dict:
    muni = ex.get("municipality"); places = ex.get("place_strings") or []
    if idx is not None:
        for ptxt in places:
            hit = idx.search(ptxt, min_fuzzy_score if use_fuzzy else 101)
            if hit: lon, lat, typ = hit; return {"lon":lon, "lat":lat, "type":typ}
        if muni:
            hit = idx.search(muni, min_fuzzy_score if use_fuzzy else 101)
            if hit: lon, lat, typ = hit; return {"lon":lon, "lat":lat, "type":typ}
    if muni:
        for ptxt in places:
            ll = nominatim_geocode(ptxt, muni)
            if ll: return {"lon":ll[0], "lat":ll[1], "type":"facility"}
        ll = nominatim_geocode(muni, None)
        if ll: return {"lon":ll[0], "lat":ll[1], "type":"city"}
    return {"lon":EHIME_PREF_LON, "lat":EHIME_PREF_LAT, "type":"pref"}

with ThreadPoolExecutor(max_workers=MAX_WORKERS) as exctr:
    results = list(exctr.map(resolve_one, extracted))

rows: List[Dict] = []
for ex, loc in zip(extracted, results):
    typ = loc.get("type","city")
    radius = {"facility":300,"intersection":250,"town":600,"chome":600,"oaza":900,"aza":900,"city":2000}.get(typ, 1200)
    rows.append({
        "lon": float(loc["lon"]), "lat": float(loc["lat"]),
        "category": ex["category"],
        "summary": short_summary(ex["summary"], 60),
        "municipality": ex.get("municipality") or "",
        "radius_m": int(radius),
        "pred": make_prediction(ex["category"], ex.get("municipality")),
        "src": EHIME_POLICE_URL,
    })

df = pd.DataFrame(rows)

# ===== カテゴリ色・アイコン（Unicode簡易。IconLayer相当を TextLayerで実現） =====
CAT_STYLE = {
    "交通事故": {"color":[255, 99, 99, 230],  "radius":86, "icon":"▲"},   # alert-red
    "火災":     {"color":[255, 140, 66, 230], "radius":88, "icon":"🔥"},  # orange-fire
    "死亡事案": {"color":[197, 128, 255, 230],"radius":92, "icon":"✖"},   # purple
    "窃盗":     {"color":[98, 165, 255, 230], "radius":78, "icon":"🔓"},  # blue
    "詐欺":     {"color":[70, 205, 180, 230], "radius":78, "icon":"⚠"},   # teal-yellow
    "事件":     {"color":[255, 210, 64, 230], "radius":82, "icon":"！"},   # amber
    "その他":   {"color":[130, 150, 166, 210], "radius":70, "icon":"・"},  # gray
}

# ===== トグル（チップUI） =====
active = st.session_state.get("active_cats") or {k: True for k in CAT_STYLE}
chips = ["<div class='fab-bar'>"]
for k, v in CAT_STYLE.items():
    on = active.get(k, True)
    cls = "chip active" if on else "chip"
    ico = v["icon"]
    chips.append(
        f"<button class='{cls}' onclick=\\\"window.parent.postMessage({{{{'type':'toggle','cat':'{k}'}}}},'*')\\\">"
        f"<span class='ico'>{ico}</span>{k}</button>"
    )
chips.append("</div>")
st.markdown("".join(chips), unsafe_allow_html=True)

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
for k in list(CAT_STYLE.keys()):
    kk = "cat_"+k
    if kk in qs: active[k] = (qs[kk] != "0")
st.session_state["active_cats"] = active

vis_df = df[df["category"].apply(lambda c: active.get(str(c), True))]

# ===== H3クラスタ =====
centers = []
if not vis_df.empty:
    def h3_res_from_zoom(zoom_val:int) -> int:
        return {7:5,8:6,9:7,10:8,11:9,12:9,13:10,14:10}.get(zoom_val, 8)
    def cluster_points(df: pd.DataFrame, zoom_val:int) -> List[Dict]:
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
    centers = cluster_points(vis_df, 10)

# ===== レイヤ構築（Scatter + Text 2種：縦ラベル + アイコン） =====
hex_points = [{"position":[c["lon"],c["lat"]],"count":c["count"]} for c in centers]
points: List[Dict] = []
icon_labels: List[Dict] = []
mini_labels_fg: List[Dict] = []
mini_labels_bg: List[Dict] = []
polys: List[Dict] = []

def spiderfy(clon: float, clat: float, n: int, base_px: int = 16, gap_px: int = 8):
    out = []; rpx = base_px
    for k in range(n):
        ang = math.radians(137.5 * k)
        dx = rpx*math.cos(ang); dy = rpx*math.sin(ang)
        dlon = dx / (111320 * math.cos(math.radians(clat))); dlat = dy / 110540
        out.append((clon + dlon, clat + dlat)); rpx += gap_px
    return out

MAX_LABELS = 400
for c in centers:
    cnt = c["count"]; clat, clon = c["lat"], c["lon"]
    if cnt <= 4:
        offs = spiderfy(clon, clat, cnt, base_px=16, gap_px=8)
        for (lon, lat), row in zip(offs, c["rows"]):
            sty = CAT_STYLE.get(row["category"], CAT_STYLE["その他"])
            points.append({
                "position":[lon,lat], "color":sty["color"], "radius":sty["radius"],
                "c":row["category"], "s":row["summary"], "m":row.get("municipality",""),
                "pred": row.get("pred",""), "src": row.get("src", EHIME_POLICE_URL),
                "r": int(row.get("radius_m", 600)),
                "ico": sty["icon"],
            })
            # アイコン（重ならないよう少し上に）
            icon_labels.append({"position":[lon,lat], "label":sty["icon"], "tcolor":[255,255,255,240], "offset":[0,-2]})
            # スモール縦ラベル（4文字を縦並び）
            if len(mini_labels_fg) < MAX_LABELS:
                vtxt = (row["summary"] or "")[:4]
                vtxt = "\n".join(list(vtxt))
                offset_px = int(-14*label_scale)
                mini_labels_bg.append({"position":[lon,lat],"label":vtxt,"tcolor":[0,0,0,220],"offset":[0,offset_px]})
                mini_labels_fg.append({"position":[lon,lat],"label":vtxt,"tcolor":[255,255,255,235],"offset":[0,offset_px]})
            polys.append({"lon":lon,"lat":lat,"r":int(row.get("radius_m",600))})
    else:
        points.append({"position":[clon,clat],"color":[90,90,90,200],"radius":70,"c":f"{cnt}件","s":"周辺に多数","m":"","pred":"","src":EHIME_POLICE_URL,"r":0,"ico":"◎"})
        icon_labels.append({"position":[clon,clat], "label":"◎", "tcolor":[255,255,255,230], "offset":[0,-2]})
        if len(mini_labels_fg) < MAX_LABELS:
            mini_labels_bg.append({"position":[clon,clat],"label":str(cnt),"tcolor":[0,0,0,220],"offset":[0,-12]})
            mini_labels_fg.append({"position":[clon,clat],"label":str(cnt),"tcolor":[255,255,255,235],"offset":[0,-12]})

# 近似円
def circle_coords(lon: float, lat: float, radius_m: int = 300, n: int = 64):
    coords = []
    r_earth = 6378137.0
    dlat = radius_m / r_earth
    dlon = radius_m / (r_earth * math.cos(math.radians(lat)))
    for i in range(n):
        ang = 2 * math.pi * i / n
        lat_i = lat + math.degrees(dlat * math.sin(ang))
        lon_i = lon + math.degrees(dlon * math.cos(math.radians(lat)))
        coords.append([lon_i, lat_i])
    coords.append(coords[0]); return coords

geo_features = []
for p in points:
    if p.get("r",0) > 0:
        geo_features.append({"type":"Feature","geometry":{"type":"Polygon","coordinates":[circle_coords(p["position"][0], p["position"][1], int(p["r"]))]},"properties":{}})
geojson = {"type":"FeatureCollection","features": geo_features}

# ===== レイアウト =====
col_map, col_feed = st.columns([7,5], gap="large")

with col_map:
    TILES = {
        "GSI 淡色": {"url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom": 18},
        "GSI 標準": {"url": "https://cyberjapandata.gsi.go.jp/xyz/std/{z}/{x}/{y}.png", "max_zoom": 18},
    }
    TILE = TILES["GSI 淡色"]
    layers = [
        pdk.Layer("TileLayer", data=TILE["url"], min_zoom=0, max_zoom=TILE.get("max_zoom",18), tile_size=256, opacity=1.0),
        pdk.Layer("HexagonLayer", data=[{"position":x["position"],"count":x["count"]} for x in hex_points],
                  get_position="position", get_elevation_weight="count", elevation_scale=5, elevation_range=[0,800],
                  extruded=False, radius=500, coverage=0.9, opacity=0.22, pickable=False),
        pdk.Layer("GeoJsonLayer", data=geojson, pickable=False, stroked=True, filled=True,
                  get_line_width=2, get_line_color=[0,224,255], get_fill_color=[0,224,255,40], auto_highlight=False),
        pdk.Layer("ScatterplotLayer", data=points, get_position="position", get_fill_color="color", get_radius="radius",
                  pickable=True, radius_min_pixels=3, radius_max_pixels=60),
        # アイコン（文字）レイヤ
        pdk.Layer("TextLayer", data=icon_labels, get_position="position", get_text="label", get_color="tcolor",
                  get_size=14, get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        # 縦ラベル（背景→前景）
        pdk.Layer("TextLayer", data=mini_labels_bg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*label_scale), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        pdk.Layer("TextLayer", data=mini_labels_fg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*label_scale), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
    ]

    tooltip = {
        "html": "<b>{c}</b><br/>{s}<br/>{m}<br/>予測: {pred}<br/><a href='{src}' target='_blank'>出典</a>",
        "style": {"backgroundColor":"rgba(10,15,20,.96)","color":"#e6f1ff","maxWidth":"280px","whiteSpace":"normal",
                  "wordBreak":"break-word","lineHeight":1.4,"fontSize":"12px","padding":"10px 12px",
                  "borderRadius":"12px","border":"1px solid #2b3a4d","boxShadow":"0 8px 32px rgba(0,224,255,.15)"}
    }

    deck = pdk.Deck(
        layers=layers,
        initial_view_state=pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9),
        tooltip=tooltip, map_provider=None, map_style=None
    )
    st.pydeck_chart(deck, use_container_width=True, height=540)

    # 凡例（アイコン＋色ドット）
    legend_items = []
    for k, v in CAT_STYLE.items():
        rgba = f"rgba({v['color'][0]}, {v['color'][1]}, {v['color'][2]}, {v['color'][3]/255:.9f})"
        legend_items.append(f"<span class='item'><span class='ic'>{v['icon']}</span><span class='dot' style='background:{rgba}'></span>{k}</span>")
    st.markdown(f"<div class='legend'>{''.join(legend_items)}<div style='margin-top:6px;color:var(--muted);font-size:.85rem'>円は概ねの範囲。詳細は出典を確認。</div></div>", unsafe_allow_html=True)

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
        cat = r.get('category',''); icon = CAT_STYLE.get(cat, CAT_STYLE["その他"])["icon"]
        html_list.append("<div class='feed-card'>")
        html_list.append(f"<div class='feed-title'>{icon} {cat}</div>")
        html_list.append(f"<div>{r.get('summary','')}</div>")
        muni = r.get('municipality') or ''
        if muni: html_list.append(f"<div class='feed-meta'>{muni}</div>")
        html_list.append(f"<div class='feed-pred'>予測: {r.get('pred','')}</div>")
        html_list.append(f"<div class='feed-meta'><a href='{r.get('src')}' target='_blank'>出典</a></div>")
        html_list.append("</div>")
    html_list.append("</div>")
    st.markdown("\n".join(html_list), unsafe_allow_html=True)
    st.markdown("</div>", unsafe_allow_html=True)

st.caption("地図: 国土地理院 / 情報: 県警速報。緊急時は110・119へ。")

# -*- coding: utf-8 -*-
# 愛媛セーフティ・プラットフォーム / Ehime Safety Platform  v8.0
# - 追加: Gemini 2.5 Flash による事案テキスト→地名候補抽出（無料タイル/キー無しでも動作、キーがあれば精度向上）
# - 強化: ガゼッティア（外部CSV + 内蔵市町中心）を用いたジオコーディングの堅牢化
# - 踏襲: 無料地図選択（GSI/OSM/HOT/OpenTopo）・2D/3D 切替・将来バッファ拡大・クラスタ/凡例/フィード

import os, re, math, time, json, sqlite3, threading, unicodedata, hashlib
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

# === Gemini (任意) ===
try:
    import google.generativeai as genai  # requirements: google-generativeai
    _HAS_GEMINI = True
except Exception:
    _HAS_GEMINI = False

APP_TITLE = "愛媛セーフティ・プラットフォーム"
EHIME_POLICE_URL = "https://www.police.pref.ehime.jp/sokuho/sokuho.htm"
USER_AGENT = "ESP/8.0 (gemini+gazetteer)"
TIMEOUT = 12
TTL_HTML = 600
MAX_WORKERS = 6

EHIME_PREF_LAT = 33.8390
EHIME_PREF_LON = 132.7650

# 将来影響を考慮した概位置バッファ倍率
FUTURE_BUFFER_SCALE = 1.8

# 内部既定
ZOOM_LIKE = 10
FANOUT_THRESHOLD = 4
LABEL_SCALE = 1.0
MAX_LABELS = 400

CITY_NAMES = [
    "松山市","今治市","新居浜市","西条市","大洲市","伊予市","四国中央市",
    "西予市","東温市","上島町","久万高原町","松前町","砥部町","内子町",
    "伊方町","松野町","鬼北町","愛南町","宇和島市","八幡浜市"
]

# 内蔵市町中心（確実に市町へ落とす）
MUNI_CENTERS = {
    "松山市":(132.7650,33.8390),"今治市":(133.0000,34.0660),"新居浜市":(133.2830,33.9600),
    "西条市":(133.1830,33.9180),"大洲市":(132.5500,33.5000),"伊予市":(132.7010,33.7550),
    "四国中央市":(133.5500,33.9800),"西予市":(132.5000,33.3660),"東温市":(132.8710,33.7930),
    "上島町":(133.2000,34.2600),"久万高原町":(132.9040,33.5380),"松前町":(132.7110,33.7870),
    "砥部町":(132.7870,33.7350),"内子町":(132.6580,33.5360),"伊方町":(132.3560,33.4880),
    "松野町":(132.7570,33.2260),"鬼北町":(132.8800,33.2280),"愛南町":(132.5660,33.0000),
    "宇和島市":(132.5600,33.2230),"八幡浜市":(132.4230,33.4620),
}

CATEGORY_PATTERNS = [
    ("交通事故", r"交通.*事故|自転車|バス|二輪|乗用|衝突|交差点|国道|県道|人身事故"),
    ("火災",     r"火災|出火|全焼|半焼|延焼"),
    ("死亡事案", r"死亡|死亡事案"),
    ("窃盗",     r"窃盗|万引|盗"),
    ("詐欺",     r"詐欺|還付金|投資詐欺|特殊詐欺"),
    ("事件",     r"威力業務妨害|条例違反|暴行|傷害|脅迫|器物損壊|青少年保護"),
]

# ===== UIテーマ =====
st.set_page_config(page_title="Ehime Safety Platform", layout="wide")
st.markdown(
    """
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
          <div class="subnote">今を知り・危険の先を読む危険確認プラットフォーム</div>
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

    st.markdown("#### 地図タイル")
    map_choice = st.selectbox(
        "地図スタイル",
        ["GSI 淡色","GSI 標準","OpenStreetMap Standard","OSM Humanitarian","OpenTopoMap"],
        index=0
    )

    st.markdown("#### 表示モード")
    mode_3d = st.radio("2D / 3D", ["2D","3D"], horizontal=True, index=0)
    st.markdown("</div>", unsafe_allow_html=True)

# ===== SQLite cache =====
@st.cache_resource
def get_sqlite():
    os.makedirs("data", exist_ok=True)
    conn = sqlite3.connect("data/esp_cache.sqlite", check_same_thread=False)
    with conn:
        conn.execute("CREATE TABLE IF NOT EXISTS geocode_cache(key TEXT PRIMARY KEY, lon REAL, lat REAL, type TEXT, created_at TEXT)")
        conn.execute("CREATE TABLE IF NOT EXISTS llm_cache(key TEXT PRIMARY KEY, json TEXT, created_at TEXT)")
    return conn
conn = get_sqlite(); conn_lock = threading.Lock()

def cache_get(table:str, key:str) -> Optional[str]:
    with conn_lock:
        row = conn.execute(f"SELECT json FROM {table} WHERE key=?", (key,)).fetchone()
    return row[0] if row else None

def cache_put(table:str, key:str, payload:str):
    with conn_lock, conn:
        conn.execute(f"INSERT OR REPLACE INTO {table} VALUES (?,?,datetime('now'))", (key, payload))

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
            except: d = None
        out.append(IncidentItem(h.replace("■", "").strip(), body, d))
    return out

# ===== 軽量ルール抽出 =====
def rule_extract(it: IncidentItem) -> Dict:
    t = it.heading + " " + it.body
    cat = "その他"
    for name, pat in CATEGORY_PATTERNS:
        if re.search(pat, t): cat = name; break
    muni = None
    for c in CITY_NAMES:
        if c in t: muni = c; break
    places = []
    for hint in ["小学校","中学校","高校","大学","学校","グラウンド","体育館","公園","駅","港","病院","交差点"]:
        places += re.findall(rf"([\w\u3040-\u30ff\u4e00-\u9fffA-Za-z0-9]+{hint})", t)[:2]
    s = re.sub(r"\s+", " ", it.body).strip()
    s = s[:120] + ("…" if len(s)>120 else "")
    return {"category":cat,"municipality":muni,"place_strings":list(dict.fromkeys(places))[:3],
            "summary": s or it.heading, "date": it.incident_date}

# ===== Gazetteer（外部CSVは任意） =====
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

# ===== Gemini 解析（任意、APIキーがあれば使用） =====
def gemini_candidates(full_text: str, muni_hint: Optional[str]) -> List[Dict]:
    api_key = os.getenv("GEMINI_API_KEY", "")
    if not (_HAS_GEMINI and api_key):
        return []
    # キャッシュ
    key_src = f"gem8|{muni_hint or ''}|{full_text}"
    key = hashlib.sha1(key_src.encode("utf-8")).hexdigest()
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
            "入力の事件・事故テキストから、地名や施設名候補を高精度で抽出します。"
            "出力は次のJSONのみ: {\"candidates\":[{\"name\":str,\"kind\":str,\"confidence\":0..1}]}"
            "kindは facility/street/intersection/town/city/unknown のいずれか。"
            "文章内の固有の地物に限定し、あいまいなら市町でよい。最大5件まで。"
        )
        muni_line = f"市町ヒント: {muni_hint}\n" if muni_hint else ""
        prompt = (
            f"{system}\n\nテキスト:\n{full_text}\n\n{muni_line}"
            "JSONのみで応答してください。追加説明は不要です。"
        )
        resp = model.generate_content(prompt)
        txt = resp.text if hasattr(resp, "text") else str(resp)
        # JSON抽出
        start = txt.find("{"); end = txt.rfind("}")
        if start >=0 and end>start:
            txt = txt[start:end+1]
        obj = json.loads(txt)
        if isinstance(obj, dict):
            cache_put("llm_cache", key, json.dumps(obj, ensure_ascii=False))
            return obj.get("candidates", [])
    except Exception:
        return []
    return []

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

# ===== 表示テキスト =====
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

# ===== パイプライン =====
with st.spinner("速報を取得中…"):
    html = fetch_ehime_html()
raw_items = parse_items(html)

extracted: List[Dict] = []
for it in raw_items:
    ex = rule_extract(it)
    ex["heading"] = it.heading
    ex["full_text"] = (it.heading + " " + it.body).strip()
    extracted.append(ex)

# 外部ガゼッティア（任意）
gdf = load_gazetteer("data/gazetteer_ehime.csv")
idx = GazetteerIndex(gdf) if gdf is not None else None

# ---- 座標決定順序（Gemini + ガゼッティア + 内蔵 + Nominatim + 県庁） ----
# 1) Geminiが提案する候補（施設/交差点/町名）
# 2) 外部ガゼッティア（候補名→一致/ファジー）
# 3) 内蔵市町中心
# 4) Nominatim（施設→市町）
# 5) 県庁

def try_gazetteer(name:str, min_score:int=78) -> Optional[Tuple[float,float,str]]:
    if not idx: return None
    hit = idx.search(name, min_score)
    return hit

def resolve_one(ex: Dict) -> Dict:
    muni = ex.get("municipality"); places = ex.get("place_strings") or []
    full_text = ex.get("full_text", "")

    # 1) Gemini 候補抽出
    llm_cands = gemini_candidates(full_text, muni)
    cand_names = [c.get("name","") for c in llm_cands if isinstance(c, dict)]

    # 優先順: Gemini候補 → ルール抽出のplace_strings → 市町
    queries = [q for q in cand_names if q] + places + ([muni] if muni else [])

    # 2) 外部ガゼッティア
    for q in queries:
        hit = try_gazetteer(q, 78)
        if hit:
            lon, lat, typ = hit
            return {"lon":lon, "lat":lat, "type":typ or "facility"}

    # 3) 内蔵市町中心
    if muni and muni in MUNI_CENTERS:
        lon, lat = MUNI_CENTERS[muni]
        return {"lon":lon, "lat":lat, "type":"city"}

    # 4) Nominatim
    for q in queries:
        ll = nominatim_geocode(q, muni)
        if ll:
            return {"lon":ll[0], "lat":ll[1], "type":"facility"}

    # 5) 県庁
    return {"lon":EHIME_PREF_LON, "lat":EHIME_PREF_LAT, "type":"pref"}

with ThreadPoolExecutor(max_workers=MAX_WORKERS) as exctr:
    results = list(exctr.map(resolve_one, extracted))

rows: List[Dict] = []
for ex, loc in zip(extracted, results):
    typ = loc.get("type","city")
    base_radius = {"facility":300,"intersection":250,"town":600,"chome":600,"oaza":900,"aza":900,"city":2000,"pref":2500}.get(typ, 1200)
    radius = int(base_radius * FUTURE_BUFFER_SCALE)
    rows.append({
        "lon": float(loc["lon"]), "lat": float(loc["lat"]),
        "category": ex["category"],
        "summary": short_summary(ex["summary"], 60),
        "municipality": ex.get("municipality") or "",
        "radius_m": radius,
        "pred": make_prediction(ex["category"], ex.get("municipality")),
        "src": EHIME_POLICE_URL,
    })

df = pd.DataFrame(rows)

# ===== カテゴリ色（ライト/ダーク両対応） =====
CAT_STYLE = {
    "交通事故": {"color":[220, 60, 60, 235],   "radius":86, "icon":"▲"},
    "火災":     {"color":[245, 130, 50, 235],  "radius":88, "icon":"🔥"},
    "死亡事案": {"color":[170, 120, 240, 235], "radius":92, "icon":"✖"},
    "窃盗":     {"color":[70, 150, 245, 235],  "radius":78, "icon":"🔓"},
    "詐欺":     {"color":[40, 180, 160, 235],  "radius":78, "icon":"⚠"},
    "事件":     {"color":[245, 200, 60, 235],  "radius":82, "icon":"！"},
    "その他":   {"color":[128, 144, 160, 220], "radius":70, "icon":"・"},
}

# ===== 可視データ・クラスタ =====
vis_df = df
centers = cluster_points(vis_df, ZOOM_LIKE) if not vis_df.empty else []

# ===== レイヤデータ作成 =====
def spiderfy(clon: float, clat: float, n: int, base_px: int = 16, gap_px: int = 8):
    out = []; rpx = base_px
    for k in range(n):
        ang = math.radians(137.5 * k)
        dx = rpx*math.cos(ang); dy = rpx*math.sin(ang)
        dlon = dx / (111320 * math.cos(math.radians(clat))); dlat = dy / 110540
        out.append((clon + dlon, clat + dlat)); rpx += gap_px
    return out

hex_points = [{"position":[c["lon"],c["lat"]],"count":c["count"]} for c in centers]
points: List[Dict] = []
icon_labels: List[Dict] = []
mini_labels_fg: List[Dict] = []
mini_labels_bg: List[Dict] = []
polys: List[Dict] = []

for c in centers:
    cnt = c["count"]; clat, clon = c["lat"], c["lon"]
    if cnt <= FANOUT_THRESHOLD:
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
            icon_labels.append({"position":[lon,lat], "label":sty["icon"], "tcolor":[255,255,255,235], "offset":[0,-2]})
            if len(mini_labels_fg) < MAX_LABELS:
                vtxt = (row["summary"] or "")[:4]; vtxt = "\n".join(list(vtxt))
                offset_px = int(-14*LABEL_SCALE)
                mini_labels_bg.append({"position":[lon,lat],"label":vtxt,"tcolor":[0,0,0,220],"offset":[0,offset_px]})
                mini_labels_fg.append({"position":[lon,lat],"label":vtxt,"tcolor":[255,255,255,235],"offset":[0,offset_px]})
            polys.append({"lon":lon,"lat":lat,"r":int(row.get("radius_m",600))})
    else:
        points.append({"position":[clon,clat],"color":[100,100,100,210],"radius":70,"c":f"{cnt}件","s":"周辺に多数","m":"","pred":"","src":EHIME_POLICE_URL,"r":0,"ico":"◎"})
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
    TILESETS = {
        "GSI 淡色": {"url": "https://cyberjapandata.gsi.go.jp/xyz/pale/{z}/{x}/{y}.png", "max_zoom": 18},
        "GSI 標準": {"url": "https://cyberjapandata.gsi.go.jp/xyz/std/{z}/{x}/{y}.png", "max_zoom": 18},
        "OpenStreetMap Standard": {"url": "https://tile.openstreetmap.org/{z}/{x}/{y}.png", "max_zoom": 19},
        "OSM Humanitarian": {"url": "https://tile-a.openstreetmap.fr/hot/{z}/{x}/{y}.png", "max_zoom": 19},
        "OpenTopoMap": {"url": "https://a.tile.opentopomap.org/{z}/{x}/{y}.png", "max_zoom": 17},
    }
    TILE = TILESETS.get(map_choice, TILESETS["GSI 淡色"])

    is_3d = (mode_3d == "3D")
    hex_layer = pdk.Layer(
        "HexagonLayer",
        data=[{"position":x["position"],"count":x["count"]} for x in hex_points],
        get_position="position",
        get_elevation_weight="count",
        elevation_scale=10 if is_3d else 5,
        elevation_range=[0,1200 if is_3d else 800],
        extruded=is_3d,
        radius=500,
        coverage=0.9,
        opacity=0.25 if is_3d else 0.22,
        pickable=False
    )

    layers = [
        pdk.Layer("TileLayer", data=TILE["url"], min_zoom=0, max_zoom=TILE.get("max_zoom",18), tile_size=256, opacity=1.0),
        hex_layer,
        pdk.Layer("GeoJsonLayer", data=geojson, pickable=False, stroked=True, filled=True,
                  get_line_width=2, get_line_color=[0,160,220], get_fill_color=[0,160,220,40], auto_highlight=False),
        pdk.Layer("ScatterplotLayer", data=points, get_position="position", get_fill_color="color", get_radius="radius",
                  pickable=True, radius_min_pixels=3, radius_max_pixels=60),
        pdk.Layer("TextLayer", data=icon_labels, get_position="position", get_text="label", get_color="tcolor",
                  get_size=14, get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        pdk.Layer("TextLayer", data=mini_labels_bg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*LABEL_SCALE), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
        pdk.Layer("TextLayer", data=mini_labels_fg, get_position="position", get_text="label", get_color="tcolor",
                  get_size=int(12*LABEL_SCALE), get_pixel_offset="offset", get_alignment_baseline="bottom", get_text_anchor="middle"),
    ]

    tooltip = {
        "html": "<b>{c}</b><br/>{s}<br/>{m}<br/>予測: {pred}<br/><a href='{src}' target='_blank'>出典</a>",
        "style": {"backgroundColor":"rgba(10,15,20,.96)","color":"#e6f1ff","maxWidth":"280px","whiteSpace":"normal",
                  "wordBreak":"break-word","lineHeight":1.4,"fontSize":"12px","padding":"10px 12px",
                  "borderRadius":"12px","border":"1px solid var(--border)"}
    }

    initial_view = pdk.ViewState(latitude=EHIME_PREF_LAT, longitude=EHIME_PREF_LON, zoom=9, pitch=(45 if is_3d else 0), bearing=0)
    deck = pdk.Deck(layers=layers, initial_view_state=initial_view, tooltip=tooltip, map_provider=None, map_style=None)
    st.pydeck_chart(deck, use_container_width=True, height=560)

    legend_items = []
    for k, v in CAT_STYLE.items():
        rgba = f"rgba({v['color'][0]}, {v['color'][1]}, {v['color'][2]}, {v['color'][3]/255:.9f})"
        legend_items.append(f"<span class='item'><span class='dot' style='background:{rgba}'></span>{k}</span>")
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

st.caption("地図: GSI / OSM / OpenTopoMap（APIキー不要） | 情報: 県警速報。緊急時は110・119へ。")

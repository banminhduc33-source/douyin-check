#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
[v28 - thêm --sort time|likes|both: xếp hạng theo giờ đăng mới nhất và/hoặc số tim; bảng HTML/CSV thêm cột Hạng giờ, Tim, Hạng tim]
[v27 - thêm --workers (chạy song song, --time-only mặc định 2 luồng), --min-time (mỗi tài khoản tối thiểu 5 giây) và --time-only (chỉ lấy giờ đăng + tên tác giả, xếp theo giờ đăng mới nhất)]
[v26 - tối ưu tốc độ: chặn tài nguyên bằng CDP, upload Drive thưa, lưu tiến độ thưa, goto "commit", thêm --turbo]
douyin_last_post.py - Kiểm tra video MỚI NHẤT của từng tài khoản Douyin được đăng từ bao giờ
(+ like/share/lưu và xếp hạng video xu hướng). LUÔN chạy ở chế độ tiết kiệm RAM cho máy 4GB:
chỉ giữ 1 tab nặng, khởi động lại trình duyệt mỗi 12 tài khoản, mỗi tài khoản chỉ mở 1 trang video.

Cài đặt (một lần):  pip install playwright   &&   playwright install chromium

Chạy:
  python douyin_last_post.py link_unique.txt --limit 5     # thử 5 tài khoản
  python douyin_last_post.py link_unique.txt               # chạy toàn bộ
  python douyin_last_post.py link_unique.txt --card-only --no-name-lookup   # nhẹ nhất
  python douyin_last_post.py link_unique.txt --time-only   # (v27) chỉ giờ đăng + tên, xếp mới nhất lên đầu

Kết quả: 1 file doyin/ketqua_douyin_<giờ chạy>.html, mỗi tài khoản một dòng "tên - hạng N - đăng <giờ đăng> (<cách đây>)" (hạng xu hướng, 1 = nhất).
Ctrl+C vẫn giữ kết quả đã làm. Phiên đăng nhập lưu ở douyin_profile/.
Nếu Douyin hiện captcha: chương trình DỪNG hẳn, giải trong cửa sổ trình duyệt là tự chạy tiếp (hoặc nhấn Enter ở terminal). Không thấy ảnh captcha thì chạy lại với --load-all.

Đầu vào: link tìm kiếm https://www.douyin.com/search/<từ khóa>?type=user, link trang cá nhân
https://www.douyin.com/user/<sec_uid> (chính xác nhất), link chia sẻ m.douyin.com/share/user/<sec_uid>,
hoặc mỗi dòng một từ khóa (.txt / .md).
"""
from __future__ import annotations

import argparse
import email.utils
import copy
import gc
import json
import queue
import random
import re
import shutil
import statistics
import sys
import threading
import time
import unicodedata
from dataclasses import asdict, dataclass, fields
from dataclasses import field as dc_field
from datetime import datetime
from pathlib import Path
from urllib.parse import quote, unquote, urlparse

try:
    from playwright.sync_api import sync_playwright
except ImportError:  # vẫn import được module để test các hàm thuần
    sync_playwright = None

BASE = "https://www.douyin.com"
SEARCH_TIMEOUT = 20    # giây tối đa chờ kết quả tìm kiếm
PROFILE_TIMEOUT = 30   # giây tối đa chờ danh sách bài đăng (trang cá nhân www)
MOBILE_TIMEOUT = 15    # (v24) trang di động: thường trả trong 1-3 giây, quá 15 giây là hỏng -> khỏi chờ 30 giây
STATS_TIMEOUT = 8      # (v24) trang video lấy share/lưu (trước đây 12 giây)

ST_OK = "OK"
ST_NO_VIDEO = "Chưa có video"
ST_PRIVATE = "Riêng tư"
ST_GONE = "Không truy cập được"
ST_NOT_FOUND = "Không tìm thấy"
ST_ERROR = "Lỗi"

PRIVATE_HINTS = ("私密账号", "账号为私密")
GONE_HINTS = ("账号已注销", "已被封禁", "账号已封禁", "账号不存在", "用户不存在")


# ============================================================================
# 1. ĐỌC DANH SÁCH
# ============================================================================
@dataclass
class Entry:
    name: str           # tên hiển thị trong file danh sách
    keyword: str        # từ khóa tìm kiếm (giải mã từ link)
    url: str            # link gốc trong file
    sec_uid: str = ""   # có sẵn nếu link là link trang cá nhân /user/...


_LIST_PREFIX = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+(?:\[[ xX]\]\s*)?")
_MD_LINK = re.compile(r"^\[(?P<text>.*)\]\((?P<url>https?://[^\s)]+)\)\s*$")


def make_entry(name: str, url: str) -> Entry:
    path = urlparse(url).path
    keyword, sec_uid = name, ""
    m = re.match(r"^/(?:share/)?user/([^/?#]+)", path)
    if m:
        sec_uid = m.group(1)
    else:
        m = re.match(r"^/search/([^/?#]+)", path)
        if m:
            keyword = unquote(m.group(1))
    keyword = keyword or name or sec_uid
    return Entry(name=name or keyword, keyword=keyword, url=url, sec_uid=sec_uid)


def parse_input(path: Path) -> list[Entry]:
    entries: list[Entry] = []
    seen: set[str] = set()
    for raw in path.read_text(encoding="utf-8-sig").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        line = _LIST_PREFIX.sub("", line).strip()
        m = _MD_LINK.match(line)
        if m:
            entry = make_entry(m.group("text").strip(), m.group("url"))
        elif re.match(r"^https?://", line):
            entry = make_entry("", line)
        else:
            entry = make_entry(line, BASE + "/search/" + quote(line, safe="") + "?type=user")
        key = entry.sec_uid or entry.url
        if key in seen:
            continue
        seen.add(key)
        entries.append(entry)
    return entries


# ============================================================================
# 2. XỬ LÝ DỮ LIỆU API (thuần Python, không cần trình duyệt)
# ============================================================================
def norm(s) -> str:
    """Chuẩn hóa để so sánh: NFKC (ngoặc full-width -> ASCII...), bỏ khoảng trắng, không phân biệt hoa/thường."""
    s = unicodedata.normalize("NFKC", str(s or ""))
    return re.sub(r"\s+", "", s).casefold()


def _as_int(v) -> int:
    try:
        return int(v)
    except (TypeError, ValueError):
        return 0


def best_id(c: dict) -> str:
    uid = str(c.get("unique_id") or "").strip()
    if uid:
        return uid
    sid = str(c.get("short_id") or "").strip()
    return "" if sid in ("", "0") else sid


def extract_users(data) -> list[dict]:
    """Tìm mọi object 'người dùng' (có sec_uid + nickname) trong JSON bất kỳ.
    Ưu tiên user_list[].user_info (kết quả tìm kiếm). Giữ nguyên thứ tự xuất hiện."""
    found: dict[str, dict] = {}

    def add(d: dict) -> None:
        sec = d.get("sec_uid")
        if not isinstance(sec, str) or not sec or "nickname" not in d:
            return
        cand = {
            "sec_uid": sec,
            "nickname": str(d.get("nickname") or ""),
            "unique_id": str(d.get("unique_id") or ""),
            "short_id": str(d.get("short_id") or ""),
            "uid": str(d.get("uid") or ""),
            "followers": _as_int(d.get("follower_count") or d.get("mplatform_followers_count")),
            "aweme_count": _as_int(d.get("aweme_count")),
        }
        old = found.get(sec)
        if old is None:
            found[sec] = cand
        else:
            for k, v in cand.items():
                if not old.get(k) and v:
                    old[k] = v

    def walk(x, depth=0) -> None:
        if depth > 12:
            return
        if isinstance(x, dict):
            user_list = x.get("user_list")
            if isinstance(user_list, list):
                for it in user_list:
                    if isinstance(it, dict) and isinstance(it.get("user_info"), dict):
                        add(it["user_info"])
            add(x)
            for v in x.values():
                walk(v, depth + 1)
        elif isinstance(x, list):
            for v in x:
                walk(v, depth + 1)

    walk(data)
    return list(found.values())


def pick_candidate(keyword: str, cands: list[dict]):
    """Chọn tài khoản khớp nhất với từ khóa.
    Trả về (candidate | None, nhãn độ khớp, chắc chắn?, ghi chú)."""
    if not cands:
        return None, "", False, ""
    k = norm(keyword)
    k2 = norm(keyword.lstrip("@\uff20"))

    def id_set(c: dict) -> set:
        return {norm(c.get(f)) for f in ("unique_id", "short_id", "uid")} - {"", "0"}

    tiers = [
        ("ID khớp", lambda c: k in id_set(c)),
        ("Tên khớp", lambda c: norm(c["nickname"]) == k),
    ]
    if k2 and k2 != k:
        tiers.append(("Tên khớp (bỏ @)", lambda c: norm(c["nickname"]) == k2 or k2 in id_set(c)))
    for label, test in tiers:
        hits = [c for c in cands if test(c)]
        if hits:
            hits.sort(key=lambda c: c.get("followers", 0), reverse=True)
            note = ""
            if len(hits) > 1:
                note = "có %d tài khoản trùng, chọn tài khoản nhiều người theo dõi nhất" % len(hits)
            return hits[0], label, True, note
    for c in cands:
        if k and k in norm(c["nickname"]):
            return c, "Tên chứa từ khóa (cần kiểm tra)", False, ""
    return cands[0], "Kết quả đầu tiên (cần kiểm tra)", False, ""


def is_image_post(item: dict) -> bool:
    return bool(item.get("images")) or item.get("aweme_type") in (2, 68)


def post_stats(it: dict) -> dict:
    """Tương tác của một bài: like / share / lưu (KHÔNG gồm bình luận).
    -1 = API không trả số liệu đó (khác với 0 thật)."""
    st = it.get("statistics")
    if not isinstance(st, dict):
        st = {}

    def g(*keys) -> int:
        for k in keys:
            for src in (st, it):
                v = src.get(k)
                if v is not None and v != "":
                    return max(0, _as_int(v))
        return -1

    return {"likes": g("digg_count"), "shares": g("share_count"), "saves": g("collect_count")}


def merge_stats(info: dict, *sources) -> None:
    """Điền số liệu còn thiếu của bài `info` từ các danh sách bài khác (cùng aweme_id)."""
    for lst in sources:
        for it in lst or []:
            if isinstance(it, dict) and str(it.get("aweme_id") or "") == info["aweme_id"]:
                for k, v in post_stats(it).items():
                    if info.get(k, -1) < 0 and v >= 0:
                        info[k] = v


def post_ts(it: dict) -> int:
    ts = _as_int(it.get("create_time"))
    if ts > 10 ** 12:
        ts //= 1000
    if ts <= 0:
        ts = ts_from_aweme_id(it.get("aweme_id"))
    return ts


def list_videos(only_video: bool, *sources, limit: int = 15) -> list:
    """Gộp các bài gần nhất (theo aweme_id) từ nhiều nguồn, mỗi bài kèm like/share/lưu.
    Số liệu thiếu ở nguồn này được điền từ nguồn khác."""
    vids: dict = {}
    real_ids: set = set()
    for lst in sources:
        for it in lst or []:
            if not isinstance(it, dict):
                continue
            aid = str(it.get("aweme_id") or "")
            ts = post_ts(it)
            if not aid or ts <= 0 or (only_video and is_image_post(it)):
                continue
            real = _as_int(it.get("create_time")) > 0 and not it.get("_ts_from_id")
            if real and aid in vids and aid not in real_ids:
                vids[aid]["ts"] = ts            # cùng video: giờ thật thay giờ suy từ id
            if real:
                real_ids.add(aid)
            v = vids.setdefault(aid, {
                "aweme_id": aid, "ts": ts, "kind": "ảnh (图文)" if is_image_post(it) else "video",
                "desc": " ".join(str(it.get("desc") or "").split())[:100],
                "likes": -1, "shares": -1, "saves": -1})
            for k, val in post_stats(it).items():
                if v[k] < 0 and val >= 0:
                    v[k] = val
    return sorted(vids.values(), key=lambda v: v["ts"], reverse=True)[:limit]


def summarize_posts(aweme_list, only_video: bool = False):
    """Từ danh sách bài đăng lấy bài MỚI NHẤT (create_time lớn nhất)."""
    items = []
    for it in aweme_list or []:
        if not isinstance(it, dict):
            continue
        ts = _as_int(it.get("create_time"))
        if ts > 10 ** 12:  # phòng trường hợp mili-giây
            ts //= 1000
        if ts <= 0:  # API di động m.douyin.com KHÔNG có create_time -> suy ra từ aweme_id
            ts = ts_from_aweme_id(it.get("aweme_id"))
        if ts <= 0:
            continue
        if only_video and is_image_post(it):
            continue
        items.append((ts, it))
    if not items:
        return None
    ts, it = max(items, key=lambda x: x[0])
    return {
        "ts": ts,
        "aweme_id": str(it.get("aweme_id") or ""),
        "desc": " ".join(str(it.get("desc") or "").split())[:100],
        "kind": "ảnh (图文)" if is_image_post(it) else "video",
        "n": len(items),
        # True = giờ lấy từ create_time thật; False = suy ra từ aweme_id (API di động / thẻ thiếu create_time)
        "ts_real": _as_int(it.get("create_time")) > 0 and not it.get("_ts_from_id"),
        **post_stats(it),
    }


# --- Đồng hồ: lấy giờ chuẩn từ header "Date" của máy chủ Douyin ---------------------------------
# Nếu đồng hồ/múi giờ máy tính bị lệch (vd chỉnh tay giờ cho "đúng" nhưng sai múi giờ) thì mọi phép
# trừ "bây giờ - giờ đăng" đều sai: video đăng 4 tiếng trước có thể hiện "1 phút trước".
_SKEW_SAMPLES: list = []


def note_server_date(date_header) -> None:
    try:
        srv = email.utils.parsedate_to_datetime(str(date_header)).timestamp()
    except Exception:
        return
    _SKEW_SAMPLES.append(srv - time.time())
    del _SKEW_SAMPLES[:-30]


def clock_skew() -> float:
    """Giây cần cộng vào time.time() để ra giờ thật (0 nếu lệch < 2 phút hoặc chưa có dữ liệu)."""
    if len(_SKEW_SAMPLES) < 3:
        return 0.0
    m = statistics.median(_SKEW_SAMPLES)
    return m if abs(m) > 120 else 0.0


def now_epoch() -> float:
    return time.time() + clock_skew()


def ts_from_aweme_id(aid) -> int:
    """aweme_id của Douyin là dạng snowflake: 32 bit cao = unix timestamp lúc tạo video.
    Dùng khi JSON không có create_time."""
    n = _as_int(aid)
    if n <= 0:
        return 0
    ts = n >> 32
    return ts if 1_400_000_000 <= ts <= time.time() + 86400 else 0


def posts_by_user(data) -> dict:
    """Quét JSON tìm các video (có aweme_id) và gán cho đúng tài khoản.
    Dùng cho thẻ 'người dùng + 最新作品' trên so.douyin.com.
    Trả về {sec_uid: {aweme_id: dict giống phần tử aweme_list}}."""
    out: dict = {}

    def add(sec: str, it: dict) -> None:
        aid = str(it.get("aweme_id") or it.get("group_id") or "")
        if not re.fullmatch(r"\d{15,20}", aid):
            return
        ts = _as_int(it.get("create_time"))
        if ts > 10 ** 12:
            ts //= 1000
        from_id = ts <= 0
        if from_id:
            ts = ts_from_aweme_id(aid)
        if ts <= 0:
            return
        out.setdefault(sec, {})[aid] = {
            "aweme_id": aid, "create_time": ts, "desc": it.get("desc") or "", "_ts_from_id": from_id,
            "images": it.get("images"), "aweme_type": it.get("aweme_type"),
            "statistics": it.get("statistics"),
        }

    def walk(x, sec: str, depth: int) -> None:
        if depth > 14:
            return
        if isinstance(x, dict):
            ui = x.get("user_info")
            if isinstance(ui, dict) and isinstance(ui.get("sec_uid"), str) and ui["sec_uid"]:
                sec = ui["sec_uid"]
            elif isinstance(x.get("sec_uid"), str) and x["sec_uid"] and "nickname" in x:
                sec = x["sec_uid"]
            if "aweme_id" in x or ("group_id" in x and "create_time" in x):
                au = x.get("author")
                owner = au.get("sec_uid") if isinstance(au, dict) and au.get("sec_uid") else sec
                if owner:
                    add(owner, x)
            for v in x.values():
                walk(v, sec, depth + 1)
        elif isinstance(x, list):
            for v in x:
                walk(v, sec, depth + 1)

    walk(data, "", 0)
    return out


_RSC_PUSH = re.compile(r'self\.__rsc_f\.push\(\[(\d+),("(?:[^"\\]|\\.)*")\]\)')
_BUSINESS_DATA = re.compile(r'\{"business_data":\[')


def ssr_payloads(html: str) -> list:
    """Lấy dữ liệu kết quả tìm kiếm NHÚNG SẴN trong HTML của so.douyin.com.

    Trang này render phía server: thẻ người dùng (ala_src = "user_card") cùng 10 video mới nhất
    (aweme_id + create_time + author.sec_uid) nằm trong HTML, KHÔNG đi qua XHR/fetch nên
    việc "nghe" phản hồi API không thấy. Dữ liệu có 2 dạng:
      - JSON thường trong <script> (video đơn lẻ):   let data = {"business_data":[...]}
      - JSON bị escape trong luồng React Server Components: self.__rsc_f.push([1,"...\\"..."])
        (thẻ người dùng nằm ở đây) -> phải giải mã chuỗi JS trước rồi mới parse.
    """
    if not html:
        return []
    texts = [html]
    parts = []
    for kind, lit in _RSC_PUSH.findall(html):
        if kind != "1":
            continue
        try:
            parts.append(json.loads(lit))
        except ValueError:
            continue
    if parts:
        texts.append("".join(parts))
    dec = json.JSONDecoder()
    out = []
    for text in texts:
        for m in _BUSINESS_DATA.finditer(text):
            try:
                data, _end = dec.raw_decode(text, m.start())
            except ValueError:
                continue
            out.append(data)
    return out


def card_posts(col) -> dict:
    """Gộp video lấy từ mọi phản hồi so.douyin.com / tìm kiếm đã bắt được."""
    merged: dict = {}
    for _url, data in col.search:
        for sec, posts in posts_by_user(data).items():
            merged.setdefault(sec, {}).update(posts)
    return merged


def classify_page(text: str):
    for hint in PRIVATE_HINTS:
        if hint in text:
            return ST_PRIVATE, "trang hiển thị: " + hint
    for hint in GONE_HINTS:
        if hint in text:
            return ST_GONE, "trang hiển thị: " + hint
    return None, ""


def join_notes(*parts) -> str:
    return "; ".join(p for p in parts if p)


# ============================================================================
# 3. KẾT QUẢ
# ============================================================================
@dataclass
class Row:
    key: str = ""            # link gốc trong file (dùng làm khóa lưu tiến độ)
    keyword: str = ""
    name: str = ""
    status: str = ""
    note: str = ""
    nickname: str = ""
    douyin_id: str = ""
    match: str = ""
    confident: bool = False
    sec_uid: str = ""
    followers: int = 0
    latest_ts: int = 0
    kind: str = ""
    aweme_id: str = ""
    desc: str = ""
    checked_at: str = ""
    likes: int = -1          # lượt thích video mới nhất (-1 = không có số liệu)
    shares: int = -1         # lượt chia sẻ
    saves: int = -1          # lượt lưu (收藏)
    videos: list = dc_field(default_factory=list)   # ~15 bài gần nhất: để xếp hạng xu hướng
    seq: int = 0             # thứ tự trong lần chạy (n trong [n/tổng])
    total: int = 0           # tổng số tài khoản lần chạy
    took: float = 0.0        # số giây xử lý tài khoản này






def fmt_dt(ts: int) -> str:
    return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M")


def fmt_ago(seconds: float) -> str:
    seconds = int(seconds)
    if seconds < -300:   # giờ đăng lớn hơn giờ máy: KHÔNG che thành "1 phút trước" nữa
        return "giờ đăng ở tương lai (lệch %d phút - kiểm tra)" % (-seconds // 60)
    seconds = max(0, seconds)
    if seconds < 60:
        return "vừa xong"
    if seconds < 3600:
        return "%d phút trước" % (seconds // 60)
    if seconds < 86400:
        return "%d giờ trước" % (seconds // 3600)
    d = seconds // 86400
    if d < 60:
        return "%d ngày trước" % d
    if d < 365:
        return "%d ngày trước (~%d tháng)" % (d, d // 30)
    return "%d ngày trước (~%.1f năm)" % (d, d / 365)


def fmt_stat(n: int) -> str:
    """Số liệu tương tác để hiển thị; -1 (không có) -> chuỗi rỗng."""
    return "" if n is None or n < 0 else str(n)


def fmt_engage(r: Row) -> str:
    return "like %s | share %s | lưu %s" % tuple(fmt_stat(v) or "?" for v in (r.likes, r.shares, r.saves))


TREND_W = (("likes", 1.0), ("saves", 2.0), ("shares", 3.0))   # share/lưu là tín hiệu mạnh hơn like
TREND_GRAVITY = 1.5


def trend_score(v: dict, now_ts: float):
    """Điểm xu hướng = tương tác có trọng số / (tuổi video tính bằng giờ + 2)^1.5.
    Video không có bất kỳ số liệu nào -> None (không xếp hạng). Số liệu thiếu tính là 0."""
    if all(v.get(k, -1) < 0 for k, _ in TREND_W):
        return None
    eng = sum(max(0, v.get(k, -1)) * w for k, w in TREND_W)
    age_h = max(0.0, (now_ts - v["ts"]) / 3600)
    return eng / (age_h + 2) ** TREND_GRAVITY




def trend_rows(items, now_ts: float, days: int) -> list:
    """Mọi video (trong `days` ngày gần đây, 0 = không giới hạn) của mọi tài khoản, xếp theo điểm xu hướng."""
    out = []
    for i, e, r in items:
        if r is None or r.status != ST_OK:
            continue
        vids = r.videos or [{"aweme_id": r.aweme_id, "ts": r.latest_ts, "kind": r.kind, "desc": r.desc,
                             "likes": r.likes, "shares": r.shares, "saves": r.saves}]
        for v in vids:
            if days > 0 and now_ts - v["ts"] > days * 86400:
                continue
            sc = trend_score(v, now_ts)
            if sc is None:
                continue
            out.append({**v, "stt": i, "name": r.nickname or e.name, "score": sc})
    out.sort(key=lambda x: x["score"], reverse=True)
    return out


def result_parts(r: Row, now_ts: float, time_only: bool = False):
    """Dòng kết quả dạng: [6/71] 2026-10-23 21:09 | 1 ngày trước | video | like .. | share .. | lưu .. | Tên (@id)  [3.4s]
    Trả về (trước_tên, tên, sau_tên); tên là phần bấm để sao chép trong file HTML."""
    head = ("[%d/%d] " % (r.seq, r.total)) if r.seq and r.total else ""
    tail = ("  [%.1fs]" % r.took) if r.took > 0 else ""
    if r.status == ST_OK and time_only:   # (v27) chỉ giờ đăng + tên tác giả
        nick = (r.nickname or r.name or r.keyword or "").strip()
        return "%s%s | %s | " % (head, fmt_dt(r.latest_ts), fmt_ago(now_ts - r.latest_ts)), nick, tail
    if r.status == ST_OK:
        nick = (r.nickname or r.name or r.keyword or "").strip()
        before = "%s%s | %s | %s | %s | " % (head, fmt_dt(r.latest_ts), fmt_ago(now_ts - r.latest_ts),
                                            r.kind, fmt_engage(r))
        after = (" (@%s)" % r.douyin_id if r.douyin_id else "") + tail
        return before, nick, after
    nick = (r.nickname or r.name or r.keyword or "").strip()
    after = " | " + r.status + (" - " + r.note if r.note else "") + tail
    return head, nick, after


def format_result(r: Row, now_ts: float, time_only: bool = False) -> str:
    return "%s%s%s" % result_parts(r, now_ts, time_only)


def describe(r: Row, now_ts: float) -> str:
    if r.status == ST_OK:
        who = r.nickname + (" (@%s)" % r.douyin_id if r.douyin_id else "")
        return "%s | %s | %s | %s | %s | %s" % (
            fmt_dt(r.latest_ts), fmt_ago(now_ts - r.latest_ts), r.kind, fmt_engage(r), r.match, who)
    return r.status + (" - " + r.note if r.note else "")


# ============================================================================
# 4. TRÌNH DUYỆT
# ============================================================================
class Blocked(Exception):
    """Douyin chặn / yêu cầu captcha mà không xử lý được."""


def is_closed_error(e: Exception) -> bool:
    s = str(e).lower()
    return "has been closed" in s or "target closed" in s or "browser closed" in s


SO_PARAMS = ("enter_method=web_search&in_ogs=40&in_tfs=OS&original_source=40"
             "&query_correct_type=1&search_entrance=overseas&traffic_source=ZY1112"
             "&innerWidth=392&innerHeight=786")
SORT_MODE = "default"   # (v28) default | time | likes | both
SO_WEB_ID = ""   # có thể truyền bằng --web-id (douyin_web_id lấy từ link trình duyệt)


def search_url(entry) -> str:
    """Dùng trang so.douyin.com (không bị chặn như www.douyin.com/search)."""
    if "so.douyin.com" in entry.url:
        return entry.url
    u = "https://so.douyin.com/s?keyword=%s&%s" % (quote(entry.keyword, safe=""), SO_PARAMS)
    if SO_WEB_ID:
        u += "&douyin_web_id=" + SO_WEB_ID
    return u


def is_user_search_url(url: str) -> bool:
    return "aweme_user_web" in url or "/discover/search/" in url


def is_so_url(url: str) -> bool:
    return "so.douyin.com" in url


class Collector:
    """Thu các phản hồi API mà trang Douyin tự gọi (không tự gọi API nào)."""

    def __init__(self):
        self.reset()

    def reset(self) -> None:
        self._pending: list = []
        self.search: list = []      # [(url, json)]
        self.posts: list = []
        self.profiles: list = []
        self.details: list = []     # aweme_detail của trang video (có đủ like/share/lưu)
        self.user_search_seen = False
        self.verify_required = False
        self.ssr_ok = False         # đã đọc được dữ liệu nhúng sẵn trong HTML chưa

    def add_html(self, url: str, html: str) -> int:
        """Đưa dữ liệu nhúng trong HTML (SSR) vào danh sách kết quả tìm kiếm."""
        n = 0
        for data in ssr_payloads(html):
            self.search.append((url, data))
            n += 1
        if n:
            self.ssr_ok = True
        return n

    @staticmethod
    def _maybe_json(resp) -> bool:
        """(v24) Header đã có sẵn nên kiểm tra không tốn thêm lượt gọi trình duyệt; chỉ đọc body khi có thể là JSON.
        Header thiếu/lạ -> vẫn đọc (giữ hành vi cũ)."""
        try:
            ct = (resp.headers.get("content-type") or "").lower()
        except Exception:
            return True
        if not ct:
            return True
        return "json" in ct or "javascript" in ct or "text/plain" in ct

    def on_response(self, resp) -> None:
        try:
            url = resp.url
        except Exception:
            return
        if "douyin.com" in url:
            try:
                note_server_date(resp.headers.get("date"))
            except Exception:
                pass
        if "so.douyin.com" in url:
            # Trang tìm kiếm so.douyin.com: lấy mọi phản hồi XHR/JSON (không biết trước tên endpoint)
            try:
                rtype = resp.request.resource_type
            except Exception:
                rtype = ""
            if rtype == "document":
                # HTML của trang tìm kiếm: chứa sẵn thẻ người dùng + video mới nhất (SSR)
                self._pending.append(("doc", url, resp))
            elif rtype in ("xhr", "fetch"):
                self._pending.append(("search", url, resp))
            return
        if "m.douyin.com/web/api/v2/aweme/post/" in url:
            self._pending.append(("post", url, resp))   # trang chia sẻ di động (có a_bogus do trang tự ký)
            return
        if "douyin.com/aweme/" not in url:
            if "douyin.com" in url:  # endpoint lạ: vẫn thử đọc, có thể chứa aweme_list
                try:
                    rtype = resp.request.resource_type
                except Exception:
                    rtype = ""
                if rtype in ("xhr", "fetch") and self._maybe_json(resp):
                    self._pending.append(("any", url, resp))
            return
        if "douyin.com/aweme/v1/web/" not in url:
            if self._maybe_json(resp):
                self._pending.append(("any", url, resp))
            return
        if "/aweme/v1/web/aweme/detail/" in url:
            self._pending.append(("detail", url, resp))
        elif "/aweme/v1/web/aweme/post/" in url:
            self._pending.append(("post", url, resp))
        elif "/aweme/v1/web/user/profile/other/" in url:
            self._pending.append(("profile", url, resp))
        elif "search" in url:
            self._pending.append(("search", url, resp))

    def drain(self) -> None:
        """Đọc nội dung các phản hồi đã bắt được (làm ngoài event handler cho an toàn)."""
        pending, self._pending = self._pending, []
        for kind, url, resp in pending:
            if kind == "doc":
                try:
                    self.add_html(url, resp.text())
                except Exception:
                    pass
                continue
            try:
                data = resp.json()
            except Exception:
                continue
            if isinstance(data, dict) and isinstance(data.get("aweme_detail"), dict):
                self.details.append(data["aweme_detail"])
                continue
            if isinstance(data, dict) and isinstance(data.get("item_list"), list):   # API iteminfo của trang di động
                for it in data["item_list"]:
                    if isinstance(it, dict) and it.get("aweme_id") and isinstance(it.get("statistics"), dict):
                        self.details.append(it)
            if kind == "detail":
                continue
            if kind != "post" and isinstance(data, dict) and isinstance(data.get("aweme_list"), list) \
                    and any(isinstance(x, dict) and (x.get("create_time") or x.get("aweme_id"))
                            for x in data["aweme_list"]):
                self.posts.append((url, data))   # bất kỳ endpoint nào trả danh sách bài có create_time
                continue
            if kind == "any":
                if extract_users(data):
                    self.profiles.append((url, data))
                continue
            if kind == "post":
                self.posts.append((url, data))
            elif kind == "profile":
                self.profiles.append((url, data))
            elif is_so_url(url):
                # so.douyin.com: không chắc là API tìm kiếm -> chỉ tính khi thật sự có người dùng
                self.search.append((url, data))
                if not extract_users(data) and "verify_check" in json.dumps(data, ensure_ascii=False)[:4000]:
                    self.verify_required = True
            else:
                self.search.append((url, data))
                if is_user_search_url(url):
                    self.user_search_seen = True
                    if not extract_users(data):
                        blob = json.dumps(data, ensure_ascii=False)[:4000]
                        if "verify_check" in blob:
                            self.verify_required = True


_CAPTCHA_SELECTORS = ("#captcha_container", ".captcha_verify_container", "#captcha-verify-image")


_CAPTCHA_JS = """sels => {
    if ((document.title || '').indexOf('验证码') >= 0) return true;
    for (const s of sels) {
        const el = document.querySelector(s);
        if (el && (el.offsetWidth > 0 || el.offsetHeight > 0 || el.getClientRects().length > 0)) return true;
    }
    return false;
}"""


def has_captcha(page) -> bool:
    """(v24) Một lượt gọi trình duyệt duy nhất (trước đây title() + 3 locator = 4-7 lượt mỗi lần kiểm tra)."""
    try:
        return bool(page.evaluate(_CAPTCHA_JS, list(_CAPTCHA_SELECTORS)))
    except Exception as e:
        if is_closed_error(e):
            raise
    return False


_STOP = threading.Event()   # (v27) Ctrl+C -> báo mọi luồng dừng
_ENTER_Q: list = []          # mỗi lần nhấn Enter ở terminal thêm 1 phần tử (một luồng đọc duy nhất)
_ENTER_THREAD = []


def _enter_reader() -> None:
    while True:
        try:
            input()
        except EOFError:
            _ENTER_Q.append("eof")
            return
        _ENTER_Q.append("enter")


def ask_captcha(page=None, visible: bool = True) -> bool:
    """DỪNG hẳn để bạn giải captcha trong cửa sổ trình duyệt. Tự chạy tiếp khi captcha biến mất,
    hoặc khi bạn nhấn Enter ở terminal. Không giới hạn thời gian chờ (Ctrl+C để dừng cả chương trình)."""
    import threading
    print("\n   [!] Douyin đang yêu cầu xác minh (captcha).  >>> ĐÃ DỪNG, chờ bạn giải <<<\a")
    print("       Giải captcha trong cửa sổ trình duyệt. Xong sẽ tự chạy tiếp"
          if visible else "       Hãy giải/kiểm tra trong cửa sổ trình duyệt rồi nhấn Enter ở đây để chạy tiếp")
    print("       (hoặc nhấn Enter ở terminal để chạy tiếp ngay).", flush=True)
    print("       Nếu cửa sổ không hiện ảnh captcha: nhấn Ctrl+C rồi chạy lại với --load-all.", flush=True)
    if page is not None:
        try:
            page.bring_to_front()
        except Exception as e:
            if is_closed_error(e):
                raise
    if not _ENTER_THREAD:
        t = threading.Thread(target=_enter_reader, daemon=True)
        t.start()
        _ENTER_THREAD.append(t)
    _ENTER_Q[:] = [x for x in _ENTER_Q if x == "eof"]    # bỏ các Enter cũ
    gone, last_beep, t_chk = 0, time.time(), 0.0
    while True:
        if _STOP.is_set():
            raise KeyboardInterrupt
        if _ENTER_Q:
            if _ENTER_Q[0] == "eof" and visible is False:
                return False
            if _ENTER_Q[0] == "enter":
                _ENTER_Q.pop(0)
                return True
        if visible and page is not None and time.time() - t_chk >= 1.0:
            t_chk = time.time()
            gone = 0 if has_captcha(page) else gone + 1
            if gone >= 2:                      # captcha đã biến mất 2 lần liên tiếp -> đã giải xong
                print("       Đã giải xong captcha, chạy tiếp...", flush=True)
                return True
        if time.time() - last_beep > 20:
            last_beep = time.time()
            print("       ... vẫn đang chờ bạn giải captcha \a", flush=True)
        if page is not None:
            try:
                page.wait_for_timeout(300)     # để Playwright xử lý sự kiện
            except Exception as e:
                if is_closed_error(e):
                    raise
                time.sleep(0.3)
        else:
            time.sleep(0.3)


BLOCK_PATTERNS = [
    "*.mp4*", "*.m4a*", "*.mp3*", "*.webm*", "*.m3u8*", "*.woff*", "*.ttf*", "*.otf*",
    "*.gif*", "*.png*", "*.jpg*", "*.jpeg*", "*.webp*", "*.awebp*", "*.avif*",
    "*mon.zijieapi.com*", "*mcs.zijieapi.com*", "*mon.snssdk.com*", "*log.snssdk.com*",
    "*/aweme/v1/web/report/*", "*/monitor_browser/*", "*/slardar/*",
]


def block_heavy(page) -> None:
    """(v26) Chặn video/ảnh/font/telemetry bằng CDP Network.setBlockedURLs: Chrome tự chặn, KHÔNG đi vòng qua Python
    như page.route nên không làm chậm. Lỗi thì bỏ qua (chạy bình thường)."""
    try:
        cdp = page.context.new_cdp_session(page)
        cdp.send("Network.enable")
        cdp.send("Network.setBlockedURLs", {"urls": BLOCK_PATTERNS})
    except Exception:
        pass


def _block_heavy_old(page) -> None:
    """(v23) Không còn dùng page.route nữa: mỗi request phải đi vòng qua Python rất chậm và còn làm Chrome
    tắt cache. Việc chặn ảnh/font giờ do cờ của Chrome đảm nhiệm (xem launch(): imagesEnabled=false,
    --disable-remote-fonts) nên hàm này để trống, giữ lại cho các chỗ gọi cũ."""
    return None


def goto(page, url: str, wait: str = "domcontentloaded") -> None:
    try:
        page.goto(url, wait_until=wait, timeout=45000)
    except Exception as e:
        if is_closed_error(e):
            raise
        # Quá thời gian tải trang chưa chắc là hỏng: API vẫn có thể đã trả dữ liệu


def reload_page(page) -> None:
    try:
        page.reload(wait_until="domcontentloaded", timeout=45000)
    except Exception as e:
        if is_closed_error(e):
            raise


def page_text(page) -> str:
    try:
        return page.inner_text("body", timeout=3000)
    except Exception:
        return ""


def poll(page, col: Collector, step, timeout: float, args):
    """Gọi step(elapsed) ~3 lần/giây tới khi nó trả về giá trị khác None hoặc hết giờ.
    Tự phát hiện captcha và nhờ người dùng giải."""
    t0 = time.time()
    last_cap = t0          # (v24) có dữ liệu thì khỏi kiểm tra captcha; chỉ kiểm tra khi đã chờ > 1.5 giây
    rounds = 0
    while True:
        col.drain()
        res = step(time.time() - t0)
        if res is not None:
            return res
        if time.time() - t0 > timeout:
            return None
        if time.time() - last_cap > 1.5:
            last_cap = time.time()
            seen_cap = has_captcha(page)
            if seen_cap or col.verify_required:
                rounds += 1
                if args.headless or rounds > 50 or not ask_captcha(page, visible=seen_cap):
                    raise Blocked("Douyin yêu cầu xác minh (captcha)")
                col.reset()
                reload_page(page)
                t0 = time.time()
        page.wait_for_timeout(80)  # cần dùng hàm của Playwright để nó xử lý sự kiện (v24: 80ms, trước 150ms)


def dom_candidates(page) -> list[dict]:
    """Phương án dự phòng: đọc thẳng các link /user/... trên trang kết quả tìm kiếm."""
    try:
        items = page.eval_on_selector_all(
            'a[href*="/user/"]',
            "els => els.map(e => ({href: e.href, text: (e.innerText || '').trim()}))",
        )
    except Exception:
        return []
    out, seen = [], set()
    if not items:
        # trang render phía server: sec_uid nằm trong HTML/JSON nhúng
        try:
            html = page.content()
        except Exception:
            html = ""
        for sec in re.findall(r"MS4wLjABAAAA[A-Za-z0-9_\-]{20,}", html):
            if sec not in seen:
                seen.add(sec)
                out.append({"sec_uid": sec, "nickname": "", "unique_id": "", "short_id": "",
                            "uid": "", "followers": 0, "aweme_count": 0})
        return out
    for it in items or []:
        m = re.search(r"/user/([A-Za-z0-9_\-]{20,})", it.get("href", ""))
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        text = it.get("text", "")
        lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
        idm = re.search(r"抖音号[:：]\s*(\S+)", text)
        out.append({
            "sec_uid": m.group(1),
            "nickname": lines[0] if lines else "",
            "unique_id": idm.group(1) if idm else "",
            "short_id": "", "uid": "", "followers": 0, "aweme_count": 0,
        })
    return out


def search_user(page, col: Collector, entry: Entry, args):
    """Mở trang tìm kiếm người dùng, trả về (danh sách ứng viên, có nhận được phản hồi?)."""
    col.reset()
    goto(page, search_url(entry), wait="commit")   # (v24) dữ liệu nằm sẵn trong HTML -> khỏi chờ DOMContentLoaded
    state = {"t_strong": None, "t_empty": None, "t_html": -99.0, "key": None, "sw": ([], [])}

    def read_html(elapsed):
        """Dự phòng: nếu chưa bắt được HTML gốc thì đọc thẳng DOM hiện tại (cũng chứa dữ liệu nhúng)."""
        if col.ssr_ok or elapsed < 2 or elapsed - state["t_html"] < 2:
            return
        state["t_html"] = elapsed
        try:
            if is_so_url(page.url):
                col.add_html(page.url, page.content())
        except Exception as e:
            if is_closed_error(e):
                raise

    def split():
        key = (id(col.search), len(col.search))
        if key != state["key"]:          # chỉ quét lại JSON khi có phản hồi mới (poll giờ chạy dày hơn)
            strong, weak = {}, {}
            for url, data in col.search:
                target = strong if (is_user_search_url(url) or is_so_url(url)) else weak
                for c in extract_users(data):
                    target.setdefault(c["sec_uid"], c)
            state["key"], state["sw"] = key, (list(strong.values()), list(weak.values()))
        return state["sw"]

    def step(elapsed):
        read_html(elapsed)
        strong, weak = split()
        now = time.time()
        if strong:
            if state["t_strong"] is None:
                state["t_strong"] = now          # chờ thêm một chút cho đủ dữ liệu
            elif now - state["t_strong"] >= 0.25:     # (v24) trước đây 0.5 giây
                return strong, True
        elif col.verify_required:
            return None                          # đợi captcha được xử lý
        elif col.user_search_seen:               # API trả về nhưng không có người dùng nào
            if state["t_empty"] is None:
                state["t_empty"] = now
            elif now - state["t_empty"] >= 2.0:
                return [], True
        elif weak and elapsed > 5:               # đề phòng tên endpoint thay đổi
            return weak, True
        elif elapsed > 6 and is_so_url(page.url):  # so.douyin.com có thể render sẵn trong HTML
            dom = dom_candidates(page)
            if dom:
                return dom, True
        return None

    res = poll(page, col, step, SEARCH_TIMEOUT, args)
    if res is not None:
        return res
    strong, weak = split()
    cands = strong or weak or dom_candidates(page)
    if col.verify_required and not cands:
        raise Blocked("Douyin yêu cầu xác minh khi tìm kiếm (verify_check)")
    return cands, bool(cands) or col.user_search_seen


MOBILE_UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 "
             "(KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1")
MOBILE_QS = ("?scene_from=douyin_h5_search&search_entrance=overseas&traffic_source=ZY1112"
             "&original_source=40&in_tfs=OS&in_ogs=40&browser_type=unknown")
_MOBILE_PAGES: dict = {}   # id(context) -> tab giả lập điện thoại (dùng lại cho mọi tài khoản)


args_ref = argparse.Namespace(load_all=False)


def get_mobile_page(page, col: Collector):
    ctx = page.context
    mp = _MOBILE_PAGES.get(id(ctx))
    if mp is not None:
        try:
            if not mp.is_closed():
                mp.bring_to_front()      # tab được giữ lại (đang trống) -> đưa lên trước để thấy captcha nếu có
                return mp
        except Exception:
            pass
    mp = ctx.new_page()
    try:
        cdp = ctx.new_cdp_session(mp)
        cdp.send("Emulation.setUserAgentOverride", {"userAgent": MOBILE_UA, "platform": "iPhone"})
        cdp.send("Emulation.setDeviceMetricsOverride",
                 {"width": 390, "height": 844, "deviceScaleFactor": 1, "mobile": True})
        cdp.send("Emulation.setTouchEmulationEnabled", {"enabled": True})
    except Exception as e:
        if is_closed_error(e):
            raise
    mp.on("response", col.on_response)
    if not getattr(args_ref, "load_all", False):
        block_heavy(mp)
    _MOBILE_PAGES[id(ctx)] = mp
    return mp


_TITLE_SUFFIX = re.compile(r"\s*(?:的抖音(?:主页|号)?|的个人主页|的主页|[-|｜]\s*抖音.*|\s抖音)\s*$")
_BAD_NAMES = {"", "抖音", "douyin", "抖音分享", "抖音-记录美好生活", "抖音-记录美好生活!"}


def _clean_title(t: str) -> str:
    t = " ".join(str(t or "").split())
    for _ in range(2):
        t = _TITLE_SUFFIX.sub("", t).strip()
    return "" if t.casefold() in _BAD_NAMES else t


def parse_profile_html(html: str, sec_uid: str) -> dict:
    """Lấy tên tài khoản / Douyin ID / người theo dõi từ HTML trang chia sẻ di động.
    API aweme/post của trang di động KHÔNG có thông tin tác giả nên phải đọc từ chính trang:
    (1) JSON nhúng (window._ROUTER_DATA...), (2) cụm "nickname" gần sec_uid, (3) <title>/og:title,
    (4) dòng "抖音号：xxx"."""
    out = {"nickname": "", "douyin_id": "", "followers": 0}
    if not html:
        return out
    dec = json.JSONDecoder()
    # (1) JSON nhúng trong <script>
    for m in re.finditer(r"(?:_ROUTER_DATA|__INITIAL_STATE__|RENDER_DATA)\s*=\s*(\{)", html):
        try:
            data, _ = dec.raw_decode(html, m.start(1))
        except ValueError:
            continue
        users = extract_users(data)
        pick = next((u for u in users if u["sec_uid"] == sec_uid), None) or (users[0] if users else None)
        if pick and pick["nickname"]:
            out.update(nickname=pick["nickname"], douyin_id=best_id(pick), followers=pick["followers"])
            break
    # (2) "nickname" nằm gần sec_uid (JSON bị escape hoặc không)
    if not out["nickname"]:
        for m in re.finditer(re.escape(sec_uid), html):
            win = html[max(0, m.start() - 3000): m.end() + 3000].replace('\\"', '"')
            nm = re.search(r'"nickname"\s*:\s*"((?:[^"\\]|\\.)*)"', win)
            if nm:
                try:
                    out["nickname"] = json.loads('"%s"' % nm.group(1))
                except ValueError:
                    out["nickname"] = nm.group(1)
                um = re.search(r'"unique_id"\s*:\s*"([^"]+)"', win) or re.search(r'"short_id"\s*:\s*"(\d{3,})"', win)
                fm = re.search(r'"(?:mplatform_followers_count|follower_count)"\s*:\s*(\d+)', win)
                out["douyin_id"] = um.group(1) if um else ""
                out["followers"] = int(fm.group(1)) if fm else 0
                break
    # (3) <title> / og:title
    if not out["nickname"]:
        for pat in (r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)',
                    r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:title',
                    r"<title[^>]*>([^<]+)</title>"):
            tm = re.search(pat, html, re.I)
            if tm:
                name = _clean_title(tm.group(1))
                if name:
                    out["nickname"] = name
                    break
    # (4) 抖音号 hiển thị trên trang
    if not out["douyin_id"]:
        im = re.search(r"抖音号[:：]\s*([A-Za-z0-9_.\-]+)", html)
        if im:
            out["douyin_id"] = im.group(1)
    return out


def dom_profile(mp, sec_uid: str) -> dict:
    """Đọc tên ngay trên giao diện trang di động (dự phòng khi HTML không có JSON)."""
    out = {"nickname": "", "douyin_id": "", "followers": 0}
    try:
        for sel in ('[class*="nickname"]', '[class*="user-name"]', '[class*="author-name"]',
                    '[class*="name"] >> nth=0', "h1", "h2"):
            loc = mp.locator(sel)
            if loc.count() > 0:
                txt = " ".join((loc.first.inner_text(timeout=1500) or "").split())
                if txt and txt.casefold() not in _BAD_NAMES and len(txt) <= 40:
                    out["nickname"] = txt
                    break
        body = page_text(mp)
        im = re.search(r"抖音号[:：]\s*([A-Za-z0-9_.\-]+)", body)
        if im:
            out["douyin_id"] = im.group(1)
        if not out["nickname"]:
            out["nickname"] = _clean_title(mp.title())
    except Exception as e:
        if is_closed_error(e):
            raise
    return out


def grab_profile_hint(mp, col: Collector, sec_uid: str) -> None:
    """Sau khi trang di động tải xong: lấy tên/ID từ HTML + giao diện, lưu vào col.profile_hint."""
    info = {"nickname": "", "douyin_id": "", "followers": 0}

    def read_html() -> str:
        try:
            return mp.content()
        except Exception as e:
            if is_closed_error(e):
                raise
            return ""

    html = read_html()
    parts = [parse_profile_html(html, sec_uid)]
    if not parts[0]["nickname"]:           # HTML chưa có tên -> chờ giao diện render rồi mới đọc DOM
        mp.wait_for_timeout(600)
        html = read_html()
        parts = [parse_profile_html(html, sec_uid), dom_profile(mp, sec_uid)]
    col.mobile_html = html
    for part in parts:
        for k, v in part.items():
            if v and not info[k]:
                info[k] = v
    col.profile_hint = info


def fetch_posts_mobile(page, col: Collector, sec_uid: str, args):
    """Trang chia sẻ di động m.douyin.com/share/user/<sec_uid>: gọi /web/api/v2/aweme/post/ (HTTP 200,
    15 bài mới nhất, KHÔNG có create_time -> giờ đăng suy ra từ aweme_id)."""
    mp = get_mobile_page(page, col)
    col.reset()
    col.profile_hint = {}
    col.mobile_html = ""
    goto(mp, "https://m.douyin.com/share/user/%s%s" % (sec_uid, MOBILE_QS), wait="commit")

    def step(elapsed):
        for url, data in col.posts:
            if "/aweme/post/" in url and sec_uid in url and isinstance(data, dict) and "aweme_list" in data:
                return data
        return None

    data = poll(mp, col, step, MOBILE_TIMEOUT, args)
    if data is not None and getattr(col, "want_hint", True):   # đã biết tên (từ tìm kiếm/lần trước) thì khỏi đọc
        grab_profile_hint(mp, col, sec_uid)
    return data


def fetch_name_www(page, col: Collector, sec_uid: str, args) -> dict:
    """Phương án cuối để lấy tên: mở trang cá nhân www.douyin.com và đọc API hồ sơ (profile/other)."""
    col.reset()
    goto(page, "%s/user/%s" % (BASE, sec_uid), wait="commit")

    def step(elapsed):
        for _u, pdata in col.profiles:
            for u in extract_users(pdata):
                if u["sec_uid"] == sec_uid and u["nickname"]:
                    return {"nickname": u["nickname"], "douyin_id": best_id(u), "followers": u["followers"]}
        return None

    res = poll(page, col, step, 12, args)
    if res:
        return res
    try:
        info = parse_profile_html(page.content(), sec_uid)
    except Exception as e:
        if is_closed_error(e):
            raise
        info = {"nickname": "", "douyin_id": "", "followers": 0}
    return info


def fetch_posts(page, col: Collector, sec_uid: str, args):
    """Ưu tiên trang di động (ổn định); nếu không có bài nào thì dùng trang cá nhân www.douyin.com."""
    blocked = None
    try:
        park_page(page)              # nhả RAM trang tìm kiếm trước khi mở tab di động
        data = fetch_posts_mobile(page, col, sec_uid, args)
        if data and data.get("aweme_list"):
            return data              # (v24) KHÔNG về about:blank ở đây: tab di động còn dùng cho bước share/lưu,
                                     # free_memory() sẽ nhả sau khi xong tài khoản
    except Blocked as e:
        blocked = e
    close_mobile_page(page)          # sắp mở trang www nặng -> nhả tab di động trước
    try:
        return fetch_posts_www(page, col, sec_uid, args)
    except Blocked:
        raise
    except Exception:
        if blocked is not None:
            raise blocked
        raise


def fetch_posts_www(page, col: Collector, sec_uid: str, args):
    """Mở trang cá nhân, trả về JSON `aweme/post` đầu tiên (hoặc None nếu hết giờ)."""
    col.reset()
    goto(page, "%s/user/%s" % (BASE, sec_uid), wait="commit")

    def step(elapsed):
        for url, data in col.posts:
            if not (isinstance(data, dict) and "aweme_list" in data):
                continue
            by_author = any(isinstance(x, dict) and isinstance(x.get("author"), dict)
                            and x["author"].get("sec_uid") == sec_uid for x in data["aweme_list"])
            if sec_uid in url or by_author or elapsed > 10:
                return data
        return None

    return poll(page, col, step, PROFILE_TIMEOUT, args)


_STAT_KEYS = {"likes": "digg_count", "shares": "share_count", "saves": "collect_count"}


def stats_from_html(html: str, aweme_id: str) -> dict:
    """Dự phòng: đọc digg/share/collect_count nằm gần aweme_id trong HTML trang video."""
    out: dict = {}
    if not html or not aweme_id:
        return out
    for m in re.finditer(re.escape(aweme_id), html):
        win = html[max(0, m.start() - 5000): m.end() + 5000]
        for k, key in _STAT_KEYS.items():
            if k in out:
                continue
            mm = re.search(r'%s\\*"\s*:\s*(\d+)' % key, win)
            if mm:
                out[k] = int(mm.group(1))
        if len(out) == 3:
            break
    return out


def router_item(html: str, aweme_id: str):
    """Trang chia sẻ di động nhúng sẵn JSON `window._ROUTER_DATA = {...}` chứa bài đăng (có statistics)."""
    if not html or not aweme_id:
        return None
    i = html.find("_ROUTER_DATA")
    j = html.find("{", i) if i >= 0 else -1
    if j < 0:
        return None
    try:
        data, _end = json.JSONDecoder().raw_decode(html, j)
    except ValueError:
        return None
    stack = [data]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            if str(x.get("aweme_id") or "") == aweme_id and isinstance(x.get("statistics"), dict):
                return x
            stack.extend(x.values())
        elif isinstance(x, list):
            stack.extend(x)
    return None


def need_more_stats(info: dict) -> bool:
    """Share/lưu thiếu (-1) hoặc nghi là số 0 giả của API di động."""
    if info["shares"] < 0 or info["saves"] < 0:
        return True
    return info["shares"] == 0 and info["saves"] == 0 and info["likes"] > 20


def fetch_video_stats(page, col: Collector, aweme_id: str, kind: str, args) -> dict:
    """Mở trang chia sẻ DI ĐỘNG m.douyin.com/share/video/<id> (ít bị chặn hơn trang www) để lấy like/share/lưu.
    Đọc từ JSON nhúng sẵn _ROUTER_DATA hoặc từ API iteminfo mà trang tự gọi. (Bài ảnh tự chuyển sang /share/slides.)"""
    mp = get_mobile_page(page, col)
    col.reset()
    goto(mp, "https://m.douyin.com/share/video/%s%s" % (aweme_id, MOBILE_QS), wait="commit")
    state = {"last": -9.0}

    def step(elapsed):
        for d in col.details:
            if str(d.get("aweme_id") or "") == aweme_id:
                return post_stats(d)
        if elapsed - state["last"] >= 0.6:   # (v24) đọc HTML ngay lần đầu, sau đó thưa 0.6s (đỡ tốn RAM/CPU)
            state["last"] = elapsed
            html = page_html(mp)
            item = router_item(html, aweme_id)
            if item is not None:
                return post_stats(item)
            if elapsed > 6:
                got = stats_from_html(html, aweme_id)
                if got.get("shares") is not None or got.get("saves") is not None:
                    return {"likes": got.get("likes", -1), "shares": got.get("shares", -1),
                            "saves": got.get("saves", -1)}
        return None

    return poll(mp, col, step, STATS_TIMEOUT, args) or {}


def page_html(page) -> str:
    try:
        return page.content()
    except Exception:
        return ""


_STATS_STATE = {"fails": 0, "off": False}


def safe_fetch_stats(page, col: Collector, aweme_id: str, kind: str, args) -> dict:
    """Lấy share/lưu từ trang video. Gặp captcha: dừng chờ bạn giải (với --headless thì bỏ qua).
    Thất bại 3 lần liên tiếp thì tắt bước này cho phần còn lại của lần chạy (tránh chạy mãi / bị chặn thêm)."""
    if _STATS_STATE["off"]:
        return {}
    quiet = args            # gặp captcha thì DỪNG chờ bạn giải (chỉ bỏ qua nếu chạy --headless)
    print("   ... lấy share/lưu từ trang video di động %s" % aweme_id, flush=True)
    try:
        got = fetch_video_stats(page, col, aweme_id, kind, quiet)
    except Blocked:
        got = {}
    if got:
        _STATS_STATE["fails"] = 0
    else:
        _STATS_STATE["fails"] += 1
        if _STATS_STATE["fails"] >= 3:
            _STATS_STATE["off"] = True
            print("   [!] Trang video liên tục không trả số liệu/captcha -> tạm tắt bước lấy share/lưu "
                  "cho phần còn lại (kết quả vẫn chạy tiếp).", flush=True)
    return got


def check_entry(page, col: Collector, entry: Entry, prev, args, reuse: bool = False) -> Row:
    row = Row(key=entry.url, keyword=entry.keyword, name=entry.name,
              checked_at=datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
    col.profile_hint, col.mobile_html = {}, ""   # tránh dính tên của tài khoản trước
    try:
        card: dict = {}   # video lấy từ thẻ tìm kiếm so.douyin.com
        # --- Bước 1: xác định tài khoản (sec_uid) ---
        if entry.sec_uid:
            row.sec_uid, row.match, row.confident = entry.sec_uid, "Link trực tiếp", True
            if prev is not None and prev.nickname:   # dùng lại tên đã lấy được ở lần trước
                row.nickname, row.douyin_id, row.followers = prev.nickname, prev.douyin_id, prev.followers
        elif (args.refresh or reuse) and prev is not None and prev.sec_uid:
            row.sec_uid, row.match, row.confident = prev.sec_uid, prev.match, prev.confident
            row.nickname, row.douyin_id, row.followers = prev.nickname, prev.douyin_id, prev.followers
            if not args.fast:   # vẫn mở trang tìm kiếm để lấy video mới nhất ở thẻ người dùng
                try:
                    search_user(page, col, entry, args)
                    card = card_posts(col)
                except Blocked:
                    pass
        else:
            cands, saw_response = search_user(page, col, entry, args)
            card = card_posts(col)
            if not cands:
                if saw_response:
                    row.status, row.note = ST_NOT_FOUND, "Tìm kiếm không có người dùng nào"
                else:
                    row.status = ST_ERROR
                    row.note = "Không nhận được kết quả tìm kiếm (mạng chậm / chưa đăng nhập / bị chặn?)"
                return row
            cand, label, confident, note = pick_candidate(entry.keyword, cands)
            row.sec_uid, row.match, row.confident, row.note = cand["sec_uid"], label, confident, note
            row.nickname, row.douyin_id, row.followers = cand["nickname"], best_id(cand), cand["followers"]

        # --- Bước 2: lấy danh sách bài đăng ---
        cinfo = summarize_posts(list(card.get(row.sec_uid, {}).values()), args.only_video)
        data = None
        col.want_hint = not row.nickname      # chỉ đọc tên từ trang di động khi chưa có tên
        if cinfo and args.card_only:
            row.note = join_notes(row.note, "chỉ dùng thẻ tìm kiếm (--card-only)")
        else:
            try:
                data = fetch_posts(page, col, row.sec_uid, args)
            except Blocked:
                if not cinfo:
                    raise
                row.note = join_notes(row.note, "trang cá nhân bị chặn/captcha, dùng dữ liệu thẻ tìm kiếm")
        if data is None and not cinfo:
            status, why = classify_page(page_text(page))
            if status:
                row.status, row.note = status, join_notes(row.note, why)
            else:
                row.status = ST_ERROR
                row.note = join_notes(row.note, "Không nhận được danh sách bài đăng (hết thời gian chờ)")
            return row

        prof_count = 0  # số bài mà API hồ sơ báo (nếu có) - để phát hiện bị giới hạn tạm thời
        for _url, pdata in col.profiles:  # bổ sung thông tin từ API hồ sơ (nếu có)
            for u in extract_users(pdata):
                if u["sec_uid"] == row.sec_uid:
                    row.nickname = u["nickname"] or row.nickname
                    row.douyin_id = best_id(u) or row.douyin_id
                    row.followers = u["followers"] or row.followers
                    prof_count = max(prof_count, u["aweme_count"])

        # --- Tên tác giả: trang di động không trả tác giả trong API bài đăng -> lấy từ trang ---
        hint = getattr(col, "profile_hint", None) or {}
        if hint.get("nickname") and not row.nickname:
            row.nickname = hint["nickname"]
        if hint.get("douyin_id") and not row.douyin_id:
            row.douyin_id = hint["douyin_id"]
        if hint.get("followers") and not row.followers:
            row.followers = hint["followers"]
        if not row.nickname:   # (v27) trang www trả sẵn author trong từng bài -> khỏi mở thêm trang lấy tên
            for it in (data or {}).get("aweme_list") or []:
                au = it.get("author") if isinstance(it, dict) else None
                if isinstance(au, dict) and au.get("sec_uid") == row.sec_uid and au.get("nickname"):
                    row.nickname = au["nickname"]
                    break
        if not row.nickname and not getattr(args, "no_name_lookup", False):
            try:
                close_mobile_page(page)      # (v24) nhả tab di động trước khi mở trang www nặng
                got = fetch_name_www(page, col, row.sec_uid, args)
                row.nickname = got.get("nickname") or row.nickname
                row.douyin_id = got.get("douyin_id") or row.douyin_id
                row.followers = got.get("followers") or row.followers
            except Blocked:
                row.note = join_notes(row.note, "không lấy được tên (captcha ở trang cá nhân)")
        if not row.nickname:
            row.note = join_notes(row.note, "không lấy được tên tài khoản")

        aweme_list = (data or {}).get("aweme_list") or []
        info = summarize_posts(aweme_list, args.only_video)
        if info and cinfo and info["aweme_id"] == cinfo["aweme_id"]:
            # cùng MỘT video: giờ create_time thật thắng giờ suy từ aweme_id (hai giờ lệch vài phút
            # từng bị báo nhầm là "thẻ tìm kiếm mới hơn trang cá nhân 1 phút")
            if cinfo["ts_real"] and not info["ts_real"]:
                info["ts"], info["ts_real"] = cinfo["ts"], True
        elif cinfo and (info is None or cinfo["ts"] > info["ts"]):
            if info:
                row.note = join_notes(row.note, "thẻ tìm kiếm mới hơn trang cá nhân %s"
                                      % fmt_ago(cinfo["ts"] - info["ts"]).replace(" trước", ""))
            else:
                row.note = join_notes(row.note, "lấy từ thẻ tìm kiếm so.douyin.com")
            info = cinfo
        if info:
            # nguồn được chọn có thể thiếu like/share/lưu -> lấy bổ sung từ nguồn còn lại (cùng aweme_id)
            if info["ts"] > now_epoch() + 300:
                row.note = join_notes(row.note, "giờ đăng lớn hơn giờ máy tính - kiểm tra đồng hồ/múi giờ máy")
            merge_stats(info, aweme_list, list(card.get(row.sec_uid, {}).values()))
            row.status, row.latest_ts, row.kind = ST_OK, info["ts"], info["kind"]
            row.aweme_id, row.desc = info["aweme_id"], info["desc"]
            stats_on = not getattr(args, "no_stats_lookup", False)
            used = 0
            if stats_on and need_more_stats(info) and info["aweme_id"]:
                used = 1
                more = safe_fetch_stats(page, col, info["aweme_id"], info["kind"], args)
                for k, v in more.items():
                    if v is not None and v >= 0 and (info.get(k, -1) <= 0 or v > info[k]):
                        info[k] = v
                if not more:
                    row.note = join_notes(row.note, "không lấy được share/lưu từ trang video")
                elif need_more_stats(info):
                    row.note = join_notes(row.note, "Douyin không trả share/lưu cho video này")
            row.likes, row.shares, row.saves = info["likes"], info["shares"], info["saves"]
            row.videos = list_videos(args.only_video, aweme_list, list(card.get(row.sec_uid, {}).values()))
            for v in row.videos:                   # đồng bộ số liệu đã bổ sung của video mới nhất
                if v["aweme_id"] == info["aweme_id"]:
                    for k in ("likes", "shares", "saves"):
                        if info[k] >= 0 and (v[k] <= 0 or info[k] > v[k]):
                            v[k] = info[k]
            budget = max(0, getattr(args, "stats_max", 1) - used)
            if stats_on and budget:
                cutoff = now_epoch() - (args.trend_days * 86400 if args.trend_days > 0 else 10 ** 10)
                for v in row.videos:               # các video khác (mới nhất trước) cũng bị trống share/lưu
                    if budget <= 0 or _STATS_STATE["off"]:
                        break
                    if v["aweme_id"] == info["aweme_id"] or v["ts"] < cutoff or not need_more_stats(v):
                        continue
                    budget -= 1
                    more = safe_fetch_stats(page, col, v["aweme_id"], v["kind"], args)
                    for k, val in more.items():
                        if val is not None and val >= 0 and (v.get(k, -1) <= 0 or val > v[k]):
                            v[k] = val
        else:
            status, why = classify_page(page_text(page))
            if status is None:
                if prof_count > 0 and not aweme_list:
                    status = ST_ERROR
                    why = ("Hồ sơ báo có %d bài nhưng API trả danh sách rỗng "
                           "(có thể Douyin giới hạn tạm thời - chạy lại sau)" % prof_count)
                else:
                    status = ST_NO_VIDEO
                    why = "Danh sách bài đăng trống"
                    if aweme_list and args.only_video:
                        why = "Chỉ có bài ảnh (đã lọc bằng --only-video)"
            row.status = status
            row.note = join_notes(row.note, why)
    except Blocked as e:
        row.status, row.note = ST_ERROR, join_notes(row.note, str(e))
    except Exception as e:
        if is_closed_error(e):
            raise
        row.status = ST_ERROR
        row.note = join_notes(row.note, "%s: %s" % (type(e).__name__, str(e)[:150]))
    return row


# Cờ giúp Chrome/Chromium dùng ít RAM hơn (máy 4GB): tắt GPU/tiện ích/đồng bộ (đã bỏ giới hạn bộ nhớ JS vì làm tab Chrome bị crash)
LOW_RAM_ARGS = [
    "--disable-gpu", "--disable-dev-shm-usage", "--disable-extensions", "--disable-background-networking",
    "--disable-sync", "--disable-default-apps", "--no-first-run", "--mute-audio",
    "--disable-features=IsolateOrigins,site-per-process,Translate,BackForwardCache,MediaRouter,OptimizationHints",
]


# Cờ tiết kiệm RAM (luôn bật, dành cho máy 4GB): chỉ tắt các thành phần phụ, TUYỆT ĐỐI không giới hạn bộ nhớ JS (gây "Ôi hỏng")
LOW_RAM_EXTRA = [
    "--disable-component-update", "--disable-breakpad", "--disable-domain-reliability",
    "--disable-renderer-accessibility", "--disable-notifications", "--disable-speech-api",
    "--autoplay-policy=user-gesture-required", "--disk-cache-size=157286400",   # cache ĐĨA 150MB (không tốn RAM): khỏi tải lại JS của Douyin mỗi tài khoản
    "--metrics-recording-only",
    # (v24) tab nền không bị Chrome hãm timer/render -> trang tìm kiếm chạy trong lúc tab di động đang ở trước
    "--disable-background-timer-throttling", "--disable-renderer-backgrounding",
    "--disable-backgrounding-occluded-windows",
]


def launch(p, args):
    kw = dict(
        user_data_dir=str(Path(args.profile).resolve()),
        headless=args.headless,
        viewport={"width": 1000, "height": 700},
        locale="zh-CN",
        args=["--disable-blink-features=AutomationControlled"] + LOW_RAM_ARGS + LOW_RAM_EXTRA
             + ([] if args.load_all else ["--blink-settings=imagesEnabled=false", "--disable-remote-fonts"]),
        ignore_default_args=["--enable-automation"],
    )
    if args.browser == "chrome":
        try:
            return p.chromium.launch_persistent_context(channel="chrome", **kw)
        except Exception:
            print("  (không mở được Google Chrome -> dùng Chromium của Playwright)")
    try:
        return p.chromium.launch_persistent_context(**kw)
    except Exception as e:
        sys.exit("Không mở được trình duyệt: %s\nHãy chạy:  playwright install chromium" % str(e)[:200])


def close_mobile_page(page) -> None:
    """Dùng xong thì đưa tab di động về trang trống (nhả RAM) nhưng GIỮ tab để lần sau khỏi tạo lại
    (tạo tab + CDP mỗi lần tốn ~1 giây). Tab hỏng thì bỏ."""
    key = id(page.context)
    mp = _MOBILE_PAGES.get(key)
    if mp is None:
        return
    try:
        if mp.is_closed():
            _MOBILE_PAGES.pop(key, None)
        elif mp.url != "about:blank":
            mp.goto("about:blank", timeout=8000)
    except Exception:
        _MOBILE_PAGES.pop(key, None)
        try:
            mp.close()
        except Exception:
            pass


def park_page(page) -> None:
    """Đưa tab chính về trang trống để Chrome trả RAM của trang tìm kiếm/trang cá nhân."""
    try:
        if page.url != "about:blank":
            page.goto("about:blank", timeout=8000)
    except Exception:
        pass


def free_memory(page) -> None:
    """Sau mỗi tài khoản: đưa tab di động + tab chính về trang trống, dọn rác Python."""
    close_mobile_page(page)
    try:
        if page.url != "about:blank":      # thường đã trống rồi -> khỏi điều hướng thừa
            page.goto("about:blank", timeout=8000)
        page.bring_to_front()
    except Exception:
        pass
    gc.collect()


def restart_browser(p, ctx, col: Collector, args):
    """Đóng hẳn trình duyệt rồi mở lại (cùng profile nên vẫn giữ đăng nhập) để trả RAM về cho máy."""
    print("   (khởi động lại trình duyệt để giải phóng RAM)", flush=True)
    try:
        ctx.close()
    except Exception:
        pass
    _MOBILE_PAGES.clear()
    gc.collect()
    ctx = launch(p, args)
    page = ctx.pages[0] if ctx.pages else ctx.new_page()
    page.on("response", col.on_response)
    if not args.load_all:
        block_heavy(page)
    return ctx, page


def is_logged_in(ctx) -> bool:
    try:
        names = {c["name"] for c in ctx.cookies() if "douyin.com" in c.get("domain", "")}
    except Exception:
        return False
    return bool(names & {"sessionid", "sessionid_ss", "sid_tt"})


def ensure_login(ctx, page, args) -> bool:
    """Không mở douyin.com và không hỏi gì: vào thẳng bước kiểm tra, dùng phiên đã lưu trong --profile."""
    ok = is_logged_in(ctx)
    print("Dùng phiên Douyin đã lưu." if ok else "Chưa có phiên đăng nhập Douyin (vẫn chạy, nhưng dễ gặp captcha hơn).")
    return ok


# ============================================================================
# 5. LƯU TIẾN ĐỘ
# ============================================================================























def load_cache(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if not isinstance(raw, dict):      
        return {}
    names = {f.name for f in fields(Row)}
    out = {}
    for key, val in (raw.get("rows") or {}).items():
        try:
            out[key] = Row(**{k: v for k, v in val.items() if k in names})
        except (TypeError, AttributeError):
            continue
    return out




def save_cache(path: Path, cache: dict) -> None:
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps({"version": 1, "rows": {k: asdict(v) for k, v in cache.items()}},
                              ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    tmp.replace(path)






def account_ranks(items, now_ts: float, days: int) -> dict:
    """Hạng xu hướng của TÀI KHOẢN: dựa trên video xu hướng nhất của tài khoản đó (1 = xu hướng nhất)."""
    best: dict = {}
    for v in trend_rows(items, now_ts, days):      # đã xếp giảm dần theo điểm
        best.setdefault(v["stt"], v["score"])
    order = sorted(best, key=lambda k: best[k], reverse=True)
    return {stt: n for n, stt in enumerate(order, 1)}


def write_txt(path: Path, items, now_ts: float, days: int, time_only: bool = False) -> None:
    """File txt: mỗi tài khoản một dòng '[n/tổng] giờ đăng | cách đây | loại | like | share | lưu | tên (@id)  [giây]'.
    File html: bảng cũ (tên - hạng - video mới nhất), bấm tên để sao chép."""
    ok_items = [(i, r) for i, e, r in items if r is not None and r.status == ST_OK and r.latest_ts > 0]
    # (v28) hạng theo giờ đăng (1 = mới đăng nhất) và hạng theo tim (1 = nhiều tim nhất; không có số tim -> không xếp)
    t_order = sorted(ok_items, key=lambda x: (-x[1].latest_ts, x[0]))
    time_rank = {i: n for n, (i, _r) in enumerate(t_order, 1)}
    l_order = sorted((x for x in ok_items if x[1].likes >= 0), key=lambda x: (-x[1].likes, -x[1].latest_ts, x[0]))
    like_rank = {i: n for n, (i, _r) in enumerate(l_order, 1)}
    mode = SORT_MODE
    if mode == "time" or (mode == "default" and time_only):
        ranks = dict(time_rank)
    elif mode == "likes":
        ranks = dict(like_rank)
    elif mode == "both":   # điểm = hạng giờ + hạng tim (thấp = tốt); thiếu tim -> hạng tim cuối bảng; bằng điểm -> bài mới hơn trước
        worst = len(l_order) + 1
        score = {i: time_rank[i] + like_rank.get(i, worst) for i, _r in ok_items}
        order = sorted(ok_items, key=lambda x: (score[x[0]], time_rank[x[0]]))
        ranks = {i: n for n, (i, _r) in enumerate(order, 1)}
    else:
        ranks = account_ranks(items, now_ts, days)
    rows = []
    for i, e, r in items:
        if r is None:
            continue
        if r.status == ST_OK and r.latest_ts > 0:
            posted = "đăng %s (%s)" % (fmt_dt(r.latest_ts), fmt_ago(now_ts - r.latest_ts))
        else:
            posted = "không có giờ đăng" + (" (%s)" % r.status if r.status else "")
        extra = (time_rank.get(i), like_rank.get(i), r.likes)
        rows.append((ranks.get(i, 10 ** 9), i, (r.nickname or e.name).strip(), posted, result_parts(r, now_ts, time_only), extra))
    rows.sort(key=lambda x: (x[0], x[1]))
    write_html(path.with_suffix(".html"), [(rk, i, n, p, ex) for rk, i, n, p, _parts, ex in rows])


def write_csv(path: Path, rows) -> None:
    """CSV (UTF-8 có BOM): mở bằng Google Sheets/Excel; chạm ô tác giả rồi Sao chép (không bị trình duyệt chặn)."""
    import csv
    with open(path, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["STT", "Tác giả", "Hạng", "Hạng giờ", "Tim", "Hạng tim", "Video mới nhất"])
        for n, (rk, _i, name, posted, ex) in enumerate(rows, 1):
            w.writerow([n, name, rk if rk < 10 ** 9 else "-", ex[0] or "-", ex[2] if ex[2] is not None and ex[2] >= 0 else "-",
                        ex[1] or "-", posted])


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="vi"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Kết quả Douyin</title>
<style>
body{font-family:Segoe UI,Arial,sans-serif;margin:0;padding:24px;background:#f5f5f7;color:#1d1d1f}
h1{font-size:20px;margin:0 0 4px} .hint{color:#666;font-size:14px;margin-bottom:16px}
table{border-collapse:collapse;width:100%;max-width:1100px;background:#fff;border-radius:8px;overflow:hidden}
th,td{padding:10px 14px;text-align:left;border-bottom:1px solid #eee;font-size:15px}
th{background:#fafafa;font-size:13px;color:#666}
.name{color:#0b57d0;cursor:pointer;font-weight:600;display:inline-block;padding:4px 2px;-webkit-tap-highlight-color:rgba(11,87,208,.25);touch-action:manipulation} .name:hover{text-decoration:underline}
.copied{background:#e6f4ea} .copied .name{color:#137333}
#toast{position:fixed;bottom:24px;left:50%;transform:translateX(-50%);background:#202124;color:#fff;
padding:10px 18px;border-radius:20px;font-size:14px;opacity:0;transition:opacity .2s;pointer-events:none}
#toast.show{opacity:1}
.nm{font:inherit;font-weight:600;color:#0b57d0;border:1px solid #ddd;border-radius:6px;padding:6px 8px;width:11em;max-width:45vw;background:#fff}
.cp{font-size:14px;padding:7px 12px;margin-left:6px;border:0;border-radius:6px;background:#0b57d0;color:#fff;touch-action:manipulation}
.cp:active{background:#0842a0}
.copied .cp{background:#137333}
#manual{display:none;position:fixed;left:0;right:0;bottom:0;background:#fff;padding:14px;box-shadow:0 -2px 12px rgba(0,0,0,.25);z-index:30}
#manual textarea{width:100%;box-sizing:border-box;font-size:16px;padding:8px;border:1px solid #ccc;border-radius:6px}
#manual button{margin-top:8px;font-size:15px;padding:6px 14px}
</style></head><body>
<h1>Kết quả Douyin</h1>
<div class="hint">Bấm nút <b>Sao chép</b> cạnh tên tác giả (hoặc chạm vào ô tên rồi giữ để chép tay). Cập nhật lúc __TIME__ · __COUNT__ tài khoản</div>
<table><thead><tr><th>#</th><th>Tác giả</th><th>Hạng</th><th>Hạng giờ</th><th>Tim</th><th>Hạng tim</th><th>Video mới nhất</th></tr></thead>
<tbody>
__ROWS__
</tbody></table>
<div id="toast"></div>
<div id="manual"><div>Máy chặn tự sao chép — chữ đã được chọn sẵn, hãy giữ ngón tay rồi chọn <b>Sao chép</b>:</div>
<textarea id="mt" rows="2"></textarea><br><button id="mc">Đóng</button></div>
<script>
var timer;
function toast(m){var b=document.getElementById("toast");b.textContent=m;b.classList.add("show");clearTimeout(timer);timer=setTimeout(function(){b.classList.remove("show");},2200);}
function pick(inp){inp.focus();inp.select();try{inp.setSelectionRange(0,inp.value.length);}catch(e){}}
function copyFrom(inp,tr){
  var t=inp.value,ok=false;
  pick(inp);                                        /* ô tên thật, đang hiện trên màn hình -> Android cho chép */
  try{ok=document.execCommand("copy");}catch(e){ok=false;}
  function fin(good){
    if(good){tr.classList.add("copied");toast("Đã sao chép: "+t);}
    else{pick(inp);toast("Chữ đã được chọn sẵn: giữ ngón tay rồi chọn Sao chép");}
  }
  if(navigator.clipboard&&navigator.clipboard.writeText){
    navigator.clipboard.writeText(t).then(function(){fin(true);},function(){fin(ok);});
  }else{fin(ok);}
}
document.querySelectorAll("tr").forEach(function(tr){
  var inp=tr.querySelector(".nm"),btn=tr.querySelector(".cp");
  if(!inp||!btn)return;
  btn.addEventListener("click",function(ev){ev.preventDefault();copyFrom(inp,tr);});
  inp.addEventListener("click",function(){pick(inp);});
});
</script></body></html>"""


def write_html(path: Path, rows) -> None:
    """File HTML: bấm vào tên tác giả để sao chép tên."""
    import html as _html
    trs = []
    for n, (rk, _i, name, posted, ex) in enumerate(rows, 1):
        rank = ("%d" % rk) if rk < 10 ** 9 else "-"
        t_rk = ("%d" % ex[0]) if ex[0] else "-"
        l_rk = ("%d" % ex[1]) if ex[1] else "-"
        likes = ("{:,}".format(ex[2])) if ex[2] is not None and ex[2] >= 0 else "-"
        trs.append('<tr><td>%d</td><td><input class="nm" readonly value="%s"><button class="cp" type="button">Sao chép</button></td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>'
                   % (n, _html.escape(name, quote=True), rank, t_rk, likes, l_rk, _html.escape(posted)))
    page = (HTML_TEMPLATE.replace("__TIME__", datetime.now().strftime("%d/%m/%Y %H:%M:%S"))
            .replace("__COUNT__", str(len(rows))).replace("__ROWS__", "\n".join(trs)))
    path.write_text(page, encoding="utf-8")


def save_txt(entries, cache: dict, path: Path, days: int, time_only: bool = False) -> None:
    items = [(i, e, cache.get(e.url)) for i, e in enumerate(entries, 1)]
    try:
        write_txt(path, items, now_epoch(), days, time_only)
    except PermissionError:
        print("  [!] Không ghi được %s (đang mở?). Hãy đóng file rồi chạy lại." % path)


# ============================================================================
# 6. CHƯƠNG TRÌNH CHÍNH
# ============================================================================
# ---------------------------------------------------------------- Google Drive
DRIVE_SCOPES = ["https://www.googleapis.com/auth/drive.file"]


class DriveUploader:
    """Upload/cập nhật file kết quả lên Google Drive. Lỗi Drive KHÔNG làm dừng việc quét."""

    def __init__(self, folder_name, creds_path="credentials.json", token_path="token.json"):
        self.folder_name = folder_name
        self.creds_path = Path(creds_path)
        self.token_path = Path(token_path)
        self.service = None
        self.folder_id = None
        self.file_ids = {}
        self.ok = False

    def connect(self) -> bool:
        try:
            from google.auth.transport.requests import Request
            from google.oauth2.credentials import Credentials
            from google_auth_oauthlib.flow import InstalledAppFlow
            from googleapiclient.discovery import build
        except ImportError:
            print("[Drive] Thiếu thư viện. Chạy: pip install google-api-python-client google-auth-oauthlib")
            return False
        try:
            creds = None
            if self.token_path.exists():
                creds = Credentials.from_authorized_user_file(str(self.token_path), DRIVE_SCOPES)
            if not creds or not creds.valid:
                if creds and creds.expired and creds.refresh_token:
                    try:
                        creds.refresh(Request())
                    except Exception:
                        creds = None
                if not creds or not creds.valid:
                    if not self.creds_path.exists():
                        print("[Drive] Không thấy %s (đặt cạnh script)." % self.creds_path)
                        return False
                    flow = InstalledAppFlow.from_client_secrets_file(str(self.creds_path), DRIVE_SCOPES)
                    creds = flow.run_local_server(port=0)   # lần đầu: mở trình duyệt xin quyền
                self.token_path.write_text(creds.to_json(), encoding="utf-8")
            self.service = build("drive", "v3", credentials=creds, cache_discovery=False)
            self.folder_id = self._get_or_create_folder(self.folder_name)
            self.ok = True
            print("[Drive] Đã kết nối. Thư mục Drive: %s" % self.folder_name)
            return True
        except Exception as ex:
            print("[Drive] Không kết nối được: %s" % ex)
            return False

    def _get_or_create_folder(self, name):
        q = ("name='%s' and mimeType='application/vnd.google-apps.folder' and trashed=false"
             % name.replace("'", "\\'"))
        res = self.service.files().list(q=q, fields="files(id)", pageSize=1).execute()
        if res.get("files"):
            return res["files"][0]["id"]
        meta = {"name": name, "mimeType": "application/vnd.google-apps.folder"}
        return self.service.files().create(body=meta, fields="id").execute()["id"]

    def upload(self, path) -> None:
        if not self.ok:
            return
        try:
            from googleapiclient.http import MediaFileUpload
            path = Path(path)
            if not path.exists():
                return
            is_csv = path.suffix.lower() == ".csv"
            mime = "text/html" if path.suffix.lower() == ".html" else ("text/csv" if is_csv else "text/plain")
            media = MediaFileUpload(str(path), mimetype=mime, resumable=False)
            fid = self.file_ids.get(path.name)
            if fid:
                self.service.files().update(fileId=fid, media_body=media).execute()
            else:
                meta = {"name": path.name, "parents": [self.folder_id]}
                if is_csv:      # đổi thành Google Sheets: mở bằng app Sheets, chạm ô rồi Sao chép
                    meta = {"name": path.stem, "parents": [self.folder_id],
                            "mimeType": "application/vnd.google-apps.spreadsheet"}
                self.file_ids[path.name] = self.service.files().create(
                    body=meta, media_body=media, fields="id").execute()["id"]
        except Exception as ex:
            print("   [Drive] Upload lỗi (bỏ qua, vẫn chạy tiếp): %s" % ex)

    def cleanup_old(self, prefix) -> int:
        """Chuyển vào THÙNG RÁC các file kết quả cũ (tên bắt đầu bằng prefix) trong thư mục Drive,
        trừ file của lần chạy này. Chỉ đụng tới file do chính script tạo (quyền drive.file)."""
        if not self.ok:
            return 0
        keep = set(self.file_ids.values())
        trashed = 0
        try:
            page = None
            while True:
                res = self.service.files().list(
                    q="'%s' in parents and trashed=false" % self.folder_id,
                    fields="nextPageToken, files(id,name)", pageSize=200, pageToken=page).execute()
                for f in res.get("files", []):
                    if f["id"] in keep or not f["name"].startswith(prefix):
                        continue
                    self.service.files().update(fileId=f["id"], body={"trashed": True}).execute()
                    trashed += 1
                page = res.get("nextPageToken")
                if not page:
                    break
        except Exception as ex:
            print("[Drive] Dọn file cũ lỗi (bỏ qua): %s" % ex)
        return trashed


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        description="Kiểm tra video mới nhất của các tài khoản Douyin được đăng từ bao giờ.")
    ap.add_argument("input", nargs="?",
                    help="File danh sách link (mặc định: link_unique* trong thư mục hiện tại)")
    ap.add_argument("-o", "--out", default="ketqua_douyin",
                    help="Tiền tố tên file kết quả (mặc định: ketqua_douyin -> doyin/ketqua_douyin_<giờ chạy>.html)")
    ap.add_argument("--dir", default="doyin",
                    help="Thư mục lưu kết quả (mặc định: doyin; chưa có thì tự tạo, có rồi thì ghi thẳng vào)")
    ap.add_argument("--no-drive", action="store_true",
                    help="Không upload kết quả lên Google Drive")
    ap.add_argument("--keep-old-drive", action="store_true",
                    help="KHÔNG xóa file kết quả cũ trên Drive (mặc định: dọn file cũ sau khi chạy xong)")
    ap.add_argument("--drive-folder", default="Douyin",
                    help="Tên thư mục trên Google Drive (mặc định: Douyin; chưa có thì tự tạo)")
    ap.add_argument("--drive-creds", default="credentials.json",
                    help="File OAuth của Google (mặc định: credentials.json cạnh script)")
    ap.add_argument("--profile", default="douyin_profile", help="Thư mục lưu phiên trình duyệt / đăng nhập")
    ap.add_argument("--limit", type=int, default=0,
                    help="Chỉ kiểm tra N tài khoản chưa xong (0 = tất cả). Dùng để chạy thử")
    ap.add_argument("--start", type=int, default=1, help="Bắt đầu từ STT này")
    ap.add_argument("--refresh", action="store_true",
                    help="Kiểm tra lại tất cả (dùng lại sec_uid đã tìm được nên bỏ qua bước tìm kiếm)")
    ap.add_argument("--fast", action="store_true",
                    help="Với --refresh: bỏ qua bước tìm kiếm (nhanh hơn nhưng không lấy được video mới ở thẻ tìm kiếm)")
    ap.add_argument("--delay", type=float, nargs=2, metavar=("MIN", "MAX"), default=[0.3, 0.8],
                    help="Nghỉ ngẫu nhiên MIN-MAX giây giữa các tài khoản (mặc định 0.3 0.8; gặp captcha nhiều thì tăng lên, vd --delay 1 2)")
    ap.add_argument("--load-all", action="store_true",
                    help="Tải cả ảnh/video/font (mặc định đã chặn để chạy nhanh hơn)")
    ap.add_argument("--only-video", action="store_true", help="Bỏ qua bài dạng ảnh (图文), chỉ tính video")
    ap.add_argument("--card-only", action="store_true",
                    help="Nếu thẻ tìm kiếm so.douyin.com đã có video thì KHÔNG mở trang cá nhân "
                         "(nhanh hơn nhiều, ít bị captcha; thẻ chứa 10 video mới nhất)")
    ap.add_argument("--browser", choices=["chrome", "chromium"], default="chrome",
                    help="chrome = Google Chrome đã cài (tự chuyển sang chromium nếu không có)")
    ap.add_argument("--headless", action="store_true",
                    help="Chạy ẩn (dễ bị Douyin chặn hơn và không giải được captcha)")
    ap.add_argument("--web-id", default="",
                    help="douyin_web_id lấy từ link so.douyin.com trên trình duyệt của bạn (tuỳ chọn)")
    ap.add_argument("--trend-days", type=int, default=30,
                    help="Chỉ xếp hạng xu hướng các video đăng trong N ngày gần đây (mặc định 30, 0 = tất cả)")
    ap.add_argument("--no-name-lookup", action="store_true",
                    help="Không mở trang cá nhân www.douyin.com để tìm tên khi trang di động không có tên")
    ap.add_argument("--restart-every", type=int, default=12,
                    help="Cứ N tài khoản thì đóng và mở lại trình duyệt để giải phóng RAM (mặc định 12, 0 = không; "
                         "máy hay bị đầy RAM thì hạ xuống 6-8)")
    ap.add_argument("--stats-max", type=int, default=1,
                    help="Mỗi tài khoản mở tối đa N trang video để bổ sung share/lưu còn trống (mặc định 1, 0 = tắt)")
    ap.add_argument("--no-stats-lookup", action="store_true",
                    help="Không mở trang video để bổ sung share/lưu khi API không trả (nhanh hơn nhưng có thể trống)")
    ap.add_argument("--drive-every", type=int, default=0,
                    help="(v26) Cứ N tài khoản upload Drive 1 lần giữa chừng. Mặc định 0 = CHỈ upload 1 lần ở cuối khi chạy xong (hoặc Ctrl+C)")
    ap.add_argument("--save-every", type=int, default=5,
                    help="(v26) Cứ N tài khoản mới ghi file tiến độ tien_do.json (mặc định 5). File .txt vẫn ghi sau mỗi tài khoản")
    ap.add_argument("--turbo", action="store_true",
                    help="(v26) Chạy nhanh nhất: --fast + --card-only + --no-name-lookup + --no-stats-lookup + --no-drive (mất share/lưu và tên đôi khi trống)")
    ap.add_argument("--min-time", type=float, default=5.0, metavar="GIÂY",
                    help="(v27) Thời gian TỐI THIỂU cho mỗi tài khoản (mặc định 5 giây; xử lý nhanh hơn thì chờ cho đủ, 0 = tắt)")
    ap.add_argument("--workers", type=int, default=0, metavar="N",
                    help="(v27) Số luồng chạy song song, mỗi luồng 1 cửa sổ Chrome riêng (0 = tự chọn: --time-only dùng 2, "
                         "các chế độ khác dùng 1). Luồng 2+ dùng thư mục douyin_profile_w2... (tự sao chép từ profile chính)")
    ap.add_argument("--sort", choices=["default", "time", "likes", "both"], default="default",
                    help="(v28) Cách xếp hạng: time = giờ đăng mới nhất lên đầu; likes = nhiều tim nhất lên đầu; "
                         "both = kết hợp (hạng giờ + hạng tim, thấp nhất lên đầu); default = như cũ (xu hướng, hoặc theo giờ nếu --time-only)")
    ap.add_argument("--time-only", action="store_true",
                    help="(v27) Chỉ lấy giờ đăng của bài mới nhất + tên tác giả: chỉ mở trang cá nhân (không tìm kiếm, "
                         "không lấy like/share/lưu), kết quả xếp theo giờ đăng gần nhất lên đầu")
    return ap


def find_link_unique() -> Path | None:
    """Tìm file danh sách link_unique* (không phân biệt hoa/thường) trong thư mục hiện tại."""
    found = sorted(f for f in Path(".").iterdir()
                   if f.is_file() and f.name.casefold().startswith("link_unique"))
    return found[0] if found else None


def resolve_input(arg) -> Path:
    """Danh sách link duy nhất để chạy: tham số input / file link_unique* trong thư mục."""
    if arg:
        p = Path(arg)
        if not p.exists():
            sys.exit("Không thấy file: %s" % p)
        return p
    lu = find_link_unique()
    if lu:
        return lu
    sys.exit("Không thấy file link_unique* trong thư mục hiện tại. Hãy đặt file link_unique.txt "
             "cùng thư mục với script, hoặc chỉ định:  python douyin_last_post.py link_unique.txt")


def clone_profile(src: Path, dst: Path) -> None:
    """(v27) Mỗi cửa sổ Chrome cần thư mục profile riêng. Sao chép profile chính (giữ đăng nhập) một lần,
    bỏ qua cache cho nhẹ. Muốn đồng bộ lại đăng nhập thì xóa thư mục douyin_profile_w2."""
    if dst.exists():
        return
    if not src.exists():
        dst.mkdir(parents=True, exist_ok=True)
        return
    print("Sao chép profile -> %s (một lần duy nhất)..." % dst)
    ig = shutil.ignore_patterns("Cache", "Code Cache", "GPUCache", "GrShaderCache", "ShaderCache", "Crashpad",
                                "Service Worker", "Singleton*", "lockfile", "*.lock")
    try:
        shutil.copytree(src, dst, ignore=ig)
    except Exception as ex:
        print("  [!] Sao chép profile chưa trọn vẹn (%s) - luồng này có thể phải đăng nhập lại." % str(ex)[:120])
        dst.mkdir(parents=True, exist_ok=True)


def run_parallel(args, todo, entries, state, cache, txt_path, state_path, drive, timings, time_only) -> bool:
    """(v27) Chạy `args.workers` luồng song song, lấy tài khoản từ chung một hàng đợi (luồng xong trước lấy tiếp).
    Mỗi luồng có sync_playwright + Chrome + profile riêng. Trả về True nếu bị dừng giữa chừng."""
    q: queue.Queue = queue.Queue()
    for n, (idx, e) in enumerate(todo, 1):
        q.put((n, idx, e))
    total = len(todo)
    nw = max(1, min(args.workers, total))
    profiles = [args.profile] + ["%s_w%d" % (args.profile, k) for k in range(2, nw + 1)]
    for pr in profiles[1:]:
        clone_profile(Path(args.profile), Path(pr))
    args_ref.load_all = args.load_all
    lock = threading.Lock()
    state_info = {"done": 0, "stopped": False}

    def nap(seconds: float) -> None:
        end = time.time() + seconds
        while time.time() < end and not _STOP.is_set():
            time.sleep(min(0.25, max(0.0, end - time.time())))

    def worker(w: int, prof: str) -> None:
        wargs = copy.copy(args)
        wargs.profile = prof
        tag = "[L%d] " % w
        try:
            with sync_playwright() as p:
                ctx = launch(p, wargs)
                try:
                    page = ctx.pages[0] if ctx.pages else ctx.new_page()
                    col = Collector()
                    page.on("response", col.on_response)
                    if not args.load_all:
                        block_heavy(page)
                    ensure_login(ctx, page, wargs)
                    count = 0
                    while not _STOP.is_set():
                        try:
                            n, idx, e = q.get_nowait()
                        except queue.Empty:
                            break
                        with lock:
                            print("\n%s[%d/%d | STT %d] %s" % (tag, n, total, idx, e.keyword), flush=True)
                        acc_t0 = time.time()
                        try:
                            row = check_entry(page, col, e, state.get(e.url), wargs, reuse=e.url not in cache)
                        except KeyboardInterrupt:
                            q.put((n, idx, e))
                            raise
                        except Exception as ex:
                            if is_closed_error(ex):
                                with lock:
                                    print("%sCửa sổ trình duyệt đã bị đóng -> luồng này dừng." % tag, flush=True)
                                q.put((n, idx, e))      # trả lại cho luồng còn lại
                                break
                            row = Row(key=e.url, keyword=e.keyword, name=e.name, status=ST_ERROR,
                                      note="%s: %s" % (type(ex).__name__, str(ex)[:150]),
                                      checked_at=datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
                        row.seq, row.total, row.took = n, total, time.time() - acc_t0
                        free_memory(page)
                        with lock:
                            cache[e.url] = row
                            state[e.url] = row
                            state_info["done"] += 1
                            d = state_info["done"]
                            if d % max(1, args.save_every) == 0:
                                save_cache(state_path, state)
                            save_txt(entries, cache, txt_path, args.trend_days, time_only)
                            if drive.ok and args.drive_every > 0 and d % args.drive_every == 0:
                                drive.upload(txt_path.with_suffix(".html"))
                            timings.append((time.time() - acc_t0, idx, e.keyword, row.status))
                            print(tag + format_result(row, now_epoch(), time_only), flush=True)
                        if q.empty():
                            break
                        nap(max(random.uniform(*sorted(args.delay)), args.min_time - (time.time() - acc_t0)))
                        count += 1
                        if args.restart_every > 0 and count % args.restart_every == 0 and not _STOP.is_set():
                            ctx, page = restart_browser(p, ctx, col, wargs)
                except KeyboardInterrupt:
                    state_info["stopped"] = True
                finally:
                    try:
                        ctx.close()
                    except Exception:
                        pass
        except KeyboardInterrupt:
            state_info["stopped"] = True
        except BaseException as ex:   # SystemExit từ launch() cũng vào đây: luồng khác vẫn chạy tiếp
            with lock:
                print("%sLuồng dừng do lỗi: %s: %s" % (tag, type(ex).__name__, str(ex)[:200]), flush=True)

    threads = []
    for w, prof in enumerate(profiles, 1):
        t = threading.Thread(target=worker, args=(w, prof), daemon=True)
        threads.append(t)
        t.start()
        if w < nw:
            time.sleep(2.0)      # so le việc mở Chrome để khỏi giật máy
    try:
        while any(t.is_alive() for t in threads):
            time.sleep(0.3)
    except KeyboardInterrupt:
        _STOP.set()
        state_info["stopped"] = True
        print("\nĐã dừng theo yêu cầu, đang đóng các cửa sổ... Kết quả đã lưu trong thư mục kết quả.")
        for t in threads:
            t.join(timeout=15)
    finally:
        try:
            save_cache(state_path, state)
        except Exception:
            pass
    return state_info["stopped"]


def run(args) -> int:
    if sync_playwright is None:
        sys.exit("Chưa cài Playwright. Chạy:\n  pip install playwright\n  playwright install chromium")

    global SO_WEB_ID, SORT_MODE
    SO_WEB_ID = args.web_id
    SORT_MODE = getattr(args, "sort", "default")
    if getattr(args, "turbo", False):
        args.fast = args.card_only = args.no_name_lookup = args.no_stats_lookup = args.no_drive = True
    time_only = bool(getattr(args, "time_only", False))
    if time_only:
        args.fast, args.card_only, args.no_stats_lookup, args.stats_max = True, False, True, 0
        print("[time-only] Chỉ lấy giờ đăng + tên tác giả (chỉ mở trang cá nhân), xếp theo giờ đăng mới nhất.")
    if getattr(args, "workers", 0) <= 0:
        args.workers = 2 if time_only else 1
    entries = parse_input(resolve_input(args.input))
    if not entries:
        sys.exit("File không có tài khoản nào.")
    print("Chỉ chạy các link trong: %s" % resolve_input(args.input))
    folder = Path(args.dir)
    folder.mkdir(parents=True, exist_ok=True)          # đã có thì dùng luôn
    stamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    txt_path = folder / ("%s_%s.txt" % (Path(args.out).name, stamp))
    cache = {}                                          # kết quả lần chạy này (mỗi lần làm lại từ đầu)
    Path(args.profile).mkdir(parents=True, exist_ok=True)
    state_path = Path(args.profile) / "tien_do.json"   # nhớ sec_uid giữa các lần chạy (nằm ngoài thư mục kết quả)
    state = load_cache(state_path)
    print("Kết quả lần chạy này lưu vào: %s" % txt_path.with_suffix(".html"))
    drive = DriveUploader(args.drive_folder, args.drive_creds)
    if not args.no_drive:
        drive.connect()
    print("Giờ máy: %s (UTC%s) - nếu sai so với giờ thật thì 'cách đây' sẽ sai" % (
        datetime.now().strftime("%Y-%m-%d %H:%M:%S"), datetime.now().astimezone().strftime("%z")))

    todo = []
    for idx, e in enumerate(entries, 1):
        if idx < args.start:
            continue
        todo.append((idx, e))
    if args.limit > 0:
        todo = todo[:args.limit]

    print("Danh sách: %d tài khoản | cần kiểm tra lần này: %d" % (len(entries), len(todo)))
    interrupted = False
    timings: list = []          # (giây, STT, tên, trạng thái) - để cuối lần chạy chỉ ra tài khoản nào chậm
    run_t0 = time.time()
    if todo:
        avg = max((args.delay[0] + args.delay[1]) / 2 + 2.5, args.min_time) / max(1, min(args.workers, len(todo)))
        print("Ước tính ~%d phút (~%d giây/tài khoản tính cả các luồng). Có thể nhấn Ctrl+C bất cứ lúc nào, "
              "tiến độ đã được lưu." % (max(1, round(len(todo) * avg / 60)), round(avg)))
        if args.workers > 1:
            interrupted = run_parallel(args, todo, entries, state, cache, txt_path, state_path, drive, timings, time_only)
        else:
            with sync_playwright() as p:
                ctx = launch(p, args)
                try:
                    page = ctx.pages[0] if ctx.pages else ctx.new_page()
                    col = Collector()
                    page.on("response", col.on_response)
                    args_ref.load_all = args.load_all
                    if not args.load_all:
                        block_heavy(page)
                    ensure_login(ctx, page, args)
                    for n, (idx, e) in enumerate(todo, 1):
                        print("\n[%d/%d | STT %d] %s" % (n, len(todo), idx, e.keyword), flush=True)
                        acc_t0 = time.time()
                        try:
                            row = check_entry(page, col, e, state.get(e.url), args,
                                              reuse=e.url not in cache)
                        except KeyboardInterrupt:
                            raise
                        except Exception as ex:
                            if is_closed_error(ex):
                                print("  Cửa sổ trình duyệt đã bị đóng -> dừng. Kết quả đã lưu trong thư mục kết quả.")
                                interrupted = True
                                break
                            raise
                        row.seq, row.total, row.took = n, len(todo), time.time() - acc_t0
                        cache[e.url] = row
                        state[e.url] = row
                        if n % max(1, args.save_every) == 0:
                            save_cache(state_path, state)
                        save_txt(entries, cache, txt_path, args.trend_days, time_only)   # ghi lại sau mỗi tài khoản (Ctrl+C vẫn còn kết quả)
                        if drive.ok and args.drive_every > 0 and n % args.drive_every == 0:
                            drive.upload(txt_path.with_suffix(".html"))
                        free_memory(page)
                        took = time.time() - acc_t0
                        timings.append((took, idx, e.keyword, row.status))
                        print(format_result(row, now_epoch(), time_only), flush=True)
                        if n < len(todo):
                            # (v27) mỗi tài khoản tối thiểu --min-time giây (tính từ lúc bắt đầu tài khoản)
                            wait = max(random.uniform(*sorted(args.delay)),
                                       args.min_time - (time.time() - acc_t0))
                            if wait > 0:
                                time.sleep(wait)
                            if args.restart_every > 0 and n % args.restart_every == 0:
                                ctx, page = restart_browser(p, ctx, col, args)
                except KeyboardInterrupt:
                    interrupted = True
                    print("\nĐã dừng theo yêu cầu. Kết quả đã lưu trong thư mục kết quả.")
                finally:
                    try:
                        save_cache(state_path, state)
                    except Exception:
                        pass
                    try:
                        ctx.close()
                    except Exception:
                        pass
    else:
        print("Không có tài khoản nào để kiểm tra (xem --start).")

    save_txt(entries, cache, txt_path, args.trend_days, time_only)
    drive.upload(txt_path.with_suffix(".html"))
    if drive.ok and not args.keep_old_drive:
        if args.limit > 0 or args.start > 1:
            print("[Drive] Lần chạy một phần (--limit/--start) nên KHÔNG xóa file cũ trên Drive.")
        else:
            n_old = drive.cleanup_old(Path(args.out).name)
            if n_old:
                print("[Drive] Đã chuyển %d file kết quả cũ vào thùng rác trên Drive." % n_old)
    sk = clock_skew()
    if sk:
        print("\n[!] Đồng hồ máy tính %s %.1f giờ so với máy chủ Douyin -> đã tự hiệu chỉnh khi tính 'cách đây'.\n"
              "    Nên chỉnh lại ngày giờ + múi giờ Windows (bật 'Set time automatically')."
              % ("chậm hơn" if sk > 0 else "nhanh hơn", abs(sk) / 3600))
    if timings:
        total = time.time() - run_t0
        print("\nTổng thời gian: %.0f giây cho %d tài khoản (TB %.1f giây/tài khoản)."
              % (total, len(timings), sum(t[0] for t in timings) / len(timings)))
        slow = sorted(timings, reverse=True)[:5]
        if slow[0][0] > 10:
            print("Chậm nhất (thường là tài khoản riêng tư / bị khóa / không có bài -> chờ hết thời gian):")
            for took, idx, kw, st in slow:
                print("   %5.1fs  STT %d  %s  [%s]" % (took, idx, kw, st))
    print("\nĐã ghi: %s (mở file .html bằng trình duyệt, bấm tên để chép)" % txt_path.with_suffix(".html"))
    return 130 if interrupted else 0


def main(argv=None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    return run(build_parser().parse_args(argv))


if __name__ == "__main__":
    sys.exit(main())

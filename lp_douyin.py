#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
lp_douyin.py - Bản Lightpanda của script Douyin, nói chuyện CDP trực tiếp qua websocket (KHÔNG dùng Playwright).

So với bản Playwright: không còn tiến trình Node (mỗi luồng tiết kiệm ~100MB RAM), khởi động nhanh hơn.
Đặt CÙNG THƯ MỤC với doyinskibidi3_fixed_v28_drive.py (file này import lại các hàm xử lý/ghi HTML từ đó).

Cài:   pip install websocket-client
Chạy:  python lp_douyin.py link_unique.txt --workers 3 --no-spawn
"""
from __future__ import annotations

import argparse
import base64
import json
import queue
import random
import socket
import subprocess
import sys
import threading
import time
import types
from datetime import datetime
from pathlib import Path

import doyinskibidi3_fixed_v28_drive as d

try:
    import websocket   # pip install websocket-client
except ImportError:
    sys.exit("Chưa cài websocket-client:  pip install websocket-client")

# Lightpanda từ chối UA có chữ "Mozilla" nên dùng UA iPhone không có chữ đó
LP_UA = ("(iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 "
         "(KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1")

STOP = threading.Event()


class CDPClosed(Exception):
    """Mất kết nối tới Lightpanda."""


class CDP:
    """Client CDP tối giản, đồng bộ: gửi lệnh, đọc tin nhắn, chuyển sự kiện cho on_event."""

    def __init__(self, port: int):
        self.ws = websocket.create_connection("ws://127.0.0.1:%d" % port, timeout=10, suppress_origin=True)
        self.n = 0
        self.sid = None
        self.on_event = None

    def close(self) -> None:
        try:
            self.ws.close()
        except Exception:
            pass

    def _recv(self, timeout: float):
        self.ws.settimeout(timeout)
        try:
            raw = self.ws.recv()
        except websocket.WebSocketTimeoutException:
            return None
        except (websocket.WebSocketException, OSError) as ex:
            raise CDPClosed(str(ex))
        if not raw:
            raise CDPClosed("kết nối đóng")
        try:
            return json.loads(raw)
        except ValueError:
            return None

    def _dispatch(self, m: dict) -> None:
        if "method" in m and self.on_event:
            try:
                self.on_event(m["method"], m.get("params") or {})
            except Exception:
                pass

    def call(self, method: str, params=None, session: bool = True, timeout: float = 10.0) -> dict:
        self.n += 1
        i = self.n
        msg = {"id": i, "method": method, "params": params or {}}
        if session and self.sid:
            msg["sessionId"] = self.sid
        try:
            self.ws.send(json.dumps(msg))
        except (websocket.WebSocketException, OSError) as ex:
            raise CDPClosed(str(ex))
        t0 = time.time()
        while True:
            left = timeout - (time.time() - t0)
            if left <= 0:
                raise TimeoutError(method)
            m = self._recv(min(left, 1.0))
            if m is None:
                continue
            if m.get("id") == i:
                if "error" in m:
                    raise RuntimeError("%s: %s" % (method, (m["error"] or {}).get("message", "")))
                return m.get("result") or {}
            self._dispatch(m)

    def pump(self, dur: float) -> None:
        """Đọc và chuyển sự kiện trong `dur` giây."""
        end = time.time() + dur
        while True:
            left = end - time.time()
            if left <= 0:
                return
            m = self._recv(min(left, 0.1))
            if m is not None:
                self._dispatch(m)

    def open_page(self) -> None:
        """Tạo context + tab mới giả lập điện thoại và bật Network."""
        ctx = {}
        try:
            r = self.call("Target.createBrowserContext", session=False)
            if r.get("browserContextId"):
                ctx = {"browserContextId": r["browserContextId"]}
        except CDPClosed:
            raise
        except Exception:
            pass
        attached = []

        def ev(method, p):
            if method == "Target.attachedToTarget" and p.get("sessionId"):
                attached.append(p["sessionId"])
        self.on_event = ev
        tid = self.call("Target.createTarget", dict(url="about:blank", **ctx), session=False)["targetId"]
        self.pump(0.1)
        try:
            self.sid = self.call("Target.attachToTarget", {"targetId": tid, "flatten": True}, session=False)["sessionId"]
        except CDPClosed:
            raise
        except Exception:
            if not attached:
                raise
            self.sid = attached[-1]
        self.on_event = None
        self.call("Network.enable")
        for method, params in (("Emulation.setUserAgentOverride", {"userAgent": LP_UA}),
                               ("Network.setUserAgentOverride", {"userAgent": LP_UA}),
                               ("Emulation.setDeviceMetricsOverride",
                                {"width": 390, "height": 844, "deviceScaleFactor": 1, "mobile": True})):
            try:
                self.call(method, params, timeout=5)
            except CDPClosed:
                raise
            except Exception:
                pass


class Resp:
    """Giả lập đối tượng response của Playwright đủ cho d.Collector (url, headers, request.resource_type, json(), text())."""

    def __init__(self, cdp: CDP, rid: str, url: str, headers: dict, rtype: str):
        self._cdp, self._rid, self._body = cdp, rid, None
        self.url, self.headers = url, headers
        self.request = types.SimpleNamespace(resource_type=rtype)

    def text(self) -> str:
        if self._body is None:
            last = None
            for _ in range(3):
                try:
                    r = self._cdp.call("Network.getResponseBody", {"requestId": self._rid}, timeout=5)
                    b = r.get("body") or ""
                    if r.get("base64Encoded"):
                        b = base64.b64decode(b).decode("utf-8", "replace")
                    self._body = b
                    break
                except CDPClosed:
                    raise
                except Exception as ex:
                    last = ex
                    self._cdp.pump(0.05)
            if self._body is None:
                raise last or RuntimeError("không đọc được body")
        return self._body

    def json(self):
        return json.loads(self.text())


def wait_port(port: int, timeout: float = 60.0) -> bool:
    t0 = time.time()
    while time.time() - t0 < timeout and not STOP.is_set():
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return True
        except OSError:
            time.sleep(0.2)
    return False


def get_html(cdp: CDP) -> str:
    try:
        r = cdp.call("Runtime.evaluate", {"expression": "document.documentElement.outerHTML",
                                          "returnByValue": True}, timeout=10)
        return (r.get("result") or {}).get("value") or ""
    except CDPClosed:
        raise
    except Exception:
        return ""


def check(cdp: CDP, col: d.Collector, e: d.Entry, args) -> d.Row:
    row = d.Row(key=e.url, keyword=e.keyword, name=e.name,
                checked_at=datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
    if not e.sec_uid:
        row.status = d.ST_ERROR
        row.note = "bản Lightpanda chỉ nhận link /user/<sec_uid> (không tìm theo từ khóa)"
        return row
    sec = e.sec_uid
    row.sec_uid, row.match, row.confident = sec, "Link trực tiếp", True
    col.reset()
    col.profile_hint, col.mobile_html = {}, ""
    try:
        cdp.call("Page.navigate", {"url": "https://m.douyin.com/share/user/%s%s" % (sec, d.MOBILE_QS)}, timeout=30)
    except CDPClosed:
        raise
    except Exception:
        pass   # hết giờ/lỗi điều hướng: vẫn chờ dữ liệu như bản cũ
    data = None
    t0 = time.time()
    while time.time() - t0 < args.timeout and not STOP.is_set():
        cdp.pump(0.1)
        col.drain()
        for url, dt in col.posts:
            if "/aweme/post/" in url and sec in url and isinstance(dt, dict) and "aweme_list" in dt:
                data = dt
                break
        if data is not None or col.verify_required:
            break
    if col.verify_required and data is None:
        row.status, row.note = d.ST_ERROR, "Douyin yêu cầu captcha (Lightpanda không giải được)"
        return row
    html = get_html(cdp)
    hint = d.parse_profile_html(html, sec)
    row.nickname, row.douyin_id, row.followers = hint["nickname"], hint["douyin_id"], hint["followers"]
    if data is None:
        st, why = d.classify_page(html)
        row.status = st or d.ST_ERROR
        row.note = why or "Không nhận được danh sách bài đăng (Lightpanda chưa chạy được JS của trang?)"
        return row
    info = d.summarize_posts(data.get("aweme_list") or [], args.only_video)
    if not info:
        row.status, row.note = d.ST_NO_VIDEO, "Danh sách bài đăng trống"
        return row
    row.status, row.latest_ts, row.kind = d.ST_OK, info["ts"], info["kind"]
    row.aweme_id, row.desc = info["aweme_id"], info["desc"]
    row.likes, row.shares, row.saves = info["likes"], info["shares"], info["saves"]
    if not row.nickname:
        row.note = "không lấy được tên tài khoản"
    return row


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", nargs="?")
    ap.add_argument("-o", "--out", default="ketqua_douyin")
    ap.add_argument("--dir", default="doyin")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--min-time", type=float, default=3.0, help="giây tối thiểu mỗi tài khoản (mỗi luồng)")
    ap.add_argument("--delay", type=float, nargs=2, default=[0.2, 0.5])
    ap.add_argument("--timeout", type=float, default=15.0, help="giây chờ API bài đăng")
    ap.add_argument("--max-hours", type=float, default=12.0)
    ap.add_argument("--sort", choices=["default", "time", "likes", "both"], default="time")
    ap.add_argument("--only-video", action="store_true")
    ap.add_argument("--lp-path", default="lightpanda", help="đường dẫn file lightpanda")
    ap.add_argument("--port", type=int, default=9222, help="cổng đầu tiên (luồng k dùng port+k-1)")
    ap.add_argument("--no-spawn", action="store_true", help="không tự bật lightpanda (bạn đã bật sẵn)")
    ap.add_argument("--no-drive", action="store_true", help="không tải kết quả lên Google Drive")
    ap.add_argument("--keep-old-drive", action="store_true", help="không xóa (vào thùng rác) file kết quả cũ trên Drive")
    ap.add_argument("--drive-folder", default="Douyin", help="tên thư mục trên Drive (chưa có thì tự tạo)")
    ap.add_argument("--drive-creds", default="credentials.json", help="file OAuth của Google")
    args = ap.parse_args()

    d.MAX_HOURS, d.SORT_MODE = args.max_hours, args.sort
    entries = d.parse_input(d.resolve_input(args.input))
    todo = [(i, e) for i, e in enumerate(entries, 1) if i >= args.start]
    if args.limit > 0:
        todo = todo[:args.limit]
    if not todo:
        sys.exit("Không có tài khoản nào để kiểm tra.")
    folder = Path(args.dir)
    folder.mkdir(parents=True, exist_ok=True)
    txt_path = folder / ("%s_%s.txt" % (Path(args.out).name, datetime.now().strftime("%Y-%m-%d_%H-%M-%S")))
    print("Kết quả: %s" % txt_path.with_suffix(".html"))
    drive = d.DriveUploader(args.drive_folder, args.drive_creds)
    if not args.no_drive:
        drive.connect()   # lần đầu mở trình duyệt xin quyền, các lần sau dùng token.json

    q: queue.Queue = queue.Queue()
    for n, (i, e) in enumerate(todo, 1):
        q.put((n, i, e))
    total, cache, lock = len(todo), {}, threading.Lock()
    nw = max(1, min(args.workers, total))
    procs: list = []

    def worker(w: int) -> None:
        port = args.port + w - 1
        tag = "[L%d] " % w
        if not args.no_spawn:
            procs.append(subprocess.Popen([args.lp_path, "serve", "--host", "127.0.0.1", "--port", str(port)],
                                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))
        col = d.Collector()
        holder = {"cdp": None}

        def connect() -> bool:
            if holder["cdp"]:
                holder["cdp"].close()
                holder["cdp"] = None
            if not wait_port(port, 60 if holder.get("first", True) else 10):
                print("%sKhông kết nối được lightpanda ở cổng %d" % (tag, port), flush=True)
                return False
            holder["first"] = False
            cdp = CDP(port)

            def on_event(method, p):
                if method == "Network.responseReceived":
                    r = p.get("response") or {}
                    hdr = {str(k).lower(): v for k, v in (r.get("headers") or {}).items()}
                    col.on_response(Resp(cdp, p.get("requestId"), r.get("url", ""), hdr,
                                         str(p.get("type", "")).lower()))
            cdp.open_page()
            cdp.on_event = on_event
            holder["cdp"] = cdp
            return True

        def run_check(e):
            try:
                return check(holder["cdp"], col, e, args)
            except CDPClosed:
                if STOP.is_set() or not connect():
                    raise
                return check(holder["cdp"], col, e, args)

        try:
            if not connect():
                return
            while not STOP.is_set():
                try:
                    n, idx, e = q.get_nowait()
                except queue.Empty:
                    break
                t0 = time.time()
                try:
                    row = run_check(e)
                except Exception as ex:
                    row = d.Row(key=e.url, keyword=e.keyword, name=e.name, status=d.ST_ERROR,
                                note="%s: %s" % (type(ex).__name__, str(ex)[:150]))
                if row.status == d.ST_ERROR and "bài đăng" in row.note:   # lỗi thoáng qua: thử lại 1 lần
                    try:
                        row = run_check(e)
                    except Exception:
                        pass
                if row.status == d.ST_OK and row.douyin_id:   # hiển thị Douyin ID thay cho tên
                    row.nickname = row.douyin_id
                row.seq, row.total, row.took = n, total, time.time() - t0
                with lock:
                    cache[e.url] = row
                    d.save_txt(entries, cache, txt_path, 30, True)
                    print(tag + d.format_result(row, d.now_epoch(), True), flush=True)
                if not q.empty():
                    time.sleep(max(random.uniform(*sorted(args.delay)), args.min_time - (time.time() - t0)))
        except Exception as ex:
            print("%sLuồng dừng: %s: %s" % (tag, type(ex).__name__, str(ex)[:200]), flush=True)
        finally:
            if holder["cdp"]:
                holder["cdp"].close()

    threads = [threading.Thread(target=worker, args=(w,), daemon=True) for w in range(1, nw + 1)]
    t_start = time.time()
    try:
        for t in threads:
            t.start()
            time.sleep(0.1)
        while any(t.is_alive() for t in threads):
            time.sleep(0.3)
    except KeyboardInterrupt:
        STOP.set()
        print("\nĐã dừng theo yêu cầu.")
        for t in threads:
            t.join(timeout=10)
    finally:
        for pr in procs:
            try:
                pr.terminate()
            except Exception:
                pass
        d.save_txt(entries, cache, txt_path, 30, True)
    if drive.ok:
        drive.upload(txt_path.with_suffix(".html"))
        if not args.keep_old_drive and args.limit == 0 and args.start == 1 and not STOP.is_set():
            n_old = drive.cleanup_old(Path(args.out).name)
            if n_old:
                print("[Drive] Đã chuyển %d file kết quả cũ vào thùng rác." % n_old)
        print("[Drive] Đã tải kết quả lên thư mục Drive: %s" % args.drive_folder)
    print("\nXong %d/%d tài khoản trong %.0f giây. Mở: %s" % (len(cache), total, time.time() - t_start,
                                                          txt_path.with_suffix(".html")))
    return 0


if __name__ == "__main__":
    sys.exit(main())

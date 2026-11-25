#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
coopchat.py - Ứng dụng Chat THẬT chạy trên MẠNG TRUYỀN THÔNG CỘNG TÁC, có giao diện web.

Cách chạy (chỉ cần Python 3.8+, KHÔNG cần cài thêm thư viện):
    python coopchat.py
Trình duyệt sẽ tự động mở. Mọi thao tác sau đó đều làm trên giao diện.

  - Mỗi lần chạy là MỘT NÚT. Chạy 3 lần (3 cửa sổ trình duyệt) để có Alice, Bob, Carol.
  - Hai máy khác nhau: ở màn hình "Tham gia", nhập thêm địa chỉ của máy kia (vd 192.168.1.20:9001).
    Chỉ cần biết MỘT nút, các nút còn lại tự tìm thấy nhau (lan truyền địa chỉ qua gói HELLO).
  - Nút nào không đang trò chuyện sẽ TỰ ĐỘNG làm relay giúp các nút khác.

Các thẻ [COOP-x] trong mã đánh dấu chỗ ứng dụng truyền thông cộng tác:
    [COOP-A] Quảng bá - mọi nút trong vùng phủ cùng nghe một lần phát.
    [COOP-B] Chuyển tiếp tăng dần - relay chỉ phát khi chưa thấy ACK.
    [COOP-C] DF (Decode-and-Forward) - relay chỉ chuyển tiếp khi tự giải mã đúng (CRC + SNR).
    [COOP-D] Chọn relay phân tán bằng bộ đếm giờ (Bletsas 2006) + Jitter tránh va chạm.
    [COOP-E] Triệt tiêu (Suppression) - relay im lặng khi thấy ACK hoặc relay khác đã phát.
    [COOP-F] ARQ đầu cuối ở nguồn, timeout dài hơn để chờ relay.
    [COOP-G] Vai trò động - nút nào cũng có thể làm nguồn, đích hoặc relay.
    [BASE]   Chế độ "Gửi thẳng" (không cộng tác) dùng để so sánh.
"""
from __future__ import annotations

import argparse
import heapq
import itertools
import json
import math
import queue
import random
import re
import socket
import sys
import threading
import time
import webbrowser
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

# ----------------------------------------------------------------------------
# Tham số giao thức (giây; nhân với hệ số cfg["slow"] khi chạy chậm để trình diễn)
# ----------------------------------------------------------------------------
LINK_DELAY = 0.020      # Thời gian một gói "bay" trong kênh
RELAY_WAIT = 0.050      # Relay chờ ACK từng này trước khi giúp
SEL_SPAN = 0.060        # Độ trải của bộ đếm giờ chọn relay
T_DIRECT = 0.100        # Timeout ARQ khi gửi thẳng
T_COOP = 0.230          # Timeout ARQ khi cộng tác (phải chờ relay)
HELLO_EVERY = 1.0
PEER_TTL = 4.0
MAX_TEXT = 400
NAMES = ["Alice", "Bob", "Carol", "Dan", "Eve", "Frank", "Grace", "Heidi"]

DEFAULT_CFG: Dict[str, Any] = dict(snr_db=6.0, alpha=3.0, rate=1.0, coop=True, select="opp",
                                   max_retx=3, slow=1.0, ver=0, by="")


def lan_ip() -> str:
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


def default_pos(name: str) -> Tuple[float, float]:
    if name.lower() == "alice":
        return (0.0, 0.0)
    if name.lower() == "bob":
        return (1.0, 0.0)
    h = zlib.crc32(name.encode("utf-8"))
    return (0.3 + (h % 400) / 1000.0, ((h >> 10) % 700) / 1000.0 - 0.35)


def crc_of(src: str, dst: str, seq: int, text: str) -> int:
    return zlib.crc32(f"{src}|{dst}|{seq}|{text}".encode("utf-8")) & 0xFFFFFFFF


def db(x: float) -> float:
    return 10.0 * math.log10(max(x, 1e-12))


# ----------------------------------------------------------------------------
# Bộ lập lịch (hẹn giờ có thể huỷ)
# ----------------------------------------------------------------------------
class Scheduler(threading.Thread):
    def __init__(self) -> None:
        super().__init__(daemon=True)
        self.cv = threading.Condition()
        self.heap: List[Tuple[float, int, Any]] = []
        self.cnt = itertools.count()
        self.cancelled: Set[int] = set()
        self.alive = True

    def at(self, when: float, fn: Any) -> int:
        h = next(self.cnt)
        with self.cv:
            heapq.heappush(self.heap, (when, h, fn))
            self.cv.notify()
        return h

    def cancel(self, h: Optional[int]) -> None:
        if h is None:
            return
        with self.cv:
            self.cancelled.add(h)

    def stop(self) -> None:
        with self.cv:
            self.alive = False
            self.cv.notify()

    def run(self) -> None:
        while True:
            with self.cv:
                fn: Optional[Any] = None
                while self.alive:
                    if not self.heap:
                        self.cancelled.clear()
                        self.cv.wait()
                        continue
                    when, h, f = self.heap[0]
                    if h in self.cancelled:
                        heapq.heappop(self.heap)
                        self.cancelled.discard(h)
                        continue
                    now = time.time()
                    if when <= now:
                        heapq.heappop(self.heap)
                        fn = f
                        break
                    self.cv.wait(when - now)
                if not self.alive:
                    return
            try:
                if fn is not None:
                    fn()
            except Exception as e:
                print("[scheduler]", repr(e), file=sys.stderr)


# ----------------------------------------------------------------------------
# Nút mạng
# ----------------------------------------------------------------------------
class Node:
    def __init__(self, app: "App", name: str, udp_port: int, seeds: Set[Tuple[str, int]],
                 pos: Optional[Sequence[float]] = None) -> None:
        self.app = app
        self.name = name
        self.udp_port = udp_port
        self.lan = lan_ip()
        self.lock = threading.RLock()
        self.cfg: Dict[str, Any] = dict(DEFAULT_CFG)
        self.pos: List[float] = list(pos or default_pos(name))
        self.peers: Dict[str, Dict[str, Any]] = {}
        self.known: Set[Tuple[str, int]] = set(seeds)
        self.self_addrs: Set[Tuple[str, int]] = {("127.0.0.1", udp_port), (self.lan, udp_port)}
        self.known -= self.self_addrs
        self.rng = random.Random()
        self.seq = 0
        self.pending: Dict[int, Dict[str, Any]] = {}
        self.msgs: List[Dict[str, Any]] = []
        self.received: Dict[Tuple[str, int], Dict[str, Any]] = {}
        self.relay_buf: Dict[Tuple[str, int, int], Dict[str, Any]] = {}
        self.relayed_keys: Set[Tuple[str, int]] = set()
        self.acked: Dict[Tuple[str, int], float] = {}
        self.logs: List[Dict[str, Any]] = []
        self.flows: List[Dict[str, Any]] = []
        self.flow_id = 0
        self.relay_stats: Dict[str, int] = dict(heard=0, relayed=0, helped=0, suppressed=0)
        self.bench: Dict[str, Any] = dict(running=False, done=0, total=0, runs=[])
        self.running = True
        self.sched = Scheduler()
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("0.0.0.0", udp_port))
        if sys.platform == "win32":
            try:
                self.sock.ioctl(socket.SIO_UDP_CONNRESET, False)  # type: ignore[attr-defined]
            except Exception:
                pass

    def T(self, x: float) -> float:
        return x * float(self.cfg["slow"])

    def notify(self) -> None:
        self.app.dirty = True

    def log(self, kind: str, msg: str) -> None:
        with self.lock:
            self.logs.append(dict(t=time.time(), k=kind, m=msg))
            del self.logs[:-300]
        self.notify()

    def flow(self, kind: str, frm: str, to: str, lost: Optional[bool]) -> None:
        with self.lock:
            self.flow_id += 1
            self.flows.append(dict(id=self.flow_id, k=kind, f=frm, to=to, lost=lost, t=time.time()))
            del self.flows[:-80]
        self.notify()

    def start(self) -> None:
        self.sched.start()
        threading.Thread(target=self._rx_loop, daemon=True).start()
        threading.Thread(target=self._hello_loop, daemon=True).start()
        self.log("net", f"{self.name} sẵn sàng tại {self.lan}:{self.udp_port}")

    def _channel(self, tx: str) -> Optional[Tuple[float, float, float]]:
        """[KÊNH] SNR tức thời từ nút phát `tx` tới nút này: gamma = gbar * Exp(1)."""
        with self.lock:
            p = self.peers.get(tx)
            if not p:
                return None
            d = max(math.hypot(p["pos"][0] - self.pos[0], p["pos"][1] - self.pos[1]), 0.1)
            gbar = 10 ** (self.cfg["snr_db"] / 10.0) * d ** (-self.cfg["alpha"])
            psi = 2 ** self.cfg["rate"] - 1
        return gbar * self.rng.expovariate(1.0), gbar, psi

    def _gbar_between(self, a_pos: Sequence[float], b_pos: Sequence[float]) -> float:
        d = max(math.hypot(a_pos[0] - b_pos[0], a_pos[1] - b_pos[1]), 0.1)
        return 10 ** (self.cfg["snr_db"] / 10.0) * d ** (-self.cfg["alpha"])

    def _sendto(self, pkt: Dict[str, Any], addr: Tuple[str, int]) -> None:
        try:
            self.sock.sendto(json.dumps(pkt, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), addr)
        except OSError:
            pass

    def _send(self, pkt: Dict[str, Any], name: str) -> None:
        with self.lock:
            p = self.peers.get(name)
            addr = p["addr"] if p else None
        if addr:
            self._sendto(pkt, addr)

    def _adv_list(self) -> List[str]:
        out: List[str] = []
        for p in self.peers.values():
            ip, port = p["addr"]
            if ip.startswith("127."):
                ip = self.lan
            out.append(f"{ip}:{port}")
        return out

    def _hello_pkt(self) -> Dict[str, Any]:
        with self.lock:
            return dict(t="HELLO", n=self.name, p=self.udp_port, pos=self.pos,
                        cfg=self.cfg, peers=self._adv_list())

    def _hello_loop(self) -> None:
        while self.running:
            with self.lock:
                targets = set(self.known) | {p["addr"] for p in self.peers.values()}
            pkt = self._hello_pkt()
            for a in targets:
                self._sendto(pkt, a)
            time.sleep(HELLO_EVERY)

    def _rx_loop(self) -> None:
        while self.running:
            try:
                data, addr = self.sock.recvfrom(65535)
                pkt = json.loads(data.decode("utf-8"))
            except ConnectionResetError:
                continue
            except (ValueError, UnicodeDecodeError):
                continue
            except OSError:
                if not self.running:
                    break
                time.sleep(0.1)
                continue
            try:
                self._on_packet(pkt, addr)
            except Exception as e:
                print("[rx]", repr(e), file=sys.stderr)

    def _on_packet(self, pkt: Dict[str, Any], addr: Tuple[str, int]) -> None:
        t = pkt.get("t")
        if t == "HELLO":
            self._on_hello(pkt, addr)
        elif t == "CFG":
            self._adopt_cfg(pkt.get("cfg"))
        elif t in ("DATA", "RELAYED", "ACK"):
            self.sched.at(time.time() + self.T(LINK_DELAY), lambda p=pkt: self._on_air(p))

    def _on_hello(self, pkt: Dict[str, Any], addr: Tuple[str, int]) -> None:
        name, ip, port = pkt["n"], addr[0], int(pkt["p"])
        if name == self.name:
            with self.lock:
                self.self_addrs.add((ip, port))
                self.known.discard((ip, port))
            return
        new_addrs: List[Tuple[str, int]] = []
        with self.lock:
            fresh = name not in self.peers
            self.peers[name] = dict(addr=(ip, port), pos=tuple(pkt["pos"]), seen=time.time())
            self.known.add((ip, port))
            for s in pkt.get("peers", []):
                try:
                    h, p_str = s.rsplit(":", 1)
                    a = (h, int(p_str))
                except ValueError:
                    continue
                if a not in self.self_addrs and a not in self.known:
                    self.known.add(a)
                    new_addrs.append(a)
        self._adopt_cfg(pkt.get("cfg"))
        if fresh:
            self.log("net", f"{name} đã tham gia mạng ({ip}:{port})")
            self._sendto(self._hello_pkt(), (ip, port))
        for a in new_addrs:
            self._sendto(self._hello_pkt(), a)
        self.notify()

    def _adopt_cfg(self, c: Any) -> None:
        if not isinstance(c, dict):
            return
        with self.lock:
            if (c.get("ver", 0), c.get("by", "")) > (self.cfg["ver"], self.cfg["by"]):
                self.cfg = {**DEFAULT_CFG, **c}
                changed = True
            else:
                changed = False
        if changed:
            self.log("cfg", f"Cấu hình kênh được cập nhật bởi {c.get('by') or 'mạng'}")

    def set_cfg(self, upd: Dict[str, Any]) -> Dict[str, Any]:
        lim = dict(snr_db=(-10, 40), alpha=(1.5, 6), rate=(0.25, 4), max_retx=(0, 8), slow=(1, 50))
        with self.lock:
            c = dict(self.cfg)
            for k, (lo, hi) in lim.items():
                if k in upd:
                    try:
                        c[k] = type(DEFAULT_CFG[k])(min(hi, max(lo, float(upd[k]))))
                    except (TypeError, ValueError):
                        pass
            if "coop" in upd:
                c["coop"] = bool(upd["coop"])
            if upd.get("select") in ("opp", "avg"):
                c["select"] = upd["select"]
            c["ver"] = self.cfg["ver"] + 1
            c["by"] = self.name
            self.cfg = c
            addrs = {p["addr"] for p in self.peers.values()} | set(self.known)
        for a in addrs:
            self._sendto(dict(t="CFG", cfg=c), a)
        self.notify()
        return c

    def set_pos(self, x: float, y: float) -> None:
        with self.lock:
            self.pos = [max(-0.3, min(1.3, float(x))), max(-0.7, min(0.7, float(y)))]
            addrs = {p["addr"] for p in self.peers.values()}
        pkt = self._hello_pkt()
        for a in addrs:
            self._sendto(pkt, a)
        self.notify()

    def send_text(self, to: str, text: str, bench: bool = False
                  ) -> Tuple[Optional[Dict[str, Any]], Optional[threading.Event]]:
        text = (text or "").strip()[:MAX_TEXT]
        if not text:
            return None, None
        with self.lock:
            if to not in self.peers:
                return None, None
            self.seq += 1
            seq = self.seq
            rec = dict(id=f"{self.name}:{seq}", seq=seq, frm=self.name, to=to, text=text, ts=time.time(),
                       status="sending", path=None, attempts=0, delay_ms=None, bench=bench,
                       mode="coop" if self.cfg["coop"] else "direct")
            ev = threading.Event()
            if not bench:
                self.msgs.append(rec)
                del self.msgs[:-500]
            self.pending[seq] = dict(rec=rec, att=0, timer=None, ev=ev, t0=time.time())
        self._transmit(seq)
        return rec, ev

    def _transmit(self, seq: int) -> None:
        with self.lock:
            p = self.pending.get(seq)
            if not p:
                return
            rec = p["rec"]
            p["att"] += 1
            att = p["att"]
            rec["attempts"] = att
            coop = self.cfg["coop"]
            dst = rec["to"]
            pkt = dict(t="DATA", f=self.name, s=self.name, d=dst, q=seq, a=att, x=rec["text"],
                       c=crc_of(self.name, dst, seq, rec["text"]), b=1 if rec["bench"] else 0)
            targets = [dst] + ([n for n in self.peers if n not in (dst, self.name)] if coop else [])
            timeout = self.T(T_COOP if coop else T_DIRECT)
            p["timer"] = self.sched.at(time.time() + timeout, lambda s=seq, a=att: self._on_timeout(s, a))
        for n in targets:
            self._send(pkt, n)
            self.flow("DATA", self.name, n, None)
        if not rec["bench"]:
            extra = f", {len(targets) - 1} nút khác cùng nghe" if coop and len(targets) > 1 else ""
            self.log("send", f"Gửi #{seq} tới {dst} (lượt {att}{extra})")

    def _on_timeout(self, seq: int, att: int) -> None:
        with self.lock:
            p = self.pending.get(seq)
            if not p or p["att"] != att:
                return
            rec = p["rec"]
            if att >= int(self.cfg["max_retx"]) + 1:
                del self.pending[seq]
                rec["status"] = "failed"
                p["ev"].set()
                give_up = True
            else:
                give_up = False
        if give_up:
            self.log("fail", f"Không gửi được #{seq} sau {att} lượt")
        else:
            if not rec["bench"]:
                self.log("retx", f"Hết giờ #{seq} (lượt {att}), gửi lại")
            self._transmit(seq)

    def _on_air(self, pkt: Dict[str, Any]) -> None:
        t = pkt["t"]
        if t == "ACK":
            return self._on_ack(pkt)
        tx = pkt["f"]
        ch = self._channel(tx)
        if ch is None:
            return
        g, gbar, psi = ch
        src, dst, seq = pkt["s"], pkt["d"], pkt["q"]
        lost = g < psi
        self.flow(t, tx, self.name, lost)
        bench = bool(pkt.get("b"))
        if lost:
            if dst == self.name and not bench:
                self.log("lost", f"Mất gói từ {tx}: SNR {db(g):.1f} dB < ngưỡng {db(psi):.1f} dB")
            return
        if crc_of(src, dst, seq, pkt["x"]) != pkt["c"]:
            return
        if t == "DATA":
            if dst == self.name:
                self._deliver(pkt, tx)
            elif src != self.name:
                self._overhear(pkt, g, gbar)
        elif t == "RELAYED":
            if dst == self.name:
                self._deliver(pkt, tx)
            elif src != self.name:
                self._suppress(pkt)

    def _deliver(self, pkt: Dict[str, Any], tx: str) -> None:
        src, seq = pkt["s"], pkt["q"]
        bench = bool(pkt.get("b"))
        with self.lock:
            fresh = (src, seq) not in self.received
            if fresh:
                rec = dict(id=f"{src}:{seq}", seq=seq, frm=src, to=self.name, text=pkt["x"], ts=time.time(),
                           status="received", path="direct" if tx == src else tx, attempts=pkt["a"],
                           delay_ms=None, bench=bench)
                self.received[(src, seq)] = rec
                if not bench:
                    self.msgs.append(rec)
                    del self.msgs[:-500]
            coop = self.cfg["coop"]
            targets = [src] + ([n for n in self.peers if n not in (src, self.name)] if coop else [])
        if fresh and not bench:
            via = "trực tiếp" if tx == src else f"qua {tx}"
            self.log("recv", f"Nhận “{pkt['x'][:40]}” từ {src} {via}")
        ack = dict(t="ACK", f=self.name, s=src, d=self.name, q=seq, v=tx)
        for n in targets:
            self._send(ack, n)
            self.flow("ACK", self.name, n, None)

    def _on_ack(self, pkt: Dict[str, Any]) -> None:
        src, seq, via = pkt["s"], pkt["q"], pkt["v"]
        self.flow("ACK", pkt["f"], self.name, False)
        with self.lock:
            self.acked[(src, seq)] = time.time()
            if len(self.acked) > 400:
                cutoff = time.time() - 60
                self.acked = {k: v for k, v in self.acked.items() if v > cutoff}
            for key in [k for k in list(self.relay_buf.keys()) if k[0] == src and k[1] == seq]:
                self.sched.cancel(self.relay_buf.pop(key)["handle"])
                self.log_unlocked_later("ack", f"Thấy ACK #{seq} của {src}, huỷ chuyển tiếp")
            if via == self.name and (src, seq) in self.relayed_keys:
                self.relay_stats["helped"] += 1
                self.relayed_keys.discard((src, seq))
            p = self.pending.pop(seq, None) if src == self.name else None
            if p:
                self.sched.cancel(p["timer"])
                rec = p["rec"]
                rec["status"] = "delivered"
                rec["delay_ms"] = round((time.time() - p["t0"]) * 1000)
                rec["path"] = "direct" if via == self.name else via
                p["ev"].set()
        if p:
            if not p["rec"]["bench"]:
                how = "trực tiếp" if p["rec"]["path"] == "direct" else f"qua {p['rec']['path']}"
                self.log("ack", f"{p['rec']['to']} đã nhận #{seq} {how}, sau {p['rec']['delay_ms']} ms")
        self.notify()

    def log_unlocked_later(self, kind: str, msg: str) -> None:
        threading.Thread(target=self.log, args=(kind, msg), daemon=True).start()

    def _overhear(self, pkt: Dict[str, Any], g: float, gbar_sr: float) -> None:
        """[COOP-A][COOP-B][COOP-C][COOP-G] Nút ngoài cuộc nghe được DATA và quyết định có giúp không."""
        src, dst, seq, att = pkt["s"], pkt["d"], pkt["q"], pkt["a"]
        key = (src, seq, att)
        wait: float = 0.0          # khởi tạo sớm để Pylance luôn thấy kiểu float
        with self.lock:
            if not self.cfg["coop"] or (src, seq) in self.acked or key in self.relay_buf:
                return
            dp = self.peers.get(dst)
            if not dp:
                return
            gbar_rd = self._gbar_between(self.pos, dp["pos"])
            m = min(g if self.cfg["select"] == "opp" else gbar_sr, gbar_rd)
            # [COOP-D] thêm jitter ngẫu nhiên để tránh va chạm nếu 2 relay có chỉ số giống hệt nhau
            jitter = self.rng.uniform(0, 0.015)
            wait = self.T(RELAY_WAIT + SEL_SPAN / (1.0 + m) + jitter)
            h = self.sched.at(time.time() + wait, lambda k=key: self._relay_fire(k))
            self.relay_buf[key] = dict(handle=h, pkt=pkt)
            self.relay_stats["heard"] += 1
        if not pkt.get("b"):
            self.log("relay", f"Nghe được #{seq} của {src} gửi {dst} (SNR {db(g):.1f} dB), "
                              f"hẹn giờ giúp sau {wait * 1000:.0f} ms")

    def _relay_fire(self, key: Tuple[str, int, int]) -> None:
        """[COOP-B] Hết giờ mà chưa thấy ACK hay relay khác: chuyển tiếp bản đã giải mã tới D."""
        with self.lock:
            ent = self.relay_buf.pop(key, None)
            if not ent or (key[0], key[1]) in self.acked:
                return
            pkt = dict(ent["pkt"], t="RELAYED", f=self.name)
            targets = [n for n in self.peers if n != self.name]
            self.relay_stats["relayed"] += 1
            self.relayed_keys.add((key[0], key[1]))
        for n in targets:
            self._send(pkt, n)
            self.flow("RELAYED", self.name, n, None)
        if not pkt.get("b"):
            self.log("relay", f"Chuyển tiếp #{key[1]} của {key[0]} tới {pkt['d']}")

    def _suppress(self, pkt: Dict[str, Any]) -> None:
        """[COOP-E] Nghe thấy relay khác đã chuyển tiếp trước thì im lặng."""
        key = (pkt["s"], pkt["q"], pkt["a"])
        with self.lock:
            ent = self.relay_buf.pop(key, None)
            if ent:
                self.sched.cancel(ent["handle"])
                self.relay_stats["suppressed"] += 1
        if ent and not pkt.get("b"):
            self.log("relay", f"{pkt['f']} đã chuyển tiếp #{pkt['q']} trước, {self.name} giữ im lặng")

    def start_bench(self, to: str, n: int) -> bool:
        with self.lock:
            if self.bench["running"] or to not in self.peers:
                return False
            n = max(5, min(200, int(n)))
            self.bench.update(running=True, done=0, total=n)
        threading.Thread(target=self._bench_run, args=(to, n), daemon=True).start()
        return True

    def _bench_run(self, to: str, n: int) -> None:
        recs: List[Dict[str, Any]] = []
        cfg = dict(self.cfg)
        for i in range(n):
            rec, ev = self.send_text(to, f"đo thử {i + 1}/{n}", bench=True)
            if rec is None or ev is None:
                break
            ev.wait(timeout=self.T(T_COOP) * (int(cfg["max_retx"]) + 2) + 2)
            recs.append(rec)
            with self.lock:
                self.bench["done"] = i + 1
            self.notify()
            time.sleep(self.T(0.01))
        ok = [r for r in recs if r["status"] == "delivered"]
        delays = sorted(r["delay_ms"] for r in ok if r["delay_ms"] is not None)
        run: Dict[str, Any] = dict(mode="coop" if cfg["coop"] else "direct", snr=cfg["snr_db"], rate=cfg["rate"],
                   select=cfg["select"], n=len(recs),
                   delivered=len(ok) / len(recs) if recs else 0.0,
                   mean_ms=sum(delays) / len(delays) if delays else None,
                   p95_ms=delays[min(len(delays) - 1, int(0.95 * len(delays)))] if delays else None,
                   attempts=sum(r["attempts"] for r in recs) / len(recs) if recs else 0.0,
                   relayed=sum(1 for r in ok if r["path"] != "direct") / len(ok) if ok else 0.0)
        with self.lock:
            self.bench["running"] = False
            self.bench["runs"].append(run)
            del self.bench["runs"][:-12]
        self.log("net", f"Đo thử xong: {run['delivered'] * 100:.0f}% tin đến nơi "
                        f"({'cộng tác' if run['mode'] == 'coop' else 'gửi thẳng'})")

    def snapshot(self) -> Dict[str, Any]:
        now = time.time()
        with self.lock:
            psi = 2 ** self.cfg["rate"] - 1
            peers: List[Dict[str, Any]] = []
            for name, p in sorted(self.peers.items()):
                gbar = self._gbar_between(self.pos, p["pos"])
                peers.append(dict(name=name, addr=f"{p['addr'][0]}:{p['addr'][1]}", pos=list(p["pos"]),
                                  online=(now - p["seen"]) < PEER_TTL, q=math.exp(-psi / gbar)))
            keys = ("id", "frm", "to", "text", "ts", "status", "path", "attempts", "delay_ms", "mode")
            chat = [{k: r.get(k) for k in keys} for r in self.msgs[-300:]]
            sent = [r for r in self.msgs if r["frm"] == self.name]
            dl = [r for r in sent if r["status"] == "delivered"]
            fin = [r for r in sent if r["status"] != "sending"]
            stats = dict(sent=len(sent), delivered=len(dl), failed=len([r for r in sent if r["status"] == "failed"]),
                         mean_ms=(sum(r["delay_ms"] for r in dl if r["delay_ms"] is not None) / len(dl)) if dl else None,
                         relayed=(sum(1 for r in dl if r["path"] != "direct") / len(dl)) if dl else 0.0,
                         attempts=(sum(r["attempts"] for r in fin) / len(fin)) if fin else 0.0)
            flows = [dict(id=f["id"], k=f["k"], f=f["f"], to=f["to"], lost=f["lost"], age=int((now - f["t"]) * 1000))
                     for f in self.flows if now - f["t"] < 4]
            return dict(joined=True, me=dict(name=self.name, addr=f"{self.lan}:{self.udp_port}", pos=list(self.pos)),
                        cfg=dict(self.cfg), peers=peers, chat=chat, stats=stats, relay=dict(self.relay_stats),
                        bench=dict(running=self.bench["running"], done=self.bench["done"],
                                   total=self.bench["total"], runs=list(self.bench["runs"])),
                        logs=[dict(t=l["t"], k=l["k"], m=l["m"]) for l in self.logs[-120:]],
                        flows=flows, link=dict(delay=LINK_DELAY * self.cfg["slow"]), now=now)

    def stop(self) -> None:
        self.running = False
        self.sched.stop()
        try:
            self.sock.close()
        except OSError:
            pass


# ----------------------------------------------------------------------------
# Ứng dụng web (một nút + giao diện)
# ----------------------------------------------------------------------------
class App:
    def __init__(self, index: int) -> None:
        self.node: Optional[Node] = None
        self.index = index
        self.dirty = False
        self.subs: List[queue.Queue] = []
        self.sub_lock = threading.Lock()
        self.defaults: Dict[str, Any] = dict(name=NAMES[index % len(NAMES)], udp=9001 + index,
                                             peers=", ".join(f"127.0.0.1:{9001 + i}" for i in range(5)),
                                             lan=lan_ip())
        threading.Thread(target=self._pusher, daemon=True).start()

    def snapshot(self) -> Dict[str, Any]:
        if self.node:
            return self.node.snapshot()
        return dict(joined=False, defaults=self.defaults)

    def _pusher(self) -> None:
        last = 0.0
        while True:
            time.sleep(0.08)
            if self.dirty or time.time() - last > 1.0:
                self.dirty = False
                last = time.time()
                snap = self.snapshot()
                with self.sub_lock:
                    for q in self.subs:
                        try:
                            q.put_nowait(snap)
                        except queue.Full:
                            try:
                                q.get_nowait()
                                q.put_nowait(snap)
                            except (queue.Empty, queue.Full):
                                pass

    def join(self, name: Any, udp: Any, peers: Any) -> Dict[str, Any]:
        if self.node:
            return dict(ok=False, error="Bạn đã tham gia mạng rồi.")
        name = str(name or "").strip()
        if not re.fullmatch(r"[\w\-]{1,16}", name):
            return dict(ok=False, error="Tên chỉ gồm chữ, số, dấu gạch, tối đa 16 ký tự.")
        try:
            udp_int = int(udp)
            assert 1024 <= udp_int <= 65535
        except (TypeError, ValueError, AssertionError):
            return dict(ok=False, error="Cổng UDP phải là số từ 1024 đến 65535.")
        seeds: Set[Tuple[str, int]] = set()
        for tok in re.split(r"[,\s;]+", str(peers or "")):
            if not tok:
                continue
            try:
                h, p = tok.rsplit(":", 1)
                seeds.add((h, int(p)))
            except ValueError:
                return dict(ok=False, error=f"Địa chỉ “{tok}” không đúng dạng IP:cổng.")
        try:
            node = Node(self, name, udp_int, seeds)
        except OSError:
            return dict(ok=False, error=f"Cổng UDP {udp_int} đang được dùng. Hãy chọn cổng khác.")
        self.node = node
        node.start()
        self.dirty = True
        return dict(ok=True)


APP: Optional[App] = None


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.0"

    def log_message(self, format: str, *args: Any) -> None:  # khớp signature base class
        pass

    def _json(self, obj: Dict[str, Any], code: int = 200) -> None:
        b = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(b)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(b)

    def do_GET(self) -> None:
        assert APP is not None
        if self.path in ("/", "/index.html"):
            b = INDEX_HTML.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(b)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(b)
        elif self.path == "/api/state":
            self._json(APP.snapshot())
        elif self.path == "/events":
            self._sse()
        else:
            self._json(dict(ok=False, error="not found"), 404)

    def _sse(self) -> None:
        assert APP is not None
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        q: queue.Queue = queue.Queue(maxsize=2)
        with APP.sub_lock:
            APP.subs.append(q)
        try:
            self.wfile.write(b"data: " + json.dumps(APP.snapshot(), ensure_ascii=False).encode("utf-8") + b"\n\n")
            while True:
                try:
                    snap = q.get(timeout=10)
                except queue.Empty:
                    self.wfile.write(b": ping\n\n")
                    continue
                self.wfile.write(b"data: " + json.dumps(snap, ensure_ascii=False).encode("utf-8") + b"\n\n")
        except (BrokenPipeError, ConnectionResetError, OSError):
            pass
        finally:
            with APP.sub_lock:
                if q in APP.subs:
                    APP.subs.remove(q)

    def do_POST(self) -> None:
        assert APP is not None
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n) or b"{}")
        except (ValueError, OSError):
            return self._json(dict(ok=False, error="Dữ liệu gửi lên không hợp lệ."), 400)
        node = APP.node
        if self.path == "/api/join":
            return self._json(APP.join(body.get("name"), body.get("udp"), body.get("peers")))
        if not node:
            return self._json(dict(ok=False, error="Chưa tham gia mạng."), 400)
        if self.path == "/api/send":
            rec, _ = node.send_text(body.get("to", ""), body.get("text", ""))
            return self._json(dict(ok=rec is not None, error=None if rec else "Nút nhận không còn trong mạng."))
        if self.path == "/api/config":
            node.set_cfg(body)
            return self._json(dict(ok=True))
        if self.path == "/api/pos":
            node.set_pos(body.get("x", 0), body.get("y", 0))
            return self._json(dict(ok=True))
        if self.path == "/api/bench":
            ok = node.start_bench(body.get("to", ""), body.get("n", 30))
            return self._json(dict(ok=ok, error=None if ok else "Đang đo thử hoặc nút nhận không có mặt."))
        self._json(dict(ok=False, error="not found"), 404)


# ----------------------------------------------------------------------------
# Giao diện web (nhúng sẵn, chạy offline)
# ----------------------------------------------------------------------------
INDEX_HTML = r"""<!doctype html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Chat cộng tác</title>
<style>
:root{
  --paper:#EEF3F1; --panel:#FFFFFF; --ink:#14222B; --ink2:#485D68; --rule:#D3DDDA;
  --direct:#2455E6; --direct-tint:#E2E9FD; --relay:#0B8F73; --relay-tint:#D8F0E8; --loss:#CF2E4B;
  --font:"Segoe UI Variable Text","Segoe UI",system-ui,-apple-system,"Helvetica Neue",Arial,sans-serif;
  --mono:ui-monospace,"Cascadia Mono","SF Mono",Menlo,Consolas,monospace;
  color-scheme:light dark;
}
@media (prefers-color-scheme:dark){
  :root{--paper:#0D1920; --panel:#122229; --ink:#E3EDEF; --ink2:#9FB4BC; --rule:#243B45;
    --direct:#8CA8FF; --direct-tint:#1B2C5A; --relay:#3ECFA7; --relay-tint:#11433A; --loss:#FF7B93}
}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;background:var(--paper);color:var(--ink);font:14px/1.45 var(--font);-webkit-font-smoothing:antialiased}
button,input,select{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--direct);outline-offset:2px}
[hidden]{display:none!important}
.visually-hidden{position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0 0 0 0)}

#join{min-height:100%;display:grid;place-items:center;padding:24px}
.join-box{width:min(440px,100%)}
.join-box h1{font-size:24px;line-height:1.2;margin:0 0 8px;font-weight:650;letter-spacing:-.01em}
.join-box p{margin:0 0 20px;color:var(--ink2);max-width:60ch}
.field{display:block;margin:0 0 14px}
.field span{display:block;font-weight:600;margin-bottom:4px}
.field small{display:block;color:var(--ink2);margin-top:4px}
.field input{width:100%;padding:9px 10px;border:1px solid var(--rule);border-radius:6px;background:var(--panel)}
.btn{padding:9px 16px;border:1px solid var(--ink);border-radius:6px;background:var(--ink);color:var(--paper);font-weight:600;cursor:pointer}
.btn:hover{opacity:.9}
.btn[disabled]{opacity:.45;cursor:not-allowed}
.btn.quiet{background:transparent;color:var(--ink);border-color:var(--rule);font-weight:500}
.err{color:var(--loss);margin:10px 0 0;min-height:1.4em}

#app{height:100vh;display:grid;grid-template-columns:232px minmax(340px,1fr) 400px;background:var(--panel)}
.col{min-height:0;display:flex;flex-direction:column;border-right:1px solid var(--rule)}
.col:last-child{border-right:0}
.col>header{padding:14px 16px;border-bottom:1px solid var(--rule)}
h2{font-size:13px;font-weight:650;margin:0}
.sub{color:var(--ink2);font-size:12.5px}

#side{background:var(--paper)}
.me{display:flex;gap:10px;align-items:center}
.avatar{width:34px;height:34px;border-radius:50%;display:grid;place-items:center;font-weight:650;background:var(--ink);color:var(--paper);flex:none}
.avatar.peer{background:transparent;color:var(--ink);border:1.5px solid var(--ink2)}
.avatar.off{border-style:dashed;opacity:.55}
.me b{display:block}
.addr{font-family:var(--mono);font-size:11.5px;color:var(--ink2);word-break:break-all}
.copy{margin-top:8px;font-size:12.5px;padding:4px 10px}
#peers{list-style:none;margin:0;padding:6px 8px;overflow:auto;flex:1}
#peers button{width:100%;display:flex;gap:10px;align-items:center;text-align:left;padding:8px;border:0;border-radius:8px;background:transparent;cursor:pointer}
#peers button:hover{background:var(--panel)}
#peers button[aria-current="true"]{background:var(--panel);box-shadow:inset 3px 0 0 var(--direct)}
.pname{display:block;font-weight:600}
.meter{display:block;height:4px;border-radius:2px;background:var(--rule);margin-top:5px;overflow:hidden;width:100px}
.meter i{display:block;height:100%;background:var(--direct)}
.empty{padding:16px;color:var(--ink2)}
.empty b{color:var(--ink);display:block;margin-bottom:4px}

#chat header h1{font-size:18px;margin:0;font-weight:650}
#thread{flex:1;min-height:0;overflow:auto;padding:16px;display:flex;flex-direction:column;gap:12px}
.msg{max-width:min(520px,86%);display:flex;flex-direction:column;gap:3px}
.msg.mine{align-self:flex-end;align-items:flex-end}
.bubble{padding:8px 12px;border-radius:14px;background:var(--paper);overflow-wrap:anywhere;white-space:pre-wrap}
.mine .bubble{background:var(--direct-tint);border-bottom-right-radius:4px}
.theirs .bubble{border-bottom-left-radius:4px}
.meta{display:flex;gap:8px;align-items:center;flex-wrap:wrap;font-size:12px;color:var(--ink2)}
.chip{padding:1px 8px;border-radius:99px;font-weight:600;font-size:12px}
.chip.direct{background:var(--direct-tint);color:var(--direct)}
.chip.relay{background:var(--relay-tint);color:var(--relay)}
.chip.fail{background:transparent;color:var(--loss);border:1px solid var(--loss)}
.chip.wait{background:transparent;color:var(--ink2);border:1px dashed var(--ink2)}
.retry{border:0;background:none;color:var(--direct);cursor:pointer;text-decoration:underline;padding:0}
.hint{margin:auto;color:var(--ink2);text-align:center;max-width:36ch}
#compose{display:flex;gap:8px;padding:12px 16px;border-top:1px solid var(--rule)}
#compose input{flex:1;padding:10px 12px;border:1px solid var(--rule);border-radius:8px;background:var(--panel)}

#net{overflow:auto;background:var(--paper)}
.sec{padding:14px 16px;border-bottom:1px solid var(--rule)}
.sec:last-child{border-bottom:0}
.sec h2{margin-bottom:8px}
#map{display:block;width:100%;height:auto;aspect-ratio:1.4/1.1;touch-action:none;cursor:default;border:1px solid var(--rule);border-radius:8px;background:var(--panel)}
.legend{margin:8px 0 0;font-size:12.5px;color:var(--ink2)}
.seg{display:flex;border:1px solid var(--rule);border-radius:8px;overflow:hidden;background:var(--panel)}
.seg button{flex:1;padding:7px 8px;border:0;background:transparent;cursor:pointer}
.seg button+button{border-left:1px solid var(--rule)}
.seg button[aria-pressed="true"]{background:var(--ink);color:var(--paper);font-weight:600}
.row{display:flex;align-items:center;gap:10px;margin:10px 0}
.row label{flex:none;width:118px;color:var(--ink2)}
.row input[type=range]{flex:1;accent-color:var(--direct)}
.row output{width:62px;text-align:right;font-variant-numeric:tabular-nums;font-weight:600}
.row select,.row input[type=number]{padding:5px 8px;border:1px solid var(--rule);border-radius:6px;background:var(--panel);flex:1}
details summary{cursor:pointer;color:var(--ink2);margin-top:6px}
table{width:100%;border-collapse:collapse;font-size:12.5px;margin-top:10px;font-variant-numeric:tabular-nums}
th,td{padding:5px 6px;text-align:right;border-bottom:1px solid var(--rule)}
th:first-child,td:first-child{text-align:left}
th{font-weight:600;color:var(--ink2)}
.bar{height:6px;background:var(--rule);border-radius:3px;overflow:hidden;margin-top:8px}
.bar i{display:block;height:100%;background:var(--relay)}
#log{margin:0;padding:0;list-style:none;font:11.5px/1.5 var(--mono);max-height:230px;overflow:auto;border:1px solid var(--rule);border-radius:8px;background:var(--panel)}
#log li{padding:3px 8px;border-bottom:1px solid var(--rule)}
#log li:last-child{border-bottom:0}
#log .t{color:var(--ink2)}
#log .k-relay{color:var(--relay)} #log .k-lost,#log .k-fail{color:var(--loss)} #log .k-ack,#log .k-send{color:var(--direct)}
#conn{position:fixed;left:50%;top:10px;transform:translateX(-50%);padding:6px 14px;border-radius:99px;background:var(--loss);color:#fff;font-weight:600;z-index:9}

.tabs{display:none}
@media (max-width:1040px){
  #app{display:block;height:auto;min-height:100vh;padding-bottom:56px}
  .col{border-right:0;height:calc(100vh - 56px)}
  body[data-tab="chat"] #side,body[data-tab="chat"] #net{display:none}
  body[data-tab="net"] #chat{display:none}
  body[data-tab="net"] #side{height:auto;max-height:42vh}
  body[data-tab="net"] #net{height:auto}
  .tabs{display:flex;position:fixed;left:0;right:0;bottom:0;height:56px;background:var(--panel);border-top:1px solid var(--rule)}
  .tabs button{flex:1;border:0;background:none;font-weight:600;color:var(--ink2)}
  .tabs button[aria-pressed="true"]{color:var(--direct);box-shadow:inset 0 3px 0 var(--direct)}
}
</style>
</head>
<body data-tab="chat">
<div id="conn" hidden role="status">Mất kết nối. Đang thử kết nối lại...</div>

<main id="join" hidden>
  <form class="join-box" id="joinForm" autocomplete="off">
    <h1>Tham gia mạng cộng tác</h1>
    <p>Mỗi cửa sổ là một nút. Nút nào không đang trò chuyện sẽ tự động giúp chuyển tiếp tin cho các nút còn lại khi đường truyền thẳng bị mất gói.</p>
    <label class="field"><span>Tên của bạn</span><input id="j-name" required maxlength="16"></label>
    <label class="field"><span>Cổng UDP</span><input id="j-udp" required inputmode="numeric"></label>
    <label class="field"><span>Địa chỉ các nút đã biết</span><input id="j-peers">
      <small>Chạy nhiều cửa sổ trên cùng một máy: giữ nguyên giá trị này. Với máy khác, thêm địa chỉ của nút đó, ví dụ 192.168.1.20:9002.</small></label>
    <button class="btn" type="submit">Tham gia</button>
    <p class="err" id="j-err" role="alert"></p>
  </form>
</main>

<div id="app" hidden>
  <aside class="col" id="side" aria-label="Các nút trong mạng">
    <header>
      <div class="me"><div class="avatar" id="me-av"></div><div><b id="me-name"></b><span class="sub">Địa chỉ của bạn</span></div></div>
      <div class="addr" id="me-addr" style="margin-top:8px"></div>
      <button class="btn quiet copy" id="copyAddr" type="button">Sao chép địa chỉ</button>
    </header>
    <ul id="peers"></ul>
  </aside>

  <section class="col" id="chat" aria-label="Trò chuyện">
    <header><h1 id="chat-title">Chưa chọn người nhận</h1><div class="sub" id="chat-sub"></div></header>
    <div id="thread" aria-live="polite"></div>
    <form id="compose" autocomplete="off">
      <label class="visually-hidden" for="text">Nội dung tin nhắn</label>
      <input id="text" placeholder="Nhập tin nhắn rồi nhấn Enter" maxlength="400">
      <button class="btn" type="submit" id="sendBtn">Gửi</button>
    </form>
  </section>

  <section class="col" id="net" aria-label="Mạng và kênh truyền">
    <div class="sec">
      <h2>Bản đồ sóng</h2>
      <canvas id="map" width="720" height="566" role="img" aria-label="Vị trí các nút và gói tin đang truyền"></canvas>
      <p class="legend">Kéo nút của bạn để đổi khoảng cách. Chấm là gói đang phát, vòng là gói vừa nhận, dấu × là gói bị mất. Số % là xác suất một gói đi qua được liên kết.</p>
    </div>
    <div class="sec">
      <h2>Kênh và chế độ</h2>
      <div class="seg" role="group" aria-label="Chế độ truyền">
        <button type="button" data-mode="direct" aria-pressed="false">Gửi thẳng</button>
        <button type="button" data-mode="coop" aria-pressed="true">Cộng tác</button>
      </div>
      <div class="row"><label for="snr">Chất lượng kênh</label><input type="range" id="snr" min="-5" max="25" step="0.5"><output id="snr-o" for="snr"></output></div>
      <div class="row"><label for="sel">Chọn relay</label>
        <select id="sel"><option value="opp">Theo kênh tức thời</option><option value="avg">Theo vị trí</option></select></div>
      <div class="row"><label for="slow">Tốc độ</label>
        <select id="slow"><option value="1">Thực</option><option value="10">Chậm ×10</option><option value="25">Rất chậm ×25</option></select></div>
      <details><summary>Nâng cao</summary>
        <div class="row"><label for="alpha">Hệ số suy hao</label><input type="number" id="alpha" min="1.5" max="6" step="0.5"></div>
        <div class="row"><label for="rate">Tốc độ mã hoá</label><input type="number" id="rate" min="0.25" max="4" step="0.25"></div>
        <div class="row"><label for="retx">Số lần thử lại</label><input type="number" id="retx" min="0" max="8" step="1"></div>
      </details>
    </div>
    <div class="sec">
      <h2>Đo thử</h2>
      <div class="row" style="margin-top:0"><label for="bn">Số tin</label><input type="number" id="bn" min="5" max="200" value="30">
        <button class="btn" id="bench" type="button">Chạy đo thử</button></div>
      <div class="bar" id="bbar" hidden><i style="width:0%"></i></div>
      <div class="sub" id="bstat"></div>
      <table id="btable" hidden><thead><tr><th>Chế độ</th><th>Kênh</th><th>Đến nơi</th><th>Trễ TB</th><th>p95</th><th>Lượt</th><th>Qua relay</th></tr></thead><tbody></tbody></table>
    </div>
    <div class="sec">
      <h2>Nhật ký mạng</h2>
      <ul id="log" aria-live="off"></ul>
    </div>
  </section>
</div>

<nav class="tabs" aria-label="Chuyển màn hình">
  <button type="button" data-tab="chat" aria-pressed="true">Trò chuyện</button>
  <button type="button" data-tab="net" aria-pressed="false">Mạng</button>
</nav>

<script>
(() => {
'use strict';
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const el = (tag, props = {}, ...kids) => {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(props)) {
    if (k === 'class') n.className = v;
    else if (k.startsWith('on')) n.addEventListener(k.slice(2), v);
    else if (v !== false && v != null) n.setAttribute(k, v === true ? '' : v);
  }
  for (const c of kids.flat()) if (c != null && c !== false) n.append(c instanceof Node ? c : document.createTextNode(c));
  return n;
};
const api = (path, body) => fetch(path, {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body || {})})
  .then(r => r.json()).catch(() => ({ok: false, error: 'Không kết nối được với chương trình.'}));
const fmtTime = ts => new Date(ts * 1000).toLocaleTimeString('vi-VN', {hour: '2-digit', minute: '2-digit', second: '2-digit'});
const reduced = matchMedia('(prefers-reduced-motion: reduce)').matches;

let S = null, peerSel = null, tabOn = 'chat';
const keys = {};
const changed = (name, v) => { const s = JSON.stringify(v); if (keys[name] === s) return false; keys[name] = s; return true; };

const es = new EventSource('/events');
es.onmessage = ev => { S = JSON.parse(ev.data); S._at = performance.now(); $('#conn').hidden = true; update(); };
es.onerror = () => { $('#conn').hidden = false; };

let joinFilled = false;
$('#joinForm').addEventListener('submit', async e => {
  e.preventDefault();
  $('#j-err').textContent = '';
  const r = await api('/api/join', {name: $('#j-name').value, udp: $('#j-udp').value, peers: $('#j-peers').value});
  if (!r.ok) $('#j-err').textContent = r.error || 'Không tham gia được.';
});

function update() {
  $('#join').hidden = S.joined;
  $('#app').hidden = !S.joined;
  if (!S.joined) {
    if (!joinFilled) { joinFilled = true; $('#j-name').value = S.defaults.name; $('#j-udp').value = S.defaults.udp; $('#j-peers').value = S.defaults.peers; }
    return;
  }
  document.title = S.me.name + ' - Chat cộng tác';
  if (!peerSel || !S.peers.find(p => p.name === peerSel)) {
    const first = S.peers.find(p => p.online) || S.peers[0];
    peerSel = first ? first.name : null;
  }
  renderSide(); renderChat(); syncControls(); renderBench(); renderLog(); ingestFlows();
}

function renderSide() {
  $('#me-av').textContent = S.me.name[0].toUpperCase();
  $('#me-name').textContent = S.me.name;
  $('#me-addr').textContent = S.me.addr;
  if (!changed('side', [S.peers.map(p => [p.name, p.online, Math.round(p.q * 100)]), peerSel])) return;
  const ul = $('#peers');
  ul.replaceChildren();
  if (!S.peers.length) {
    ul.append(el('li', {class: 'empty'}, el('b', {}, 'Chưa thấy nút nào khác'),
      'Mở thêm một cửa sổ chạy coopchat.py, hoặc nhập địa chỉ của máy kia ở màn hình tham gia. Cần ít nhất ba nút để thấy cộng tác.'));
    return;
  }
  for (const p of S.peers) {
    ul.append(el('li', {}, el('button', {type: 'button', 'aria-current': p.name === peerSel ? 'true' : 'false',
      onclick: () => { peerSel = p.name; keys.side = keys.chat = null; update(); }},
      el('span', {class: 'avatar peer' + (p.online ? '' : ' off')}, p.name[0].toUpperCase()),
      el('span', {}, el('span', {class: 'pname'}, p.name),
        el('span', {class: 'sub'}, p.online ? `Nhận được ${Math.round(p.q * 100)}% gói trực tiếp` : 'Không còn phản hồi'),
        el('span', {class: 'meter'}, el('i', {style: `width:${Math.round(p.q * 100)}%`}))))));
  }
}

function renderChat() {
  const peer = S.peers.find(p => p.name === peerSel);
  const others = S.peers.filter(p => p.online && p.name !== peerSel).length;
  $('#chat-title').textContent = peer ? peer.name : 'Chưa chọn người nhận';
  $('#chat-sub').textContent = peer
    ? (S.cfg.coop ? `Chế độ cộng tác: ${others} nút khác có thể giúp chuyển tiếp. Đường thẳng nhận được ${Math.round(peer.q * 100)}% gói.`
                  : `Chế độ gửi thẳng. Đường thẳng nhận được ${Math.round(peer.q * 100)}% gói.`)
    : 'Chờ có nút khác tham gia mạng.';
  $('#text').disabled = $('#sendBtn').disabled = !(peer && peer.online);
  const msgs = S.chat.filter(m => (m.frm === peerSel && m.to === S.me.name) || (m.frm === S.me.name && m.to === peerSel));
  if (!changed('chat', [msgs.map(m => [m.id, m.status, m.path, m.attempts, m.delay_ms]), peerSel])) return;
  const th = $('#thread');
  const atBottom = th.scrollHeight - th.scrollTop - th.clientHeight < 60;
  th.replaceChildren();
  if (!msgs.length) th.append(el('div', {class: 'hint'}, peer ? `Chưa có tin nhắn nào với ${peer.name}. Hãy gửi tin đầu tiên.` : 'Chưa có nút nào để trò chuyện.'));
  for (const m of msgs) {
    const mine = m.frm === S.me.name;
    const meta = el('div', {class: 'meta'});
    if (mine) {
      if (m.status === 'sending') meta.append(el('span', {class: 'chip wait'}, m.attempts > 1 ? `Đang gửi, lượt ${m.attempts}` : 'Đang gửi'));
      else if (m.status === 'failed') meta.append(el('span', {class: 'chip fail'}, 'Không gửi được'),
        el('button', {class: 'retry', type: 'button', onclick: () => api('/api/send', {to: m.to, text: m.text})}, 'Gửi lại'));
      else meta.append(el('span', {class: 'chip ' + (m.path === 'direct' ? 'direct' : 'relay')}, m.path === 'direct' ? 'Trực tiếp' : 'Qua ' + m.path),
        el('span', {}, `${m.delay_ms} ms`), el('span', {}, `${m.attempts} lượt`));
    } else {
      meta.append(el('span', {class: 'chip ' + (m.path === 'direct' ? 'direct' : 'relay')}, m.path === 'direct' ? 'Nhận trực tiếp' : 'Nhận qua ' + m.path));
    }
    meta.append(el('span', {}, fmtTime(m.ts)));
    th.append(el('div', {class: 'msg ' + (mine ? 'mine' : 'theirs')}, el('div', {class: 'bubble'}, m.text), meta));
  }
  if (atBottom || msgs.length) th.scrollTop = th.scrollHeight;
}

$('#compose').addEventListener('submit', async e => {
  e.preventDefault();
  const t = $('#text').value.trim();
  if (!t || !peerSel) return;
  $('#text').value = '';
  const r = await api('/api/send', {to: peerSel, text: t});
  if (!r.ok) alert(r.error || 'Không gửi được.');
});

$('#copyAddr').addEventListener('click', async () => {
  try { await navigator.clipboard.writeText(S.me.addr); $('#copyAddr').textContent = 'Đã sao chép'; }
  catch { $('#copyAddr').textContent = 'Hãy chép thủ công'; }
  setTimeout(() => $('#copyAddr').textContent = 'Sao chép địa chỉ', 1500);
});

let snrTimer = null;
function syncControls() {
  const c = S.cfg;
  $$('.seg button').forEach(b => b.setAttribute('aria-pressed', String((b.dataset.mode === 'coop') === c.coop)));
  if (document.activeElement !== $('#snr')) $('#snr').value = c.snr_db;
  $('#snr-o').textContent = `${Number(c.snr_db).toFixed(1)} dB`;
  const set = (id, v) => { const n = $(id); if (document.activeElement !== n) n.value = v; };
  set('#sel', c.select); set('#slow', String(c.slow)); set('#alpha', c.alpha); set('#rate', c.rate); set('#retx', c.max_retx);
  const peer = S.peers.find(p => p.name === peerSel);
  $('#bench').disabled = S.bench.running || !(peer && peer.online);
}
$$('.seg button').forEach(b => b.addEventListener('click', () => api('/api/config', {coop: b.dataset.mode === 'coop'})));
$('#snr').addEventListener('input', () => {
  $('#snr-o').textContent = `${Number($('#snr').value).toFixed(1)} dB`;
  clearTimeout(snrTimer); snrTimer = setTimeout(() => api('/api/config', {snr_db: Number($('#snr').value)}), 120);
});
$('#sel').addEventListener('change', () => api('/api/config', {select: $('#sel').value}));
$('#slow').addEventListener('change', () => api('/api/config', {slow: Number($('#slow').value)}));
$('#alpha').addEventListener('change', () => api('/api/config', {alpha: Number($('#alpha').value)}));
$('#rate').addEventListener('change', () => api('/api/config', {rate: Number($('#rate').value)}));
$('#retx').addEventListener('change', () => api('/api/config', {max_retx: Number($('#retx').value)}));

$('#bench').addEventListener('click', async () => {
  const r = await api('/api/bench', {to: peerSel, n: Number($('#bn').value)});
  if (!r.ok) alert(r.error || 'Không chạy được.');
});
function renderBench() {
  const b = S.bench;
  $('#bbar').hidden = !b.running;
  if (b.running) $('#bbar i').style.width = `${Math.round(100 * b.done / Math.max(1, b.total))}%`;
  $('#bstat').textContent = b.running ? `Đang gửi ${b.done} trên ${b.total} tin…`
    : (b.runs.length ? 'Đổi chế độ hoặc chất lượng kênh rồi đo lại để so sánh.' : 'Gửi một loạt tin liên tiếp để đo tỉ lệ đến nơi và độ trễ.');
  if (!changed('bench', b.runs)) return;
  $('#btable').hidden = !b.runs.length;
  const tb = $('#btable tbody'); tb.replaceChildren();
  for (const r of [...b.runs].reverse()) tb.append(el('tr', {},
    el('td', {}, r.mode === 'coop' ? 'Cộng tác' : 'Gửi thẳng'), el('td', {}, `${Number(r.snr).toFixed(1)} dB`),
    el('td', {}, `${(r.delivered * 100).toFixed(0)}%`), el('td', {}, r.mean_ms == null ? '-' : `${r.mean_ms.toFixed(0)} ms`),
    el('td', {}, r.p95_ms == null ? '-' : `${r.p95_ms} ms`), el('td', {}, r.attempts.toFixed(2)), el('td', {}, `${(r.relayed * 100).toFixed(0)}%`)));
}

function renderLog() {
  if (!changed('log', S.logs.map(l => l.t))) return;
  const ul = $('#log');
  const atBottom = ul.scrollHeight - ul.scrollTop - ul.clientHeight < 40;
  ul.replaceChildren(...S.logs.map(l => el('li', {class: 'k-' + l.k}, el('span', {class: 't'}, fmtTime(l.t) + ' '), l.m)));
  if (atBottom) ul.scrollTop = ul.scrollHeight;
}

const cv = $('#map'), ctx = cv.getContext('2d');
const WX = [-0.15, 1.15], WY = [-0.55, 0.55];
const seen = new Set(); let anims = []; let colors = {};
function readColors() {
  const cs = getComputedStyle(document.documentElement);
  for (const k of ['ink', 'ink2', 'rule', 'panel', 'direct', 'relay', 'loss']) colors[k] = cs.getPropertyValue('--' + k).trim();
}
readColors(); matchMedia('(prefers-color-scheme: dark)').addEventListener('change', readColors);

const nodes = () => S ? [{name: S.me.name, pos: S.me.pos, me: true, online: true}, ...S.peers.map(p => ({name: p.name, pos: p.pos, online: p.online}))] : [];
const w2c = p => [(p[0] - WX[0]) / (WX[1] - WX[0]) * cv.width, (p[1] - WY[0]) / (WY[1] - WY[0]) * cv.height];
const c2w = (x, y) => [WX[0] + x / cv.width * (WX[1] - WX[0]), WY[0] + y / cv.height * (WY[1] - WY[0])];
const posOf = name => { const n = nodes().find(n => n.name === name); return n ? w2c(n.pos) : null; };
const qOf = (a, b) => {
  const psi = 2 ** S.cfg.rate - 1, d = Math.max(0.1, Math.hypot(a[0] - b[0], a[1] - b[1]));
  return Math.exp(-psi / (10 ** (S.cfg.snr_db / 10) * d ** (-S.cfg.alpha)));
};

function ingestFlows() {
  const now = performance.now();
  const dur = Math.min(1500, Math.max(380, S.link.delay * 1000));
  for (const f of S.flows) {
    if (seen.has(f.id)) continue;
    seen.add(f.id);
    const t0 = now - f.age;
    if (f.f === S.me.name && f.lost === null) anims.push({kind: 'dot', k: f.k, from: f.f, to: f.to, t0, dur});
    else if (f.to === S.me.name && f.lost) anims.push({kind: 'loss', from: f.f, to: f.to, t0, dur: 1300});
    else if (f.to === S.me.name) anims.push({kind: 'pulse', k: f.k, from: f.f, to: f.to, t0, dur: 800});
  }
  if (seen.size > 600) { const keep = new Set(S.flows.map(f => f.id)); for (const id of [...seen]) if (!keep.has(id)) seen.delete(id); }
}
const kindColor = k => k === 'RELAYED' ? colors.relay : (k === 'ACK' ? colors.ink2 : colors.direct);

function drawMap() {
  requestAnimationFrame(drawMap);
  if (!S || !S.joined || $('#app').hidden || !ctx) return;
  const dpr = devicePixelRatio || 1, w = cv.clientWidth;
  if (w && Math.abs(cv.width - w * dpr) > 2) { cv.width = Math.round(w * dpr); cv.height = Math.round(w * dpr * 1.1 / 1.4); }
  ctx.clearRect(0, 0, cv.width, cv.height);
  const sc = cv.width / 360;
  const ns = nodes(); const now = performance.now();
  ctx.lineCap = 'round'; ctx.font = `${11 * sc}px ${getComputedStyle(document.body).fontFamily}`;
  for (let i = 0; i < ns.length; i++) for (let j = i + 1; j < ns.length; j++) {
    const a = ns[i], b = ns[j]; if (!a.online || !b.online) continue;
    const q = qOf(a.pos, b.pos), pa = w2c(a.pos), pb = w2c(b.pos);
    const pair = (a.name === peerSel && b.me) || (b.name === peerSel && a.me);
    ctx.strokeStyle = pair ? colors.direct : colors.ink2; ctx.globalAlpha = (pair ? 0.35 : 0.18) + 0.55 * q;
    ctx.lineWidth = (pair ? 1.5 : 1) * sc + 3 * sc * q; ctx.setLineDash(q < 0.35 ? [5 * sc, 5 * sc] : []);
    ctx.beginPath(); ctx.moveTo(...pa); ctx.lineTo(...pb); ctx.stroke();
    ctx.setLineDash([]); ctx.globalAlpha = 1;
    const mx = (pa[0] + pb[0]) / 2, my = (pa[1] + pb[1]) / 2, label = Math.round(q * 100) + '%';
    const tw = ctx.measureText(label).width;
    ctx.fillStyle = colors.panel; ctx.fillRect(mx - tw / 2 - 3 * sc, my - 8 * sc, tw + 6 * sc, 15 * sc);
    ctx.fillStyle = colors.ink2; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(label, mx, my);
  }
  anims = anims.filter(a => now - a.t0 < a.dur + 100);
  for (const a of anims) {
    const pa = posOf(a.from), pb = posOf(a.to); if (!pa || !pb) continue;
    const t = Math.min(1, Math.max(0, (now - a.t0) / a.dur));
    if (a.kind === 'dot') {
      if (t <= 0 || t >= 1) continue;
      const x = reduced ? pb[0] : pa[0] + (pb[0] - pa[0]) * t, y = reduced ? pb[1] : pa[1] + (pb[1] - pa[1]) * t;
      ctx.fillStyle = kindColor(a.k); ctx.beginPath(); ctx.arc(x, y, (a.k === 'ACK' ? 3 : 5) * sc, 0, 7); ctx.fill();
    } else if (a.kind === 'pulse') {
      ctx.strokeStyle = kindColor(a.k); ctx.globalAlpha = 1 - t; ctx.lineWidth = 2 * sc;
      ctx.beginPath(); ctx.arc(pb[0], pb[1], (16 + 16 * t) * sc, 0, 7); ctx.stroke(); ctx.globalAlpha = 1;
    } else if (a.kind === 'loss') {
      const x = pa[0] + (pb[0] - pa[0]) * 0.78, y = pa[1] + (pb[1] - pa[1]) * 0.78, r = 6 * sc;
      ctx.strokeStyle = colors.loss; ctx.globalAlpha = 1 - t * t; ctx.lineWidth = 2.5 * sc;
      ctx.beginPath(); ctx.moveTo(x - r, y - r); ctx.lineTo(x + r, y + r); ctx.moveTo(x + r, y - r); ctx.lineTo(x - r, y + r); ctx.stroke(); ctx.globalAlpha = 1;
    }
  }
  for (const n of ns) {
    const [x, y] = w2c(n.pos), r = 15 * sc;
    ctx.beginPath(); ctx.arc(x, y, r, 0, 7);
    ctx.fillStyle = n.me ? colors.ink : colors.panel; ctx.fill();
    ctx.lineWidth = 2 * sc; ctx.strokeStyle = n.name === peerSel ? colors.direct : (n.online ? colors.ink : colors.ink2);
    ctx.setLineDash(n.online ? [] : [3 * sc, 3 * sc]); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = n.me ? colors.panel : colors.ink; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.font = `600 ${12 * sc}px ${getComputedStyle(document.body).fontFamily}`; ctx.fillText(n.name[0].toUpperCase(), x, y + sc * 0.5);
    ctx.fillStyle = colors.ink; ctx.font = `${11.5 * sc}px ${getComputedStyle(document.body).fontFamily}`;
    ctx.fillText(n.name + (n.me ? ' (bạn)' : ''), x, y + r + 11 * sc);
  }
}
requestAnimationFrame(drawMap);

let drag = false, dragT = 0;
const evPos = e => { const r = cv.getBoundingClientRect(); return [(e.clientX - r.left) / r.width * cv.width, (e.clientY - r.top) / r.height * cv.height]; };
cv.addEventListener('pointerdown', e => {
  if (!S || !S.joined) return;
  const [x, y] = evPos(e), [mx, my] = w2c(S.me.pos);
  if (Math.hypot(x - mx, y - my) < 26 * (cv.width / 360)) { drag = true; cv.setPointerCapture(e.pointerId); cv.style.cursor = 'grabbing'; }
});
cv.addEventListener('pointermove', e => {
  if (!S || !S.joined) return;
  const [x, y] = evPos(e);
  if (!drag) { const [mx, my] = w2c(S.me.pos); cv.style.cursor = Math.hypot(x - mx, y - my) < 26 * (cv.width / 360) ? 'grab' : 'default'; return; }
  const p = c2w(x, y); S.me.pos = [Math.max(-0.1, Math.min(1.1, p[0])), Math.max(-0.5, Math.min(0.5, p[1]))];
  const now = performance.now();
  if (now - dragT > 60) { dragT = now; api('/api/pos', {x: S.me.pos[0], y: S.me.pos[1]}); }
});
const endDrag = () => { if (drag) { drag = false; cv.style.cursor = 'default'; api('/api/pos', {x: S.me.pos[0], y: S.me.pos[1]}); } };
cv.addEventListener('pointerup', endDrag); cv.addEventListener('pointercancel', endDrag);

const ro = new ResizeObserver(() => {
    if(S && S.joined) {
        const dpr = devicePixelRatio || 1, w = cv.clientWidth;
        if (w && Math.abs(cv.width - w * dpr) > 2) { cv.width = Math.round(w * dpr); cv.height = Math.round(w * dpr * 1.1 / 1.4); }
    }
});
ro.observe(cv);

$$('.tabs button').forEach(b => b.addEventListener('click', () => {
  tabOn = b.dataset.tab; document.body.dataset.tab = tabOn;
  $$('.tabs button').forEach(x => x.setAttribute('aria-pressed', String(x === b)));
}));
})();
</script>
</body>
</html>
"""


# ----------------------------------------------------------------------------
# Khởi động
# ----------------------------------------------------------------------------
def main() -> None:
    global APP
    ap = argparse.ArgumentParser(description="Chat cộng tác có giao diện web")
    ap.add_argument("--http", type=int, default=8000, help="cổng giao diện web bắt đầu tìm (mặc định 8000)")
    ap.add_argument("--no-browser", action="store_true", help="không tự mở trình duyệt")
    ap.add_argument("--name", help="tham gia ngay với tên này (bỏ qua màn hình tham gia)")
    ap.add_argument("--udp", type=int, help="cổng UDP của nút")
    ap.add_argument("--peers", default="", help="địa chỉ các nút đã biết, vd 192.168.1.20:9001")
    a = ap.parse_args()

    srv = None
    for port in range(a.http, a.http + 30):
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            continue
    if srv is None:
        sys.exit("Không tìm được cổng giao diện web còn trống.")
    srv.daemon_threads = True
    index = srv.server_address[1] - a.http
    APP = App(index)
    if a.name:
        r = APP.join(a.name, a.udp or APP.defaults["udp"], a.peers or APP.defaults["peers"])
        if not r["ok"]:
            sys.exit(r["error"])
    url = f"http://127.0.0.1:{srv.server_address[1]}/"
    print(f"Giao diện: {url}   (nhấn Ctrl+C để thoát)")
    if not a.no_browser:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        if APP.node:
            APP.node.stop()


if __name__ == "__main__":
    main()
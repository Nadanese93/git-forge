#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""git-forge: a standalone GitHub-compatible git forge in one process.

Serves, from its own in-memory store and with the Python standard library only:
  - git smart HTTP  (/owner/repo.git): upload-pack protocol v2, receive-pack v0
  - GitHub REST v3   (/api/v3): repos, branches, commits, contents, issues,
    comments, labels, pull requests, git refs
  - GitHub GraphQL v4 (/api/graphql): the documents gh and github-mcp-server send
  - MCP over Streamable HTTP (/mcp): server/discover (2026-07-28) and the
    legacy initialize handshake, with the six required tools

Lifecycle (the make.fun harness contract): bind an ephemeral port, register it
with POST $MAKEFUN_ENV_URL/register, poll GET $MAKEFUN_ENV_URL/done until
{"done": true}, then exit 0. Never binds 8080.

Determinism: no wall clock and no unseeded randomness anywhere in state.
Every timestamp the forge invents is a fixed epoch plus a monotonic sequence
number, so two runs fed the same requests produce byte-identical state.
The scenario viewer identity is derived from the kit's public fixed seed
(SCENARIO_SEED) with a faithful port of the kit's seeded generator.
"""

import base64
import difflib
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote, urlparse, parse_qs

ZERO_OID = "0" * 40
VIEWER_FALLBACK = "adaiversen"
EPOCH_BASE = 1735689600  # 2025-01-01T00:00:00Z; deterministic clock base
SERVER_NAME = "git-forge"
SERVER_VERSION = "1.0.0"

# --------------------------------------------------------------------------
# Seeded scenario (faithful port of kit sdk/conformance/wire.ts)
# --------------------------------------------------------------------------
_MASK = (1 << 64) - 1
_SCENARIO_SEED = 0x6A09E667F3BCC909


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & _MASK
    return h


def _mix64(value):
    z = (value + 0x9E3779B97F4A7C15) & _MASK
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & _MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & _MASK
    return (z ^ (z >> 31)) & _MASK


def _seed_for(label):
    return _mix64(_SCENARIO_SEED ^ _fnv1a64(label))


class _Rng:
    def __init__(self, seed):
        s = seed & _MASK
        self.state = s if s != 0 else _SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & _MASK
        x = (x ^ (x << 25)) & _MASK
        x = (x ^ (x >> 27)) & _MASK
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & _MASK

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, m):
        if m == 1:
            return 0
        rng = 4294967296
        limit = rng - (rng % m)
        while True:
            v = self.next_u32()
            if v < limit:
                return v % m

    def pick(self, items):
        return items[self.next_int(len(items))]


_FIRST = ["ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
          "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
          "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane"]
_LAST = ["anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
         "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
         "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich",
         "vega", "weber", "xu", "yilmaz", "zimmer"]


def _scenario_users():
    rng = _Rng(_seed_for("users"))
    used = set()
    users = []
    for i in range(12):
        first = rng.pick(_FIRST)
        last = rng.pick(_LAST)
        base = first + last
        login = base
        suffix = 2
        while login in used:
            login = "%s-%d" % (base, suffix)
            suffix += 1
        used.add(login)
        users.append({"id": 1000 + i, "login": login,
                      "name": "%s %s" % (first, last),
                      "email": "%s@example.invalid" % login})
    return users


try:
    _USERS = _scenario_users()
    VIEWER = _USERS[0]
except Exception:
    VIEWER = {"id": 1000, "login": VIEWER_FALLBACK, "name": "ada iversen",
              "email": "adaiversen@example.invalid"}

# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------


def _b64e(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return base64.b64encode(data).decode("ascii")


def _b64d(text):
    return base64.b64decode(text.encode("ascii"))


def _sha1(data):
    return hashlib.sha1(data).hexdigest()


def _iso(epoch):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(epoch))


def _git_date(epoch):
    return "%d +0000" % epoch


def _json_bytes(obj):
    # Canonical writer: sorted keys, compact separators. Every JSON reply
    # goes through here, so key order can never leak hash-seed nondeterminism.
    return (json.dumps(obj, separators=(",", ":"), ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")


def _slug_ok(name):
    return bool(re.match(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$", name or ""))


# --------------------------------------------------------------------------
# Git objects
# --------------------------------------------------------------------------

TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(otype, data):
    h = hashlib.sha1()
    h.update(("%s %d\x00" % (otype, len(data))).encode("ascii"))
    h.update(data)
    return h.hexdigest()


def parse_tree(data):
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp].decode("ascii")
        nul = data.index(b"\x00", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append({"mode": mode, "name": name, "oid": oid})
        i = nul + 21
    return entries


def _tree_sort_key(e):
    return e["name"] + ("/" if e["mode"] == "40000" else "")


def build_tree(entries):
    out = bytearray()
    for e in sorted(entries, key=_tree_sort_key):
        out += ("%s %s\x00" % (e["mode"], e["name"])).encode("utf-8", "surrogateescape")
        out += bytes.fromhex(e["oid"])
    return bytes(out)


def parse_commit(data):
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    parents = []
    tree = None
    author = ""
    committer = ""
    for line in head.split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
        elif line.startswith("author "):
            author = line[7:]
        elif line.startswith("committer "):
            committer = line[10:]
    return {"tree": tree, "parents": parents, "author": author,
            "committer": committer, "message": message}


def parse_tag(data):
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    out = {"object": None, "type": None, "tag": None, "tagger": "", "message": message}
    for line in head.split("\n"):
        if line.startswith("object "):
            out["object"] = line[7:].strip()
        elif line.startswith("type "):
            out["type"] = line[5:].strip()
        elif line.startswith("tag "):
            out["tag"] = line[4:].strip()
        elif line.startswith("tagger "):
            out["tagger"] = line[7:]
    return out


def build_commit(tree, parents, author_line, committer_line, message):
    lines = ["tree %s" % tree]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s" % author_line)
    lines.append("committer %s" % committer_line)
    msg = message if message.endswith("\n") else message + "\n"
    return ("\n".join(lines) + "\n\n" + msg).encode("utf-8")


# --- packfile ---------------------------------------------------------------


def _read_varint(buf, pos):
    first = buf[pos]
    pos += 1
    size = first & 0x0F
    shift = 4
    while first & 0x80:
        first = buf[pos]
        pos += 1
        size |= (first & 0x7F) << shift
        shift += 7
    return size, pos


def _apply_delta(base, delta):
    def varint(b, p):
        v = 0
        s = 0
        while True:
            c = b[p]
            p += 1
            v |= (c & 0x7F) << s
            s += 7
            if not (c & 0x80):
                return v, p
    _, p = varint(delta, 0)
    result_size, p = varint(delta, p)
    out = bytearray()
    while p < len(delta):
        op = delta[p]
        p += 1
        if op & 0x80:
            offset = 0
            size = 0
            for i in range(4):
                if op & (1 << i):
                    offset |= delta[p] << (8 * i)
                    p += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[p] << (8 * i)
                    p += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[p:p + op]
            p += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != result_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_pack(pack):
    """Parse a packfile; returns (objects dict oid->(type,data), delta_count)."""
    if len(pack) < 12 or pack[:4] != b"PACK":
        raise ValueError("not a packfile")
    count = int.from_bytes(pack[8:12], "big")
    objects = {}
    offsets = {}  # pack offset -> oid
    pending = []  # (offset, base_offset_or_oid, delta_data, is_ref)
    delta_count = 0
    pos = 12
    for _ in range(count):
        start = pos
        first = pack[pos]
        pos += 1
        otype = (first >> 4) & 7
        size, pos = _read_varint_from_first(pack, pos, first)
        if otype in (6, 7):
            delta_count += 1
            if otype == 6:
                c = pack[pos]
                pos += 1
                off = c & 0x7F
                while c & 0x80:
                    c = pack[pos]
                    pos += 1
                    off = ((off + 1) << 7) | (c & 0x7F)
                base_off = start - off
                raw, pos = _inflate_at(pack, pos)
                pending.append((start, base_off, raw, False))
            else:
                base_oid = pack[pos:pos + 20].hex()
                pos += 20
                raw, pos = _inflate_at(pack, pos)
                pending.append((start, base_oid, raw, True))
        else:
            raw, pos = _inflate_at(pack, pos)
            t = CODE_TYPE[otype]
            oid = hash_object(t, raw)
            objects[oid] = (t, raw)
            offsets[start] = oid
    # resolve deltas (may chain; iterate until all resolved)
    unresolved = list(pending)
    for _ in range(len(pending) + 2):
        if not unresolved:
            break
        still = []
        for (start, base, raw, is_ref) in unresolved:
            if is_ref:
                base_entry = objects.get(base)
                base_oid = base
            else:
                base_oid = offsets.get(base)
                base_entry = objects.get(base_oid) if base_oid else None
            if base_entry is None:
                still.append((start, base, raw, is_ref))
                continue
            btype, bdata = base_entry
            data = _apply_delta(bdata, raw)
            oid = hash_object(btype, data)
            objects[oid] = (btype, data)
            offsets[start] = oid
        if len(still) == len(unresolved):
            break
        unresolved = still
    return objects, delta_count


def _read_varint_from_first(buf, pos, first):
    size = first & 0x0F
    shift = 4
    while first & 0x80:
        first = buf[pos]
        pos += 1
        size |= (first & 0x7F) << shift
        shift += 7
    return size, pos


def _inflate_at(buf, pos):
    d = zlib.decompressobj()
    out = d.decompress(buf[pos:])
    consumed = len(buf[pos:]) - len(d.unused_data)
    return out, pos + consumed


def write_pack(objects):
    """objects: iterable of (oid, type, data). Full objects only, sorted by oid."""
    items = sorted(objects, key=lambda x: x[0])
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(items).to_bytes(4, "big")
    for oid, otype, data in items:
        code = TYPE_CODE[otype]
        size = len(data)
        first = (code << 4) | (size & 0x0F)
        size >>= 4
        hdr = bytearray()
        if size:
            hdr.append(first | 0x80)
            while size:
                b = size & 0x7F
                size >>= 7
                hdr.append(b | (0x80 if size else 0))
        else:
            hdr.append(first)
        out += bytes(hdr)
        out += zlib.compress(data, 1)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


def pack_checksum_ok(pack):
    if len(pack) < 20:
        return False
    return hashlib.sha1(pack[:-20]).digest() == pack[-20:]


# --- pkt-line ----------------------------------------------------------------


def pkt_line(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def pkt_lines(items):
    out = bytearray()
    for it in items:
        if it == "flush":
            out += pkt_flush()
        elif it == "delim":
            out += pkt_delim()
        else:
            out += pkt_line(it)
    return bytes(out)


def parse_pkt_lines(data):
    """Parse a byte string into a list of ('data', bytes) | ('flush',) |
    ('delim',) | ('end',). Raises ValueError on malformed framing."""
    out = []
    i = 0
    n = len(data)
    while i < n:
        if i + 4 > n:
            raise ValueError("truncated pkt-line header")
        hexlen = data[i:i + 4]
        try:
            ln = int(hexlen.decode("ascii"), 16)
        except ValueError:
            raise ValueError("bad pkt-line length")
        if ln == 0:
            out.append(("flush", b""))
            i += 4
        elif ln == 1:
            out.append(("delim", b""))
            i += 4
        elif ln == 2:
            out.append(("end", b""))
            i += 4
        elif ln < 4 or i + ln > n:
            raise ValueError("bad pkt-line length")
        else:
            out.append(("data", data[i + 4:i + ln]))
            i += ln
    return out


def sideband_pack(pack, chunk=60000):
    """Wrap pack bytes in sideband band-1 pkt-lines."""
    out = bytearray()
    for i in range(0, len(pack), chunk):
        out += pkt_line(b"\x01" + pack[i:i + chunk])
    out += pkt_flush()
    return bytes(out)


def sideband_text(text):
    if isinstance(text, str):
        text = text.encode("utf-8")
    out = bytearray()
    for i in range(0, len(text), 60000):
        out += pkt_line(b"\x01" + text[i:i + 60000])
    out += pkt_flush()
    return bytes(out)

# --------------------------------------------------------------------------
# Store
# --------------------------------------------------------------------------


class ForgeError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # (owner, name) -> Repo
        self.seq = 0             # deterministic clock / id sequence
        self.next_repo_id = 5000
        self.next_comment_id = 1
        self.next_label_id = 1
        self.req_seq = 0

    def tick(self):
        self.seq += 1
        return self.seq

    def now_epoch(self):
        return EPOCH_BASE + self.seq

    def now_iso(self):
        return _iso(self.now_epoch())


class Repo:
    def __init__(self, store, owner, name, description, private):
        self.store = store
        self.id = store.next_repo_id
        store.next_repo_id += 1
        self.owner = owner
        self.name = name
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.refs = {}           # full ref name -> oid
        self.objects = {}        # oid -> (type, data)
        self.issues = {}         # number -> dict
        self.pulls = {}          # number -> dict
        self.labels = {}         # name -> dict
        self.next_number = 1
        self.created_seq = store.tick()
        self.updated_seq = self.created_seq

    # -- identity ----------------------------------------------------------
    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def global_id(self, kind=None):
        return _b64e("Repository:%d" % self.id)

    # -- git objects ---------------------------------------------------------
    def put_object(self, otype, data):
        oid = hash_object(otype, data)
        self.objects.setdefault(oid, (otype, data))
        return oid

    def get_object(self, oid):
        return self.objects.get(oid)

    def reachable(self, roots):
        """All oids reachable from commit/tag roots (commits, trees, blobs, tags)."""
        seen = set()
        stack = list(roots)
        while stack:
            oid = stack.pop()
            if oid in seen or oid == ZERO_OID:
                continue
            entry = self.objects.get(oid)
            if entry is None:
                continue
            seen.add(oid)
            otype, data = entry
            if otype == "commit":
                c = parse_commit(data)
                stack.append(c["tree"])
                stack.extend(c["parents"])
            elif otype == "tree":
                for e in parse_tree(data):
                    stack.append(e["oid"])
            elif otype == "tag":
                t = parse_tag(data)
                if t["object"]:
                    stack.append(t["object"])
        return seen

    def is_ancestor(self, anc, desc):
        if anc == desc:
            return True
        seen = set()
        stack = [desc]
        while stack:
            oid = stack.pop()
            if oid in seen:
                continue
            seen.add(oid)
            entry = self.objects.get(oid)
            if entry is None or entry[0] != "commit":
                continue
            for p in parse_commit(entry[1])["parents"]:
                if p == anc:
                    return True
                stack.append(p)
        return False

    def commit_history(self, tip):
        """Commits reachable from tip, newest-first by parent walk (topological)."""
        out = []
        seen = set()
        stack = [tip]
        while stack:
            oid = stack.pop(0)
            if oid in seen or oid == ZERO_OID:
                continue
            entry = self.objects.get(oid)
            if entry is None or entry[0] != "commit":
                continue
            seen.add(oid)
            out.append(oid)
            stack.extend(parse_commit(entry[1])["parents"])
        return out

    def merge_base(self, a, b):
        anc_a = set(self.commit_history(a))
        for oid in self.commit_history(b):
            if oid in anc_a:
                return oid
        return None

    # -- trees ---------------------------------------------------------------
    def tree_map(self, tree_oid):
        """Flatten a tree oid to {path: (mode, oid)}."""
        out = {}

        def walk(oid, prefix):
            entry = self.objects.get(oid)
            if entry is None or entry[0] != "tree":
                return
            for e in parse_tree(entry[1]):
                path = prefix + e["name"]
                if e["mode"] == "40000":
                    walk(e["oid"], path + "/")
                else:
                    out[path] = (e["mode"], e["oid"])
        walk(tree_oid, "")
        return out

    def build_tree_from_map(self, files):
        """files: {path: (mode, oid)} -> root tree oid (creates subtrees)."""
        dirs = {}

        def subtree(paths):
            entries = []
            sub = {}
            for path, (mode, oid) in paths.items():
                if "/" in path:
                    head, rest = path.split("/", 1)
                    sub.setdefault(head, {})[rest] = (mode, oid)
                else:
                    entries.append({"mode": mode, "name": path, "oid": oid})
            for d, subpaths in sub.items():
                entries.append({"mode": "40000", "name": d,
                                "oid": subtree(subpaths)})
            return self.put_object("tree", build_tree(entries))
        return subtree(files)

    def tip_tree_map(self, ref):
        oid = self.refs.get(ref)
        if not oid:
            return {}, None
        entry = self.objects.get(oid)
        if entry is None or entry[0] != "commit":
            return {}, None
        return self.tree_map(parse_commit(entry[1])["tree"]), oid

    # -- commits created by the forge itself ----------------------------------
    def make_commit(self, tree_oid, parents, message, author=None):
        author = author or VIEWER
        seq = self.store.tick()
        epoch = EPOCH_BASE + seq
        ident = "%s <%s> %s" % (author["name"], author["email"], _git_date(epoch))
        data = build_commit(tree_oid, parents, ident, ident, message)
        return self.put_object("commit", data)

    def commit_file(self, branch, path, content_bytes, message):
        """Create/update a file on a branch; returns (commit_oid, blob_oid)."""
        ref = "refs/heads/" + branch
        files, tip = self.tip_tree_map(ref)
        blob_oid = self.put_object("blob", content_bytes)
        files[path] = ("100644", blob_oid)
        tree_oid = self.build_tree_from_map(files)
        parents = [tip] if tip else []
        commit_oid = self.make_commit(tree_oid, parents, message)
        self.refs[ref] = commit_oid
        return commit_oid, blob_oid

    def delete_file(self, branch, path, message):
        ref = "refs/heads/" + branch
        files, tip = self.tip_tree_map(ref)
        if path not in files:
            raise ForgeError(404, "Not Found")
        del files[path]
        tree_oid = self.build_tree_from_map(files)
        commit_oid = self.make_commit(tree_oid, [tip] if tip else [], message)
        self.refs[ref] = commit_oid
        return commit_oid

    # -- diff ------------------------------------------------------------------
    def diff_files(self, base_tip, head_tip):
        """Files changed head vs base. Returns list of dicts with filename,
        status, additions, deletions, changes."""
        base_files, _ = self.tip_tree_map("refs/heads/__x__") if False else ({}, None)
        bf = {}
        hf = {}
        if base_tip:
            entry = self.objects.get(base_tip)
            if entry and entry[0] == "commit":
                bf = self.tree_map(parse_commit(entry[1])["tree"])
        if head_tip:
            entry = self.objects.get(head_tip)
            if entry and entry[0] == "commit":
                hf = self.tree_map(parse_commit(entry[1])["tree"])
        out = []
        for path in sorted(set(bf) | set(hf)):
            if path not in bf:
                status = "added"
                new = self.objects.get(hf[path][1])
                new_lines = new[1].decode("utf-8", "replace").splitlines() if new else []
                out.append({"filename": path, "status": status,
                            "additions": len(new_lines), "deletions": 0,
                            "changes": len(new_lines)})
            elif path not in hf:
                old = self.objects.get(bf[path][1])
                old_lines = old[1].decode("utf-8", "replace").splitlines() if old else []
                out.append({"filename": path, "status": "removed",
                            "additions": 0, "deletions": len(old_lines),
                            "changes": len(old_lines)})
            elif bf[path][1] != hf[path][1]:
                old = self.objects.get(bf[path][1])
                new = self.objects.get(hf[path][1])
                old_lines = old[1].decode("utf-8", "replace").splitlines() if old else []
                new_lines = new[1].decode("utf-8", "replace").splitlines() if new else []
                sm = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
                adds = dels = 0
                for tag, i1, i2, j1, j2 in sm.get_opcodes():
                    if tag in ("insert", "replace"):
                        adds += j2 - j1
                    if tag in ("delete", "replace"):
                        dels += i2 - i1
                if adds == 0 and dels == 0:
                    adds = 1
                out.append({"filename": path, "status": "modified",
                            "additions": adds, "deletions": dels,
                            "changes": adds + dels})
        return out

    def pr_conflicts(self, base_tip, head_tip):
        """True when head and base both changed the same file differently
        since their merge base."""
        if not base_tip or not head_tip:
            return False
        mb = self.merge_base(base_tip, head_tip)
        if mb is None:
            return False
        mb_entry = self.objects.get(mb)
        if mb_entry is None or mb_entry[0] != "commit":
            return False
        mb_files = self.tree_map(parse_commit(mb_entry[1])["tree"])
        base_entry = self.objects.get(base_tip)
        head_entry = self.objects.get(head_tip)
        if not base_entry or not head_entry:
            return False
        base_files = self.tree_map(parse_commit(base_entry[1])["tree"])
        head_files = self.tree_map(parse_commit(head_entry[1])["tree"])
        for path in set(base_files) | set(head_files):
            base_changed = base_files.get(path, (None, None))[1] != mb_files.get(path, (None, None))[1]
            head_changed = head_files.get(path, (None, None))[1] != mb_files.get(path, (None, None))[1]
            if base_changed and head_changed:
                if base_files.get(path, (None, None))[1] != head_files.get(path, (None, None))[1]:
                    return True
        return False


STORE = Store()


def get_repo_or_404(owner, name):
    repo = STORE.repos.get((owner, name))
    if repo is None:
        raise ForgeError(404, "Not Found")
    return repo


def viewer_user_json():
    return {"login": VIEWER["login"], "id": VIEWER["id"], "node_id": _b64e("User:%d" % VIEWER["id"]),
            "avatar_url": "", "type": "User", "site_admin": False,
            "name": VIEWER["name"], "email": VIEWER["email"]}


def repo_json(repo):
    return {
        "id": repo.id, "node_id": repo.global_id(), "name": repo.name,
        "full_name": repo.full_name(), "owner": viewer_user_json() if repo.owner == VIEWER["login"] else
        {"login": repo.owner, "id": 0, "type": "User"},
        "private": repo.private, "description": repo.description,
        "fork": False, "created_at": _iso(EPOCH_BASE + repo.created_seq),
        "updated_at": _iso(EPOCH_BASE + repo.updated_seq),
        "pushed_at": _iso(EPOCH_BASE + repo.updated_seq),
        "homepage": None, "size": 0, "stargazers_count": 0, "watchers_count": 0,
        "language": None, "has_issues": True, "has_projects": True,
        "has_downloads": True, "has_wiki": True, "has_pages": False,
        "default_branch": repo.default_branch, "visibility": "private" if repo.private else "public",
        "html_url": "https://example.invalid/%s" % repo.full_name(),
        "clone_url": "https://example.invalid/%s.git" % repo.full_name(),
        "git_url": "git://example.invalid/%s.git" % repo.full_name(),
        "ssh_url": "git@example.invalid:%s.git" % repo.full_name(),
        "url": "/api/v3/repos/%s/%s" % (repo.owner, repo.name),
    }


def issue_json(repo, issue):
    return {
        "id": issue["id"], "node_id": issue["node_id"], "number": issue["number"],
        "title": issue["title"], "body": issue["body"], "state": issue["state"],
        "labels": [dict(l) for l in issue["labels"]],
        "user": viewer_user_json(), "assignee": None, "assignees": [],
        "locked": False, "comments": len(issue["comments"]),
        "created_at": issue["created_at"], "updated_at": issue["updated_at"],
        "closed_at": issue["closed_at"],
        "url": "/api/v3/repos/%s/%s/issues/%d" % (repo.owner, repo.name, issue["number"]),
        "html_url": "https://example.invalid/%s/issues/%d" % (repo.full_name(), issue["number"]),
    }


def pull_json(repo, pr):
    head_sha = repo.refs.get("refs/heads/" + pr["head"], "")
    base_sha = repo.refs.get("refs/heads/" + pr["base"], "")
    return {
        "id": pr["id"], "node_id": pr["node_id"], "number": pr["number"],
        "title": pr["title"], "body": pr["body"], "state": pr["state"],
        "locked": False, "user": viewer_user_json(),
        "head": {"ref": pr["head"], "sha": head_sha,
                 "label": "%s:%s" % (repo.owner, pr["head"]),
                 "user": viewer_user_json()},
        "base": {"ref": pr["base"], "sha": base_sha,
                 "label": "%s:%s" % (repo.owner, pr["base"]),
                 "user": viewer_user_json()},
        "merged": pr["merged"], "merged_at": pr["merged_at"],
        "merge_commit_sha": pr["merge_commit_sha"],
        "mergeable": not repo.pr_conflicts(base_sha, head_sha) if head_sha and base_sha else True,
        "created_at": pr["created_at"], "updated_at": pr["updated_at"],
        "closed_at": pr["closed_at"],
        "url": "/api/v3/repos/%s/%s/pulls/%d" % (repo.owner, repo.name, pr["number"]),
        "html_url": "https://example.invalid/%s/pull/%d" % (repo.full_name(), pr["number"]),
    }

# --------------------------------------------------------------------------
# Git smart HTTP
# --------------------------------------------------------------------------

GIT_AGENT = "git-forge/1.0"


def _peeled(repo, oid):
    """Peel a tag oid to its commit oid, or None."""
    entry = repo.objects.get(oid)
    if entry and entry[0] == "tag":
        t = parse_tag(entry[1])
        target = t["object"]
        if target:
            return _peeled(repo, target) or target
    return None


def _sorted_refs(repo):
    out = []
    for name in sorted(repo.refs):
        out.append((name, repo.refs[name]))
    return out


def git_advertise_v2(repo):
    lines = ["# service=git-upload-pack\n", "flush", "version 2\n",
             "ls-refs=unborn\n", "fetch=shallow filter\n",
             "object-format=sha1\n", "agent=%s\n" % GIT_AGENT, "flush"]
    return pkt_lines(lines)


def git_advertise_v0(repo, service):
    caps = ("report-status report-status-v2 side-band-64k delete-refs "
            "ofs-delta thin-pack agent=%s" % GIT_AGENT)
    if service == "git-upload-pack":
        caps = ("side-band-64k multi_ack multi_ack_detailed thin-pack "
                "ofs-delta shallow agent=%s" % GIT_AGENT)
    head_ref = "refs/heads/" + repo.default_branch
    caps = "symref=HEAD:%s %s" % (head_ref, caps)
    lines = ["# service=%s\n" % service, "flush"]
    head_oid = repo.refs.get(head_ref, ZERO_OID)
    lines.append("%s HEAD\x00%s\n" % (head_oid, caps))
    for name, oid in _sorted_refs(repo):
        lines.append("%s %s\n" % (oid, name))
        peeled = _peeled(repo, oid)
        if peeled:
            lines.append("%s %s^{}\n" % (peeled, name))
    lines.append("flush")
    return pkt_lines(lines)


def git_ls_refs_v2(repo, prefixes, want_peel, want_symrefs, want_unborn):
    lines = []
    head_ref = "refs/heads/" + repo.default_branch
    head_oid = repo.refs.get(head_ref)
    # HEAD is a ref named "HEAD" for prefix filtering (real git's clone
    # sends ref-prefix HEAD; the suite's unmatched prefix must yield 0).
    head_matches = (not prefixes) or any("HEAD".startswith(p) for p in prefixes)
    if head_matches:
        if head_oid:
            line = "%s HEAD" % head_oid
            if want_symrefs:
                line += " symref-target:%s" % head_ref
            lines.append(line + "\n")
        elif want_unborn:
            line = "unborn HEAD"
            if want_symrefs:
                line += " symref-target:%s" % head_ref
            lines.append(line + "\n")
    for name, oid in _sorted_refs(repo):
        if prefixes and not any(name.startswith(p) for p in prefixes):
            continue
        line = "%s %s" % (oid, name)
        if want_peel:
            peeled = _peeled(repo, oid)
            if peeled:
                line += " peeled:%s" % peeled
        lines.append(line + "\n")
    lines.append("flush")
    return pkt_lines(lines)


def _commit_depths(repo, wants, max_depth=None):
    """BFS from want commits; returns {commit_oid: depth} (depth 0 = want).
    With max_depth set, parents deeper than max_depth - 1 are not expanded:
    a depth-1 fetch only ever visits the wants themselves."""
    depths = {}
    queue = [(w, 0) for w in wants]
    qi = 0
    while qi < len(queue):
        oid, d = queue[qi]
        qi += 1
        if oid in depths:
            continue
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "commit":
            continue
        depths[oid] = d
        if max_depth is not None and d >= max_depth - 1:
            continue
        for p in parse_commit(entry[1])["parents"]:
            queue.append((p, d + 1))
    return depths


def _commit_own_objects(repo, oid):
    """A commit plus its tree closure (trees + blobs), NOT its parents."""
    out = set()
    entry = repo.objects.get(oid)
    if entry is None or entry[0] != "commit":
        return out
    out.add(oid)
    stack = [parse_commit(entry[1])["tree"]]
    while stack:
        t = stack.pop()
        if t in out:
            continue
        e = repo.objects.get(t)
        if e is None:
            continue
        out.add(t)
        if e[0] == "tree":
            for ent in parse_tree(e[1]):
                stack.append(ent["oid"])
    return out


def compute_fetch(repo, wants, haves, depth, shallow_bounds, deepen_relative=False):
    """Returns (objects dict, shallow list, unshallow list).

    Depth is the ABSOLUTE target depth (the suite sends `deepen N` meaning
    N generations from each want). When the client also sends
    `deepen-relative` (real git), N is added to the client's current depth,
    derived from the distance of its shallow boundaries from the wants.
    Objects sent are the own-objects of the included commits only: parents
    outside the included set are never sent. A have that is a shallow
    boundary is held only as its own objects, never as its full ancestry.
    Shallow boundaries after the fetch are the held commits whose parents
    are not held.
    """
    wants = [w for w in dict.fromkeys(wants)]
    shallow_bounds = set(shallow_bounds or [])
    # what the client already holds (commit graph view)
    held_commits = set()
    have_objects = set()
    for h in haves:
        entry = repo.objects.get(h)
        if entry is None:
            continue
        if entry[0] == "commit":
            if h in shallow_bounds:
                held_commits.add(h)
                have_objects |= _commit_own_objects(repo, h)
            else:
                for o in repo.reachable([h]):
                    e2 = repo.objects.get(o)
                    if e2 is not None and e2[0] == "commit":
                        held_commits.add(o)
                have_objects |= repo.reachable([h])
        else:
            have_objects |= repo.reachable([h])
    # expand wants that are tags to their targets (keep tag objects too)
    want_commits = []
    extra_want_objects = set()
    for w in wants:
        entry = repo.objects.get(w)
        if entry is None:
            continue
        if entry[0] == "tag":
            extra_want_objects.add(w)
            target = parse_tag(entry[1])["object"]
            if target:
                want_commits.append(target)
        elif entry[0] == "commit":
            want_commits.append(w)
        else:
            extra_want_objects.add(w)
    # Cap the BFS at the target depth (a depth-1 fetch visits only the
    # wants). With deepen-relative the old depth is derived from the
    # boundaries first, so that case walks the full history.
    depths = _commit_depths(repo, want_commits,
                            max_depth=None if deepen_relative else depth)
    if depth is not None and deepen_relative:
        # the client's current depth = deepest shallow boundary + 1
        cur = 0
        for b in shallow_bounds:
            if b in depths:
                cur = max(cur, depths[b] + 1)
        depth = cur + depth if cur else depth
    included_commits = set()
    for oid, d in depths.items():
        if depth is None or d < depth:
            included_commits.add(oid)
    held_commits |= included_commits
    # objects to send: own objects of included commits, minus what is held
    send = set()
    for oid in included_commits:
        send |= _commit_own_objects(repo, oid)
    send |= extra_want_objects
    send -= have_objects
    objects = {}
    for oid in send:
        entry = repo.objects.get(oid)
        if entry is not None:
            objects[oid] = entry
    # shallow boundaries after the fetch: held commits with a missing parent
    boundary = set()
    for oid in held_commits:
        entry = repo.objects.get(oid)
        if entry is None or entry[0] != "commit":
            continue
        parents = parse_commit(entry[1])["parents"]
        if any(p not in held_commits for p in parents):
            boundary.add(oid)
    shallow = sorted(boundary)
    unshallow = sorted(b for b in shallow_bounds if b in held_commits and b not in boundary)
    return objects, shallow, unshallow


def handle_git_upload_pack(repo, body):
    """POST /owner/repo.git/git-upload-pack. Returns (status, ctype, bytes)."""
    try:
        packets = parse_pkt_lines(body)
    except ValueError:
        return 400, "application/x-git-upload-pack-result", b"bad pkt-line\n"
    lines = []
    section = None
    for kind, payload in packets:
        if kind == "flush":
            break
        if kind == "delim":
            section = "args"
            continue
        if kind != "data":
            continue
        lines.append(payload.decode("utf-8", "surrogateescape"))
    if not lines or not lines[0].startswith("command="):
        return 400, "application/x-git-upload-pack-result", b"bad request\n"
    cmd = lines[0][len("command="):].strip()
    args = lines[1:]
    if cmd == "ls-refs":
        prefixes = []
        peel = symrefs = unborn = False
        for a in args:
            a = a.strip()
            if a.startswith("ref-prefix "):
                prefixes.append(a[len("ref-prefix "):])
            elif a == "peel":
                peel = True
            elif a == "symrefs":
                symrefs = True
            elif a == "unborn":
                unborn = True
        return 200, "application/x-git-upload-pack-result", \
            git_ls_refs_v2(repo, prefixes, peel, symrefs, unborn)
    if cmd != "fetch":
        return 400, "application/x-git-upload-pack-result", b"unknown command\n"
    wants, haves, shallow_in, depth = [], [], [], None
    done = False
    deepen_relative = False
    for a in args:
        a = a.strip()
        if a.startswith("want "):
            wants.append(a[5:].strip())
        elif a.startswith("have "):
            haves.append(a[5:].strip())
        elif a.startswith("shallow "):
            shallow_in.append(a[8:].strip())
        elif a.startswith("deepen "):
            try:
                depth = int(a[7:].strip())
            except ValueError:
                depth = None
        elif a == "deepen-relative":
            deepen_relative = True
        elif a == "done":
            done = True
    if haves and not done:
        # negotiation round: the client sent haves but has not said done yet.
        # Reply with acknowledgments only; the client will follow up with
        # a request carrying `done` (repeating the wants).
        out = bytearray()
        out += pkt_line("acknowledgments\n")
        out += pkt_line("NAK\n")
        out += pkt_flush()
        return 200, "application/x-git-upload-pack-result", bytes(out)
    objects, shallow, unshallow = compute_fetch(repo, wants, haves, depth, shallow_in, deepen_relative)
    pack = write_pack([(oid, t, d) for oid, (t, d) in objects.items()])
    out = bytearray()
    if haves:
        out += pkt_line("acknowledgments\n")
        out += pkt_line("NAK\n")
        out += pkt_delim()
    if shallow or unshallow:
        out += pkt_line("shallow-info\n")
        for s in shallow:
            out += pkt_line("shallow %s\n" % s)
        for s in unshallow:
            out += pkt_line("unshallow %s\n" % s)
        out += pkt_delim()
    out += pkt_line("packfile\n")
    out += sideband_pack(pack)
    return 200, "application/x-git-upload-pack-result", bytes(out)


def _scan_pkt_section(body):
    """Scan pkt-lines from the start of body until the first flush (or end).
    Returns (command_lines, pack_bytes, malformed_bool)."""
    lines = []
    i = 0
    n = len(body)
    while i < n:
        if i + 4 > n:
            return lines, b"", True
        try:
            ln = int(body[i:i + 4].decode("ascii"), 16)
        except ValueError:
            return lines, b"", True
        if ln == 0:
            return lines, body[i + 4:], False
        if ln in (1, 2):
            i += 4
            continue
        if ln < 4 or i + ln > n:
            return lines, b"", True
        lines.append(body[i + 4:i + ln])
        i += ln
    return lines, b"", False


def handle_git_receive_pack(repo, body):
    """POST /owner/repo.git/git-receive-pack. Returns (status, ctype, bytes)."""
    raw_lines, pack, malformed = _scan_pkt_section(body)
    if malformed:
        # malformed framing: answer a report the client can parse, stay up
        report = "unpack error malformed pkt-line\n"
        return 200, "application/x-git-receive-pack-result", sideband_text(report)
    commands = []
    capabilities = set()
    for payload in raw_lines:
        text = payload.decode("utf-8", "surrogateescape")
        if "\x00" in text:
            head, caps = text.split("\x00", 1)
            text = head
            capabilities = set(caps.strip().split())
        parts = text.strip().split(" ")
        if len(parts) >= 3:
            commands.append((parts[0], parts[1], parts[2]))
    unpack_ok = True
    unpack_detail = "ok"
    new_objects = {}
    if pack:
        if not pack_checksum_ok(pack):
            unpack_ok = False
            unpack_detail = "error pack checksum mismatch"
        else:
            try:
                new_objects, _ = read_pack(pack)
            except Exception as exc:
                unpack_ok = False
                unpack_detail = "error %s" % exc
    report_lines = []
    if unpack_ok:
        for oid, (t, d) in new_objects.items():
            repo.objects.setdefault(oid, (t, d))
        for old, new, ref in commands:
            current = repo.refs.get(ref, ZERO_OID)
            ok = True
            reason = ""
            if old != current:
                ok = False
                reason = "non-fast-forward"
            elif new == ZERO_OID:
                if current == ZERO_OID:
                    ok = False
                    reason = "non-fast-forward"
            else:
                if current == ZERO_OID:
                    # create: new object must exist
                    if new not in repo.objects:
                        ok = False
                        reason = "object not found"
                else:
                    if new == current:
                        pass
                    elif new not in repo.objects:
                        ok = False
                        reason = "object not found"
                    elif not repo.is_ancestor(current, new):
                        ok = False
                        reason = "non-fast-forward"
            if ok:
                if new == ZERO_OID:
                    repo.refs.pop(ref, None)
                else:
                    repo.refs[ref] = new
                report_lines.append("ok %s\n" % ref)
            else:
                report_lines.append("ng %s %s\n" % (ref, reason))
        report = "unpack ok\n" + "".join(report_lines)
    else:
        report = "unpack %s\n" % unpack_detail
    if "report-status-v2" in capabilities:
        # v2: the report stream is itself pkt-lined inside band 1.
        inner = b"".join(pkt_line(l) for l in report.splitlines(keepends=True)) + pkt_flush()
        return 200, "application/x-git-receive-pack-result", sideband_text(inner)
    return 200, "application/x-git-receive-pack-result", sideband_text(report)

# --------------------------------------------------------------------------
# REST v3
# --------------------------------------------------------------------------


def _label_json(label):
    return {"id": label["id"], "node_id": label["node_id"], "name": label["name"],
            "color": label["color"], "description": label.get("description", ""),
            "default": False,
            "url": "/api/v3/repos/%s/%s/labels/%s" % (label["owner"], label["repo"], label["name"])}


def _new_issue(repo, title, body, labels):
    number = repo.next_number
    repo.next_number += 1
    seq = STORE.tick()
    issue = {
        "id": 100000 + repo.id * 1000 + number,
        "node_id": _b64e("Issue:%d:%d" % (repo.id, number)),
        "number": number, "title": title or "", "body": body or "",
        "state": "open", "labels": list(labels), "comments": [],
        "created_at": _iso(EPOCH_BASE + seq), "updated_at": _iso(EPOCH_BASE + seq),
        "closed_at": None, "created_seq": seq,
    }
    repo.issues[number] = issue
    return issue


def _new_pull(repo, title, body, head, base):
    number = repo.next_number
    repo.next_number += 1
    seq = STORE.tick()
    pr = {
        "id": 200000 + repo.id * 1000 + number,
        "node_id": _b64e("PullRequest:%d:%d" % (repo.id, number)),
        "number": number, "title": title or "", "body": body or "",
        "state": "open", "head": head, "base": base,
        "merged": False, "merged_at": None, "merge_commit_sha": None,
        "created_at": _iso(EPOCH_BASE + seq), "updated_at": _iso(EPOCH_BASE + seq),
        "closed_at": None, "created_seq": seq,
    }
    repo.pulls[number] = pr
    return pr


def _paginate(items, query):
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    end = start + per_page
    return items[start:end], page, per_page, total


def _link_header(base_url, path, query, page, per_page, total):
    if total <= per_page:
        return None
    last = (total + per_page - 1) // per_page
    parts = []
    q = dict(query)
    def url(p):
        qq = {k: v[0] for k, v in q.items()}
        qq["page"] = str(p)
        qq["per_page"] = str(per_page)
        qs = "&".join("%s=%s" % (k, v) for k, v in sorted(qq.items()))
        return "%s%s?%s" % (base_url, path, qs)
    if page < last:
        parts.append('<%s>; rel="next"' % url(page + 1))
        parts.append('<%s>; rel="last"' % url(last))
    if page > 1:
        parts.append('<%s>; rel="first"' % url(1))
        parts.append('<%s>; rel="prev"' % url(page - 1))
    return ", ".join(parts) if parts else None


def _content_entry(repo, path, ref):
    """Resolve a contents path at a ref (branch name or commit sha).
    Returns ('file', blob_oid, size) | ('dir', [(name, type, sha, path)]) | None."""
    tip = None
    if ref:
        if ref in repo.refs:
            tip = repo.refs[ref]
        elif ref in [r[11:] for r in repo.refs if r.startswith("refs/heads/")]:
            tip = repo.refs["refs/heads/" + ref]
        elif ref in repo.objects:
            tip = ref
    if tip is None:
        tip = repo.refs.get("refs/heads/" + repo.default_branch)
    if tip is None:
        return None
    entry = repo.objects.get(tip)
    if entry is None or entry[0] != "commit":
        return None
    files = repo.tree_map(parse_commit(entry[1])["tree"])
    if path == "" or path is None:
        # root listing
        names = {}
        for p in files:
            head = p.split("/")[0]
            names.setdefault(head, "dir" if "/" in p else "file")
        out = []
        for name in sorted(names):
            if names[name] == "dir":
                sub = {pp: v for pp, v in files.items() if pp.startswith(name + "/")}
                tree_oid = repo.build_tree_from_map(sub)
                out.append((name, "dir", tree_oid, name))
            else:
                out.append((name, "file", files[name][1], name))
        return ("dir", out)
    if path in files:
        mode, oid = files[path]
        blob = repo.objects.get(oid)
        return ("file", oid, len(blob[1]) if blob else 0)
    prefix = path.rstrip("/") + "/"
    children = {}
    for p in files:
        if p.startswith(prefix):
            rest = p[len(prefix):]
            head = rest.split("/")[0]
            children.setdefault(head, "dir" if "/" in rest else "file")
    if not children:
        return None
    out = []
    for name in sorted(children):
        if children[name] == "dir":
            sub = {pp: v for pp, v in files.items() if pp.startswith(prefix + name + "/")}
            tree_oid = repo.build_tree_from_map(sub)
            out.append((name, "dir", tree_oid, prefix + name))
        else:
            out.append((name, "file", files[prefix + name][1], prefix + name))
    return ("dir", out)


def rest_dispatch(method, path, query, body, base_url):
    """Returns (status, obj_or_bytes, extra_headers). Raises ForgeError."""
    segs = [s for s in path.split("/") if s != ""]
    if method == "GET" and (path == "/api/v3" or path == "/api/v3/"):
        return 200, {"current_user_url": "/api/v3/user",
                     "rate_limit_url": "/api/v3/rate_limit",
                     "repository_url": "/api/v3/repos/{owner}/{repo}"}, \
            {"X-Oauth-Scopes": "repo, read:org"}
    if method == "GET" and path == "/api/v3/meta":
        return 200, {"installed_version": "1.0.0"}, {}
    if method == "GET" and path == "/api/v3/rate_limit":
        return 200, {"resources": {"core": {"limit": 5000, "remaining": 4999,
                                            "reset": EPOCH_BASE + 3600}},
                     "rate": {"limit": 5000, "remaining": 4999,
                              "reset": EPOCH_BASE + 3600}}, {}
    if method == "GET" and path == "/api/v3/user":
        return 200, viewer_user_json(), {}
    if method == "GET" and path == "/api/v3/user/repos":
        repos = [repo_json(r) for r in sorted(STORE.repos.values(),
                                               key=lambda r: r.created_seq)
                 if r.owner == VIEWER["login"]]
        page_items, page, per_page, total = _paginate(repos, query)
        headers = {}
        link = _link_header(base_url, path, query, page, per_page, total)
        if link:
            headers["Link"] = link
        return 200, page_items, headers
    if method == "POST" and path == "/api/v3/user/repos":
        name = (body or {}).get("name")
        if not name or not isinstance(name, str):
            raise ForgeError(422, "Validation Failed: name is required")
        if (VIEWER["login"], name) in STORE.repos:
            raise ForgeError(422, "Repository already exists")
        repo = Repo(STORE, VIEWER["login"], name,
                    (body or {}).get("description", ""),
                    (body or {}).get("private", False))
        STORE.repos[(VIEWER["login"], name)] = repo
        return 201, repo_json(repo), {}
    # /api/v3/repos/{owner}/{repo}/...
    if len(segs) >= 4 and segs[0] == "api" and segs[1] == "v3" and segs[2] == "repos":
        owner = unquote(segs[3])
        name = unquote(segs[4])
        rest = segs[5:]
        if owner != VIEWER["login"]:
            raise ForgeError(404, "Not Found")
        repo = STORE.repos.get((owner, name))
        if repo is None:
            raise ForgeError(404, "Not Found")
        return _repo_dispatch(repo, method, rest, query, body, base_url, path)
    if len(segs) >= 3 and segs[0] == "api" and segs[1] == "v3" and segs[2] == "users":
        login = unquote(segs[3]) if len(segs) > 3 else ""
        if login == VIEWER["login"]:
            return 200, viewer_user_json(), {}
        raise ForgeError(404, "Not Found")
    raise ForgeError(404, "Not Found")


def _repo_dispatch(repo, method, rest, query, body, base_url, full_path):
    body = body or {}
    # ---- repository itself ----
    if not rest:
        if method == "GET":
            return 200, repo_json(repo), {}
        if method == "PATCH":
            if "description" in body:
                repo.description = body["description"]
            if "default_branch" in body and isinstance(body["default_branch"], str):
                repo.default_branch = body["default_branch"]
            repo.updated_seq = STORE.tick()
            return 200, repo_json(repo), {}
        if method == "DELETE":
            del STORE.repos[(repo.owner, repo.name)]
            return 204, None, {}
        raise ForgeError(404, "Not Found")
    head = rest[0]
    # ---- branches ----
    if head == "branches":
        if method == "GET" and len(rest) == 1:
            out = [{"name": r[11:], "commit": {"sha": oid},
                    "protected": False}
                   for r, oid in sorted(repo.refs.items())
                   if r.startswith("refs/heads/")]
            return 200, out, {}
        if method == "GET" and len(rest) == 2:
            ref = "refs/heads/" + unquote(rest[1])
            oid = repo.refs.get(ref)
            if oid is None:
                raise ForgeError(404, "Not Found")
            return 200, {"name": unquote(rest[1]), "commit": {"sha": oid},
                         "protected": False}, {}
        raise ForgeError(404, "Not Found")
    # ---- commits ----
    if head == "commits":
        if method == "GET":
            sha = query.get("sha", [None])[0]
            if sha:
                if sha in repo.refs:
                    tip = repo.refs[sha]
                elif "refs/heads/" + sha in repo.refs:
                    tip = repo.refs["refs/heads/" + sha]
                elif sha in repo.objects:
                    tip = sha
                else:
                    raise ForgeError(404, "Not Found")
            else:
                tip = repo.refs.get("refs/heads/" + repo.default_branch)
            if tip is None:
                return 200, [], {}
            out = []
            for oid in repo.commit_history(tip):
                entry = repo.objects.get(oid)
                c = parse_commit(entry[1])
                out.append(_commit_json(repo, oid, c))
            page_items, page, per_page, total = _paginate(out, query)
            return 200, page_items, {}
        raise ForgeError(404, "Not Found")
    # ---- git data: refs ----
    if head == "git" and len(rest) >= 2 and rest[1] == "refs":
        if method == "GET" and len(rest) == 2:
            out = [{"ref": r, "node_id": _b64e("Ref:%s" % r),
                    "url": "/api/v3/repos/%s/%s/git/refs/%s" % (repo.owner, repo.name, r),
                    "object": {"sha": oid, "type": "commit"}}
                   for r, oid in sorted(repo.refs.items())]
            return 200, out, {}
        if method == "GET" and len(rest) >= 3:
            refname = "/".join(unquote(s) for s in rest[2:])
            oid = repo.refs.get(refname)
            if oid is None:
                raise ForgeError(404, "Not Found")
            return 200, {"ref": refname, "object": {"sha": oid, "type": "commit"}}, {}
        if method == "POST" and len(rest) == 2:
            refname = body.get("ref")
            sha = body.get("sha")
            if not refname or not sha or sha not in repo.objects:
                raise ForgeError(422, "Validation Failed")
            if refname in repo.refs:
                raise ForgeError(422, "Reference already exists")
            repo.refs[refname] = sha
            return 201, {"ref": refname, "object": {"sha": sha, "type": "commit"}}, {}
        if method == "PATCH" and len(rest) >= 3:
            refname = "/".join(unquote(s) for s in rest[2:])
            sha = body.get("sha")
            if refname not in repo.refs or not sha or sha not in repo.objects:
                raise ForgeError(422, "Validation Failed")
            repo.refs[refname] = sha
            return 200, {"ref": refname, "object": {"sha": sha, "type": "commit"}}, {}
        if method == "DELETE" and len(rest) >= 3:
            refname = "/".join(unquote(s) for s in rest[2:])
            if refname not in repo.refs:
                raise ForgeError(404, "Not Found")
            del repo.refs[refname]
            return 204, None, {}
        raise ForgeError(404, "Not Found")
    # ---- contents ----
    if head == "contents":
        cpath = "/".join(unquote(s) for s in rest[1:])
        if method == "GET":
            ref = query.get("ref", [None])[0]
            got = _content_entry(repo, cpath, ref)
            if got is None:
                raise ForgeError(404, "Not Found")
            if got[0] == "file":
                _, oid, size = got
                blob = repo.objects.get(oid)
                data = blob[1] if blob else b""
                return 200, {"type": "file", "encoding": "base64",
                             "size": size, "name": cpath.split("/")[-1],
                             "path": cpath, "content": _b64e(data),
                             "sha": oid}, {}
            out = [{"type": t, "name": n, "path": p, "sha": s, "size": 0}
                   for (n, t, s, p) in got[1]]
            return 200, out, {}
        if method == "PUT":
            message = body.get("message", "")
            content_b64 = body.get("content")
            if content_b64 is None:
                raise ForgeError(422, "Validation Failed: content is required")
            try:
                content = base64.b64decode(content_b64.encode("ascii"))
            except Exception:
                raise ForgeError(422, "Validation Failed: content is not base64")
            branch = body.get("branch") or repo.default_branch
            ref = "refs/heads/" + branch
            if ref not in repo.refs:
                # create the branch from the default tip (or empty)
                base_tip = repo.refs.get("refs/heads/" + repo.default_branch)
                if base_tip:
                    repo.refs[ref] = base_tip
            files, tip = repo.tip_tree_map(ref)
            existing = files.get(cpath)
            sha = body.get("sha")
            if existing is not None:
                if sha is not None and sha != existing[1]:
                    raise ForgeError(409, "Conflict: sha does not match")
                status = 200
            else:
                if sha is not None:
                    raise ForgeError(409, "Conflict: sha does not match")
                status = 201
            commit_oid, blob_oid = repo.commit_file(branch, cpath, content, message)
            entry = {"type": "file", "encoding": "base64",
                     "size": len(content), "name": cpath.split("/")[-1],
                     "path": cpath, "content": content_b64, "sha": blob_oid}
            commit = {"sha": commit_oid, "message": message,
                      "author": {"name": VIEWER["name"], "email": VIEWER["email"]},
                      "committer": {"name": VIEWER["name"], "email": VIEWER["email"]}}
            return status, {"content": entry, "commit": commit}, {}
        if method == "DELETE":
            branch = body.get("branch") or repo.default_branch
            sha = body.get("sha")
            files, tip = repo.tip_tree_map("refs/heads/" + branch)
            if cpath not in files:
                raise ForgeError(404, "Not Found")
            if sha is not None and sha != files[cpath][1]:
                raise ForgeError(409, "Conflict: sha does not match")
            commit_oid = repo.delete_file(branch, cpath, body.get("message", ""))
            return 200, {"commit": {"sha": commit_oid}}, {}
        raise ForgeError(404, "Not Found")
    # ---- labels ----
    if head == "labels":
        if method == "GET":
            return 200, [_label_json(l) for l in repo.labels.values()], {}
        if method == "POST":
            name = body.get("name")
            if not name:
                raise ForgeError(422, "Validation Failed: name is required")
            if name in repo.labels:
                raise ForgeError(422, "Label already exists")
            label = {"id": STORE.next_label_id, "node_id": _b64e("Label:%d:%s" % (repo.id, name)),
                     "name": name, "color": body.get("color", "ededed"),
                     "description": body.get("description", ""),
                     "owner": repo.owner, "repo": repo.name}
            STORE.next_label_id += 1
            repo.labels[name] = label
            return 201, _label_json(label), {}
        raise ForgeError(404, "Not Found")
    # ---- issues ----
    if head == "issues":
        if method == "POST" and len(rest) == 1:
            labels = []
            for lname in body.get("labels", []) or []:
                lab = repo.labels.get(lname)
                if lab is None:
                    raise ForgeError(422, "Validation Failed: label does not exist")
                labels.append(_label_json(lab))
            issue = _new_issue(repo, body.get("title", ""), body.get("body", ""), labels)
            return 201, issue_json(repo, issue), {}
        if method == "GET" and len(rest) == 1:
            state = query.get("state", ["open"])[0]
            direction = query.get("direction", ["desc"])[0]
            sort = query.get("sort", ["created"])[0]
            items = list(repo.issues.values())
            if state != "all":
                items = [i for i in items if i["state"] == state]
            reverse = direction != "asc"
            items.sort(key=lambda i: i["created_seq"], reverse=reverse)
            out = [issue_json(repo, i) for i in items]
            page_items, page, per_page, total = _paginate(out, query)
            headers = {}
            link = _link_header(base_url, full_path, query, page, per_page, total)
            if link:
                headers["Link"] = link
            return 200, page_items, headers
        if len(rest) >= 2:
            try:
                number = int(rest[1])
            except ValueError:
                raise ForgeError(404, "Not Found")
            issue = repo.issues.get(number)
            if issue is None:
                raise ForgeError(404, "Not Found")
            if len(rest) == 2:
                if method == "GET":
                    return 200, issue_json(repo, issue), {}
                if method == "PATCH":
                    if "state" in body:
                        issue["state"] = body["state"]
                        issue["closed_at"] = _iso(EPOCH_BASE + STORE.seq) if body["state"] == "closed" else None
                    if "title" in body:
                        issue["title"] = body["title"]
                    if "body" in body:
                        issue["body"] = body["body"]
                    issue["updated_at"] = _iso(EPOCH_BASE + STORE.tick())
                    return 200, issue_json(repo, issue), {}
                raise ForgeError(404, "Not Found")
            if len(rest) == 3 and rest[2] == "comments":
                if method == "GET":
                    out = [{"id": c["id"], "node_id": c["node_id"], "body": c["body"],
                            "user": viewer_user_json(),
                            "created_at": c["created_at"], "updated_at": c["updated_at"]}
                           for c in issue["comments"]]
                    return 200, out, {}
                if method == "POST":
                    cid = STORE.next_comment_id
                    STORE.next_comment_id += 1
                    seq = STORE.tick()
                    comment = {"id": cid, "node_id": _b64e("Comment:%d" % cid),
                               "body": body.get("body", ""),
                               "created_at": _iso(EPOCH_BASE + seq),
                               "updated_at": _iso(EPOCH_BASE + seq)}
                    issue["comments"].append(comment)
                    return 201, {"id": cid, "node_id": comment["node_id"],
                                 "body": comment["body"],
                                 "user": viewer_user_json(),
                                 "created_at": comment["created_at"],
                                 "updated_at": comment["updated_at"]}, {}
                raise ForgeError(404, "Not Found")
        raise ForgeError(404, "Not Found")
    # ---- pulls ----
    if head == "pulls":
        if method == "POST" and len(rest) == 1:
            head_ref = body.get("head", "")
            base_ref = body.get("base", repo.default_branch)
            if ("refs/heads/" + head_ref) not in repo.refs:
                raise ForgeError(422, "Validation Failed: head branch does not exist")
            if ("refs/heads/" + base_ref) not in repo.refs:
                raise ForgeError(422, "Validation Failed: base branch does not exist")
            for pr in repo.pulls.values():
                if pr["head"] == head_ref and pr["base"] == base_ref and pr["state"] == "open":
                    raise ForgeError(422, "Validation Failed: pull request already exists")
            pr = _new_pull(repo, body.get("title", ""), body.get("body", ""),
                           head_ref, base_ref)
            return 201, pull_json(repo, pr), {}
        if method == "GET" and len(rest) == 1:
            state = query.get("state", ["open"])[0]
            items = list(repo.pulls.values())
            if state != "all":
                items = [p for p in items if p["state"] == state]
            items.sort(key=lambda p: p["created_seq"], reverse=True)
            out = [pull_json(repo, p) for p in items]
            page_items, page, per_page, total = _paginate(out, query)
            return 200, page_items, {}
        if len(rest) >= 2:
            try:
                number = int(rest[1])
            except ValueError:
                raise ForgeError(404, "Not Found")
            pr = repo.pulls.get(number)
            if pr is None:
                raise ForgeError(404, "Not Found")
            if len(rest) == 2:
                if method == "GET":
                    return 200, pull_json(repo, pr), {}
                raise ForgeError(404, "Not Found")
            if len(rest) == 3 and rest[2] == "files" and method == "GET":
                head_sha = repo.refs.get("refs/heads/" + pr["head"], "")
                base_sha = repo.refs.get("refs/heads/" + pr["base"], "")
                return 200, repo.diff_files(base_sha, head_sha), {}
            if len(rest) == 3 and rest[2] == "merge" and method == "PUT":
                return _merge_pull(repo, pr, body)
            if len(rest) == 3 and rest[2] == "comments" and method == "GET":
                return 200, [], {}
        raise ForgeError(404, "Not Found")
    raise ForgeError(404, "Not Found")


def _commit_json(repo, oid, c):
    author = c["author"]
    name = author.split(" <")[0] if " <" in author else author
    email = ""
    date = ""
    m = re.search(r"<([^>]*)> (\d+) ", author)
    if m:
        email = m.group(1)
        date = _iso(int(m.group(2)))
    # GitHub's REST view shows the commit message without the trailing
    # newline the raw git object carries; the raw object keeps it.
    message = c["message"]
    if message.endswith("\n"):
        message = message[:-1]
    return {
        "sha": oid,
        "commit": {"message": message, "tree": {"sha": c["tree"]},
                   "author": {"name": name, "email": email, "date": date},
                   "committer": {"name": name, "email": email, "date": date}},
        "author": {"login": VIEWER["login"], "id": VIEWER["id"]},
        "committer": {"login": VIEWER["login"], "id": VIEWER["id"]},
        "parents": [{"sha": p} for p in c["parents"]],
        "url": "/api/v3/repos/%s/%s/commits/%s" % (repo.owner, repo.name, oid),
    }


def _merge_pull(repo, pr, body):
    if pr["state"] != "open":
        raise ForgeError(405, "Pull request is already merged or closed")
    head_sha = repo.refs.get("refs/heads/" + pr["head"])
    base_sha = repo.refs.get("refs/heads/" + pr["base"])
    if not head_sha or not base_sha:
        raise ForgeError(404, "Not Found")
    if repo.pr_conflicts(base_sha, head_sha):
        raise ForgeError(405, "Merge conflict: the pull request cannot be merged")
    head_entry = repo.objects.get(head_sha)
    head_tree = parse_commit(head_entry[1])["tree"]
    method = (body or {}).get("merge_method", "squash")
    if method == "squash":
        message = "%s (#%d)" % (pr["title"], pr["number"])
    else:
        message = "Merge pull request #%d from %s" % (pr["number"], pr["head"])
    merge_sha = repo.make_commit(head_tree, [base_sha], message)
    repo.refs["refs/heads/" + pr["base"]] = merge_sha
    pr["state"] = "closed"
    pr["merged"] = True
    pr["merged_at"] = _iso(EPOCH_BASE + STORE.seq)
    pr["closed_at"] = pr["merged_at"]
    pr["merge_commit_sha"] = merge_sha
    return 200, {"merged": True, "sha": merge_sha,
                 "message": "Pull Request successfully merged"}, {}

# --------------------------------------------------------------------------
# GraphQL v4
# --------------------------------------------------------------------------

_GQL_ISSUE_FIELDS = ["id", "number", "title", "state", "body", "createdAt",
                     "updatedAt", "url", "author", "labels", "comments",
                     "closedAt", "repository"]
_GQL_PR_FIELDS = ["id", "number", "title", "state", "body", "createdAt",
                  "updatedAt", "url", "author", "headRefName", "baseRefName",
                  "headRef", "baseRef", "mergeable", "merged", "files",
                  "mergeCommit", "closedAt", "repository"]
_GQL_REPO_FIELDS = ["id", "databaseId", "name", "nameWithOwner", "owner",
                    "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                    "description", "isPrivate", "url", "createdAt", "updatedAt",
                    "issue", "issues", "pullRequests", "pullRequest", "labels"]
_GQL_USER_FIELDS = ["id", "login", "name", "email", "url"]
_GQL_REF_FIELDS = ["name", "target"]
_GQL_COMMENT_FIELDS = ["id", "body", "author", "createdAt", "updatedAt"]
_GQL_TYPES = {
    "Query": {"viewer", "repository", "node", "__type", "__schema"},
    "Mutation": {"createIssue", "closeIssue", "createPullRequest",
                 "mergePullRequest", "addComment"},
    "Repository": set(_GQL_REPO_FIELDS),
    "Issue": set(_GQL_ISSUE_FIELDS),
    "PullRequest": set(_GQL_PR_FIELDS),
    "User": set(_GQL_USER_FIELDS),
    "Actor": set(_GQL_USER_FIELDS),
    "Ref": set(_GQL_REF_FIELDS),
    "IssueComment": set(_GQL_COMMENT_FIELDS),
    "IssueConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "PullRequestConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "PullRequestChangedFileConnection": {"nodes", "edges", "pageInfo", "totalCount"},
    "PageInfo": {"hasNextPage", "hasPreviousPage", "endCursor", "startCursor"},
    "Commit": {"oid", "message", "author", "committer"},
    "PullRequestChangedFile": {"path", "additions", "deletions", "changeType"},
    "IssueCommentEdge": {"node", "cursor"},
    "PullRequestEdge": {"node", "cursor"},
    "IssueEdge": {"node", "cursor"},
}


class _GqlToken:
    __slots__ = ("kind", "value")

    def __init__(self, kind, value):
        self.kind = kind
        self.value = value


def _gql_lex(text):
    tokens = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n,":
            i += 1
        elif c == "#":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "." and text[i:i + 3] == "...":
            tokens.append(_GqlToken("...", "..."))
            i += 3
        elif c in "{}()[]:!=$@":
            tokens.append(_GqlToken(c, c))
            i += 1
        elif c == '"':
            j = i + 1
            out = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    esc = text[j + 1]
                    out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"',
                                "\\": "\\", "/": "/"}.get(esc, esc))
                    j += 2
                else:
                    out.append(text[j])
                    j += 1
            tokens.append(_GqlToken("string", "".join(out)))
            i = j + 1
        elif c.isdigit() or (c == "-" and i + 1 < n and text[i + 1].isdigit()):
            j = i
            while j < n and (text[j].isdigit() or text[j] in ".eE+-"):
                j += 1
            raw = text[i:j]
            try:
                tokens.append(_GqlToken("int", int(raw)))
            except ValueError:
                tokens.append(_GqlToken("float", float(raw)))
            i = j
        elif c.isalpha() or c == "_":
            j = i
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(_GqlToken("name", text[i:j]))
            i = j
        else:
            raise ValueError("unexpected character %r" % c)
    tokens.append(_GqlToken("eof", None))
    return tokens


class _GqlParser:
    def __init__(self, tokens):
        self.toks = tokens
        self.pos = 0

    def peek(self):
        return self.toks[self.pos]

    def next(self):
        t = self.toks[self.pos]
        self.pos += 1
        return t

    def expect(self, kind):
        t = self.next()
        if t.kind != kind:
            raise ValueError("expected %s, got %s" % (kind, t.kind))
        return t

    def skip(self, kind):
        if self.peek().kind == kind:
            self.pos += 1
            return True
        return False

    def parse_document(self):
        ops = []
        while self.peek().kind != "eof":
            ops.append(self.parse_operation())
        return ops

    def parse_operation(self):
        kind = "query"
        name = None
        if self.peek().kind == "name" and self.peek().value in ("query", "mutation", "subscription"):
            kind = self.next().value
            if self.peek().kind == "name":
                name = self.next().value
        elif self.peek().kind == "name":
            name = self.next().value
        variables = {}
        if self.peek().kind == "(":
            variables = self.parse_var_defs()
        directives = self.parse_directives()
        sel = self.parse_selection_set()
        return {"kind": kind, "name": name, "variables": variables,
                "selection": sel}

    def parse_var_defs(self):
        self.expect("(")
        defs = {}
        while self.peek().kind != ")":
            self.expect("$")
            name = self.expect("name").value
            self.expect(":")
            defs[name] = self.parse_type()
            if self.peek().kind == "=":
                self.next()
                self.parse_value()
            if self.peek().kind == "name":
                # variable default directives etc; skip
                pass
        self.expect(")")
        return defs

    def parse_type(self):
        if self.skip("["):
            inner = self.parse_type()
            self.expect("]")
            t = "[" + inner + "]"
        else:
            t = self.expect("name").value
        if self.skip("!"):
            t += "!"
        return t

    def parse_directives(self):
        while self.peek().kind == "@":
            self.next()
            self.expect("name")
            if self.peek().kind == "(":
                self.parse_arguments()
        return []

    def parse_selection_set(self):
        self.expect("{")
        fields = []
        while self.peek().kind != "}":
            fields.append(self.parse_field())
        self.expect("}")
        return fields

    def parse_field(self):
        if self.peek().kind == "...":
            self.next()
            if self.peek().kind == "name" and self.peek().value == "on":
                self.next()
                type_name = self.expect("name").value
                self.parse_directives()
                sel = self.parse_selection_set()
                return {"fragment": True, "type": type_name, "selection": sel}
            name = self.expect("name").value
            self.parse_directives()
            return {"fragment": True, "spread": name}
        alias = None
        name = self.expect("name").value
        if self.peek().kind == ":":
            self.next()
            alias = name
            name = self.expect("name").value
        args = {}
        if self.peek().kind == "(":
            args = self.parse_arguments()
        self.parse_directives()
        sel = None
        if self.peek().kind == "{":
            sel = self.parse_selection_set()
        return {"name": name, "alias": alias or name, "args": args,
                "selection": sel}

    def parse_arguments(self):
        self.expect("(")
        args = {}
        while self.peek().kind != ")":
            name = self.expect("name").value
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        t = self.peek()
        if t.kind == "$":
            self.next()
            return ("var", self.expect("name").value)
        if t.kind == "string":
            self.next()
            return t.value
        if t.kind in ("int", "float"):
            self.next()
            return t.value
        if t.kind == "name":
            self.next()
            if t.value == "true":
                return True
            if t.value == "false":
                return False
            if t.value == "null":
                return None
            return ("enum", t.value)
        if t.kind == "[":
            self.next()
            out = []
            while self.peek().kind != "]":
                out.append(self.parse_value())
            self.expect("]")
            return out
        if t.kind == "{":
            self.next()
            out = {}
            while self.peek().kind != "}":
                k = self.expect("name").value
                self.expect(":")
                out[k] = self.parse_value()
            self.expect("}")
            return out
        raise ValueError("unexpected value token %s" % t.kind)


def _resolve_value(v, variables):
    if isinstance(v, tuple) and v and v[0] == "var":
        return variables.get(v[1])
    if isinstance(v, tuple) and v and v[0] == "enum":
        return v[1]
    if isinstance(v, list):
        return [_resolve_value(x, variables) for x in v]
    if isinstance(v, dict):
        return {k: _resolve_value(x, variables) for k, x in v.items()}
    return v


def _resolve_args(args, variables):
    return {k: _resolve_value(v, variables) for k, v in args.items()}


class _GqlError(Exception):
    pass


def _cursor_encode(idx):
    return _b64e("cursor:%d" % idx)


def _cursor_decode(cursor):
    try:
        text = base64.b64decode(cursor.encode("ascii")).decode("ascii")
        if text.startswith("cursor:"):
            return int(text[len("cursor:"):])
    except Exception:
        return None
    return None


def _decode_global_id(gid):
    try:
        text = base64.b64decode(gid.encode("ascii")).decode("ascii")
    except Exception:
        return None
    parts = text.split(":")
    if len(parts) < 2:
        return None
    return parts[0], parts[1:]


class GraphQLExecutor:
    def __init__(self):
        self.errors = []

    # -- public ------------------------------------------------------------
    def execute(self, doc_text, variables):
        self.errors = []
        try:
            ops = _GqlParser(_gql_lex(doc_text)).parse_document()
        except Exception as exc:
            return {"data": None, "errors": [{"message": "Syntax Error: %s" % exc}]}
        if not ops:
            return {"data": None, "errors": [{"message": "Syntax Error: empty document"}]}
        op = ops[0]
        if op["kind"] == "mutation":
            data = self._exec_selection(op["selection"], "Mutation", None, variables)
        else:
            data = self._exec_selection(op["selection"], "Query", None, variables)
        out = {"data": data}
        if self.errors:
            out["errors"] = self.errors
        return out

    # -- validation + execution ----------------------------------------------
    def _validate(self, fields, parent_type):
        allowed = _GQL_TYPES.get(parent_type, set())
        for f in fields:
            if f.get("fragment"):
                if f.get("type"):
                    self._validate(f["selection"], f["type"])
                continue
            if f["name"] not in allowed:
                self.errors.append({"message":
                    'Cannot query field "%s" on type "%s".' % (f["name"], parent_type)})

    def _exec_selection(self, fields, parent_type, obj, variables):
        self._validate(fields, parent_type)
        if self.errors:
            return None
        data = {}
        for f in fields:
            if f.get("fragment"):
                sub = self._exec_selection(f["selection"], f.get("type", parent_type),
                                           obj, variables)
                if sub:
                    data.update(sub)
                continue
            args = _resolve_args(f.get("args", {}), variables)
            value = self._field(parent_type, obj, f["name"], args, f, variables)
            data[f["alias"]] = value
        return data

    # -- field resolvers -------------------------------------------------------
    def _field(self, ptype, obj, name, args, field, variables):
        if ptype == "Query":
            if name == "viewer":
                return self._exec_selection(field["selection"] or [], "User",
                                            VIEWER, variables)
            if name == "repository":
                repo = STORE.repos.get((args.get("owner"), args.get("name")))
                if repo is None or repo.owner != args.get("owner"):
                    return None
                return self._exec_selection(field["selection"] or [], "Repository",
                                            repo, variables)
            if name == "node":
                return self._node(args.get("id"), field, variables)
            if name == "__type":
                return self._type_info(args.get("name"))
            if name == "__schema":
                return {"types": []}
            return None
        if ptype == "Mutation":
            return self._mutation(name, args, field, variables)
        if ptype == "Repository":
            return self._repo_field(obj, name, args, field, variables)
        if ptype == "Issue":
            return self._issue_field(obj, name, args, field, variables)
        if ptype == "PullRequest":
            return self._pr_field(obj, name, args, field, variables)
        if ptype == "User":
            if name == "login":
                return obj["login"]
            if name == "id":
                return _b64e("User:%d" % obj["id"])
            if name == "name":
                return obj["name"]
            if name == "email":
                return obj["email"]
            if name == "url":
                return "https://example.invalid/%s" % obj["login"]
            return None
        if ptype == "Ref":
            if name == "name":
                return obj.get("name")
            if name == "target":
                return obj.get("target")
            return None
        if ptype == "IssueComment":
            if name == "id":
                return obj["node_id"]
            if name == "body":
                return obj["body"]
            if name == "author":
                return self._exec_selection(field["selection"] or [], "User",
                                            VIEWER, variables)
            if name == "createdAt":
                return obj["created_at"]
            if name == "updatedAt":
                return obj["updated_at"]
            return None
        return None

    def _type_info(self, name):
        if name == "Issue":
            return {"name": "Issue", "kind": "OBJECT",
                    "fields": [{"name": f} for f in _GQL_ISSUE_FIELDS],
                    "enumValues": None}
        if name == "PullRequest":
            return {"name": "PullRequest", "kind": "OBJECT",
                    "fields": [{"name": f} for f in _GQL_PR_FIELDS],
                    "enumValues": None}
        if name == "Repository":
            return {"name": "Repository", "kind": "OBJECT",
                    "fields": [{"name": f} for f in _GQL_REPO_FIELDS],
                    "enumValues": None}
        if name == "SearchType":
            return {"name": "SearchType", "kind": "ENUM", "fields": None,
                    "enumValues": [{"name": n} for n in
                                   ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"]]}
        if name in ("User", "Actor", "Ref", "IssueComment"):
            fields = {"User": _GQL_USER_FIELDS, "Actor": _GQL_USER_FIELDS,
                      "Ref": _GQL_REF_FIELDS, "IssueComment": _GQL_COMMENT_FIELDS}[name]
            return {"name": name, "kind": "OBJECT",
                    "fields": [{"name": f} for f in fields], "enumValues": None}
        return None

    def _node(self, gid, field, variables):
        dec = _decode_global_id(gid or "")
        if not dec:
            return None
        kind, rest = dec
        sel = field.get("selection") or []
        if kind == "Repository":
            try:
                rid = int(rest[0])
            except (ValueError, IndexError):
                return None
            repo = next((r for r in STORE.repos.values() if r.id == rid), None)
            if repo is None:
                return None
            # inline fragments choose the type; execute as Repository
            out = {}
            for f in sel:
                if f.get("fragment"):
                    sub = self._exec_selection(f["selection"], f.get("type", "Repository"),
                                               repo, variables)
                    if sub:
                        out.update(sub)
                    continue
                args = _resolve_args(f.get("args", {}), variables)
                out[f["alias"]] = self._field("Repository", repo, f["name"], args, f, variables)
            return out
        if kind == "Issue":
            try:
                rid, number = int(rest[0]), int(rest[1])
            except (ValueError, IndexError):
                return None
            repo = next((r for r in STORE.repos.values() if r.id == rid), None)
            if repo is None:
                return None
            issue = repo.issues.get(number)
            if issue is None:
                return None
            return self._exec_selection(sel, "Issue", (repo, issue), variables)
        if kind == "PullRequest":
            try:
                rid, number = int(rest[0]), int(rest[1])
            except (ValueError, IndexError):
                return None
            repo = next((r for r in STORE.repos.values() if r.id == rid), None)
            if repo is None:
                return None
            pr = repo.pulls.get(number)
            if pr is None:
                return None
            return self._exec_selection(sel, "PullRequest", (repo, pr), variables)
        return None

    # -- repository fields -------------------------------------------------------
    def _repo_field(self, repo, name, args, field, variables):
        if name == "id":
            return repo.global_id()
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return repo.full_name()
        if name == "owner":
            return self._exec_selection(field["selection"] or [], "User",
                                        {"login": repo.owner, "id": VIEWER["id"],
                                         "name": VIEWER["name"], "email": VIEWER["email"]},
                                        variables)
        if name == "defaultBranchRef":
            tip = repo.refs.get("refs/heads/" + repo.default_branch)
            if tip is None:
                return None
            return self._exec_selection(field["selection"] or [], "Ref",
                                        {"name": repo.default_branch,
                                         "target": {"oid": tip}}, variables)
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "description":
            return repo.description
        if name == "isPrivate":
            return repo.private
        if name == "url":
            return "https://example.invalid/%s" % repo.full_name()
        if name == "createdAt":
            return _iso(EPOCH_BASE + repo.created_seq)
        if name == "updatedAt":
            return _iso(EPOCH_BASE + repo.updated_seq)
        if name == "issue":
            issue = repo.issues.get(args.get("number"))
            if issue is None:
                return None
            return self._exec_selection(field["selection"] or [], "Issue",
                                        (repo, issue), variables)
        if name == "issues":
            return self._issues_connection(repo, args, field, variables)
        if name == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            if pr is None:
                return None
            return self._exec_selection(field["selection"] or [], "PullRequest",
                                        (repo, pr), variables)
        if name == "pullRequests":
            return self._prs_connection(repo, args, field, variables)
        if name == "labels":
            return []
        return None

    def _issues_connection(self, repo, args, field, variables):
        issues = list(repo.issues.values())
        states = args.get("states")
        if states:
            want = {"OPEN": "open", "CLOSED": "closed"}
            issues = [i for i in issues if i["state"] in
                      {want.get(s, s.lower()) for s in states}]
        order = args.get("orderBy") or {}
        if isinstance(order, dict) and order.get("direction") == "DESC":
            issues.sort(key=lambda i: i["created_seq"], reverse=True)
        else:
            issues.sort(key=lambda i: i["created_seq"])
        first = args.get("first")
        after = args.get("after")
        start = 0
        if after:
            idx = _cursor_decode(after)
            if idx is not None:
                start = idx + 1
        total = len(issues)
        if first is not None:
            page = issues[start:start + first]
        else:
            page = issues[start:]
        nodes = [self._exec_selection(field["selection"] or [], "IssueConnection",
                                      None, variables) if False else None
                 for _ in page]
        # nodes need the Issue selection from inside the connection selection
        node_sel = []
        page_sel = None
        for f in (field.get("selection") or []):
            if f["name"] == "nodes":
                node_sel = f.get("selection") or []
            if f["name"] == "pageInfo":
                page_sel = f.get("selection") or []
        nodes = [self._exec_selection(node_sel, "Issue", (repo, i), variables)
                 for i in page]
        end = start + len(page)
        page_info = {"hasNextPage": end < total, "hasPreviousPage": start > 0,
                     "endCursor": _cursor_encode(end - 1) if page else None,
                     "startCursor": _cursor_encode(start) if page else None}
        out = {}
        for f in (field.get("selection") or []):
            if f["name"] == "nodes":
                out[f["alias"]] = nodes
            elif f["name"] == "pageInfo":
                out[f["alias"]] = {k: v for k, v in page_info.items()
                                   if page_sel is None or k in
                                   [g["name"] for g in page_sel]}
            elif f["name"] == "totalCount":
                out[f["alias"]] = total
            elif f["name"] == "edges":
                out[f["alias"]] = [{"node": n, "cursor": _cursor_encode(start + i)}
                                   for i, n in enumerate(nodes)]
        return out

    def _prs_connection(self, repo, args, field, variables):
        prs = list(repo.pulls.values())
        states = args.get("states")
        if states:
            want = {"OPEN": "open", "CLOSED": "closed", "MERGED": "closed"}
            prs = [p for p in prs if p["state"] in
                   {want.get(s, s.lower()) for s in states}]
        else:
            prs = [p for p in prs if p["state"] == "open"]
        prs.sort(key=lambda p: p["created_seq"], reverse=True)
        first = args.get("first")
        page = prs[:first] if first is not None else prs
        node_sel = []
        for f in (field.get("selection") or []):
            if f["name"] == "nodes":
                node_sel = f.get("selection") or []
        nodes = [self._exec_selection(node_sel, "PullRequest", (repo, p), variables)
                 for p in page]
        out = {}
        for f in (field.get("selection") or []):
            if f["name"] == "nodes":
                out[f["alias"]] = nodes
            elif f["name"] == "pageInfo":
                out[f["alias"]] = {"hasNextPage": False, "hasPreviousPage": False,
                                   "endCursor": None, "startCursor": None}
            elif f["name"] == "totalCount":
                out[f["alias"]] = len(prs)
            elif f["name"] == "edges":
                out[f["alias"]] = [{"node": n, "cursor": None} for n in nodes]
        return out

    # -- issue / PR fields -------------------------------------------------------
    def _issue_field(self, obj, name, args, field, variables):
        repo, issue = obj
        if name == "id":
            return issue["node_id"]
        if name == "number":
            return issue["number"]
        if name == "title":
            return issue["title"]
        if name == "body":
            return issue["body"]
        if name == "state":
            return issue["state"].upper()
        if name == "createdAt":
            return issue["created_at"]
        if name == "updatedAt":
            return issue["updated_at"]
        if name == "closedAt":
            return issue["closed_at"]
        if name == "url":
            return "https://example.invalid/%s/issues/%d" % (repo.full_name(), issue["number"])
        if name == "author":
            return self._exec_selection(field["selection"] or [], "User",
                                        VIEWER, variables)
        if name == "labels":
            return {"nodes": [dict(l) for l in issue["labels"]]}
        if name == "comments":
            return {"nodes": []}
        if name == "repository":
            return self._exec_selection(field["selection"] or [], "Repository",
                                        repo, variables)
        return None

    def _pr_field(self, obj, name, args, field, variables):
        repo, pr = obj
        if name == "id":
            return pr["node_id"]
        if name == "number":
            return pr["number"]
        if name == "title":
            return pr["title"]
        if name == "body":
            return pr["body"]
        if name == "state":
            if pr["merged"]:
                return "MERGED"
            return pr["state"].upper()
        if name == "headRefName":
            return pr["head"]
        if name == "baseRefName":
            return pr["base"]
        if name == "mergeable":
            head_sha = repo.refs.get("refs/heads/" + pr["head"], "")
            base_sha = repo.refs.get("refs/heads/" + pr["base"], "")
            if not head_sha or not base_sha:
                return "UNKNOWN"
            return "CONFLICTING" if repo.pr_conflicts(base_sha, head_sha) else "MERGEABLE"
        if name == "merged":
            return pr["merged"]
        if name == "createdAt":
            return pr["created_at"]
        if name == "updatedAt":
            return pr["updated_at"]
        if name == "closedAt":
            return pr["closed_at"]
        if name == "url":
            return "https://example.invalid/%s/pull/%d" % (repo.full_name(), pr["number"])
        if name == "author":
            return self._exec_selection(field["selection"] or [], "User",
                                        VIEWER, variables)
        if name == "headRef":
            return self._exec_selection(field["selection"] or [], "Ref",
                                        {"name": pr["head"]}, variables)
        if name == "baseRef":
            return self._exec_selection(field["selection"] or [], "Ref",
                                        {"name": pr["base"]}, variables)
        if name == "mergeCommit":
            if pr["merge_commit_sha"]:
                return {"oid": pr["merge_commit_sha"]}
            return None
        if name == "files":
            head_sha = repo.refs.get("refs/heads/" + pr["head"], "")
            base_sha = repo.refs.get("refs/heads/" + pr["base"], "")
            files = repo.diff_files(base_sha, head_sha)
            first = args.get("first")
            if first is not None:
                files = files[:first]
            nodes = [{"path": f["filename"], "additions": f["additions"],
                      "deletions": f["deletions"], "changeType": f["status"].upper()}
                     for f in files]
            out = {}
            for f in (field.get("selection") or []):
                if f["name"] == "nodes":
                    out[f["alias"]] = nodes
                elif f["name"] == "totalCount":
                    out[f["alias"]] = len(files)
                elif f["name"] == "pageInfo":
                    out[f["alias"]] = {"hasNextPage": False, "hasPreviousPage": False,
                                       "endCursor": None, "startCursor": None}
            return out
        if name == "repository":
            return self._exec_selection(field["selection"] or [], "Repository",
                                        repo, variables)
        return None

    # -- mutations ---------------------------------------------------------------
    def _mutation(self, name, args, field, variables):
        inp = args.get("input") or {}
        sel = field.get("selection") or []
        if name == "createIssue":
            dec = _decode_global_id(inp.get("repositoryId") or "")
            repo = None
            if dec and dec[0] == "Repository":
                try:
                    rid = int(dec[1][0])
                    repo = next((r for r in STORE.repos.values() if r.id == rid), None)
                except (ValueError, IndexError):
                    repo = None
            if repo is None:
                self.errors.append({"message": "Could not resolve to a Repository with the id provided."})
                return None
            issue = _new_issue(repo, inp.get("title", ""), inp.get("body", ""), [])
            out = {}
            for f in sel:
                if f["name"] == "issue":
                    out[f["alias"]] = self._exec_selection(f.get("selection") or [], "Issue",
                                                            (repo, issue), variables)
            return out
        if name == "closeIssue":
            dec = _decode_global_id(inp.get("issueId") or "")
            issue = None
            repo = None
            if dec and dec[0] == "Issue":
                try:
                    rid, number = int(dec[1][0]), int(dec[1][1])
                    repo = next((r for r in STORE.repos.values() if r.id == rid), None)
                    issue = repo.issues.get(number) if repo else None
                except (ValueError, IndexError):
                    pass
            if issue is None:
                self.errors.append({"message": "Could not resolve to an Issue with the id provided."})
                return None
            issue["state"] = "closed"
            issue["closed_at"] = _iso(EPOCH_BASE + STORE.seq)
            out = {}
            for f in sel:
                if f["name"] == "issue":
                    out[f["alias"]] = self._exec_selection(f.get("selection") or [], "Issue",
                                                            (repo, issue), variables)
            return out
        if name == "createPullRequest":
            dec = _decode_global_id(inp.get("repositoryId") or "")
            repo = None
            if dec and dec[0] == "Repository":
                try:
                    rid = int(dec[1][0])
                    repo = next((r for r in STORE.repos.values() if r.id == rid), None)
                except (ValueError, IndexError):
                    repo = None
            if repo is None:
                self.errors.append({"message": "Could not resolve to a Repository with the id provided."})
                return None
            head = inp.get("headRefName", "")
            base = inp.get("baseRefName", repo.default_branch)
            if ("refs/heads/" + head) not in repo.refs:
                self.errors.append({"message": "Head branch %s does not exist." % head})
                return None
            pr = _new_pull(repo, inp.get("title", ""), inp.get("body", ""), head, base)
            out = {}
            for f in sel:
                if f["name"] == "pullRequest":
                    out[f["alias"]] = self._exec_selection(f.get("selection") or [], "PullRequest",
                                                            (repo, pr), variables)
            return out
        if name == "mergePullRequest":
            dec = _decode_global_id(inp.get("pullRequestId") or "")
            pr = None
            repo = None
            if dec and dec[0] == "PullRequest":
                try:
                    rid, number = int(dec[1][0]), int(dec[1][1])
                    repo = next((r for r in STORE.repos.values() if r.id == rid), None)
                    pr = repo.pulls.get(number) if repo else None
                except (ValueError, IndexError):
                    pass
            if pr is None or repo is None:
                self.errors.append({"message": "Could not resolve to a PullRequest with the id provided."})
                return None
            try:
                _merge_pull(repo, pr, {"merge_method": "squash"})
            except ForgeError as exc:
                self.errors.append({"message": exc.message})
                return None
            out = {}
            for f in sel:
                if f["name"] == "pullRequest":
                    out[f["alias"]] = self._exec_selection(f.get("selection") or [], "PullRequest",
                                                            (repo, pr), variables)
            return out
        if name == "addComment":
            dec = _decode_global_id(inp.get("subjectId") or "")
            issue = None
            repo = None
            if dec and dec[0] == "Issue":
                try:
                    rid, number = int(dec[1][0]), int(dec[1][1])
                    repo = next((r for r in STORE.repos.values() if r.id == rid), None)
                    issue = repo.issues.get(number) if repo else None
                except (ValueError, IndexError):
                    pass
            if issue is None:
                self.errors.append({"message": "Could not resolve to an Issue with the id provided."})
                return None
            cid = STORE.next_comment_id
            STORE.next_comment_id += 1
            seq = STORE.tick()
            comment = {"id": cid, "node_id": _b64e("Comment:%d" % cid),
                       "body": inp.get("body", ""),
                       "created_at": _iso(EPOCH_BASE + seq),
                       "updated_at": _iso(EPOCH_BASE + seq)}
            issue["comments"].append(comment)
            out = {}
            for f in sel:
                if f["name"] == "commentEdge":
                    node = None
                    for g in (f.get("selection") or []):
                        if g["name"] == "node":
                            node = self._exec_selection(g.get("selection") or [], "IssueComment",
                                                        comment, variables)
                    out[f["alias"]] = {"node": node}
            return out
        self.errors.append({"message": 'Cannot query field "%s" on type "Mutation".' % name})
        return None


def graphql_dispatch(body):
    """body: parsed JSON (dict or list). Returns a dict or list result."""
    executor = GraphQLExecutor()
    if isinstance(body, list):
        return [executor.execute(item.get("query", ""),
                                 item.get("variables") or {}) for item in body]
    if not isinstance(body, dict):
        return {"data": None, "errors": [{"message": "Request body must be a JSON object."}]}
    return executor.execute(body.get("query", ""), body.get("variables") or {})

# --------------------------------------------------------------------------
# MCP (Model Context Protocol, Streamable HTTP)
# --------------------------------------------------------------------------

MCP_REVISIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "name": {"type": "string", "description": "Repository name"},
                         "description": {"type": "string", "description": "Repository description"},
                         "private": {"type": "boolean", "description": "Whether the repository is private"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "title": {"type": "string", "description": "Issue title"},
                         "body": {"type": "string", "description": "Issue body"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "state": {"type": "string", "description": "Issue state: open, closed or all"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request from a head branch into a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "title": {"type": "string", "description": "Pull request title"},
                         "body": {"type": "string", "description": "Pull request body"},
                         "head": {"type": "string", "description": "Head branch name"},
                         "base": {"type": "string", "description": "Base branch name"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request with a squash commit.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "pull_number": {"type": "integer", "description": "Pull request number"}},
                     "required": ["owner", "repo", "pull_number"]}},
    {"name": "get_issue",
     "description": "Get one issue by number.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "issue_number": {"type": "integer", "description": "Issue number"}},
                     "required": ["owner", "repo", "issue_number"]}},
    {"name": "list_pull_requests",
     "description": "List pull requests in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string", "description": "Repository owner login"},
                         "repo": {"type": "string", "description": "Repository name"},
                         "state": {"type": "string", "description": "Pull request state: open, closed or all"}},
                     "required": ["owner", "repo"]}},
]


def _mcp_result(obj):
    text = json.dumps(obj, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": obj}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _tool_call(name, args):
    """Returns (result_dict, is_error)."""
    try:
        if name == "create_repo":
            repo_name = args.get("name")
            if not repo_name:
                return _mcp_error_result("Missing required argument: name"), True
            if (VIEWER["login"], repo_name) in STORE.repos:
                raise ForgeError(422, "Repository already exists")
            repo = Repo(STORE, VIEWER["login"], repo_name,
                        args.get("description", ""), bool(args.get("private", False)))
            STORE.repos[(VIEWER["login"], repo_name)] = repo
            return _mcp_result(repo_json(repo)), False
        if name == "get_repo":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            return _mcp_result(repo_json(repo)), False
        if name == "create_issue":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            title = args.get("title")
            if not title:
                return _mcp_error_result("Missing required argument: title"), True
            issue = _new_issue(repo, title, args.get("body", ""), [])
            return _mcp_result(issue_json(repo, issue)), False
        if name == "list_issues":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            state = args.get("state", "open")
            items = list(repo.issues.values())
            if state != "all":
                items = [i for i in items if i["state"] == state]
            items.sort(key=lambda i: i["created_seq"])
            return _mcp_result([issue_json(repo, i) for i in items]), False
        if name == "create_pull_request":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            head = args.get("head")
            base = args.get("base", repo.default_branch)
            if not head:
                return _mcp_error_result("Missing required argument: head"), True
            if ("refs/heads/" + head) not in repo.refs:
                return _mcp_error_result("Head branch does not exist: %s" % head), True
            for pr in repo.pulls.values():
                if pr["head"] == head and pr["base"] == base and pr["state"] == "open":
                    return _mcp_error_result("Pull request already exists"), True
            pr = _new_pull(repo, args.get("title", ""), args.get("body", ""), head, base)
            return _mcp_result(pull_json(repo, pr)), False
        if name == "merge_pull_request":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            number = args.get("pull_number")
            if number is None:
                return _mcp_error_result("Missing required argument: pull_number"), True
            pr = repo.pulls.get(int(number))
            if pr is None:
                return _mcp_error_result("Pull request not found"), True
            status, merged, _ = _merge_pull(repo, pr, {"merge_method": "squash"})
            out = pull_json(repo, pr)
            out["merged"] = True
            out["sha"] = merged["sha"]
            return _mcp_result(out), False
        if name == "get_issue":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            issue = repo.issues.get(int(args.get("issue_number", -1)))
            if issue is None:
                return _mcp_error_result("Issue not found"), True
            return _mcp_result(issue_json(repo, issue)), False
        if name == "list_pull_requests":
            repo = get_repo_or_404(args.get("owner"), args.get("repo"))
            state = args.get("state", "open")
            items = list(repo.pulls.values())
            if state != "all":
                items = [p for p in items if p["state"] == state]
            items.sort(key=lambda p: p["created_seq"], reverse=True)
            return _mcp_result([pull_json(repo, p) for p in items]), False
    except ForgeError as exc:
        return _mcp_error_result(exc.message), True
    return None, True


def _mcp_tools_list():
    return [dict(t) for t in MCP_TOOLS]


def mcp_dispatch(raw_body):
    """Returns (http_status, response_obj_or_None)."""
    try:
        req = json.loads(raw_body.decode("utf-8"))
    except Exception:
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32700, "message": "Parse error"}}
    if not isinstance(req, dict):
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32600, "message": "Invalid Request"}}
    rid = req.get("id")
    method = req.get("method")
    params = req.get("params") or {}
    is_notification = "id" not in req
    if method == "server/discover":
        result = {
            "resultType": "DiscoverResult",
            "supportedVersions": list(MCP_REVISIONS),
            "capabilities": {"tools": {}},
            "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
            "instructions": "A GitHub-compatible git forge.",
            "_meta": {"io.modelcontextprotocol/serverInfo":
                      {"name": SERVER_NAME, "version": SERVER_VERSION}},
        }
        return 200, {"jsonrpc": "2.0", "id": rid, "result": result}
    if method == "initialize":
        offered = params.get("protocolVersion", "2025-03-26")
        chosen = offered if offered in MCP_REVISIONS else "2025-03-26"
        result = {"protocolVersion": chosen,
                  "capabilities": {"tools": {}},
                  "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION}}
        return 200, {"jsonrpc": "2.0", "id": rid, "result": result}
    if method == "notifications/initialized":
        return 202, None
    if method == "ping":
        return 200, {"jsonrpc": "2.0", "id": rid, "result": {}}
    if method == "tools/list":
        return 200, {"jsonrpc": "2.0", "id": rid,
                     "result": {"tools": _mcp_tools_list()}}
    if method == "tools/call":
        name = params.get("name")
        args = params.get("arguments") or {}
        tool = next((t for t in MCP_TOOLS if t["name"] == name), None)
        if tool is None:
            return 200, {"jsonrpc": "2.0", "id": rid,
                         "error": {"code": -32602, "message": "Unknown tool: %s" % name}}
        missing = [p for p in tool["inputSchema"].get("required", [])
                   if p not in args or args[p] is None]
        if missing:
            return 200, {"jsonrpc": "2.0", "id": rid,
                         "result": _mcp_error_result(
                             "Missing required arguments: %s" % ", ".join(missing))}
        result, _is_err = _tool_call(name, args)
        return 200, {"jsonrpc": "2.0", "id": rid, "result": result}
    if is_notification:
        return 202, None
    return 200, {"jsonrpc": "2.0", "id": rid,
                 "error": {"code": -32601, "message": "Method not found: %s" % method}}


# --------------------------------------------------------------------------
# HTTP server
# --------------------------------------------------------------------------

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


def _auth_ok(headers):
    if not TOKEN:
        return True
    auth = headers.get("Authorization", "")
    return auth == "Bearer " + TOKEN


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "git-forge/1.0"

    def log_message(self, fmt, *args):  # keep stdout clean
        pass

    def setup(self):
        super().setup()
        # Kill the Nagle/delayed-ACK 40 ms stall: keep-alive clients (the
        # suite reuses one connection per workload) otherwise pay it per
        # request, which alone costs the whole perf budget.
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    # -- plumbing ------------------------------------------------------------
    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _send(self, status, body, ctype="application/json; charset=utf-8",
              extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        if body is None:
            body = b""
        STORE.req_seq += 1
        headers = {"Server": "git-forge/1.0",
                   "Content-Type": ctype,
                   "Content-Length": str(len(body)),
                   "X-GitHub-Request-Id": "req-%d" % STORE.req_seq}
        if extra:
            headers.update(extra)
        # One write for the whole response: many small writes on a
        # keep-alive connection trigger the Nagle/delayed-ACK stall.
        reason = self.responses.get(status, ("", ""))[0] or "OK"
        head = ("HTTP/1.1 %d %s\r\n" % (status, reason)).encode("ascii")
        head += b"".join(("%s: %s\r\n" % (k, v)).encode("latin-1") for k, v in headers.items())
        head += b"\r\n"
        if self.command == "HEAD" or not body:
            self.wfile.write(head)
        else:
            self.wfile.write(head + body)

    def _send_json(self, status, obj, extra=None):
        if obj is None:
            self._send(status, b"", extra=extra)
        else:
            self._send(status, _json_bytes(obj), extra=extra)

    def _err(self, status, message):
        self._send_json(status, {"message": message})

    # -- routing ---------------------------------------------------------------
    def _route(self, method):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query, keep_blank_values=True)
        base_url = "http://%s" % (self.headers.get("Host") or "127.0.0.1")
        try:
            body_bytes = self._read_body()
            with STORE.lock:
                return self._dispatch(method, path, query, body_bytes, base_url)
        except ForgeError as exc:
            return ("json", exc.status, {"message": exc.message}, {})
        except Exception as exc:  # never crash on a request
            return ("json", 500, {"message": "Internal error: %s" % exc}, {})

    def _dispatch(self, method, path, query, body_bytes, base_url):
        # health probe: no auth
        if method == "GET" and path == "/healthz":
            return ("json", 200, {"ok": True}, {})
        # git smart HTTP: /{owner}/{repo}.git/...
        m = re.match(r"^/([^/]+)/([^/]+)\.git(/.*)?$", path)
        if m and (m.group(3) or "").startswith(("/info/refs", "/git-upload-pack", "/git-receive-pack")):
            owner, repo_name = unquote(m.group(1)), unquote(m.group(2))
            suffix = m.group(3) or ""
            repo = STORE.repos.get((owner, repo_name))
            if repo is None:
                return ("raw", 404, b'{"message":"Not Found"}\n',
                        "application/json; charset=utf-8")
            if suffix.startswith("/info/refs"):
                service = query.get("service", [""])[0]
                if service == "git-receive-pack":
                    return ("raw", 200, git_advertise_v0(repo, "git-receive-pack"),
                            "application/x-git-receive-pack-advertisement")
                if self.headers.get("Git-Protocol", "") == "version=2":
                    return ("raw", 200, git_advertise_v2(repo),
                            "application/x-git-upload-pack-advertisement")
                return ("raw", 200, git_advertise_v0(repo, "git-upload-pack"),
                        "application/x-git-upload-pack-advertisement")
            if suffix == "/git-upload-pack" and method == "POST":
                status, ctype, data = handle_git_upload_pack(repo, body_bytes)
                return ("raw", status, data, ctype)
            if suffix == "/git-receive-pack" and method == "POST":
                status, ctype, data = handle_git_receive_pack(repo, body_bytes)
                return ("raw", status, data, ctype)
            return ("json", 404, {"message": "Not Found"}, {})
        # API surfaces require auth
        if path.startswith("/api/v3") or path == "/api/graphql" or path == "/mcp":
            if not _auth_ok(self.headers):
                return ("json", 401, {"message": "Requires authentication"}, {})
        if path == "/api/graphql":
            if method != "POST":
                return ("json", 404, {"message": "Not Found"}, {})
            try:
                payload = json.loads(body_bytes.decode("utf-8")) if body_bytes else {}
            except Exception:
                return ("json", 400, {"message": "Malformed JSON body"}, {})
            result = graphql_dispatch(payload)
            return ("json", 200, result, {})
        if path == "/mcp":
            if method == "GET":
                return ("json", 405, {"message": "Method Not Allowed"}, {})
            if method == "DELETE":
                return ("raw", 204, b"", "application/json; charset=utf-8")
            if method != "POST":
                return ("json", 405, {"message": "Method Not Allowed"}, {})
            status, obj = mcp_dispatch(body_bytes)
            if obj is None:
                return ("raw", status, b"", "application/json; charset=utf-8")
            return ("json", status, obj, {})
        if path.startswith("/api/v3"):
            body = None
            if body_bytes:
                try:
                    body = json.loads(body_bytes.decode("utf-8"))
                except Exception:
                    return ("json", 400, {"message": "Malformed JSON body"}, {})
            status, obj, extra = rest_dispatch(method, path, query, body, base_url)
            return ("json", status, obj, extra)
        return ("json", 404, {"message": "Not Found"}, {})

    def _handle(self, method):
        kind, status, payload, extra = self._route(method)
        if kind == "raw":
            ctype = extra if isinstance(extra, str) else "application/octet-stream"
            self._send(status, payload, ctype=ctype)
        else:
            self._send_json(status, payload, extra=extra if isinstance(extra, dict) else {})

    def do_GET(self):
        self._handle("GET")

    def do_POST(self):
        self._handle("POST")

    def do_PUT(self):
        self._handle("PUT")

    def do_PATCH(self):
        self._handle("PATCH")

    def do_DELETE(self):
        self._handle("DELETE")

    def do_HEAD(self):
        self._handle("HEAD")


# --------------------------------------------------------------------------
# Lifecycle
# --------------------------------------------------------------------------

def _http_json(url, method, payload=None, timeout=30):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()
    except Exception:
        return 0, b""


def main():
    standalone = "--standalone" in sys.argv
    port_arg = None
    if "--port" in sys.argv:
        try:
            port_arg = int(sys.argv[sys.argv.index("--port") + 1])
        except (ValueError, IndexError):
            port_arg = None
    env_url = (os.environ.get("MAKEFUN_ENV_URL") or "").rstrip("/")
    if not env_url and not standalone:
        sys.stderr.write("[entry] MAKEFUN_ENV_URL is not set: there is no env to register with\n")
        return 1
    # The bench opens 50 clone connections at once; the socketserver
    # default listen backlog is 5, which drops SYNs and costs ~1 s
    # retransmits. Raise it before the socket is bound.
    ThreadingHTTPServer.request_queue_size = 128
    server = ThreadingHTTPServer(("127.0.0.1", port_arg or 0), Handler)
    server.daemon_threads = True
    port = server.server_address[1]
    sys.stdout.write("[entry] listening on port %d\n" % port)
    sys.stdout.flush()
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    if standalone:
        sys.stdout.write("[entry] standalone mode on port %d (no env)\n" % port)
        sys.stdout.flush()
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            pass
        server.shutdown()
        return 0
    # register with retries
    attempt = 0
    while True:
        status, _ = _http_json(env_url + "/register", "POST", {"port": port})
        if status in (200, 409):
            break
        if status in (400, 405):
            sys.stderr.write("[entry] register answered HTTP %d\n" % status)
            return 1
        time.sleep(min(2.0, 0.25 * (2 ** min(attempt, 8))))
        attempt += 1
    sys.stdout.write("[entry] registered; waiting for the env to say done\n")
    sys.stdout.flush()
    attempt = 0
    while True:
        status, data = _http_json(env_url + "/done", "GET")
        if status == 200:
            try:
                if json.loads(data.decode("utf-8")).get("done") is True:
                    break
            except Exception:
                pass
        time.sleep(min(2.0, 0.25 * (2 ** min(attempt, 8))))
        attempt += 1
    server.shutdown()
    sys.stdout.write("[entry] done\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())

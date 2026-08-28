#!/usr/bin/env python3
# Vibe coded by Codex
"""Convert a PC/GEOS Field background VM file to a PNG image."""

from __future__ import annotations

import copy
import math
import os
import struct
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    from PIL import Image, ImageChops, ImageDraw
except ImportError as exc:  # pragma: no cover - depends on the host
    raise SystemExit("geoWorksGEOSBackground.py requires Pillow (PIL)") from exc


class FormatError(Exception):
    """The input is not a supported, structurally valid Field background."""


def need(condition: bool, message: str) -> None:
    if not condition:
        raise FormatError(message)


def u16(data: bytes, offset: int) -> int:
    need(0 <= offset <= len(data) - 2, "truncated 16-bit field")
    return struct.unpack_from("<H", data, offset)[0]


def s16(data: bytes, offset: int) -> int:
    need(0 <= offset <= len(data) - 2, "truncated signed 16-bit field")
    return struct.unpack_from("<h", data, offset)[0]


def u32(data: bytes, offset: int) -> int:
    need(0 <= offset <= len(data) - 4, "truncated 32-bit field")
    return struct.unpack_from("<I", data, offset)[0]


def s32(data: bytes, offset: int) -> int:
    need(0 <= offset <= len(data) - 4, "truncated signed 32-bit field")
    return struct.unpack_from("<i", data, offset)[0]


def round4(value: int) -> int:
    return (value + 3) & ~3


def fixed_16_16(data: bytes, offset: int) -> float:
    """Read GEOS WWFixed (fraction word followed by signed integer word)."""
    return s16(data, offset + 2) + u16(data, offset) / 65536.0


def fixed_32_16(data: bytes, offset: int) -> float:
    """Read GEOS DWFixed (fraction word followed by signed dword integer)."""
    return s32(data, offset + 2) + u16(data, offset) / 65536.0


@dataclass
class VMRecord:
    handle: int
    used: bool
    mem_or_next: int
    signature_or_prev_high: int
    flags_or_prev_low: int
    uid_or_size_low: int
    size: int
    position: int


class VMFile:
    GEOS2_MAGIC = b"\xc7E\xc1S"

    def __init__(self, data: bytes):
        self.data = data
        self.records: dict[int, VMRecord] = {}
        self.header_fields: dict[str, Any] = {}
        self._parse()

    def _parse(self) -> None:
        d = self.data
        need(len(d) >= 280, "file is too short for a GEOS 2.x VM file")
        need(d[:4] == self.GEOS2_MAGIC, "not a GEOS 2.x file")

        file_type = u16(d, 40)
        need(file_type == 2, "GEOS file is not a VM file")
        need(d[56:62] == b"BKGD\0\0", "GEOS token is not BKGD")
        protocol = (u16(d, 52), u16(d, 54))
        need(protocol in ((1, 0), (0, 0)), "unsupported background protocol")

        self.header_fields = {
            "long_name": d[4:40],
            "file_type": file_type,
            "flags": u16(d, 42),
            "release": struct.unpack_from("<4H", d, 44),
            "protocol": protocol,
            "token": d[56:62],
            "creator": d[62:68],
            "user_notes": d[68:168],
            "notice": d[168:200],
            "created_date": u16(d, 200),
            "created_time": u16(d, 202),
            "password": d[204:212],
            "desktop": d[212:228],
            "reserved": d[228:256],
        }

        need(u16(d, 256) == 0xADEB, "bad VM file signature")
        header_size = u16(d, 258)
        header_rel = u32(d, 260)
        self.update_counter = u16(d, 264)
        self.update_type = u16(d, 266)
        self.vm_reserved = struct.unpack_from("<6H", d, 268)
        need(header_rel >= 24, "VM header overlaps the fixed VM file header")
        header_pos = 256 + header_rel
        need(header_pos + header_size <= len(d), "VM header pointer is out of range")
        h = d[header_pos:header_pos + header_size]
        need(len(h) >= 32 and u16(h, 0) == 0x00FB, "bad VM header signature")

        assigned = u16(h, 2)
        last_assigned = u16(h, 4)
        unassigned = u16(h, 6)
        last_handle = u16(h, 8)
        counts = struct.unpack_from("<5h", h, 10)
        self.map_handle = u16(h, 20)
        self.compact_threshold = u16(h, 22)
        used_size = u32(h, 24)
        self.attributes = h[28]
        self.no_compress = h[29]
        self.db_map_handle = u16(h, 30)

        need(last_handle <= header_size and header_size - last_handle < 16,
             "VM handle-table capacity is inconsistent with header size")
        need(last_handle >= 32 and (last_handle - 32) % 12 == 0,
             "invalid VM handle-table size")

        for handle in range(32, last_handle, 12):
            raw = h[handle:handle + 12]
            need(len(raw) == 12, "truncated VM block record")
            sig = raw[2]
            if sig >= 0xFE:
                mem, sig, flags, uid, size, pos = struct.unpack("<HBBHHI", raw)
                need(size > 0, f"used VM block {handle:#x} has zero size")
                rec = VMRecord(handle, True, mem, sig, flags, uid, size, pos)
            else:
                nxt, prev, size, pos = struct.unpack("<HHII", raw)
                rec = VMRecord(handle, False, nxt, (prev >> 8) & 0xFF,
                               prev & 0xFF, size & 0xFFFF, size, pos)
            self.records[handle] = rec

        used = [r for r in self.records.values() if r.used]
        free_assigned = [r for r in self.records.values() if not r.used and r.size]
        free_unassigned = [r for r in self.records.values() if not r.used and not r.size]
        need(counts[0] == len(free_assigned), "VM assigned-block count mismatch")
        need(counts[1] == len(free_unassigned), "VM unassigned-handle count mismatch")
        need(counts[2] == len(used), "VM used-block count mismatch")
        # This is a cached runtime count, not an on-disk allocation count.  A
        # clean close may preserve any value from zero through numUsed.
        need(0 <= counts[3] <= counts[2], "invalid VM resident-block count")
        need(used_size == sum(r.size for r in used), "VM used-byte count mismatch")

        self._validate_assigned_chain(assigned, last_assigned, free_assigned)
        self._validate_unassigned_chain(unassigned, free_unassigned)

        intervals = sorted((r.position, r.position + r.size, r.handle)
                           for r in used + free_assigned)
        cursor = 24
        for start, end, handle in intervals:
            need(start == cursor, f"gap or overlap before VM block {handle:#x}")
            need(end > start and 256 + end <= len(d),
                 f"VM block {handle:#x} is outside the file")
            cursor = end
        need(256 + cursor == len(d), "unaccounted bytes at end of VM file")

        header_record = self.records.get(32)
        need(header_record is not None and header_record.used,
             "VM header block record is absent")
        expected_header_uid = 0 if protocol == (0, 0) else 0xADEB
        need(header_record.uid_or_size_low == expected_header_uid,
             "VM header block has wrong user ID")
        need(header_record.position == header_rel and header_record.size == header_size,
             "VM header block record disagrees with fixed header")
        need(self.map_handle in self.records and self.records[self.map_handle].used,
             "VM map handle is not a used block")

    @staticmethod
    def _prev(rec: VMRecord) -> int:
        return (rec.signature_or_prev_high << 8) | rec.flags_or_prev_low

    def _validate_assigned_chain(self, first: int, last: int,
                                 records: list[VMRecord]) -> None:
        expected = {r.handle for r in records}
        seen: list[int] = []
        prev = 0
        current = first
        while current:
            need(current in expected and current not in seen,
                 "broken VM assigned free-space chain")
            rec = self.records[current]
            need(self._prev(rec) == prev, "bad previous link in assigned chain")
            seen.append(current)
            prev, current = current, rec.mem_or_next
        need(set(seen) == expected, "assigned VM records are not all linked")
        need((seen[-1] if seen else 0) == last, "bad last-assigned VM handle")

    def _validate_unassigned_chain(self, first: int,
                                   records: list[VMRecord]) -> None:
        expected = {r.handle for r in records}
        seen: list[int] = []
        current = first
        while current:
            need(current in expected and current not in seen,
                 "broken VM unassigned-handle chain")
            seen.append(current)
            current = self.records[current].mem_or_next
        need(set(seen) == expected, "unassigned VM records are not all linked")

    def block(self, handle: int) -> bytes:
        rec = self.records.get(handle)
        need(rec is not None and rec.used, f"VM handle {handle:#x} is not used")
        start = 256 + rec.position
        return self.data[start:start + rec.size]


@dataclass
class LMemInfo:
    logical_size: int
    handle_offset: int
    handles: list[int]
    free_ranges: list[tuple[int, int]]
    live_ranges: list[tuple[int, int]]


def parse_lmem(block: bytes, expected_handles: int) -> LMemInfo:
    need(len(block) >= 16, "truncated LMem block")
    _, handle_off, flags, lmem_type, logical, nhandles, free_head, total_free = \
        struct.unpack_from("<8H", block, 0)
    need(flags & 0x0100, "HugeArray LMem block lacks LMF_IS_VM")
    need(not (flags & 0x0200), "HugeArray unexpectedly uses handle-less LMem")
    need(lmem_type == 0, "HugeArray LMem type is not general")
    need(16 <= logical <= len(block), "invalid LMem logical block size")
    need(nhandles == expected_handles, "unexpected HugeArray LMem handle count")
    need(handle_off >= 16 and handle_off + 2 * nhandles <= logical,
         "LMem handle table is out of range")
    handles = [u16(block, handle_off + 2 * i) for i in range(nhandles)]

    live_ranges: list[tuple[int, int]] = []
    for ptr in handles:
        if ptr in (0, 0xFFFF):
            continue
        need(ptr >= handle_off + 2 * nhandles + 2 and ptr < logical and ptr % 2 == 0,
             "LMem chunk pointer is out of range")
        stored_size = u16(block, ptr - 2)
        need(stored_size >= 2, "invalid LMem chunk size")
        end = ptr - 2 + round4(stored_size)
        need(end <= logical, "LMem chunk extends beyond logical block")
        live_ranges.append((ptr - 2, end))

    free_ranges: list[tuple[int, int]] = []
    seen: set[int] = set()
    current = free_head
    free_sum = 0
    while current:
        need(current not in seen and current % 2 == 0,
             "cyclic or unaligned LMem free list")
        need(current >= handle_off + 2 * nhandles + 2 and current < logical,
             "LMem free chunk is out of range")
        seen.add(current)
        stored_size = u16(block, current - 2)
        size = round4(stored_size)
        need(stored_size >= 4 and current - 2 + size <= logical,
             "invalid LMem free chunk size")
        free_ranges.append((current - 2, current - 2 + size))
        free_sum += size
        nxt = u16(block, current)
        need(nxt == 0 or nxt > current, "LMem free list is not sorted")
        current = nxt
    need(free_sum == total_free, "LMem total-free field mismatch")

    heap_start = handle_off + 2 * nhandles
    ranges = sorted(live_ranges + free_ranges)
    cursor = heap_start
    for start, end in ranges:
        need(start == cursor, "LMem heap contains a gap or overlapping chunks")
        cursor = end
    need(cursor == logical, "LMem heap does not cover its logical block")
    return LMemInfo(logical, handle_off, handles, free_ranges, live_ranges)


@dataclass
class Command:
    opcode: int
    raw: bytes
    fields: dict[str, Any] = field(default_factory=dict)


def parse_huge_array(vm: VMFile, directory_handle: int) -> list[bytes]:
    rec = vm.records[directory_handle]
    need(rec.uid_or_size_low == 0xFF03,
         "GString handle is not a HugeArray directory")
    block = vm.block(directory_handle)
    info = parse_lmem(block, 2)
    need(info.handle_offset >= 28, "HugeArray directory header is truncated")
    first_data = u16(block, 16)
    dir_chunk_handle = u16(block, 18)
    xdir = u16(block, 20)
    self_handle = u16(block, 22)
    element_size = u16(block, 24)
    need(block[0:2] == block[16:18], "directory VM-chain link mismatch")
    need(dir_chunk_handle == info.handle_offset and info.handles[1] == 0,
         "directory chunk handle mismatch")
    need(xdir == 0, "extended HugeArray directories are unsupported")
    need(self_handle == directory_handle, "HugeArray self handle mismatch")
    need(element_size == 0, "GString HugeArray is not variable-sized")
    chunk = info.handles[0]
    count, elem_size, cur_off, data_off = struct.unpack_from("<4H", block, chunk)
    need(elem_size == 8 and cur_off == 0 and data_off == 8,
         "invalid HugeArray directory ChunkArray header")
    chunk_size = u16(block, chunk - 2) - 2
    need(8 + count * 8 == chunk_size, "HugeArray directory chunk size mismatch")
    entries = [struct.unpack_from("<IHH", block, chunk + 8 + i * 8)
               for i in range(count)]
    need(entries and entries[0] == (0xFFFFFFFF, 0, 0),
         "HugeArray directory lacks its sentinel entry")
    need((entries[1][2] if len(entries) > 1 else 0) == first_data,
         "HugeArray first-data handle mismatch")

    result: list[bytes] = []
    expected_first = 0
    previous_handle = 0
    for index, (last, logical_size, handle) in enumerate(entries[1:], 1):
        need(last >= expected_first, "HugeArray directory indices do not ascend")
        num_elements = last - expected_first + 1
        drec = vm.records.get(handle)
        need(drec is not None and drec.used and drec.uid_or_size_low == 0xFF04,
             "HugeArray directory points to a non-data block")
        data = vm.block(handle)
        dinfo = parse_lmem(data, 2)
        next_handle, prev_handle, parent = struct.unpack_from("<3H", data, 16)
        need(data[0:2] == data[16:18], "data-block VM-chain link mismatch")
        need(prev_handle == previous_handle and parent == directory_handle,
             "broken HugeArray data-block back link")
        expected_next = entries[index + 1][2] if index + 1 < len(entries) else 0
        need(next_handle == expected_next, "broken HugeArray data-block forward link")
        need(dinfo.handle_offset == 24 and dinfo.handles[1] == 0,
             "invalid HugeArray data handle table")
        ptr = dinfo.handles[0]
        count2, elem_size2, cur2, offset2 = struct.unpack_from("<4H", data, ptr)
        need(count2 == num_elements and elem_size2 == 0 and cur2 == 0 and offset2 == 8,
             "invalid variable ChunkArray header")
        offsets = [u16(data, ptr + 8 + i * 2) for i in range(count2)]
        chunk_payload_size = u16(data, ptr - 2) - 2
        need(offsets == sorted(offsets), "GString element offsets do not ascend")
        need(not offsets or offsets[0] == 8 + count2 * 2,
             "first GString element offset is invalid")
        for i, start_rel in enumerate(offsets):
            end_rel = offsets[i + 1] if i + 1 < len(offsets) else chunk_payload_size
            need(start_rel < end_rel <= chunk_payload_size,
                 "GString element range is invalid")
            result.append(data[ptr + start_rel:ptr + end_rel])
        used_bytes = dinfo.logical_size - sum(e - s for s, e in dinfo.free_ranges)
        need(logical_size == used_bytes, "HugeArray directory block-size field mismatch")
        expected_first = last + 1
        previous_handle = handle
    need(len(result) == expected_first, "HugeArray element total mismatch")
    return result


FIXED_ELEMENT_SIZES = {
    0x00: 1, 0x03: 9, 0x11: 9, 0x12: 9, 0x13: 29, 0x14: 9,
    0x18: 1, 0x19: 1, 0x1A: 1, 0x20: 9, 0x2C: 9, 0x32: 17,
    0x33: 13, 0x35: 9, 0x41: 1, 0x42: 9, 0x48: 9, 0x49: 2,
    0x60: 1, 0x61: 1, 0x62: 2, 0x63: 5, 0x69: 4, 0x6A: 2,
    0x6B: 2, 0x6C: 5, 0x6D: 2, 0x6E: 2, 0x6F: 14, 0x70: 5,
    0x75: 4, 0x76: 2, 0x77: 2, 0x78: 7, 0x7B: 3, 0x7E: 2, 0x81: 3,
    0x82: 4, 0xA0: 5, 0xA1: 1, 0xA2: 11, 0xA6: 4,
}


def parse_command(raw: bytes) -> Command:
    need(raw, "zero-length GString element")
    op = raw[0]
    cmd = Command(op, raw)
    if op in FIXED_ELEMENT_SIZES:
        need(len(raw) == FIXED_ELEMENT_SIZES[op],
             f"wrong size for GString opcode {op:#04x}")
    elif op == 0x0E:  # escape: opcode, escape code, payload size, payload
        need(len(raw) >= 5 and len(raw) == 5 + u16(raw, 3),
             "invalid GR_ESCAPE element")
        cmd.fields.update(code=u16(raw, 1), payload=raw[5:])
    elif op == 0x27:  # polyline
        need(len(raw) >= 3 and len(raw) == 3 + 4 * u16(raw, 1),
             "invalid GR_DRAW_POLYLINE element")
    elif op == 0x3E:  # GDF_saved, then TFStyleRun/TextAttr/text tuples
        need(len(raw) >= 15, "truncated GR_DRAW_TEXT_FIELD element")
        total_chars = u16(raw, 1)
        pos = 15  # opcode plus the 14-byte GDF_saved structure
        runs = []
        chars_seen = 0
        while chars_seen < total_chars:
            need(pos + 26 <= len(raw), "truncated text-field style run")
            run_chars = u16(raw, pos)
            need(0 < run_chars <= total_chars - chars_seen,
                 "invalid text-field style-run character count")
            attr = raw[pos + 2:pos + 26]  # complete 24-byte TextAttr
            pos += 26
            need(pos + run_chars <= len(raw), "truncated text-field string")
            runs.append((run_chars, attr, raw[pos:pos + run_chars]))
            pos += run_chars
            chars_seen += run_chars
        need(pos == len(raw), "unused bytes after text-field runs")
        cmd.fields.update(font_dependent=True, text_runs=runs)
    elif op == 0x47:  # fill polygon: count, rule, points
        need(len(raw) >= 4 and len(raw) == 4 + 4 * u16(raw, 1),
             "invalid GR_FILL_POLYGON element")
        need(raw[3] in (0, 1), "invalid polygon fill rule")
    elif op in (0x4C, 0x50):
        need(len(raw) >= 27 and len(raw) == 7 + u16(raw, 5),
             "invalid positioned bitmap GString element")
        cmd.fields.update(x=s16(raw, 1), y=s16(raw, 3), bitmap=raw[7:])
    elif op in (0x4D, 0x51, 0x54):
        need(len(raw) >= 23 and len(raw) == 3 + u16(raw, 1),
             "invalid current-position bitmap GString element")
        cmd.fields["bitmap"] = raw[3:]
    else:
        raise FormatError(f"unsupported GString opcode {op:#04x}")
    return cmd


def parse_legacy_gstring(vm: VMFile, first_handle: int) -> list[Command]:
    need(vm.header_fields["protocol"] == (0, 0),
         "non-HugeArray GString requires legacy protocol 0.0")
    slices: list[bytes] = []
    seen: set[int] = set()
    handle = first_handle
    first = True
    while handle:
        need(handle not in seen, "cyclic legacy GString VM chain")
        seen.add(handle)
        rec = vm.records.get(handle)
        need(rec is not None and rec.used and rec.uid_or_size_low == 0,
             "legacy GString chain points to an invalid block")
        data = vm.block(handle)
        need(len(data) >= 4, "truncated legacy GString block")
        nxt, used_end = struct.unpack_from("<2H", data, 0)
        need(4 <= used_end <= len(data), "bad legacy GString used-byte marker")
        payload = data[4:used_end]
        if first:
            need(payload and payload[0] == 0x1A,
                 "legacy stream does not begin with GR_DRAW_BITMAP_CP")
            payload = payload[1:]
            first = False
        need(len(payload) >= 2, "truncated legacy bitmap slice")
        slice_size = u16(payload, 0)
        need(2 + slice_size <= len(payload), "truncated legacy bitmap data")
        slices.append(payload[2:2 + slice_size])
        tail = payload[2 + slice_size:]
        if tail:
            need(tail == b"\0", "unexpected data after legacy bitmap slice")
            need(nxt in (0, 0x00FF), "legacy GString end has an invalid next link")
            handle = 0
        else:
            need(nxt in vm.records, "legacy GString next handle is invalid")
            handle = nxt
    need(slices, "empty legacy GString")
    return [Command(0x51, b"", {"bitmap_slices": slices, "legacy": True}),
            Command(0x00, b"\0")]


class Background:
    def __init__(self, data: bytes):
        self.vm = VMFile(data)
        map_rec = self.vm.records[self.vm.map_handle]
        need(map_rec.uid_or_size_low == 0 and not (map_rec.flags_or_prev_low & 1),
             "background map block has unexpected VM metadata")
        block = self.vm.block(self.vm.map_handle)
        need(len(block) >= 12, "truncated Field background map block")
        self.width = u16(block, 0)
        self.height = u16(block, 2)
        self.x_offset = s16(block, 4)
        self.y_offset = s16(block, 6)
        bg_type = u16(block, 8)
        self.gstring_handle = u16(block, 10)
        need(self.width and self.height, "background dimensions must be nonzero")
        need(bg_type == 0, "unsupported Field background storage type")
        # Bytes after the 12-byte payload are VM allocation slack, not fields.
        grec = self.vm.records.get(self.gstring_handle)
        need(grec is not None and grec.used, "map block points to an invalid GString")
        if grec.uid_or_size_low == 0xFF03:
            elements = parse_huge_array(self.vm, self.gstring_handle)
            self.commands = [parse_command(element) for element in elements]
        else:
            self.commands = parse_legacy_gstring(self.vm, self.gstring_handle)
        need(self.commands and self.commands[-1].opcode == 0,
             "GString is not terminated")
        need(all(c.opcode != 0 for c in self.commands[:-1]),
             "GString contains data after its end marker")
        referenced = {32, self.vm.map_handle, self.gstring_handle}
        if grec.uid_or_size_low == 0xFF03:
            referenced.update(r.handle for r in self.vm.records.values()
                              if r.used and r.uid_or_size_low == 0xFF04)
        else:
            referenced.update(r.handle for r in self.vm.records.values()
                              if r.used and r.uid_or_size_low == 0)
        used = {r.handle for r in self.vm.records.values() if r.used}
        need(referenced == used, "VM file contains unreferenced used blocks")


def default_palette() -> list[tuple[int, int, int]]:
    p = [
        (0x00, 0x00, 0x00), (0x00, 0x00, 0xAA),
        (0x00, 0xAA, 0x00), (0x00, 0xAA, 0xAA),
        (0xAA, 0x00, 0x00), (0xAA, 0x00, 0xAA),
        (0xAA, 0x55, 0x00), (0xAA, 0xAA, 0xAA),
        (0x55, 0x55, 0x55), (0x55, 0x55, 0xFF),
        (0x55, 0xFF, 0x55), (0x55, 0xFF, 0xFF),
        (0xFF, 0x55, 0x55), (0xFF, 0x55, 0xFF),
        (0xFF, 0xFF, 0x55), (0xFF, 0xFF, 0xFF),
    ]
    p.extend((v, v, v) for v in range(0, 256, 17))
    p.extend([(0, 0, 0)] * 8)
    levels = (0, 0x33, 0x66, 0x99, 0xCC, 0xFF)
    p.extend((r, g, b) for r in levels for g in levels for b in levels)
    need(len(p) == 256, "internal palette construction error")
    return p


@dataclass
class BitmapSlice:
    width: int
    height: int
    compact: int
    bm_type: int
    start: int
    scans: int
    dev_info: int
    x_res: int
    y_res: int
    palette: list[tuple[int, int, int]] | None
    rows: list[tuple[bytes | None, bytes]]


def decode_packbits_rows(data: bytes, row_size: int, rows: int) -> list[bytes]:
    pos = 0
    result: list[bytes] = []
    for _ in range(rows):
        out = bytearray()
        while len(out) < row_size:
            need(pos < len(data), "truncated PackBits scan line")
            control = struct.unpack_from("<b", data, pos)[0]
            pos += 1
            if control >= 0:
                count = control + 1
                need(pos + count <= len(data), "truncated PackBits literal run")
                out.extend(data[pos:pos + count])
                pos += count
            else:
                count = 1 - control
                need(pos < len(data), "truncated PackBits repeat run")
                out.extend(data[pos:pos + 1] * count)
                pos += 1
            need(len(out) <= row_size, "PackBits run crosses a scan-line boundary")
        result.append(bytes(out))
    need(pos == len(data), "unused bytes after PackBits scan data")
    return result


def parse_cbitmap(data: bytes, legacy: bool = False) -> BitmapSlice:
    need(len(data) >= 20, "truncated CBitmap")
    width, height, compact, bm_type, start, scans, dev, data_off, pal_off, xr, yr = \
        struct.unpack_from("<HHBB7H", data, 0)
    need(width and height and start + scans <= height, "invalid CBitmap dimensions")
    need(xr and yr, "CBitmap resolution must be nonzero")
    need(bm_type & 0x08, "serialized background bitmap is not complex")
    need(compact in (0, 1), "unsupported bitmap compaction method")
    fmt = bm_type & 7
    need(fmt in (0, 1, 2), "unsupported bitmap pixel format")
    need(data_off >= 20 and data_off <= len(data), "CBitmap data offset is invalid")

    palette = None
    accounted = [(0, 20), (data_off, len(data))]
    if legacy and pal_off:
        need(not (bm_type & 0x40), "legacy CBitmap has conflicting palette flag")
        need(pal_off == 20 and data_off == 68, "invalid legacy 16-color palette")
        palette = [tuple(data[pal_off + 3 * i:pal_off + 3 * i + 3])
                   for i in range(16)]
        accounted.append((pal_off, data_off))
    elif bm_type & 0x40:
        need(20 <= pal_off <= len(data) - 2, "CBitmap palette offset is invalid")
        count = u16(data, pal_off)
        need(count in (2, 16, 256), "unsupported CBitmap palette size")
        pal_end = pal_off + 2 + count * 3
        need(pal_end <= len(data), "truncated CBitmap palette")
        palette = [tuple(data[pal_off + 2 + 3 * i:pal_off + 5 + 3 * i])
                   for i in range(count)]
        accounted.append((pal_off, pal_end))
    # Without BMT_PALETTE, CB_palette is an inactive runtime scratch field;
    # old writers did not consistently clear it.

    # Any bytes between defined substructures are alignment bytes and must be zero.
    merged: list[tuple[int, int]] = []
    for start_i, end_i in sorted(accounted):
        need(not merged or start_i >= merged[-1][1], "overlapping CBitmap substructures")
        if merged and start_i == merged[-1][1]:
            merged[-1] = (merged[-1][0], end_i)
        else:
            merged.append((start_i, end_i))
    cursor = 0
    for start_i, end_i in merged:
        need(not any(data[cursor:start_i]), "nonzero CBitmap alignment bytes")
        cursor = end_i
    need(cursor == len(data), "unaccounted CBitmap bytes")

    pixel_bytes = (width + 7) // 8 if fmt == 0 else ((width + 1) // 2 if fmt == 1 else width)
    mask_bytes = (width + 7) // 8 if bm_type & 0x10 else 0
    row_size = pixel_bytes + mask_bytes
    packed = data[data_off:]
    decoded = (decode_packbits_rows(packed, row_size, scans) if compact == 1
               else [packed[i * row_size:(i + 1) * row_size] for i in range(scans)])
    if compact == 0:
        need(len(packed) == scans * row_size, "raw CBitmap scan-data size mismatch")
    rows_out = [(row[:mask_bytes] if mask_bytes else None, row[mask_bytes:])
                for row in decoded]
    return BitmapSlice(width, height, compact, bm_type, start, scans, dev, xr, yr,
                       palette, rows_out)


def assemble_bitmap(parts: list[bytes], fill_color: tuple[int, int, int] | None,
                    legacy: bool = False) -> Image.Image:
    slices = [parse_cbitmap(part, legacy) for part in parts]
    base = slices[0]
    palette = next((s.palette for s in slices if s.palette is not None), None)
    if palette is None:
        palette = default_palette()
    covered = [False] * base.height
    out = Image.new("RGBA", (base.width, base.height), (0, 0, 0, 0))
    pixels = out.load()
    base_shape = base.bm_type & (0x10 | 7)
    for slc in slices:
        need((slc.width, slc.height) == (base.width, base.height),
             "bitmap slices disagree on dimensions")
        need((slc.x_res, slc.y_res) == (base.x_res, base.y_res),
             "bitmap slices disagree on resolution")
        need((slc.bm_type & (0x10 | 7)) == base_shape,
             "bitmap slices disagree on format or mask")
        for row_index, (mask, pixel_data) in enumerate(slc.rows):
            y = slc.start + row_index
            need(not covered[y], "overlapping bitmap slices")
            covered[y] = True
            fmt = slc.bm_type & 7
            for x in range(slc.width):
                opaque = True
                if mask is not None:
                    opaque = bool(mask[x // 8] & (0x80 >> (x & 7)))
                if fmt == 0:
                    bit = bool(pixel_data[x // 8] & (0x80 >> (x & 7)))
                    if fill_color is not None:
                        opaque = opaque and bit
                        color = fill_color
                    else:
                        opaque = opaque and bit
                        color = (0, 0, 0)
                elif fmt == 1:
                    value = ((pixel_data[x // 2] >> 4) if not (x & 1)
                             else pixel_data[x // 2] & 15)
                    need(value < len(palette), "4-bit pixel exceeds palette")
                    color = palette[value]
                else:
                    value = pixel_data[x]
                    need(value < len(palette), "8-bit pixel exceeds palette")
                    color = palette[value]
                pixels[x, y] = (*color, 255 if opaque else 0)
    need(all(covered), "bitmap slice sequence does not cover every scan line")
    return out


@dataclass
class GraphicsState:
    matrix: tuple[float, float, float, float, float, float] = (1, 0, 0, 1, 0, 0)
    default_matrix: tuple[float, float, float, float, float, float] = (1, 0, 0, 1, 0, 0)
    current: tuple[float, float] = (0, 0)
    line_color: tuple[int, int, int] = (0, 0, 0)
    area_color: tuple[int, int, int] = (0, 0, 0)
    line_width: float = 1.0
    line_mask: int = 25
    area_mask: int = 25
    mix_mode: int = 1
    path: list[list[tuple[float, float]]] | None = None
    clip: Image.Image | None = None


def multiply(n: tuple[float, ...], c: tuple[float, ...]) -> tuple[float, ...]:
    na, nb, nc, nd, ne, nf = n
    ca, cb, cc, cd, ce, cf = c
    return (na * ca + nb * cc, na * cb + nb * cd,
            nc * ca + nd * cc, nc * cb + nd * cd,
            ne * ca + nf * cc + ce, ne * cb + nf * cd + cf)


class Renderer:
    def __init__(self, bg: Background):
        self.bg = bg
        self.canvas = Image.new("RGBA", (bg.width, bg.height), (0, 0, 0, 0))
        self.state = GraphicsState()
        self.stack: list[GraphicsState] = []
        self.transform_stack: list[tuple[float, ...]] = []

    def point(self, p: tuple[float, float]) -> tuple[float, float]:
        x, y = p
        a, b, c, d, e, f = self.state.matrix
        return (x * a + y * c + e - self.bg.x_offset,
                x * b + y * d + f - self.bg.y_offset)

    def points(self, raw: bytes, offset: int, count: int) -> list[tuple[float, float]]:
        return [self.point((s16(raw, offset + 4 * i), s16(raw, offset + 4 * i + 2)))
                for i in range(count)]

    def _composite_layer(self, layer: Image.Image) -> None:
        if self.state.clip is not None:
            alpha = ImageChops.multiply(layer.getchannel("A"), self.state.clip)
            layer.putalpha(alpha)
        if self.state.mix_mode == 1:
            self.canvas.alpha_composite(layer)
        elif self.state.mix_mode == 5:  # MM_XOR, exact on RGBA byte channels
            self.canvas = ImageChops.logical_xor(self.canvas.convert("1"), layer.convert("1")).convert("RGBA")
        else:
            raise FormatError(f"unsupported GEOS mix mode {self.state.mix_mode}")

    def _shape(self, kind: str, points: list[tuple[float, float]], fill: bool) -> None:
        if self.state.path is not None:
            self.state.path.append(points)
            return
        mask = self.state.area_mask if fill else self.state.line_mask
        base = mask & 0x7F
        enabled = (base == 25) ^ bool(mask & 0x80)
        need(base in (25, 89), "unsupported dithered system draw mask")
        if not enabled:
            return
        layer = Image.new("RGBA", self.canvas.size, (0, 0, 0, 0))
        draw = ImageDraw.Draw(layer)
        color = (*self.state.area_color, 255) if fill else (*self.state.line_color, 255)
        width = max(1, round(self.state.line_width))
        if kind == "polygon":
            if fill:
                draw.polygon(points, fill=color)
            else:
                draw.line(points + [points[0]], fill=color, width=width, joint="curve")
        elif kind == "polyline":
            draw.line(points, fill=color, width=width, joint="curve")
        self._composite_layer(layer)

    def _rect_points(self, raw: bytes) -> list[tuple[float, float]]:
        l, t, r, b = struct.unpack_from("<4h", raw, 1)
        return [self.point((l, t)), self.point((r, t)),
                self.point((r, b)), self.point((l, b))]

    def _ellipse(self, raw: bytes, fill: bool) -> None:
        l, t, r, b = struct.unpack_from("<4h", raw, 1)
        pts = []
        for i in range(96):
            angle = 2 * math.pi * i / 96
            p = ((l + r) / 2 + (r - l) / 2 * math.cos(angle),
                 (t + b) / 2 + (b - t) / 2 * math.sin(angle))
            pts.append(self.point(p))
        self._shape("polygon", pts, fill)

    def _curve(self, coords: list[tuple[float, float]]) -> None:
        p0, p1, p2, p3 = coords
        pts = []
        for i in range(65):
            t = i / 64
            q = ((1-t)**3*p0[0] + 3*(1-t)**2*t*p1[0] + 3*(1-t)*t*t*p2[0] + t**3*p3[0],
                 (1-t)**3*p0[1] + 3*(1-t)**2*t*p1[1] + 3*(1-t)*t*t*p2[1] + t**3*p3[1])
            pts.append(self.point(q))
        self._shape("polyline", pts, False)
        self.state.current = p3

    def _bitmap(self, image: Image.Image, x: float, y: float,
                x_res: int, y_res: int) -> None:
        a, b, c, d, e, f = self.state.matrix
        sx, sy = 72.0 / x_res, 72.0 / y_res
        forward = (sx * a, sx * b, sy * c, sy * d,
                   x * a + y * c + e - self.bg.x_offset,
                   x * b + y * d + f - self.bg.y_offset)
        det = forward[0] * forward[3] - forward[1] * forward[2]
        need(abs(det) > 1e-12, "singular transform for bitmap")
        ia = forward[3] / det
        ib = -forward[2] / det
        ic = (forward[2] * forward[5] - forward[3] * forward[4]) / det
        id_ = -forward[1] / det
        ie = forward[0] / det
        iff = (forward[1] * forward[4] - forward[0] * forward[5]) / det
        layer = image.transform(self.canvas.size, Image.Transform.AFFINE,
                                (ia, ib, ic, id_, ie, iff),
                                resample=Image.Resampling.NEAREST)
        self._composite_layer(layer)

    def render(self) -> Image.Image:
        commands = self.bg.commands
        if any(c.fields.get("font_dependent") for c in commands):
            raise FormatError("GString uses external GEOS fonts (GR_DRAW_TEXT_FIELD)")
        index = 0
        while index < len(commands):
            c = commands[index]
            op, raw = c.opcode, c.raw
            if op == 0:
                break
            if op == 0x03:  # declared bounds, informational during playback
                pass
            elif op == 0x0E:
                # GrEscape only records data when the destination is another
                # GString; normal playback to a GState intentionally does nil.
                pass
            elif op in (0x11, 0x12, 0x13, 0x14):
                if op == 0x11:
                    n = (fixed_16_16(raw, 1), 0, 0, fixed_16_16(raw, 5), 0, 0)
                elif op == 0x12:
                    n = (1, 0, 0, 1, fixed_16_16(raw, 1), fixed_16_16(raw, 5))
                elif op == 0x14:
                    n = (1, 0, 0, 1, s32(raw, 1), s32(raw, 5))
                else:
                    n = (fixed_16_16(raw, 1), fixed_16_16(raw, 5),
                         fixed_16_16(raw, 9), fixed_16_16(raw, 13),
                         fixed_32_16(raw, 17), fixed_32_16(raw, 23))
                self.state.matrix = multiply(n, self.state.matrix)
            elif op == 0x18:
                self.state.default_matrix = self.state.matrix
            elif op == 0x19:
                self.transform_stack.append(self.state.matrix)
            elif op == 0x1A:
                need(self.transform_stack, "transform stack underflow")
                self.state.matrix = self.transform_stack.pop()
            elif op == 0x20:
                pts = self.points(raw, 1, 2)
                self._shape("polyline", pts, False)
                self.state.current = (s16(raw, 5), s16(raw, 7))
            elif op == 0x27:
                count = u16(raw, 1)
                self._shape("polyline", self.points(raw, 3, count), False)
                self.state.current = (s16(raw, len(raw)-4), s16(raw, len(raw)-2))
            elif op == 0x2C:
                self._shape("polygon", self._rect_points(raw), False)
            elif op == 0x32:
                vals = struct.unpack_from("<8h", raw, 1)
                self._curve([(vals[i], vals[i+1]) for i in range(0, 8, 2)])
            elif op == 0x33:
                vals = struct.unpack_from("<6h", raw, 1)
                self._curve([self.state.current] +
                            [(vals[i], vals[i+1]) for i in range(0, 6, 2)])
            elif op == 0x35:
                self._ellipse(raw, False)
            elif op == 0x3E:
                raise FormatError("GString uses external GEOS fonts (GR_DRAW_TEXT_FIELD)")
            elif op == 0x41:
                need(self.state.path is not None, "GR_DRAW_PATH without a path")
                path = self.state.path
                self.state.path = None
                for points in path:
                    self._shape("polyline", points, False)
                self.state.path = path
            elif op == 0x42:
                self._shape("polygon", self._rect_points(raw), True)
            elif op == 0x47:
                self._shape("polygon", self.points(raw, 4, u16(raw, 1)), True)
            elif op == 0x48:
                self._ellipse(raw, True)
            elif op == 0x49:
                need(self.state.path is not None, "GR_FILL_PATH without a path")
                path = self.state.path
                self.state.path = None
                for points in path:
                    self._shape("polygon", points, True)
                self.state.path = path
            elif op in (0x4C, 0x4D, 0x50, 0x51):
                parts = (c.fields["bitmap_slices"] if "bitmap_slices" in c.fields
                         else [c.fields["bitmap"]])
                while index + 1 < len(commands) and commands[index + 1].opcode == 0x54:
                    index += 1
                    parts.append(commands[index].fields["bitmap"])
                fill = self.state.area_color if op in (0x4C, 0x4D) else None
                bitmap_header = parse_cbitmap(parts[0], bool(c.fields.get("legacy")))
                image = assemble_bitmap(parts, fill, bool(c.fields.get("legacy")))
                x, y = ((c.fields["x"], c.fields["y"]) if op in (0x4C, 0x50)
                        else self.state.current)
                self._bitmap(image, x, y, bitmap_header.x_res, bitmap_header.y_res)
                self.state.current = (x, y)
            elif op == 0x54:
                raise FormatError("orphan bitmap slice")
            elif op == 0x60:
                self.stack.append(copy.copy(self.state))
                self.state.path = copy.deepcopy(self.state.path)
                self.state.clip = self.state.clip.copy() if self.state.clip else None
            elif op == 0x61:
                need(self.stack, "graphics-state stack underflow")
                self.state = self.stack.pop()
            elif op == 0x62:
                self.state.mix_mode = raw[1]
                need(raw[1] in (1,), "unsupported non-copy GString mix mode")
            elif op == 0x63:
                self.state.current = (s16(raw, 1), s16(raw, 3))
            elif op == 0x69:
                self.state.line_color = tuple(raw[1:4])
            elif op == 0x6A:
                self.state.line_mask = raw[1]
                need(raw[1] & 0x7F in (25, 89), "unsupported dithered line draw mask")
            elif op == 0x6B:
                need(raw[1] in (0, 1), "invalid line color-map mode")
            elif op == 0x6C:
                self.state.line_width = fixed_16_16(raw, 1)
                need(self.state.line_width >= 0, "negative line width")
            elif op in (0x6D, 0x6E):
                need(raw[1] in (0, 1, 2), "invalid line join/end value")
            elif op == 0x6F:
                need(raw[1] in (0, 0x80), "invalid line ColorFlag")
                self.state.line_color = tuple(raw[2:5]) if raw[1] == 0x80 else default_palette()[raw[2]]
                self.state.line_mask = raw[5]
                need(raw[5] & 0x7F in (25, 89) and raw[6] in (0, 1),
                     "unsupported line attributes")
                self.state.line_width = fixed_16_16(raw, 10)
            elif op == 0x70:
                need(fixed_16_16(raw, 1) >= 0, "negative miter limit")
            elif op == 0x75:
                self.state.area_color = tuple(raw[1:4])
            elif op == 0x76:
                self.state.area_mask = raw[1]
                need(raw[1] & 0x7F in (25, 89), "unsupported dithered area draw mask")
            elif op == 0x77:
                need(raw[1] in (0, 1), "invalid area color-map mode")
            elif op == 0x78:
                need(raw[1] in (0, 0x80), "invalid area ColorFlag")
                self.state.area_color = tuple(raw[2:5]) if raw[1] == 0x80 else default_palette()[raw[2]]
                self.state.area_mask = raw[5]
                need(raw[5] & 0x7F in (25, 89) and raw[6] in (0, 1),
                     "unsupported area attributes")
            elif op == 0x7B:
                need(raw[1] == 0, "unsupported non-solid area pattern")
            elif op in (0x7E, 0x81, 0x82):
                # Text mode/space-pad state is structurally consumed; it has no
                # visual effect unless a later font-dependent text opcode occurs.
                pass
            elif op == 0xA0:
                need(self.state.path is None and u16(raw, 1) in (0, 1, 2, 3),
                     "invalid GR_BEGIN_PATH")
                self.state.path = []
            elif op == 0xA1:
                need(self.state.path is not None, "GR_END_PATH without a path")
            elif op == 0xA2:
                combine = u16(raw, 1)
                need(combine in (0, 1, 2, 3), "invalid clip-rectangle combine mode")
                mask = Image.new("L", self.canvas.size, 0)
                ImageDraw.Draw(mask).polygon(self._rect_points(raw[2:]), fill=255)
                self._set_clip(mask, combine)
            elif op == 0xA6:
                need(self.state.path is not None and raw[1] in (0, 1)
                     and u16(raw, 2) in (0, 1, 2, 3), "invalid window clip path")
                mask = Image.new("L", self.canvas.size, 0)
                md = ImageDraw.Draw(mask)
                for points in self.state.path:
                    md.polygon(points, fill=255)
                self._set_clip(mask, u16(raw, 2))
                self.state.path = None
            else:  # guarded by parse_command
                raise FormatError(f"unimplemented GString opcode {op:#04x}")
            index += 1
        need(not self.stack and not self.transform_stack, "unbalanced GString state stack")
        return self.canvas

    def _set_clip(self, mask: Image.Image, combine: int) -> None:
        if combine == 0:
            self.state.clip = Image.new("L", self.canvas.size, 0)
        elif combine == 1 or self.state.clip is None:
            self.state.clip = mask
        elif combine == 2:
            self.state.clip = ImageChops.lighter(self.state.clip, mask)
        else:
            self.state.clip = ImageChops.multiply(self.state.clip, mask)


def convert(input_path: Path, output_path: Path) -> None:
    data = input_path.read_bytes()
    bg = Background(data)
    image = Renderer(bg).render()
    output_parent = output_path.parent
    need(output_parent.is_dir(), "output directory does not exist")
    temp_name = None
    try:
        with tempfile.NamedTemporaryFile(prefix=f".{output_path.name}.", suffix=".tmp",
                                         dir=output_parent, delete=False) as temp:
            temp_name = temp.name
        image.save(temp_name, format="PNG", optimize=True)
        os.chmod(temp_name, 0o664)
        os.replace(temp_name, output_path)
        temp_name = None
    finally:
        if temp_name is not None:
            try:
                os.unlink(temp_name)
            except FileNotFoundError:
                pass


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(f"usage: {Path(argv[0]).name} <inputFile> <outputFile>", file=sys.stderr)
        return 2
    input_path = Path(argv[1])
    output_path = Path(argv[2])
    try:
        convert(input_path, output_path)
    except (FormatError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

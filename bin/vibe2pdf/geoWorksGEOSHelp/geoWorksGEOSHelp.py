#!/usr/bin/env python3
# Vibe coded by Codex
"""Convert a PC/GEOS 2.x Help VM database to a PDF document."""

from __future__ import annotations

import io
import copy
import bisect
import datetime
import math
import os
import struct
import sys
import tempfile
import zlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

try:
    from PIL import Image, ImageChops, ImageDraw, ImageFont
except ImportError:  # The parser can still report a format error without Pillow.
    Image = ImageChops = ImageDraw = ImageFont = None  # type: ignore[assignment]


class FormatError(Exception):
    """The input is not a supported, structurally valid GEOS Help file."""


def need(condition: bool, message: str) -> None:
    if not condition:
        raise FormatError(message)


def u16(data: bytes, offset: int = 0) -> int:
    need(0 <= offset <= len(data) - 2, "truncated 16-bit field")
    return struct.unpack_from("<H", data, offset)[0]


def s16(data: bytes, offset: int = 0) -> int:
    need(0 <= offset <= len(data) - 2, "truncated signed 16-bit field")
    return struct.unpack_from("<h", data, offset)[0]


def u32(data: bytes, offset: int = 0) -> int:
    need(0 <= offset <= len(data) - 4, "truncated 32-bit field")
    return struct.unpack_from("<I", data, offset)[0]


def s32(data: bytes, offset: int = 0) -> int:
    need(0 <= offset <= len(data) - 4, "truncated signed 32-bit field")
    return struct.unpack_from("<i", data, offset)[0]


def word_and_a_half(data: bytes, offset: int = 0) -> int:
    need(0 <= offset <= len(data) - 3, "truncated 24-bit field")
    return data[offset] | (data[offset + 1] << 8) | (data[offset + 2] << 16)


def round4(value: int) -> int:
    return (value + 3) & ~3


def color_quad(data: bytes, offset: int) -> tuple[int, int, int]:
    """Convert a GEOS ColorQuad to RGB, rejecting unsupported color modes."""
    need(offset + 4 <= len(data), "truncated ColorQuad")
    first, mode, green, blue = data[offset:offset + 4]
    if mode == 0:  # CF_INDEX -- the PC/GEOS 256-color palette
        return GEOS_PALETTE[first]
    if mode == 1:  # CF_GRAY
        return (first, first, first)
    if mode == 3:  # CF_CMY
        return (255 - first, 255 - green, 255 - blue)
    if mode == 0x80:  # CF_RGB
        return (first, green, blue)
    raise FormatError(f"unsupported GEOS ColorFlag {mode:#04x}")


def make_geos_palette() -> tuple[tuple[int, int, int], ...]:
    palette = [
        (0x00, 0x00, 0x00), (0x00, 0x00, 0xAA),
        (0x00, 0xAA, 0x00), (0x00, 0xAA, 0xAA),
        (0xAA, 0x00, 0x00), (0xAA, 0x00, 0xAA),
        (0xAA, 0x55, 0x00), (0xAA, 0xAA, 0xAA),
        (0x55, 0x55, 0x55), (0x55, 0x55, 0xFF),
        (0x55, 0xFF, 0x55), (0x55, 0xFF, 0xFF),
        (0xFF, 0x55, 0x55), (0xFF, 0x55, 0xFF),
        (0xFF, 0xFF, 0x55), (0xFF, 0xFF, 0xFF),
    ]
    palette.extend((value, value, value) for value in range(0, 256, 17))
    palette.extend([(0, 0, 0)] * 8)
    levels = (0, 0x33, 0x66, 0x99, 0xCC, 0xFF)
    palette.extend((red, green, blue)
                   for red in levels for green in levels for blue in levels)
    need(len(palette) == 256, "internal GEOS palette error")
    return tuple(palette)


GEOS_PALETTE = make_geos_palette()


# ---------------------------------------------------------------------------
# PKWARE Data Compression Library (DCL) implode stream decoder


class _Huffman:
    def __init__(self, repetitions: Iterable[int]):
        lengths: list[int] = []
        for packed in repetitions:
            lengths.extend([packed & 15] * ((packed >> 4) + 1))
        self.counts = [0] * 14
        for length in lengths:
            need(length <= 13, "invalid DCL Huffman code length")
            self.counts[length] += 1
        offsets = [0] * 14
        for length in range(1, 13):
            offsets[length + 1] = offsets[length] + self.counts[length]
        self.symbols = [0] * (len(lengths) - self.counts[0])
        for symbol, length in enumerate(lengths):
            if length:
                self.symbols[offsets[length]] = symbol
                offsets[length] += 1


class _BitReader:
    def __init__(self, data: bytes):
        self.data = data
        self.position = 0
        self.buffer = 0
        self.count = 0

    def bits(self, count: int) -> int:
        while self.count < count:
            need(self.position < len(self.data), "truncated DCL bitstream")
            self.buffer |= self.data[self.position] << self.count
            self.position += 1
            self.count += 8
        result = self.buffer & ((1 << count) - 1)
        self.buffer >>= count
        self.count -= count
        return result

    def decode(self, table: _Huffman) -> int:
        code = first = index = 0
        for length in range(1, 14):
            code |= self.bits(1) ^ 1
            count = table.counts[length]
            if code < first + count:
                return table.symbols[index + code - first]
            index += count
            first = (first + count) << 1
            code <<= 1
        raise FormatError("invalid DCL Huffman code")


_DCL_LITERAL = _Huffman([
    11, 124, 8, 7, 28, 7, 188, 13, 76, 4, 10, 8, 12, 10, 12, 10,
    8, 23, 8, 9, 7, 6, 7, 8, 7, 6, 55, 8, 23, 24, 12, 11, 7, 9,
    11, 12, 6, 7, 22, 5, 7, 24, 6, 11, 9, 6, 7, 22, 7, 11, 38, 7,
    9, 8, 25, 11, 8, 11, 9, 12, 8, 12, 5, 38, 5, 38, 5, 11, 7, 5,
    6, 21, 6, 10, 53, 8, 7, 24, 10, 27, 44, 253, 253, 253, 252,
    252, 252, 13, 12, 45, 12, 45, 12, 61, 12, 45, 44, 173,
])
_DCL_LENGTH = _Huffman([2, 35, 36, 53, 38, 23])
_DCL_DISTANCE = _Huffman([2, 20, 53, 230, 247, 151, 248])
_DCL_LENGTH_BASE = (3, 2, 4, 5, 6, 7, 8, 9, 10, 12, 16, 24, 40, 72, 136, 264)
_DCL_LENGTH_EXTRA = (0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8)


def dcl_explode(data: bytes) -> bytes:
    """Decode one complete PKWARE DCL implode stream."""
    bits = _BitReader(data)
    coded_literals = bits.bits(8)
    dictionary_bits = bits.bits(8)
    need(coded_literals in (0, 1), "invalid DCL literal mode")
    need(4 <= dictionary_bits <= 6, "invalid DCL dictionary size")
    output = bytearray()
    while True:
        if bits.bits(1):
            symbol = bits.decode(_DCL_LENGTH)
            length = _DCL_LENGTH_BASE[symbol] + bits.bits(_DCL_LENGTH_EXTRA[symbol])
            if length == 519:
                break
            extra = 2 if length == 2 else dictionary_bits
            distance = (bits.decode(_DCL_DISTANCE) << extra) + bits.bits(extra) + 1
            need(distance <= len(output), "DCL copy points before output start")
            for _ in range(length):
                output.append(output[-distance])
        else:
            output.append(bits.decode(_DCL_LITERAL) if coded_literals else bits.bits(8))
    # The end code may leave high padding bits in its final byte, but there may
    # not be another byte or a non-zero padding bit after it.
    need(bits.position == len(data), "bytes follow DCL end code")
    need(bits.buffer == 0, "non-zero bits follow DCL end code")
    return bytes(output)


# ---------------------------------------------------------------------------
# GEOS VM file and local-memory blocks


@dataclass(frozen=True)
class VMRecord:
    handle: int
    used: bool
    mem_or_next: int
    signature_or_previous: int
    flags: int
    uid: int
    size: int
    position: int


class VMFile:
    GEOS2_MAGIC = b"\xc7E\xc1S"

    def __init__(self, data: bytes):
        self.data = data
        self.records: dict[int, VMRecord] = {}
        self.common: dict[str, object] = {}
        self._parse()

    def _parse(self) -> None:
        data = self.data
        need(len(data) >= 288, "file is too short for a GEOS 2.x VM file")
        need(data[:4] == self.GEOS2_MAGIC, "not a GEOS 2.x file")
        need(u16(data, 0x28) == 2, "GEOS file is not a VM file")
        need(data[0x38:0x3e] == b"hlpf\0\0", "GEOS token is not hlpf")
        need(data[0x3e:0x44] == b"hlpv\0\0", "GEOS creator is not hlpv")
        self.common = {
            "long_name": data[0x04:0x28], "file_type": u16(data, 0x28),
            "flags": u16(data, 0x2a), "release": struct.unpack_from("<4H", data, 0x2c),
            "protocol": struct.unpack_from("<2H", data, 0x34),
            "token": data[0x38:0x3e], "creator": data[0x3e:0x44],
            "user_notes": data[0x44:0xa8], "notice": data[0xa8:0xc8],
            "created_date": u16(data, 0xc8), "created_time": u16(data, 0xca),
            "password": data[0xcc:0xd4], "desktop": data[0xd4:0xe4],
            "reserved": data[0xe4:0x100],
        }

        need(u16(data, 0x100) == 0xadeb, "bad VM file signature")
        header_size = u16(data, 0x102)
        header_relative = u32(data, 0x104)
        self.update_counter = u16(data, 0x108)
        self.update_type = u16(data, 0x10a)
        self.fixed_reserved = data[0x10c:0x118]
        need(header_relative >= 24, "VM header overlaps fixed VM header")
        header_absolute = 0x100 + header_relative
        need(header_absolute + header_size <= len(data), "VM header is outside file")
        header = data[header_absolute:header_absolute + header_size]
        need(len(header) >= 32 and u16(header) == 0x00fb, "bad VM header signature")
        self.header = header

        first_assigned, last_assigned, first_unassigned, last_handle = \
            struct.unpack_from("<4H", header, 2)
        counts = struct.unpack_from("<5h", header, 10)
        self.map_handle = u16(header, 20)
        self.compaction_threshold = s16(header, 22)
        used_size = u32(header, 24)
        self.attributes = header[28]
        self.compression_flags = header[29]
        self.db_map_handle = u16(header, 30)
        need(self.map_handle == 0, "Help VM file unexpectedly has a normal map block")
        need(last_handle >= 32 and (last_handle - 32) % 12 == 0,
             "invalid VM handle-table size")
        need(last_handle <= header_size and header_size - last_handle < 16,
             "VM handle table disagrees with header allocation")

        for handle in range(32, last_handle, 12):
            raw = header[handle:handle + 12]
            need(len(raw) == 12, "truncated VM record")
            if raw[2] >= 0xfe:
                mem, signature, flags, uid, size, position = struct.unpack("<HBBHHI", raw)
                need(size > 0, f"used VM block {handle:#06x} has zero size")
                record = VMRecord(handle, True, mem, signature, flags, uid, size, position)
            else:
                next_handle, previous, size, position = struct.unpack("<HHII", raw)
                record = VMRecord(handle, False, next_handle, previous, 0, 0, size, position)
            self.records[handle] = record

        used = [record for record in self.records.values() if record.used]
        assigned = [record for record in self.records.values()
                    if not record.used and record.size]
        unassigned = [record for record in self.records.values()
                      if not record.used and not record.size]
        need(counts[0] == len(assigned), "VM assigned-free count mismatch")
        need(counts[1] == len(unassigned), "VM unassigned-handle count mismatch")
        need(counts[2] == len(used), "VM used-block count mismatch")
        need(0 <= counts[3] <= counts[2], "invalid cached VM resident count")
        need(used_size == sum(record.size for record in used), "VM used-byte count mismatch")
        self._validate_free_chain(first_assigned, last_assigned, assigned, True)
        self._validate_free_chain(first_unassigned, 0, unassigned, False)

        intervals = sorted((record.position, record.position + record.size, record.handle)
                           for record in used + assigned)
        cursor = 24
        for start, end, handle in intervals:
            need(start == cursor, f"gap or overlap before VM block {handle:#06x}")
            need(end > start and 0x100 + end <= len(data),
                 f"VM block {handle:#06x} is outside file")
            cursor = end
        need(0x100 + cursor == len(data), "unaccounted bytes at end of VM file")

        header_record = self.records.get(32)
        need(header_record is not None and header_record.used,
             "VM header block record is absent")
        need(header_record.uid in (0xadeb, 0x8000), "VM header record has wrong UID")
        need(header_record.position == header_relative and header_record.size == header_size,
             "fixed VM header and header record disagree")
        db_record = self.records.get(self.db_map_handle)
        need(db_record is not None and db_record.used and db_record.uid == 0xff00,
             "VM DB map handle is invalid")

    def _validate_free_chain(self, first: int, last: int,
                             records: list[VMRecord], doubly_linked: bool) -> None:
        expected = {record.handle for record in records}
        seen: list[int] = []
        previous = 0
        current = first
        while current:
            need(current in expected and current not in seen, "broken VM free chain")
            record = self.records[current]
            if doubly_linked:
                need(record.signature_or_previous == previous,
                     "bad previous link in VM assigned-free chain")
            seen.append(current)
            previous, current = current, record.mem_or_next
        need(set(seen) == expected, "not all VM free records are linked")
        if doubly_linked:
            need((seen[-1] if seen else 0) == last, "bad VM last-assigned handle")

    def block(self, handle: int, uid: int | None = None) -> bytes:
        record = self.records.get(handle)
        need(record is not None and record.used, f"VM handle {handle:#06x} is not used")
        if uid is not None:
            need(record.uid == uid, f"VM handle {handle:#06x} has wrong UID")
        start = 0x100 + record.position
        return self.data[start:start + record.size]


@dataclass(frozen=True)
class LMemChunk:
    handle: int
    pointer: int
    payload: bytes
    allocation: tuple[int, int]


@dataclass
class LMemBlock:
    raw: bytes
    header_size: int = 16
    expected_type: int | None = None
    self_handle: int | None = None
    require_vm_flag: bool = True
    logical_size: int = field(init=False)
    handle_offset: int = field(init=False)
    chunks: dict[int, LMemChunk] = field(init=False, default_factory=dict)
    free_ranges: list[tuple[int, int]] = field(init=False, default_factory=list)

    def __post_init__(self) -> None:
        data = self.raw
        need(len(data) >= self.header_size, "truncated LMem block")
        on_disk, handle_offset, flags, block_type, logical_size, handle_count, \
            free_head, total_free = struct.unpack_from("<8H", data)
        if self.require_vm_flag:
            need(flags & 0x0100, "LMem block lacks LMF_IS_VM")
        need(not (flags & 0x0200), "handle-less LMem is unsupported")
        if self.expected_type is not None:
            need(block_type == self.expected_type, "wrong LMem block type")
        if self.self_handle is not None:
            need(on_disk == self.self_handle, "LMem VM-chain/self handle mismatch")
        need(self.header_size <= handle_offset <= logical_size,
             "invalid LMem handle-table offset")
        need(handle_offset + 2 * handle_count <= logical_size <= len(data),
             "invalid LMem logical size")
        self.logical_size = logical_size
        self.handle_offset = handle_offset
        ranges: list[tuple[int, int]] = []
        pointers: set[int] = set()
        for index in range(handle_count):
            handle = handle_offset + index * 2
            pointer = u16(data, handle)
            if pointer in (0, 0xffff):
                continue
            need(pointer not in pointers, "duplicate LMem chunk pointer")
            pointers.add(pointer)
            need(pointer >= handle_offset + 2 * handle_count + 2 and pointer % 2 == 0,
                 "LMem chunk pointer is invalid")
            stored_size = u16(data, pointer - 2)
            need(stored_size >= 2, "invalid LMem chunk size")
            end = pointer - 2 + round4(stored_size)
            need(end <= logical_size, "LMem chunk extends past logical block")
            payload = data[pointer:pointer + stored_size - 2]
            self.chunks[handle] = LMemChunk(handle, pointer, payload, (pointer - 2, end))
            ranges.append((pointer - 2, end))

        free_sum = 0
        current = free_head
        seen: set[int] = set()
        while current:
            need(current not in seen and current % 2 == 0, "bad LMem free list")
            seen.add(current)
            need(current >= handle_offset + 2 * handle_count + 2,
                 "LMem free pointer is before heap")
            stored_size = u16(data, current - 2)
            allocation = round4(stored_size)
            need(stored_size >= 4 and current - 2 + allocation <= logical_size,
                 "bad LMem free chunk size")
            interval = (current - 2, current - 2 + allocation)
            self.free_ranges.append(interval)
            ranges.append(interval)
            free_sum += allocation
            next_free = u16(data, current)
            need(next_free == 0 or next_free > current, "LMem free list is not sorted")
            current = next_free
        need(free_sum == total_free, "LMem total-free field mismatch")

        cursor = handle_offset + 2 * handle_count
        for start, end in sorted(ranges):
            need(start == cursor, "LMem heap has a gap or overlap")
            cursor = end
        need(cursor == logical_size, "LMem heap does not cover logical size")
        # Bytes from logical_size through the VM allocation are allocator slack.

    def only_chunk(self) -> bytes:
        need(len(self.chunks) == 1, "expected exactly one live LMem chunk")
        return next(iter(self.chunks.values())).payload


# ---------------------------------------------------------------------------
# Database manager, ElementArrays, and Help document data


@dataclass(frozen=True)
class DBItemRef:
    group: int
    item: int


@dataclass
class DBGroup:
    vm: VMFile
    handle: int
    raw: bytes = field(init=False)
    block_size: int = field(init=False)
    heap_start: int = field(init=False)
    item_blocks: dict[int, int] = field(init=False, default_factory=dict)
    free_items: set[int] = field(init=False, default_factory=set)
    free_blocks: set[int] = field(init=False, default_factory=set)

    def __post_init__(self) -> None:
        self.raw = self.vm.block(self.handle, 0xff01)
        need(len(self.raw) >= 16, "truncated DB group")
        own, runtime, flags, first_block, first_free_item, first_free_block, \
            block_size, num_items = struct.unpack_from("<8H", self.raw)
        need(own == self.handle, "DB group self handle mismatch")
        need(flags & 0x1fff == 0, "DB group has undefined flag bits")
        need(16 <= block_size <= len(self.raw), "invalid DB group logical size")
        self.block_size = block_size
        # DBGH_numItems was added with the new ungroup allocator.  In an old
        # group (GF_NEW_UNGROUP clear), its word at 0x0e is the first legacy
        # DBItemInfo slot rather than a header field.
        self.heap_start = 16 if flags & 0x4000 else 14
        current = first_block
        seen: set[int] = set()
        while current:
            need(current not in seen and self.heap_start <= current <= block_size - 6
                 and current % 2 == 0,
                 "bad DB item-block-info chain")
            seen.add(current)
            next_info, block, reference_count = struct.unpack_from("<HHh", self.raw, current)
            record = self.vm.records.get(block)
            need(record is not None and record.used and record.uid == 0xff02,
                 "DB group points to invalid item block")
            need(reference_count >= 0, "negative DB item-block reference count")
            need(block not in self.item_blocks, "duplicate DB item block")
            self.item_blocks[block] = current
            current = next_info
        self.free_items = self._free_chain(first_free_item, 4, "item")
        self.free_blocks = self._free_chain(first_free_block, 6, "block")
        need(not (seen & self.free_blocks), "active and free DB block infos overlap")
        if flags & 0x4000:  # GF_NEW_UNGROUP
            need(num_items <= 0x3fff, "invalid DB group item count")
        # runtime and non-new-ungroup num_items are cache/legacy fields.

    def _free_chain(self, first: int, size: int, description: str) -> set[int]:
        result: set[int] = set()
        current = first
        while current:
            need(current not in result and current % 2 == 0,
                 f"cyclic DB free-{description} chain")
            need(self.heap_start <= current <= self.block_size - size,
                 f"DB free-{description} record outside group")
            result.add(current)
            current = u16(self.raw, current)
        return result

    def item(self, offset: int) -> bytes:
        need(offset % 2 == 0 and self.heap_start <= offset <= self.block_size - 4,
             "DB item offset is outside group")
        need(offset not in self.free_items, "DB item offset names a free record")
        info_offset, chunk_handle = struct.unpack_from("<2H", self.raw, offset)
        need(info_offset in self.item_blocks.values(), "DB item has invalid block-info pointer")
        block_handle = u16(self.raw, info_offset + 2)
        block = LMemBlock(self.vm.block(block_handle, 0xff02), header_size=20,
                          expected_type=0, self_handle=block_handle,
                          require_vm_flag=False)
        need(u16(block.raw, 16) == block_handle, "DB item block self handle mismatch")
        need(u16(block.raw, 18) == info_offset, "DB item block info pointer mismatch")
        chunk = block.chunks.get(chunk_handle)
        need(chunk is not None, "DB item points to an absent LMem chunk")
        return chunk.payload

    def all_items(self) -> dict[int, bytes]:
        """Recover and validate every allocated DBItemInfo in this group."""
        result: dict[int, bytes] = {}
        claimed_slots: set[int] = set()
        for block_handle, info_offset in self.item_blocks.items():
            block = LMemBlock(self.vm.block(block_handle, 0xff02), header_size=20,
                              expected_type=0, self_handle=block_handle,
                              require_vm_flag=False)
            need(u16(block.raw, 16) == block_handle, "DB item block self handle mismatch")
            need(u16(block.raw, 18) == info_offset, "DB item block info pointer mismatch")
            by_chunk: dict[int, list[int]] = {handle: [] for handle in block.chunks}
            for offset in range(self.heap_start, self.block_size - 3, 2):
                if u16(self.raw, offset) == info_offset:
                    chunk_handle = u16(self.raw, offset + 2)
                    if chunk_handle in by_chunk:
                        by_chunk[chunk_handle].append(offset)
            need(all(len(offsets) == 1 for offsets in by_chunk.values()),
                 "DB item chunks do not have unique DBItemInfo records")
            need(s16(self.raw, info_offset + 4) == len(by_chunk),
                 "DB item-block reference count mismatch")
            for chunk_handle, offsets in by_chunk.items():
                offset = offsets[0]
                need(offset not in claimed_slots, "overlapping DB group structures")
                claimed_slots.add(offset)
                result[offset] = block.chunks[chunk_handle].payload
        return result


class Database:
    def __init__(self, vm: VMFile):
        self.vm = vm
        raw = vm.block(vm.db_map_handle, 0xff00)
        need(len(raw) >= 12, "truncated DB map block")
        own, runtime, map_group, map_item, ungrouped, new_ungrouped = \
            struct.unpack_from("<6H", raw)
        need(own == vm.db_map_handle, "DB map self handle mismatch")
        self.map_ref = DBItemRef(map_group, map_item)
        self.ungrouped = ungrouped
        self.new_ungrouped = new_ungrouped
        self.groups: dict[int, DBGroup] = {}
        # runtime and bytes after the twelve-byte structure are allocator state/slack.

    def group(self, handle: int) -> DBGroup:
        if handle not in self.groups:
            self.groups[handle] = DBGroup(self.vm, handle)
        return self.groups[handle]

    def item(self, reference: DBItemRef) -> bytes:
        return self.group(reference.group).item(reference.item)

    def all_items(self) -> dict[DBItemRef, bytes]:
        result: dict[DBItemRef, bytes] = {}
        group_handles = {record.handle for record in self.vm.records.values()
                         if record.used and record.uid == 0xff01}
        if self.ungrouped:
            need(self.ungrouped in group_handles, "DB map has invalid ungrouped handle")
        if self.new_ungrouped:
            need(self.new_ungrouped in group_handles, "DB map has invalid new-ungrouped handle")
        referenced_blocks: set[int] = set()
        for group_handle in group_handles:
            group = self.group(group_handle)
            referenced_blocks.update(group.item_blocks)
            for item_offset, payload in group.all_items().items():
                result[DBItemRef(group_handle, item_offset)] = payload
        actual_blocks = {record.handle for record in self.vm.records.values()
                         if record.used and record.uid == 0xff02}
        need(referenced_blocks == actual_blocks, "unreferenced or missing DB item block")
        return result


@dataclass(frozen=True)
class ArrayElement:
    token: int
    data: bytes
    free: bool


@dataclass
class ElementArray:
    data: bytes
    header_size: int
    fixed_size: int | None = None
    array_type: int | None = None
    elements: list[ArrayElement] = field(init=False, default_factory=list)
    free_head: int = field(init=False)

    def __post_init__(self) -> None:
        need(len(self.data) >= self.header_size, "truncated ElementArray")
        count, element_size, current_offset, data_offset, self.free_head = \
            struct.unpack_from("<5H", self.data)
        need(current_offset == 0, "ElementArray has non-zero transient cursor")
        need(data_offset == self.header_size, "unexpected ElementArray data offset")
        if self.fixed_size is not None:
            need(element_size == self.fixed_size, "wrong fixed ElementArray element size")
        if self.array_type is not None:
            need(self.header_size >= 12 and self.data[10] == self.array_type and self.data[11] == 0,
                 "wrong TextElementArray type or reserved byte")
        ranges: list[tuple[int, int]] = []
        if element_size:
            need(data_offset + count * element_size == len(self.data),
                 "fixed ElementArray size mismatch")
            ranges = [(data_offset + index * element_size,
                       data_offset + (index + 1) * element_size)
                      for index in range(count)]
        else:
            need(data_offset + count * 2 <= len(self.data), "truncated variable offset table")
            offsets = [u16(self.data, data_offset + 2 * index) for index in range(count)]
            need(offsets == sorted(offsets), "ElementArray offsets do not ascend")
            if count:
                need(offsets[0] >= data_offset + count * 2,
                     "first ElementArray element overlaps offset table")
            ranges = [(start, offsets[index + 1] if index + 1 < count else len(self.data))
                      for index, start in enumerate(offsets)]
        for token, (start, end) in enumerate(ranges):
            need(start <= end <= len(self.data), "ElementArray element range is invalid")
            element = self.data[start:end]
            # Zero-length entries are legal deleted variable elements; their token
            # is retained in the offset table but no RefElementHeader remains.
            free = not element or (len(element) >= 3 and element[2] == 0xff)
            if element:
                need(len(element) >= 3, "truncated RefElementHeader")
            self.elements.append(ArrayElement(token, element, free))
        self._validate_free_list()

    def _validate_free_list(self) -> None:
        free_tokens = {element.token for element in self.elements if element.free}
        seen: set[int] = set()
        current = self.free_head
        while current != 0xffff:
            need(current in free_tokens and current not in seen,
                 "bad ElementArray free-token list")
            seen.add(current)
            element = self.elements[current].data
            if not element:
                # A zero-sized deleted slot cannot carry a link and is only
                # permitted when it is not the list head.
                raise FormatError("zero-sized ElementArray slot is linked as free")
            current = u16(element)
        need(seen == free_tokens, "not all free ElementArray elements are linked")


def vm_element_array(vm: VMFile, handle: int, array_type: int,
                     element_size: int) -> ElementArray:
    record = vm.records.get(handle)
    need(record is not None and record.used and record.uid == 0,
         "attribute-array VM handle is invalid")
    lmem = LMemBlock(vm.block(handle), expected_type=0, self_handle=handle)
    return ElementArray(lmem.only_chunk(), 12, element_size, array_type)


@dataclass(frozen=True)
class NameElement:
    token: int
    reference_count: int
    name_type: int
    context_type: int
    file_token: int
    text: DBItemRef
    extension: bytes
    name_bytes: bytes


@dataclass(frozen=True)
class CharAttr:
    token: int
    style_token: int
    font_id: int
    point_size: float
    text_styles: int
    foreground: tuple[int, int, int]
    track_kerning: int
    font_weight: int
    font_width: int
    extended_styles: int
    gray_screen: int
    pattern: tuple[int, int]
    background: tuple[int, int, int]
    background_gray: int
    background_pattern: tuple[int, int]


@dataclass(frozen=True)
class Tab:
    position: int
    attributes: int
    gray_screen: int
    line_width: int
    line_spacing: int
    anchor: int


@dataclass(frozen=True)
class ParaAttr:
    token: int
    raw: bytes
    tabs: tuple[Tab, ...]


@dataclass(frozen=True)
class TypeAttr:
    token: int
    hyperlink_name: int
    hyperlink_file: int
    context: int


@dataclass(frozen=True)
class GraphicAttr:
    token: int
    vm_chain_low: int
    vm_chain_high: int
    width: int
    height: int
    graphic_type: int
    flags: int
    reserved: bytes
    opaque: bytes


@dataclass(frozen=True)
class GStringCommand:
    opcode: int
    raw: bytes
    fields: dict[str, object] = field(default_factory=dict)


def parse_huge_array(vm: VMFile, directory_handle: int,
                     owned_data_handles: set[int] | None = None) -> list[bytes]:
    """Return each variable element of a GString HugeArray."""
    directory = vm.block(directory_handle, 0xff03)
    lmem = LMemBlock(directory, expected_type=0)
    need(lmem.handle_offset >= 28, "truncated HugeArray directory header")
    first_data, directory_chunk, extended_directory, own_handle, element_size = \
        struct.unpack_from("<5H", directory, 16)
    need(directory[0:2] == directory[16:18], "HugeArray VM-chain link mismatch")
    need(directory_chunk == lmem.handle_offset, "HugeArray directory chunk mismatch")
    need(extended_directory == 0, "extended HugeArray directories are unsupported")
    need(own_handle == directory_handle, "HugeArray self handle mismatch")
    need(element_size == 0, "GString HugeArray is not variable-sized")
    need(set(lmem.chunks) == {directory_chunk}, "unexpected HugeArray directory chunks")
    chunk = lmem.chunks[directory_chunk].payload
    count, fixed_size, cursor, data_offset = struct.unpack_from("<4H", chunk)
    need(fixed_size == 8 and cursor == 0 and data_offset == 8,
         "invalid HugeArray directory ChunkArray")
    need(len(chunk) == 8 + count * 8, "HugeArray directory size mismatch")
    entries = [struct.unpack_from("<IHH", chunk, 8 + index * 8)
               for index in range(count)]
    need(entries and entries[0] == (0xffffffff, 0, 0),
         "HugeArray directory lacks sentinel")
    need((entries[1][2] if len(entries) > 1 else 0) == first_data,
         "HugeArray first-data pointer mismatch")

    result: list[bytes] = []
    expected_first = 0
    previous = 0
    for index, (last, directory_size, handle) in enumerate(entries[1:], 1):
        need(last >= expected_first, "HugeArray directory indices do not ascend")
        expected_count = last - expected_first + 1
        data = vm.block(handle, 0xff04)
        if owned_data_handles is not None:
            need(handle not in owned_data_handles,
                 "HugeArray data block belongs to more than one directory")
            owned_data_handles.add(handle)
        block = LMemBlock(data, expected_type=0)
        next_handle, previous_handle, parent = struct.unpack_from("<3H", data, 16)
        need(data[0:2] == data[16:18], "HugeArray data VM-chain link mismatch")
        # Early HugeArray writers used the directory, rather than zero, as the
        # first HAB_prev backlink.  Both values have defined parent semantics.
        expected_previous = (0, directory_handle) if index == 1 else (previous,)
        need(previous_handle in expected_previous and parent == directory_handle,
             "broken HugeArray data backlink")
        expected_next = entries[index + 1][2] if index + 1 < len(entries) else 0
        need(next_handle == expected_next, "broken HugeArray data forward link")
        need(block.handle_offset == 24 and set(block.chunks) == {24},
             "invalid HugeArray data handle table")
        array = block.chunks[24].payload
        array_count, array_size, array_cursor, array_offset = \
            struct.unpack_from("<4H", array)
        need((array_count, array_size, array_cursor, array_offset) ==
             (expected_count, 0, 0, 8), "invalid HugeArray data ChunkArray")
        offsets = [u16(array, 8 + item * 2) for item in range(array_count)]
        need(offsets == sorted(offsets), "HugeArray element offsets do not ascend")
        need(not offsets or offsets[0] == 8 + 2 * array_count,
             "first HugeArray element offset is invalid")
        for item, start in enumerate(offsets):
            end = offsets[item + 1] if item + 1 < len(offsets) else len(array)
            need(start < end <= len(array), "invalid HugeArray element range")
            result.append(array[start:end])
        used_size = block.logical_size - sum(end - start
                                             for start, end in block.free_ranges)
        need(directory_size == used_size, "HugeArray directory block-size mismatch")
        expected_first = last + 1
        previous = handle
    need(len(result) == expected_first, "HugeArray total element count mismatch")
    return result


_GSTRING_FIXED_SIZES = {
    0x00: 1, 0x02: 1, 0x03: 9, 0x0d: 3, 0x0f: 2,
    0x10: 5, 0x11: 9, 0x12: 9, 0x13: 29, 0x14: 9, 0x15: 29,
    0x16: 1, 0x17: 1, 0x18: 1, 0x19: 1, 0x1a: 1,
    0x20: 9, 0x21: 5, 0x22: 9, 0x23: 7, 0x24: 3, 0x25: 7,
    0x26: 3, 0x28: 14, 0x29: 27, 0x2a: 19, 0x2b: 19,
    0x2c: 9, 0x2d: 5, 0x2e: 11, 0x2f: 7,
    0x32: 17, 0x33: 13, 0x34: 13, 0x35: 9,
    0x37: 5, 0x38: 1, 0x3a: 6, 0x3b: 2,
    0x3f: 7, 0x40: 9, 0x41: 1, 0x42: 9, 0x43: 5,
    0x44: 11, 0x45: 7, 0x46: 14, 0x48: 9, 0x49: 2,
    0x4a: 27, 0x4b: 19, 0x4e: 9, 0x4f: 7, 0x52: 9, 0x53: 7,
    0x60: 1, 0x61: 1, 0x62: 2, 0x63: 5, 0x64: 9,
    0x65: 1, 0x66: 1, 0x67: 6, 0x69: 4, 0x6a: 2, 0x6b: 2,
    0x6c: 5, 0x6d: 2, 0x6e: 2, 0x6f: 14, 0x70: 5, 0x71: 3,
    0x72: 2, 0x73: 9, 0x75: 4, 0x76: 2, 0x77: 2, 0x78: 7,
    0x79: 2, 0x7a: 9, 0x7b: 3, 0x7d: 4, 0x7e: 2, 0x7f: 2,
    0x80: 3, 0x81: 3, 0x82: 4, 0x83: 25, 0x84: 6, 0x85: 2,
    0x86: 9, 0x87: 3, 0x88: 2, 0x89: 2, 0x8a: 3, 0x8b: 3,
    0x8c: 3, 0x8e: 9, 0x8f: 2,
    0xa0: 5, 0xa1: 1, 0xa2: 11, 0xa3: 11, 0xa4: 1,
    0xa5: 4, 0xa6: 4, 0xa7: 1,
}


def parse_gstring_command(raw: bytes) -> GStringCommand:
    need(raw, "zero-length GString element")
    opcode = raw[0]
    fields: dict[str, object] = {}
    if opcode in _GSTRING_FIXED_SIZES:
        need(len(raw) == _GSTRING_FIXED_SIZES[opcode],
             f"wrong size for GString opcode {opcode:#04x}")
    elif opcode in (0x01,):  # GR_COMMENT
        need(len(raw) >= 3 and len(raw) == 3 + u16(raw, 1), "invalid GString comment")
        fields["payload"] = raw[3:]
    elif opcode == 0x0e:  # GR_ESCAPE
        need(len(raw) >= 5 and len(raw) == 5 + u16(raw, 3), "invalid GString escape")
        fields.update(code=u16(raw, 1), payload=raw[5:])
    elif opcode in (0x27, 0x30, 0x31, 0x36):
        need(len(raw) >= 3 and len(raw) == 3 + 4 * u16(raw, 1),
             "invalid variable coordinate GString element")
    elif opcode == 0x39:
        need(len(raw) >= 5 and len(raw) == 5 + 4 * u16(raw, 1),
             "invalid brush-polyline GString element")
    elif opcode == 0x3c:
        need(len(raw) >= 7 and len(raw) == 7 + u16(raw, 5), "invalid GR_DRAW_TEXT")
        fields["text"] = raw[7:]
    elif opcode == 0x3d:
        need(len(raw) >= 3 and len(raw) == 3 + u16(raw, 1), "invalid GR_DRAW_TEXT_CP")
        fields["text"] = raw[3:]
    elif opcode == 0x3e:
        need(len(raw) >= 15, "truncated GR_DRAW_TEXT_FIELD")
        total = u16(raw, 1)
        position = 15
        runs: list[tuple[bytes, bytes]] = []
        characters = 0
        while characters < total:
            need(position + 26 <= len(raw), "truncated text-field style run")
            count = u16(raw, position)
            need(0 < count <= total - characters, "invalid text-field run length")
            attr = raw[position + 2:position + 26]
            position += 26
            need(position + count <= len(raw), "truncated text-field string")
            runs.append((attr, raw[position:position + count]))
            position += count
            characters += count
        need(position == len(raw), "bytes follow text-field runs")
        fields["text_runs"] = runs
    elif opcode == 0x47:
        need(len(raw) >= 4 and len(raw) == 4 + 4 * u16(raw, 1),
             "invalid fill-polygon GString element")
        need(raw[3] in (0, 1), "invalid polygon fill rule")
    elif opcode in (0x4c, 0x50):
        need(len(raw) >= 7 and len(raw) == 7 + u16(raw, 5),
             "invalid positioned bitmap GString element")
        fields.update(x=s16(raw, 1), y=s16(raw, 3), bitmap=raw[7:])
    elif opcode in (0x4d, 0x51, 0x54):
        need(len(raw) >= 3 and len(raw) == 3 + u16(raw, 1),
             "invalid current-position bitmap GString element")
        fields["bitmap"] = raw[3:]
    elif opcode == 0x68:
        need(len(raw) >= 4 and len(raw) == 4 + 3 * u16(raw, 2),
             "invalid custom palette GString element")
    elif opcode == 0x74:
        need(len(raw) >= 5 and len(raw) == 5 + 2 * u16(raw, 3),
             "invalid custom line-style GString element")
    elif opcode in (0x7c, 0x8d):
        need(len(raw) >= 5 and len(raw) == 5 + u16(raw, 3),
             "invalid custom pattern GString element")
    else:
        raise FormatError(f"undefined or unsupported GString opcode {opcode:#04x}")
    return GStringCommand(opcode, raw, fields)


def parse_gstring(vm: VMFile, handle: int,
                  owned_data_handles: set[int] | None = None) -> tuple[GStringCommand, ...]:
    commands = tuple(parse_gstring_command(element)
                     for element in parse_huge_array(vm, handle, owned_data_handles))
    need(commands and commands[-1].opcode == 0, "GString lacks end marker")
    need(all(command.opcode != 0 for command in commands[:-1]),
         "GString has elements after end marker")
    return commands


@dataclass(frozen=True)
class TextRun:
    position: int
    token: int


@dataclass(frozen=True)
class RunArray:
    element_vm_block: int
    runtime_element_array: int
    runs: tuple[TextRun, ...]


@dataclass
class HelpPage:
    name: NameElement
    flags: int
    text_bytes: bytes
    char_runs: RunArray
    para_runs: RunArray
    type_runs: RunArray
    graphic_runs: RunArray


class HelpDocument:
    def __init__(self, data: bytes):
        self.vm = VMFile(data)
        self.database = Database(self.vm)
        self.names: list[NameElement] = []
        self.char_attrs: dict[int, CharAttr] = {}
        self.para_attrs: dict[int, ParaAttr] = {}
        self.type_attrs: dict[int, TypeAttr] = {}
        self.graphic_attrs: dict[int, GraphicAttr] = {}
        self.gstrings: dict[int, tuple[GStringCommand, ...]] = {}
        self.huge_data_handles: set[int] = set()
        self.incomplete_para_tokens: set[int] = set()
        self.pages: list[HelpPage] = []
        self._parse()

    def _parse(self) -> None:
        map_data = self.database.item(self.database.map_ref)
        need(len(map_data) == 51, "HelpFileMapBlock has wrong size")
        major, minor, flags, compression = struct.unpack_from("<HHHB", map_data)
        dictionary, names, chars, paras, types, graphics = struct.unpack_from("<6H", map_data, 7)
        need((major, minor) == (2, 0), "unsupported Help file protocol")
        need(flags & 0x3fff == 0, "HelpFileMapBlock has undefined flags")
        need(compression in (0, 2), "unsupported Help compression method")
        need(dictionary == 0, "Help compression dictionaries are unsupported")
        need(all((names, chars, paras, types)), "Help map lacks a required attribute array")
        need(not any(map_data[19:]), "non-zero HelpFileMapBlock reserved bytes")
        self.flags = flags
        self.compression = compression
        self.handles = (names, chars, paras, types, graphics)
        self._parse_names(names)
        self._parse_char_attrs(chars)
        self._parse_para_attrs(paras)
        self._parse_type_attrs(types)
        if graphics:
            self._parse_graphic_attrs(graphics)
        self._parse_pages()
        referenced_char = {run.token for page in self.pages
                           for run in page.char_runs.runs[:-1]}
        referenced_para = {run.token for page in self.pages
                           for run in page.para_runs.runs[:-1]}
        referenced_type = {run.token for page in self.pages
                           for run in page.type_runs.runs[:-1]}
        referenced_graphic = {run.token for page in self.pages
                              for run in page.graphic_runs.runs[:-1]}
        need(referenced_char <= self.char_attrs.keys(),
             "a text run references a missing character element")
        need(not (referenced_para & self.incomplete_para_tokens),
             "a text run references an incomplete paragraph element")
        need(referenced_para <= self.para_attrs.keys(),
             "a text run references a missing paragraph element")
        need(referenced_type <= self.type_attrs.keys(),
             "a text run references a missing type element")
        need(referenced_graphic <= self.graphic_attrs.keys(),
             "a text run references a missing graphic element")
        self._validate_vm_ownership()

    def _validate_vm_ownership(self) -> None:
        """Require every used VM block to belong to one parsed Help object."""
        arrays = {handle for handle in self.handles if handle}
        groups = {record.handle for record in self.vm.records.values()
                  if record.used and record.uid == 0xff01}
        item_blocks = {record.handle for record in self.vm.records.values()
                       if record.used and record.uid == 0xff02}
        expected = ({32, self.vm.db_map_handle} | arrays | groups | item_blocks |
                    set(self.gstrings) | self.huge_data_handles)
        actual = {record.handle for record in self.vm.records.values() if record.used}
        need(actual == expected, "unowned or missing VM block in Help file")

    def _array_block(self, handle: int) -> bytes:
        record = self.vm.records.get(handle)
        need(record is not None and record.used and record.uid == 0,
             "Help array VM handle is invalid")
        return LMemBlock(self.vm.block(handle), expected_type=0,
                         self_handle=handle).only_chunk()

    def _parse_names(self, handle: int) -> None:
        array = ElementArray(self._array_block(handle), 12)
        need(u16(array.data, 2) == 0, "name array must use variable elements")
        need(u16(array.data, 10) == 16, "wrong Help name-array data size")
        for element in array.elements:
            if element.free:
                continue
            raw = element.data
            need(len(raw) >= 19, "truncated HelpFileNameArrayElement")
            reference_count = word_and_a_half(raw)
            name_type, context_type, file_token, item, group = \
                struct.unpack_from("<BBHHH", raw, 3)
            need(name_type in (0, 1), "invalid VisTextNameType")
            need(context_type in (0, 1, 2, 3, 4, 0xff), "invalid VisTextContextType")
            if name_type == 0:
                need(context_type != 0xff, "context name has file context type")
            else:
                need(context_type == 0xff, "file name lacks file context type")
            self.names.append(NameElement(element.token, reference_count, name_type,
                                          context_type, file_token,
                                          DBItemRef(group, item), raw[11:19], raw[19:]))

    def _parse_char_attrs(self, handle: int) -> None:
        array = vm_element_array(self.vm, handle, 0, 38)
        for element in array.elements:
            if element.free:
                continue
            raw = element.data
            need(len(raw) == 38, "wrong VisTextCharAttr size")
            need(not any(raw[31:38]), "non-zero VisTextCharAttr reserved bytes")
            self.char_attrs[element.token] = CharAttr(
                element.token, u16(raw, 3), u16(raw, 5),
                raw[7] / 256.0 + u16(raw, 8), raw[10], color_quad(raw, 11),
                s16(raw, 15), raw[17], raw[18], u16(raw, 19), raw[21],
                (raw[22], raw[23]), color_quad(raw, 24), raw[28],
                (raw[29], raw[30]))

    def _parse_para_attrs(self, handle: int) -> None:
        array = ElementArray(self._array_block(handle), 12, 0, 1)
        for element in array.elements:
            if element.free:
                continue
            raw = element.data
            if len(raw) == 3:
                # A few writers left an unreferenced RefElementHeader-only
                # slot in an otherwise valid variable ElementArray.  It has no
                # VisTextParaAttr body and is safe only while no run names it.
                self.incomplete_para_tokens.add(element.token)
                continue
            need(len(raw) >= 72 and (len(raw) - 72) % 8 == 0,
                 "wrong VisTextParaAttr size")
            tab_count = raw[31]
            need(len(raw) == 72 + tab_count * 8, "paragraph tab count/size mismatch")
            need(not any(raw[57:72]), "non-zero VisTextParaAttr reserved bytes")
            tabs = tuple(Tab(*struct.unpack_from("<HBBBBH", raw, 72 + index * 8))
                         for index in range(tab_count))
            self.para_attrs[element.token] = ParaAttr(element.token, raw, tabs)

    def _parse_type_attrs(self, handle: int) -> None:
        array = vm_element_array(self.vm, handle, 3, 10)
        for element in array.elements:
            raw = element.data
            need(raw[9] == 0, "non-zero VisTextType unused byte")
            # A historic text-library writer can leave a still-referenced
            # fixed-size type record on the ElementArray free list.  Unlike a
            # variable free element, the complete ten-byte record remains in
            # its fixed slot and is therefore the authoritative run target.
            self.type_attrs[element.token] = TypeAttr(
                element.token, u16(raw, 3), u16(raw, 5), u16(raw, 7))

    def _parse_graphic_attrs(self, handle: int) -> None:
        array = vm_element_array(self.vm, handle, 2, 50)
        for element in array.elements:
            if element.free:
                continue
            raw = element.data
            graphic_type = raw[11]
            flags = u16(raw, 12)
            need(graphic_type in (0, 1), "invalid VisTextGraphicType")
            need(flags & 0x1fff == 0, "undefined VisTextGraphicFlags bits")
            attr = GraphicAttr(
                element.token, u16(raw, 3), u16(raw, 5), u16(raw, 7), u16(raw, 9),
                graphic_type, flags, raw[14:18], raw[18:50])
            need(not any(attr.reserved), "non-zero VisTextGraphic reserved bytes")
            if graphic_type == 0:
                need(attr.flags == 0, "GString graphic has unexpected flags")
                need(attr.vm_chain_low == 0 and attr.vm_chain_high != 0,
                     "serialized GString is not a VM HugeArray chain")
                if attr.vm_chain_high not in self.gstrings:
                    self.gstrings[attr.vm_chain_high] = parse_gstring(
                        self.vm, attr.vm_chain_high, self.huge_data_handles)
            else:
                need((attr.vm_chain_low, attr.vm_chain_high) == (0, 0),
                     "variable graphic unexpectedly has a VM chain")
                need(attr.flags == 0x8000, "variable graphic has unexpected flags")
                need(u16(attr.opaque) == 0, "unknown variable-graphic manufacturer")
                need(u16(attr.opaque, 2) <= 14, "unknown VisTextVariableType")
            self.graphic_attrs[element.token] = attr

    @staticmethod
    def _run_array(data: bytes, expected_block: int) -> RunArray:
        need(len(data) >= 12, "truncated TextRunArray")
        count, element_size, cursor, data_offset, block, runtime_array = \
            struct.unpack_from("<6H", data)
        need(element_size == 5 and cursor == 0 and data_offset == 12,
             "invalid TextRunArray header")
        need(block == expected_block, "TextRunArray references wrong element block")
        need(len(data) == 12 + count * 5 and count >= 1,
             "TextRunArray size mismatch")
        runs = tuple(TextRun(word_and_a_half(data, 12 + index * 5),
                             u16(data, 15 + index * 5))
                     for index in range(count))
        need(runs[-1] == TextRun(0xffffff, 0xffff), "TextRunArray lacks sentinel")
        # ChunkArray itself does not impose ordering.  Normal text-library
        # arrays ascend, but old help writers can leave duplicated descending
        # graphic-run fragments; those entries are still structurally valid.
        return RunArray(block, runtime_array, runs)

    def _parse_page(self, name: NameElement, data: bytes) -> HelpPage:
        if self.compression == 2:
            need(len(data) >= 4, "truncated compressed Help page")
            expected = u16(data)
            data = dcl_explode(data[2:])
            need(len(data) == expected, "Help page decompressed-size mismatch")
        need(len(data) >= 2, "truncated serialized VisText page")
        flags = u16(data)
        need(flags & 0x000f == 0, "VisTextSaveDBFlags reserved bits are set")
        need(flags & 0x8000, "Help page has no text")
        save_types = ((flags >> 13) & 3, (flags >> 11) & 3,
                      (flags >> 9) & 3, (flags >> 7) & 3)
        need(save_types == (2, 2, 2, 2),
             "Help page does not use external-element run arrays")
        need(flags & 0x0070 == 0, "styles, regions, or names in page are unsupported")
        position = 2
        chunks: list[bytes] = []
        for _ in range(5):
            need(position + 2 <= len(data), "truncated serialized VisText chunk size")
            size = u16(data, position)
            position += 2
            need(position + size <= len(data), "serialized VisText chunk is truncated")
            chunks.append(data[position:position + size])
            position += size
        need(position == len(data), "bytes follow serialized VisText page")
        text, chars, paras, types, graphics = chunks
        need(text and text[-1] == 0, "Help page text is not NUL-terminated")
        text_length = len(text) - 1
        char_runs = self._run_array(chars, self.handles[1])
        para_runs = self._run_array(paras, self.handles[2])
        type_runs = self._run_array(types, self.handles[3])
        graphic_runs = self._run_array(graphics, self.handles[4])
        for run_array in (char_runs, para_runs, type_runs, graphic_runs):
            need(all(run.position <= text_length for run in run_array.runs[:-1]),
                 "text run begins beyond page text")
        need(char_runs.runs[0].position == 0 and para_runs.runs[0].position == 0
             and type_runs.runs[0].position == 0,
             "character, paragraph, or type runs do not begin at zero")
        return HelpPage(name, flags, text[:-1], char_runs, para_runs,
                        type_runs, graphic_runs)

    def _parse_pages(self) -> None:
        all_items = self.database.all_items()
        need(self.database.map_ref in all_items, "DB map item is not allocated")
        seen: dict[DBItemRef, HelpPage] = {}
        names_by_item: dict[DBItemRef, NameElement] = {}
        for name in self.names:
            if name.name_type != 0 or name.text == DBItemRef(0, 0):
                continue
            names_by_item.setdefault(name.text, name)
            if name.text not in seen:
                need(name.text in all_items, "name points to an unallocated DB item")
                seen[name.text] = self._parse_page(name, all_items[name.text])
                self.pages.append(seen[name.text])
        for reference in sorted(all_items, key=lambda item: (item.group, item.item)):
            if reference == self.database.map_ref or reference in seen:
                continue
            synthetic = NameElement(
                0xffff, 0, 0, 0, 0xffff, reference, b"\0" * 8,
                f"orphan-{reference.group:04x}-{reference.item:04x}".encode("ascii"))
            self.pages.append(self._parse_page(synthetic, all_items[reference]))


# ---------------------------------------------------------------------------
# Bitmap and GString rasterization


def fixed_16_16(data: bytes, offset: int) -> float:
    return s16(data, offset + 2) + u16(data, offset) / 65536.0


def fixed_32_16(data: bytes, offset: int) -> float:
    return s32(data, offset + 2) + u16(data, offset) / 65536.0


def wb_fixed(data: bytes, offset: int) -> float:
    need(offset + 3 <= len(data), "truncated WBFixed")
    return u16(data, offset + 1) + data[offset] / 256.0


def multiply_matrix(new: tuple[float, ...], current: tuple[float, ...]) -> tuple[float, ...]:
    na, nb, nc, nd, ne, nf = new
    ca, cb, cc, cd, ce, cf = current
    return (na * ca + nb * cc, na * cb + nb * cd,
            nc * ca + nd * cc, nc * cb + nd * cd,
            ne * ca + nf * cc + ce, ne * cb + nf * cd + cf)


@dataclass(frozen=True)
class BitmapSlice:
    width: int
    height: int
    compact: int
    bitmap_type: int
    start: int
    scans: int
    x_resolution: int
    y_resolution: int
    palette: tuple[tuple[int, int, int], ...] | None
    rows: tuple[tuple[bytes | None, bytes], ...]
    descriptor: bool = False


def decode_packbits_rows(data: bytes, row_size: int, rows: int) -> list[bytes]:
    position = 0
    result: list[bytes] = []
    for _ in range(rows):
        row = bytearray()
        while len(row) < row_size:
            need(position < len(data), "truncated PackBits scan line")
            control = struct.unpack_from("<b", data, position)[0]
            position += 1
            if control >= 0:
                count = control + 1
                need(position + count <= len(data), "truncated PackBits literal run")
                row.extend(data[position:position + count])
                position += count
            else:
                count = 1 - control
                need(position < len(data), "truncated PackBits repeat run")
                row.extend(data[position:position + 1] * count)
                position += 1
            need(len(row) <= row_size, "PackBits run crosses scan-line boundary")
        result.append(bytes(row))
    need(position == len(data), "bytes follow PackBits scan data")
    return result


def parse_cbitmap(data: bytes, allow_descriptor: bool = False) -> BitmapSlice:
    need(len(data) >= 20, "truncated CBitmap")
    width, height, compact, bitmap_type, start, scans, device_info, data_offset, \
        palette_offset, x_resolution, y_resolution = struct.unpack_from("<HHBB7H", data)
    need(width and height and x_resolution and y_resolution, "invalid CBitmap dimensions")
    need(bitmap_type & 0x08, "serialized bitmap is not a complex CBitmap")
    need(compact in (0, 1), "unsupported CBitmap compaction")
    pixel_format = bitmap_type & 7
    need(pixel_format in (0, 1, 2), "unsupported CBitmap pixel format")

    descriptor = scans == 0
    if descriptor:
        # Complex bitmap sequences may start with the 20-byte descriptor by
        # itself, or with a descriptor followed by its palette.  In the latter
        # representation CB_data points one byte past the serialized object.
        need(allow_descriptor and start == 0 and
             data_offset in (0, 20, len(data)),
             "invalid header-only CBitmap descriptor")
    else:
        need(start + scans <= height, "CBitmap scan range exceeds image")
        need(20 <= data_offset <= len(data), "CBitmap data offset is invalid")

    palette = None
    accounted: list[tuple[int, int]] = [(0, 20)]
    if not descriptor:
        accounted.append((data_offset, len(data)))
    if bitmap_type & 0x40:
        need(20 <= palette_offset <= len(data) - 2, "CBitmap palette offset is invalid")
        count = u16(data, palette_offset)
        need(count in (2, 16, 256), "unsupported CBitmap palette size")
        palette_end = palette_offset + 2 + count * 3
        need(palette_end <= len(data), "truncated CBitmap palette")
        palette = tuple(tuple(data[palette_offset + 2 + 3 * index:
                                   palette_offset + 5 + 3 * index])
                        for index in range(count))
        accounted.append((palette_offset, palette_end))
    # CB_devInfo and an inactive CB_palette are transient pointers/offsets and
    # are not dereferenced unless the corresponding serialized flag is set.
    _ = device_info

    merged: list[tuple[int, int]] = []
    for start_range, end_range in sorted(accounted):
        need(not merged or start_range >= merged[-1][1], "overlapping CBitmap regions")
        if merged and start_range == merged[-1][1]:
            merged[-1] = (merged[-1][0], end_range)
        else:
            merged.append((start_range, end_range))
    cursor = 0
    for start_range, end_range in merged:
        need(not any(data[cursor:start_range]), "non-zero CBitmap alignment bytes")
        cursor = end_range
    need(cursor == len(data), "unaccounted CBitmap bytes")

    if descriptor:
        return BitmapSlice(width, height, compact, bitmap_type, 0, 0,
                           x_resolution, y_resolution, palette, (), True)
    pixel_bytes = ((width + 7) // 8 if pixel_format == 0 else
                   (width + 1) // 2 if pixel_format == 1 else width)
    mask_bytes = (width + 7) // 8 if bitmap_type & 0x10 else 0
    row_size = pixel_bytes + mask_bytes
    packed = data[data_offset:]
    decoded = (decode_packbits_rows(packed, row_size, scans) if compact == 1 else
               [packed[index * row_size:(index + 1) * row_size]
                for index in range(scans)])
    if compact == 0:
        need(len(packed) == scans * row_size, "raw CBitmap scan-data size mismatch")
    rows = tuple((row[:mask_bytes] if mask_bytes else None, row[mask_bytes:])
                 for row in decoded)
    return BitmapSlice(width, height, compact, bitmap_type, start, scans,
                       x_resolution, y_resolution, palette, rows)


def assemble_bitmap(parts: list[bytes], fill_color: tuple[int, int, int] | None):
    need(Image is not None, "Pillow is required for bitmap rendering")
    need(parts, "empty bitmap slice sequence")
    first = parse_cbitmap(parts[0], allow_descriptor=len(parts) > 1)
    if first.descriptor:
        need(len(parts) > 1, "CBitmap descriptor has no slices")
        slices = [first] + [parse_cbitmap(part) for part in parts[1:]]
    else:
        slices = [first] + [parse_cbitmap(part) for part in parts[1:]]
    palette = next((item.palette for item in slices if item.palette is not None), None)
    if palette is None:
        palette = GEOS_PALETTE
    covered = [False] * first.height
    output = Image.new("RGBA", (first.width, first.height), (0, 0, 0, 0))
    pixels = output.load()
    base_shape = first.bitmap_type & (0x10 | 7)
    for item in slices:
        need((item.width, item.height) == (first.width, first.height),
             "CBitmap slices disagree on dimensions")
        need((item.x_resolution, item.y_resolution) ==
             (first.x_resolution, first.y_resolution),
             "CBitmap slices disagree on resolution")
        need((item.bitmap_type & (0x10 | 7)) == base_shape,
             "CBitmap slices disagree on pixel format")
        for row_index, (mask, pixel_data) in enumerate(item.rows):
            y = item.start + row_index
            need(not covered[y], "overlapping CBitmap slices")
            covered[y] = True
            for x in range(item.width):
                opaque = True
                if mask is not None:
                    opaque = bool(mask[x // 8] & (0x80 >> (x & 7)))
                pixel_format = item.bitmap_type & 7
                if pixel_format == 0:
                    bit = bool(pixel_data[x // 8] & (0x80 >> (x & 7)))
                    if fill_color is None:
                        opaque = opaque and bit
                        color = (0, 0, 0)
                    else:
                        opaque = opaque and bit
                        color = fill_color
                elif pixel_format == 1:
                    value = (pixel_data[x // 2] >> 4) if not x & 1 else pixel_data[x // 2] & 15
                    need(value < len(palette), "4-bit pixel exceeds palette")
                    color = palette[value]
                else:
                    value = pixel_data[x]
                    need(value < len(palette), "8-bit pixel exceeds palette")
                    color = palette[value]
                pixels[x, y] = (*color, 255 if opaque else 0)
    need(all(covered), "bitmap slices do not cover every scan line")
    return output, first.x_resolution, first.y_resolution


def geos_character(byte: int) -> str:
    if byte == 0x19:
        return ""
    if byte == 0x1b:
        return "\u2009"
    if byte == 0x1c:
        return "\u2002"
    if byte == 0x1d:
        return "\u2003"
    if byte == 0x1e:
        return "\u2011"
    if byte == 0x1f:
        return "\u00ad"
    if byte == 0xca:
        return "\u00a0"
    return bytes((byte,)).decode("mac_roman")


def gstring_color(data: bytes, offset: int) -> tuple[int, int, int]:
    """Decode ColorFlag followed by RGBValue (LineAttr/AreaAttr layout)."""
    need(offset + 4 <= len(data), "truncated GString color attribute")
    mode = data[offset]
    red_or_index, green, blue = data[offset + 1:offset + 4]
    if mode == 0:
        return GEOS_PALETTE[red_or_index]
    if mode == 1:
        return (red_or_index,) * 3
    if mode == 3:
        return (255 - red_or_index, 255 - green, 255 - blue)
    if mode == 0x80:
        return (red_or_index, green, blue)
    raise FormatError(f"unsupported GString ColorFlag {mode:#04x}")


@dataclass
class GStringState:
    matrix: tuple[float, ...] = (1, 0, 0, 1, 0, 0)
    default_matrix: tuple[float, ...] = (1, 0, 0, 1, 0, 0)
    current: tuple[float, float] = (0, 0)
    line_color: tuple[int, int, int] = (0, 0, 0)
    area_color: tuple[int, int, int] = (0, 0, 0)
    text_color: tuple[int, int, int] = (0, 0, 0)
    line_mask: int = 25
    area_mask: int = 25
    text_mask: int = 25
    line_width: float = 1.0
    line_style: int = 0
    line_join: int = 0
    line_end: int = 0
    mix_mode: int = 1
    font_id: int = 0x1000
    point_size: float = 12.0
    text_styles: int = 0
    text_mode: int = 0
    path: list[list[tuple[float, float]]] | None = None
    clip = None


def _draw_mask_alpha(mask: int) -> int:
    inverse = bool(mask & 0x80)
    base = mask & 0x7f
    if 25 <= base <= 89:
        alpha = round(255 * (89 - base) / 64)
    elif base == 0x7f:
        alpha = 255
    else:
        # Named system hatch/tile masks are one-bit patterns; 50% gives their
        # average coverage when rasterized below the source device resolution.
        need(0 <= base <= 9, "unknown SystemDrawMask")
        alpha = 128
    return 255 - alpha if inverse else alpha


class FontCache:
    def __init__(self):
        self.cache: dict[tuple[int, int, bool, bool], object] = {}

    @staticmethod
    def family(font_id: int) -> str:
        group = (font_id & 0x0e00) // 0x0200
        if group == 0:
            return "DejaVuSerif"
        if group == 5:
            return "DejaVuSansMono"
        return "DejaVuSans"

    def get(self, font_id: int, pixels: float, bold: bool, italic: bool):
        need(ImageFont is not None, "Pillow is required for font rendering")
        size = max(1, min(600, round(pixels)))
        key = (font_id, size, bold, italic)
        if key not in self.cache:
            family = self.family(font_id)
            suffix = ("-BoldOblique" if bold and italic else "-Bold" if bold else
                      "-Oblique" if italic else "")
            if family == "DejaVuSerif" and italic:
                suffix = "-BoldItalic" if bold else "-Italic"
            filename = f"{family}{suffix}.ttf"
            try:
                font = ImageFont.truetype(filename, size)
            except OSError as error:
                raise FormatError(f"required TrueType font {filename} was not found") from error
            self.cache[key] = font
        return self.cache[key]


class GStringRenderer:
    SCALE = 96.0 / 72.0

    def __init__(self, document: HelpDocument, attr: GraphicAttr, fonts: FontCache):
        need(Image is not None and ImageDraw is not None and ImageChops is not None,
             "Pillow is required for GString rendering")
        self.document = document
        self.attr = attr
        self.fonts = fonts
        width = max(1, round(attr.width * self.SCALE))
        height = max(1, round(attr.height * self.SCALE))
        need(width <= 10000 and height <= 20000, "embedded graphic is unreasonably large")
        self.canvas = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        opaque = attr.opaque
        matrix = (fixed_16_16(opaque, 0), fixed_16_16(opaque, 4),
                  fixed_16_16(opaque, 8), fixed_16_16(opaque, 12),
                  fixed_32_16(opaque, 16), fixed_32_16(opaque, 22))
        self.state = GStringState(matrix=matrix, default_matrix=matrix,
                                  current=(s16(opaque, 28), s16(opaque, 30)))
        self.stack: list[GStringState] = []
        self.transform_stack: list[tuple[float, ...]] = []

    def point(self, point: tuple[float, float]) -> tuple[float, float]:
        x, y = point
        a, b, c, d, e, f = self.state.matrix
        return ((x * a + y * c + e) * self.SCALE,
                (x * b + y * d + f) * self.SCALE)

    @staticmethod
    def _raw_points(raw: bytes, offset: int, count: int) -> list[tuple[float, float]]:
        return [(s16(raw, offset + index * 4), s16(raw, offset + index * 4 + 2))
                for index in range(count)]

    def points(self, raw: bytes, offset: int, count: int) -> list[tuple[float, float]]:
        return [self.point(point) for point in self._raw_points(raw, offset, count)]

    def _composite(self, layer) -> None:
        alpha = layer.getchannel("A")
        if self.state.clip is not None:
            alpha = ImageChops.multiply(alpha, self.state.clip)
            layer.putalpha(alpha)
        mode = self.state.mix_mode
        if mode == 1:
            self.canvas.alpha_composite(layer)
            return
        if mode == 2:  # MM_NOP
            return
        destination = self.canvas.convert("RGB")
        source = layer.convert("RGB")
        if mode == 0:  # MM_CLEAR
            result = Image.new("RGB", self.canvas.size, (0, 0, 0))
        elif mode == 3:  # MM_AND -- multiplication is the color-device analogue
            result = ImageChops.multiply(destination, source)
        elif mode == 4:  # MM_INVERT
            result = ImageChops.invert(destination)
        elif mode == 5:  # MM_XOR
            result = ImageChops.difference(destination, source)
        elif mode == 6:  # MM_SET
            result = Image.new("RGB", self.canvas.size, (255, 255, 255))
        elif mode == 7:  # MM_OR
            result = ImageChops.lighter(destination, source)
        else:
            raise FormatError(f"invalid GString mix mode {mode}")
        mixed = Image.composite(result, destination, alpha).convert("RGBA")
        mixed.putalpha(ImageChops.lighter(self.canvas.getchannel("A"), alpha))
        self.canvas = mixed

    def _shape(self, points: list[tuple[float, float]], fill: bool,
               closed: bool = False, width: float | None = None) -> None:
        if self.state.path is not None:
            self.state.path.append(points + ([points[0]] if closed and points else []))
            return
        mask = self.state.area_mask if fill else self.state.line_mask
        alpha = _draw_mask_alpha(mask)
        if alpha == 0 or not points:
            return
        layer = Image.new("RGBA", self.canvas.size, (0, 0, 0, 0))
        draw = ImageDraw.Draw(layer)
        color = self.state.area_color if fill else self.state.line_color
        ink = (*color, alpha)
        line_width = max(1, round((self.state.line_width if width is None else width)
                                  * self.SCALE))
        if fill:
            draw.polygon(points, fill=ink)
        else:
            sequence = points + ([points[0]] if closed else [])
            if self.state.line_style == 0 or len(sequence) < 2:
                draw.line(sequence, fill=ink, width=line_width, joint="curve")
            else:
                dash = max(2, line_width * (4 if self.state.line_style == 1 else 1))
                for start, end in zip(sequence, sequence[1:]):
                    dx, dy = end[0] - start[0], end[1] - start[1]
                    length = math.hypot(dx, dy)
                    if not length:
                        continue
                    position = 0.0
                    draw_on = True
                    while position < length:
                        next_position = min(length, position + dash)
                        if draw_on:
                            p1 = (start[0] + dx * position / length,
                                  start[1] + dy * position / length)
                            p2 = (start[0] + dx * next_position / length,
                                  start[1] + dy * next_position / length)
                            draw.line((p1, p2), fill=ink, width=line_width)
                        draw_on = not draw_on
                        position = next_position
        self._composite(layer)

    def _rectangle(self, raw: bytes, offset: int, fill: bool, radius: float = 0) -> None:
        left, top, right, bottom = struct.unpack_from("<4h", raw, offset)
        points = [self.point((left, top)), self.point((right, top)),
                  self.point((right, bottom)), self.point((left, bottom))]
        if radius <= 0 or self.state.path is not None:
            self._shape(points, fill, True)
            return
        layer = Image.new("RGBA", self.canvas.size, (0, 0, 0, 0))
        draw = ImageDraw.Draw(layer)
        bounds = (min(point[0] for point in points), min(point[1] for point in points),
                  max(point[0] for point in points), max(point[1] for point in points))
        mask = self.state.area_mask if fill else self.state.line_mask
        color = self.state.area_color if fill else self.state.line_color
        ink = (*color, _draw_mask_alpha(mask))
        draw.rounded_rectangle(bounds, radius=max(1, round(radius * self.SCALE)),
                               fill=ink if fill else None, outline=None if fill else ink,
                               width=max(1, round(self.state.line_width * self.SCALE)))
        self._composite(layer)

    def _ellipse_points(self, bounds: tuple[float, float, float, float],
                        start: float = 0, end: float = 360) -> list[tuple[float, float]]:
        left, top, right, bottom = bounds
        steps = max(12, round(abs(end - start) / 4))
        result = []
        for index in range(steps + 1):
            angle = math.radians(start + (end - start) * index / steps)
            result.append(self.point(((left + right) / 2 + (right - left) / 2 * math.cos(angle),
                                      (top + bottom) / 2 - (bottom - top) / 2 * math.sin(angle))))
        return result

    def _curve(self, source: list[tuple[float, float]]) -> None:
        p0, p1, p2, p3 = source
        points = []
        for index in range(65):
            value = index / 64
            points.append(self.point((
                (1-value) ** 3 * p0[0] + 3 * (1-value) ** 2 * value * p1[0]
                + 3 * (1-value) * value ** 2 * p2[0] + value ** 3 * p3[0],
                (1-value) ** 3 * p0[1] + 3 * (1-value) ** 2 * value * p1[1]
                + 3 * (1-value) * value ** 2 * p2[1] + value ** 3 * p3[1])))
        self._shape(points, False)
        self.state.current = p3

    def _draw_text(self, text: bytes, position: tuple[float, float] | None = None,
                   text_attr: bytes | None = None) -> None:
        if text_attr is None:
            font_id = self.state.font_id
            point_size = self.state.point_size
            styles = self.state.text_styles
            color = self.state.text_color
            mask = self.state.text_mask
        else:
            need(len(text_attr) == 24, "wrong TextAttr size")
            font_id = u16(text_attr, 14)
            point_size = wb_fixed(text_attr, 16)
            styles = text_attr[7]
            color = color_quad(text_attr, 0)
            mask = text_attr[4]
        string = "".join(geos_character(byte) for byte in text)
        if not string:
            return
        font = self.fonts.get(font_id, point_size * self.SCALE,
                              bool(styles & 0x20), bool(styles & 0x10))
        source_position = self.state.current if position is None else position
        x, y = self.point(source_position)
        layer = Image.new("RGBA", self.canvas.size, (0, 0, 0, 0))
        draw = ImageDraw.Draw(layer)
        ink = (*color, _draw_mask_alpha(mask))
        draw.text((x, y - point_size * self.SCALE), string, font=font, fill=ink)
        width = draw.textlength(string, font=font) / self.SCALE
        self._composite(layer)
        self.state.current = (source_position[0] + width, source_position[1])

    def _draw_bitmap(self, parts: list[bytes], fill: bool,
                     source_position: tuple[float, float]) -> None:
        image, x_resolution, y_resolution = assemble_bitmap(
            parts, self.state.area_color if fill else None)
        scale_x = 72.0 / x_resolution * self.SCALE
        scale_y = 72.0 / y_resolution * self.SCALE
        width = max(1, round(image.width * scale_x))
        height = max(1, round(image.height * scale_y))
        image = image.resize((width, height), Image.Resampling.NEAREST)
        x, y = self.point(source_position)
        layer = Image.new("RGBA", self.canvas.size, (0, 0, 0, 0))
        layer.alpha_composite(image, (round(x), round(y)))
        self._composite(layer)
        self.state.current = source_position

    def _set_clip(self, mask, combine: int) -> None:
        need(combine in (0, 1, 2, 3), "invalid clip combine mode")
        if combine == 0:
            self.state.clip = Image.new("L", self.canvas.size, 0)
        elif combine == 1 or self.state.clip is None:
            self.state.clip = mask
        elif combine == 2:
            self.state.clip = ImageChops.lighter(self.state.clip, mask)
        else:
            self.state.clip = ImageChops.multiply(self.state.clip, mask)

    def render(self) -> object:
        commands = self.document.gstrings[self.attr.vm_chain_high]
        index = 0
        while index < len(commands):
            command = commands[index]
            opcode, raw = command.opcode, command.raw
            if opcode == 0:
                break
            if opcode in (0x01, 0x02, 0x03, 0x0d, 0x0e, 0x0f):
                pass  # comments, bounds, labels, escapes, and page hints
            elif opcode in (0x10, 0x11, 0x12, 0x13, 0x14, 0x15):
                if opcode == 0x10:
                    angle = math.radians(fixed_16_16(raw, 1))
                    transform = (math.cos(angle), math.sin(angle),
                                 -math.sin(angle), math.cos(angle), 0, 0)
                elif opcode == 0x11:
                    transform = (fixed_16_16(raw, 1), 0, 0,
                                 fixed_16_16(raw, 5), 0, 0)
                elif opcode == 0x12:
                    transform = (1, 0, 0, 1, fixed_16_16(raw, 1), fixed_16_16(raw, 5))
                elif opcode == 0x14:
                    transform = (1, 0, 0, 1, s32(raw, 1), s32(raw, 5))
                else:
                    transform = (fixed_16_16(raw, 1), fixed_16_16(raw, 5),
                                 fixed_16_16(raw, 9), fixed_16_16(raw, 13),
                                 fixed_32_16(raw, 17), fixed_32_16(raw, 23))
                self.state.matrix = (transform if opcode == 0x15 else
                                     multiply_matrix(transform, self.state.matrix))
            elif opcode == 0x16:
                self.state.matrix = (1, 0, 0, 1, 0, 0)
            elif opcode == 0x17:
                self.state.matrix = self.state.default_matrix
            elif opcode == 0x18:
                self.state.default_matrix = self.state.matrix
            elif opcode == 0x19:
                self.transform_stack.append(self.state.matrix)
            elif opcode == 0x1a:
                need(self.transform_stack, "GString transform stack underflow")
                self.state.matrix = self.transform_stack.pop()
            elif opcode == 0x20:
                points = self.points(raw, 1, 2); self._shape(points, False)
                self.state.current = (s16(raw, 5), s16(raw, 7))
            elif opcode == 0x21:
                target = (s16(raw, 1), s16(raw, 3))
                self._shape([self.point(self.state.current), self.point(target)], False)
                self.state.current = target
            elif opcode == 0x22:
                target = (self.state.current[0] + fixed_16_16(raw, 1),
                          self.state.current[1] + fixed_16_16(raw, 5))
                self._shape([self.point(self.state.current), self.point(target)], False)
                self.state.current = target
            elif opcode in (0x23, 0x25):
                first, second, third = struct.unpack_from("<3h", raw, 1)
                points = ([(first, second), (third, second)] if opcode == 0x23 else
                          [(first, second), (first, third)])
                self._shape([self.point(point) for point in points], False)
                self.state.current = points[-1]
            elif opcode in (0x24, 0x26):
                value = s16(raw, 1)
                target = ((value, self.state.current[1]) if opcode == 0x24 else
                          (self.state.current[0], value))
                self._shape([self.point(self.state.current), self.point(target)], False)
                self.state.current = target
            elif opcode in (0x27, 0x30, 0x31, 0x36, 0x39):
                count = u16(raw, 1)
                offset = 5 if opcode == 0x39 else 3
                source = self._raw_points(raw, offset, count)
                if opcode == 0x31:
                    source.insert(0, self.state.current)
                self._shape([self.point(point) for point in source], False,
                            closed=opcode == 0x36,
                            width=max(raw[3], raw[4]) if opcode == 0x39 else None)
                if source:
                    self.state.current = source[-1]
            elif opcode in (0x28, 0x46):
                close = raw[1]
                bounds = tuple(struct.unpack_from("<4h", raw, 2))
                start, end = struct.unpack_from("<2h", raw, 10)
                points = self._ellipse_points(bounds, start, end)
                if close == 1:
                    left, top, right, bottom = bounds
                    points.append(self.point(((left + right) / 2, (top + bottom) / 2)))
                self._shape(points, opcode == 0x46, closed=close != 0)
            elif opcode in (0x29, 0x2a, 0x2b, 0x4a, 0x4b):
                # Three-point arc records contain fixed-point endpoints and an
                # ArcCloseType.  A polyline through the defining points is a
                # stable raster approximation at help-viewer resolutions.
                values = [s16(raw, offset) for offset in range(3, len(raw) - 1, 2)]
                points = [self.point((values[pos], values[pos + 1]))
                          for pos in range(0, len(values) - 1, 2)]
                self._shape(points, opcode in (0x4a, 0x4b), closed=raw[1] != 0)
            elif opcode in (0x2c, 0x42):
                self._rectangle(raw, 1, opcode == 0x42)
            elif opcode in (0x2d, 0x43):
                target = (s16(raw, 1), s16(raw, 3))
                temporary = bytes((opcode,)) + struct.pack("<4h", *self.state.current, *target)
                self._rectangle(temporary, 1, opcode == 0x43)
                self.state.current = target
            elif opcode in (0x2e, 0x44):
                radius = u16(raw, 1); self._rectangle(raw, 3, opcode == 0x44, radius)
            elif opcode in (0x2f, 0x45):
                radius = u16(raw, 1); target = (s16(raw, 3), s16(raw, 5))
                temporary = b"\0" + struct.pack("<4h", *self.state.current, *target)
                self._rectangle(temporary, 1, opcode == 0x45, radius)
                self.state.current = target
            elif opcode == 0x32:
                values = struct.unpack_from("<8h", raw, 1)
                self._curve([(values[pos], values[pos + 1]) for pos in range(0, 8, 2)])
            elif opcode in (0x33, 0x34):
                values = list(struct.unpack_from("<6h", raw, 1))
                points = [(values[pos], values[pos + 1]) for pos in range(0, 6, 2)]
                if opcode == 0x34:
                    points = [(self.state.current[0] + point[0],
                               self.state.current[1] + point[1]) for point in points]
                self._curve([self.state.current] + points)
            elif opcode in (0x35, 0x48):
                bounds = tuple(struct.unpack_from("<4h", raw, 1))
                self._shape(self._ellipse_points(bounds), opcode == 0x48, True)
            elif opcode == 0x37:
                point = (s16(raw, 1), s16(raw, 3)); self._shape([self.point(point)], False)
                self.state.current = point
            elif opcode == 0x38:
                self._shape([self.point(self.state.current)], False)
            elif opcode == 0x3a:
                self._draw_text(raw[1:2], (s16(raw, 2), s16(raw, 4)))
            elif opcode == 0x3b:
                self._draw_text(raw[1:2])
            elif opcode == 0x3c:
                self._draw_text(command.fields["text"], (s16(raw, 1), s16(raw, 3)))
            elif opcode == 0x3d:
                self._draw_text(command.fields["text"])
            elif opcode == 0x3e:
                position = (wb_fixed(raw, 3), wb_fixed(raw, 6))
                for text_attr, text in command.fields["text_runs"]:
                    self._draw_text(text, position, text_attr)
                    position = self.state.current
            elif opcode == 0x41:
                need(self.state.path is not None, "GR_DRAW_PATH without a path")
                path = self.state.path; self.state.path = None
                for points in path:
                    self._shape(points, False)
                self.state.path = path
            elif opcode == 0x47:
                self._shape(self.points(raw, 4, u16(raw, 1)), True, True)
            elif opcode == 0x49:
                need(self.state.path is not None, "GR_FILL_PATH without a path")
                path = self.state.path; self.state.path = None
                for points in path:
                    self._shape(points, True, True)
                self.state.path = path
            elif opcode in (0x4c, 0x4d, 0x50, 0x51):
                parts = [command.fields["bitmap"]]
                while index + 1 < len(commands) and commands[index + 1].opcode == 0x54:
                    index += 1
                    parts.append(commands[index].fields["bitmap"])
                position = ((command.fields["x"], command.fields["y"])
                            if opcode in (0x4c, 0x50) else self.state.current)
                self._draw_bitmap(parts, opcode in (0x4c, 0x4d), position)
            elif opcode == 0x54:
                raise FormatError("orphan GString bitmap slice")
            elif opcode == 0x60:
                self.stack.append(copy.copy(self.state))
                self.state.path = copy.deepcopy(self.state.path)
                self.state.clip = self.state.clip.copy() if self.state.clip else None
            elif opcode == 0x61:
                need(self.stack, "GString state stack underflow")
                self.state = self.stack.pop()
            elif opcode == 0x62:
                need(raw[1] <= 7, "invalid GString mix mode")
                self.state.mix_mode = raw[1]
            elif opcode == 0x63:
                self.state.current = (s16(raw, 1), s16(raw, 3))
            elif opcode == 0x64:
                self.state.current = (self.state.current[0] + fixed_16_16(raw, 1),
                                      self.state.current[1] + fixed_16_16(raw, 5))
            elif opcode in (0x65, 0x66, 0x67, 0x68):
                pass  # palette bookkeeping; serialized bitmaps carry their palette
            elif opcode == 0x69:
                self.state.line_color = tuple(raw[1:4])
            elif opcode == 0x6a:
                _draw_mask_alpha(raw[1]); self.state.line_mask = raw[1]
            elif opcode == 0x6b:
                need(raw[1] in (0, 1, 0x80, 0x81), "invalid line color-map mode")
            elif opcode == 0x6c:
                self.state.line_width = fixed_16_16(raw, 1)
                need(self.state.line_width >= 0, "negative line width")
            elif opcode == 0x6d:
                need(raw[1] <= 2, "invalid line join"); self.state.line_join = raw[1]
            elif opcode == 0x6e:
                need(raw[1] <= 2, "invalid line end"); self.state.line_end = raw[1]
            elif opcode == 0x6f:
                self.state.line_color = gstring_color(raw, 1)
                self.state.line_mask = raw[5]; _draw_mask_alpha(raw[5])
                need(raw[6] in (0, 1, 0x80, 0x81), "invalid line map mode")
                need(raw[7] <= 2 and raw[8] <= 2 and raw[9] <= 5,
                     "invalid combined line attributes")
                self.state.line_end, self.state.line_join, self.state.line_style = raw[7:10]
                self.state.line_width = fixed_16_16(raw, 10)
            elif opcode == 0x70:
                need(fixed_16_16(raw, 1) >= 0, "negative miter limit")
            elif opcode == 0x71:
                need(raw[1] <= 5, "invalid line style"); self.state.line_style = raw[1]
            elif opcode == 0x72:
                self.state.line_color = GEOS_PALETTE[raw[1]]
            elif opcode in (0x73, 0x74):
                pass  # custom masks/styles are fully consumed by the parser
            elif opcode == 0x75:
                self.state.area_color = tuple(raw[1:4])
            elif opcode == 0x76:
                _draw_mask_alpha(raw[1]); self.state.area_mask = raw[1]
            elif opcode == 0x77:
                need(raw[1] in (0, 1, 0x80, 0x81), "invalid area color-map mode")
            elif opcode == 0x78:
                self.state.area_color = gstring_color(raw, 1)
                self.state.area_mask = raw[5]; _draw_mask_alpha(raw[5])
                need(raw[6] in (0, 1, 0x80, 0x81), "invalid area map mode")
            elif opcode == 0x79:
                self.state.area_color = GEOS_PALETTE[raw[1]]
            elif opcode in (0x7a, 0x7b, 0x7c):
                pass  # custom/system area patterns affect texture, not geometry
            elif opcode == 0x7d:
                self.state.text_color = tuple(raw[1:4])
            elif opcode == 0x7e:
                _draw_mask_alpha(raw[1]); self.state.text_mask = raw[1]
            elif opcode == 0x7f:
                need(raw[1] in (0, 1, 0x80, 0x81), "invalid text color-map mode")
            elif opcode == 0x80:
                self.state.text_styles = ((self.state.text_styles | raw[1]) & ~raw[2])
            elif opcode == 0x81:
                self.state.text_mode = ((self.state.text_mode | raw[1]) & ~raw[2])
            elif opcode == 0x82:
                pass
            elif opcode == 0x83:
                self.state.text_color = color_quad(raw, 1)
                self.state.text_mask = raw[5]
                self.state.text_styles = ((self.state.text_styles | raw[8]) & ~raw[9])
                self.state.text_mode = ((self.state.text_mode | raw[10]) & ~raw[11])
                self.state.font_id = u16(raw, 15)
                self.state.point_size = wb_fixed(raw, 17)
            elif opcode == 0x84:
                self.state.point_size = wb_fixed(raw, 1); self.state.font_id = u16(raw, 4)
            elif opcode == 0x85:
                self.state.text_color = GEOS_PALETTE[raw[1]]
            elif opcode in (0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d):
                pass
            elif opcode == 0x8e:
                self.state.current = (fixed_16_16(raw, 1), fixed_16_16(raw, 5))
            elif opcode == 0x8f:
                need(raw[1] in (0, 1), "invalid text direction")
            elif opcode == 0xa0:
                need(self.state.path is None and u16(raw, 1) <= 3, "invalid GR_BEGIN_PATH")
                self.state.path = []
            elif opcode == 0xa1:
                need(self.state.path is not None, "GR_END_PATH without a path")
            elif opcode in (0xa2, 0xa3):
                combine = u16(raw, 1)
                points = self.points(raw, 3, 2)
                mask = Image.new("L", self.canvas.size, 0)
                ImageDraw.Draw(mask).rectangle((points[0], points[1]), fill=255)
                self._set_clip(mask, combine)
            elif opcode == 0xa4:
                need(self.state.path is not None and self.state.path,
                     "GR_CLOSE_SUB_PATH without a path")
                path = self.state.path[-1]
                if path and path[-1] != path[0]: path.append(path[0])
            elif opcode in (0xa5, 0xa6):
                need(self.state.path is not None and raw[1] in (0, 1),
                     "clip-path operation without a path")
                mask = Image.new("L", self.canvas.size, 0)
                draw = ImageDraw.Draw(mask)
                for points in self.state.path: draw.polygon(points, fill=255)
                self._set_clip(mask, u16(raw, 2))
                self.state.path = None
            elif opcode == 0xa7:
                need(self.state.path is not None, "GR_SET_STROKE_PATH without a path")
            else:
                raise FormatError(f"unimplemented GString opcode {opcode:#04x}")
            index += 1
        need(not self.stack and not self.transform_stack, "unbalanced GString state stack")
        return self.canvas


# ---------------------------------------------------------------------------
# VisText layout and PDF serialization


@dataclass
class LayoutUnit:
    kind: str
    width: float
    ascent: float
    descent: float
    text: str = ""
    font: object | None = None
    color: tuple[int, int, int] = (0, 0, 0)
    background: tuple[int, int, int] | None = None
    styles: int = 0
    extended_styles: int = 0
    image: object | None = None


@dataclass
class LayoutLine:
    units: list[LayoutUnit]
    width: float
    ascent: float
    descent: float
    last_in_paragraph: bool = False


def resolved_run_tokens(run_array: RunArray, length: int) -> list[int]:
    """Apply serialized run changes in storage order.

    VisText run chunks are mutation logs as well as lookup tables.  A later
    fragment is authoritative even when an old writer appended a fragment
    whose start precedes a prior fragment.
    """
    tokens = [run_array.runs[0].token] * max(1, length)
    for run in run_array.runs[:-1]:
        if run.position < length:
            tokens[run.position:] = [run.token] * (length - run.position)
    return tokens


def dos_datetime(date_word: int, time_word: int) -> datetime.datetime:
    year = 1980 + ((date_word >> 9) & 0x7f)
    month = (date_word >> 5) & 15
    day = date_word & 31
    hour = (time_word >> 11) & 31
    minute = (time_word >> 5) & 63
    second = (time_word & 31) * 2
    try:
        return datetime.datetime(year, month, day, hour, minute, second)
    except ValueError as error:
        raise FormatError("invalid FileDateAndTime in GEOS header") from error


def ordinal(number: int) -> str:
    suffix = "th" if 10 <= number % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(
        number % 10, "th")
    return f"{number}{suffix}"


def format_geos_datetime(value: datetime.datetime, format_id: int) -> str:
    """Render the locale-independent English form of DateTimeFormat."""
    month = value.strftime("%B")
    month_short = value.strftime("%b")
    weekday = value.strftime("%A")
    weekday_short = value.strftime("%a")
    year_short = value.year % 100
    date_formats = {
        0: f"{weekday}, {month} {ordinal(value.day)}, {value.year}",
        1: f"{weekday_short}, {month_short} {value.day}, {value.year}",
        2: f"{month} {ordinal(value.day)}, {value.year}",
        3: f"{month_short} {value.day}, {value.year}",
        4: f"{value.month}/{value.day}/{year_short}",
        5: f"{value.month:02d}/{value.day:02d}/{year_short:02d}",
        6: f"{weekday}, {month} {ordinal(value.day)}",
        7: f"{month} {ordinal(value.day)}",
        8: f"{value.month}/{value.day}",
        9: f"{month} {value.year}",
        10: f"{value.month}/{year_short}",
        11: str(value.year),
        12: month,
        13: ordinal(value.day),
        14: weekday,
    }
    if format_id in date_formats:
        return date_formats[format_id]
    hour = value.hour % 12 or 12
    marker = "AM" if value.hour < 12 else "PM"
    time_formats = {
        15: f"{hour}:{value.minute:02d}:{value.second:02d} {marker}",
        16: f"{hour}:{value.minute:02d} {marker}",
        17: f"{hour} {marker}",
        18: f"{value.minute}:{value.second:02d}",
        19: f"{value.hour:02d}:{value.minute:02d}:{value.second:02d}",
        20: f"{value.hour:02d}:{value.minute:02d}",
    }
    need(format_id in time_formats, "invalid DateTimeFormat in variable graphic")
    return time_formats[format_id]


class HelpPageRenderer:
    SCALE = 96.0 / 72.0
    PAGE_POINTS = (612, 792)
    PAGE_PIXELS = (816, 1056)
    MARGIN = 48
    CONTENT_BOTTOM = 1008

    def __init__(self, document: HelpDocument, modified: datetime.datetime):
        need(Image is not None and ImageDraw is not None,
             "Pillow is required for PDF rendering")
        self.document = document
        self.modified = modified
        self.created = dos_datetime(int(document.vm.common["created_date"]),
                                    int(document.vm.common["created_time"]))
        self.fonts = FontCache()
        self.graphic_cache: dict[int, object] = {}
        self.pages: list[object] = []
        self.canvas = None
        self.draw = None
        self.y = 0.0
        self.context = ""
        self.continuation = 0
        self.name_by_token = {name.token: name for name in document.names}

    @staticmethod
    def _name(name: NameElement) -> str:
        return "".join(geos_character(byte) for byte in name.name_bytes)

    def _new_page(self, continuation: bool = False) -> None:
        self.canvas = Image.new("RGB", self.PAGE_PIXELS, (255, 255, 255))
        self.draw = ImageDraw.Draw(self.canvas)
        header_font = self.fonts.get(0x1200, 9 * self.SCALE, False, False)
        label = self.context + ("  (continued)" if continuation else "")
        self.draw.text((self.MARGIN, 22), label, font=header_font, fill=(90, 98, 108))
        self.draw.line((self.MARGIN, 43, self.PAGE_PIXELS[0] - self.MARGIN, 43),
                       fill=(205, 210, 216), width=1)
        self.y = 58.0
        self.pages.append(self.canvas)

    def _run_attr(self, tokens: list[int], position: int) -> CharAttr:
        return self.document.char_attrs[tokens[min(position, len(tokens) - 1)]]

    def _variable_text(self, attr: GraphicAttr) -> str:
        variable_type = u16(attr.opaque, 2)
        private = attr.opaque[4:]
        if variable_type in (6, 7):
            value = self.created if variable_type == 6 else self.modified
            return format_geos_datetime(value, u16(private))
        if variable_type == 13:
            token = u16(private, 2)
            name = self.name_by_token.get(token)
            need(name is not None, "context-name variable references a missing name")
            return self._name(name)
        # These values are fully defined by the file format, but require page
        # or section state that Help documents do not otherwise serialize.
        number_type = u16(private)
        need(number_type <= 4, "invalid VisTextNumberType in variable graphic")
        if variable_type == 0:
            return "1"
        if variable_type == 1:
            return "1"
        if variable_type == 2:
            return str(len(self.document.pages))
        if variable_type == 3:
            return str(len(self.document.pages))
        if variable_type in (4, 5):
            return "1"
        if variable_type in (10, 11, 12):
            return "1"
        if variable_type in (8, 9):
            return format_geos_datetime(datetime.datetime.now().astimezone().replace(tzinfo=None),
                                        u16(private))
        if variable_type == 14:
            return ""
        raise FormatError("unsupported variable graphic type")

    @staticmethod
    def _masked_color(color: tuple[int, int, int], mask: int) -> tuple[int, int, int]:
        alpha = _draw_mask_alpha(mask)
        return tuple(round(component * alpha / 255 + 255 * (255 - alpha) / 255)
                     for component in color)

    def _text_unit(self, character: str, attr: CharAttr) -> LayoutUnit:
        styles = attr.text_styles
        extended = attr.extended_styles
        if extended & 0x0400:  # VTES_HIDDEN
            return LayoutUnit("text", 0, 0, 0)
        if extended & 0x1000:  # VTES_ALL_CAP
            character = character.upper()
        small_cap = bool(extended & 0x0800 and character.islower())
        if small_cap:
            character = character.upper()
        size = attr.point_size * (0.78 if small_cap else 1.0)
        if styles & 0x0c:  # superscript or subscript
            size *= 0.65
        bold = bool(styles & 0x20 or attr.font_weight >= 115)
        italic = bool(styles & 0x10)
        font = self.fonts.get(attr.font_id, size * self.SCALE, bold, italic)
        ascent, descent = font.getmetrics()
        width = self.draw.textlength(character, font=font)
        width *= max(0.25, attr.font_width / 100.0)
        width += size * self.SCALE * attr.track_kerning / 1000.0
        background = None
        if extended & 0x0100:
            background = self._masked_color(attr.background, attr.background_gray)
        return LayoutUnit("text", max(0, width), ascent, descent,
                          character, font,
                          self._masked_color(attr.foreground, attr.gray_screen),
                          background, styles, extended)

    def _graphic_unit(self, attr: GraphicAttr, char_attr: CharAttr) -> list[LayoutUnit]:
        if attr.graphic_type == 1:
            return [self._text_unit(character, char_attr)
                    for character in self._variable_text(attr)]
        if attr.token not in self.graphic_cache:
            self.graphic_cache[attr.token] = GStringRenderer(
                self.document, attr, self.fonts).render()
        image = self.graphic_cache[attr.token]
        return [LayoutUnit("image", float(image.width), float(image.height), 0,
                           image=image)]

    def _make_units(self, page: HelpPage, start: int, end: int,
                    char_tokens: list[int], graphic_tokens: dict[int, int]) -> list[LayoutUnit]:
        result: list[LayoutUnit] = []
        for position in range(start, end):
            value = page.text_bytes[position]
            attr = self._run_attr(char_tokens, position)
            if value == 0x1a:  # C_GRAPHIC
                need(position in graphic_tokens,
                     "C_GRAPHIC has no graphic-run element")
                result.extend(self._graphic_unit(
                    self.document.graphic_attrs[graphic_tokens[position]], attr))
            elif value == 0x09:
                result.append(LayoutUnit("tab", 0, attr.point_size * self.SCALE,
                                         attr.point_size * self.SCALE * 0.25))
            elif value == 0x19:  # C_NULL_WIDTH
                continue
            elif value == 0x1f:  # optional hyphen: a legal zero-width break
                result.append(LayoutUnit("soft_hyphen", 0, 0, 0))
            elif value >= 0x20 or value in (0x1b, 0x1c, 0x1d, 0x1e):
                result.append(self._text_unit(geos_character(value), attr))
            else:
                raise FormatError(f"unsupported VisText control character {value:#04x}")
        return result

    def _tab_width(self, x: float, para: ParaAttr) -> float:
        point_x = x / self.SCALE
        for tab in para.tabs:
            stop = tab.position / 8.0
            if stop > point_x + 0.01:
                return (stop - point_x) * self.SCALE
        interval = u16(para.raw, 41) / 8.0 or 18.0
        stop = (math.floor(point_x / interval) + 1) * interval
        return max(self.SCALE, (stop - point_x) * self.SCALE)

    def _layout_lines(self, units: list[LayoutUnit], para: ParaAttr,
                      first_width: float, other_width: float) -> list[LayoutLine]:
        raw = para.raw
        disable_wrap = bool(u16(raw, 11) & 0x0400)
        lines: list[LayoutLine] = []
        current: list[LayoutUnit] = []
        width = 0.0
        last_break = -1
        index = 0

        def finish(split: int | None = None) -> None:
            nonlocal current, width, last_break
            carry: list[LayoutUnit] = []
            if split is not None:
                carry = current[split:]
                current = current[:split]
            while current and current[-1].kind == "text" and current[-1].text == " ":
                current.pop()
            line_width = sum(unit.width for unit in current)
            ascent = max((unit.ascent for unit in current), default=12 * self.SCALE)
            descent = max((unit.descent for unit in current), default=3 * self.SCALE)
            lines.append(LayoutLine(current, line_width, ascent, descent))
            current = carry
            while current and current[0].kind == "text" and current[0].text == " ":
                current.pop(0)
            width = sum(unit.width for unit in current)
            last_break = -1
            for pos, unit in enumerate(current):
                if unit.kind in ("tab", "soft_hyphen") or (unit.kind == "text" and unit.text == " "):
                    last_break = pos + 1

        while index < len(units):
            unit = units[index]
            allowed = first_width if not lines else other_width
            if unit.kind == "tab":
                unit.width = self._tab_width(width, para)
            if not disable_wrap and current and width + unit.width > allowed:
                finish(last_break if last_break > 0 else None)
                continue
            current.append(unit)
            width += unit.width
            if unit.kind in ("tab", "soft_hyphen") or (unit.kind == "text" and unit.text == " "):
                last_break = len(current)
            index += 1
        if current or not lines:
            finish()
        lines[-1].last_in_paragraph = True
        return lines

    def _draw_line(self, line: LayoutLine, para: ParaAttr, left: float,
                   available: float, y: float, line_height: float) -> None:
        justification = u16(para.raw, 11) >> 14
        extra_per_space = 0.0
        if justification == 1:
            x = left + max(0, available - line.width)
        elif justification == 2:
            x = left + max(0, (available - line.width) / 2)
        else:
            x = left
            if justification == 3 and not line.last_in_paragraph:
                spaces = sum(unit.kind == "text" and unit.text == " " for unit in line.units)
                if spaces:
                    extra_per_space = max(0, available - line.width) / spaces
        baseline = y + line.ascent
        for unit in line.units:
            if unit.background is not None and unit.width:
                self.draw.rectangle((x, y, x + unit.width, y + line_height),
                                    fill=unit.background)
            if unit.kind == "text" and unit.text:
                text_y = baseline - unit.ascent
                if unit.styles & 0x08:
                    text_y -= unit.ascent * 0.35
                elif unit.styles & 0x04:
                    text_y += unit.ascent * 0.30
                self.draw.text((x, text_y), unit.text, font=unit.font, fill=unit.color,
                               stroke_width=1 if unit.styles & 0x40 else 0,
                               stroke_fill=unit.color)
                if unit.styles & 0x01:
                    self.draw.line((x, baseline + 1, x + unit.width, baseline + 1),
                                   fill=unit.color, width=1)
                if unit.styles & 0x02:
                    strike = baseline - unit.ascent * 0.35
                    self.draw.line((x, strike, x + unit.width, strike),
                                   fill=unit.color, width=1)
                if unit.extended_styles & (0x8000 | 0x4000):
                    self.draw.rectangle((x, y, x + unit.width, y + line_height - 1),
                                        outline=unit.color, width=1)
            elif unit.kind == "image" and unit.image is not None:
                image_y = y + max(0, (line_height - unit.image.height) / 2)
                self.canvas.paste(unit.image, (round(x), round(image_y)), unit.image)
            x += unit.width
            if unit.kind == "text" and unit.text == " ":
                x += extra_per_space

    def _render_paragraph(self, page: HelpPage, start: int, end: int,
                          para: ParaAttr, units: list[LayoutUnit]) -> None:
        raw = para.raw
        left_margin = u16(raw, 13) / 8.0 * self.SCALE
        right_margin = u16(raw, 15) / 8.0 * self.SCALE
        para_margin = u16(raw, 17) / 8.0 * self.SCALE
        base_left = self.MARGIN
        right = self.PAGE_PIXELS[0] - self.MARGIN - right_margin
        first_left = base_left + para_margin
        other_left = base_left + left_margin
        first_width = max(1, right - first_left)
        other_width = max(1, right - other_left)
        lines = self._layout_lines(units, para, first_width, other_width)
        top_space = u16(raw, 23) / 8.0 * self.SCALE
        bottom_space = u16(raw, 25) / 8.0 * self.SCALE
        leading = u16(raw, 21) / 8.0 * self.SCALE
        spacing = u16(raw, 19) / 256.0 or 1.0
        self.y += top_space
        bg_alpha = _draw_mask_alpha(raw[36])
        bg_color = color_quad(raw, 27)
        bg_fill = tuple(round(component * bg_alpha / 255 + 255 * (255 - bg_alpha) / 255)
                        for component in bg_color)
        border_flags = u16(raw, 5)
        border_color = color_quad(raw, 7)
        border_width = max(1, round(raw[32] / 8.0 * self.SCALE))
        for line_index, line in enumerate(lines):
            height = max(line.ascent + line.descent, max(
                (unit.ascent + unit.descent for unit in line.units if unit.kind == "image"),
                default=0))
            height = max(1, height * spacing + leading)
            if self.y + height > self.CONTENT_BOTTOM:
                self._new_page(True)
            left = first_left if line_index == 0 else other_left
            available = first_width if line_index == 0 else other_width
            if bg_alpha:
                self.draw.rectangle((base_left, self.y, right, self.y + height), fill=bg_fill)
            if border_flags & 0x8000:
                self.draw.line((base_left, self.y, base_left, self.y + height),
                               fill=border_color, width=border_width)
            if border_flags & 0x2000:
                self.draw.line((right, self.y, right, self.y + height),
                               fill=border_color, width=border_width)
            if border_flags & 0x4000 and line_index == 0:
                self.draw.line((base_left, self.y, right, self.y),
                               fill=border_color, width=border_width)
            if border_flags & 0x1000 and line.last_in_paragraph:
                self.draw.line((base_left, self.y + height, right, self.y + height),
                               fill=border_color, width=border_width)
            self._draw_line(line, para, left, available, self.y, height)
            self.y += height
        self.y += bottom_space

    def render(self) -> list[object]:
        for page in self.document.pages:
            self.context = self._name(page.name)
            self._new_page(False)
            length = len(page.text_bytes)
            char_tokens = resolved_run_tokens(page.char_runs, length)
            para_tokens = resolved_run_tokens(page.para_runs, length)
            graphic_tokens: dict[int, int] = {}
            for run in page.graphic_runs.runs[:-1]:
                graphic_tokens[run.position] = run.token
            graphic_characters = {index for index, value in enumerate(page.text_bytes)
                                  if value == 0x1a}
            need(graphic_characters == set(graphic_tokens),
                 "graphic runs and C_GRAPHIC characters disagree")
            start = 0
            for position in range(length + 1):
                separator = page.text_bytes[position] if position < length else 0x0d
                if separator not in (0x0b, 0x0c, 0x0d):
                    continue
                para_token = para_tokens[min(start, max(0, length - 1))]
                para = self.document.para_attrs[para_token]
                units = self._make_units(page, start, position, char_tokens, graphic_tokens)
                self._render_paragraph(page, start, position, para, units)
                start = position + 1
                if separator in (0x0b, 0x0c) and position + 1 < length:
                    self._new_page(True)
        need(self.pages, "Help document contains no renderable pages")
        return self.pages


def pdf_bytes(images: list[object], title: str) -> bytes:
    """Build a PDF 1.4 file containing lossless RGB page images."""
    need(images, "cannot create an empty PDF")
    objects: list[bytes] = []

    def reserve() -> int:
        objects.append(b"")
        return len(objects)

    catalog = reserve()
    pages_object = reserve()
    info_object = reserve()
    page_objects: list[int] = []
    for index, image in enumerate(images):
        rgb = image.convert("RGB")
        compressed = zlib.compress(rgb.tobytes(), 9)
        image_object = reserve()
        content_object = reserve()
        page_object = reserve()
        name = f"Im{index + 1}"
        objects[image_object - 1] = (
            f"<< /Type /XObject /Subtype /Image /Width {rgb.width} /Height {rgb.height} "
            f"/ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /FlateDecode "
            f"/Length {len(compressed)} >>\nstream\n".encode("ascii") + compressed +
            b"\nendstream")
        content = f"q 612 0 0 792 0 0 cm /{name} Do Q\n".encode("ascii")
        objects[content_object - 1] = (f"<< /Length {len(content)} >>\nstream\n".encode(
            "ascii") + content + b"endstream")
        objects[page_object - 1] = (
            f"<< /Type /Page /Parent {pages_object} 0 R /MediaBox [0 0 612 792] "
            f"/Resources << /XObject << /{name} {image_object} 0 R >> >> "
            f"/Contents {content_object} 0 R >>".encode("ascii"))
        page_objects.append(page_object)
    kids = " ".join(f"{number} 0 R" for number in page_objects)
    objects[pages_object - 1] = (
        f"<< /Type /Pages /Count {len(page_objects)} /Kids [{kids}] >>".encode("ascii"))
    objects[catalog - 1] = f"<< /Type /Catalog /Pages {pages_object} 0 R >>".encode("ascii")
    escaped_title = title.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
    objects[info_object - 1] = (
        f"<< /Title ({escaped_title}) /Creator (geoWorksGEOSHelp.py) >>".encode(
            "latin-1", "replace"))
    output = io.BytesIO()
    output.write(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offsets = [0]
    for number, body in enumerate(objects, 1):
        offsets.append(output.tell())
        output.write(f"{number} 0 obj\n".encode("ascii"))
        output.write(body)
        output.write(b"\nendobj\n")
    xref = output.tell()
    output.write(f"xref\n0 {len(objects) + 1}\n".encode("ascii"))
    output.write(b"0000000000 65535 f \n")
    for offset in offsets[1:]:
        output.write(f"{offset:010d} 00000 n \n".encode("ascii"))
    output.write((f"trailer\n<< /Size {len(objects) + 1} /Root {catalog} 0 R "
                  f"/Info {info_object} 0 R >>\nstartxref\n{xref}\n%%EOF\n").encode("ascii"))
    return output.getvalue()


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(f"usage: {Path(argv[0]).name} <inputFile> <outputFile>", file=sys.stderr)
        return 2
    source = Path(argv[1])
    destination = Path(argv[2])
    temporary: str | None = None
    try:
        need(source.resolve() != destination.resolve(),
             "input and output paths must be different")
        source_stat = source.stat()
        document = HelpDocument(source.read_bytes())
        modified = datetime.datetime.fromtimestamp(source_stat.st_mtime).astimezone().replace(
            tzinfo=None)
        images = HelpPageRenderer(document, modified).render()
        title = str(document.vm.common["long_name"].split(b"\0", 1)[0].decode(
            "mac_roman", "replace"))
        result = pdf_bytes(images, title)
        need(destination.parent.is_dir(), "output directory does not exist")
        descriptor, temporary = tempfile.mkstemp(
            prefix=f".{destination.name}.", suffix=".tmp", dir=destination.parent)
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(result)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, 0o664)
        os.replace(temporary, destination)
        temporary = None
    except (OSError, FormatError) as error:
        print(f"{source}: {error}", file=sys.stderr)
        return 1
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary)
            except OSError:
                pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

#!/usr/bin/env python3
# Vibe coded by Codex
"""Strict GeoWrite 1.x/protocol-1 and 2.x/protocol-3 to PDF converter."""

from __future__ import annotations

import html
import math
import os
import pathlib
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from typing import Iterable, Sequence

try:
    import cairo
except ImportError as exc:  # pragma: no cover - depends on the host installation
    raise SystemExit("geoWorksGeoWriteDocument.py: Pycairo is required") from exc


class FormatError(Exception):
    """The input is not the precisely supported GeoWrite format."""


def fail(message: str) -> None:
    raise FormatError(message)


def need(data: bytes, offset: int, size: int, what: str) -> None:
    if offset < 0 or size < 0 or offset + size > len(data):
        fail(f"truncated {what} at 0x{offset:x}")


def u8(data: bytes, offset: int) -> int:
    need(data, offset, 1, "byte")
    return data[offset]


def u16(data: bytes, offset: int) -> int:
    need(data, offset, 2, "word")
    return struct.unpack_from("<H", data, offset)[0]


def s16(data: bytes, offset: int) -> int:
    need(data, offset, 2, "signed word")
    return struct.unpack_from("<h", data, offset)[0]


def u24(data: bytes, offset: int) -> int:
    need(data, offset, 3, "24-bit value")
    return data[offset] | (data[offset + 1] << 8) | (data[offset + 2] << 16)


def u32(data: bytes, offset: int) -> int:
    need(data, offset, 4, "dword")
    return struct.unpack_from("<I", data, offset)[0]


def s32(data: bytes, offset: int) -> int:
    need(data, offset, 4, "signed dword")
    return struct.unpack_from("<i", data, offset)[0]


def wbfixed(data: bytes, offset: int) -> float:
    """Decode GEOS WBFixed (fraction byte followed by integer word)."""
    need(data, offset, 3, "WBFixed")
    return u16(data, offset + 1) + data[offset] / 256.0


def swbfixed(data: bytes, offset: int) -> float:
    """Decode a signed GEOS WBFixed coordinate."""
    need(data, offset, 3, "signed WBFixed")
    return s16(data, offset + 1) + data[offset] / 256.0


def wwfixed(data: bytes, offset: int) -> float:
    """Decode a signed GEOS WWFixed (16.16, fraction word first)."""
    need(data, offset, 4, "WWFixed")
    return struct.unpack_from("<i", data, offset)[0] / 65536.0


def dwfixed(data: bytes, offset: int) -> float:
    """Decode a signed GEOS DWFixed (32.16, fraction word first)."""
    need(data, offset, 6, "DWFixed")
    integer = s32(data, offset + 2)
    return integer + u16(data, offset) / 65536.0


def decode_geos(raw: bytes) -> str:
    """Decode the SBCS PC/GEOS character set (the Macintosh Roman table)."""
    return raw.decode("mac_roman", errors="strict")


def decoded_c_string(raw: bytes) -> str:
    return decode_geos(raw.split(b"\0", 1)[0])


@dataclass(frozen=True)
class VMBlock:
    handle: int
    flags: int
    uid: int
    position: int
    data: bytes


class VMFile:
    """Validated old or current PC/GEOS VM container."""

    HEADER_SIZE = 256
    VM_FILE_HEADER_SIZE = 24

    def __init__(self, raw: bytes):
        self.raw = raw
        self.blocks: dict[int, VMBlock] = {}
        self.long_name = ""
        self.release = (0, 0, 0, 0)
        self.protocol = (0, 0)
        self.map_handle = 0
        self.db_map_handle = 0
        self.legacy = False
        self._parse()

    def _parse(self) -> None:
        d = self.raw
        need(d, 0, 4, "GEOS signature")
        if d[0:4] == b"\xc7E\xc1S":
            header_size = self.HEADER_SIZE
            vm_file_header_size = self.VM_FILE_HEADER_SIZE
            position_bias = header_size
            need(d, 0, header_size + vm_file_header_size, "GEOS 2.x header")
            self.long_name = decoded_c_string(d[4:40])
            if u16(d, 40) != 2:
                fail("GEOS file is not a VM data file")
            header_flags = u16(d, 42)
            self.release = tuple(u16(d, 44 + i * 2) for i in range(4))
            self.protocol = (u16(d, 52), u16(d, 54))
            token_offset = 56
            creator_offset = 62
            expected_protocol = (3, 0)
            block_flag_mask = 0x1F
            compression_flag = 0x10
        elif d[0:4] == b"\xc7E\xcfS":
            self.legacy = True
            header_size = 200
            vm_file_header_size = 8
            position_bias = 0
            need(d, 0, header_size + vm_file_header_size, "GEOS 1.x header")
            if u16(d, 4) != 1:
                fail("old GEOS file is not a VM data file")
            header_flags = u16(d, 6)
            self.release = tuple(u16(d, 8 + i * 2) for i in range(4))
            self.protocol = (u16(d, 16), u16(d, 18))
            token_offset = 20
            creator_offset = 26
            self.long_name = decoded_c_string(d[32:68])
            expected_protocol = (1, 0)
            block_flag_mask = 0x07
            compression_flag = 0
        else:
            fail("not a recognized PC/GEOS file (bad GEOS signature)")
        if header_flags & ~0xEF00:
            fail("GEOS header contains unknown flag bits")
        if header_flags & 0x0400:
            fail("DBCS GeoWrite documents are not supported")
        if d[token_offset : token_offset + 4] != b"WDAT" or u16(d, token_offset + 4) != 0:
            fail("GEOS token is not WDAT/GeoWrite")
        if d[creator_offset : creator_offset + 4] != b"WP00" or u16(d, creator_offset + 4) != 0:
            fail("GEOS creator is not WP00/GeoWrite")
        if self.protocol != expected_protocol:
            fail(f"unsupported GeoWrite protocol {self.protocol[0]}.{self.protocol[1]}")

        ext = header_size
        if u16(d, ext) != 0xADEB:
            fail("bad VM-file signature")
        directory_size = u16(d, ext + 2)
        directory_pos = position_bias + u32(d, ext + 4)
        if not self.legacy:
            update_type = u16(d, ext + 10)
            if update_type > 6 and update_type < 0x8000:
                fail("invalid VM update operation")
        if directory_size < 44 or directory_size % 4:
            fail("invalid VM directory size")
        need(d, directory_pos, directory_size, "VM directory")
        directory = d[directory_pos : directory_pos + directory_size]
        if u16(directory, 0) != 0x00FB:
            fail("bad VM-directory signature")
        last_handle = u16(directory, 8)
        if last_handle > directory_size or last_handle < 44 or (last_handle - 32) % 12:
            fail("inconsistent VM handle table size")
        if any(directory[last_handle:]):
            fail("nonzero bytes follow the VM handle table")
        num_assigned = s16(directory, 10)
        num_unassigned = s16(directory, 12)
        num_used = s16(directory, 14)
        if min(num_assigned, num_unassigned, num_used) < 0:
            fail("negative VM block count")
        self.map_handle = u16(directory, 20)
        self.db_map_handle = u16(directory, 30)

        used_count = assigned_count = unassigned_count = 0
        physical_spans: list[tuple[int, int, str]] = []
        signatures: dict[int, int] = {}
        backup_targets: dict[int, int] = {}
        for handle in range(32, last_handle, 12):
            record = directory[handle : handle + 12]
            signature = record[2]
            signatures[handle] = signature
            if signature & 1:
                flags = record[3]
                uid = u16(record, 4)
                size = u16(record, 6)
                position = position_bias + u32(record, 8)
                if signature not in (0xF9, 0xFB, 0xFD, 0xFF):
                    fail(f"VM block 0x{handle:04x} has unknown block type 0x{signature:02x}")
                if flags & ~block_flag_mask:
                    fail(f"VM block 0x{handle:04x} has unknown flags")
                if not size:
                    fail(f"VM block 0x{handle:04x} has zero size")
                need(d, position, size, f"VM block 0x{handle:04x}")
                if compression_flag and flags & compression_flag:
                    fail(f"VM block 0x{handle:04x} uses unsupported LZG compression")
                block = VMBlock(handle, flags, uid, position, d[position : position + size])
                physical_spans.append((position, position + size, f"block 0x{handle:04x}"))
                if signature in (0xFD, 0xFF):
                    self.blocks[handle] = block
                    used_count += 1
                elif signature == 0xFB:
                    backup_targets[handle] = uid
            else:
                free_size = u32(record, 4)
                free_pos = position_bias + u32(record, 8)
                if free_size:
                    need(d, free_pos, free_size, f"assigned free area 0x{handle:04x}")
                    physical_spans.append((free_pos, free_pos + free_size, f"free area 0x{handle:04x}"))
                    assigned_count += 1
                else:
                    unassigned_count += 1

        if (used_count, assigned_count, unassigned_count) != (
            num_used,
            num_assigned,
            num_unassigned,
        ):
            fail("VM directory block counts do not match its handle records")
        for backup_handle, target_handle in backup_targets.items():
            if signatures.get(target_handle) != 0xFD:
                fail(f"backup VM block 0x{backup_handle:04x} does not identify a duplicate block")
            if not (self.blocks[target_handle].flags & 0x02):
                fail(f"duplicate VM block 0x{target_handle:04x} lacks its backup flag")
        if self.map_handle not in self.blocks:
            fail("VM map handle does not identify a used block")
        header_block = self.blocks.get(32)
        if (
            header_block is None
            or header_block.uid != 0xADEB
            or header_block.position != directory_pos
            or len(header_block.data) != directory_size
        ):
            fail("VM directory self-record is inconsistent")
        physical_spans.sort()
        for left, right in zip(physical_spans, physical_spans[1:]):
            if left[1] > right[0]:
                fail(f"overlapping VM storage: {left[2]} and {right[2]}")
        expected_position = header_size + vm_file_header_size
        for start, end, description in physical_spans:
            if start != expected_position:
                fail(f"unaccounted file bytes before {description} at 0x{start:x}")
            expected_position = end
        if expected_position != len(d):
            fail("unaccounted bytes follow the last VM storage extent")

    def block(self, handle: int, uid: int | None = None) -> VMBlock:
        try:
            result = self.blocks[handle]
        except KeyError:
            fail(f"invalid VM block handle 0x{handle:04x}")
        if uid is not None and result.uid != uid:
            fail(f"VM block 0x{handle:04x} has UID 0x{result.uid:04x}, expected 0x{uid:04x}")
        return result


class LMemBlock:
    """Validated GEOS local-memory heap and its chunk handles."""

    def __init__(self, vm_block: VMBlock, required_type: int | None = None):
        self.vm_block = vm_block
        self.data = vm_block.data
        need(self.data, 0, 16, "LMem header")
        self.handle_table = u16(self.data, 2)
        self.flags = u16(self.data, 4)
        self.kind = u16(self.data, 6)
        self.block_size = u16(self.data, 8)
        self.handle_count = u16(self.data, 10)
        self.free_list = u16(self.data, 12)
        self.total_free = u16(self.data, 14)
        if required_type is not None and self.kind != required_type:
            fail(f"VM block 0x{vm_block.handle:04x} has LMem type {self.kind}, expected {required_type}")
        if self.kind > 6:
            fail(f"VM block 0x{vm_block.handle:04x} has invalid LMem type {self.kind}")
        if self.block_size > len(self.data) or self.block_size < 16:
            fail(f"VM block 0x{vm_block.handle:04x} has invalid LMem size")
        need(self.data, self.handle_table, self.handle_count * 2, "LMem handle table")
        self.handles = [self.handle_table + 2 * i for i in range(self.handle_count)]
        allocations: list[tuple[int, int, int]] = []
        for chunk_handle in self.handles:
            pointer = u16(self.data, chunk_handle)
            if pointer in (0, 0xFFFF):
                continue
            if pointer < 2 or pointer > self.block_size:
                fail(f"invalid LMem chunk pointer at handle 0x{chunk_handle:04x}")
            allocation_size = u16(self.data, pointer - 2)
            if allocation_size < 2 or pointer - 2 + allocation_size > self.block_size:
                fail(f"invalid LMem chunk size at handle 0x{chunk_handle:04x}")
            allocations.append((pointer - 2, pointer - 2 + allocation_size, chunk_handle))
        allocations.sort()
        for left, right in zip(allocations, allocations[1:]):
            if left[1] > right[0]:
                fail(f"overlapping LMem chunks 0x{left[2]:04x} and 0x{right[2]:04x}")

    def chunk(self, chunk_handle: int) -> bytes:
        if chunk_handle not in self.handles:
            fail(f"0x{chunk_handle:04x} is not a local handle")
        pointer = u16(self.data, chunk_handle)
        if pointer in (0, 0xFFFF):
            fail(f"unallocated LMem chunk 0x{chunk_handle:04x}")
        allocation_size = u16(self.data, pointer - 2)
        return self.data[pointer : pointer - 2 + allocation_size]


def chunk_array(chunk: bytes) -> tuple[int, list[bytes]]:
    """Return (fixed element size, raw elements) from a ChunkArray."""
    need(chunk, 0, 8, "ChunkArray header")
    count = u16(chunk, 0)
    element_size = u16(chunk, 2)
    cur_offset = u16(chunk, 4)
    data_offset = u16(chunk, 6)
    if cur_offset > count:
        fail("ChunkArray current element exceeds its count")
    if data_offset < 8 or data_offset > len(chunk):
        fail("invalid ChunkArray data offset")
    if element_size:
        need(chunk, data_offset, count * element_size, "fixed ChunkArray elements")
        return element_size, [
            chunk[data_offset + i * element_size : data_offset + (i + 1) * element_size]
            for i in range(count)
        ]
    need(chunk, data_offset, count * 2, "variable ChunkArray offsets")
    offsets = [u16(chunk, data_offset + i * 2) for i in range(count)]
    minimum = data_offset + count * 2
    if offsets and (offsets[0] < minimum or any(a >= b for a, b in zip(offsets, offsets[1:]))):
        fail("invalid variable ChunkArray element offsets")
    if offsets and offsets[-1] >= len(chunk):
        fail("variable ChunkArray element is out of range")
    ends = offsets[1:] + [len(chunk)]
    return 0, [chunk[start:end] for start, end in zip(offsets, ends)]


def name_array(chunk: bytes) -> tuple[int, list[bytes]]:
    need(chunk, 0, 12, "NameArray header")
    if u16(chunk, 2) != 0 or u16(chunk, 6) < 12:
        fail("NameArray is not a variable ElementArray")
    data_size = u16(chunk, 10)
    _, elements = chunk_array(chunk)
    for element in elements:
        need(element, 0, 3, "NameArray element header")
        if element[2] != 0xFF:
            need(element, 0, 3 + data_size, "NameArray element")
    return data_size, elements


def element_array(vm: VMFile, handle: int, expected_type: int) -> list[bytes]:
    lmem = LMemBlock(vm.block(handle))
    active = [h for h in lmem.handles if u16(lmem.data, h) not in (0, 0xFFFF)]
    if not active:
        fail(f"empty text element block 0x{handle:04x}")
    chunk = lmem.chunk(active[0])
    need(chunk, 0, 12, "TextElementArrayHeader")
    if chunk[10] != expected_type:
        fail(f"text element block 0x{handle:04x} has array type {chunk[10]}, expected {expected_type}")
    _, elements = chunk_array(chunk)
    return elements


def validate_name_array_block(vm: VMFile, handle: int) -> list[bytes]:
    lmem = LMemBlock(vm.block(handle))
    active = [h for h in lmem.handles if u16(lmem.data, h) not in (0, 0xFFFF)]
    if not active:
        fail(f"empty NameArray block 0x{handle:04x}")
    _, elements = name_array(lmem.chunk(active[0]))
    return elements


@dataclass
class HugeArray:
    handle: int
    element_size: int
    extra_header: bytes
    elements: list[bytes]


def lmem_used_size(data: bytes) -> int:
    need(data, 0, 16, "LMem header")
    block_size = u16(data, 8)
    total_free = u16(data, 14)
    if total_free > block_size:
        fail("LMem free-byte count exceeds block size")
    return block_size - total_free


def huge_array(vm: VMFile, handle: int) -> HugeArray:
    directory_block = vm.block(handle, 0xFF03)
    directory_lmem = LMemBlock(directory_block)
    d = directory_lmem.data
    need(d, 16, 10, "HugeArrayDirectory")
    first_block = u16(d, 16)
    directory_chunk_handle = u16(d, 18)
    extended_directory = u16(d, 20)
    self_handle = u16(d, 22)
    element_size = u16(d, 24)
    if extended_directory:
        fail("extended HugeArray directories are not part of GeoWrite protocol 3.0")
    if self_handle != handle:
        fail(f"HugeArray 0x{handle:04x} has inconsistent self handle")
    if directory_lmem.handle_table < 26:
        fail("HugeArray header overlaps its LMem handle table")
    extra = d[26 : directory_lmem.handle_table]
    directory_chunk = directory_lmem.chunk(directory_chunk_handle)
    fixed, directory_entries = chunk_array(directory_chunk)
    if fixed != 8 or not directory_entries:
        fail("invalid HugeArray block directory")
    if (u32(directory_entries[0], 0), u16(directory_entries[0], 4), u16(directory_entries[0], 6)) != (
        0xFFFFFFFF,
        0,
        0,
    ):
        fail("HugeArray directory lacks its required sentinel")

    elements: list[bytes] = []
    expected_first = first_block
    previous = 0
    last_index = -1
    for entry in directory_entries[1:]:
        entry_last = u32(entry, 0)
        entry_size = u16(entry, 4)
        data_handle = u16(entry, 6)
        if not data_handle:
            fail("HugeArray directory contains a null data block")
        block = vm.block(data_handle, 0xFF04)
        lmem = LMemBlock(block)
        need(lmem.data, 16, 8, "HugeArray data header")
        next_handle = u16(lmem.data, 16)
        prev_handle = u16(lmem.data, 18)
        owner_handle = u16(lmem.data, 20)
        valid_prev = prev_handle == previous or (previous == 0 and prev_handle == handle)
        if data_handle != expected_first or not valid_prev or owner_handle != handle:
            fail(f"broken HugeArray link at block 0x{data_handle:04x}")
        payload_handle = lmem.handle_table
        fixed_size, block_elements = chunk_array(lmem.chunk(payload_handle))
        if fixed_size != element_size:
            fail(f"HugeArray 0x{handle:04x} element-size mismatch")
        elements.extend(block_elements)
        last_index += len(block_elements)
        if entry_last != last_index:
            fail(f"HugeArray 0x{handle:04x} directory index mismatch")
        previous = data_handle
        expected_first = next_handle
    if expected_first:
        fail(f"HugeArray 0x{handle:04x} has an unlisted linked data block")
    return HugeArray(handle, element_size, extra, elements)


Matrix = tuple[float, float, float, float, float, float]
IDENTITY_MATRIX: Matrix = (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)


def trans_matrix(data: bytes, offset: int = 0) -> Matrix:
    """Decode TransMatrix in Cairo's xx,yx,xy,yy,x0,y0 order."""
    need(data, offset, 28, "TransMatrix")
    return (
        wwfixed(data, offset),
        wwfixed(data, offset + 4),
        wwfixed(data, offset + 8),
        wwfixed(data, offset + 12),
        dwfixed(data, offset + 16),
        dwfixed(data, offset + 22),
    )


def multiply_matrix(left: Matrix, right: Matrix) -> Matrix:
    """Return the affine product left*right."""
    lxx, lyx, lxy, lyy, lx0, ly0 = left
    rxx, ryx, rxy, ryy, rx0, ry0 = right
    return (
        lxx * rxx + lxy * ryx,
        lyx * rxx + lyy * ryx,
        lxx * rxy + lxy * ryy,
        lyx * rxy + lyy * ryy,
        lxx * rx0 + lxy * ry0 + lx0,
        lyx * rx0 + lyy * ry0 + ly0,
    )


def cairo_safe_matrix(matrix: Matrix) -> Matrix:
    """Preserve a GEOS singular transform with a sub-pixel Cairo perturbation."""
    xx, yx, xy, yy, x0, y0 = matrix
    if abs(xx * yy - yx * xy) >= 1e-12:
        return matrix
    epsilon = 1e-7
    if abs(xy) + abs(yy) >= abs(xx) + abs(yx):
        length = math.hypot(xy, yy) or 1.0
        xx += yy / length * epsilon
        yx -= xy / length * epsilon
    else:
        length = math.hypot(xx, yx) or 1.0
        xy -= yx / length * epsilon
        yy += xx / length * epsilon
    if abs(xx * yy - yx * xy) < 1e-15:
        fail("GString transform cannot be represented by Cairo")
    return xx, yx, xy, yy, x0, y0


def geos_palette_color(index: int) -> tuple[int, int, int]:
    """Return one entry of the standard 256-color PC/GEOS palette."""
    standard = (
        (0x00, 0x00, 0x00), (0x00, 0x00, 0xAA),
        (0x00, 0xAA, 0x00), (0x00, 0xAA, 0xAA),
        (0xAA, 0x00, 0x00), (0xAA, 0x00, 0xAA),
        (0xAA, 0x55, 0x00), (0xAA, 0xAA, 0xAA),
        (0x55, 0x55, 0x55), (0x55, 0x55, 0xFF),
        (0x55, 0xFF, 0x55), (0x55, 0xFF, 0xFF),
        (0xFF, 0x55, 0x55), (0xFF, 0x55, 0xFF),
        (0xFF, 0xFF, 0x55), (0xFF, 0xFF, 0xFF),
    )
    if not 0 <= index <= 255:
        fail("bitmap palette index is outside the byte range")
    if index < 16:
        return standard[index]
    if index < 32:
        value = (index - 16) * 17
        return value, value, value
    if index < 40:
        return 0, 0, 0
    cube = index - 40
    return (cube // 36) * 51, ((cube // 6) % 6) * 51, (cube % 6) * 51


# The 90 PC/GEOS SystemDrawMask rows, in numeric enum order. Each mask is
# eight bytes high and its most-significant bit is the leftmost pixel. The
# first 25 are named patterns; 25 through 89 are the kernel's ordered 64-step
# dither table from solid through empty.
SYSTEM_DRAW_MASKS = bytes.fromhex(
    "9942249999244299fbf5fbf5fbf5fbf5ff00ff00ff00ff00555555555555555501020408102040808040201008040201"
    "ff888888ff888888ff80808080808080ff808080ff080808081c22c180010204881422418800aa008040200002040800"
    "40a00000040a00008244394482010101038448300c020101f87422478f1722718080413e080814e355a04040550a0404"
    "102054aaff020408205088888888050277898f8f7798f8f8bf00bfbfb0b0b0b00008142a552a1408000000ff00000000"
    "1010101010101010ffffffffffffffffffffffffffffff7ffffffff7ffffff7ffffffff7ffffff77ffffff77ffffff77"
    "ffffff77ffdfff77fffdff77ffdfff77fffdff77ffddff77ffddff77ffddff77ffddff77ffddff57ffddff75ffddff57"
    "ffddff75ffddff55ffddff55ffddff55ffddff55ff5dff55ffd5ff55ff5dff55ffd5ff55ff55ff55ff55ff55ff55ff55"
    "ff55ff55ff55bf55ff55fb55ff55bf55ff55fb55ff55bb55ff55bb55ff55bb55ff55bb55ef55bb55fe55bb55ef55bb55"
    "fe55bb55ee55bb55ee55bb55ee55bb55ee55bb55ee55ab55ee55ba55ee55ab55ee55ba55ee55aa55ee55aa55ee55aa55"
    "ee55aa55ae55aa55ea55aa55ae55aa55ea55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa15aa55aa51aa55aa15"
    "aa55aa51aa55aa11aa55aa11aa55aa11aa55aa11aa45aa11aa54aa11aa45aa11aa54aa11aa44aa11aa44aa11aa44aa11"
    "aa44aa11aa44aa01aa44aa10aa44aa01aa44aa10aa44aa00aa44aa00aa44aa00aa44aa00aa04aa00aa40aa00aa04aa00"
    "aa40aa00aa00aa00aa00aa00aa00aa00aa00aa00aa002a00aa00a200aa002a00aa00a200aa002200aa002200aa002200"
    "aa0022008a002200a80022008a002200a800220088002200880022008800220088002200880002008800200088000200"
    "880020008800000088000000880000008800000008000000800000000800000080000000000000000000000000000000"
)


def draw_mask_rows(mask_type: int, custom: bytes | None) -> bytes:
    """Resolve a SystemDrawMask, including its inverse flag, to eight rows."""
    number = mask_type & 0x7F
    if number == 0x7F:
        if custom is None or len(custom) != 8:
            fail("custom area draw mask does not contain eight rows")
        rows = custom
    elif number <= 89:
        rows = SYSTEM_DRAW_MASKS[number * 8 : number * 8 + 8]
    else:
        fail(f"area draw mask uses undefined system pattern {number}")
    if mask_type & 0x80:
        rows = bytes(value ^ 0xFF for value in rows)
    return rows


@dataclass(frozen=True)
class BitmapRaster:
    width: int
    height: int
    x_resolution: int
    y_resolution: int
    bgra: bytes
    coverage: bytes


@dataclass(frozen=True)
class BitmapSlice:
    width: int
    height: int
    compression: int
    bitmap_type: int
    start_scan: int
    scan_count: int
    x_resolution: int
    y_resolution: int
    palette: tuple[tuple[int, int, int], ...] | None
    encoded_data: bytes


@dataclass
class GStringGraphic:
    elements: list[bytes]
    bitmaps: dict[int, BitmapRaster]
    continuation_indices: set[int]
    legacy: bool


@dataclass
class VisTextGraphic:
    width: int
    height: int
    graphic_type: int
    flags: int
    matrix: Matrix
    draw_offset: tuple[int, int]
    gstring: GStringGraphic | None


def bitmap_scan_size(width: int, bitmap_type: int) -> tuple[int, int]:
    mask_size = (width + 7) // 8
    bitmap_format = bitmap_type & 7
    if bitmap_format == 0:
        pixel_size = mask_size
    elif bitmap_format == 1:
        pixel_size = (width + 1) // 2
    elif bitmap_format == 2:
        pixel_size = width
    elif bitmap_format == 3:
        pixel_size = width * 3
    elif bitmap_format == 4:
        pixel_size = mask_size * 4
    elif bitmap_format == 5:
        pixel_size = mask_size * 3
    else:
        fail(f"bitmap uses reserved pixel format {bitmap_format}")
    return mask_size, pixel_size + (mask_size if bitmap_type & 0x10 else 0)


def unpack_packbits_row(data: bytes, offset: int, output_size: int) -> tuple[bytes, int]:
    result = bytearray()
    cursor = offset
    while len(result) < output_size:
        need(data, cursor, 1, "PackBits control byte")
        control = data[cursor]
        cursor += 1
        if control < 0x80:
            count = control + 1
            need(data, cursor, count, "PackBits literal")
            result.extend(data[cursor : cursor + count])
            cursor += count
        else:
            count = 257 - control
            need(data, cursor, 1, "PackBits repeated byte")
            result.extend(bytes((data[cursor],)) * count)
            cursor += 1
        if len(result) > output_size:
            fail("PackBits run crosses a bitmap scan-line boundary")
    return bytes(result), cursor


def parse_bitmap_slice(raw: bytes) -> BitmapSlice:
    need(raw, 0, 6, "Bitmap header")
    width, height = u16(raw, 0), u16(raw, 2)
    compression, bitmap_type = raw[4], raw[5]
    if not width or not height:
        fail("bitmap has a zero width or height")
    if bitmap_type & 0x80:
        fail("bitmap has its reserved type bit set")
    if bitmap_type & 0x20:
        fail("inline GString bitmap incorrectly uses HugeBitmap storage")
    if compression not in (0, 1):
        fail(f"unsupported bitmap compression method {compression}")

    if bitmap_type & 0x08:
        need(raw, 0, 20, "CBitmap header")
        start_scan, scan_count = u16(raw, 6), u16(raw, 8)
        data_offset, palette_offset = u16(raw, 12), u16(raw, 14)
        x_resolution, y_resolution = u16(raw, 16), u16(raw, 18)
        if not x_resolution or not y_resolution:
            fail("CBitmap has a zero resolution")
        if start_scan + scan_count > height:
            fail("CBitmap slice lies beyond its declared height")
        palette: tuple[tuple[int, int, int], ...] | None = None
        occupied_end = 20
        if bitmap_type & 0x40:
            if palette_offset != 20:
                fail("GString CBitmap palette does not immediately follow its header")
            need(raw, palette_offset, 2, "bitmap Palette")
            count = u16(raw, palette_offset)
            if not count or count > 256:
                fail("bitmap Palette has an invalid entry count")
            palette_end = palette_offset + 2 + count * 3
            need(raw, palette_offset, 2 + count * 3, "bitmap Palette entries")
            palette = tuple(
                tuple(raw[palette_offset + 2 + i * 3 : palette_offset + 5 + i * 3])
                for i in range(count)
            )
            occupied_end = palette_end
        if scan_count:
            if data_offset != occupied_end:
                fail("GString CBitmap data does not immediately follow its header/palette")
            encoded = raw[data_offset:]
        else:
            if len(raw) != occupied_end:
                fail("zero-scan CBitmap slice contains unexplained bytes")
            encoded = b""
        return BitmapSlice(
            width, height, compression, bitmap_type, start_scan, scan_count,
            x_resolution, y_resolution, palette, encoded,
        )

    if bitmap_type & 0x40:
        fail("simple Bitmap sets the ignored complex-bitmap palette flag")
    return BitmapSlice(
        width, height, compression, bitmap_type, 0, height, 72, 72, None, raw[6:]
    )


def decode_bitmap_rows(bitmap_slice: BitmapSlice) -> list[bytes]:
    _, scan_size = bitmap_scan_size(bitmap_slice.width, bitmap_slice.bitmap_type)
    data = bitmap_slice.encoded_data
    if bitmap_slice.compression == 0:
        expected = scan_size * bitmap_slice.scan_count
        if len(data) != expected:
            fail(f"uncompressed bitmap slice has {len(data)} data bytes, expected {expected}")
        return [data[i * scan_size : (i + 1) * scan_size] for i in range(bitmap_slice.scan_count)]
    rows: list[bytes] = []
    cursor = 0
    for _ in range(bitmap_slice.scan_count):
        row, cursor = unpack_packbits_row(data, cursor, scan_size)
        rows.append(row)
    if cursor != len(data):
        fail("bytes remain after the final PackBits bitmap scan line")
    return rows


def decode_bitmap(slices: list[BitmapSlice], fill_bitmap: bool) -> BitmapRaster:
    if not slices:
        fail("bitmap command has no bitmap slices")
    first = slices[0]
    common = (
        first.width, first.height, first.compression, first.bitmap_type & ~0x40,
        first.x_resolution, first.y_resolution,
    )
    palette = first.palette
    rows: list[bytes | None] = [None] * first.height
    for item in slices:
        if (
            item.width, item.height, item.compression, item.bitmap_type & ~0x40,
            item.x_resolution, item.y_resolution,
        ) != common:
            fail("CBitmap continuation changes bitmap header properties")
        if item.palette is not None:
            if palette is not None and item.palette != palette:
                fail("CBitmap continuation changes its palette")
            palette = item.palette
        decoded = decode_bitmap_rows(item)
        for row_number, row in enumerate(decoded, item.start_scan):
            if rows[row_number] is not None:
                fail("CBitmap slices overlap")
            rows[row_number] = row
    if any(row is None for row in rows):
        fail("CBitmap slices do not cover every declared scan line")
    if fill_bitmap and (first.bitmap_type & 7) != 0:
        fail("GR_FILL_BITMAP requires a monochrome bitmap")

    mask_size, _ = bitmap_scan_size(first.width, first.bitmap_type)
    pixel_offset = mask_size if first.bitmap_type & 0x10 else 0
    bgra = bytearray()
    coverage = bytearray()
    for maybe_row in rows:
        assert maybe_row is not None
        row = maybe_row
        for x in range(first.width):
            alpha = 255
            if first.bitmap_type & 0x10:
                alpha = 255 if row[x // 8] & (0x80 >> (x & 7)) else 0
            bitmap_format = first.bitmap_type & 7
            if bitmap_format == 0:
                index = 1 if row[pixel_offset + x // 8] & (0x80 >> (x & 7)) else 0
                red = green = blue = 0 if index else 255
                shape = 255 if index else 0
            elif bitmap_format == 1:
                packed = row[pixel_offset + x // 2]
                index = packed >> 4 if not (x & 1) else packed & 0x0F
                red, green, blue = palette[index] if palette is not None else geos_palette_color(index)
                shape = alpha
            elif bitmap_format == 2:
                index = row[pixel_offset + x]
                if palette is not None:
                    if index >= len(palette):
                        fail("8-bit bitmap pixel exceeds its supplied palette")
                    red, green, blue = palette[index]
                else:
                    red, green, blue = geos_palette_color(index)
                shape = alpha
            elif bitmap_format == 3:
                base = pixel_offset + x * 3
                red, green, blue = row[base : base + 3]
                shape = alpha
            else:
                fail("CMY/CMYK bitmap rendering is not implemented")
            if alpha == 0:
                red = green = blue = 0
            coverage.append(min(alpha, shape) if fill_bitmap else alpha)
            bgra.extend((blue, green, red, alpha))
    return BitmapRaster(
        first.width, first.height, first.x_resolution, first.y_resolution,
        bytes(bgra), bytes(coverage),
    )


def parse_gstring(vm: VMFile, handle: int) -> GStringGraphic:
    array = huge_array(vm, handle)
    if array.element_size != 0:
        fail("GString HugeArray is not variable-sized")
    elements = array.elements
    if not elements or elements[-1] != b"\0":
        fail("GString does not end with a one-byte GR_END_GSTRING")
    bitmaps: dict[int, BitmapRaster] = {}
    continuations: set[int] = set()
    index = 0
    while index < len(elements):
        element = elements[index]
        need(element, 0, 1, "GString element")
        opcode = element[0]
        if opcode == 0 and index != len(elements) - 1:
            fail("GString contains an early GR_END_GSTRING")
        if opcode == 0x54:
            fail("GString contains an orphan GSE_BITMAP_SLICE")
        if opcode in (0x4C, 0x4D, 0x50, 0x51):
            header_size = 3 if opcode in (0x4D, 0x51) else 7
            need(element, 0, header_size, "GString bitmap command")
            size_offset = 1 if header_size == 3 else 5
            if u16(element, size_offset) != len(element) - header_size:
                fail("GString bitmap command byte count does not match its element")
            first_slice = parse_bitmap_slice(element[header_size:])
            slices = [first_slice]
            next_index = index + 1
            if first_slice.bitmap_type & 0x08:
                while next_index < len(elements) and elements[next_index][0] == 0x54:
                    continuation = elements[next_index]
                    need(continuation, 0, 3, "GString bitmap continuation")
                    if u16(continuation, 1) != len(continuation) - 3:
                        fail("GString bitmap continuation byte count is inconsistent")
                    slices.append(parse_bitmap_slice(continuation[3:]))
                    continuations.add(next_index)
                    next_index += 1
            bitmaps[index] = decode_bitmap(slices, opcode in (0x4C, 0x4D))
            index = next_index
            continue
        index += 1
    return GStringGraphic(elements, bitmaps, continuations, False)


def parse_graphic_elements(vm: VMFile, elements: list[bytes]) -> list[VisTextGraphic | None]:
    result: list[VisTextGraphic | None] = []
    cache: dict[int, GStringGraphic] = {}
    for element in elements:
        need(element, 0, 3, "VisTextGraphic element")
        if element[2] == 0xFF:
            result.append(None)
            continue
        if len(element) != 50:
            fail(f"VisTextGraphic element is {len(element)} bytes, expected 50")
        chain = u32(element, 3)
        width, height = u16(element, 7), u16(element, 9)
        graphic_type, flags = element[11], u16(element, 12)
        if graphic_type not in (0, 1):
            fail(f"VisTextGraphic has unknown type {graphic_type}")
        if flags & ~0xE000:
            fail("VisTextGraphic has unknown flag bits")
        if element[14:18] != b"\0\0\0\0":
            fail("VisTextGraphic reserved bytes are not zero")
        if graphic_type == 0:
            if not width or not height:
                fail("GString VisTextGraphic has a zero saved size")
            if not chain or (chain & 0xFFFF):
                fail("GString VisTextGraphic does not use a VM-chain block")
            handle = chain >> 16
            if handle not in cache:
                cache[handle] = parse_gstring(vm, handle)
            matrix = trans_matrix(element, 18)
            draw_offset = (s16(element, 46), s16(element, 48))
            gstring = cache[handle]
        else:
            if chain:
                fail("variable VisTextGraphic unexpectedly owns a VM chain")
            matrix = IDENTITY_MATRIX
            draw_offset = (0, 0)
            gstring = None
        result.append(
            VisTextGraphic(width, height, graphic_type, flags, matrix, draw_offset, gstring)
        )
    return result


@dataclass(frozen=True)
class Run:
    position: int
    token: int


def run_array(vm: VMFile, handle: int, element_block: int, require_zero: bool = True) -> list[Run]:
    array = huge_array(vm, handle)
    if array.element_size != 5 or len(array.extra_header) != 2 or u16(array.extra_header, 0) != element_block:
        fail(f"HugeArray 0x{handle:04x} is not the expected text run array")
    runs = [Run(u24(e, 0), u16(e, 3)) for e in array.elements]
    if not runs or runs[-1].position != 0xFFFFFF or (require_zero and len(runs) > 1 and runs[0].position != 0):
        fail(f"text run array 0x{handle:04x} has invalid endpoints")
    if any(a.position >= b.position for a, b in zip(runs, runs[1:])):
        fail(f"text run array 0x{handle:04x} is not ordered")
    return runs


@dataclass(frozen=True)
class CharAttr:
    style_token: int
    font_id: int
    point_size: float
    styles: int
    color: tuple[float, float, float]
    tracking: int
    weight: int
    width: int
    extended_styles: int
    foreground_mask: int = 25
    foreground_pattern: tuple[int, int] = (0, 0)
    background_color: tuple[float, float, float] = (1.0, 1.0, 1.0)
    background_mask: int = 25
    background_pattern: tuple[int, int] = (0, 0)


GEOS_PALETTE = (
    (0.0, 0.0, 0.0),
    (0.0, 0.0, 0.67),
    (0.0, 0.5, 0.0),
    (0.0, 0.5, 0.5),
    (0.67, 0.0, 0.0),
    (0.5, 0.0, 0.5),
    (0.5, 0.33, 0.0),
    (0.75, 0.75, 0.75),
    (0.5, 0.5, 0.5),
    (0.25, 0.25, 1.0),
    (0.25, 1.0, 0.25),
    (0.25, 1.0, 1.0),
    (1.0, 0.25, 0.25),
    (1.0, 0.25, 1.0),
    (1.0, 1.0, 0.0),
    (1.0, 1.0, 1.0),
)


def color_quad(data: bytes, offset: int) -> tuple[float, float, float]:
    need(data, offset, 4, "ColorQuad")
    red_or_index, info, green, blue = data[offset : offset + 4]
    if info == 0x80:
        return red_or_index / 255.0, green / 255.0, blue / 255.0
    if info == 0:
        if red_or_index < len(GEOS_PALETTE):
            return GEOS_PALETTE[red_or_index]
        if 0x10 <= red_or_index <= 0x1F:
            level = (red_or_index - 0x10) / 15.0
            return level, level, level
        fail(f"unsupported indexed GEOS color 0x{red_or_index:02x}")
    if info == 1:
        level = red_or_index / 255.0
        return level, level, level
    if info == 3:
        return 1.0 - red_or_index / 255.0, 1.0 - green / 255.0, 1.0 - blue / 255.0
    fail(f"unsupported GEOS ColorFlag 0x{info:02x}")


def parse_char_attrs(elements: Sequence[bytes]) -> dict[int, CharAttr]:
    result: dict[int, CharAttr] = {}
    for token, e in enumerate(elements):
        need(e, 0, 38, "VisTextCharAttr")
        if len(e) != 38:
            fail("VisTextCharAttr has an unexpected size")
        if e[2] == 0xFF:
            continue
        extended_styles = u16(e, 19)
        if extended_styles & 0x007F:
            fail("VisTextCharAttr has undefined extended-style bits")
        if e[22] > 1 or e[29] > 1:
            fail("VisTextCharAttr uses an unsupported GraphicPattern type")
        if (e[22] == 1 and e[23] > 5) or (e[29] == 1 and e[30] > 5):
            fail("VisText GraphicPattern uses an unknown system hatch")
        draw_mask_rows(e[21], None)
        draw_mask_rows(e[28], None)
        if any(e[31:38]):
            fail("VisTextCharAttr reserved bytes are nonzero")
        result[token] = CharAttr(
            u16(e, 3),
            u16(e, 5),
            wbfixed(e, 7),
            e[10],
            color_quad(e, 11),
            s16(e, 15),
            e[17],
            e[18],
            extended_styles,
            e[21],
            (e[22], e[23]),
            color_quad(e, 24),
            e[28],
            (e[29], e[30]),
        )
    return result


@dataclass(frozen=True)
class ParaAttr:
    style_token: int
    border_flags: int
    attributes: int
    left_margin: float
    right_margin: float
    para_margin: float
    line_spacing: float
    leading: float
    space_on_top: float
    space_on_bottom: float
    tabs: tuple[tuple[float, int, int, int, int, int], ...]


def parse_para_attrs(elements: Sequence[bytes]) -> dict[int, ParaAttr]:
    result: dict[int, ParaAttr] = {}
    for token, e in enumerate(elements):
        need(e, 0, 3, "VisTextParaAttr header")
        if e[2] == 0xFF:
            continue
        need(e, 0, 72, "VisTextParaAttr")
        tab_count = e[31]
        exact_size = 72 + tab_count * 8
        need(e, 0, exact_size, "paragraph tabs")
        if any(e[exact_size:]):
            fail("non-padding bytes follow VisTextParaAttr")
        tabs = tuple(
            (
                u16(e, 72 + i * 8) / 8.0,
                e[74 + i * 8],
                e[75 + i * 8],
                e[76 + i * 8],
                e[77 + i * 8],
                u16(e, 78 + i * 8),
            )
            for i in range(tab_count)
        )
        result[token] = ParaAttr(
            u16(e, 3),
            u16(e, 5),
            u16(e, 11),
            u16(e, 13) / 8.0,
            u16(e, 15) / 8.0,
            u16(e, 17) / 8.0,
            e[19] + e[18] / 256.0,
            u16(e, 21) / 8.0,
            u16(e, 23) / 8.0,
            u16(e, 25) / 8.0,
            tabs,
        )
    return result


@dataclass(frozen=True)
class FieldInfo:
    char_count: int
    position: int
    width: int
    tab_reference: int


@dataclass(frozen=True)
class LineInfo:
    flags: int
    height: float
    baseline: float
    adjustment: int
    char_count: int
    space_pad: float
    line_end: int
    fields: tuple[FieldInfo, ...]


def parse_line(element: bytes) -> LineInfo:
    need(element, 0, 25, "LineInfo")
    count = u24(element, 10)
    fields: list[FieldInfo] = []
    consumed = 0
    offset = 18
    while consumed < count or not fields:
        need(element, offset, 7, "FieldInfo")
        field_info = FieldInfo(u16(element, offset), u16(element, offset + 2), u16(element, offset + 4), element[offset + 6])
        if not field_info.char_count and count:
            fail("zero-length field in nonempty LineInfo")
        fields.append(field_info)
        consumed += field_info.char_count
        offset += 7
        if consumed > count:
            fail("FieldInfo character counts exceed LineInfo count")
    if any(element[offset:]):
        fail("non-padding bytes follow LineInfo fields")
    return LineInfo(
        u16(element, 0),
        wbfixed(element, 2),
        wbfixed(element, 5),
        s16(element, 8),
        count,
        wbfixed(element, 13),
        u16(element, 16),
        tuple(fields),
    )


@dataclass(frozen=True)
class Region:
    char_count: int
    line_count: int
    section: int
    x: int
    y: int
    width: int
    height: int
    calculated_height: float
    text_region: tuple[int, int]
    flags: int
    inherited_text_region: tuple[int, int]
    draw_region: tuple[int, int]
    object_optr: tuple[int, int]


def parse_regions(chunk: bytes) -> list[Region]:
    fixed, elements = chunk_array(chunk)
    if fixed != 54:
        fail("ArticleRegionArray does not contain 54-byte records")
    result = []
    for e in elements:
        result.append(
            Region(
                u32(e, 0),
                u32(e, 4),
                u16(e, 8),
                s32(e, 10),
                s32(e, 14),
                u16(e, 18),
                u16(e, 20),
                wbfixed(e, 22),
                (u16(e, 25), u16(e, 27)),
                u16(e, 29),
                (u16(e, 34), u16(e, 36)),
                (u16(e, 38), u16(e, 40)),
                (u16(e, 42), u16(e, 44)),
            )
        )
    return result


@dataclass
class Article:
    name: str
    raw_text: bytes
    char_runs: list[Run]
    para_runs: list[Run]
    type_runs: list[Run]
    graphic_runs: list[Run]
    lines: list[LineInfo]
    regions: list[Region]


@dataclass
class Section:
    name: str
    flags: int
    starting_page: int
    master_pages: tuple[int, ...]
    columns: int
    rule_width: float
    column_spacing: float
    margins: tuple[float, float, float, float]
    page_count: int


@dataclass(frozen=True)
class GrObjTransform:
    center: tuple[float, float]
    size: tuple[float, float]
    parent_size: tuple[float, float]
    matrix: Matrix


@dataclass(frozen=True)
class GrObjLineAttr:
    color: tuple[float, float, float]
    end: int
    join: int
    width: float
    mask: int
    style: int
    miter_limit: float
    draw_mode: int
    info: int
    arrow_angle: int
    arrow_length: int


@dataclass(frozen=True)
class GrObjAreaAttr:
    color: tuple[float, float, float]
    mask: int
    draw_mode: int
    pattern: tuple[int, int]
    background: tuple[float, float, float]
    transparent: bool
    gradient: tuple[int, tuple[float, float, float], int, int] | None


@dataclass
class GrObjNode:
    optr: tuple[int, int]
    kind: str
    transform: GrObjTransform
    attr_flags: int
    area_token: int
    line_token: int
    children: tuple["GrObjNode", ...] = ()
    ward_bounds: tuple[float, float, float, float] | None = None
    text: Article | None = None
    bitmap: BitmapRaster | None = None
    gstring: GStringGraphic | None = None
    gstring_offset: tuple[float, float] = (0.0, 0.0)
    radius: float = 0.0
    arc_data: tuple[int, float, float] | None = None


@dataclass(frozen=True)
class GrObjBody:
    bounds: tuple[int, int, int, int]
    children: tuple[GrObjNode, ...]


def gr_obj_element_array(vm: VMFile, handle: int, what: str) -> list[bytes]:
    """Read a GrObj ElementArray, whose header has no text-array type byte."""
    if not handle:
        fail(f"GeoWrite document lacks its {what} array")
    lmem = LMemBlock(vm.block(handle))
    active = [item for item in lmem.handles if u16(lmem.data, item) not in (0, 0xFFFF)]
    if len(active) != 1:
        fail(f"{what} block does not contain exactly one active ElementArray")
    _, elements = chunk_array(lmem.chunk(active[0]))
    return elements


def parse_gr_obj_line_attrs(elements: Sequence[bytes]) -> dict[int, GrObjLineAttr]:
    result: dict[int, GrObjLineAttr] = {}
    for token, element in enumerate(elements):
        need(element, 0, 3, "GrObj line element header")
        if element[2] == 0xFF:
            if len(element) != 3:
                fail("free GrObj line element is not three bytes")
            continue
        if len(element) != 26:
            fail("GrObjBaseLineAttrElement is not 26 bytes")
        if element[20] != 0 or u16(element, 24) != 0:
            fail("GrObj line element has an unknown type or nonzero reserved word")
        if element[8] > 2 or element[9] > 2 or element[15] > 4:
            fail("GrObj line element has an invalid end, join, or line style")
        draw_mask_rows(element[14], None)
        result[token] = GrObjLineAttr(
            tuple(value / 255.0 for value in element[5:8]),
            element[8], element[9], wwfixed(element, 10), element[14], element[15],
            wwfixed(element, 16), 1, element[21], element[22], element[23],
        )
    return result


def parse_gr_obj_area_attrs(elements: Sequence[bytes]) -> dict[int, GrObjAreaAttr]:
    result: dict[int, GrObjAreaAttr] = {}
    for token, element in enumerate(elements):
        need(element, 0, 3, "GrObj area element header")
        if element[2] == 0xFF:
            if len(element) != 3:
                fail("free GrObj area element is not three bytes")
            continue
        need(element, 0, 20, "GrObjBaseAreaAttrElement")
        element_type = element[15]
        expected = 20 if element_type == 0 else 28 if element_type == 1 else 0
        if not expected or len(element) != expected:
            fail("GrObj area element has an unknown type or size")
        if element[17] or u16(element, 18):
            fail("GrObj area element reserved fields are nonzero")
        if element[16] & ~1:
            fail("GrObj area element has unknown area-info bits")
        if element[10] > 1:
            fail("GrObj GraphicPattern has an unknown pattern type")
        draw_mask_rows(element[8], None)
        gradient = None
        if element_type == 1:
            if element[20] > 4:
                fail("GrObj gradient element has an invalid type")
            gradient = (
                element[20],
                tuple(value / 255.0 for value in element[21:24]),
                u16(element, 24),
                u16(element, 26),
            )
        result[token] = GrObjAreaAttr(
            tuple(value / 255.0 for value in element[5:8]),
            element[8], element[9], (element[10], element[11]),
            tuple(value / 255.0 for value in element[12:15]),
            bool(element[16] & 1), gradient,
        )
    return result


def saved_vm_handle(value: int, current: int, what: str) -> int:
    """Resolve a protocol-3 saved relocation word to a VM handle."""
    if value == 0x4000:
        return current
    if value & 0xF000 == 0x7000:
        handle = 32 + (value & 0x0FFF) * 12
        return handle
    fail(f"{what} has invalid saved relocation 0x{value:04x}")


def saved_optr(data: bytes, offset: int, current: int, what: str) -> tuple[int, int] | None:
    chunk, relocation = u16(data, offset), u16(data, offset + 2)
    if not chunk:
        if relocation:
            fail(f"null {what} has a nonzero block relocation")
        return None
    return saved_vm_handle(relocation, current, what), chunk & ~1


def parse_gr_obj_transform(block: LMemBlock, handle: int, what: str) -> GrObjTransform:
    if not handle:
        fail(f"{what} has no normal transform")
    raw = block.chunk(handle)
    if len(raw) != 44:
        fail(f"{what} normal transform is not 44 bytes")
    # Signed dimensions preserve horizontal/vertical reflection.  GeoWrite
    # saved negative sizes instead of folding every reflection into e11/e22.
    width, height = wwfixed(raw, 12), wwfixed(raw, 16)
    return GrObjTransform(
        (dwfixed(raw, 0), dwfixed(raw, 6)),
        (width, height),
        (wwfixed(raw, 20), wwfixed(raw, 24)),
        (wwfixed(raw, 28), wwfixed(raw, 32), wwfixed(raw, 36), wwfixed(raw, 40), 0.0, 0.0),
    )


def parse_local_text_runs(chunk: bytes, element_block: int, what: str, require_zero: bool = True) -> list[Run]:
    fixed, elements = chunk_array(chunk)
    if fixed != 5 or u16(chunk, 6) != 12:
        fail(f"{what} is not the expected cached TextRunArray")
    runs = [Run(u24(element, 0), u16(element, 3)) for element in elements]
    if not runs or runs[-1].position != 0xFFFFFF:
        fail(f"{what} lacks its terminal run")
    if require_zero and len(runs) > 1 and runs[0].position != 0:
        fail(f"{what} does not begin at text position zero")
    if any(left.position >= right.position for left, right in zip(runs, runs[1:])):
        fail(f"{what} is not ordered")
    if len(runs) > 1 and u16(chunk, 8) != element_block:
        fail(f"{what} references an unexpected element block")
    return runs


class GrObjParser:
    """Protocol-3 GrObj object-tree, ward, and DB-bitmap parser."""

    def __init__(
        self,
        vm: VMFile,
        line_attrs: dict[int, GrObjLineAttr],
        area_attrs: dict[int, GrObjAreaAttr],
        char_element_handle: int,
        para_element_handle: int,
        type_element_handle: int,
        graphic_element_handle: int,
        char_attrs: dict[int, CharAttr],
        para_attrs: dict[int, ParaAttr],
        type_elements: Sequence[bytes],
        graphic_elements: Sequence[VisTextGraphic | None],
    ):
        self.vm = vm
        self.line_attrs = line_attrs
        self.area_attrs = area_attrs
        self.char_element_handle = char_element_handle
        self.para_element_handle = para_element_handle
        self.type_element_handle = type_element_handle
        self.graphic_element_handle = graphic_element_handle
        self.char_attrs = char_attrs
        self.para_attrs = para_attrs
        self.type_elements = type_elements
        self.graphic_elements = graphic_elements
        self.blocks: dict[int, LMemBlock] = {}
        self.bitmap_cache: dict[int, BitmapRaster] = {}
        self.gstring_cache: dict[int, GStringGraphic] = {}
        self.active: set[tuple[int, int]] = set()

    def block(self, handle: int) -> LMemBlock:
        if handle not in self.blocks:
            self.blocks[handle] = LMemBlock(self.vm.block(handle), required_type=2)
        return self.blocks[handle]

    def parse_bitmap(self, handle: int) -> BitmapRaster:
        if handle in self.bitmap_cache:
            return self.bitmap_cache[handle]
        array = huge_array(self.vm, handle)
        header = array.extra_header
        need(header, 0, 24, "EditableBitmap header")
        width, height = u16(header, 0), u16(header, 2)
        compression, bitmap_type = header[4], header[5]
        if not width or not height or bitmap_type & 0x80:
            fail("EditableBitmap has invalid dimensions or type bits")
        if bitmap_type & 0x28 != 0x28:
            fail("GrObjBitmap data is not a complex HugeBitmap")
        if compression not in (0, 1):
            fail(f"unsupported EditableBitmap compression method {compression}")
        if u16(header, 6) or u16(header, 8):
            fail("HugeBitmap CBitmap scan range must be zero")
        device_offset, data_offset, palette_offset = u16(header, 10), u16(header, 12), u16(header, 14)
        x_resolution, y_resolution = u16(header, 16), u16(header, 18)
        if device_offset not in (0, 24) or data_offset or not x_resolution or not y_resolution:
            fail("EditableBitmap has invalid device/data offsets or resolution")
        # Bytes 20..23 are BitmapMode and ColorTransfer; 24..palette is the
        # saved VideoDriverInfo.  The renderer does not need the device's
        # private driver strings, but their exact bounded extent is retained.
        palette: tuple[tuple[int, int, int], ...] | None = None
        if bitmap_type & 0x40 and palette_offset:
            if palette_offset < 20 or palette_offset >= len(header):
                fail("EditableBitmap palette offset is outside its header")
            need(header, palette_offset, 2, "EditableBitmap Palette")
            count = u16(header, palette_offset)
            if not count or count > 256:
                fail("EditableBitmap Palette has an invalid entry count")
            palette_end = palette_offset + 2 + count * 3
            need(header, palette_offset, palette_end - palette_offset, "EditableBitmap Palette entries")
            palette = tuple(
                tuple(header[palette_offset + 2 + index * 3 : palette_offset + 5 + index * 3])
                for index in range(count)
            )
        elif not bitmap_type & 0x40 and palette_offset:
            fail("palette-less EditableBitmap has a palette offset")
        _, scan_size = bitmap_scan_size(width, bitmap_type)
        if len(array.elements) != height:
            fail("HugeBitmap does not contain exactly one element per scan line")
        if compression == 0:
            if array.element_size != scan_size or any(len(row) != scan_size for row in array.elements):
                fail("uncompressed HugeBitmap scan-line size is inconsistent")
        elif array.element_size and any(len(row) != array.element_size for row in array.elements):
            fail("fixed-size compressed HugeBitmap elements are inconsistent")
        bitmap_slice = BitmapSlice(
            width, height, compression, bitmap_type, 0, height,
            x_resolution, y_resolution, palette, b"".join(array.elements),
        )
        raster = decode_bitmap([bitmap_slice], False)
        self.bitmap_cache[handle] = raster
        return raster

    def parse_small_text(self, block_handle: int, chunk_handle: int) -> tuple[tuple[float, float, float, float], Article]:
        block = self.block(block_handle)
        raw = block.chunk(chunk_handle)
        if (u16(raw, 0), u16(raw, 2)) != (0x3003, 19) or u16(raw, 4) != 8 or u16(raw, 6) != 106:
            fail("MultTextGuardian ward is not a saved GrObjTextClass object")
        bounds = tuple(float(s16(raw, offset)) for offset in (8, 10, 12, 14))
        text_handle, char_handle, para_handle = u16(raw, 25), u16(raw, 27), u16(raw, 29)
        lines_handle = u16(raw, 33)
        if not all((text_handle, char_handle, para_handle, lines_handle)) or u16(raw, 31):
            fail("small VisText fixed storage references are invalid")
        text = block.chunk(text_handle)
        if not text or text[-1] or b"\0" in text[:-1]:
            fail("small VisText does not have exactly one terminal NUL")
        line_fixed, line_elements = chunk_array(block.chunk(lines_handle))
        if line_fixed:
            fail("small VisText LineInfo array is not variable-sized")
        lines = [parse_line(element) for element in line_elements]
        if sum(line.char_count for line in lines) != len(text) - 1:
            fail("small VisText LineInfo does not cover its text")
        type_handle = graphic_handle = 0
        position = 114
        while position < len(raw):
            need(raw, position, 2, "small VisText variable-data type")
            type_flags = u16(raw, position)
            data_type = type_flags & 0xFFFC
            if type_flags & 2:
                need(raw, position, 4, "small VisText variable-data header")
                entry_size = u16(raw, position + 2)
                if entry_size < 4 or entry_size & 1:
                    fail("small VisText variable-data entry has an invalid size")
                need(raw, position, entry_size, "small VisText variable-data entry")
                payload = raw[position + 4 : position + entry_size]
            else:
                entry_size, payload = 2, b""
            if data_type == 0x4800:
                if len(payload) != 2:
                    fail("small ATTR_VIS_TEXT_TYPE_RUNS has invalid size")
                type_handle = u16(payload, 0)
            elif data_type == 0x4804:
                if len(payload) != 2:
                    fail("small ATTR_VIS_TEXT_GRAPHIC_RUNS has invalid size")
                graphic_handle = u16(payload, 0)
            position += entry_size
        if position != len(raw):
            fail("small VisText variable data does not fill its chunk")
        char_runs = parse_local_text_runs(
            block.chunk(char_handle), self.char_element_handle, "small character runs"
        )
        para_runs = parse_local_text_runs(
            block.chunk(para_handle), self.para_element_handle, "small paragraph runs"
        )
        type_runs = (
            parse_local_text_runs(block.chunk(type_handle), self.type_element_handle, "small type runs")
            if type_handle else []
        )
        graphic_runs = (
            parse_local_text_runs(
                block.chunk(graphic_handle), self.graphic_element_handle, "small graphic runs", False
            ) if graphic_handle else []
        )
        for label, runs, available in (
            ("character", char_runs, self.char_attrs),
            ("paragraph", para_runs, self.para_attrs),
        ):
            for run in runs[:-1]:
                if run.position >= len(text) or run.token not in available:
                    fail(f"small VisText {label} run references unavailable data")
        for run in type_runs[:-1]:
            if run.position >= len(text) or run.token >= len(self.type_elements):
                fail("small VisText type run references unavailable data")
        for run in graphic_runs[:-1]:
            if run.position >= len(text) or run.token >= len(self.graphic_elements):
                fail("small VisText graphic run references unavailable data")
        graphic_positions = [run.position for run in graphic_runs[:-1]]
        if graphic_positions != [index for index, byte in enumerate(text[:-1]) if byte == 0x1A]:
            fail("small VisText graphic runs do not match graphic characters")
        return bounds, Article(
            "GrObjText", text, char_runs, para_runs, type_runs, graphic_runs, lines, []
        )

    def parse_spline(self, block_handle: int, chunk_handle: int) -> tuple[tuple[float, float, float, float], tuple[tuple[float, float, int], ...], int]:
        raw = self.block(block_handle).chunk(chunk_handle)
        if (u16(raw, 0), u16(raw, 2)) != (0x3003, 17) or u16(raw, 4) != 8 or u16(raw, 6) != 56:
            fail("SplineGuardian ward is not a saved GrObjSplineClass object")
        bounds = tuple(float(s16(raw, offset)) for offset in (8, 10, 12, 14))
        state = raw[25]
        if state & 0x80 or state & 0x10:
            fail("saved GrObjSpline has transient boundary/attribute-chunk state")
        point_block = saved_vm_handle(u16(raw, 27), block_handle, "VisSpline point block")
        point_chunk = u16(raw, 29)
        point_lmem = self.block(point_block)
        fixed, elements = chunk_array(point_lmem.chunk(point_chunk))
        if fixed != 7:
            fail("VisSpline point array is not an array of SplinePointStruct")
        points = tuple((swbfixed(item, 0), swbfixed(item, 3), item[6]) for item in elements)
        for _, _, info in points:
            if info & 0x80:
                if info & ~0x90:
                    fail("VisSpline control point has unknown saved flags")
            elif info & 0xF8:
                fail("VisSpline anchor point has transient saved flags")
        return bounds, points, state

    def parse_node(self, optr: tuple[int, int]) -> GrObjNode:
        if optr in self.active:
            fail("GrObj group hierarchy contains a cycle")
        self.active.add(optr)
        block_handle, chunk_handle = optr
        block = self.block(block_handle)
        raw = block.chunk(chunk_handle)
        need(raw, 0, 31, "GrObj object")
        class_pair = u16(raw, 0), u16(raw, 2)
        go = u16(raw, 4)
        if go != 6:
            fail("GrObjClass master instance is not at offset six")
        transform = parse_gr_obj_transform(block, u16(raw, go + 17), f"GrObj {optr}")
        sprite = u16(raw, go + 19)
        if sprite:
            parse_gr_obj_transform(block, sprite, f"GrObj {optr} sprite")
        attr_flags = u16(raw, go + 8)
        if attr_flags & ~0x03FF:
            fail("GrObj has unknown saved GrObjAttrFlags bits")
        area_token, line_token = u16(raw, go + 21), u16(raw, go + 23)
        if area_token != 0xFFFF and area_token not in self.area_attrs:
            fail(f"GrObj references missing area token {area_token}")
        if line_token != 0xFFFF and line_token not in self.line_attrs:
            fail(f"GrObj references missing line token {line_token}")
        node = GrObjNode(optr, "", transform, attr_flags, area_token, line_token)
        library, ordinal = class_pair
        if library == 0x6000 and ordinal in (0, 4):
            node.kind = "flow"
        elif library == 0x6000 and ordinal == 7:
            node.kind = "rect"
        elif library == 0x3003 and ordinal in (7, 8, 9, 10, 11):
            node.kind = {7: "rect", 8: "round_rect", 9: "ellipse", 10: "line", 11: "arc"}[ordinal]
            if ordinal == 8:
                if len(raw) != go + 27:
                    fail("GrObjRoundedRect instance has an invalid size")
                node.radius = float(u16(raw, go + 25))
            elif ordinal == 11:
                need(raw, go + 25, 33, "GrObjArc instance")
                close_type = raw[go + 25]
                if close_type > 2:
                    fail("GrObjArc has an invalid ArcCloseType")
                node.arc_data = (close_type, wwfixed(raw, go + 26), wwfixed(raw, go + 30))
        elif class_pair == (0x3003, 12):
            if len(raw) != go + 35:
                fail("GrObjGString instance has an invalid size")
            node.kind = "gstring"
            handle = u16(raw, go + 25)
            if handle not in self.gstring_cache:
                self.gstring_cache[handle] = parse_gstring(self.vm, handle)
            node.gstring = self.gstring_cache[handle]
            node.gstring_offset = (round(wwfixed(raw, go + 27)), round(wwfixed(raw, go + 31)))
        elif class_pair == (0x3003, 13):
            if len(raw) < go + 32:
                fail("GrObjGroup instance has an invalid size")
            node.kind = "group"
            head = saved_optr(raw, go + 25, block_handle, "GrObjGroup draw head")
            children: list[GrObjNode] = []
            current = head
            while current is not None:
                if len(children) > 65535:
                    fail("GrObjGroup child list does not terminate")
                children.append(self.parse_node(current))
                child_raw = self.block(current[0]).chunk(current[1])
                child_go = u16(child_raw, 4)
                link_chunk = u16(child_raw, child_go)
                link_relocation = u16(child_raw, child_go + 2)
                if link_chunk & 1:
                    parent = saved_vm_handle(link_relocation, current[0], "last GrObj child link")
                    if (parent, link_chunk & ~1) != optr:
                        fail("last GrObj child link does not return to its group")
                    break
                current = saved_optr(child_raw, child_go, current[0], "GrObj child link")
                if current is None:
                    fail("GrObjGroup child list ends without its last-link flag")
            node.children = tuple(children)
            if bool(attr_flags & 0x0100) != any(child.attr_flags & 0x0080 for child in children):
                fail("GrObjGroup paste-inside summary flag disagrees with its children")
        elif class_pair in ((0x3003, 16), (0x3003, 18), (0x3003, 21)):
            need(raw, go + 25, 9, "GrObjVisGuardian instance")
            ward = saved_optr(raw, go + 25, block_handle, "GrObjVisGuardian ward")
            if ward is None:
                fail("GrObjVisGuardian has no ward")
            expected = {16: 15, 18: 17, 21: 19}[ordinal]
            if (u16(raw, go + 29), u16(raw, go + 31)) != (0x3003, expected):
                fail("GrObjVisGuardian saved ward class does not match its guardian")
            if ordinal == 16:
                ward_raw = self.block(ward[0]).chunk(ward[1])
                if (u16(ward_raw, 0), u16(ward_raw, 2)) != (0x3003, 15) or u16(ward_raw, 4) != 8:
                    fail("BitmapGuardian ward is not a saved GrObjBitmapClass object")
                node.kind = "bitmap"
                node.ward_bounds = tuple(float(s16(ward_raw, offset)) for offset in (8, 10, 12, 14))
                node.bitmap = self.parse_bitmap(u16(ward_raw, 28))
            elif ordinal == 18:
                node.kind = "spline"
                bounds, points, state = self.parse_spline(*ward)
                node.ward_bounds = bounds
                # Keep the exact saved point/type stream and SplineState in a
                # private, renderer-consumed payload on this otherwise common node.
                node.arc_data = (state, 0.0, 0.0)
                node.children = tuple(
                    GrObjNode(
                        (-1, info), "point",
                        GrObjTransform((x, y), (0, 0), (0, 0), IDENTITY_MATRIX),
                        0, 0, 0,
                    )
                    for x, y, info in points
                )
            else:
                node.kind = "text"
                node.ward_bounds, node.text = self.parse_small_text(*ward)
        else:
            fail(f"unsupported protocol-3 GrObj class {class_pair[0]:04x}:{class_pair[1]:04x}")
        self.active.remove(optr)
        return node

    def parse_body(self, manager_handle: int) -> GrObjBody:
        manager = self.block(manager_handle)
        bodies = []
        for chunk_handle in manager.handles:
            if u16(manager.data, chunk_handle) in (0, 0xFFFF):
                continue
            raw = manager.chunk(chunk_handle)
            if len(raw) >= 4 and (u16(raw, 0), u16(raw, 2)) == (0x6000, 2):
                bodies.append((chunk_handle, raw))
        if len(bodies) != 1:
            fail("GrObj manager block does not contain exactly one WriteGrObjBody")
        body_chunk, raw = bodies[0]
        need(raw, 0, 61, "WriteGrObjBody instance")
        bounds = tuple(s32(raw, offset) for offset in (35, 39, 43, 47))
        count = u16(raw, 59)
        current = saved_optr(raw, 51, manager_handle, "GrObjBody draw head")
        if bool(current) != bool(count):
            fail("GrObjBody draw head and child count disagree")
        children: list[GrObjNode] = []
        for index in range(count):
            assert current is not None
            children.append(self.parse_node(current))
            child_raw = self.block(current[0]).chunk(current[1])
            go = u16(child_raw, 4)
            link_chunk, link_relocation = u16(child_raw, go), u16(child_raw, go + 2)
            if index == count - 1:
                if not link_chunk & 1:
                    fail("final GrObjBody child lacks its last-link flag")
                parent = saved_vm_handle(link_relocation, current[0], "last GrObjBody child link")
                if (parent, link_chunk & ~1) != (manager_handle, body_chunk):
                    fail("final GrObjBody child does not link back to its body")
            else:
                if link_chunk & 1:
                    fail("GrObjBody child list ends before its saved count")
                current = saved_optr(child_raw, go, current[0], "GrObjBody child link")
                if current is None:
                    fail("GrObjBody child list contains a null link")
        return GrObjBody(bounds, tuple(children))


@dataclass
class GeoWriteDocument:
    vm: VMFile
    width: int
    height: int
    total_pages: int
    display_mode: int
    sections: list[Section]
    articles: list[Article]
    char_attrs: dict[int, CharAttr]
    para_attrs: dict[int, ParaAttr]
    graphic_elements: list[VisTextGraphic | None] | dict[int, VisTextGraphic | None]
    type_elements: list[bytes]
    grobj_block: int
    grobj_body: GrObjBody | None = None
    grobj_line_attrs: dict[int, GrObjLineAttr] = field(default_factory=dict)
    grobj_area_attrs: dict[int, GrObjAreaAttr] = field(default_factory=dict)
    feature_notes: list[str] = field(default_factory=list)

    @classmethod
    def parse(cls, raw: bytes) -> "GeoWriteDocument":
        vm = VMFile(raw)
        if vm.legacy:
            return parse_legacy_document(vm)
        map_lmem = LMemBlock(vm.block(vm.map_handle))
        m = map_lmem.data
        need(m, 0, 100, "GeoWrite MapBlockHeader")
        char_elements_handle = u16(m, 16)
        para_elements_handle = u16(m, 18)
        graphic_elements_handle = u16(m, 20)
        type_elements_handle = u16(m, 22)
        name_elements_handle = u16(m, 24)
        text_styles_handle = u16(m, 26)
        line_elements_handle = u16(m, 28)
        area_elements_handle = u16(m, 30)
        graphic_styles_handle = u16(m, 32)
        grobj_block = u16(m, 34)
        total_pages = u16(m, 38)
        width, height = u16(m, 40), u16(m, 42)
        display_mode = u16(m, 46)
        if not total_pages or not width or not height:
            fail("GeoWrite map has an invalid page count or page size")
        if display_mode > 4:
            fail("GeoWrite map has an invalid display mode")
        if map_lmem.handle_count < 2:
            fail("GeoWrite map lacks its section/article arrays")

        section_data_size, section_elements = name_array(map_lmem.chunk(map_lmem.handles[0]))
        if section_data_size != 57:
            fail(f"SectionArray data size is {section_data_size}, expected 57")
        sections: list[Section] = []
        for e in section_elements:
            if e[2] == 0xFF:
                continue
            need(e, 0, 60, "SectionArrayElement")
            master_count = u16(e, 7)
            if master_count > 4:
                fail("section has more than four master pages")
            masters = tuple(u16(e, 23 + i * 2) for i in range(master_count))
            sections.append(
                Section(
                    decode_geos(e[60:]).rstrip("\0"),
                    u16(e, 3),
                    u16(e, 5),
                    masters,
                    u16(e, 9),
                    u16(e, 11) / 8.0,
                    u16(e, 13) / 8.0,
                    tuple(u16(e, 15 + i * 2) / 8.0 for i in range(4)),
                    u16(e, 42),
                )
            )
        if not sections:
            fail("GeoWrite document has no section")

        article_data_size, article_elements = name_array(map_lmem.chunk(map_lmem.handles[1]))
        if article_data_size != 34:
            fail(f"ArticleArray data size is {article_data_size}, expected 34")

        char_elements = element_array(vm, char_elements_handle, 0)
        para_elements = element_array(vm, para_elements_handle, 1)
        graphic_element_bytes = element_array(vm, graphic_elements_handle, 2)
        type_elements = element_array(vm, type_elements_handle, 3)
        # These arrays are parsed and validated even where the PDF renderer does not consume them.
        validate_name_array_block(vm, name_elements_handle)
        validate_name_array_block(vm, text_styles_handle)
        line_element_bytes = gr_obj_element_array(vm, line_elements_handle, "GrObj line attributes")
        area_element_bytes = gr_obj_element_array(vm, area_elements_handle, "GrObj area attributes")
        if graphic_styles_handle:
            LMemBlock(vm.block(graphic_styles_handle))

        articles: list[Article] = []
        for article_element in article_elements:
            if article_element[2] == 0xFF:
                continue
            need(article_element, 0, 37, "ArticleArrayElement")
            article_handle = u16(article_element, 3)
            article_name = decode_geos(article_element[37:]).rstrip("\0")
            article_lmem = LMemBlock(vm.block(article_handle), required_type=2)
            if article_lmem.handle_count < 3:
                fail("article object block lacks fixed chunks")
            object_chunk = article_lmem.chunk(article_lmem.handles[1])
            region_chunk = article_lmem.chunk(article_lmem.handles[2])
            need(object_chunk, 0, 124, "VisLargeText object instance")
            # VisTextInstance starts at the protocol-3 class offset; the
            # inherited byte fields make these saved words intentionally odd.
            text_handle = u16(object_chunk, 23)
            char_runs_handle = u16(object_chunk, 25)
            para_runs_handle = u16(object_chunk, 27)
            lines_handle = u16(object_chunk, 31)
            text_array = huge_array(vm, text_handle)
            if text_array.element_size != 1:
                fail("article text HugeArray is not byte-sized")
            raw_text = b"".join(text_array.elements)
            if not raw_text or raw_text[-1] != 0 or b"\0" in raw_text[:-1]:
                fail("article text does not have exactly one terminal NUL")

            type_runs_handle = graphic_runs_handle = 0
            pos = 124
            while pos < len(object_chunk):
                need(object_chunk, pos, 2, "object variable-data type")
                data_type_with_flags = u16(object_chunk, pos)
                data_type = data_type_with_flags & 0xFFFC
                if data_type_with_flags & 2:
                    need(object_chunk, pos, 4, "object variable-data header")
                    entry_size = u16(object_chunk, pos + 2)
                    if entry_size < 4 or entry_size & 1:
                        fail("invalid object variable-data entry size")
                    need(object_chunk, pos, entry_size, "object variable-data entry")
                    payload = object_chunk[pos + 4 : pos + entry_size]
                else:
                    entry_size = 2
                    payload = b""
                if data_type == 0x4800:
                    if len(payload) != 2:
                        fail("ATTR_VIS_TEXT_TYPE_RUNS has invalid size")
                    type_runs_handle = u16(payload, 0)
                elif data_type == 0x4804:
                    if len(payload) != 2:
                        fail("ATTR_VIS_TEXT_GRAPHIC_RUNS has invalid size")
                    graphic_runs_handle = u16(payload, 0)
                pos += entry_size
            if pos != len(object_chunk):
                fail("object variable-data entries do not fill their chunk")

            line_array = huge_array(vm, lines_handle)
            if line_array.element_size != 0:
                fail("line-info HugeArray is not variable-sized")
            lines = [parse_line(e) for e in line_array.elements]
            if sum(line.char_count for line in lines) != len(raw_text) - 1:
                fail("LineInfo character counts do not cover article text before its terminal NUL")
            regions = parse_regions(region_chunk)
            if sum(r.line_count for r in regions) != len(lines):
                fail("article region line counts do not cover LineInfo")
            if sum(r.char_count for r in regions) != len(raw_text) - 1:
                fail("article region character counts do not cover text")
            char_runs = run_array(vm, char_runs_handle, char_elements_handle)
            para_runs = run_array(vm, para_runs_handle, para_elements_handle)
            type_runs = run_array(vm, type_runs_handle, type_elements_handle) if type_runs_handle else []
            graphic_runs = (
                run_array(vm, graphic_runs_handle, graphic_elements_handle, require_zero=False)
                if graphic_runs_handle
                else []
            )
            for label, runs, elements in (
                ("character", char_runs, char_elements),
                ("paragraph", para_runs, para_elements),
                ("type", type_runs, type_elements),
                ("graphic", graphic_runs, graphic_element_bytes),
            ):
                for run in runs[:-1]:
                    if run.position >= len(raw_text):
                        fail(f"{label} run position lies past article text")
                    if run.token >= len(elements) or len(elements[run.token]) < 3 or elements[run.token][2] == 0xFF:
                        fail(f"{label} run references missing element token {run.token}")
            graphic_positions = [run.position for run in graphic_runs[:-1]]
            text_graphic_positions = [i for i, value in enumerate(raw_text[:-1]) if value == 0x1A]
            if graphic_positions != text_graphic_positions:
                fail("graphic runs do not correspond one-for-one with embedded-graphic characters")
            articles.append(
                Article(
                    article_name,
                    raw_text,
                    char_runs,
                    para_runs,
                    type_runs,
                    graphic_runs,
                    lines,
                    regions,
                )
            )
        if not articles:
            fail("GeoWrite document has no article")

        graphic_elements = parse_graphic_elements(vm, graphic_element_bytes)
        char_attrs = parse_char_attrs(char_elements)
        para_attrs = parse_para_attrs(para_elements)
        line_attrs = parse_gr_obj_line_attrs(line_element_bytes)
        area_attrs = parse_gr_obj_area_attrs(area_element_bytes)
        grobj_body = None
        if grobj_block:
            grobj_body = GrObjParser(
                vm, line_attrs, area_attrs,
                char_elements_handle, para_elements_handle,
                type_elements_handle, graphic_elements_handle,
                char_attrs, para_attrs, type_elements, graphic_elements,
            ).parse_body(grobj_block)

        notes: list[str] = []
        if grobj_block:
            notes.append("page drawing-layer objects are parsed and rendered")
        if any(section.master_pages for section in sections):
            notes.append("master-page objects are present")
        referenced_graphics = [
            graphic_elements[run.token]
            for article in articles
            for run in article.graphic_runs[:-1]
        ]
        if any(
            graphic is not None and graphic.gstring is not None and graphic.gstring.bitmaps
            for graphic in referenced_graphics
        ):
            notes.append("embedded bitmap graphics are rendered")
        if any(
            graphic is not None
            and graphic.gstring is not None
            and any(
                0x20 <= element[0] <= 0x5F and element[0] not in (0x4C, 0x4D, 0x50, 0x51, 0x54)
                for element in graphic.gstring.elements
            )
            for graphic in referenced_graphics
        ):
            notes.append("non-bitmap GString drawing commands are present")
        if any(graphic is not None and graphic.graphic_type == 1 for graphic in referenced_graphics):
            notes.append("application-variable text graphics are present")
        if any(region.text_region != (0, 0) or region.inherited_text_region != (0, 0) for article in articles for region in article.regions):
            notes.append("non-rectangular text-flow regions are present")

        return cls(
            vm,
            width,
            height,
            total_pages,
            display_mode,
            sections,
            articles,
            char_attrs,
            para_attrs,
            graphic_elements,
            type_elements,
            grobj_block,
            grobj_body,
            line_attrs,
            area_attrs,
            notes,
        )


def legacy_vm_handle(relocation_id: int, what: str) -> int:
    """Turn an ORS_NON_STATE_VM relocation ID into its 12-byte VM handle."""
    if relocation_id & 0xF000 != 0x7000:
        fail(f"{what} is not an old non-state-VM relocation")
    return 32 + (relocation_id & 0x0FFF) * 12


def legacy_element_chunk(vm: VMFile, handle: int, what: str) -> bytes:
    lmem = LMemBlock(vm.block(handle), required_type=2)
    active = [h for h in lmem.handles if u16(lmem.data, h) not in (0, 0xFFFF)]
    if active != [0x20, 0x22] or len(lmem.chunk(0x20)) != 2:
        fail(f"{what} is not a canonical old ElementArray object block")
    return lmem.chunk(0x22)


def validate_legacy_element_free_list(chunk: bytes, element_size: int, what: str) -> None:
    """Account for every fixed old ElementArray entry, active or free."""
    count = u16(chunk, 0)
    expected_tokens = {6 + index * element_size for index in range(count)}
    free_tokens = {token for token in expected_tokens if u16(chunk, token) == 0}
    encountered: set[int] = set()
    token = u16(chunk, 2)
    while token:
        if token not in expected_tokens or token in encountered:
            fail(f"{what} free list is cyclic or points outside the array")
        if u16(chunk, token):
            fail(f"{what} free list points to an active element")
        encountered.add(token)
        token = u16(chunk, token + 2)
    if encountered != free_tokens:
        fail(f"{what} does not account for every free element")
    if u16(chunk, 4):
        fail(f"{what} has a nonzero insertion token")


def parse_legacy_char_attrs(chunk: bytes) -> dict[int, CharAttr]:
    need(chunk, 0, 6, "old character ElementArray")
    count = u16(chunk, 0)
    if len(chunk) != 6 + count * 18:
        fail("old character ElementArray has inconsistent length")
    validate_legacy_element_free_list(chunk, 18, "old character ElementArray")
    result: dict[int, CharAttr] = {}
    for index in range(count):
        token = 6 + index * 18
        element = chunk[token : token + 18]
        if not u16(element, 0):
            continue
        if element[16:18] != b"\0\0":
            fail("old OVisTextStyle reserved bytes are nonzero")
        color_info = element[11]
        if color_info & 0x80:
            color = (element[10] / 255.0, element[12] / 255.0, element[13] / 255.0)
        else:
            color = tuple(value / 255.0 for value in geos_palette_color(element[10]))
        result[token] = CharAttr(
            0xFFFF,
            u16(element, 4),
            wbfixed(element, 6),
            element[9],
            color,
            s16(element, 14),
            100,
            100,
            0,
        )
    return result


def parse_legacy_para_attrs(chunk: bytes) -> dict[int, ParaAttr]:
    need(chunk, 0, 6, "old ruler ElementArray")
    count = u16(chunk, 0)
    if u16(chunk, 4):
        fail("old ruler ElementArray has a nonzero insertion token")
    offset = 6
    result: dict[int, ParaAttr] = {}
    for _ in range(count):
        need(chunk, offset, 36, "old OVisTextRuler")
        tab_count = chunk[offset + 31]
        size = 36 + tab_count * 4
        need(chunk, offset, size, "old OVisTextRuler tabs")
        if chunk[offset + 32 : offset + 36] != b"\0\0\0\0":
            fail("old OVisTextRuler reserved bytes are nonzero")
        token = u16(chunk, offset + 4)
        if u16(chunk, offset):
            if token in result:
                fail("duplicate old ruler token")
            tabs = tuple(
                (
                    float(u16(chunk, offset + 36 + i * 4)),
                    chunk[offset + 38 + i * 4],
                    0,
                    0,
                    0,
                    chunk[offset + 39 + i * 4],
                )
                for i in range(tab_count)
            )
            result[token] = ParaAttr(
                0xFFFF,
                u16(chunk, offset + 6),
                chunk[offset + 12],
                float(u16(chunk, offset + 13)),
                float(u16(chunk, offset + 15)),
                float(u16(chunk, offset + 17)),
                chunk[offset + 20] + chunk[offset + 19] / 256.0,
                float(u16(chunk, offset + 21)),
                chunk[offset + 24] + chunk[offset + 23] / 256.0,
                chunk[offset + 26] + chunk[offset + 25] / 256.0,
                tabs,
            )
        offset += size
    if offset != len(chunk):
        fail("bytes remain after the old ruler ElementArray")
    return result


def parse_legacy_gstring(vm: VMFile, first_handle: int) -> GStringGraphic:
    """Validate the linked storage envelope of a GeoWrite 1.x GString."""
    handle = first_handle
    seen: set[int] = set()
    payload = bytearray()
    while handle:
        if handle in seen:
            fail("old GString VM chain is cyclic")
        seen.add(handle)
        block = vm.block(handle).data
        need(block, 0, 4, "old GString VM-chain header")
        used = u16(block, 2)
        if used < 4 or used > len(block):
            fail("old GString VM-chain used-size is invalid")
        payload.extend(block[4:used])
        handle = u16(block, 0)
    if not payload or payload[-1] != 0:
        fail("old GString does not end with GR_END_STRING")
    # parse_legacy_gstring_elements upgrades this raw stream to protocol-2
    # element records and extracts any bitmaps.
    return parse_legacy_gstring_elements(bytes(payload))


def legacy_trans_matrix_bytes(raw: bytes) -> bytes:
    """Expand a 1.x six-WWFixed matrix to the 2.x 28-byte TransMatrix."""
    need(raw, 0, 24, "old GString transform")
    result = bytearray(raw[:16])
    for offset in (16, 20):
        result.extend(raw[offset : offset + 2])
        result.extend(struct.pack("<i", s16(raw, offset + 2)))
    return bytes(result)


def parse_legacy_bitmap_slice(raw: bytes) -> tuple[BitmapSlice, bytes]:
    """Parse a 1.x bitmap slice and return it plus its canonical 2.x bytes."""
    need(raw, 0, 6, "old Bitmap")
    if not raw[5] & 0x08:
        parsed = parse_bitmap_slice(raw)
        return parsed, raw
    need(raw, 0, 20, "old CBitmap")
    data_offset, palette_offset = u16(raw, 12), u16(raw, 14)
    # GeoWrite 1.x reserved 48 bytes for a 16-entry RGB palette even when
    # BMT_PALETTE was clear.  ConvertGString deliberately ignored that table.
    if (data_offset, palette_offset) not in ((20, 0), (68, 20)):
        fail("old CBitmap has an invalid data/palette layout")
    need(raw, data_offset, 0, "old CBitmap pixel data")
    canonical = bytearray(
        raw[:12] + struct.pack("<HH", 20, 0) + raw[16:20] + raw[data_offset:]
    )
    canonical[5] &= ~0x40
    parsed = parse_bitmap_slice(bytes(canonical))
    return parsed, bytes(canonical)


def parse_legacy_gstring_elements(payload: bytes) -> GStringGraphic:
    """Parse and normalize every opcode in a VM-based GeoWrite 1.x GString."""
    fixed_sizes = {
        2: 0, 4: 0, 5: 0, 6: 0, 7: 4, 8: 8, 9: 8,
        10: 24, 11: 24, 12: 0, 13: 8, 14: 4, 15: 8, 16: 4,
        17: 6, 18: 2, 19: 6, 20: 2, 23: 4, 24: 0,
        29: 5, 30: 1, 36: 8, 40: 8, 41: 4, 46: 8,
        47: 1, 48: 4, 49: 4, 50: 3, 51: 1, 52: 1, 53: 2,
        54: 1, 55: 1, 56: 10, 57: 4, 58: 2, 59: 3, 60: 1,
        61: 1, 62: 6, 63: 3, 64: 1, 65: 1, 66: 2, 67: 2,
        68: 3, 69: 20, 70: 5, 71: 0, 72: 2, 73: 2, 74: 2,
        75: 2, 76: 2, 77: 1, 78: 1, 79: 8, 80: 1, 81: 8,
        82: 1, 83: 8, 85: 2, 86: 0, 87: 0, 88: 10, 89: 10,
    }
    opcode_map = {
        0: 0x00, 1: 0x01, 2: 0x02, 3: 0x0E, 4: 0x60, 5: 0x61,
        6: 0x0F, 7: 0x10, 8: 0x11, 9: 0x12, 10: 0x15, 11: 0x13,
        12: 0x16, 13: 0x20, 14: 0x21, 15: 0x2C, 16: 0x2D,
        17: 0x23, 18: 0x24, 19: 0x25, 20: 0x26, 23: 0x37,
        24: 0x38, 29: 0x3A, 30: 0x3B, 31: 0x3C, 32: 0x3D,
        33: 0x3E, 35: 0x27, 36: 0x35, 38: 0x30, 39: 0x36,
        40: 0x42, 41: 0x43, 45: 0x47, 46: 0x48, 47: 0x62,
        48: 0x64, 49: 0x63, 50: 0x69, 51: 0x6A, 52: 0x6B,
        53: 0x6C, 54: 0x6D, 55: 0x6E, 56: 0x6F, 57: 0x70,
        58: 0x71, 59: 0x75, 60: 0x76, 61: 0x77, 62: 0x78,
        63: 0x7D, 64: 0x7E, 65: 0x7F, 66: 0x80, 67: 0x81,
        68: 0x82, 69: 0x83, 70: 0x84, 76: 0x6C, 77: 0x6D,
        78: 0x72, 79: 0x73, 80: 0x79, 81: 0x7A, 82: 0x85,
        83: 0x86, 84: 0x74, 85: 0x87, 86: 0x18, 87: 0x17,
        # The original Convert library intentionally discarded both old
        # clip-rectangle opcodes because their 1.x flag semantics differ.
        88: 0x55, 89: 0x55,
    }
    elements: list[bytes] = []
    bitmaps: dict[int, BitmapRaster] = {}
    continuations: set[int] = set()
    cursor = 0
    while cursor < len(payload):
        start = cursor
        opcode = payload[cursor]
        cursor += 1
        if opcode == 0:
            if cursor != len(payload):
                fail("old GString contains an early GR_END_STRING")
            elements.append(b"\0")
            break
        if opcode in (21, 22, 37, 42, 43, 44):
            fail(f"old GString uses opcode {opcode}, unsupported by the original GeoWorks converter")
        if opcode in (27, 28, 34):
            fail("old GString contains a saved-memory pointer drawing opcode")

        if opcode == 1:
            need(payload, cursor, 2, "old GString comment length")
            count = u16(payload, cursor)
            cursor += 2 + count
        elif opcode == 3:
            need(payload, cursor, 4, "old GString escape header")
            count = u16(payload, cursor + 2)
            cursor += 4 + count
        elif opcode in (25, 26):
            x = y = 0
            if opcode == 25:
                need(payload, cursor, 4, "old positioned bitmap coordinates")
                x, y = s16(payload, cursor), s16(payload, cursor + 2)
                cursor += 4
            slices: list[BitmapSlice] = []
            canonical_slices: list[bytes] = []
            covered = 0
            total_height: int | None = None
            while total_height is None or covered < total_height:
                need(payload, cursor, 2, "old bitmap slice size")
                byte_count = u16(payload, cursor)
                need(payload, cursor + 2, byte_count, "old bitmap slice")
                parsed_slice, canonical = parse_legacy_bitmap_slice(
                    payload[cursor + 2 : cursor + 2 + byte_count]
                )
                if total_height is None:
                    total_height = parsed_slice.height
                if parsed_slice.start_scan != covered:
                    fail("old CBitmap slices are not contiguous from scan zero")
                covered += parsed_slice.scan_count
                slices.append(parsed_slice)
                canonical_slices.append(canonical)
                cursor += 2 + byte_count
            if total_height is None or covered != total_height:
                fail("old CBitmap slices do not cover their declared height")
            fill = (slices[0].bitmap_type & 7) == 0
            command_opcode = 0x4C if fill and opcode == 25 else (0x4D if fill else 0x50) if opcode == 25 else 0x51
            first_raw = canonical_slices[0]
            if opcode == 25:
                command = bytes((command_opcode,)) + struct.pack("<hhH", x, y, len(first_raw)) + first_raw
            else:
                command = bytes((command_opcode,)) + struct.pack("<H", len(first_raw)) + first_raw
            bitmap_index = len(elements)
            elements.append(command)
            bitmaps[bitmap_index] = decode_bitmap(slices, fill)
            for canonical in canonical_slices[1:]:
                continuations.add(len(elements))
                elements.append(bytes((0x54,)) + struct.pack("<H", len(canonical)) + canonical)
            continue
        elif opcode in (31, 32):
            if opcode == 31:
                need(payload, cursor, 6, "old positioned draw-text header")
                count = u16(payload, cursor + 4)
                cursor += 6 + count
            else:
                need(payload, cursor, 2, "old current-position draw-text header")
                count = u16(payload, cursor)
                cursor += 2 + count
        elif opcode == 33:
            need(payload, cursor, 2, "old draw-text-field byte count")
            byte_count = u16(payload, cursor)
            if byte_count < 50:
                fail("old draw-text-field fixed data and first style run are truncated")
            data_start = cursor + 2
            first_run = data_start + byte_count - 22
            string_length = byte_count - 50
            need(payload, data_start, byte_count, "old draw-text-field data")
            run_cursor = first_run
            covered = 0
            while covered < string_length:
                need(payload, run_cursor, 22, "old draw-text-field style run")
                run_count = u16(payload, run_cursor)
                if not run_count:
                    fail("old draw-text-field has a zero-length style run")
                covered += run_count
                run_cursor += 22
            if covered != string_length:
                fail("old draw-text-field style runs do not cover its string")
            cursor = run_cursor
        elif opcode in (35, 39):
            need(payload, cursor, 2, "old coordinate-list count")
            count = u16(payload, cursor)
            cursor += 2 + count * 4
        elif opcode in (38, 45):
            need(payload, cursor, 3, "old spline/polygon header")
            count = u16(payload, cursor + 1)
            cursor += 3 + count * 4
        elif opcode == 84:
            need(payload, cursor, 3, "old custom-line-style header")
            count = u16(payload, cursor + 1)
            cursor += 3 + count * 2
        else:
            try:
                cursor += fixed_sizes[opcode]
            except KeyError:
                fail(f"old GString contains undefined opcode 0x{opcode:02x}")
        need(payload, start, cursor - start, "old GString element")

        mapped = opcode_map.get(opcode, 0x55)
        arguments = payload[start + 1 : cursor]
        if opcode in (10, 11):
            arguments = legacy_trans_matrix_bytes(arguments)
        elif opcode == 6:
            arguments = b"\0"
        elements.append(bytes((mapped,)) + arguments)
    if not elements or elements[-1] != b"\0":
        fail("old GString lacks its final GR_END_STRING")
    return GStringGraphic(elements, bitmaps, continuations, True)


def parse_legacy_graphics(vm: VMFile, chunk: bytes) -> dict[int, VisTextGraphic | None]:
    need(chunk, 0, 6, "old graphic ElementArray")
    count = u16(chunk, 0)
    if len(chunk) != 6 + count * 58:
        fail("old graphic ElementArray has inconsistent length")
    validate_legacy_element_free_list(chunk, 58, "old graphic ElementArray")
    result: dict[int, VisTextGraphic | None] = {}
    for index in range(count):
        token = 6 + index * 58
        element = chunk[token : token + 58]
        if not u16(element, 0):
            result[token] = None
            continue
        width, height = u16(element, 4), u16(element, 6)
        graphic_type, flags = element[40], element[41]
        if graphic_type > 3:
            fail(f"old OVisTextGraphic has invalid type {graphic_type}")
        if flags & ~0x80:
            fail("old OVisTextGraphic has unknown flag bits")
        if element[36:40] != b"\0\0\0\0":
            fail("old OVisTextGraphic reserved bytes are nonzero")
        if graphic_type == 2:
            if u16(element, 42) != 0:
                fail("old VM GString stores a nonzero obsolete file handle")
            if u16(element, 46) or any(element[48:58]):
                fail("old VM GString does not use its null-terminated chain/play defaults")
            gstring_handle = u16(element, 44)
            vm.block(gstring_handle)
            # The old stream is parsed separately below; the initial text
            # implementation still preserves its exact saved advance.
            gstring = parse_legacy_gstring(vm, gstring_handle)
            matrix = trans_matrix(element, 8)
        elif graphic_type == 3:
            if u16(element, 42) != 0x4007 or any(element[44:58]):
                fail("old method graphic is not the defined page-number method")
            gstring = None
            matrix = IDENTITY_MATRIX
        elif graphic_type == 0:
            gstring = None
            matrix = trans_matrix(element, 8)
        else:
            fail("old chunk-based GString graphics are not supported")
        result[token] = VisTextGraphic(
            width,
            height,
            1 if graphic_type == 3 else 0,
            0x8000 if flags & 0x80 else 0,
            matrix,
            (0, 0),
            gstring,
        )
    return result


def parse_legacy_run_array(
    vm: VMFile,
    lmem: LMemBlock,
    chunk_handle: int,
    expected_element_handle: int | None,
    what: str,
    require_zero: bool,
) -> list[Run]:
    chunk = lmem.chunk(chunk_handle)
    need(chunk, 0, 14, f"old {what} RunArray")
    if (len(chunk) - 10) % 4:
        fail(f"old {what} RunArray has a partial run")
    element_chunk = u16(chunk, 0)
    element_relocation = u16(chunk, 2)
    name_chunk = u16(chunk, 4)
    name_relocation = u16(chunk, 6)
    if element_relocation:
        element_handle = legacy_vm_handle(element_relocation, f"old {what} element array")
        vm.block(element_handle)
    else:
        element_handle = lmem.vm_block.handle
        if element_chunk and element_chunk not in lmem.handles:
            fail(f"old {what} RunArray has an invalid local ElementArray chunk")
    if expected_element_handle is not None and element_handle != expected_element_handle:
        fail(f"old {what} RunArray references the wrong global ElementArray")
    if expected_element_handle is not None and element_chunk != 0x22:
        fail(f"old {what} RunArray does not reference ElementArray chunk 0x22")
    if name_relocation:
        vm.block(legacy_vm_handle(name_relocation, f"old {what} name array"))
    elif name_chunk and name_chunk not in lmem.handles:
        fail(f"old {what} RunArray has an invalid local name chunk")
    runs = [Run(u16(chunk, pos), u16(chunk, pos + 2)) for pos in range(10, len(chunk), 4)]
    if not runs or runs[-1].position != 0x8000:
        fail(f"old {what} RunArray lacks its 0x8000 terminator")
    if any(a.position >= b.position for a, b in zip(runs, runs[1:])):
        fail(f"old {what} RunArray positions are not ordered")
    if require_zero and len(runs) > 1 and runs[0].position != 0:
        fail(f"old {what} RunArray does not begin at zero")
    return runs


def parse_legacy_lines(
    lmem: LMemBlock,
    lines_handle: int,
    fields_handle: int,
    free_field: int,
    text_length: int,
    x_scale: float,
    y_scale: float,
) -> list[LineInfo]:
    line_data = lmem.chunk(lines_handle)
    field_data = lmem.chunk(fields_handle)
    if not line_data or len(line_data) % 10:
        fail("old line-info chunk is not a sequence of 10-byte records")
    if not field_data or len(field_data) % 13:
        fail("old field-info chunk is not a sequence of 13-byte records")

    chains: list[list[int]] = []
    occupied: set[int] = set()
    for offset in range(0, len(line_data), 10):
        chain: list[int] = []
        field = u16(line_data, offset)
        while field != 0xFFFF:
            if field % 13 or field >= len(field_data) or field in occupied:
                fail("old active field list is cyclic, shared, or out of range")
            occupied.add(field)
            chain.append(field)
            field = u16(field_data, field)
        if not chain:
            fail("old line has no field")
        chains.append(chain)

    field = free_field
    while field != 0xFFFF:
        if field % 13 or field >= len(field_data) or field in occupied:
            fail("old free-field list is cyclic, shared, or out of range")
        occupied.add(field)
        field = u16(field_data, field)
    if occupied != set(range(0, len(field_data), 13)):
        fail("old field records are not all assigned to a line or the free list")

    line_starts = [u16(field_data, chain[0] + 3) for chain in chains]
    if line_starts[0] != 0 or any(a > b for a, b in zip(line_starts, line_starts[1:])):
        fail("old line text positions are not ordered from zero")
    if line_starts[-1] > text_length:
        fail("old line starts beyond the text")

    result: list[LineInfo] = []
    for line_number, chain in enumerate(chains):
        line_offset = line_number * 10
        line_end = line_starts[line_number + 1] if line_number + 1 < len(chains) else text_length
        starts = [u16(field_data, item + 3) for item in chain]
        if starts != sorted(starts) or starts[0] != line_starts[line_number] or starts[-1] > line_end:
            fail("old fields are not ordered within their line")
        ends = starts[1:] + [line_end]
        fields = tuple(
            FieldInfo(
                end - start,
                u16(field_data, item + 5) * x_scale,
                u16(field_data, item + 7) * x_scale,
                field_data[item + 12],
            )
            for item, start, end in zip(chain, starts, ends)
        )
        if any(item.char_count < 0 for item in fields):
            fail("old FieldInfo has a negative inferred character count")
        final_flags = field_data[chain[-1] + 2]
        hyphen_flag = 0x0040 if final_flags & (0x20 | 0x04) else 0
        result.append(
            LineInfo(
                hyphen_flag,
                u16(line_data, line_offset + 4) * y_scale,
                u16(line_data, line_offset + 6) * y_scale,
                s16(line_data, line_offset + 8) * x_scale,
                line_end - line_starts[line_number],
                0.0,
                0,
                fields,
            )
        )
    if sum(line.char_count for line in result) != text_length:
        fail("old line records do not cover the text")
    return result


def legacy_link(vm: VMFile, block_handle: int, object_chunk: bytes) -> tuple[int, int, bool]:
    vis_offset = u16(object_chunk, 4)
    need(object_chunk, vis_offset, 17, "old VisInstance")
    target_chunk = u16(object_chunk, vis_offset + 13)
    relocation = u16(object_chunk, vis_offset + 15)
    is_parent = bool(target_chunk & 1)
    target_chunk &= 0xFFFE
    if is_parent:
        return block_handle, target_chunk, True
    if relocation == 0x4000:
        return block_handle, target_chunk, False
    return legacy_vm_handle(relocation, "old visual link"), target_chunk, False


def parse_legacy_text_object(
    vm: VMFile,
    block_handle: int,
    chunk_handle: int,
    page_number: int,
    label: str,
    char_element_handle: int,
    para_element_handle: int,
    graphic_element_handle: int,
    char_attrs: dict[int, CharAttr],
    para_attrs: dict[int, ParaAttr],
    graphics: dict[int, VisTextGraphic | None],
    page_height: int,
    x_scale: float,
    y_scale: float,
) -> Article:
    lmem = LMemBlock(vm.block(block_handle), required_type=2)
    obj = lmem.chunk(chunk_handle)
    need(obj, 0, 87, "old text object")
    if u16(obj, 0) != 0x6000 or u16(obj, 4) != 8 or u16(obj, 6) != 0x57:
        fail("old text object has unexpected master offsets")
    if len(obj) not in (89, 93):
        fail("old GeoWrite text subclass has an unexpected instance size")
    if len(obj) == 89:
        if u16(obj, 2) != 13 or u16(obj, 87) != 0x4000:
            fail("old header/footer text object has invalid subclass data")
    else:
        if u16(obj, 2) != 12:
            fail("old column text object has an invalid class master offset")
        for offset in (87, 89, 91):
            relocation = u16(obj, offset)
            if relocation and relocation & 0xF000 != 0x7000:
                fail("old column text object has an invalid VM relocation")
    left, top, right, bottom = (s16(obj, 8 + i * 2) for i in range(4))
    if right <= left or bottom <= top:
        fail("old text object has invalid visual bounds")
    text = lmem.chunk(u16(obj, 25))
    if not text or text[-1] != 0 or b"\0" in text[:-1]:
        fail("old text chunk does not contain exactly one terminal NUL")
    type_flags = obj[36]
    if type_flags & 0xE0 != 0xE0:
        fail("old single-style/ruler/type text objects are outside GeoWrite's saved-document schema")
    char_runs = parse_legacy_run_array(
        vm, lmem, u16(obj, 27), char_element_handle, "character", True
    )
    para_runs = parse_legacy_run_array(
        vm, lmem, u16(obj, 29), para_element_handle, "paragraph", True
    )
    type_runs = parse_legacy_run_array(vm, lmem, u16(obj, 31), None, "type", True)
    graphic_runs = parse_legacy_run_array(
        vm, lmem, u16(obj, 33), graphic_element_handle, "graphic", False
    )
    text_length = len(text) - 1
    for name, runs, available in (
        ("character", char_runs, char_attrs),
        ("paragraph", para_runs, para_attrs),
        ("graphic", graphic_runs, graphics),
    ):
        for run in runs[:-1]:
            if run.position > text_length or (name == "graphic" and run.position == text_length):
                fail(f"old {name} run lies beyond its text object")
            if run.token not in available or available[run.token] is None:
                fail(f"old {name} run references a missing element")
    graphic_positions = [run.position for run in graphic_runs[:-1]]
    if graphic_positions != [i for i, value in enumerate(text[:-1]) if value == 0x1A]:
        fail("old graphic runs do not match embedded-graphic characters")
    lines = parse_legacy_lines(
        lmem, u16(obj, 54), u16(obj, 56), u16(obj, 58), text_length,
        x_scale, y_scale,
    )
    region = Region(
        text_length,
        len(lines),
        0,
        left * x_scale,
        page_number * page_height + top * y_scale,
        (right - left) * x_scale,
        (bottom - top) * y_scale,
        sum(line.height for line in lines),
        (0, 0),
        0,
        (0, 0),
        (0, 0),
        (0, chunk_handle),
    )
    return Article(label, text, char_runs, para_runs, type_runs, graphic_runs, lines, [region])


def parse_legacy_document(vm: VMFile) -> GeoWriteDocument:
    map_lmem = LMemBlock(vm.block(vm.map_handle), required_type=2)
    if map_lmem.handles != [0x18 + i * 2 for i in range(16)]:
        fail("old GeoWrite map block does not have its 16-handle schema")
    if len(map_lmem.chunk(0x18)) != 16:
        fail("old GeoWrite map object-flags chunk is not 16 bytes")
    if any(u16(map_lmem.data, handle) not in (0, 0xFFFF) for handle in range(0x20, 0x38, 2)):
        fail("old GeoWrite map has an allocated reserved chunk")
    page_chunk = map_lmem.chunk(0x1A)
    master_chunk = map_lmem.chunk(0x1C)
    document_data = map_lmem.chunk(0x1E)
    need(page_chunk, 0, 4, "old page array")
    page_count, page_element_size = u16(page_chunk, 0), u16(page_chunk, 2)
    if not page_count or page_element_size != 30 or len(page_chunk) != 4 + page_count * 30:
        fail("old page array has an invalid count, element size, or length")
    need(master_chunk, 0, 4, "old master-page array")
    master_count, master_size = u16(master_chunk, 0), u16(master_chunk, 2)
    if not master_count or master_size != 87 or len(master_chunk) != 4 + master_count * 87:
        fail("old master-page array has an invalid count, element size, or length")
    if len(document_data) != 64:
        fail("old WriteDocumentData is not 64 bytes")

    orientation = document_data[2]
    columns = document_data[3]
    if orientation > 1 or not 1 <= columns <= 4:
        fail("old document has invalid orientation or column count")
    paging_type, title_page = u16(document_data, 6), u16(document_data, 8)
    if paging_type > 1 or title_page > 1:
        fail("old document has an invalid paging or title-page value")
    if master_count != paging_type + 1:
        fail("old master-page count does not agree with the paging type")
    attrs = u16(document_data, 18)
    if attrs & ~0xC000:
        fail("old WriteDocumentData has unknown attribute bits")
    if document_data[30] & 0x7F or any(document_data[35:64]):
        fail("old WriteDocumentData has nonzero reserved flag bits or bytes")
    if attrs & 0x4000:
        width, height = u16(document_data, 31), u16(document_data, 33)
    else:
        packed_size = u16(document_data, 0)
        width, height = (packed_size & 0xFF) * 9, (packed_size >> 8) * 9
    if orientation:
        width, height = height, width
    if not width or not height:
        fail("old document has a zero page dimension")
    margins = tuple(float(u16(document_data, 10 + i * 2)) for i in range(4))
    if margins[0] + margins[2] >= width or margins[1] + margins[3] >= height:
        fail("old document margins leave no page body")

    master_elements: list[bytes] = []
    for master_number in range(master_count):
        master = master_chunk[4 + master_number * 87 : 4 + (master_number + 1) * 87]
        if (u16(master, 0), u16(master, 2)) != (width, height):
            fail("old master page size disagrees with WriteDocumentData")
        left, top, right, bottom = (u16(master, offset) for offset in (4, 6, 8, 10))
        if not (left < right <= width and top < bottom <= height):
            fail("old master page has invalid body bounds")
        if master[12] != columns or master[13] != document_data[5] or master[14]:
            fail("old master page has inconsistent column metadata")
        active_columns: list[tuple[int, int, int, int]] = []
        for column_number in range(4):
            column = master[15 + column_number * 18 : 33 + column_number * 18]
            if column_number >= columns:
                if any(column):
                    fail("old master page has data in an unused column slot")
                continue
            if u16(column, 0) or any(column[10:18]):
                fail("old master-page column has nonzero reserved data")
            x, y, column_width, column_height = (
                u16(column, offset) for offset in (2, 4, 6, 8)
            )
            if not column_width or not column_height or x + column_width > width or y + column_height > height:
                fail("old master-page column has invalid bounds")
            active_columns.append((x, y, column_width, column_height))
        if [left, top, right, bottom] != [
            active_columns[0][0],
            active_columns[0][1],
            active_columns[-1][0] + active_columns[-1][2],
            active_columns[0][1] + active_columns[0][3],
        ]:
            fail("old master-page body does not bound its columns")
        if any(
            current[0] + current[2] > following[0]
            or (current[1], current[3]) != (following[1], following[3])
            for current, following in zip(active_columns, active_columns[1:])
        ):
            fail("old master-page columns overlap or have inconsistent vertical bounds")
        master_elements.append(master)

    char_handle, para_handle, graphic_handle, name_handle = (
        u16(document_data, 20 + i * 2) for i in range(4)
    )
    char_chunk = legacy_element_chunk(vm, char_handle, "old character element block")
    para_chunk = legacy_element_chunk(vm, para_handle, "old ruler element block")
    graphic_chunk = legacy_element_chunk(vm, graphic_handle, "old graphic element block")
    name_chunk = legacy_element_chunk(vm, name_handle, "old name element block")
    if name_chunk != b"\0\0\0\0\0\0":
        fail("old GeoWrite name ElementArray is unexpectedly nonempty")
    char_attrs = parse_legacy_char_attrs(char_chunk)
    para_attrs = parse_legacy_para_attrs(para_chunk)
    graphics = parse_legacy_graphics(vm, graphic_chunk)

    articles: list[Article] = []
    page_handles: set[int] = set()
    column_handles: set[int] = set()
    column_links: list[tuple[int, int, int, int]] = []
    legacy_scale: tuple[float, float] | None = None
    for page_number in range(page_count):
        element = page_chunk[4 + page_number * 30 : 34 + page_number * 30]
        page_handle = u16(element, 0)
        if u16(element, 6) & ~0x8000 or any(element[20:30]):
            fail("old page-array element has unknown attributes or nonzero reserved bytes")
        if not u16(element, 2) or not u16(element, 4):
            fail("old page-array element has a zero saved display size")
        if page_handle in page_handles:
            fail("old page array repeats a page object block")
        page_handles.add(page_handle)
        page_lmem = LMemBlock(vm.block(page_handle), required_type=2)
        page_obj = page_lmem.chunk(0x22)
        if len(page_obj) != 104:
            fail("old page-content object does not have its 104-byte class instance")
        if (
            (u16(page_obj, 0), u16(page_obj, 2), u16(page_obj, 4), u16(page_obj, 6))
            != (0x6000, 8, 8, 94)
        ):
            fail("old page-content object has invalid class master offsets")
        master = master_elements[page_number % master_count]
        if page_obj[94:102] != master[4:12] or u16(page_obj, 102) & ~0x0002:
            fail("old page-content subclass does not agree with its master-page body")
        page_left, page_top, page_right, page_bottom = (
            s16(page_obj, 8 + i * 2) for i in range(4)
        )
        if page_left != 0 or page_top != 0 or page_right <= 0 or page_bottom <= 0:
            fail("old page-content object has invalid coordinate bounds")
        x_scale = width / page_right
        y_scale = height / page_bottom
        if legacy_scale is None:
            legacy_scale = (x_scale, y_scale)
        elif not (
            math.isclose(x_scale, legacy_scale[0], rel_tol=0, abs_tol=1e-12)
            and math.isclose(y_scale, legacy_scale[1], rel_tol=0, abs_tol=1e-12)
        ):
            fail("old pages use inconsistent saved coordinate scales")
        first_child = u16(page_obj, 8 + 17)
        first_child_reloc = u16(page_obj, 8 + 19)
        if first_child_reloc != 0x4000:
            fail("old page header is not in its page object block")
        header_handle = first_child
        header_obj = page_lmem.chunk(header_handle)
        footer_block, footer_handle, parent = legacy_link(vm, page_handle, header_obj)
        if parent or footer_block != page_handle:
            fail("old header does not link to a same-block footer")
        for object_handle, object_label in ((header_handle, "header"), (footer_handle, "footer")):
            article = parse_legacy_text_object(
                vm, page_handle, object_handle, page_number,
                f"page {page_number + 1} {object_label}", char_handle, para_handle,
                graphic_handle, char_attrs, para_attrs, graphics, height, x_scale, y_scale,
            )
            article_region = article.regions[0]
            local_top = article_region.y - page_number * height
            if (
                len(article.raw_text) > 1
                and local_top < height
                and local_top + article_region.height > 0
            ):
                articles.append(article)

        footer_obj = page_lmem.chunk(footer_handle)
        next_block, next_chunk, parent = legacy_link(vm, page_handle, footer_obj)
        if parent:
            fail("old page has no text column")
        for column_number in range(columns):
            if next_block in page_handles or next_block in column_handles:
                fail("old column chain contains a repeated object block")
            column_handles.add(next_block)
            column_lmem = LMemBlock(vm.block(next_block), required_type=2)
            column_obj = column_lmem.chunk(next_chunk)
            column_links.append(
                (next_block, page_handle, u16(column_obj, 89), u16(column_obj, 91))
            )
            article = parse_legacy_text_object(
                vm, next_block, next_chunk, page_number,
                f"page {page_number + 1} column {column_number + 1}", char_handle,
                para_handle, graphic_handle, char_attrs, para_attrs, graphics, height,
                x_scale, y_scale,
            )
            articles.append(article)
            next_block, next_chunk, parent = legacy_link(vm, next_block, column_obj)
            if column_number + 1 < columns and parent:
                fail("old column chain ends before the declared column count")
        if not parent:
            fail("old column chain continues past the declared column count")

    for index, (column_block, owning_page, previous_relocation, next_relocation) in enumerate(column_links):
        column_obj = LMemBlock(vm.block(column_block), required_type=2).chunk(0x22)
        if legacy_vm_handle(u16(column_obj, 87), "old column owner page") != owning_page:
            fail("old column subclass points to the wrong owning page")
        expected_previous = column_links[index - 1][0] if index else 0
        expected_next = column_links[index + 1][0] if index + 1 < len(column_links) else 0
        actual_previous = (
            legacy_vm_handle(previous_relocation, "old previous-column link")
            if previous_relocation else 0
        )
        actual_next = (
            legacy_vm_handle(next_relocation, "old next-column link")
            if next_relocation else 0
        )
        if (actual_previous, actual_next) != (expected_previous, expected_next):
            fail("old column subclass links do not form the document-wide column chain")

    assert legacy_scale is not None
    scale_matrix: Matrix = (legacy_scale[0], 0.0, 0.0, legacy_scale[1], 0.0, 0.0)
    for graphic in graphics.values():
        if graphic is not None:
            graphic.width *= legacy_scale[0]
            graphic.height *= legacy_scale[1]
            graphic.matrix = multiply_matrix(scale_matrix, graphic.matrix)

    section = Section(
        "GeoWrite 1.x document",
        attrs,
        0,
        (),
        columns,
        float(document_data[5]),
        float(document_data[4]),
        margins,
        page_count,
    )
    referenced = [graphics[run.token] for article in articles for run in article.graphic_runs[:-1]]
    notes = ["GeoWrite 1.x protocol-1 document"]
    if any(item is not None and item.gstring is not None for item in referenced):
        notes.append("legacy embedded GString bitmap, text, and vector graphics are rendered")
    if any(item is not None and item.graphic_type == 1 for item in referenced):
        notes.append("legacy page-number variables are rendered")
    return GeoWriteDocument(
        vm, width, height, page_count, 0, [section], articles, char_attrs,
        para_attrs, graphics, [], 0, None, {}, {}, notes,
    )


def run_token_at(runs: Sequence[Run], position: int) -> int:
    if not runs:
        return 0
    lo, hi = 0, len(runs) - 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if runs[mid].position <= position:
            lo = mid
        else:
            hi = mid
    return runs[lo].token


def font_face(attr: CharAttr) -> tuple[str, int, int]:
    # FontID's low twelve bits identify a face, not merely a family.  Prefer
    # the matching fonts shipped with the conversion environment for the
    # common PC/GEOS faces; use the FontID family only when that face is not
    # available here.
    exact_faces = {
        0x1000: "Nimbus Roman",       # FID_NIMBUS_URW_ROMAN
        0x1200: "Nimbus Sans",        # FID_NIMBUS_URW_SANS
        0x1400: "Z003",               # FID_NIMBUS_ZAPF_CHANCERY
        0x1403: "ParkAvenue",         # FID_NIMBUS_PARK_AVENUE
        0x1604: "Cooper",             # FID_NIMBUS_COOPER_C_BLACK
        0x1605: "Blippo",             # FID_NIMBUS_BLIPPO_C_BLACK
        0x160B: "Old-Town",           # FID_NIMBUS_OLD_TOWN
        0x160F: "ArnoldBoecklin",     # FID_NIMBUS_ARNOLD_BOCKLIN
        0x1800: "Standard Symbols PS", # FID_NIMBUS_URW_SYMBOLPS
        0x1801: "D050000L",           # FID_NIMBUS_DINGBATS
        0x1A00: "Nimbus Mono PS",     # FID_NIMBUS_URW_MONO
    }
    family_code = attr.font_id & 0x0E00
    families = {
        0x0000: "Nimbus Roman",
        0x0200: "Nimbus Sans",
        0x0400: "Z003",
        0x0600: "Nimbus Sans",
        0x0800: "Standard Symbols PS",
        0x0A00: "Nimbus Mono PS",
        0x0C00: "Nimbus Sans",
        0x0E00: "Nimbus Sans",
    }
    slant = cairo.FONT_SLANT_ITALIC if attr.styles & 0x10 else cairo.FONT_SLANT_NORMAL
    weight = cairo.FONT_WEIGHT_BOLD if (attr.styles & 0x20 or attr.weight >= 125) else cairo.FONT_WEIGHT_NORMAL
    return exact_faces.get(attr.font_id, families[family_code]), slant, weight


def display_text(raw: bytes, line_flags: int) -> str:
    output: list[str] = []
    for value in raw:
        if value in (0x00, 0x09, 0x0B, 0x0C, 0x0D, 0x19, 0x1A):
            continue
        if value == 0x1B:
            output.append("\u2009")
        elif value == 0x1C:
            output.append("\u2002")
        elif value == 0x1D:
            output.append("\u2003")
        elif value == 0x1E:
            output.append("\u2011")
        elif value == 0x1F:
            continue
        else:
            output.append(decode_geos(bytes((value,))))
    if line_flags & 0x00C0:
        output.append("-")
    return "".join(output)


def text_extents_advance(extents: object) -> float:
    return float(getattr(extents, "x_advance", extents[4]))


def track_kerning_increment(point_size: float, degree: int) -> float:
    """Return PC/GEOS' BBFixed per-character track-kerning increment."""
    rounded_size = math.floor(point_size + 0.5)
    return rounded_size * degree / 256.0


@dataclass(frozen=True)
class ClipRectangle:
    matrix: Matrix
    left: float
    top: float
    right: float
    bottom: float


@dataclass(frozen=True)
class ClipPrimitive:
    matrix: Matrix
    opcode: int
    element: bytes


ClipShape = ClipRectangle | ClipPrimitive


def combine_clip(
    clips: list[list[ClipShape]],
    shapes: list[ClipShape],
    operation: int,
) -> list[list[ClipShape]]:
    if operation == 0:  # PCT_NULL
        return []
    if operation == 1:  # PCT_REPLACE
        return [shapes]
    if operation == 2:  # PCT_UNION
        if len(clips) > 1:
            fail("GString requests a clip union after an intersection")
        existing = clips[0] if clips else []
        return [existing + shapes]
    if operation == 3:  # PCT_INTERSECTION
        return clips + [shapes]
    fail(f"GString has invalid PathCombineType {operation}")


def apply_clip_groups(context: cairo.Context, clips: list[list[ClipShape]]) -> None:
    for group in clips:
        context.new_path()
        for shape in group:
            context.save()
            context.transform(cairo.Matrix(*shape.matrix))
            if isinstance(shape, ClipRectangle):
                left, right = sorted((shape.left, shape.right))
                top, bottom = sorted((shape.top, shape.bottom))
                context.rectangle(left, top, right - left, bottom - top)
            elif shape.opcode in (0x2C, 0x42):
                left, top, right, bottom = (s16(shape.element, offset) for offset in (1, 3, 5, 7))
                left, right = sorted((left, right))
                top, bottom = sorted((top, bottom))
                context.rectangle(left, top, right - left, bottom - top)
            elif shape.opcode in (0x35, 0x48, 0x49):
                append_gstring_ellipse(
                    context, s16(shape.element, 1), s16(shape.element, 3),
                    s16(shape.element, 5), s16(shape.element, 7),
                )
            elif shape.opcode in (0x2E, 0x44):
                if len(shape.element) != 11:
                    fail("GString clip rounded rectangle has an invalid size")
                append_rounded_rectangle(
                    context,
                    s16(shape.element, 3), s16(shape.element, 5),
                    s16(shape.element, 7), s16(shape.element, 9),
                    s16(shape.element, 1),
                )
            elif shape.opcode == 0x29:
                append_gstring_arc_three_points(context, shape.element)
            elif shape.opcode == 0x32:
                if len(shape.element) != 17:
                    fail("GString clip curve has an invalid size")
                points = [
                    (float(s16(shape.element, offset)), float(s16(shape.element, offset + 2)))
                    for offset in (1, 5, 9, 13)
                ]
                context.move_to(*points[0])
                context.curve_to(*points[1], *points[2], *points[3])
            elif shape.opcode in (0x33, 0x34):
                if len(shape.element) != 13:
                    fail("GString clip curve-to has an invalid size")
                values = [float(s16(shape.element, offset)) for offset in (1, 3, 5, 7, 9, 11)]
                if shape.opcode == 0x33:
                    context.curve_to(*values)
                else:
                    context.rel_curve_to(*values)
            else:
                fail(f"unsupported non-rectangular GString clip primitive 0x{shape.opcode:02x}")
            context.restore()
        context.clip()


def gstring_color(
    color_flag: int, red_or_index: int, green: int, blue: int
) -> tuple[float, float, float]:
    """Resolve a GEOS ColorFlag/color payload to an RGB Cairo color."""
    if color_flag == 0:  # CF_INDEX
        red, green, blue = geos_palette_color(red_or_index)
    elif color_flag == 1:  # CF_GRAY
        red = green = blue = red_or_index
    elif color_flag == 3:  # CF_CMY
        red, green, blue = 255 - red_or_index, 255 - green, 255 - blue
    elif color_flag == 0x80:  # CF_RGB
        red = red_or_index
    else:
        fail(f"GString uses unsupported ColorFlag 0x{color_flag:02x}")
    return red / 255.0, green / 255.0, blue / 255.0


def gstring_source_for_mix(
    context: cairo.Context,
    color: tuple[float, float, float],
    mix_mode: int,
) -> bool:
    """Set Cairo's source/operator for the exact mix modes used by old GeoWrite."""
    if mix_mode == 0:  # MM_CLEAR: destination bits become zero (black)
        context.set_operator(cairo.OPERATOR_OVER)
        context.set_source_rgb(0.0, 0.0, 0.0)
    elif mix_mode == 1:  # MM_COPY
        context.set_operator(cairo.OPERATOR_OVER)
        context.set_source_rgb(*color)
    elif mix_mode == 2:  # MM_NOP
        return False
    elif mix_mode == 3:  # MM_XOR
        if not hasattr(cairo, "OPERATOR_DIFFERENCE"):
            fail("Cairo lacks the difference operator required by MM_XOR")
        context.set_operator(cairo.OPERATOR_DIFFERENCE)
        context.set_source_rgb(*color)
    elif mix_mode == 4:  # MM_INVERT
        if not hasattr(cairo, "OPERATOR_DIFFERENCE"):
            fail("Cairo lacks the difference operator required by MM_INVERT")
        context.set_operator(cairo.OPERATOR_DIFFERENCE)
        context.set_source_rgb(1.0, 1.0, 1.0)
    elif mix_mode == 6:  # MM_SET: destination bits become one (white)
        context.set_operator(cairo.OPERATOR_OVER)
        context.set_source_rgb(1.0, 1.0, 1.0)
    else:
        fail(f"rendered GString primitive uses unsupported MixMode {mix_mode}")
    return True


def gstring_draw_mask_pattern(
    context: cairo.Context, rows: bytes
) -> tuple[cairo.ImageSurface, cairo.SurfacePattern, bytearray]:
    """Create a device-aligned repeating A8 pattern for an eight-row GEOS mask."""
    mask_data = bytearray(
        0xFF if rows[row] & (0x80 >> column) else 0
        for row in range(8)
        for column in range(8)
    )
    stride = cairo.ImageSurface.format_stride_for_width(cairo.FORMAT_A8, 8)
    if stride != 8:
        fail("Cairo returned an unexpected A8 draw-mask stride")
    surface = cairo.ImageSurface.create_for_data(mask_data, cairo.FORMAT_A8, 8, 8, stride)
    pattern = cairo.SurfacePattern(surface)
    pattern.set_extend(cairo.EXTEND_REPEAT)
    pattern.set_filter(cairo.FILTER_NEAREST)
    pattern.set_matrix(context.get_matrix())
    return surface, pattern, mask_data


def paint_gstring_path(
    context: cairo.Context,
    fill: bool,
    color: tuple[float, float, float],
    mask_type: int,
    custom_mask: bytes | None,
    mix_mode: int,
) -> None:
    """Paint the current Cairo path with GEOS color, mask, and mix semantics."""
    rows = draw_mask_rows(mask_type, custom_mask)
    if rows == b"\0" * 8 or mix_mode == 2:
        context.new_path()
        return
    if rows == b"\xff" * 8:
        if not gstring_source_for_mix(context, color, mix_mode):
            context.new_path()
            return
        (context.fill if fill else context.stroke)()
        return

    context.push_group()
    context.set_operator(cairo.OPERATOR_OVER)
    if mix_mode in (0, 4):
        context.set_source_rgb(1.0, 1.0, 1.0)
    elif mix_mode == 6:
        context.set_source_rgb(1.0, 1.0, 1.0)
    elif mix_mode in (1, 3):
        context.set_source_rgb(*color)
    else:
        fail(f"masked GString primitive uses unsupported MixMode {mix_mode}")
    (context.fill if fill else context.stroke)()
    shape = context.pop_group()
    if mix_mode == 0:
        context.set_operator(cairo.OPERATOR_OVER)
        context.set_source_rgb(0.0, 0.0, 0.0)
        # The shape supplies coverage; its RGB values are immaterial here.
        context.mask(shape)
    else:
        context.set_source(shape)
        if mix_mode in (3, 4):
            context.set_operator(cairo.OPERATOR_DIFFERENCE)
    surface, pattern, mask_data = gstring_draw_mask_pattern(context, rows)
    if mix_mode == 0:
        # MM_CLEAR above has already been limited to the shape, so intersecting
        # it with a non-solid mask requires a second temporary group.
        fail("masked MM_CLEAR GString primitives are not supported")
    context.mask(pattern)
    surface.finish()


def append_gstring_ellipse(
    context: cairo.Context, left: float, top: float, right: float, bottom: float
) -> None:
    """Append the ellipse bounded by two GEOS coordinate pairs."""
    left, right = sorted((left, right))
    top, bottom = sorted((top, bottom))
    radius_x = (right - left) / 2.0
    radius_y = (bottom - top) / 2.0
    if radius_x == 0 or radius_y == 0:
        return
    context.save()
    context.translate(left + radius_x, top + radius_y)
    context.scale(radius_x, radius_y)
    context.arc(0.0, 0.0, 1.0, 0.0, math.tau)
    context.restore()


def append_gstring_arc_three_points(context: cairo.Context, element: bytes) -> tuple[float, float]:
    """Append modern GR_DRAW_ARC_3POINT and return its final point."""
    if len(element) != 27 or u16(element, 1) > 2:
        fail("GR_DRAW_ARC_3POINT has invalid data")
    points = [
        (wwfixed(element, offset), wwfixed(element, offset + 4))
        for offset in (3, 11, 19)
    ]
    (x1, y1), (x2, y2), (x3, y3) = points
    determinant = 2.0 * (x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2))
    context.move_to(x1, y1)
    if abs(determinant) < 1e-12:
        context.line_to(x2, y2)
        context.line_to(x3, y3)
        return x3, y3
    q1, q2, q3 = x1 * x1 + y1 * y1, x2 * x2 + y2 * y2, x3 * x3 + y3 * y3
    cx = (q1 * (y2 - y3) + q2 * (y3 - y1) + q3 * (y1 - y2)) / determinant
    cy = (q1 * (x3 - x2) + q2 * (x1 - x3) + q3 * (x2 - x1)) / determinant
    radius = math.hypot(x1 - cx, y1 - cy)
    angle1 = math.atan2(y1 - cy, x1 - cx)
    angle2 = math.atan2(y2 - cy, x2 - cx)
    angle3 = math.atan2(y3 - cy, x3 - cx)
    if (angle2 - angle1) % (2.0 * math.pi) <= (angle3 - angle1) % (2.0 * math.pi):
        context.arc(cx, cy, radius, angle1, angle3)
    else:
        context.arc_negative(cx, cy, radius, angle1, angle3)
    if u16(element, 1) == 1:
        context.close_path()
    elif u16(element, 1) == 2:
        context.line_to(cx, cy)
        context.close_path()
    return x3, y3


def configure_gstring_line(
    context: cairo.Context,
    width: float,
    end: int,
    join: int,
    miter_limit: float,
    style: int,
    dash_offset: int,
) -> None:
    """Apply the protocol-1 line attributes represented in a GString."""
    if width < 0:
        fail("GString uses a negative line width")
    if end not in (0, 1, 2) or join not in (0, 1, 2):
        fail("GString uses an invalid line end or join")
    if miter_limit <= 0:
        fail("GString uses a non-positive miter limit")
    context.set_line_width(width if width else 1.0)
    context.set_line_cap((cairo.LINE_CAP_BUTT, cairo.LINE_CAP_ROUND, cairo.LINE_CAP_SQUARE)[end])
    context.set_line_join((cairo.LINE_JOIN_MITER, cairo.LINE_JOIN_ROUND, cairo.LINE_JOIN_BEVEL)[join])
    context.set_miter_limit(miter_limit)
    system_dashes = {
        0: (),
        1: (4.0, 4.0),
        2: (1.0, 2.0),
        3: (4.0, 4.0, 1.0, 4.0),
        4: (4.0, 4.0, 1.0, 4.0, 1.0, 4.0),
    }
    try:
        dashes = system_dashes[style]
    except KeyError:
        fail(f"GString uses unsupported LineStyle {style}")
    context.set_dash(dashes, float(dash_offset))


@dataclass(frozen=True)
class GStringTextRun:
    raw: bytes
    color: tuple[float, float, float]
    mask: int
    styles: int
    mode: int
    font_id: int
    point_size: float
    tracking: int
    weight: int
    width: int
    space_pad: float


def parse_legacy_gstring_text_field(
    element: bytes,
) -> tuple[float, float, list[GStringTextRun]]:
    """Decode a protocol-1 OldDrawTextField after opcode normalization."""
    need(element, 0, 53, "old GString draw-text-field")
    if element[0] != 0x3E:
        fail("internal old text-field opcode mismatch")
    fixed_count = u16(element, 1)
    string_length = fixed_count - 50
    if string_length < 0:
        fail("old GString text field has an invalid fixed byte count")
    string_start = 31  # opcode + fcount + sizeof(OldGDF_saved)
    need(element, string_start, string_length, "old GString text-field string")
    raw = element[string_start : string_start + string_length]
    saved = 3
    x = float(s16(element, saved + 5) + s16(element, saved + 19) + s16(element, saved + 22))
    y = float(s16(element, saved + 24))

    runs: list[GStringTextRun] = []
    cursor = string_start + string_length
    covered = 0
    styles = mode = 0
    while covered < string_length:
        need(element, cursor, 22, "old GString text-field style run")
        count = u16(element, cursor)
        if not count or covered + count > string_length:
            fail("old GString text-field style run exceeds its string")
        attr = element[cursor + 2 : cursor + 22]
        color = gstring_color(attr[0], attr[1], attr[2], attr[3])
        mask = attr[4]
        draw_mask_rows(mask, None)
        if attr[5] not in (0, 1, 0x80, 0x81):
            fail("old GString text field uses an invalid ColorMapMode")
        styles = (styles & ~attr[7]) | attr[6]
        mode = (mode & ~attr[9]) | attr[8]
        point_size = wbfixed(attr, 15)
        tracking = s16(attr, 18)
        if point_size <= 0:
            fail("old GString text field uses a non-positive point size")
        if not -150 <= tracking <= 500:
            fail("old GString text field uses invalid track kerning")
        runs.append(
            GStringTextRun(
                raw[covered : covered + count], color, mask, styles, mode,
                u16(attr, 13), point_size, tracking, 100, 100, 0.0,
            )
        )
        covered += count
        cursor += 22
    if cursor != len(element):
        fail("bytes remain after the old GString text-field style runs")
    return x, y, runs


def render_gstring_text_run(
    context: cairo.Context,
    run: GStringTextRun,
    x: float,
    baseline: float,
    mix_mode: int,
) -> float:
    """Render one style run and return its advance in GString coordinates."""
    text = display_text(run.raw, 0)
    if not text:
        return 0.0
    attr = CharAttr(
        0, run.font_id, run.point_size, run.styles, run.color, run.tracking,
        run.weight, run.width, 0,
    )
    family, slant, weight = font_face(attr)
    context.save()
    context.select_font_face(family, slant, weight)
    script_scale = 0.5 if run.styles & 0x0C else 1.0
    effective_size = run.point_size * script_scale
    context.set_font_size(effective_size)
    vertical = 0.0
    if run.styles & 0x04:
        vertical = run.point_size * 0.5
    elif run.styles & 0x08:
        vertical = -run.point_size * 0.5
    width_scale = run.width / 100.0
    if width_scale <= 0:
        fail("GString text field uses a non-positive font width")
    context.translate(x, baseline + vertical)
    context.scale(width_scale, 1.0)

    tracking = track_kerning_increment(effective_size, run.tracking) / width_scale
    local_space_pad = run.space_pad / width_scale
    positions: list[tuple[str, float]] = []
    uses_manual_spacing = bool(tracking or (local_space_pad and " " in text))
    if uses_manual_spacing:
        local_pen = 0.0
        for character in text:
            positions.append((character, local_pen))
            advance = text_extents_advance(context.text_extents(character))
            local_pen += advance + tracking
            if character == " ":
                local_pen += local_space_pad
    else:
        local_pen = text_extents_advance(context.text_extents(text))

    rows = draw_mask_rows(run.mask, None)
    direct_text = rows == b"\xff" * 8 and mix_mode in (0, 1, 4, 6) and not (run.styles & 0x40)
    if direct_text and gstring_source_for_mix(context, run.color, mix_mode):
        if uses_manual_spacing:
            for character, position in positions:
                context.move_to(position, 0.0)
                context.show_text(character)
        else:
            context.move_to(0.0, 0.0)
            context.show_text(text)
    elif rows != b"\0" * 8 and mix_mode != 2:
        context.new_path()
        if uses_manual_spacing:
            for character, position in positions:
                context.move_to(position, 0.0)
                context.text_path(character)
        else:
            context.move_to(0.0, 0.0)
            context.text_path(text)
        if run.styles & 0x40:
            context.set_line_width(max(0.45, effective_size / 18.0))
            paint_gstring_path(context, False, run.color, run.mask, None, mix_mode)
        else:
            paint_gstring_path(context, True, run.color, run.mask, None, mix_mode)

    decoration_y: list[float] = []
    if run.styles & 0x01:
        decoration_y.append(effective_size * 0.12)
    if run.styles & 0x02:
        decoration_y.append(-effective_size * 0.3)
    for y in decoration_y:
        context.new_path()
        context.move_to(0.0, y)
        context.line_to(local_pen, y)
        context.set_line_width(max(0.45, effective_size / 18.0))
        paint_gstring_path(context, False, run.color, run.mask, None, mix_mode)
    context.restore()
    return local_pen * width_scale


def render_legacy_gstring_text_field(
    context: cairo.Context,
    element: bytes,
    matrix: Matrix,
    clips: list[list[ClipRectangle]],
    mix_mode: int,
) -> None:
    x, baseline, runs = parse_legacy_gstring_text_field(element)
    context.save()
    apply_clip_groups(context, clips)
    context.transform(cairo.Matrix(*cairo_safe_matrix(matrix)))
    pen = x
    for run in runs:
        pen += render_gstring_text_run(context, run, pen, baseline, mix_mode)
    context.restore()


def render_legacy_gstring_vector(
    context: cairo.Context,
    element: bytes,
    matrix: Matrix,
    clips: list[list[ClipRectangle]],
    line_color: tuple[float, float, float],
    line_mask: int,
    custom_line_mask: bytes | None,
    line_width: float,
    line_end: int,
    line_join: int,
    line_style: int,
    line_dash_offset: int,
    miter_limit: float,
    area_color: tuple[float, float, float],
    area_mask: int,
    custom_area_mask: bytes | None,
    mix_mode: int,
    current_point: tuple[float, float],
    legacy: bool = True,
) -> tuple[float, float]:
    """Render one normalized protocol-1 vector opcode and return the pen position."""
    opcode = element[0]
    context.save()
    apply_clip_groups(context, clips)
    # GEOS transforms primitive coordinates but keeps line attributes (width,
    # dash lengths, caps, and joins) in the GState's page-coordinate space.
    # Build the path under the primitive transform, then remove that transform
    # before stroking.  Stroking directly under a GrObj unit-shape transform
    # turns a normal one- or two-point frame into a solid object-sized block.
    context.save()
    context.transform(cairo.Matrix(*cairo_safe_matrix(matrix)))
    context.new_path()
    fill = False
    fill_rule: int | None = None
    points: list[tuple[float, float]] = []

    if opcode == 0x20:  # GR_DRAW_LINE
        if len(element) != 9:
            fail("old GR_DRAW_LINE has an invalid element size")
        points = [(s16(element, 1), s16(element, 3)), (s16(element, 5), s16(element, 7))]
    elif opcode == 0x21:  # GR_DRAW_LINE_TO
        if len(element) != 5:
            fail("old GR_DRAW_LINE_TO has an invalid element size")
        points = [current_point, (s16(element, 1), s16(element, 3))]
    elif opcode == 0x23:  # GR_DRAW_HLINE
        if len(element) != 7:
            fail("old GR_DRAW_HLINE has an invalid element size")
        points = [(s16(element, 1), s16(element, 3)), (s16(element, 5), s16(element, 3))]
    elif opcode == 0x24:  # GR_DRAW_HLINE_TO
        if len(element) != 3:
            fail("old GR_DRAW_HLINE_TO has an invalid element size")
        points = [current_point, (s16(element, 1), current_point[1])]
    elif opcode == 0x25:  # GR_DRAW_VLINE
        if len(element) != 7:
            fail("old GR_DRAW_VLINE has an invalid element size")
        points = [(s16(element, 1), s16(element, 3)), (s16(element, 1), s16(element, 5))]
    elif opcode == 0x26:  # GR_DRAW_VLINE_TO
        if len(element) != 3:
            fail("old GR_DRAW_VLINE_TO has an invalid element size")
        points = [current_point, (current_point[0], s16(element, 1))]
    elif opcode == 0x27:  # GR_DRAW_POLYLINE
        count = u16(element, 1)
        if len(element) != 3 + count * 4:
            fail("old GR_DRAW_POLYLINE coordinate count is inconsistent")
        points = [(s16(element, 3 + i * 4), s16(element, 5 + i * 4)) for i in range(count)]
    elif opcode in (0x2C, 0x35, 0x42, 0x48):
        if len(element) != 9:
            fail("old rectangle/ellipse GString opcode has an invalid element size")
        left, top, right, bottom = (s16(element, offset) for offset in (1, 3, 5, 7))
        fill = opcode in (0x42, 0x48)
        if opcode in (0x2C, 0x42):
            x1, x2 = sorted((left, right))
            y1, y2 = sorted((top, bottom))
            context.rectangle(x1, y1, x2 - x1, y2 - y1)
        else:
            append_gstring_ellipse(context, left, top, right, bottom)
    elif opcode in (0x2E, 0x44):
        if len(element) != 11:
            fail("rounded rectangle GString opcode has an invalid element size")
        append_rounded_rectangle(
            context, s16(element, 3), s16(element, 5),
            s16(element, 7), s16(element, 9), s16(element, 1),
        )
        fill = opcode == 0x44
    elif opcode in (0x2D, 0x43):
        if len(element) != 5:
            fail("old current-position rectangle opcode has an invalid element size")
        right, bottom = s16(element, 1), s16(element, 3)
        left, top = current_point
        x1, x2 = sorted((left, right))
        y1, y2 = sorted((top, bottom))
        context.rectangle(x1, y1, x2 - x1, y2 - y1)
        fill = opcode == 0x43
        current_point = (right, bottom)
    elif opcode == 0x36:  # GR_DRAW_POLYGON
        count = u16(element, 1)
        if len(element) != 3 + count * 4:
            fail("old GR_DRAW_POLYGON coordinate count is inconsistent")
        points = [(s16(element, 3 + i * 4), s16(element, 5 + i * 4)) for i in range(count)]
    elif opcode == 0x37:  # GR_DRAW_POINT
        if len(element) != 5:
            fail("old GR_DRAW_POINT has an invalid element size")
        x, y = s16(element, 1), s16(element, 3)
        points = [(x, y), (x + max(line_width, 1.0) / 1000.0, y)]
    elif opcode == 0x38:  # GR_DRAW_POINT_CP
        if len(element) != 1:
            fail("old GR_DRAW_POINT_CP has an invalid element size")
        x, y = current_point
        points = [(x, y), (x + max(line_width, 1.0) / 1000.0, y)]
    elif opcode == 0x47:  # GR_FILL_POLYGON
        if len(element) < 4:
            fail("GR_FILL_POLYGON is truncated")
        if legacy:
            rule, count = element[1], u16(element, 2)
        else:
            count, rule = u16(element, 1), element[3]
        if rule not in (0, 1) or len(element) != 4 + count * 4:
            fail("GR_FILL_POLYGON header is invalid")
        fill_rule = cairo.FILL_RULE_EVEN_ODD if rule == 0 else cairo.FILL_RULE_WINDING
        points = [(s16(element, 4 + i * 4), s16(element, 6 + i * 4)) for i in range(count)]
        fill = True
    else:
        context.restore()
        context.restore()
        fail(f"internal unsupported old vector opcode 0x{opcode:02x}")

    if points:
        context.move_to(*points[0])
        for point in points[1:]:
            context.line_to(*point)
        if opcode in (0x36, 0x47):
            context.close_path()
        current_point = points[-1]

    # Cairo retains the current path across save/restore, as GEOS requires
    # here, while the object transform is removed from subsequent pen setup.
    context.restore()
    if fill_rule is not None:
        context.set_fill_rule(fill_rule)
    if fill:
        paint_gstring_path(context, True, area_color, area_mask, custom_area_mask, mix_mode)
    else:
        configure_gstring_line(
            context, line_width, line_end, line_join, miter_limit,
            line_style, line_dash_offset,
        )
        paint_gstring_path(context, False, line_color, line_mask, custom_line_mask, mix_mode)
    context.restore()
    return current_point


def draw_bitmap_raster(
    context: cairo.Context,
    raster: BitmapRaster,
    x: float,
    y: float,
    matrix: Matrix,
    clips: list[list[ClipRectangle]],
    fill_color: tuple[float, float, float] | None,
    area_mask: int = 25,
    custom_area_mask: bytes | None = None,
) -> None:
    if fill_color is None:
        data = bytearray(raster.bgra)
    else:
        data = bytearray(raster.coverage)
    stride = cairo.ImageSurface.format_stride_for_width(cairo.FORMAT_ARGB32, raster.width)
    if fill_color is None and stride != raster.width * 4:
        fail("Cairo returned an unexpected ARGB32 bitmap stride")
    if fill_color is None:
        surface = cairo.ImageSurface.create_for_data(
            data, cairo.FORMAT_ARGB32, raster.width, raster.height, stride
        )
    else:
        stride = cairo.ImageSurface.format_stride_for_width(cairo.FORMAT_A8, raster.width)
        if stride == raster.width:
            mask_data = data
        else:
            mask_data = bytearray(stride * raster.height)
            for row in range(raster.height):
                mask_data[row * stride : row * stride + raster.width] = data[
                    row * raster.width : (row + 1) * raster.width
                ]
        surface = cairo.ImageSurface.create_for_data(
            mask_data, cairo.FORMAT_A8, raster.width, raster.height, stride
        )
    pattern = cairo.SurfacePattern(surface)
    pattern.set_filter(cairo.FILTER_NEAREST)
    context.save()
    apply_clip_groups(context, clips)
    context.transform(cairo.Matrix(*matrix))
    context.translate(x, y)
    context.scale(72.0 / raster.x_resolution, 72.0 / raster.y_resolution)
    if fill_color is None:
        context.set_source(pattern)
        context.rectangle(0, 0, raster.width, raster.height)
        context.fill()
    else:
        rows = draw_mask_rows(area_mask, custom_area_mask)
        context.push_group()
        context.set_source_rgb(*fill_color)
        context.mask(pattern)
        filled_shape = context.pop_group()
        context.set_source(filled_shape)
        if rows == b"\xff" * 8:
            context.paint()
        elif rows != b"\0" * 8:
            draw_mask_data = bytearray(
                0xFF if rows[row] & (0x80 >> column) else 0
                for row in range(8)
                for column in range(8)
            )
            mask_stride = cairo.ImageSurface.format_stride_for_width(cairo.FORMAT_A8, 8)
            if mask_stride != 8:
                fail("Cairo returned an unexpected A8 draw-mask stride")
            draw_mask_surface = cairo.ImageSurface.create_for_data(
                draw_mask_data, cairo.FORMAT_A8, 8, 8, mask_stride
            )
            draw_mask_pattern = cairo.SurfacePattern(draw_mask_surface)
            draw_mask_pattern.set_extend(cairo.EXTEND_REPEAT)
            draw_mask_pattern.set_filter(cairo.FILTER_NEAREST)
            # GrShiftDrawMask aligns the pattern to device-space window 0,0.
            # A Cairo pattern matrix maps user coordinates to pattern pixels,
            # so the current user-to-device matrix implements that rule.
            draw_mask_pattern.set_matrix(context.get_matrix())
            context.mask(draw_mask_pattern)
            draw_mask_surface.finish()
    context.restore()
    surface.finish()


def render_gstring(
    context: cairo.Context,
    graphic: VisTextGraphic,
    initial_color: tuple[float, float, float],
    initial_line: GrObjLineAttr | None = None,
    initial_area: GrObjAreaAttr | None = None,
) -> None:
    if graphic.gstring is None:
        return
    current_matrix = IDENTITY_MATRIX
    default_matrix = IDENTITY_MATRIX
    transform_stack: list[Matrix] = []
    area_color = initial_area.color if initial_area is not None else initial_color
    area_mask = initial_area.mask if initial_area is not None else 25  # SDM_100
    custom_area_mask: bytes | None = None
    line_color = initial_line.color if initial_line is not None else initial_color
    line_mask = initial_line.mask if initial_line is not None else 25
    custom_line_mask: bytes | None = None
    line_width = initial_line.width if initial_line is not None else 1.0
    line_end = initial_line.end if initial_line is not None else 0
    line_join = initial_line.join if initial_line is not None else 0
    line_style = initial_line.style if initial_line is not None else 0
    line_dash_offset = 0
    miter_limit = initial_line.miter_limit if initial_line is not None else 10.0
    current_point = (0.0, 0.0)
    mix_mode = 1  # MM_COPY
    clips: list[list[ClipShape]] = []
    clip_is_rectangular = True
    path_rectangles: list[ClipRectangle] | None = None
    path_shapes: list[ClipShape] | None = None
    path_is_rectangular = True
    saved_path_rectangles: list[ClipRectangle] = []
    saved_path_shapes: list[ClipShape] = []
    saved_path_is_rectangular = True
    saved_path_defined = False
    state_stack: list[tuple[object, ...]] = []

    context.save()
    context.transform(cairo.Matrix(*graphic.matrix))
    context.translate(*graphic.draw_offset)
    for index, element in enumerate(graphic.gstring.elements):
        if index in graphic.gstring.continuation_indices:
            continue
        opcode = element[0]
        if opcode == 0:
            if len(element) != 1 or index != len(graphic.gstring.elements) - 1:
                fail("GR_END_GSTRING is malformed or not final")
        elif opcode == 0x0E:
            # HugeArray GStrings use the element boundary as the comment size;
            # unlike stream GStrings, the saved payload omits OpComment.OC_size.
            if len(element) < 1:
                fail("GR_COMMENT is truncated")
        elif opcode == 0x10:
            if len(element) != 5:
                fail("GR_APPLY_ROTATION has an invalid element size")
            angle = math.radians(wwfixed(element, 1))
            rotation: Matrix = (
                math.cos(angle), math.sin(angle), -math.sin(angle), math.cos(angle), 0.0, 0.0,
            )
            current_matrix = multiply_matrix(current_matrix, rotation)
        elif opcode == 0x11:
            if len(element) != 9:
                fail("GR_APPLY_SCALE has an invalid element size")
            scale: Matrix = (wwfixed(element, 1), 0.0, 0.0, wwfixed(element, 5), 0.0, 0.0)
            current_matrix = multiply_matrix(current_matrix, scale)
        elif opcode == 0x12:
            if len(element) != 9:
                fail("GR_APPLY_TRANSLATION has an invalid element size")
            translation: Matrix = (1.0, 0.0, 0.0, 1.0, wwfixed(element, 1), wwfixed(element, 5))
            current_matrix = multiply_matrix(current_matrix, translation)
        elif opcode == 0x13:
            if len(element) != 29:
                fail("GR_APPLY_TRANSFORM has an invalid element size")
            current_matrix = multiply_matrix(current_matrix, trans_matrix(element, 1))
        elif opcode == 0x14:
            if len(element) != 9:
                fail("GR_APPLY_TRANSLATION_DWORD has an invalid element size")
            translation = (1.0, 0.0, 0.0, 1.0, float(s32(element, 1)), float(s32(element, 5)))
            current_matrix = multiply_matrix(current_matrix, translation)
        elif opcode == 0x15:
            if len(element) != 29:
                fail("GR_SET_TRANSFORM has an invalid element size")
            current_matrix = trans_matrix(element, 1)
        elif opcode == 0x16:
            if len(element) != 1:
                fail("GR_SET_NULL_TRANSFORM has an invalid element size")
            current_matrix = IDENTITY_MATRIX
        elif opcode == 0x17:
            if len(element) != 1:
                fail("GR_SET_DEFAULT_TRANSFORM has an invalid element size")
            current_matrix = default_matrix
        elif opcode == 0x18:
            if len(element) != 1:
                fail("GR_INIT_DEFAULT_TRANSFORM has an invalid element size")
            default_matrix = current_matrix
        elif opcode == 0x19:
            if len(element) != 1:
                fail("GR_SAVE_TRANSFORM has an invalid element size")
            transform_stack.append(current_matrix)
        elif opcode == 0x1A:
            if len(element) != 1 or not transform_stack:
                fail("GR_RESTORE_TRANSFORM has no matching saved transform")
            current_matrix = transform_stack.pop()
        elif opcode == 0x60:
            if len(element) != 1:
                fail("GR_SAVE_STATE has an invalid element size")
            state_stack.append(
                (
                    current_matrix, default_matrix, list(transform_stack), area_color,
                    area_mask, custom_area_mask, line_color, line_mask,
                    custom_line_mask, line_width, line_end, line_join, line_style,
                    line_dash_offset, miter_limit, current_point, mix_mode,
                    [list(group) for group in clips], clip_is_rectangular,
                )
            )
        elif opcode == 0x61:
            if len(element) != 1 or not state_stack:
                fail("GR_RESTORE_STATE has no matching saved state")
            (
                current_matrix, default_matrix, transform_stack, area_color,
                area_mask, custom_area_mask, line_color, line_mask,
                custom_line_mask, line_width, line_end, line_join, line_style,
                line_dash_offset, miter_limit, current_point, mix_mode, clips,
                clip_is_rectangular,
            ) = state_stack.pop()
        elif opcode == 0x62:
            if len(element) != 2 or element[1] > 7:
                fail("GR_SET_MIX_MODE has invalid data")
            mix_mode = element[1]
        elif opcode == 0x63:
            if len(element) != 5:
                fail("old GR_MOVE_TO has an invalid element size")
            current_point = (float(s16(element, 1)), float(s16(element, 3)))
        elif opcode == 0x64:
            if graphic.gstring.legacy:
                if len(element) != 5:
                    fail("old GR_REL_MOVE_TO has an invalid element size")
                delta = float(s16(element, 1)), float(s16(element, 3))
            else:
                if len(element) != 9:
                    fail("GR_REL_MOVE_TO has an invalid element size")
                delta = wwfixed(element, 1), wwfixed(element, 5)
            current_point = current_point[0] + delta[0], current_point[1] + delta[1]
        elif opcode == 0x69:
            if len(element) != 4:
                fail("old GR_SET_LINE_COLOR has an invalid element size")
            line_color = tuple(value / 255.0 for value in element[1:4])
        elif opcode == 0x6A:
            if len(element) != 2:
                fail("old GR_SET_LINE_MASK has an invalid element size")
            line_mask = element[1]
            custom_line_mask = None
            draw_mask_rows(line_mask, custom_line_mask)
        elif opcode == 0x6B:
            if len(element) != 2 or element[1] not in (0, 1, 0x80, 0x81):
                fail("old GR_SET_LINE_COLOR_MAP has invalid data")
        elif opcode == 0x6C:
            if graphic.gstring.legacy:
                if len(element) != 3:
                    fail("old GR_SET_LINE_WIDTH has an invalid element size")
                line_width = float(s16(element, 1))
            else:
                if len(element) != 5:
                    fail("GR_SET_LINE_WIDTH has an invalid element size")
                line_width = wwfixed(element, 1)
        elif opcode == 0x6D:
            if len(element) != 2 or element[1] > 2:
                fail("old GR_SET_LINE_JOIN has invalid data")
            line_join = element[1]
        elif opcode == 0x6E:
            if len(element) != 2 or element[1] > 2:
                fail("old GR_SET_LINE_END has invalid data")
            line_end = element[1]
        elif opcode == 0x6F:
            if graphic.gstring.legacy:
                if len(element) != 11:
                    fail("old GR_SET_LINE_ATTR has an invalid element size")
                line_color = gstring_color(element[1], element[2], element[3], element[4])
                if element[5] > 5:
                    fail("old GR_SET_LINE_ATTR has invalid color-map flags")
                line_mask = element[6]
                line_width = float(s16(element, 7))
                line_end, line_join, line_style, line_dash_offset = element[9], element[10], 0, 0
            else:
                if len(element) != 14:
                    fail("GR_SET_LINE_ATTR has an invalid element size")
                line_color = gstring_color(element[1], element[2], element[3], element[4])
                line_mask = element[5]
                if element[6] not in (0, 1, 0x80, 0x81):
                    fail("GR_SET_LINE_ATTR has an invalid ColorMapMode")
                line_end, line_join, line_style = element[7], element[8], element[9]
                line_dash_offset = 0
                line_width = wwfixed(element, 10)
            custom_line_mask = None
            draw_mask_rows(line_mask, custom_line_mask)
        elif opcode == 0x70:
            if len(element) != 5:
                fail("old GR_SET_MITER_LIMIT has an invalid element size")
            miter_limit = wwfixed(element, 1)
        elif opcode == 0x71:
            if len(element) != 3 or element[1] > 4:
                fail("old GR_SET_LINE_STYLE has invalid data")
            line_style, line_dash_offset = element[1], element[2]
        elif opcode == 0x72:
            if len(element) != 2:
                fail("old GR_SET_LINE_COLOR_INDEX has an invalid element size")
            line_color = tuple(value / 255.0 for value in geos_palette_color(element[1]))
        elif opcode == 0x73:
            if len(element) != 9:
                fail("old GR_SET_CUSTOM_LINE_MASK has an invalid element size")
            line_mask = 0x7F
            custom_line_mask = element[1:9]
        elif opcode == 0x75:
            if len(element) != 4:
                fail("GR_SET_AREA_COLOR has an invalid element size")
            area_color = tuple(value / 255.0 for value in element[1:4])
        elif opcode == 0x76:
            if len(element) != 2:
                fail("GR_SET_AREA_MASK has an invalid element size")
            area_mask = element[1]
            custom_area_mask = None
            draw_mask_rows(area_mask, custom_area_mask)
        elif opcode == 0x77:
            if len(element) != 2 or element[1] not in (0, 1, 0x80, 0x81):
                fail("old GR_SET_AREA_COLOR_MAP has invalid data")
        elif opcode == 0x78:
            if len(element) != 7:
                fail("GR_SET_AREA_ATTR has an invalid element size")
            color_flag = element[1]
            area_color = gstring_color(color_flag, element[2], element[3], element[4])
            if graphic.gstring.legacy:
                if element[5] > 5:
                    fail("old GR_SET_AREA_ATTR has invalid color-map flags")
                area_mask = element[6]
            else:
                if element[6] not in (0, 1, 0x80, 0x81):
                    fail("GR_SET_AREA_ATTR uses an invalid ColorMapMode")
                area_mask = element[5]
            custom_area_mask = None
            draw_mask_rows(area_mask, custom_area_mask)
        elif opcode == 0x79:
            if len(element) != 2:
                fail("GR_SET_AREA_COLOR_INDEX has an invalid element size")
            area_color = tuple(value / 255.0 for value in geos_palette_color(element[1]))
        elif opcode == 0x7A:
            if len(element) != 9:
                fail("GR_SET_CUSTOM_AREA_MASK has an invalid element size")
            area_mask = 0x7F
            custom_area_mask = element[1:9]
        elif opcode in (0xA2, 0xA3):
            if len(element) != 11:
                fail("GString clip rectangle has an invalid element size")
            matrix = current_matrix if opcode == 0xA2 else IDENTITY_MATRIX
            shape = ClipRectangle(
                matrix, s16(element, 3), s16(element, 5), s16(element, 7), s16(element, 9)
            )
            operation = u16(element, 1)
            if operation > 3:
                fail(f"GString has invalid PathCombineType {operation}")
            if operation <= 1:
                clips = combine_clip(clips, [shape], operation)
                clip_is_rectangular = True
            elif clip_is_rectangular:
                clips = combine_clip(clips, [shape], operation)
        elif opcode == 0xA0:
            if len(element) != 5:
                fail("GR_BEGIN_PATH has an invalid element size")
            path_rectangles = []
            path_shapes = []
            path_is_rectangular = True
        elif opcode == 0x2C and path_rectangles is not None:
            if len(element) != 9:
                fail("path GR_DRAW_RECT has an invalid element size")
            path_rectangles.append(
                ClipRectangle(
                    current_matrix,
                    s16(element, 1), s16(element, 3), s16(element, 5), s16(element, 7),
                )
            )
            assert path_shapes is not None
            path_shapes.append(ClipPrimitive(current_matrix, opcode, element))
        elif opcode == 0xA1:
            if len(element) != 1 or path_rectangles is None:
                fail("GR_END_PATH has no matching path")
            saved_path_rectangles = path_rectangles
            saved_path_shapes = path_shapes or []
            saved_path_is_rectangular = path_is_rectangular
            saved_path_defined = True
            path_rectangles = None
            path_shapes = None
        elif opcode in (0xA5, 0xA6):
            if len(element) != 4 or not saved_path_defined:
                fail("GString clip-path command has no preceding path")
            if element[1] not in (0, 1):
                fail("GString clip path has an invalid fill rule")
            operation = u16(element, 2)
            if operation > 3:
                fail(f"GString has invalid PathCombineType {operation}")
            if operation == 0:
                clips = []
                clip_is_rectangular = True
            elif operation == 1 or clip_is_rectangular:
                shapes: list[ClipShape] = (
                    list(saved_path_rectangles) if saved_path_is_rectangular else list(saved_path_shapes)
                )
                clips = combine_clip(clips, shapes, operation)
                clip_is_rectangular = saved_path_is_rectangular and clip_is_rectangular
            else:
                clips = combine_clip(clips, list(saved_path_shapes), operation)
                clip_is_rectangular = False
        elif path_rectangles is not None and 0x20 <= opcode <= 0x5F:
            assert path_shapes is not None
            path_shapes.append(ClipPrimitive(current_matrix, opcode, element))
            path_is_rectangular = False
        elif opcode == 0x3E and graphic.gstring.legacy:
            if not clip_is_rectangular:
                fail("old GString text uses a non-rectangular clip path")
            render_legacy_gstring_text_field(context, element, current_matrix, clips, mix_mode)
        elif opcode in {
            0x20, 0x21, 0x23, 0x24, 0x25, 0x26, 0x27, 0x2C, 0x2D,
            0x2E, 0x35, 0x36, 0x37, 0x38, 0x42, 0x43, 0x44, 0x47, 0x48,
        }:
            current_point = render_legacy_gstring_vector(
                context, element, current_matrix, clips, line_color, line_mask,
                custom_line_mask, line_width, line_end, line_join, line_style,
                line_dash_offset, miter_limit, area_color, area_mask,
                custom_area_mask, mix_mode, current_point,
                graphic.gstring.legacy,
            )
        elif opcode in (0x4C, 0x4D, 0x50, 0x51):
            if mix_mode != 1:
                fail("bitmap uses a non-copy GString mix mode")
            raster = graphic.gstring.bitmaps[index]
            bitmap_x, bitmap_y = (
                current_point if opcode in (0x4D, 0x51)
                else (float(s16(element, 1)), float(s16(element, 3)))
            )
            draw_bitmap_raster(
                context, raster, bitmap_x, bitmap_y, current_matrix, clips,
                area_color if opcode in (0x4C, 0x4D) else None,
                area_mask,
                custom_area_mask,
            )
    context.restore()


def render_field(
    context: cairo.Context,
    document: GeoWriteDocument,
    article: Article,
    raw: bytes,
    absolute_start: int,
    x: float,
    baseline: float,
    line_top: float,
    line_height: float,
    expected_width: float,
    line_flags: int,
    space_pad: float,
    page_number: int,
) -> None:
    pieces: list[tuple[str, str | VisTextGraphic, CharAttr]] = []
    graphic_runs = {run.position: run.token for run in article.graphic_runs[:-1]}
    cursor = 0
    while cursor < len(raw):
        absolute_position = absolute_start + cursor
        token = run_token_at(article.char_runs, absolute_start + cursor)
        try:
            attr = document.char_attrs[token]
        except KeyError:
            fail(f"character run references missing attribute token {token}")
        if raw[cursor] == 0x1A:
            try:
                graphic_token = graphic_runs[absolute_position]
                graphic = document.graphic_elements[graphic_token]
            except (KeyError, IndexError):
                fail("embedded-graphic character has no graphic element")
            if graphic is None:
                fail("embedded-graphic character references a free graphic element")
            pieces.append(("graphic", graphic, attr))
            cursor += 1
            continue
        end = cursor + 1
        while (
            end < len(raw)
            and raw[end] != 0x1A
            and run_token_at(article.char_runs, absolute_start + end) == token
        ):
            end += 1
        value = display_text(raw[cursor:end], 0)
        if value:
            pieces.append(("text", value, attr))
        cursor = end
    if line_flags & 0x00C0:
        hyphen_attr = document.char_attrs[run_token_at(article.char_runs, absolute_start + max(len(raw) - 1, 0))]
        pieces.append(("text", "-", hyphen_attr))
    if not pieces:
        return

    # FI_width is the cached layout width.  GeoWrite's CommonFieldDraw does
    # not scale glyphs to that value: it draws each style run at its natural
    # font width, adding the saved track kerning and the line's space pad.
    # Keep consuming FI_width as validated layout metadata, but never use it
    # as a substitute-font fitting hint (hidden CRs and tabs are included in
    # fields and make such fitting visibly wrong).
    if expected_width < 0:
        fail("LineInfo field has a negative width")

    context.save()
    context.translate(x, baseline)
    pen = 0.0
    for kind, value, attr in pieces:
        if kind == "graphic":
            assert isinstance(value, VisTextGraphic)
            context.save()
            if value.graphic_type == 1 and document.vm.legacy:
                page_text = str(page_number + 1)
                family, slant, weight = font_face(attr)
                context.select_font_face(family, slant, weight)
                context.set_font_size(max(attr.point_size, 1.0))
                text_advance = text_extents_advance(context.text_extents(page_text))
                context.translate(pen, 0.0)
                if text_advance > 0 and value.width > 0:
                    context.scale(value.width / text_advance, 1.0)
                context.set_source_rgb(*attr.color)
                context.show_text(page_text)
            else:
                context.translate(pen, -value.height)
                render_gstring(context, value, attr.color)
            context.restore()
            pen += float(value.width)
            continue
        assert isinstance(value, str)
        family, slant, weight = font_face(attr)
        context.save()
        context.translate(pen, 0.0)
        width_scale = attr.width / 100.0
        if width_scale <= 0:
            fail("VisText character attribute uses a non-positive font width")
        context.scale(width_scale, 1.0)
        context.select_font_face(family, slant, weight)
        original_size = attr.point_size
        script_scale = 0.5 if attr.styles & 0x0C else 1.0
        size = original_size * script_scale
        context.set_font_size(max(size, 1.0))
        vertical = 0.0
        if attr.styles & 0x04:
            # PC/GEOS defaults are SBS_DEFAULT=50 percent of the font size
            # and SBP_DEFAULT=50 percent of the unscaled font size down.
            vertical = original_size * 0.5
        elif attr.styles & 0x08:
            # SPS_DEFAULT and SPP_DEFAULT are likewise both exactly 50.
            vertical = -original_size * 0.5

        # Track kerning and full-justification padding are document-space
        # distances in PC/GEOS.  Divide them by the font-width transform while
        # laying out in the scaled local coordinate system.
        tracking = track_kerning_increment(size, attr.tracking) / width_scale
        local_space_pad = space_pad / width_scale
        manual_spacing = bool(tracking or (local_space_pad and " " in value))
        positions: list[tuple[str, float]] = []
        if manual_spacing:
            local_pen = 0.0
            for character in value:
                positions.append((character, local_pen))
                local_pen += text_extents_advance(context.text_extents(character))
                local_pen += tracking
                if character == " ":
                    local_pen += local_space_pad
        else:
            local_pen = text_extents_advance(context.text_extents(value))

        if attr.extended_styles & 0x0100:
            pattern_type, pattern_number = attr.background_pattern
            background_top = line_top - baseline
            if pattern_type == 0:
                context.new_path()
                context.rectangle(0.0, background_top, local_pen, line_height)
                paint_gstring_path(
                    context, True, attr.background_color,
                    attr.background_mask, None, 1,
                )
            else:
                # PatternDrawHatch temporarily establishes the null graphics
                # transform, so system hatches are page/device aligned rather
                # than restarting at each character range.  Its video-line
                # operation is one device pixel wide and square-capped.
                context.save()
                context.rectangle(0.0, background_top, local_pen, line_height)
                context.clip()
                context.identity_matrix()
                left, top, right, bottom = context.clip_extents()
                corners = ((left, top), (right, top), (left, bottom), (right, bottom))

                # Entries reproduce the system HatchLine records as
                # (angle, delta-X-along-line, dashed).  Every delta-Y is four.
                hatch_lines = {
                    0: ((90.0, 0.0, False),),
                    1: ((0.0, 0.0, False),),
                    2: ((45.0, 0.0, False),),
                    3: ((135.0, 0.0, False),),
                    4: ((0.0, 0.0, False), (90.0, 4.0, True)),
                    5: ((45.0, 0.0, False), (135.0, 4.0, True)),
                }[pattern_number]
                for angle, delta_x, dashed in hatch_lines:
                    radians = math.radians(angle)
                    direction = (math.cos(radians), math.sin(radians))
                    normal = (-direction[1], direction[0])
                    normal_extents = [x * normal[0] + y * normal[1] for x, y in corners]
                    along_extents = [x * direction[0] + y * direction[1] for x, y in corners]
                    first = math.floor(min(normal_extents) / 4.0) - 1
                    last = math.ceil(max(normal_extents) / 4.0) + 1
                    along_min = min(along_extents) - 2.0
                    along_max = max(along_extents) + 2.0
                    context.new_path()
                    for index in range(first, last + 1):
                        base_x = index * 4.0 * normal[0]
                        base_y = index * 4.0 * normal[1]
                        if not dashed:
                            context.move_to(
                                base_x + along_min * direction[0],
                                base_y + along_min * direction[1],
                            )
                            context.line_to(
                                base_x + along_max * direction[0],
                                base_y + along_max * direction[1],
                            )
                            continue
                        # The brick family's (4,4) repeat advances its dashed
                        # line four points along itself as it advances four
                        # points normally.  Emit the 4-on/4-off spans directly
                        # so that phase remains tied to the page origin.
                        phase = index * delta_x
                        dash = math.floor((along_min - phase) / 8.0) * 8.0 + phase
                        while dash <= along_max:
                            start = max(dash, along_min)
                            end = min(dash + 4.0, along_max)
                            if end > start:
                                context.move_to(
                                    base_x + start * direction[0],
                                    base_y + start * direction[1],
                                )
                                context.line_to(
                                    base_x + end * direction[0],
                                    base_y + end * direction[1],
                                )
                            dash += 8.0
                    context.set_dash(())
                    context.set_line_cap(cairo.LINE_CAP_SQUARE)
                    context.set_line_width(1.0)
                    paint_gstring_path(
                        context, False, attr.background_color,
                        attr.background_mask, None, 1,
                    )
                context.restore()

        context.set_source_rgb(*attr.color)
        if manual_spacing:
            for character, position in positions:
                context.move_to(position, vertical)
                context.show_text(character)
        else:
            context.move_to(0.0, vertical)
            context.show_text(value)
        if attr.styles & 0x01:
            context.set_line_width(max(0.45, size / 18.0))
            context.move_to(0.0, vertical + size * 0.12)
            context.line_to(local_pen, vertical + size * 0.12)
            context.stroke()
        if attr.styles & 0x02:
            context.set_line_width(max(0.45, size / 18.0))
            context.move_to(0.0, vertical - size * 0.3)
            context.line_to(local_pen, vertical - size * 0.3)
            context.stroke()
        context.restore()
        pen += local_pen * width_scale
    context.restore()


def apply_gr_obj_transform(context: cairo.Context, transform: GrObjTransform) -> None:
    context.translate(*transform.center)
    context.transform(cairo.Matrix(*cairo_safe_matrix(transform.matrix)))


def append_rounded_rectangle(
    context: cairo.Context, left: float, top: float, right: float, bottom: float, radius: float
) -> None:
    left, right = sorted((left, right))
    top, bottom = sorted((top, bottom))
    radius = min(abs(radius), (right - left) / 2.0, (bottom - top) / 2.0)
    if radius <= 0:
        context.rectangle(left, top, right - left, bottom - top)
        return
    context.new_sub_path()
    context.arc(right - radius, top + radius, radius, -math.pi / 2.0, 0.0)
    context.arc(right - radius, bottom - radius, radius, 0.0, math.pi / 2.0)
    context.arc(left + radius, bottom - radius, radius, math.pi / 2.0, math.pi)
    context.arc(left + radius, top + radius, radius, math.pi, 3.0 * math.pi / 2.0)
    context.close_path()


def paint_gr_obj_path(
    context: cairo.Context,
    document: GeoWriteDocument,
    node: GrObjNode,
    allow_fill: bool,
) -> None:
    area = document.grobj_area_attrs.get(node.area_token)
    line = document.grobj_line_attrs.get(node.line_token)
    saved_path = context.copy_path()
    if allow_fill and area is not None and not area.transparent:
        if area.gradient is None or area.gradient[0] == 0:
            paint_gstring_path(context, True, area.color, area.mask, None, area.draw_mode)
        else:
            gradient_type, ending, _, _ = area.gradient
            width, height = node.transform.size
            left, right = sorted((-width / 2.0, width / 2.0))
            top, bottom = sorted((-height / 2.0, height / 2.0))
            if gradient_type == 1:
                pattern: cairo.Pattern = cairo.LinearGradient(left, 0.0, right, 0.0)
            elif gradient_type == 2:
                pattern = cairo.LinearGradient(0.0, top, 0.0, bottom)
            elif gradient_type in (3, 4):
                pattern = cairo.RadialGradient(0.0, 0.0, 0.0, 0.0, 0.0, max(abs(width), abs(height)) / 2.0)
            else:
                fail("unsupported GrObj gradient type")
            pattern.add_color_stop_rgb(0.0, *area.color)
            pattern.add_color_stop_rgb(1.0, *ending)
            context.set_source(pattern)
            context.fill()
        context.new_path()
        context.append_path(saved_path)
    if line is not None and draw_mask_rows(line.mask, None) != b"\0" * 8:
        configure_gstring_line(
            context, max(0.0, line.width), line.end, line.join,
            max(line.miter_limit, 1.0), line.style, 0,
        )
        paint_gstring_path(context, False, line.color, line.mask, None, line.draw_mode)
    else:
        context.new_path()


def append_gr_obj_spline(context: cairo.Context, node: GrObjNode) -> tuple[bool, bool]:
    if node.arc_data is None:
        fail("GrObj spline lacks its saved SplineState")
    state = node.arc_data[0]
    points = [
        (child.transform.center[0], child.transform.center[1], child.optr[1])
        for child in node.children
    ]
    curved = any(info & 0x80 for _, _, info in points)
    anchors: list[tuple[tuple[float, float], tuple[float, float], tuple[float, float]]] = []
    if curved:
        used_controls: set[int] = set()
        for index, anchor in enumerate(points):
            if anchor[2] & 0x80:
                continue
            previous = anchor[:2]
            following = anchor[:2]
            if index and points[index - 1][2] & 0x90 == 0x90:
                previous = points[index - 1][:2]
                used_controls.add(index - 1)
            if index + 1 < len(points) and points[index + 1][2] & 0x80 and not points[index + 1][2] & 0x10:
                following = points[index + 1][:2]
                used_controls.add(index + 1)
            anchors.append((previous, anchor[:2], following))
        all_controls = {index for index, point in enumerate(points) if point[2] & 0x80}
        if used_controls != all_controls:
            fail("VisSpline contains an unattached or misordered control point")
    else:
        anchors = [(point[:2], point[:2], point[:2]) for point in points]
    if not anchors:
        fail("saved VisSpline contains no anchor")
    closed = bool(state & 0x40)
    context.move_to(*anchors[0][1])
    segment_count = len(anchors) if closed else len(anchors) - 1
    for index in range(segment_count):
        left, right = anchors[index], anchors[(index + 1) % len(anchors)]
        if curved:
            context.curve_to(*left[2], *right[0], *right[1])
        else:
            context.line_to(*right[1])
    if closed:
        context.close_path()
    return bool(state & 0x20), closed


def apply_guardian_to_ward(context: cairo.Context, node: GrObjNode) -> bool:
    if node.ward_bounds is None:
        fail("GrObj guardian lacks saved Vis bounds")
    left, top, right, bottom = node.ward_bounds
    vis_width, vis_height = right - left, bottom - top
    width, height = node.transform.size
    if not vis_width and width:
        fail("GrObj guardian has zero Vis width but nonzero object width")
    if not vis_height and height:
        fail("GrObj guardian has zero Vis height but nonzero object height")
    if not vis_width and not vis_height and not width and not height and not node.children:
        return False
    context.scale(width / vis_width if vis_width else 1.0, height / vis_height if vis_height else 1.0)
    context.translate(-(left + right) / 2.0, -(top + bottom) / 2.0)
    return True


def render_gr_obj_text(
    context: cairo.Context, document: GeoWriteDocument, node: GrObjNode, page_number: int
) -> None:
    if node.text is None or node.ward_bounds is None:
        fail("GrObj text node lacks parsed text or ward bounds")
    article = node.text
    left, top, right, bottom = node.ward_bounds
    context.save()
    context.rectangle(left, top, right - left, bottom - top)
    context.clip()
    text_position = 0
    line_top = top
    for line in article.lines:
        baseline = line_top + line.baseline
        field_position = text_position
        for field_index, field_info in enumerate(line.fields):
            raw_field = article.raw_text[field_position : field_position + field_info.char_count]
            render_field(
                context, document, article, raw_field, field_position,
                left + line.adjustment + field_info.position,
                baseline, line_top, line.height, field_info.width,
                line.flags if field_index == len(line.fields) - 1 else 0,
                line.space_pad if field_index == len(line.fields) - 1 else 0.0,
                page_number,
            )
            field_position += field_info.char_count
        text_position += line.char_count
        line_top += line.height
    context.restore()


def append_gr_obj_basic_path(context: cairo.Context, node: GrObjNode) -> None:
    """Append the OBJECT-space path for a non-guardian geometric GrObj."""
    width, height = node.transform.size
    left, top, right, bottom = -width / 2.0, -height / 2.0, width / 2.0, height / 2.0
    if node.kind == "rect":
        x1, x2 = sorted((left, right))
        y1, y2 = sorted((top, bottom))
        context.rectangle(x1, y1, x2 - x1, y2 - y1)
    elif node.kind == "round_rect":
        append_rounded_rectangle(context, left, top, right, bottom, node.radius)
    elif node.kind == "ellipse":
        append_gstring_ellipse(context, left, top, right, bottom)
    elif node.kind == "line":
        context.move_to(left, 0.0)
        context.line_to(right, 0.0)
    elif node.kind == "arc":
        if node.arc_data is None:
            fail("GrObj arc lacks saved arc data")
        close_type, start_angle, end_angle = node.arc_data
        context.save()
        context.scale(abs(width) / 2.0, abs(height) / 2.0)
        context.arc_negative(0.0, 0.0, 1.0, math.radians(-start_angle), math.radians(-end_angle))
        context.restore()
        if close_type == 1:
            context.close_path()
        elif close_type == 2:
            context.line_to(0.0, 0.0)
            context.close_path()
    else:
        fail(f"internal request for a basic path from {node.kind}")


def render_gr_obj_clip_node(
    context: cairo.Context, document: GeoWriteDocument, node: GrObjNode, page_number: int
) -> None:
    """Draw the saved MSG_GO_DRAW_CLIP_AREA result into an alpha group."""
    context.save()
    apply_gr_obj_transform(context, node.transform)
    width, height = node.transform.size
    context.set_source_rgb(1.0, 1.0, 1.0)
    if node.kind == "group":
        # GroupDrawClipArea explicitly excludes paste-inside children, even
        # when this group has a paste-inside composition of its own.
        for child in node.children:
            if not child.attr_flags & 0x0080:
                render_gr_obj_clip_node(context, document, child, page_number)
    elif node.kind in ("rect", "round_rect", "ellipse", "arc"):
        context.new_path()
        append_gr_obj_basic_path(context, node)
        context.fill()
    elif node.kind == "line":
        # LineDrawFGArea/LineDrawClipArea is deliberately empty in PC/GEOS.
        pass
    elif node.kind == "spline":
        if apply_guardian_to_ward(context, node) and node.children:
            assert node.ward_bounds is not None
            context.translate(node.ward_bounds[0], node.ward_bounds[1])
            context.new_path()
            _, closed = append_gr_obj_spline(context, node)
            if closed:
                context.fill()
    elif node.kind == "bitmap":
        # BitmapGuardian overrides the Vis ward's clip-area method with the
        # guardian's full OBJECT rectangle; bitmap transparency is irrelevant.
        x1, x2 = sorted((-width / 2.0, width / 2.0))
        y1, y2 = sorted((-height / 2.0, height / 2.0))
        context.rectangle(x1, y1, x2 - x1, y2 - y1)
        context.fill()
    elif node.kind == "text":
        # The generic VisGuardian clip-area method asks its ward to draw.  An
        # alpha group captures the exact visible glyph coverage as a clip mask.
        if apply_guardian_to_ward(context, node):
            render_gr_obj_text(context, document, node, page_number)
    elif node.kind == "gstring":
        # GStringDrawClipArea executes the saved string while a path is being
        # defined.  The alpha group is equivalent for the saved drawing ops.
        if node.gstring is None:
            fail("GrObj GString node lacks parsed GString data")
        line = document.grobj_line_attrs.get(node.line_token)
        area = document.grobj_area_attrs.get(node.area_token)
        initial = line.color if line is not None else area.color if area is not None else (0.0, 0.0, 0.0)
        render_gstring(
            context,
            VisTextGraphic(
                abs(round(width)), abs(round(height)), 0, 0, IDENTITY_MATRIX,
                node.gstring_offset, node.gstring,
            ),
            initial, line, area,
        )
    elif node.kind == "flow":
        pass
    else:
        fail(f"unsupported GrObj clip-area node kind {node.kind}")
    context.restore()


def render_gr_obj_group(
    context: cairo.Context, document: GeoWriteDocument, node: GrObjNode, page_number: int
) -> None:
    normal = [child for child in node.children if not child.attr_flags & 0x0080]
    pasted = [child for child in node.children if child.attr_flags & 0x0080]
    for child in normal:
        render_gr_obj_node(context, document, child, page_number)
    if not pasted:
        return

    # GroupDoPasteInside creates a union path from normal children, intersects
    # it with the existing clip, and then draws paste-inside children through
    # it.  Two Cairo groups retain the same affine/device-space alignment while
    # reproducing that source-through-alpha operation.
    context.push_group()
    for child in normal:
        render_gr_obj_clip_node(context, document, child, page_number)
    clip_pattern = context.pop_group()
    context.push_group()
    for child in pasted:
        render_gr_obj_node(context, document, child, page_number)
    pasted_pattern = context.pop_group()
    context.set_source(pasted_pattern)
    context.mask(clip_pattern)


def render_gr_obj_node(
    context: cairo.Context, document: GeoWriteDocument, node: GrObjNode, page_number: int
) -> None:
    if node.kind == "flow":
        return
    context.save()
    apply_gr_obj_transform(context, node.transform)
    width, height = node.transform.size
    if node.kind == "group":
        render_gr_obj_group(context, document, node, page_number)
    elif node.kind in ("rect", "round_rect", "ellipse", "line", "arc"):
        context.new_path()
        append_gr_obj_basic_path(context, node)
        paint_gr_obj_path(context, document, node, node.kind != "line")
    elif node.kind == "spline":
        visible = apply_guardian_to_ward(context, node)
        if visible and node.children:
            # VisSpline stores its points in local coordinates, then its draw
            # setup applies VI_bounds.left/top.  This translation is separate
            # from the guardian's centered VIS-to-OBJECT mapping above.
            assert node.ward_bounds is not None
            context.translate(node.ward_bounds[0], node.ward_bounds[1])
            context.new_path()
            filled, _ = append_gr_obj_spline(context, node)
            paint_gr_obj_path(context, document, node, filled)
    elif node.kind == "bitmap":
        if node.bitmap is None or node.ward_bounds is None:
            fail("GrObj bitmap node lacks parsed bitmap data")
        if apply_guardian_to_ward(context, node):
            draw_bitmap_raster(
                context, node.bitmap, node.ward_bounds[0], node.ward_bounds[1],
                IDENTITY_MATRIX, [], None,
            )
    elif node.kind == "text":
        if apply_guardian_to_ward(context, node):
            render_gr_obj_text(context, document, node, page_number)
    elif node.kind == "gstring":
        if node.gstring is None:
            fail("GrObj GString node lacks parsed GString data")
        line = document.grobj_line_attrs.get(node.line_token)
        area = document.grobj_area_attrs.get(node.area_token)
        initial = line.color if line is not None else area.color if area is not None else (0.0, 0.0, 0.0)
        render_gstring(
            context,
            VisTextGraphic(abs(round(width)), abs(round(height)), 0, 0, IDENTITY_MATRIX, node.gstring_offset, node.gstring),
            initial, line, area,
        )
    else:
        fail(f"internal unsupported GrObj node kind {node.kind}")
    context.restore()


def render_article_region(
    context: cairo.Context,
    document: GeoWriteDocument,
    article: Article,
    region: Region,
    lines: Sequence[LineInfo],
    region_text_start: int,
    page_number: int,
) -> None:
    context.save()
    context.rectangle(region.x, region.y, region.width, region.height)
    context.clip()
    top = float(region.y)
    text_position = region_text_start
    for line in lines:
        baseline = top + line.baseline
        field_text_position = text_position
        for field_index, field_info in enumerate(line.fields):
            raw_field = article.raw_text[field_text_position : field_text_position + field_info.char_count]
            render_field(
                context, document, article, raw_field, field_text_position,
                region.x + line.adjustment + field_info.position,
                baseline, top, line.height, field_info.width,
                line.flags if field_index == len(line.fields) - 1 else 0,
                line.space_pad if field_index == len(line.fields) - 1 else 0.0,
                page_number,
            )
            field_text_position += field_info.char_count
        text_position += line.char_count
        top += line.height
    context.restore()


def render_pdf(document: GeoWriteDocument, destination: pathlib.Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(prefix=f".{destination.name}.", suffix=".tmp", dir=destination.parent)
    os.close(fd)
    temporary = pathlib.Path(temporary_name)
    try:
        surface = cairo.PDFSurface(str(temporary), document.width, document.height)
        if hasattr(surface, "set_metadata"):
            surface.set_metadata(cairo.PDF_METADATA_TITLE, document.vm.long_name or destination.stem)
            surface.set_metadata(cairo.PDF_METADATA_CREATOR, "geoWorksGeoWriteDocument.py")
        context = cairo.Context(surface)

        page_lines: list[list[tuple[Article, Region, list[LineInfo], int]]] = [
            [] for _ in range(document.total_pages)
        ]
        regions_by_object: dict[tuple[int, int], tuple[Article, Region, list[LineInfo], int]] = {}
        for article in document.articles:
            line_index = 0
            text_position = 0
            for region in article.regions:
                lines = article.lines[line_index : line_index + region.line_count]
                page = int(region.y // document.height)
                if page < 0 or page >= document.total_pages:
                    fail("text region lies outside declared document pages")
                page_lines[page].append((article, region, lines, text_position))
                if document.grobj_body is not None:
                    object_optr = (region.object_optr[1], region.object_optr[0])
                    if object_optr in regions_by_object:
                        fail("multiple article regions reference the same FlowRegion object")
                    regions_by_object[object_optr] = (article, region, lines, text_position)
                line_index += region.line_count
                text_position += region.char_count

        if document.grobj_body is not None:
            flow_objects = {node.optr for node in document.grobj_body.children if node.kind == "flow"}
            if flow_objects != set(regions_by_object):
                fail("GrObjBody FlowRegion list does not correspond exactly to article regions")

        for page_number in range(document.total_pages):
            surface.set_size(document.width, document.height)
            context.set_source_rgb(1, 1, 1)
            context.paint()
            if document.grobj_body is not None:
                context.save()
                context.rectangle(0, 0, document.width, document.height)
                context.clip()
                context.translate(0.0, -page_number * document.height)
                for node in document.grobj_body.children:
                    if node.kind == "flow":
                        article, region, lines, region_text_start = regions_by_object[node.optr]
                        if int(region.y // document.height) == page_number:
                            render_article_region(
                                context, document, article, region, lines,
                                region_text_start, page_number,
                            )
                    else:
                        render_gr_obj_node(context, document, node, page_number)
                context.restore()
            else:
                for article, region, lines, region_text_start in page_lines[page_number]:
                    context.save()
                    context.translate(0.0, -page_number * document.height)
                    render_article_region(
                        context, document, article, region, lines,
                        region_text_start, page_number,
                    )
                    context.restore()
            context.show_page()
        surface.finish()
        os.chmod(temporary, 0o664)
        os.replace(temporary, destination)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def convert(input_name: str, output_name: str) -> GeoWriteDocument:
    source = pathlib.Path(input_name)
    destination = pathlib.Path(output_name)
    raw = source.read_bytes()
    document = GeoWriteDocument.parse(raw)
    render_pdf(document, destination)
    return document


def build_report(
    sample_root_names: str | Sequence[str], output_root_name: str, report_name: str
) -> int:
    """One-time corpus conversion/report mode used to produce the requested audit."""
    names = [sample_root_names] if isinstance(sample_root_names, str) else list(sample_root_names)
    sample_roots = [pathlib.Path(name).resolve() for name in names]
    if not sample_roots:
        fail("report mode requires at least one sample directory")
    if any(not root.is_dir() for root in sample_roots):
        fail("every report sample root must be a directory")
    if len({root.name for root in sample_roots}) != len(sample_roots):
        fail("report sample directories must have distinct base names")
    output_root = pathlib.Path(output_root_name).resolve()
    report = pathlib.Path(report_name).resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    records: list[tuple[pathlib.Path, pathlib.Path | None, pathlib.Path | None, str, list[str]]] = []
    for sample_root in sample_roots:
        for source in sorted(path for path in sample_root.rglob("*") if path.is_file()):
            relative = pathlib.Path(sample_root.name) / source.relative_to(sample_root)
            pdf = output_root / relative.parent / f"{source.name}.pdf"
            thumbnail = output_root / relative.parent / f"{source.name}.png"
            try:
                document = convert(str(source), str(pdf))
                thumbnail.parent.mkdir(parents=True, exist_ok=True)
                subprocess.run(
                    [
                        "pdftoppm",
                        "-f",
                        "1",
                        "-singlefile",
                        "-scale-to-x",
                        "420",
                        "-scale-to-y",
                        "-1",
                        "-png",
                        str(pdf),
                        str(thumbnail.with_suffix("")),
                    ],
                    check=True,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                )
                os.chmod(pdf, 0o664)
                os.chmod(thumbnail, 0o664)
                records.append((relative, pdf, thumbnail, "Converted", document.feature_notes))
            except Exception as exc:
                records.append((relative, None, None, f"Skipped: {exc}", []))

    by_directory: dict[pathlib.Path, list[tuple[pathlib.Path, pathlib.Path | None, pathlib.Path | None, str, list[str]]]] = {}
    for record in records:
        by_directory.setdefault(record[0].parent, []).append(record)
    parts = [
        "<!doctype html>",
        "<!-- Vibe coded by Codex -->",
        '<html lang="en"><head><meta charset="utf-8">',
        '<meta name="viewport" content="width=device-width,initial-scale=1">',
        "<title>GeoWorks GeoWrite conversion report</title>",
        "<style>",
        ":root{color-scheme:dark}*{box-sizing:border-box}body{margin:0;background:#0b0f14;color:#dce7f3;font:15px/1.45 system-ui,sans-serif}",
        "header{position:sticky;top:0;z-index:2;padding:18px 24px;background:#111923eF;border-bottom:1px solid #2a394a;backdrop-filter:blur(8px)}",
        "main{padding:16px 24px 40px}h1{margin:0 0 5px;font-size:23px}h2{margin:28px 0 12px;color:#8fd3ff}",
        ".summary{color:#9db0c3}.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(285px,1fr));gap:14px}",
        ".card{min-width:0;padding:11px;background:#121a24;border:1px solid #2a394a;border-radius:10px;box-shadow:0 5px 18px #0006}",
        ".preview{display:block;aspect-ratio:4/3;background:#080b0f;border-radius:6px;overflow:hidden}.preview img{width:100%;height:100%;object-fit:contain}",
        ".name{margin:9px 0 4px;overflow-wrap:anywhere}.ok{color:#86e3a6}.skip{color:#ffad9f}.note{color:#aebdca;font-size:12px;margin-top:5px}",
        ".scope{margin:14px 0 4px;padding:12px 14px;border:1px solid #725e2c;background:#211d12;color:#ead59a;border-radius:8px}",
        "a{color:#8fd3ff;text-decoration:none}a:hover{text-decoration:underline}</style></head><body>",
        "<header><h1>GeoWorks GeoWrite conversion report</h1>",
        f'<div class="summary">{sum(r[1] is not None for r in records)} converted · {sum(r[1] is None for r in records)} skipped · {len(records)} total</div></header><main>',
        '<div class="scope">Verification scope: the previews render saved text from protocol-1 and protocol-3 documents, exact line/field records, native font advances, face-aware FontID substitution, FontWidth, track kerning, last-field space padding, style runs, character background colors and system hatches, exact super/subscript defaults, columns, regions, page coordinates, protocol-1 header/footer text and page-number variables, protocol-1 embedded GString text fields and vector primitives, and embedded GString Bitmap/CBitmap operations. Protocol-3 output also paints the GrObjBody in saved z-order: groups and paste-inside compositions, rectangles, rounded rectangles, ellipses, lines, arcs, editable HugeArray bitmaps, small-text guardians, spline guardians, and bitmap/vector GString objects with affine transforms, attributes, masks, state, and rectangular or native-path clipping. Protocol-3 master-page object trees beyond their article FlowRegions, DB-backed non-rectangular text-flow clipping, uncommon non-text GraphicPattern fills, arrowheads, and some extended GString/text effects remain validation-only.</div>',
    ]
    for directory, directory_records in sorted(by_directory.items(), key=lambda item: str(item[0])):
        parts.append(f"<section><h2>{html.escape(str(directory))}</h2><div class=\"grid\">")
        for relative, pdf, thumbnail, status, notes in directory_records:
            parts.append('<article class="card">')
            if pdf is not None and thumbnail is not None:
                pdf_href = os.path.relpath(pdf, report.parent)
                thumb_href = os.path.relpath(thumbnail, report.parent)
                parts.append(
                    f'<a class="preview" href="{html.escape(pdf_href)}" target="_blank" rel="noopener"><img loading="lazy" src="{html.escape(thumb_href)}" alt="First page of {html.escape(relative.name)}"></a>'
                )
                parts.append(f'<div class="name"><a href="{html.escape(pdf_href)}" target="_blank" rel="noopener">{html.escape(relative.name)}</a></div>')
                parts.append(f'<div class="ok">{html.escape(status)}</div>')
                if notes:
                    parts.append(f'<div class="note">Detected: {html.escape("; ".join(notes))}</div>')
            else:
                parts.append('<div class="preview"></div>')
                parts.append(f'<div class="name">{html.escape(relative.name)}</div><div class="skip">{html.escape(status)}</div>')
            parts.append("</article>")
        parts.append("</div></section>")
    parts.append("</main></body></html>\n")
    report.parent.mkdir(parents=True, exist_ok=True)
    temporary = report.with_name(f".{report.name}.tmp")
    temporary.write_text("".join(parts), encoding="utf-8")
    os.chmod(temporary, 0o664)
    os.replace(temporary, report)
    for directory in [output_root, *[p for p in output_root.rglob("*") if p.is_dir()]]:
        os.chmod(directory, 0o775)
    return 0 if all(record[1] is not None for record in records) else 2


def main(argv: Sequence[str]) -> int:
    if len(argv) >= 5 and argv[1] == "--build-report":
        return build_report(argv[2:-2], argv[-2], argv[-1])
    if len(argv) != 3:
        print(f"usage: {pathlib.Path(argv[0]).name} <inputFile> <outputFile>", file=sys.stderr)
        return 2
    try:
        document = convert(argv[1], argv[2])
    except (FormatError, OSError, cairo.Error) as exc:
        print(f"{pathlib.Path(argv[0]).name}: {exc}", file=sys.stderr)
        return 1
    if document.feature_notes:
        print("warning: " + "; ".join(document.feature_notes), file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

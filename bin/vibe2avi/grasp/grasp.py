#!/usr/bin/env python3
# Vibe coded by Codex
"""Native GRASP GL animation to AVI converter with bounded damage recovery."""

from __future__ import annotations

import argparse
import ast
from array import array
from dataclasses import dataclass
import math
import os
from pathlib import Path
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import wave


FPS = 20
SAMPLE_RATE = 44100
OUT_WIDTH, OUT_HEIGHT = 640, 480
AUTO_WAIT = 60                 # hundredths: a short but readable key press
FADE_BYTES_PER_FRAME = 65536   # deterministic baseline DOS video-memory rate
MAX_STEPS = 2_000_000
MAX_FRAMES = FPS * 60 * 60
ENTRY_SIZE, NAME_SIZE = 17, 13
class GraspError(Exception):
    """A malformed file or unsupported, non-deterministic presentation."""


def fail(message: str) -> GraspError:
    return GraspError(message)


def u16(data: bytes, at: int) -> int:
    if at + 2 > len(data):
        raise fail("truncated 16-bit field")
    return struct.unpack_from("<H", data, at)[0]


def u32(data: bytes, at: int) -> int:
    if at + 4 > len(data):
        raise fail("truncated 32-bit field")
    return struct.unpack_from("<I", data, at)[0]


@dataclass(frozen=True)
class Member:
    name: str
    payload: bytes
    damage: str | None = None


@dataclass(frozen=True)
class Library:
    members: tuple[Member, ...]

    def by_name(self) -> dict[str, Member]:
        return {m.name.casefold(): m for m in self.members}


def parse_library(path: Path) -> Library:
    try:
        data = path.read_bytes()
    except OSError as exc:
        raise fail(f"cannot read input: {exc}") from exc
    if len(data) < 40:
        raise fail("not a GRASP GL file: too short")
    marker, data_offset, reserved = struct.unpack_from("<HHH", data)
    if marker < 34 or marker % ENTRY_SIZE or data_offset != marker + 2 or reserved:
        raise fail("not a GRASP GL file: invalid directory header")
    count = marker // ENTRY_SIZE - 1
    directory_end = 6 + ENTRY_SIZE * count
    if count < 1 or directory_end > data_offset or data_offset > len(data):
        raise fail("not a GRASP GL file: invalid directory extent")
    directory_tail = data[directory_end:data_offset]
    if directory_tail and (len(set(directory_tail)) != 1
                           or directory_tail[0] not in (0x00, 0x20, 0xff)):
        raise fail("invalid reserved-directory fill bytes")
    members: list[Member] = []
    names: set[str] = set()
    start = data_offset
    for i in range(count):
        at = 6 + ENTRY_SIZE * i
        raw = data[at:at + NAME_SIZE]
        try:
            nul = raw.index(0)
        except ValueError as exc:
            raise fail(f"directory entry {i + 1}: unterminated name") from exc
        if not nul or any(raw[nul + 1:]):
            raise fail(f"directory entry {i + 1}: invalid name padding")
        try:
            name = raw[:nul].decode("ascii")
        except UnicodeDecodeError as exc:
            raise fail(f"directory entry {i + 1}: non-ASCII name") from exc
        if not re.fullmatch(r"[A-Za-z0-9!#$%&'()@^_`{}~.\-]{1,12}", name):
            raise fail(f"invalid DOS member name {name!r}")
        folded = name.casefold()
        if folded in names:
            raise fail(f"duplicate member name {name!r}")
        names.add(folded)
        end_field = u32(data, at + NAME_SIZE)
        if i == count - 1:
            if end_field:
                raise fail("last directory entry lacks the zero EOF sentinel")
            end = len(data)
        else:
            end = end_field
            if end <= start:
                raise fail(f"member {name}: invalid absolute end offset")
        physical_start = min(start, len(data))
        physical_end = min(end, len(data))
        stored = data[physical_start:physical_end]
        damage: str | None = None
        if start >= len(data):
            damage = "member data is absent after a truncated GL payload"
        elif end > len(data):
            damage = "member data is truncated at physical end-of-file"
        if len(stored) < 4:
            payload = b""
            damage = damage or "member is missing its length prefix"
        else:
            payload_size = u32(stored, 0)
            available = len(stored) - 4
            if payload_size > available:
                payload = stored[4:]
                damage = damage or "length prefix exceeds the available member extent"
            else:
                payload = stored[4:4 + payload_size]
                member_padding = stored[4 + payload_size:]
                if member_padding and any(value not in (0x00, 0x1a)
                                          for value in member_padding):
                    damage = damage or "member has non-padding bytes after its payload"
        members.append(Member(name, payload, damage))
        start = end
    if start < len(data):
        raise fail("member chain does not account for the entire GL file")
    return Library(tuple(members))


EGA16 = ((0, 0, 0), (0, 0, 170), (0, 170, 0), (0, 170, 170),
         (170, 0, 0), (170, 0, 170), (170, 85, 0), (170, 170, 170),
         (85, 85, 85), (85, 85, 255), (85, 255, 85), (85, 255, 255),
         (255, 85, 85), (255, 85, 255), (255, 255, 85), (255, 255, 255))
CGA4 = ((0, 0, 0), (0, 170, 170), (170, 0, 170), (170, 170, 170))
CGA_PALETTE_REGISTERS = ((2, 3, 3, 10, 11, 11),
                         (4, 5, 4, 12, 13, 12),
                         (6, 15, 15, 14, 15, 15))
VGA256 = tuple((r * 36, g * 36, b * 85) for r in range(8) for g in range(8) for b in range(4))


def ega_register(value: int) -> tuple[int, int, int]:
    if value > 63:
        raise fail("EGA palette register exceeds 6 bits")
    return (((85 if value & 0x20 else 0) + (170 if value & 0x04 else 0)),
            ((85 if value & 0x10 else 0) + (170 if value & 0x02 else 0)),
            ((85 if value & 0x08 else 0) + (170 if value & 0x01 else 0)))


@dataclass(frozen=True)
class Raster:
    width: int
    height: int
    xoff: int
    yoff: int
    pixels: bytes                 # row-major, top to bottom, palette indices
    palette: tuple[tuple[int, int, int], ...] | None = None
    packed_width: int | None = None
    packed_pixels: bytes | None = None
    display_width: int | None = None
    display_height: int | None = None
    recovery: str | None = None


def marker_unpack(data: bytes, marker: int, expected: int, what: str) -> bytes:
    out = bytearray()
    pos = 0
    while pos < len(data):
        value = data[pos]
        pos += 1
        if value != marker:
            out.append(value)
            continue
        if pos >= len(data):
            raise fail(f"{what}: truncated packed run")
        count = data[pos]
        pos += 1
        if count == 0:
            if pos + 2 > len(data):
                raise fail(f"{what}: truncated extended packed run")
            count = u16(data, pos)
            pos += 2
            if count == 0:
                raise fail(f"{what}: zero-length extended packed run")
        if pos >= len(data):
            raise fail(f"{what}: packed run lacks its value")
        out.extend(bytes((data[pos],)) * count)
        pos += 1
        if len(out) > expected:
            raise fail(f"{what}: packed data expands past its declared size")
    if expected - 64 <= len(out) < expected:
        # Several surviving files from early sector-copy tools lose only the
        # final handful of packed bytes. DOS video memory remained zero in
        # those cells, so bounded zero completion reproduces that behavior.
        out.extend(bytes(expected - len(out)))
    if len(out) != expected:
        raise fail(f"{what}: packed data expands to {len(out)}, expected {expected}")
    return bytes(out)


def planar_pixels(raw: bytes, width: int, height: int, bits: int, planes: int,
                  what: str) -> bytes:
    if width <= 0 or height <= 0 or bits not in (1, 2, 4, 8) or planes <= 0:
        raise fail(f"{what}: invalid geometry or plane layout")
    row_bytes = (width * bits + 7) // 8
    if len(raw) != row_bytes * height * planes:
        raise fail(f"{what}: decoded plane byte count is not exact")
    out = bytearray(width * height)
    mask = (1 << bits) - 1
    for plane in range(planes):
        base = plane * row_bytes * height
        shift = plane * bits
        for stored_y in range(height):
            y = height - 1 - stored_y
            row = raw[base + stored_y * row_bytes:base + (stored_y + 1) * row_bytes]
            for x in range(width):
                bit = x * bits
                value = (row[bit >> 3] >> (8 - bits - (bit & 7))) & mask
                out[y * width + x] |= value << shift
    return bytes(out)


def text_capture_pixels(name: str, cells: bytes, byte_width: int,
                        rows: int) -> tuple[int, int, bytes]:
    """Expand Pictor text-memory character/attribute pairs into indexed pixels."""
    if byte_width < 2 or byte_width & 1 or len(cells) != byte_width * rows:
        raise fail(f"{name}: invalid text-page byte geometry")
    columns = byte_width // 2
    width, height = columns * 8, rows * 16
    font = text_mode_font()
    pixels = bytearray(width * height)
    for cell_row in range(rows):
        source = cell_row * byte_width
        pixel_top = cell_row * 16
        for column in range(columns):
            character, attribute = cells[source + column * 2:source + column * 2 + 2]
            foreground, background = attribute & 0x0f, (attribute >> 4) & 0x07
            left = column * 8
            for glyph_row in range(16):
                destination = (pixel_top + glyph_row) * width + left
                pixels[destination:destination + 8] = bytes((background,)) * 8
            glyph = font.glyphs[character]
            for glyph_row in range(16):
                bits = glyph[glyph_row]
                destination = (pixel_top + glyph_row) * width + left
                for column_bit in range(8):
                    if bits & (0x80 >> column_bit):
                        pixels[destination + column_bit] = foreground
    return width, height, bytes(pixels)


def pictor_palette(kind: int, extra: bytes) -> tuple[tuple[int, int, int], ...] | None:
    if kind == 0:
        if any(extra):
            raise fail("Pictor no-palette descriptor has data")
        return None
    if kind == 1:
        if len(extra) < 2 or any(extra[2:]):
            raise fail("Pictor CGA descriptor has invalid data or reserved padding")
        # Byte zero is palette/intensity, byte one is border; retain canonical CGA colors.
        return CGA4
    if kind in (2, 3):
        if len(extra) != 16:
            raise fail("Pictor EGA descriptor must be 16 bytes")
        if kind == 2:
            return tuple(EGA16[v & 15] for v in extra)
        return tuple(ega_register(v) for v in extra)
    if kind in (4, 5):
        wanted = 768 if kind == 4 else 48
        if not extra or all(value == 0xff for value in extra):
            # Pictor writers use an empty or FF-filled DAC field to mean that
            # the captured clipping carries no palette of its own.
            return None
        if len(extra) != wanted or any(v > 63 for v in extra):
            raise fail("Pictor DAC descriptor has invalid length or component")
        return tuple(tuple(extra[i + j] * 255 // 63 for j in range(3))
                     for i in range(0, len(extra), 3))
    raise fail(f"unsupported Pictor palette descriptor {kind}")


def decode_pictor(name: str, data: bytes) -> Raster:
    if len(data) < 11:
        raise fail(f"{name}: truncated Pictor header")
    recommended_mode: int | None = None
    recovery: str | None = None
    if u16(data, 0) == 0x1234:
        if len(data) < 19 or data[11] != 0xFF:
            raise fail(f"{name}: malformed extended Pictor header")
        width, height, xoff, yoff = struct.unpack_from("<HHhh", data, 2)
        plane_info = data[10]
        # data[12] is only a display-mode recommendation. Early writers use
        # either an ASCII GRASP mode letter or zero when no mode is preferred.
        recommended_mode = data[12]
        descriptor, extra_size = struct.unpack_from("<HH", data, 13)
        pos = 17
        if pos + extra_size + 2 > len(data):
            raise fail(f"{name}: truncated Pictor palette descriptor")
        palette = pictor_palette(descriptor, data[pos:pos + extra_size])
        pos += extra_size
        blocks = u16(data, pos)
        pos += 2
        expected = ((width * (plane_info & 15) + 7) // 8) * height * ((plane_info >> 4) + 1)
        if blocks == 0:
            raw = data[pos:]
            if len(raw) != expected:
                raise fail(f"{name}: raw Pictor data length is not exact")
        else:
            raw_parts: list[bytes] = []
            total = 0
            for block in range(blocks):
                if pos + 5 > len(data):
                    raise fail(f"{name}: truncated Pictor block {block + 1}")
                packed_size, unpacked_size = struct.unpack_from("<HH", data, pos)
                marker = data[pos + 4]
                if packed_size < 5 or pos + packed_size > len(data):
                    raise fail(f"{name}: invalid Pictor block size")
                raw_parts.append(marker_unpack(data[pos + 5:pos + packed_size], marker,
                                               unpacked_size, name))
                total += unpacked_size
                pos += packed_size
            if total != expected:
                raise fail(f"{name}: Pictor blocks do not account for the declared raster")
            if pos != len(data):
                recovery = (f"{name}: ignored {len(data) - pos} unreferenced bytes after "
                            "a complete exact Pictor block stream")
            raw = b"".join(raw_parts)
    else:
        meaningful, width, height, xoff, yoff = struct.unpack_from("<HHHhh", data)
        if meaningful < 11 or meaningful > len(data) or any(data[meaningful:]):
            raise fail(f"{name}: invalid old-Pictor size or nonzero sector padding")
        plane_info = data[10]
        if plane_info == 0xFF:
            if meaningful < 13:
                raise fail(f"{name}: truncated old-Pictor packed header")
            plane_info, marker, pos = data[11], data[12], 13
        else:
            marker, pos = -1, 11
        bits, planes = plane_info & 15, (plane_info >> 4) + 1
        expected = ((width * bits + 7) // 8) * height * planes
        packed = data[pos:meaningful]
        raw = packed if marker < 0 else marker_unpack(packed, marker, expected, name)
        if len(raw) != expected:
            raise fail(f"{name}: old-Pictor data length is not exact")
        palette = None
    bits, planes = plane_info & 15, (plane_info >> 4) + 1
    packed_width = ((width * bits + 7) // 8) * 8 // bits
    packed_pixels = planar_pixels(raw, packed_width, height, bits, planes, name)
    if packed_width == width:
        pixels = packed_pixels
    else:
        pixels = b"".join(packed_pixels[row * packed_width:row * packed_width + width]
                          for row in range(height))
    if recommended_mode is not None and recommended_mode in b"012":
        if bits != 8 or planes != 1 or packed_width != width:
            raise fail(f"{name}: text-mode Pictor has a non-text plane layout")
        width, height, pixels = text_capture_pixels(name, pixels, width, height)
        xoff *= 8
        yoff *= 16
        palette = EGA16
        packed_width = None
        packed_pixels = None
    return Raster(width, height, xoff, yoff, pixels, palette,
                  packed_width if packed_width != width else None,
                  packed_pixels if packed_width != width else None,
                  recovery=recovery)


def pcx_rle(data: bytes, pos: int, expected: int, name: str) -> tuple[bytes, int]:
    out = bytearray()
    while len(out) < expected:
        if pos >= len(data):
            raise fail(f"{name}: truncated PCX RLE")
        value = data[pos]
        pos += 1
        count = 1
        if value >= 0xC0:
            count = value & 0x3F
            if not count or pos >= len(data):
                raise fail(f"{name}: invalid PCX run")
            value = data[pos]
            pos += 1
        if len(out) + count > expected:
            raise fail(f"{name}: PCX run crosses the image extent")
        out.extend(bytes((value,)) * count)
    return bytes(out), pos


def decode_pcx(name: str, data: bytes) -> Raster:
    if len(data) < 128 or data[0] != 10 or data[1] not in (2, 5) or data[2] != 1:
        raise fail(f"{name}: unsupported PCX manufacturer/version/encoding")
    bits = data[3]
    xmin, ymin, xmax, ymax = struct.unpack_from("<HHHH", data, 4)
    width, height = xmax - xmin + 1, ymax - ymin + 1
    planes, row_bytes = data[65], u16(data, 66)
    if width <= 0 or height <= 0 or bits not in (1, 8) or row_bytes < (width * bits + 7) // 8:
        raise fail(f"{name}: unsupported PCX geometry")
    raw, pos = pcx_rle(data, 128, row_bytes * planes * height, name)
    palette: tuple[tuple[int, int, int], ...] | None
    if bits == 8 and planes == 1:
        if pos + 769 != len(data) or data[pos] != 12:
            raise fail(f"{name}: 256-color PCX lacks its exact trailing palette")
        p = data[pos + 1:]
        palette = tuple(tuple(p[i:i + 3]) for i in range(0, 768, 3))
    elif bits == 1 and 1 <= planes <= 4:
        if pos != len(data):
            raise fail(f"{name}: bytes remain after planar PCX data")
        p = data[16:64]
        palette = tuple(tuple(p[i:i + 3]) for i in range(0, 48, 3))
    else:
        raise fail(f"{name}: only 8x1 and 1x1..4 PCX layouts are supported")
    pixels = bytearray(width * height)
    for y in range(height):
        row = y * row_bytes * planes
        if bits == 8:
            pixels[y * width:(y + 1) * width] = raw[row:row + width]
        else:
            for plane in range(planes):
                pbase = row + plane * row_bytes
                for x in range(width):
                    pixels[y * width + x] |= ((raw[pbase + x // 8] >> (7 - x % 8)) & 1) << plane
    horizontal_resolution, vertical_resolution = struct.unpack_from("<HH", data, 12)
    display_width = (horizontal_resolution
                     if horizontal_resolution >= width and vertical_resolution >= height else None)
    display_height = (vertical_resolution
                      if horizontal_resolution >= width and vertical_resolution >= height else None)
    return Raster(width, height, 0, 0, bytes(pixels), palette,
                  display_width=display_width, display_height=display_height)


def gif_subblocks(data: bytes, pos: int, name: str) -> tuple[bytes, int]:
    out = bytearray()
    while True:
        if pos >= len(data):
            raise fail(f"{name}: truncated GIF sub-block chain")
        size = data[pos]
        pos += 1
        if size == 0:
            return bytes(out), pos
        if pos + size > len(data):
            raise fail(f"{name}: GIF sub-block exceeds member")
        out.extend(data[pos:pos + size])
        pos += size


def gif_lzw(stream: bytes, minimum: int, wanted: int, name: str,
            background: int) -> bytes:
    if minimum < 2 or minimum > 8:
        raise fail(f"{name}: invalid GIF LZW minimum code size")
    bitpos, size = 0, minimum + 1
    clear, end = 1 << minimum, (1 << minimum) + 1
    table: list[bytes] = [bytes((i,)) for i in range(clear)] + [b"", b""]
    old: bytes | None = None
    out = bytearray()
    while True:
        if bitpos + size > len(stream) * 8:
            raise fail(f"{name}: truncated GIF LZW stream")
        code = 0
        for n in range(size):
            code |= ((stream[(bitpos + n) // 8] >> ((bitpos + n) % 8)) & 1) << n
        bitpos += size
        if code == clear:
            table = [bytes((i,)) for i in range(clear)] + [b"", b""]
            size, old = minimum + 1, None
            continue
        if code == end:
            break
        if code < len(table) and table[code]:
            entry = table[code]
        elif code == len(table) and old is not None:
            entry = old + old[:1]
        else:
            raise fail(f"{name}: invalid GIF LZW code")
        out.extend(entry)
        if old is not None and len(table) < 4096:
            table.append(old + entry[:1])
            if len(table) == (1 << size) and size < 12:
                size += 1
        old = entry
        if len(out) > wanted + 1:
            raise fail(f"{name}: GIF pixels exceed image extent")
    if len(out) == wanted + 1:
        # Early encoders paired with GRASP sometimes flush the LZW prefix
        # sentinel as one extra decoded pixel; the logical image descriptor
        # clips it exactly at the right/bottom extent.
        del out[wanted:]
    if len(out) == wanted - 1:
        # A widely distributed early GIF writer used with GRASP emitted the
        # end code one pixel early. The original logical-screen compositor
        # leaves that cell at the GIF background index.
        out.append(background)
    if len(out) != wanted:
        raise fail(f"{name}: GIF decoded {len(out)} pixels, expected {wanted}")
    # The terminating sub-block may contain pad bits, but no complete unread code.
    return bytes(out)


def decode_gif(name: str, data: bytes) -> Raster:
    if len(data) < 14 or data[:6] not in (b"GIF87a", b"GIF89a"):
        raise fail(f"{name}: invalid GIF signature")
    screen_w, screen_h, packed = u16(data, 6), u16(data, 8), data[10]
    pos = 13
    palette = None
    if packed & 0x80:
        count = 1 << ((packed & 7) + 1)
        if pos + count * 3 > len(data):
            raise fail(f"{name}: truncated GIF global palette")
        p = data[pos:pos + count * 3]
        palette = tuple(tuple(p[i:i + 3]) for i in range(0, len(p), 3))
        pos += len(p)
    image = None
    while pos < len(data):
        tag = data[pos]
        pos += 1
        if tag == 0x3B:
            if any(data[pos:]) or image is None:
                raise fail(f"{name}: invalid GIF trailer or missing image")
            return image
        if tag == 0x21:
            if pos >= len(data):
                raise fail(f"{name}: truncated GIF extension")
            pos += 1
            _, pos = gif_subblocks(data, pos, name)
            continue
        if tag != 0x2C or image is not None or pos + 9 > len(data):
            raise fail(f"{name}: unsupported GIF structure or multiple images")
        left, top, width, height = struct.unpack_from("<HHHH", data, pos)
        ipacked = data[pos + 8]
        pos += 9
        local_palette = palette
        if ipacked & 0x80:
            count = 1 << ((ipacked & 7) + 1)
            if pos + count * 3 > len(data):
                raise fail(f"{name}: truncated GIF local palette")
            p = data[pos:pos + count * 3]
            local_palette = tuple(tuple(p[i:i + 3]) for i in range(0, len(p), 3))
            pos += len(p)
        if local_palette is None or left + width > screen_w or top + height > screen_h:
            raise fail(f"{name}: invalid GIF image bounds or no palette")
        minimum = data[pos]
        pos += 1
        compressed, pos = gif_subblocks(data, pos, name)
        decoded = gif_lzw(compressed, minimum, width * height, name, data[11])
        if ipacked & 0x40:
            rows: list[bytes] = []
            source = 0
            arranged = [b""] * height
            for start, step in ((0, 8), (4, 8), (2, 4), (1, 2)):
                for y in range(start, height, step):
                    arranged[y] = decoded[source:source + width]
                    source += width
            decoded = b"".join(arranged)
        if left or top or width != screen_w or height != screen_h:
            canvas = bytearray(screen_w * screen_h)
            for y in range(height):
                at = (top + y) * screen_w + left
                canvas[at:at + width] = decoded[y * width:(y + 1) * width]
            decoded, width, height = bytes(canvas), screen_w, screen_h
        image = Raster(width, height, 0, 0, decoded, local_palette)
    raise fail(f"{name}: GIF has no trailer")


@dataclass(frozen=True)
class Font:
    first: int
    count: int
    width: int
    height: int
    row_bytes: int
    glyphs: tuple[bytes, ...]
    widths: tuple[int, ...]
    bearings: tuple[int, ...]
    space_gap: int = 0
    char_gap: int = 1
    line_gap: int = 0


def decode_font(name: str, data: bytes) -> Font:
    if len(data) >= 59 and data[0] in (0x10, 0x14):
        kind = data[0]
        check = 0xBA if kind == 0x10 else 0xDC
        if data[14] != check:
            raise fail(f"{name}: invalid extended SET check byte")
        count, first, proportional = data[16], data[17] + 0x20, data[18]
        width, height, row_bytes = data[19], data[20], data[21]
        if not count or proportional not in (0, 1) or u16(data, 25) != len(data):
            raise fail(f"{name}: invalid extended SET header or exact size")
        if kind == 0x14:
            raise fail(f"{name}: compressed extended SET fonts are not defined by this corpus")
        if count > 94:
            raise fail(f"{name}: extended SET character count exceeds its fixed tables")
        # Extended SET reserves directory slots for all 94 printable DOS
        # characters even when a smaller final character is declared.
        pos = 59
        offsets_bytes = 95 * 2
        if pos + offsets_bytes + (95 if proportional else 0) > len(data):
            raise fail(f"{name}: truncated extended SET tables")
        offsets = tuple(u16(data, pos + i * 2) for i in range(count + 1))
        pos += offsets_bytes
        if proportional:
            widths = tuple(data[pos:pos + count + 1])
            pos += 95
        else:
            widths = tuple(width for _ in range(count + 1))
        cell = row_bytes * height
        glyphs: list[bytes] = []
        for i in range(count):
            off = offsets[i + 1]
            if off != pos + i * cell or off + cell > len(data):
                raise fail(f"{name}: extended SET glyph offsets are not exact")
            glyphs.append(data[off:off + cell])
        if pos + count * cell != len(data):
            raise fail(f"{name}: extended SET glyphs do not account for every byte")
        return Font(first, count, width, height, row_bytes, tuple(glyphs),
                    tuple(widths[1:]), (0,) * count, data[22], data[23], data[24])
    if len(data) < 7 or u16(data, 0) != len(data):
        raise fail(f"{name}: invalid simple font size")
    count = data[2] or 256
    first, width, height, glyph_size = data[3:7]
    row_bytes = (width + 7) // 8
    if glyph_size != row_bytes * height or 7 + count * glyph_size != len(data):
        raise fail(f"{name}: simple font glyph geometry is not exact")
    glyphs = tuple(data[7 + i * glyph_size:7 + (i + 1) * glyph_size] for i in range(count))
    widths: list[int] = []
    bearings: list[int] = []
    for glyph in glyphs:
        occupied = [column for column in range(width)
                    if any(glyph[row * row_bytes + column // 8] & (0x80 >> (column & 7))
                           for row in range(height))]
        if occupied:
            bearings.append(occupied[0])
            widths.append(occupied[-1] - occupied[0] + 1)
        else:
            bearings.append(0)
            widths.append(width // 2)
    return Font(first, count, width, height, row_bytes, glyphs,
                tuple(widths), tuple(bearings))


@dataclass(frozen=True)
class DffFrame:
    width: int
    height: int
    xoff: int
    yoff: int
    commands: bytes


@dataclass(frozen=True)
class Dff:
    bits: int
    planes: int
    frames: tuple[DffFrame, ...]


@dataclass(frozen=True)
class Flic:
    frames: tuple[Raster, ...]
    delay: float


def decode_flic(name: str, data: bytes) -> Flic:
    """Decode the Autodesk Animator FLC subset accepted by GRASP 4/5."""
    if len(data) < 128 or u32(data, 0) != len(data) or u16(data, 4) not in (0xAF11, 0xAF12):
        raise fail(f"{name}: invalid FLI/FLC header")
    frame_count, width, height, depth = struct.unpack_from("<HHHH", data, 6)
    if not frame_count or not width or not height or depth != 8 or width > 4096 or height > 4096:
        raise fail(f"{name}: unsupported FLI/FLC geometry")
    speed = u32(data, 16) if u16(data, 4) == 0xAF12 else u16(data, 16) * 1000 // 70
    delay = max(1.0, speed / 10.0)
    pixels = bytearray(width * height)
    palette = list(VGA256)
    frames: list[Raster] = []

    def color_chunk(chunk: bytes, six_bit: bool) -> None:
        if len(chunk) < 2: raise fail(f"{name}: truncated FLI/FLC color chunk")
        packets, at, index = u16(chunk, 0), 2, 0
        for _ in range(packets):
            if at + 2 > len(chunk): raise fail(f"{name}: truncated FLI/FLC color packet")
            index += chunk[at]
            count = chunk[at + 1] or 256
            at += 2
            if index + count > 256 or at + count * 3 > len(chunk):
                raise fail(f"{name}: invalid FLI/FLC color packet")
            for color in range(count):
                values = tuple(chunk[at + color * 3 + channel] for channel in range(3))
                if six_bit:
                    if any(value > 63 for value in values):
                        raise fail(f"{name}: FLI palette component exceeds six bits")
                    values = tuple(value * 255 // 63 for value in values)
                palette[index + color] = values
            index += count
            at += count * 3
        if len(chunk) - at not in (0, 1):
            raise fail(f"{name}: bytes remain in FLI/FLC color chunk")

    def brun_chunk(chunk: bytes) -> None:
        at = 0
        for row in range(height):
            if at >= len(chunk): raise fail(f"{name}: truncated FLI/FLC BRUN line")
            # The stored packet-count byte is advisory and wraps on lines with
            # more than 255 packets. Width, not that byte, terminates the line.
            at, x = at + 1, 0
            while x < width:
                if at >= len(chunk): raise fail(f"{name}: truncated FLI/FLC BRUN packet")
                count = struct.unpack_from("<b", chunk, at)[0]
                at += 1
                if count < 0:
                    count = -count
                    if at + count > len(chunk) or x + count > width:
                        raise fail(f"{name}: invalid FLI/FLC BRUN literal")
                    pixels[row * width + x:row * width + x + count] = chunk[at:at + count]
                    at += count
                else:
                    if not count or at >= len(chunk) or x + count > width:
                        raise fail(f"{name}: invalid FLI/FLC BRUN run")
                    pixels[row * width + x:row * width + x + count] = bytes((chunk[at],)) * count
                    at += 1
                x += count
            if x != width: raise fail(f"{name}: FLI/FLC BRUN line does not cover its width")
        # Animator aligns chunks to words; the one alignment byte is not
        # initialized consistently by period encoders.
        if len(chunk) - at not in (0, 1):
            raise fail(f"{name}: bytes remain in FLI/FLC BRUN chunk")

    def ss2_chunk(chunk: bytes) -> None:
        if len(chunk) < 2: raise fail(f"{name}: truncated FLC SS2 chunk")
        lines, at, row = u16(chunk, 0), 2, 0
        completed = 0
        while completed < lines:
            if at + 2 > len(chunk): raise fail(f"{name}: truncated FLC SS2 line")
            word = u16(chunk, at); at += 2
            while word & 0xC000:
                control = word & 0xC000
                if control == 0xC000:
                    skip = -struct.unpack("<h", struct.pack("<H", word))[0]
                    row += skip
                elif control == 0x4000:
                    if row >= height: raise fail(f"{name}: FLC SS2 last-pixel row is invalid")
                    pixels[row * width + width - 1] = word & 0xff
                else:
                    raise fail(f"{name}: invalid FLC SS2 control word")
                if at + 2 > len(chunk): raise fail(f"{name}: truncated FLC SS2 control chain")
                word = u16(chunk, at); at += 2
            packets, x = word, 0
            if row >= height: raise fail(f"{name}: FLC SS2 row exceeds image")
            for _ in range(packets):
                if at + 2 > len(chunk): raise fail(f"{name}: truncated FLC SS2 packet")
                x += chunk[at]
                count = struct.unpack_from("<b", chunk, at + 1)[0]
                at += 2
                if count >= 0:
                    size = count * 2
                    if at + size > len(chunk) or x + size > width:
                        raise fail(f"{name}: invalid FLC SS2 literal")
                    pixels[row * width + x:row * width + x + size] = chunk[at:at + size]
                    at += size
                else:
                    pairs = -count
                    if at + 2 > len(chunk) or x + pairs * 2 > width:
                        raise fail(f"{name}: invalid FLC SS2 run")
                    pixels[row * width + x:row * width + x + pairs * 2] = chunk[at:at + 2] * pairs
                    at += 2
                    size = pairs * 2
                x += size
            row += 1
            completed += 1
        if len(chunk) - at not in (0, 1):
            raise fail(f"{name}: bytes remain in FLC SS2 chunk")

    def postage_chunk(chunk: bytes) -> None:
        # Animator stores a non-displayed miniature as one nested BRUN chunk.
        # Validate it even though GRASP playback never composites it.
        if len(chunk) < 12:
            raise fail(f"{name}: truncated FLI/FLC postage stamp")
        stamp_h, stamp_w, translation = struct.unpack_from("<HHH", chunk)
        nested_size, nested_type = struct.unpack_from("<IH", chunk, 6)
        if (not stamp_w or not stamp_h or translation != 1 or nested_type != 15
                or nested_size < 6 or 6 + nested_size != len(chunk)):
            raise fail(f"{name}: invalid FLI/FLC postage-stamp structure")
        body, at = chunk[12:], 0
        for _row in range(stamp_h):
            if at >= len(body):
                raise fail(f"{name}: truncated FLI/FLC postage-stamp line")
            at, x = at + 1, 0
            while x < stamp_w:
                if at >= len(body):
                    raise fail(f"{name}: truncated FLI/FLC postage-stamp packet")
                count = struct.unpack_from("<b", body, at)[0]
                at += 1
                if count < 0:
                    count = -count
                    if at + count > len(body) or x + count > stamp_w:
                        raise fail(f"{name}: invalid FLI/FLC postage-stamp literal")
                    at += count
                else:
                    if not count or at >= len(body) or x + count > stamp_w:
                        raise fail(f"{name}: invalid FLI/FLC postage-stamp run")
                    at += 1
                x += count
            if x != stamp_w:
                raise fail(f"{name}: FLI/FLC postage-stamp line does not fill its width")
        if len(body) - at not in (0, 1):
            raise fail(f"{name}: bytes remain in FLI/FLC postage-stamp chunk")

    pos = 128
    while pos < len(data):
        if pos + 6 > len(data): raise fail(f"{name}: truncated FLI/FLC record header")
        frame_size, frame_type = struct.unpack_from("<IH", data, pos)
        if frame_size < 6 or pos + frame_size > len(data):
            raise fail(f"{name}: invalid FLI/FLC frame extent")
        if frame_type == 0xF100:  # prefix metadata; its chunks do not alter the movie frame
            pos += frame_size
            continue
        if frame_type != 0xF1FA:
            raise fail(f"{name}: unsupported FLI/FLC frame type {frame_type:#x}")
        if frame_size < 16:
            raise fail(f"{name}: truncated FLI/FLC display-frame header")
        chunks, cursor = u16(data, pos + 6), pos + 16
        for _ in range(chunks):
            if cursor + 6 > pos + frame_size: raise fail(f"{name}: truncated FLI/FLC chunk")
            chunk_size, chunk_type = struct.unpack_from("<IH", data, cursor)
            if chunk_size < 6 or cursor + chunk_size > pos + frame_size:
                raise fail(f"{name}: invalid FLI/FLC chunk extent")
            body = data[cursor + 6:cursor + chunk_size]
            if chunk_type == 4: color_chunk(body, False)
            elif chunk_type == 7: ss2_chunk(body)
            elif chunk_type == 11: color_chunk(body, True)
            elif chunk_type == 13: pixels[:] = bytes(len(pixels))
            elif chunk_type == 15: brun_chunk(body)
            elif chunk_type == 16:
                if len(body) != len(pixels): raise fail(f"{name}: FLI/FLC COPY size is invalid")
                pixels[:] = body
            elif chunk_type == 18: postage_chunk(body)
            else:
                raise fail(f"{name}: unsupported FLI/FLC chunk type {chunk_type}")
            cursor += chunk_size
        if cursor != pos + frame_size:
            raise fail(f"{name}: FLI/FLC chunks do not fill their frame")
        if len(frames) < frame_count:
            frames.append(Raster(width, height, 0, 0, bytes(pixels), tuple(palette)))
        pos += frame_size
    if pos != len(data) or len(frames) != frame_count:
        raise fail(f"{name}: FLI/FLC frame count or extent is not exact")
    return Flic(tuple(frames), delay)


def validate_dff_commands(name: str, index: int, data: bytes, wanted: int,
                          row_bytes: int, planes: int) -> None:
    if wanted == 0:
        # GDFF emits skip-only zero-area frames as intentional holds.
        pos = 0
        while pos < len(data):
            op = data[pos]
            pos += 1
            if op & 0xc0:
                raise fail(f"{name}: zero-area DFF frame {index} contains drawing data")
            count = op & 0x3f
            if not count:
                count, pos = u16(data, pos), pos + 2
            if not count:
                raise fail(f"{name}: zero skip in DFF frame {index}")
        return
    pos = virtual = 0
    while pos < len(data):
        op = data[pos]
        pos += 1
        if op & 0x80:
            count = op & 0x7F
            if count == 0:
                count, pos = u16(data, pos), pos + 2
            if not count or pos + count > len(data):
                raise fail(f"{name}: invalid literal in DFF frame {index}")
            pos += count
        elif op & 0x40:
            count = op & 0x3F
            if count == 0:
                count, pos = u16(data, pos), pos + 2
            if not count or pos >= len(data):
                raise fail(f"{name}: invalid fill in DFF frame {index}")
            pos += 1
        else:
            count = op & 0x3F
            if count == 0:
                count, pos = u16(data, pos), pos + 2
            if not count:
                raise fail(f"{name}: zero skip in DFF frame {index}")
        virtual += count
    # Some period encoders emitted the tail of the next plane scan line in a
    # frame command stream. DOS GRASP clipped those writes at the allocated
    # bitmap boundary. Limit recovery to two complete planar scan lines so a
    # corrupt length/count cannot silently consume arbitrary data.
    tolerated_tail = row_bytes * planes * 2
    if virtual > wanted + tolerated_tail:
        raise fail(f"{name}: DFF frame {index} substantially overruns its virtual bitmap")
    if virtual < wanted:
        raise fail(f"{name}: DFF frame {index} does not cover its virtual bitmap")


def decode_dff(name: str, data: bytes) -> Dff:
    if len(data) < 4:
        raise fail(f"{name}: truncated DFF header")
    count, bits, additional = u16(data, 0), data[2], data[3]
    planes = additional + 1
    data_start = 4 + count * 16
    if not count or bits not in (1, 2, 4, 8) or data_start > len(data):
        raise fail(f"{name}: invalid DFF header")
    frames: list[DffFrame] = []
    expected_offset = 0
    for i in range(count):
        at = 4 + i * 16
        offset, length, width, height, xoff, yoff = struct.unpack_from("<IIHHhh", data, at)
        if offset != expected_offset or data_start + offset + length > len(data):
            raise fail(f"{name}: DFF frame directory is not contiguous and exact")
        commands = data[data_start + offset:data_start + offset + length]
        row_bytes = (width * bits + 7) // 8
        wanted = row_bytes * height * planes
        validate_dff_commands(name, i, commands, wanted, row_bytes, planes)
        frames.append(DffFrame(width, height, xoff, yoff, commands))
        expected_offset += length
    if data_start + expected_offset != len(data):
        raise fail(f"{name}: DFF frames do not account for every byte")
    return Dff(bits, planes, tuple(frames))


@dataclass
class Assets:
    members: dict[str, Member]
    rasters: dict[str, Raster]
    fonts: dict[str, Font]
    dffs: dict[str, Dff | Flic]
    programs: list[tuple[str, bytes]]
    errors: dict[str, str]


def load_assets(library: Library) -> Assets:
    members = library.by_name()
    rasters: dict[str, Raster] = {}
    fonts: dict[str, Font] = {}
    dffs: dict[str, Dff | Flic] = {}
    programs: list[tuple[str, bytes]] = []
    errors: dict[str, str] = {}
    for member in library.members:
        ext = Path(member.name).suffix.casefold()
        key = member.name.casefold()
        try:
            if ext in (".pic", ".clp"):
                rasters[key] = decode_pictor(member.name, member.payload)
            elif ext in (".pcx", ".pcc"):
                if member.payload.startswith(b"\x34\x12"):
                    rasters[key] = decode_pictor(member.name, member.payload)
                else:
                    rasters[key] = decode_pcx(member.name, member.payload)
            elif ext == ".gif":
                # Several contemporary image tools retained a .GIF DOS name
                # after converting the member to Pictor. Both formats have an
                # unambiguous on-disk signature and GRASP dispatches by it.
                if member.payload.startswith(b"\x34\x12"):
                    rasters[key] = decode_pictor(member.name, member.payload)
                else:
                    rasters[key] = decode_gif(member.name, member.payload)
            elif ext == ".pal":
                if not member.payload.startswith(b"\x34\x12"):
                    raise fail(f"{member.name}: PAL member lacks its Pictor signature")
                rasters[key] = decode_pictor(member.name, member.payload)
            elif ext in (".fnt", ".set"):
                fonts[key] = decode_font(member.name, member.payload)
            elif ext == ".dff":
                dffs[key] = decode_dff(member.name, member.payload)
            elif ext in (".flc", ".fli"):
                dffs[key] = decode_flic(member.name, member.payload)
            elif ext == ".txt":
                if not member.payload or b"\0" in member.payload:
                    raise fail(f"{member.name}: empty or NUL-containing program")
                programs.append((member.name, member.payload))
            elif ext == ".bat":
                if not member.payload or b"\0" in member.payload:
                    raise fail(f"{member.name}: invalid BAT member")
            elif ext == ".com":
                if not member.payload or len(member.payload) > 0xFF00:
                    raise fail(f"{member.name}: invalid DOS COM member")
        except (GraspError, UnicodeDecodeError) as exc:
            # A GL directory is an archive. A damaged, unused member does not
            # prevent DOS GRASP from executing a different valid path, so keep
            # the member name for exact lookup and quarantine only its decoder.
            errors[key] = str(exc)
    return Assets(members, rasters, fonts, dffs, programs, errors)


@dataclass(frozen=True)
class Instruction:
    op: str
    args: tuple[str, ...]
    line: int
    raw: str


@dataclass(frozen=True)
class Program:
    name: str
    code: tuple[Instruction, ...]
    labels: dict[str, int]
    data_blocks: dict[str, tuple[str, ...]]


_UNSET = object()


@dataclass
class CallFrame:
    return_pc: int
    saved_arguments: dict[str, object]
    saved_locals: dict[str, object]


def source_without_comment(line: str) -> str:
    quoted = False
    for i, char in enumerate(line):
        if char == '"':
            quoted = not quoted
        elif char == ";" and not quoted:
            return line[:i]
    return line


class SourceToken(str):
    """A DOS source token retaining whether any portion was quoted."""
    quoted: bool

    def __new__(cls, value: str, quoted: bool = False):
        token = super().__new__(cls, value)
        token.quoted = quoted
        return token


def source_tokens(text: str) -> tuple[str, ...]:
    tokens: list[str] = []
    token: list[str] = []
    quoted = False
    token_quoted = False
    token_unquoted = False
    parentheses = 0
    empty_quoted = False
    quote_start = 0
    quote_is_comparison_rhs = False
    for char in text:
        if char == '"':
            if not quoted and token and re.fullmatch(r"[-+]?\d+\.?", "".join(token)):
                # The DOS numeric reader terminates when a quoted string
                # begins, even if an old command file omitted the comma.
                tokens.append(SourceToken("".join(token)))
                token = []
                token_unquoted = False
            if not quoted:
                empty_quoted = True
                quote_start = len(token)
                quote_is_comparison_rhs = bool(
                    re.search(r"(?:==|<>|!=|<=|>=|=)$", "".join(token)))
                quoted = True
                token_quoted = True
            else:
                if quote_is_comparison_rhs and not empty_quoted:
                    literal = "".join(token[quote_start:])
                    del token[quote_start:]
                    token.extend(repr(literal))
                quoted = False
                if empty_quoted:
                    if token:
                        # Retain an empty string that is part of an expression,
                        # such as @answer=="", after removing source quotes.
                        token.extend("''")
                    else:
                        tokens.append(SourceToken("", True))
                        token_quoted = False
                empty_quoted = False
            continue
        if not quoted and char == "(":
            parentheses += 1
        elif not quoted and char == ")" and parentheses:
            parentheses -= 1
        if not quoted and not parentheses and (char.isspace() or char == ","):
            if token:
                tokens.append(SourceToken("".join(token), token_quoted and not token_unquoted))
                token = []
                token_quoted = False
                token_unquoted = False
        else:
            token.append(char)
            if quoted:
                empty_quoted = False
            else:
                token_unquoted = True
    # The DOS parser closes a quoted token at the physical end of line. This
    # permits old command files whose final quote was omitted.
    if token:
        tokens.append(SourceToken("".join(token), token_quoted and not token_unquoted))
    return tuple(tokens)


def interrupt_source_tokens(text: str) -> tuple[str, ...]:
    """Tokenize INT while retaining register slots omitted with commas."""
    match = re.match(r"(?i)^int\b", text)
    if match is None:
        return source_tokens(text)
    body = text[match.end():].strip()
    segments: list[str] = []
    start = depth = 0
    quoted = False
    for index, character in enumerate(body):
        if character == '"':
            quoted = not quoted
        elif not quoted and character == "(":
            depth += 1
        elif not quoted and character == ")" and depth:
            depth -= 1
        elif not quoted and not depth and character == ",":
            segments.append(body[start:index])
            start = index + 1
    segments.append(body[start:])
    if len(segments) == 1:
        return (SourceToken("int"),) + source_tokens(body)
    arguments: list[str] = []
    for index, segment in enumerate(segments):
        fields = source_tokens(segment.strip())
        if index == 0:
            arguments.extend(fields)
        elif fields:
            arguments.extend(fields)
        else:
            arguments.append(SourceToken(""))
    return (SourceToken("int"), *arguments)


def parse_program(name: str, payload: bytes) -> Program:
    # DOS text readers treat the first SUB byte as end-of-file; fixed-size GL
    # member sectors may contain further SUB or NUL fill after that point.
    payload = payload.split(b"\x1a", 1)[0]
    text = payload.decode("cp437")
    physical_lines = text.splitlines()
    # GRASP 4 text strings may span physical lines. Preserve the starting line
    # number while folding a continuation into the same command record. Many
    # hand-authored files also omit a final quote; the DOS line reader closes
    # those at end-of-line. A following command therefore terminates folding.
    for index in range(len(physical_lines)):
        if physical_lines[index].count('"') % 2 == 0:
            continue
        end = index + 1
        while end < len(physical_lines):
            continuation = source_without_comment(physical_lines[end]).lstrip()
            head = re.match(r"([A-Za-z_][A-Za-z0-9_.@-]*)", continuation)
            if '"' not in continuation and (
                    re.fullmatch(r"[A-Za-z0-9_.@-]+\s*:\s*", continuation) or
                    (head and head.group(1).casefold() in SUPPORTED_COMMANDS)):
                break
            physical_lines[index] += "\n" + physical_lines[end]
            physical_lines[end] = ""
            if physical_lines[index].count('"') % 2 == 0:
                break
            end += 1
    data_blocks: dict[str, tuple[str, ...]] = {}
    inline_blocks: dict[int, str] = {}
    skipped_lines: set[int] = set()
    selected_blocks: set[str] = set()
    for physical in physical_lines:
        tokens = source_tokens(source_without_comment(physical).strip())
        if len(tokens) >= 2 and tokens[0].casefold() == "databegin":
            selected_blocks.add(tokens[1].casefold())
    # A named data definition is identified by an actual DATABEGIN reference,
    # so its elements may be filenames or words as well as numbers.
    for index, physical in enumerate(physical_lines):
        header = source_without_comment(physical).strip()
        match = re.match(r"^([A-Za-z_][A-Za-z0-9_.@-]*)\s*:", header)
        if not match or match.group(1).casefold() not in selected_blocks:
            continue
        values: list[str] = []
        end = index + 1
        while end < len(physical_lines):
            body = source_without_comment(physical_lines[end]).strip()
            if body.casefold() == "dataend":
                break
            values.extend(source_tokens(body))
            end += 1
        # A selected named block may legally extend to DOS EOF; DATAEND is
        # required only when command text follows it.
        data_blocks[match.group(1).casefold()] = tuple(values)
        skipped_lines.update(range(index, min(end + 1, len(physical_lines))))
    # Labeled data blocks omit DATABEGIN at their definition site. They are
    # distinguished from code labels by a numeric data line and DATAEND.
    for index, physical in enumerate(physical_lines):
        if index in skipped_lines:
            continue
        header = source_without_comment(physical).strip()
        match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_.@-]*)\s*:", header)
        if not match:
            continue
        cursor = index + 1
        while cursor < len(physical_lines) and not source_without_comment(physical_lines[cursor]).strip():
            cursor += 1
        if cursor >= len(physical_lines):
            continue
        first_tokens = source_tokens(source_without_comment(physical_lines[cursor]).strip())
        if not first_tokens or not re.fullmatch(r"[-+]?(?:0x[0-9a-fA-F]+|\d+)", first_tokens[0]):
            continue
        values: list[str] = []
        end = cursor
        while end < len(physical_lines):
            body = source_without_comment(physical_lines[end]).strip()
            if body.casefold() == "dataend":
                break
            values.extend(source_tokens(body))
            end += 1
        if end < len(physical_lines):
            data_blocks[match.group(1).casefold()] = tuple(values)
            skipped_lines.update(range(index, end + 1))

    # An anonymous DATABEGIN defines and selects the values that follow it.
    # Give it an internal label so execution uses the same data cursor as a
    # named block without leaving numeric data lines in the command stream.
    for index, physical in enumerate(physical_lines):
        if index in skipped_lines:
            continue
        header = source_tokens(source_without_comment(physical).strip())
        if not header or header[0].casefold() != "databegin" or len(header) != 1:
            continue
        values: list[str] = []
        end = index + 1
        while end < len(physical_lines):
            body = source_without_comment(physical_lines[end]).strip()
            if body.casefold() == "dataend":
                break
            values.extend(source_tokens(body))
            end += 1
        if end >= len(physical_lines):
            raise fail(f"{name}:{index + 1}: DATABEGIN lacks DATAEND")
        label = f"__inline_data_{index + 1}"
        data_blocks[label] = tuple(values)
        inline_blocks[index] = label
        skipped_lines.update(range(index + 1, end + 1))

    code: list[Instruction] = []
    labels: dict[str, int] = {}
    for number, physical in enumerate(physical_lines, 1):
        if number - 1 in skipped_lines:
            continue
        line = source_without_comment(physical).strip()
        while line:
            match = re.match(r"^([A-Za-z0-9_.@-]+)\s*:(?:\s*|$)", line)
            if not match:
                break
            label = match.group(1).casefold()
            if label in labels:
                raise fail(f"{name}:{number}: duplicate label {label!r}")
            labels[label] = len(code)
            line = line[match.end():].strip()
        if not line:
            continue
        try:
            tokens = (interrupt_source_tokens(line)
                      if re.match(r"(?i)^int\b", line) else source_tokens(line))
        except GraspError as exc:
            raise fail(f"{name}:{number}: {exc}") from exc
        if tokens:
            args = tokens[1:]
            if tokens[0].casefold() == "databegin" and number - 1 in inline_blocks:
                args = (inline_blocks[number - 1],)
            code.append(Instruction(tokens[0].casefold(), args, number, physical))
    if not code and not data_blocks:
        raise fail(f"{name}: empty program")
    return Program(name, tuple(code), labels, data_blocks)


SUPPORTED_COMMANDS = {
    "@sound", "box", "break", "call", "cfade", "cfree", "cgetbuf", "chgcolor", "clearscr", "cload", "databegin", "digpak",
    "circle", "closegl", "color", "cycle", "data", "dataskip", "dfree", "dload", "edge", "else", "endfloat", "endif", "exit", "fade", "ffree",
    "fgaps", "float", "fly", "fload", "font", "fstyle", "global", "gosub", "goto", "if",
    "flood", "flushkey", "free", "getcolor", "getkey", "getmouse", "ifkey", "ifmem", "ifmouse", "ifvideo", "line", "link", "load", "loop", "mark", "mode", "mouse", "move", "noise", "note", "offset", "opengl",
    "palette", "pan", "pfade", "pfree", "pgetbuf", "pload", "psave", "putdff", "putup", "rect",
    "pnewbuf", "point", "position", "psetbuf", "resetscr", "return", "revpage", "set", "setcolor", "setpage", "setrgb", "spread", "text", "tile", "timer", "when",
    "cursor", "local", "merge", "resetgl", "setupscr", "tran", "video", "wait", "waitkey", "window",
    "exec", "int",
}


def validate_program(program: Program) -> None:
    # Syntax that is reached is checked by execute(). Delaying these checks is
    # important for old presentations with an invalid command or dead branch
    # intended for a different video adapter.
    return None


class ExpressionEvaluator(ast.NodeVisitor):
    def __init__(self, variables: dict[str, int | float | str], functions=None):
        self.variables = variables
        self.functions = functions or {}


    def evaluate(self, expression: str) -> int | float | str | bool:
        source_expression = expression
        if re.fullmatch(r"0[0-9]+", expression):
            # The language is untyped: a zero-padded atom remains a string so
            # it can form names such as shot06.pcx, while IVALUE still accepts
            # it as decimal six in a numeric command position.
            return expression
        expression = re.sub(r"(?i)peekl\s*\([^)]*\)", "305419896", expression)
        expression = re.sub(r"(?i)\bdef\s*\(", "defined(", expression)
        expression = expression.replace("$", "+")
        expression = re.sub(
            r"@(\d+|[A-Za-z_][A-Za-z0-9_.]*)",
            lambda m: f"V_{m.group(1).casefold().replace('.', '__dot__')}", expression)
        expression = expression.replace("<>", "!=")
        expression = expression.replace("||", " or ").replace("&&", " and ")
        expression = re.sub(r"!(?!=)", " not ", expression)
        if not any(x in expression for x in ("==", "!=", "<=", ">=")):
            expression = re.sub(r"(?<![<>=!])=(?!=)", "==", expression)
        expression = expression.strip()
        try:
            node = ast.parse(expression, mode="eval")
        except SyntaxError as exc:
            # The DOS tokenizer removes balanced quotes while preserving their
            # contents. A quoted field consisting of spaces or punctuation is
            # therefore a literal even though it is not valid Python syntax.
            if not re.search(r"[@()=!<>+*/%&|^~]", source_expression):
                return source_expression
            raise fail(f"invalid expression {expression!r}") from exc
        return self.visit(node.body)


    def visit_Constant(self, node: ast.Constant):
        if type(node.value) not in (int, float, str):
            raise fail("expression contains an invalid constant")
        return node.value


    def visit_Name(self, node: ast.Name):
        if node.id.startswith("V_"):
            return self.variables.get(node.id[2:].casefold().replace("__dot__", "."), 0)
        if node.id.casefold() in self.variables:
            # Very early scripts occasionally omit @ on the right side of an
            # assignment. A currently defined name is unambiguously a variable;
            # otherwise a bare word remains the documented string literal.
            return self.variables[node.id.casefold()]
        # Source tokenization removes quotes, as the DOS command reader did.
        # A bare non-variable name in an expression is consequently a string
        # literal (for example @answer==H or @object==brick).
        return node.id


    def visit_Attribute(self, node: ast.Attribute):
        parts = [node.attr]
        value = node.value
        while isinstance(value, ast.Attribute):
            parts.append(value.attr)
            value = value.value
        if not isinstance(value, ast.Name):
            raise fail("unsupported expression attribute")
        parts.append(value.id)
        return ".".join(reversed(parts))


    def visit_BoolOp(self, node: ast.BoolOp):
        values = [bool(self.visit(value)) for value in node.values]
        if isinstance(node.op, ast.And): return all(values)
        if isinstance(node.op, ast.Or): return any(values)
        raise fail("unsupported boolean expression operator")


    def visit_UnaryOp(self, node: ast.UnaryOp):
        value = self.visit(node.operand)
        if isinstance(node.op, ast.USub): return -value
        if isinstance(node.op, ast.UAdd): return +value
        if isinstance(node.op, ast.Invert): return ~int(value)
        if isinstance(node.op, ast.Not): return not value
        raise fail("unsupported unary expression operator")


    def visit_BinOp(self, node: ast.BinOp):
        left, right = self.visit(node.left), self.visit(node.right)
        operations = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b,
                      ast.Mult: lambda a, b: a * b, ast.Div: lambda a, b: a / b,
                      ast.FloorDiv: lambda a, b: a // b, ast.Mod: lambda a, b: a % b,
                      ast.LShift: lambda a, b: int(a) << int(b),
                      ast.RShift: lambda a, b: int(a) >> int(b),
                      ast.BitAnd: lambda a, b: int(a) & int(b),
                      ast.BitOr: lambda a, b: int(a) | int(b),
                      ast.BitXor: lambda a, b: int(a) ^ int(b)}
        for cls, operation in operations.items():
            if isinstance(node.op, cls):
                return operation(left, right)
        raise fail("unsupported binary expression operator")


    def visit_Compare(self, node: ast.Compare):
        if len(node.ops) != 1:
            raise fail("chained comparisons are unsupported")
        left, right = self.visit(node.left), self.visit(node.comparators[0])
        op = node.ops[0]
        if isinstance(op, ast.Eq): return left == right
        if isinstance(op, ast.NotEq): return left != right
        if isinstance(op, ast.Lt): return left < right
        if isinstance(op, ast.LtE): return left <= right
        if isinstance(op, ast.Gt): return left > right
        if isinstance(op, ast.GtE): return left >= right
        raise fail("unsupported comparison")


    def visit_Call(self, node: ast.Call):
        if not isinstance(node.func, ast.Name) or node.keywords:
            raise fail("unsupported expression function syntax")
        name = node.func.id.casefold()
        if name not in self.functions:
            raise fail(f"unsupported expression function {name!r}")
        return self.functions[name](*(self.visit(argument) for argument in node.args))


    def generic_visit(self, node):
        raise fail(f"unsupported expression syntax {type(node).__name__}")


DEFAULT_FONT_B85 = (
    "c-rk(&59dG5FQ-p(;z#y1_|qu2bk0DkPN#Qze4WA5*i<xL??L;!{F0CLLm4J{1oFAG&u}9h5;$UC*@+of<fMcm`PRtO;_*6PvDZY"
    "JD;k$yZ)<{B;V*8g~W@Z;G8G$MiN5&Kn0{6r2c4WUaPydX6#ngc13chQl6FS)}UO<e7*0wZmnUKWhL1TWHs^BV0h5PGcO{Fu@Iq("
    "ym4m*-vtYj<_Wv}if0V<Yu_4FE44kGj!M;5F0Z(z#_^4~8a!qNW6a5?i$Zn-DE!jkp>5l9z|Tv-O8NZ<SZ{3h=c_v4<8uS+(~4*w"
    "7;LdKSE~nJW1;nd12hk1{QhYWUwz);aM-u@{1>@YYCweyK0^l7@DXQ&3vmY)ws)d1_(2Ly^1<3CZeCZf%NsEeT$cC2`h!y9M}zSs"
    "eVje7;Fj$EFLgFR{#bt;;i#&DLyrdEmzw-}n}5b}w?VS|A5X(!JMFK19r#<@S5Ep_{$GbWoq0amc=Y@-Pnlmo?*1V9s%Za>AyM!E"
    "?{=dQ4g-r9!s%;dr~SswEe7wyX0-mvELnc?w*9!u7c=(E@>5HNi{}59`iSMoAAet^wXfIYV_8-@#I@(w3KGECw}6vmH_2=MF!6Kw"
    "OL-so7if**U7hNX!v1nCCjUZS=Al0sOJ+=y&?yJ<CIPH`9_0(B$hbrDcyBT^&@YIO=ht3Er=Kh7{aO(HYs>(*{zaCZF&q~Q&)3TX"
    "e~|baj0rGdU_t_TZ1SgJsVk`t`>D<E8JN04duP7!as9{ck35v&D{IXD>;2x;Gn8}6v_&1&ANz0^Pe>@5A05pX=r#oBGN<x*B7_i*"
    "a|ufGMbZ4h{Rm$qBtO7$1fzV2)zr|OIw8ikIEWHr@A?POuRqP3e*eaRD@g7E{jp6ZeS`c_G@p#V6V9rR_!IdgKU5I!3Smw9he~Ka"
    "fw{DScx~JS^yPItPsudG%krUp)i>fd$nVc4edb(`PoREf9T3I`<4ybv{Lmi6M1RPypuPb4hHHW?<yAP1@H&vxLH@xU%y7I0^{8iP"
    "8^{b;{^k)<Rbe@7-?4N#VX^)F%7~b1z)Or@ej$5#5o`xY_U7^XSM>Gsd;0qO4Sn&a=^;WMUl=;s|4xg6;8^~|ynIa79h84!K6mXm"
    "LvSt9`b0(l5b3`p@|=(Hq=@C+!!$|g`bc^i`Qwu4f0<pA)2=hh|B{T+-1-u&za;({CwaTx%UkQl$Y1gPV{Bg(hHGN)a`K<1<s<)G"
    "N9#wb50CvD$II_GM&$H!bRW_4i0CpmkN17w?`=I-P}+S5<=eUYDo*>bAo2Q-<e-9{Hq9rzfA&Z#e|@*pwe`ml-!#y|VYIvZwrkJO"
    "COlMl+`sld2-n#w+;N)s4GjCK#eByAe{S4yi>$=<US^9Vx&V56+?)Qqa89z<XWzu^b=%?Dd_I5N5JLN5vnIU1W0Uk#S@*-Q{8({c"
    "xQFNZZud#bVqtq(5DFaseOCTS)2BA{<n;d!@k~}!"
)


# The proportional 8x8 NORMAL face distributed with GRASP is its resident
# graphics-mode font.  Keeping it embedded makes the converter self-contained.
GRAPHICS_FONT_B85 = (
    "c-l=;J&PML5Pc{j*}}yTT(~en1QD*>aygbo42xMz2uC<lm@5twjub9Zx>&^FpWq*LKkJe=TIJ)d*kPoZH#1Lq_vSG)O@oS!0UN{^iy"
    "vd=7a{#!w>}GS{NBi?9olJX_v0-Z2_?=qBGPySAsP4NzMH#y#*54%f5}_^GyWBWV`50p=yi8EY7c3}K;Ny}l+A7(_x)-ev-ikpcI"
    "IzGnw2(dsmwUFWp;4BTgbVpZLJD>qd)V5^=Xw$9f4r`asTae_<&8+tg0ZnEuN>8$V*4f&ncY~`&w+W^DkDHhb2!Iz#GO6I!-"
    "^QQIQHV^yzT0I6Z#d?`ZqNTlnXNPt|la-}1=c+q|!pS8F_fF>*B8!{Ld18rizyav3{|%g%3t=@$$=o^5*X(3i%j^Ua9=@N3b=(7Qng_B)q4^x0Mq$KC2{P6Jl&?Ovt$RGdK%$"
    "1*?a{8$7?X`JqUjA(2B!0AfRo=0NIue_!}<#WKp(ewZY3NSCvsN`#nHwEl|FPH1}WWEVd_IJ0A0ht11zLW46!uHR-"
    "Nay`q&-byuspCp_dU<)pZ@&L}#s"
)


def default_font() -> Font:
    import base64
    import zlib
    raw = zlib.decompress(base64.b85decode(GRAPHICS_FONT_B85.encode("ascii")))
    return decode_font("resident NORMAL font", raw)


def text_mode_font() -> Font:
    import base64
    import zlib
    raw = zlib.decompress(base64.b85decode(DEFAULT_FONT_B85.encode("ascii")))
    if len(raw) != 4096:
        raise RuntimeError("internal font corruption")
    glyphs = tuple(raw[i * 16:(i + 1) * 16] for i in range(256))
    return Font(0, 256, 8, 16, 1, glyphs, (8,) * 256, (0,) * 256,
                0, 0, 0)


MODE_INFO = {
    "a": (320, 200, 4), "b": (320, 200, 16), "c": (640, 200, 2),
    "d": (640, 200, 16), "e": (640, 350, 2), "f": (640, 350, 4),
    "g": (640, 350, 16), "h": (720, 348, 2), "i": (320, 200, 16),
    "j": (320, 200, 16), "k": (640, 400, 2), "l": (320, 200, 256),
    "m": (640, 480, 16), "n": (720, 348, 16), "o": (640, 480, 2),
    "r": (640, 400, 256), "s": (640, 480, 256),
    "t": (800, 600, 256), "u": (1024, 768, 2), "v": (1024, 768, 16),
    "w": (360, 480, 256), "x": (1024, 768, 256),
    "y": (1280, 1024, 16), "z": (1280, 1024, 256),
}


class Renderer:
    def __init__(self):
        self.width, self.height, self.colors = 640, 350, 16
        self.view_width, self.view_height = self.width, self.height
        self.viewport_x = self.viewport_y = 0
        self.screen = bytearray(self.width * self.height)
        self.palette = list(EGA16) + [(0, 0, 0)] * 240
        self.fg, self.bg = 15, 0
        self.window = (0, 0, self.width - 1, self.height - 1)  # GRASP coordinates
        self.transparent: set[int] = set()
        self.center = False
        self.right = False
        self.font = default_font()
        self.font_style = 0
        self.font_offset_x = self.font_offset_y = 1
        self.edge_color: int | None = None
        self.char_gap, self.space_gap, self.line_gap = 1, 0, 0
        self.pages: dict[int, bytearray] = {}
        self.view_screen: bytearray | None = None


    def set_video(self, mode: str) -> None:
        key = mode.casefold()
        if key in ("0", "1", "2"):
            raise fail(f"text video mode {mode!r} cannot be rendered as a GL animation")
        if key not in MODE_INFO:
            raise fail(f"unsupported GRASP video mode {mode!r}")
        width, height, colors = MODE_INFO[key]
        self.width, self.height, self.colors = width, height, colors
        self.view_width, self.view_height = width, height
        self.viewport_x = self.viewport_y = 0
        self.screen = bytearray(width * height)
        self.view_screen = None
        self.pages.clear()
        self.window = (0, 0, width - 1, height - 1)
        if colors == 256:
            self.palette = list(VGA256)
        elif colors == 4:
            self.palette = list(CGA4) + [(0, 0, 0)] * 252
        else:
            self.palette = list(EGA16) + [(0, 0, 0)] * 240
        self.fg, self.bg = min(15, colors - 1), 0
        self.font = default_font()
        self.char_gap, self.space_gap, self.line_gap = (
            self.font.char_gap, self.font.space_gap, self.font.line_gap)
        self.font_style = 0
        self.center = self.right = False


    def set_text_video(self, columns: int, rows: int) -> None:
        width, height = columns * 8, rows * 16
        if width > 1280 or height > 1600:
            raise fail("text video geometry exceeds the supported framebuffer")
        self.width, self.height, self.colors = width, height, 16
        self.view_width, self.view_height = width, height
        self.viewport_x = self.viewport_y = 0
        self.screen = bytearray(width * height)
        self.view_screen = None
        self.pages.clear()
        self.window = (0, 0, width - 1, height - 1)
        self.palette = list(EGA16) + [(0, 0, 0)] * 240
        self.fg, self.bg = 7, 0
        self.font = text_mode_font()
        self.char_gap = self.space_gap = self.line_gap = 0
        self.font_style = 0
        self.center = self.right = False


    def bounds_top(self) -> tuple[int, int, int, int]:
        x1, y1, x2, y2 = self.window
        return max(0, x1), max(0, self.height - 1 - y2), min(self.width - 1, x2), min(self.height - 1, self.height - 1 - y1)


    def point(self, x: int, y: int, color: int | None = None) -> None:
        ty = self.height - 1 - y
        wx1, wy1, wx2, wy2 = self.bounds_top()
        if wx1 <= x <= wx2 and wy1 <= ty <= wy2:
            self.screen[ty * self.width + x] = (self.fg if color is None else color) & 255


    def rect(self, x1: int, y1: int, x2: int, y2: int, color: int | None = None) -> None:
        x1, x2 = sorted((x1, x2)); y1, y2 = sorted((y1, y2))
        tx1, tx2 = max(x1, 0), min(x2, self.width - 1)
        top, bottom = max(0, self.height - 1 - y2), min(self.height - 1, self.height - 1 - y1)
        wx1, wy1, wx2, wy2 = self.bounds_top()
        tx1, tx2, top, bottom = max(tx1, wx1), min(tx2, wx2), max(top, wy1), min(bottom, wy2)
        if tx1 > tx2 or top > bottom: return
        fill = bytes(((self.fg if color is None else color) & 255,)) * (tx2 - tx1 + 1)
        for y in range(top, bottom + 1):
            self.screen[y * self.width + tx1:y * self.width + tx2 + 1] = fill


    def line(self, x1: int, y1: int, x2: int, y2: int) -> None:
        dx, sx = abs(x2 - x1), 1 if x1 < x2 else -1
        dy, sy = -abs(y2 - y1), 1 if y1 < y2 else -1
        error = dx + dy
        while True:
            self.point(x1, y1)
            if x1 == x2 and y1 == y2: break
            twice = error * 2
            if twice >= dy: error += dy; x1 += sx
            if twice <= dx: error += dx; y1 += sy


    def circle(self, cx: int, cy: int, rx: int, ry: int) -> None:
        """Draw the integer midpoint ellipse used by GRASP primitives."""
        rx, ry = abs(rx), abs(ry)
        if rx == 0 and ry == 0:
            self.point(cx, cy)
            return
        if rx == 0:
            self.line(cx, cy - ry, cx, cy + ry)
            return
        if ry == 0:
            self.line(cx - rx, cy, cx + rx, cy)
            return
        x, y = 0, ry
        rx2, ry2 = rx * rx, ry * ry
        dx, dy = 0, 2 * rx2 * y
        decision = ry2 - rx2 * ry + rx2 // 4
        while dx < dy:
            for px, py in ((cx + x, cy + y), (cx - x, cy + y),
                           (cx + x, cy - y), (cx - x, cy - y)):
                self.point(px, py)
            x += 1
            dx += 2 * ry2
            if decision < 0:
                decision += ry2 + dx
            else:
                y -= 1
                dy -= 2 * rx2
                decision += ry2 + dx - dy
        decision = (ry2 * (2 * x + 1) * (2 * x + 1)
                    + 4 * rx2 * (y - 1) * (y - 1) - 4 * rx2 * ry2)
        while y >= 0:
            for px, py in ((cx + x, cy + y), (cx - x, cy + y),
                           (cx + x, cy - y), (cx - x, cy - y)):
                self.point(px, py)
            y -= 1
            if decision > 0:
                decision += 4 * rx2 - 8 * rx2 * y
            else:
                x += 1
                decision += 8 * ry2 * x + 4 * rx2 - 8 * rx2 * y


    def box(self, x1: int, y1: int, x2: int, y2: int, thickness: int = 1) -> None:
        for n in range(max(1, thickness)):
            self.line(x1 + n, y1 + n, x2 - n, y1 + n)
            self.line(x2 - n, y1 + n, x2 - n, y2 - n)
            self.line(x2 - n, y2 - n, x1 + n, y2 - n)
            self.line(x1 + n, y2 - n, x1 + n, y1 + n)


    def install_palette(self, palette: tuple[tuple[int, int, int], ...] | None) -> None:
        if palette is None:
            return
        for i, value in enumerate(palette[:256]):
            self.palette[i] = tuple(value)


    def paste(self, image: Raster, x: int, y: int, restore: bytearray | None = None,
              honor_transparency: bool = True, use_offsets: bool = True) -> None:
        left = x + (image.xoff if use_offsets else 0)
        bottom = y + (image.yoff if use_offsets else 0)
        top = self.height - bottom - image.height
        wx1, wy1, wx2, wy2 = self.bounds_top()
        for sy in range(image.height):
            dy = top + sy
            if dy < wy1 or dy > wy2: continue
            sx1, sx2 = max(0, wx1 - left), min(image.width, wx2 - left + 1)
            if sx1 >= sx2: continue
            dest = dy * self.width + left + sx1
            source = sy * image.width + sx1
            if not honor_transparency or not self.transparent:
                self.screen[dest:dest + sx2 - sx1] = image.pixels[source:source + sx2 - sx1]
                continue
            for n in range(sx2 - sx1):
                value = image.pixels[source + n]
                if value not in self.transparent:
                    self.screen[dest + n] = value


    def extract_planar(self, width: int, height: int, x: int, y: int,
                       bits: int, planes: int) -> bytearray:
        """Encode a screen rectangle in DFF/Pictor plane and row order."""
        row_bytes = (width * bits + 7) // 8
        raw = bytearray(row_bytes * height * planes)
        mask = (1 << bits) - 1
        for plane in range(planes):
            plane_base = plane * row_bytes * height
            shift = plane * bits
            for stored_y in range(height):
                screen_y = y + stored_y
                if screen_y < 0 or screen_y >= self.height:
                    continue
                top_y = self.height - 1 - screen_y
                row_base = plane_base + stored_y * row_bytes
                for px in range(width):
                    screen_x = x + px
                    if 0 <= screen_x < self.width:
                        value = (self.screen[top_y * self.width + screen_x] >> shift) & mask
                        bit = px * bits
                        raw[row_base + (bit >> 3)] |= value << (8 - bits - (bit & 7))
        return raw


    def tiled(self, image: Raster) -> None:
        wx1, wy1, wx2, wy2 = self.bounds_top()
        first_x = wx1 - ((wx1 - image.xoff) % image.width)
        first_y = wy1 - ((wy1 - image.yoff) % image.height)
        for top in range(first_y, wy2 + 1, image.height):
            y = self.height - top - image.height
            for x in range(first_x, wx2 + 1, image.width):
                self.paste(image, x, y)


    def text_width(self, text: str) -> int:
        width = 0
        for byte in text.encode("cp437", errors="replace"):
            index = byte - self.font.first
            glyph_width = self.font.widths[index] if 0 <= index < self.font.count else self.font.width
            if byte == 32 and self.space_gap:
                glyph_width = self.space_gap
            width += glyph_width + self.char_gap
        return max(0, width - self.char_gap)


    def draw_text(self, x: int, y: int, text: str) -> None:
        if self.center:
            wx1, _, wx2, _ = self.window
            x = wx1 + (wx2 - wx1 + 1 - self.text_width(text)) // 2
        elif self.right:
            _, _, wx2, _ = self.window
            x = wx2 - self.text_width(text) + 1
        encoded = text.encode("cp437", errors="replace")
        def pass_glyphs(dx: int, dy: int, color: int) -> None:
            cursor = x
            for byte in encoded:
                index = byte - self.font.first
                if 0 <= index < self.font.count:
                    glyph = self.font.glyphs[index]
                    glyph_width = self.font.widths[index]
                    bearing = self.font.bearings[index]
                    for row in range(self.font.height):
                        for col in range(glyph_width):
                            source_col = bearing + col
                            if glyph[row * self.font.row_bytes + source_col // 8] & (0x80 >> (source_col & 7)):
                                self.point(cursor + col + dx,
                                           y + self.font.height - 1 - row + dy, color)
                else:
                    glyph_width = self.font.width
                if byte == 32 and self.space_gap:
                    glyph_width = self.space_gap
                cursor += glyph_width + self.char_gap
        ox, oy = self.font_offset_x, self.font_offset_y
        # Later GRASP styles run counter-clockwise from right. Odd styles are
        # cardinal directions and even styles are diagonals; style 8 is the
        # documented lower-right drop shadow.
        offsets = {1: (ox, 0), 2: (ox, oy), 3: (0, oy), 4: (-ox, oy),
                   5: (-ox, 0), 6: (-ox, -oy), 7: (0, -oy), 8: (ox, -oy)}
        if self.font_style in offsets:
            dx, dy = offsets[self.font_style]
            pass_glyphs(dx, dy, self.bg)
        pass_glyphs(0, 0, self.fg)


    def draw_text_mode(self, column: int, row: int, text: str) -> None:
        """Draw opaque fixed cells using DOS text coordinates and attributes."""
        x, y = column * 8, self.height - (row + 1) * 16
        encoded = text.encode("cp437", errors="replace")
        if encoded:
            self.rect(x, y, x + len(encoded) * 8 - 1, y + 15, self.bg)
        self.draw_text(x, y, text)


    def canvas_indices(self) -> bytes:
        visible = self.view_screen if self.view_screen is not None else self.screen
        width, height = self.view_width, self.view_height
        if self.width != width or self.height != height or self.viewport_x or self.viewport_y:
            if self.viewport_x < 0 or self.viewport_y < 0 \
                    or self.viewport_x + width > self.width or self.viewport_y + height > self.height:
                raise fail("hardware viewport is outside the virtual screen")
            cropped = bytearray(width * height)
            for row in range(height):
                source = (self.viewport_y + row) * self.width + self.viewport_x
                cropped[row * width:(row + 1) * width] = self.screen[source:source + width]
            visible = cropped
        if width == 320 and height == 200:
            out = bytearray(OUT_WIDTH * OUT_HEIGHT)
            for y in range(200):
                row = visible[y * 320:(y + 1) * 320]
                doubled = bytearray(640)
                doubled[0::2] = row; doubled[1::2] = row
                at = (40 + y * 2) * 640
                out[at:at + 640] = doubled
                out[at + 640:at + 1280] = doubled
            return bytes(out)
        if width == 640 and height <= 480:
            out = bytearray(OUT_WIDTH * OUT_HEIGHT)
            top = (OUT_HEIGHT - height) // 2
            out[top * 640:(top + height) * 640] = visible
            return bytes(out)
        if width > OUT_WIDTH or height > OUT_HEIGHT:
            # Extended 132-column/43-line and 80-column/60-line adapters use
            # framebuffers larger than the fixed movie canvas. Preserve the
            # complete screen with one deterministic nearest-neighbor fit.
            scale = min(OUT_WIDTH / width, OUT_HEIGHT / height)
            fitted_width = max(1, int(width * scale))
            fitted_height = max(1, int(height * scale))
            left = (OUT_WIDTH - fitted_width) // 2
            top = (OUT_HEIGHT - fitted_height) // 2
            out = bytearray(OUT_WIDTH * OUT_HEIGHT)
            xmap = tuple(x * width // fitted_width for x in range(fitted_width))
            for y in range(fitted_height):
                source = (y * height // fitted_height) * width
                destination = (top + y) * OUT_WIDTH + left
                out[destination:destination + fitted_width] = bytes(
                    visible[source + x] for x in xmap)
            return bytes(out)
        raise fail(f"cannot map {width}x{height} to the fixed output canvas")


    def rgb(self) -> bytes:
        indices = self.canvas_indices()
        red = indices.translate(bytes(c[0] for c in self.palette))
        green = indices.translate(bytes(c[1] for c in self.palette))
        blue = indices.translate(bytes(c[2] for c in self.palette))
        rgb = bytearray(len(indices) * 3)
        rgb[0::3], rgb[1::3], rgb[2::3] = red, green, blue
        return bytes(rgb)


class MovieWriter:
    def __init__(self, output: Path, renderer: Renderer):
        ffmpeg = shutil.which("ffmpeg")
        if not ffmpeg:
            raise fail("ffmpeg is required to encode the AVI container")
        parent = output.resolve().parent
        if not parent.is_dir():
            raise fail(f"output directory does not exist: {parent}")
        self.output = output
        self.renderer = renderer
        self.ffmpeg = ffmpeg
        self.frames = 0
        self.audible = False
        self.phase = 0.0
        self.temp_context = tempfile.TemporaryDirectory(prefix="grasp-native-")
        self.temp = Path(self.temp_context.name)
        self.video = self.temp / "video.mkv"
        self.audio = self.temp / "audio.s16"
        self.atomic = parent / f".{output.name}.grasp-{os.getpid()}.tmp.avi"
        self.audio_stream = self.audio.open("wb")
        command = [ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
                   "-f", "rawvideo", "-pix_fmt", "rgb24",
                   "-video_size", f"{OUT_WIDTH}x{OUT_HEIGHT}", "-framerate", str(FPS),
                   "-i", "pipe:0", "-an", "-c:v", "ffv1", "-level", "3",
                   "-pix_fmt", "bgr0", str(self.video)]
        self.process = subprocess.Popen(command, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)


    def frame(self, start_frequency: float = 0.0, end_frequency: float | None = None,
              pcm: array | None = None) -> None:
        if self.frames >= MAX_FRAMES:
            raise fail("presentation exceeds the one-hour deterministic video limit")
        assert self.process.stdin is not None
        try:
            self.process.stdin.write(self.renderer.rgb())
        except BrokenPipeError as exc:
            detail = self.process.stderr.read().decode("utf-8", errors="replace")
            raise fail(f"ffmpeg stopped accepting native frames: {detail[-500:]}") from exc
        samples = SAMPLE_RATE // FPS
        if pcm is not None:
            self.audible = True
            if len(pcm) < samples:
                pcm.extend((0,) * (samples - len(pcm)))
            elif len(pcm) > samples:
                del pcm[samples:]
            if sys.byteorder != "little":
                pcm.byteswap()
            self.audio_stream.write(pcm.tobytes())
        elif start_frequency > 0:
            self.audible = True
            end = start_frequency if end_frequency is None else max(1.0, end_frequency)
            pcm = array("h")
            for i in range(samples):
                frequency = start_frequency + (end - start_frequency) * i / max(1, samples - 1)
                self.phase += 2 * math.pi * frequency / SAMPLE_RATE
                pcm.append(6500 if math.sin(self.phase) >= 0 else -6500)
            if sys.byteorder != "little": pcm.byteswap()
            self.audio_stream.write(pcm.tobytes())
        else:
            self.audio_stream.write(bytes(samples * 2))
        self.frames += 1


    def play_u8(self, data: bytes, rate: int) -> None:
        """Play headerless unsigned 8-bit PCM while holding the current frame."""
        if not data or rate < 1000 or rate > 192000:
            raise fail("digital PCM has an invalid byte count or sample rate")
        output_samples = max(1, math.ceil(len(data) * SAMPLE_RATE / rate))
        per_frame = SAMPLE_RATE // FPS
        for base in range(0, output_samples, per_frame):
            count = min(per_frame, output_samples - base)
            pcm = array("h", (((data[min(len(data) - 1,
                                        (base + i) * rate // SAMPLE_RATE)] - 128) << 8)
                              for i in range(count)))
            self.frame(pcm=pcm)


    def delay(self, hundredths: float, start_frequency: float = 0.0,
              end_frequency: float | None = None) -> None:
        count = max(1, int(round(max(0.0, hundredths) * FPS / 100)))
        for i in range(count):
            if end_frequency is None:
                f1 = f2 = start_frequency
            else:
                f1 = start_frequency + (end_frequency - start_frequency) * i / count
                f2 = start_frequency + (end_frequency - start_frequency) * (i + 1) / count
            self.frame(f1, f2)


    def finish(self) -> None:
        if self.frames == 0:
            self.frame()
        assert self.process.stdin is not None
        self.process.stdin.close()
        stderr = self.process.stderr.read()
        returncode = self.process.wait()
        self.audio_stream.close()
        if returncode or not self.video.is_file() or not self.video.stat().st_size:
            raise fail(f"ffmpeg failed encoding frames: {stderr.decode(errors='replace')[-800:]}")
        duration = self.frames / FPS
        command = [self.ffmpeg, "-hide_banner", "-loglevel", "error", "-y",
                   "-i", str(self.video)]
        if self.audible:
            command += ["-f", "s16le", "-ar", str(SAMPLE_RATE), "-ac", "1",
                        "-i", str(self.audio), "-map", "0:v:0", "-map", "1:a:0",
                        "-c:v", "copy", "-c:a", "pcm_s16le"]
        else:
            command += ["-map", "0:v:0", "-c:v", "copy", "-an"]
        command += ["-t", f"{duration:.6f}", "-f", "avi", str(self.atomic)]
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode or not self.atomic.is_file() or not self.atomic.stat().st_size:
            if self.atomic.exists(): self.atomic.unlink()
            raise fail(f"ffmpeg failed muxing AVI: {result.stderr.decode(errors='replace')[-800:]}")
        os.chmod(self.atomic, 0o664)
        os.replace(self.atomic, self.output)
        self.temp_context.cleanup()


    def abort(self) -> None:
        """Discard an incomplete encode without leaving output or subprocesses."""
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        if self.process.stdin is not None and not self.process.stdin.closed:
            self.process.stdin.close()
        if not self.audio_stream.closed:
            self.audio_stream.close()
        if self.atomic.exists():
            self.atomic.unlink()
        self.temp_context.cleanup()
def resource_key(assets: Assets, requested: str, extensions: tuple[str, ...]) -> str:
    name = requested.casefold()
    if Path(name).suffix:
        if name not in assets.members:
            raise fail(f"resource {requested!r} is not present")
        return name
    # This is the runtime's documented default-extension search order, not
    # content guessing. In particular FLOAD prefers SET over legacy FNT.
    for extension in extensions:
        candidate = name + extension
        if candidate in assets.members:
            return candidate
    raise fail(f"resource {requested!r} is not present with a permitted extension")


def integer_range(args: tuple[str, ...], evaluate) -> list[int]:
    def number(text: str) -> int:
        value = evaluate(text)
        if isinstance(value, str):
            match = re.fullmatch(r"[pcd](\d+)", value, re.IGNORECASE)
            if match:
                return int(match.group(1))
        return int(value)
    normalized: list[str] = []
    for token in args:
        match = re.fullmatch(r"(.+)-", token)
        if match:
            normalized.extend((match.group(1), "-"))
        else:
            normalized.append(token)
    args = tuple(normalized)
    values: list[int] = []
    i = 0
    while i < len(args):
        if args[i] == "-":
            if not values or i + 1 >= len(args):
                raise fail("misplaced range hyphen")
            end = number(args[i + 1])
            start = values[-1]
            values.extend(range(start + (1 if end >= start else -1), end + (1 if end >= start else -1),
                                1 if end >= start else -1))
            i += 2
        else:
            values.append(number(args[i]))
            i += 1
    return values


class Interpreter:
    def __init__(self, assets: Assets, programs: tuple[Program, ...],
                 program: Program, writer: MovieWriter):
        self.assets, self.programs, self.program, self.writer = assets, programs, program, writer
        self.r = writer.renderer
        self.variables: dict[str, int | float | str] = {}
        self.random = random.Random(0x47524153)
        self.expr = ExpressionEvaluator(self.variables, {
            "abs": abs,
            "asc": lambda value: (str(value).encode("cp437", errors="replace") or b"\0")[0],
            "chr": lambda value: bytes((int(value) & 255,)).decode("cp437"),
            "cos": math.cos,
            "dec": lambda value, width=0: str(int(str(value), 0)).zfill(int(width)),
            "def": lambda name: int(str(name).casefold() in self.variables),
            "defined": lambda name: int(str(name).casefold() in self.variables),
            "eval": lambda value: self.expr.evaluate(str(value)),
            "exp": math.exp,
            "hex": lambda value, width=8: "0x" + format(int(value) & 0xffffffff,
                                                        f"0{int(width)}X"),
            "left": lambda value, count: str(value)[:max(0, int(count))],
            "len": lambda value: len(str(value)),
            "log": math.log,
            "lower": lambda value: str(value).lower(),
            "mid": lambda value, start, count=None: str(value)[max(0, int(start) - 1):
                    max(0, int(start) - 1) + (len(str(value)) if count is None else max(0, int(count)))],
            "pad": lambda value, width: str(value).rjust(max(0, int(width))),
            "random": lambda *bounds: self.random.randint(
                0 if len(bounds) == 1 else int(bounds[0]), int(bounds[-1])),
            "right": lambda value, count: str(value)[-max(0, int(count)):] if int(count) else "",
            "sin": math.sin,
            "sqrt": math.sqrt,
            "tan": math.tan,
            "upper": lambda value: str(value).upper(),
            "width": lambda value: self.r.text_width(str(value)),
        })
        self.clips: dict[int, Raster] = {}
        self.freed_clips: dict[int, Raster] = {}
        self.clip_unshifted_only: set[int] = set()
        self.pages: dict[int, Raster] = {}
        self.freed_pages: dict[int, Raster] = {}
        self.page_positions: dict[int, tuple[int, int]] = {}
        self.recovery_notes: list[str] = []
        self.fonts: dict[int, Font] = {0: self.r.font}
        self.font_names: dict[str, int] = {"normal": 0}
        self.symbolic_numbers: dict[str, int] = {}
        self.loaded_members: dict[str, Member] = {}
        self.current_digital_sound: Member | None = None
        self.dffs: dict[int, Dff | Flic] = {}
        self.loops: list[list[int]] = []
        self.calls: list[CallFrame] = []
        self.pc = 0
        self.steps = 0
        self.text_mode: tuple[int, int] | None = None
        self.text_x = 0
        self.text_y = 0
        self.pset_context: tuple | None = None
        self.float_background: bytes | None = None
        self.data_values: tuple[str, ...] = ()
        self.data_index = 0
        self.data_overread = 0
        self.pending_key: str | int | float | None = None
        self.pending_mouse: str | None = None
        self.mouse_x = self.mouse_y = 0
        self.interaction_visits: dict[tuple[str, int], int] = {}
        self.synthetic_actions = 0
        self.color_loop_states: dict[tuple[str, int], tuple[int, tuple[tuple[str, str], ...]]] = {}
        self.allow_navigation_return = False
        self.stop_after_navigation = False
        self.module_stack: list[tuple[Program, int, list[CallFrame], list[list[int]],
                                      tuple[str, ...], int, int, str | int | float | None,
                                      dict[str, object]]] = []
        self.module_local_scopes: list[dict[str, object]] = []
        self.merged_programs: dict[str, list[Program]] = {}
        self.program_aliases: dict[str, Program] = {}
        for candidate in programs:
            name = candidate.name.casefold()
            self.program_aliases[name] = candidate
            self.program_aliases.setdefault(Path(name).stem, candidate)
        self.linked_program_visits = {program.name.casefold()}
        self.open_gl: str | None = None
        self.offset_x = self.offset_y = 0
        self.timer_frame: int | None = None
        self.silent_chime_notes: set[tuple[str, int]] = set()
        # The educational templates use an adjacent, evenly descending NOTE
        # run as a standard success/startup ditty. It is presentation chrome,
        # not animation sound, and is intentionally rendered as equal silence.
        for candidate in programs:
            index = 0
            while index < len(candidate.code):
                end = index
                notes: list[tuple[int, int, int]] = []
                while end < len(candidate.code) and candidate.code[end].op == "note":
                    args = candidate.code[end].args
                    if len(args) < 3 or not all(re.fullmatch(r"[-+]?\d+", value)
                                                  for value in args[:3]):
                        break
                    notes.append(tuple(int(value) for value in args[:3]))
                    end += 1
                if len(notes) >= 3:
                    pitches = [note[0] for note in notes]
                    step = pitches[1] - pitches[0]
                    if step < 0 and all(pitches[n] - pitches[n - 1] == step
                                        for n in range(2, len(pitches))) \
                            and len({note[1:] for note in notes}) == 1:
                        self.silent_chime_notes.update(
                            (candidate.name.casefold(), pc) for pc in range(index, end))
                index = max(index + 1, end)


    def value(self, text: str) -> int | float | str | bool:
        if text == "@":
            wildcard = self.data_wildcard()
            if isinstance(wildcard, SourceToken) and wildcard.quoted:
                return str(wildcard)
            return self.expr.evaluate(wildcard)
        if "$" in text and any(operator in text for operator in
                                ("==", "<>", "!=", "<=", ">=", "&&", "||")):
            return self.expr.evaluate(text)
        if "$" in text:
            return self.string(text)
        if isinstance(text, SourceToken) and text.quoted:
            return str(text)
        indirect = re.fullmatch(r"@\((.+)\)", text)
        if indirect:
            name = self.string(indirect.group(1)).casefold()
            return self.variables.get(name, 0)
        return self.expr.evaluate(text)


    def ivalue(self, text: str) -> int:
        value = self.value(text)
        if isinstance(value, str):
            if value == "":
                return 0
            known = self.symbolic_numbers.get(value.casefold())
            if known is not None:
                return known
            # Bounded source recovery for the unmistakable capital-O-for-zero
            # transcription error, accepted only in an integer argument.
            if value.casefold() == "o":
                return 0
            if value == "I":
                return 1
            if re.fullmatch(r"[-+]?\d+:", value):
                return int(value[:-1])
            match = re.fullmatch(r"[pcd](\d+)", value, re.IGNORECASE)
            if match:
                return int(match.group(1))
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.-]*", value):
                key = value.casefold()
                if key in self.variables and not isinstance(self.variables[key], str):
                    return int(self.variables[key])
                if key not in self.symbolic_numbers:
                    self.symbolic_numbers[key] = 256 + len(self.symbolic_numbers)
                return self.symbolic_numbers[key]
        return int(value)


    def named_register(self, requested: str) -> int:
        key = requested.casefold()
        if key not in self.symbolic_numbers:
            self.symbolic_numbers[key] = 256 + len(self.symbolic_numbers)
        register = self.symbolic_numbers[key]
        stem = Path(key).stem
        if stem and not re.fullmatch(r"\d+", stem):
            self.symbolic_numbers.setdefault(stem, register)
        return register


    def resource_name(self, text: str) -> str:
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*\(.*\)", text):
            return self.display_value(self.value(text))
        return self.string(text)


    def play_digital_member(self, member: Member) -> None:
        extension = Path(member.name).suffix.casefold()
        if extension == ".raw":
            pcm, rate = member.payload, 11000
        elif extension == ".snd":
            if len(member.payload) < 16:
                raise fail(f"{member.name}: truncated GRASP SND header")
            size, rate = struct.unpack_from("<II", member.payload)
            if (size != len(member.payload) - 16 or rate < 1000 or rate > 192000
                    or member.payload[8] != 0xff or any(member.payload[9:16])):
                raise fail(f"{member.name}: invalid GRASP SND header")
            pcm = member.payload[16:]
        else:
            raise fail(f"{member.name}: digital playback requires RAW or SND PCM")
        if hasattr(self.writer, "play_u8"):
            self.writer.play_u8(pcm, rate)
        else:
            self.writer.delay(len(pcm) * 100 / rate)


    def xy(self, x: str, y: str) -> tuple[int, int]:
        return self.ivalue(x) + self.offset_x, self.ivalue(y) + self.offset_y


    @staticmethod
    def display_value(value: int | float | str | bool) -> str:
        if isinstance(value, float) and value.is_integer():
            return str(int(value))
        if isinstance(value, bool):
            return "1" if value else "0"
        return str(value)


    def string(self, text: str) -> str:
        if text == "@":
            return self.data_wildcard()
        if "$" in text:
            parts: list[str] = []
            start = depth = 0
            for index, character in enumerate(text):
                if character == "(":
                    depth += 1
                elif character == ")" and depth:
                    depth -= 1
                elif character == "$" and depth == 0:
                    parts.append(text[start:index])
                    start = index + 1
            parts.append(text[start:])
            result: list[str] = []
            for part in parts:
                indirect = re.fullmatch(r"@\((.*)\)", part)
                if part == "@":
                    result.append(self.display_value(self.value("@")))
                elif indirect:
                    name = self.string(indirect.group(1)).casefold()
                    result.append(self.display_value(self.variables.get(name, 0)))
                elif re.fullmatch(r"@(\d+|[A-Za-z_][A-Za-z0-9_.]*)", part) \
                        or (part.startswith("(") and part.endswith(")")):
                    result.append(self.display_value(self.value(part)))
                else:
                    result.append(re.sub(
                        r"@(\d+|[A-Za-z_][A-Za-z0-9_.]*)",
                        lambda m: self.display_value(
                            self.variables.get(m.group(1).casefold(), 0)), part))
            return "".join(result)
        indirect = re.fullmatch(r"@\((.*)\)", text)
        if indirect:
            return self.display_value(
                self.variables.get(self.string(indirect.group(1)).casefold(), 0))
        if re.fullmatch(r"@(\d+|[A-Za-z_][A-Za-z0-9_.]*)", text):
            return self.display_value(self.variables.get(text[1:].casefold(), 0))
        return re.sub(r"@(\d+|[A-Za-z_][A-Za-z0-9_.]*)",
                      lambda m: self.display_value(
                          self.variables.get(m.group(1).casefold(), 0)), text)


    def variable_name(self, text: str) -> str:
        if "$" in text or text.startswith("@("):
            return self.string(text).lstrip("@").casefold()
        return text.lstrip("@").casefold()


    def data_wildcard(self) -> str:
        if self.data_index < len(self.data_values):
            value = self.data_values[self.data_index]
            self.data_index += 1
            return value
        # A few hand-entered tables omit exactly their final member although
        # the MARK count is correct. Extend only a numeric arithmetic sequence
        # by one element; all other overreads remain fatal.
        if self.data_overread == 0 and len(self.data_values) >= 3 \
                and all(re.fullmatch(r"[-+]?\d+", value)
                        for value in self.data_values[-3:]):
            numbers = [int(value) for value in self.data_values[-3:]]
            if numbers[2] - numbers[1] == numbers[1] - numbers[0]:
                self.data_overread = 1
                value = str(numbers[2] + numbers[2] - numbers[1])
                note = f"completed one missing final DATA value as {value} from its exact arithmetic sequence"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
                return value
        raise fail("data wildcard read past DATAEND")


    def choose_key(self, site: int) -> str:
        self.synthetic_actions += 1
        if self.synthetic_actions >= 24:
            self.stop_after_navigation = True
        choices: list[tuple[str, str]] = []
        look = site
        while look < len(self.program.code) and self.program.code[look].op in ("ifkey", "ifmouse"):
            probe = self.program.code[look]
            if probe.op == "ifkey":
                choices.extend(zip(probe.args[0::2], probe.args[1::2]))
            look += 1
        usable = [(key, label) for key, label in choices
                  if key.casefold() not in ("f1", "esc", "escape")
                  and label.casefold() not in ("help", "exit", "quit", "menu")]
        if not any(key.casefold() in ("enter", "return") for key, _ in usable):
            usable = [(key, label) for key, label in usable
                      if key.casefold() not in ("up", "down", "left", "right")]
        if not usable:
            return "ENTER"
        # A sole key whose target is at or before the input site is a replay
        # request (for example F9 at an end card), not progress through an
        # interactive presentation. Let the normal no-key/timeout path end the
        # finite movie instead of replaying it until the safety ceiling.
        forward = [(key, label) for key, label in usable
                   if self.program.labels.get(label.casefold(), site + 1) > site]
        if not forward and all(label.casefold() in self.program.labels
                               for _, label in usable):
            self.stop_after_navigation = True
            return "ENTER"
        if forward:
            usable = forward
        key_names = {key.casefold(): key for key, _ in usable}
        identity = (self.program.name.casefold(), site)
        visit = self.interaction_visits.get(identity, 0)
        self.interaction_visits[identity] = visit + 1
        # For a directional menu, exercise the current row, confirm it, and
        # move to the next row only if the program returns to the selector.
        # The command stream itself therefore decides which confirmation leads
        # to content; no row count or label name is assumed.
        if "enter" in key_names and ("down" in key_names or "up" in key_names):
            horizontal = "right" if "right" in key_names else "left" if "left" in key_names else None
            vertical = "down" if "down" in key_names else "up"
            cycle = ([horizontal] if horizontal else []) + ["enter", vertical]
            if visit >= 24:
                self.stop_after_navigation = True
                return key_names["enter"]
            return key_names[cycle[visit % len(cycle)]]
        if len(usable) > 1:
            # A letter/number menu gets one complete logical selection. The
            # backward return to that selector then closes the finite movie.
            self.stop_after_navigation = True
        return usable[0][0]


    def choose_mouse_target(self, site: int) -> str:
        """Choose successive actionable regions from one IFMOUSE dispatch table."""
        self.synthetic_actions += 1
        if self.synthetic_actions >= 24:
            self.stop_after_navigation = True
        targets: list[str] = []
        look = site
        while look < len(self.program.code) and self.program.code[look].op == "ifmouse":
            args = self.program.code[look].args
            if len(args) >= 2 and args[1].casefold() not in ("help", "exit", "quit", "menu"):
                targets.append(args[1])
            look += 1
        if not targets:
            return ""
        identity = (self.program.name.casefold(), site)
        visit = self.interaction_visits.get(identity, 0)
        self.interaction_visits[identity] = visit + 1
        if visit >= len(targets):
            self.stop_after_navigation = True
        return targets[min(visit, len(targets) - 1)]


    def choose_typed_value(self, variable: str, site: int) -> int | float | str:
        marker = "@" + variable.casefold()
        end = min(len(self.program.code), site + 48)
        printable: str | None = None
        for probe in self.program.code[site:end]:
            if probe.op in ("getkey", "waitkey") and probe is not self.program.code[site]:
                break
            if probe.op != "if" or not probe.args:
                continue
            expression = probe.args[0]
            match = re.fullmatch(re.escape(marker) + r"==(.+)", expression, re.IGNORECASE)
            if not match:
                continue
            answer = match.group(1)
            if "||" in answer or "&&" in answer or marker in answer.casefold() \
                    or re.fullmatch(r"[HhQqMm]", answer):
                continue
            try:
                value = self.value(answer)
            except GraspError:
                continue
            if type(value) in (int, float):
                return value
            if isinstance(value, str):
                if value in ("\r", "\n"):
                    return value
                if len(value) == 1 and ord(value) >= 32 and value != "\x1b":
                    printable = printable or value
        if printable is not None:
            return printable
        # ENTER is the least destructive generic response when the command
        # stream does not expose a checkable expected value.
        return "ENTER"


    def push_call(self, return_pc: int, name: str, arguments: tuple[str, ...]) -> None:
        values = [self.value(argument) for argument in arguments]
        keys = {key for key in self.variables if key.isdigit()}
        keys.update(str(index) for index in range(10))
        saved = {key: self.variables.get(key, _UNSET) for key in keys}
        self.calls.append(CallFrame(return_pc, saved, {}))
        for key in keys:
            self.variables.pop(key, None)
        self.variables["0"] = name
        for index in range(1, 10):
            self.variables[str(index)] = ""
        for index, value in enumerate(values, 1):
            self.variables[str(index)] = value


    def pop_call(self, return_value: int | float | str | bool = 0) -> None:
        frame = self.calls.pop()
        for name, old in reversed(tuple(frame.saved_locals.items())):
            if old is _UNSET:
                self.variables.pop(name, None)
            else:
                self.variables[name] = old  # type: ignore[assignment]
        for name, old in frame.saved_arguments.items():
            if old is _UNSET:
                self.variables.pop(name, None)
            else:
                self.variables[name] = old  # type: ignore[assignment]
        self.variables["0"] = return_value
        self.pc = frame.return_pc


    def enter_module(self, program: Program, start: int = 0,
                     arguments: tuple[str, ...] = (), subroutine: str | None = None) -> None:
        validate_program(program)
        values = [self.value(argument) for argument in arguments]
        keys = {key for key in self.variables if key.isdigit()}
        keys.update(str(index) for index in range(10))
        saved_arguments = {key: self.variables.get(key, _UNSET) for key in keys}
        self.module_stack.append((self.program, self.pc, self.calls, self.loops,
                                  self.data_values, self.data_index, self.data_overread,
                                  self.pending_key,
                                  saved_arguments))
        self.module_local_scopes.append({})
        self.program, self.pc = program, start
        self.calls, self.loops = [], []
        self.data_values, self.data_index = (), 0
        self.data_overread = 0
        self.pending_key = None
        for key in keys:
            self.variables.pop(key, None)
        self.variables["0"] = subroutine or Path(program.name).stem
        for index in range(1, 10):
            self.variables[str(index)] = ""
        for index, value in enumerate(values, 1):
            self.variables[str(index)] = value
        self.allow_navigation_return = False


    def link_module(self, program: Program, start: int = 0,
                    arguments: tuple[str, ...] = (), subroutine: str | None = None) -> None:
        """Replace the current command file; documented LINK never returns."""
        validate_program(program)
        values = [self.value(argument) for argument in arguments]
        self.program, self.pc = program, start
        self.calls, self.loops = [], []
        self.module_stack.clear()
        self.module_local_scopes.clear()
        self.data_values, self.data_index, self.data_overread = (), 0, 0
        self.pending_key = None
        for key in [key for key in self.variables if key.isdigit()]:
            self.variables.pop(key, None)
        self.variables["0"] = subroutine or Path(program.name).stem
        for index in range(1, 10):
            self.variables[str(index)] = ""
        for index, value in enumerate(values, 1):
            self.variables[str(index)] = value
        self.allow_navigation_return = False


    def leave_module(self) -> bool:
        if not self.module_stack:
            return True
        (self.program, self.pc, self.calls, self.loops,
         self.data_values, self.data_index, self.data_overread, self.pending_key,
         saved_arguments) = self.module_stack.pop()
        return_value = self.variables.get("0", 0)
        saved_locals = self.module_local_scopes.pop()
        for name, old in reversed(tuple(saved_locals.items())):
            if old is _UNSET:
                self.variables.pop(name, None)
            else:
                self.variables[name] = old  # type: ignore[assignment]
        for name, old in saved_arguments.items():
            if old is _UNSET:
                self.variables.pop(name, None)
            else:
                self.variables[name] = old  # type: ignore[assignment]
        self.variables["0"] = return_value
        return False


    def raster(self, requested: str, kinds: tuple[str, ...]) -> Raster:
        key = resource_key(self.assets, self.string(requested), kinds)
        try:
            image = self.assets.rasters[key]
            if image.recovery and image.recovery not in self.recovery_notes:
                self.recovery_notes.append(image.recovery)
            return image
        except KeyError as exc:
            detail = self.assets.errors.get(key, "member is not a supported raster")
            raise fail(f"{requested!r} is not a decoded raster: {detail}") from exc


    def put_clip(self, register: int, x: int, y: int) -> None:
        image = self.clips.get(register) or self.pages.get(register)
        if image is None and register in self.freed_clips:
            image = self.freed_clips[register]
            self.clips[register] = image
            note = f"reused released clipping buffer {register} before its memory was overwritten"
            if note not in self.recovery_notes:
                self.recovery_notes.append(note)
        if image is None:
            raise fail(f"PUTUP buffer {register} is not loaded")
        if register in self.clips and register in self.clip_unshifted_only:
            pixels_per_byte = (8 if self.r.colors in (2, 16)
                               else 4 if self.r.colors == 4 else 1)
            if (x + image.xoff) % pixels_per_byte:
                # CLOAD's shiftparm=1 stores only the byte-aligned image.
                # Original GRASP documents a non-byte PUTUP/FLY as producing
                # no put-up rather than synthesizing a shifted copy.
                return
        self.r.paste(image, x, y)


    def jump(self, label: str) -> None:
        target = self.string(label).casefold()
        if target not in self.program.labels:
            raise fail(f"unknown label {target!r}")
        self.pc = self.program.labels[target]


    def skip_false_block(self) -> None:
        depth = 1
        while self.pc < len(self.program.code) and depth:
            probe = self.program.code[self.pc]
            if probe.op in ("if", "ifmem", "ifvideo") and len(probe.args) == 1:
                depth += 1
            elif probe.op == "endif":
                depth -= 1
            elif probe.op == "else" and depth == 1:
                self.pc += 1
                break
            self.pc += 1


    def delay_arg(self, args: tuple[str, ...], index: int, default: float = 0) -> None:
        delay = float(self.value(args[index])) if len(args) > index else default
        if delay > 0: self.writer.delay(delay)


    def flowing_text(self, text: str) -> None:
        wx1, wy1, wx2, wy2 = self.r.window
        x, y = self.text_x, self.text_y
        if not (wx1 <= x <= wx2 and wy1 <= y and y + self.r.font.height - 1 <= wy2):
            x, y = wx1, wy2 - self.r.font.height + 1
        if self.r.center or self.r.right:
            # Justification applies independently to each TEXT string. The
            # DOS formatter then leaves its cursor at the next baseline; this
            # is why consecutive CENTER/RIGHT commands form separate lines.
            lines = text.replace("\r", "").split("\n")
            for line in lines:
                if y >= wy1:
                    self.r.draw_text(wx1, y, line)
                y -= self.r.font.height + self.r.line_gap
            self.text_x, self.text_y = wx1, y
            return
        for character in text:
            if character in "\r\n":
                if character == "\n":
                    x, y = wx1, y - self.r.font.height - self.r.line_gap
                continue
            byte = character.encode("cp437", errors="replace")[0]
            index = byte - self.r.font.first
            width = (self.r.font.widths[index]
                     if 0 <= index < self.r.font.count else self.r.font.width)
            if byte == 32 and self.r.space_gap:
                width = self.r.space_gap
            if x > wx1 and x + width - 1 > wx2:
                x, y = wx1, y - self.r.font.height - self.r.line_gap
            if y >= wy1:
                self.r.draw_text(x, y, character)
            x += width + self.r.char_gap
        self.text_x, self.text_y = x, y


    def fade_transition(self, before: bytes, style: int,
                        rectangle: tuple[int, int, int, int], speed: int = 0) -> None:
        target = bytes(self.r.screen)
        if style == 0:
            self.writer.frame()
            return
        self.r.screen[:] = before
        x1, y1, x2, y2 = rectangle
        wx1, wy1, wx2, wy2 = self.r.bounds_top()
        x1, x2 = max(0, x1, wx1), min(self.r.width - 1, x2, wx2)
        y1, y2 = max(0, y1, wy1), min(self.r.height - 1, y2, wy2)
        if x1 > x2 or y1 > y2:
            self.r.screen[:] = target; self.writer.frame(); return
        width, height = x2 - x1 + 1, y2 - y1 + 1
        if style == 0:
            self.r.screen[:] = target
            self.writer.frame()
            return
        requested_phases = max(1, int(round(max(0, speed) * FPS / 100)))
        bits_per_pixel = max(1, (self.r.colors - 1).bit_length())
        stored_bytes = (width * height * bits_per_pixel + 7) // 8
        minimum_phases = max(1, (stored_bytes + FADE_BYTES_PER_FRAME - 1)
                             // FADE_BYTES_PER_FRAME)
        # GRASP disregards an omitted/explicit speed below the hardware time
        # needed to touch the video bytes. Use a fixed DOS-era 64 KiB/frame
        # baseline so native conversion has deterministic minimum timing.
        phases = max(requested_phases, minimum_phases)
        if phases == 1:
            # A hardware-minimum fade completes between two 20 fps sampling
            # instants, so only its completed state belongs in the AVI.
            self.r.screen[:] = target
            self.writer.frame()
            return
        # These are the original FADE.C drawing primitives in their original
        # order. Local y coordinates are bottom-up, like GRASP; screen rows are
        # top-down, so primitive application flips y at the last moment.
        operations: list[tuple] = []
        v = lambda x, ya=0, yb=height - 1: operations.append(("v", x, ya, yb, 1))
        v2 = lambda x, ya=0, yb=height - 1: operations.append(("v", x, ya, yb, 2))
        h = lambda y, xa=0, xb=width - 1: operations.append(("h", xa, y, xb, 1))
        h2 = lambda xa, y, xb=width - 1: operations.append(("h", xa, y, xb, 2))
        ev = lambda edge_x, x, ya=0, yb=height - 1: operations.append(
            ("ev", edge_x, x, ya, yb))
        eh = lambda edge_y, y, xa=0, xb=width - 1: operations.append(
            ("eh", edge_y, y, xa, xb))
        line = lambda xa, ya, xb, yb: operations.append(("l", xa, ya, xb, yb))
        if style == 1:
            for i in range(width):
                ev(i + 1, i) if self.r.edge_color is not None and i < width - 1 else v(i)
        elif style == 2:
            for i in range(width - 1, -1, -1):
                ev(i - 1, i) if self.r.edge_color is not None and i > 0 else v(i)
        elif style in (3, 4):
            half = width >> 1
            iterator = range(half + 1) if style == 3 else range(half, -1, -1)
            for i in iterator:
                if self.r.edge_color is not None and ((style == 3 and i < half) or
                                                       (style == 4 and i > 0)):
                    if style == 3:
                        ev(i + 1, i); ev(width - 2 - i, width - 1 - i)
                    else:
                        ev(i - 1, i); ev(width - i, width - 1 - i)
                else:
                    v(i); v(width - 1 - i)
        elif style == 5:
            for i in range(width): v2(i, 0); v2(width - 1 - i, 1)
        elif style == 6:
            for i in range(width): v2(i, 0)
            for i in range(width - 1, -1, -1): v2(i, 1)
        elif style == 7:
            half = height >> 1
            for i in range(width): v(i, 0, half)
            for i in range(width - 1, -1, -1): v(i, half + 1, height - 1)
        elif style == 8:
            half = width >> 1
            for i in range(half): v(i); v(half + i)
        elif style == 9:
            for i in range(height - 1, -1, -1):
                eh(i - 1, i) if self.r.edge_color is not None and i > 0 else h(i)
        elif style == 10:
            for i in range(height):
                eh(i + 1, i) if self.r.edge_color is not None and i < height - 1 else h(i)
        elif style in (11, 12):
            half = (height - 1) >> 1
            iterator = range(half + 1) if style == 11 else range(half, -1, -1)
            for i in iterator:
                if self.r.edge_color is not None and ((style == 11 and i < half) or
                                                       (style == 12 and i > 0)):
                    if style == 11:
                        eh(i + 1, i); eh(height - 2 - i, height - 1 - i)
                    else:
                        eh(i - 1, i); eh(height - i, height - 1 - i)
                else:
                    h(i); h(height - 1 - i)
        elif style == 13:
            odd = 1 if height & 1 else 0
            for i in range(0, height, 2):
                if i + odd < height: h(i + odd)
                h(height - 1 - i)
        elif style == 14:
            half = height >> 1
            for i in range(half): h(height - 1 - i); h(height - 1 - half - i)
        elif style == 15:
            half = width >> 1
            for i in range(height - 1, -1, -1): h(i, 0, half - 1)
            for i in range(height): h(i, half, width - 1)
        elif style == 16:
            half_w, half_h = width >> 1, height >> 1
            for i in range(half_h + 1): h(height - 1 - i, 0, half_w - 1)
            for i in range(half_h - 1, -1, -1): h(i, half_w, width - 1)
            for i in range(half_h): h(i, 0, half_w - 1)
            for i in range(half_h, -1, -1): h(height - 1 - i, half_w, width - 1)
        elif style == 17:
            for i in range(height - 1, -1, -1): h2(0, i)
            for i in range(height): h2(1, i)
        elif style == 18:
            for i in range(height - 1, -1, -2): h2(0, i)
            for i in range(1, height, 2): h2(1, i)
            for i in range(height - 2, -1, -2): h2(0, i)
            for i in range(0, height, 2): h2(1, i)
        elif style == 19:
            # The original pour copies descending four-row ribbons. Diagonal
            # scanlines preserve its flowing direction at video frame rate.
            for diagonal in range(width + height - 1):
                xa, xb = max(0, diagonal - height + 1), min(width - 1, diagonal)
                line(xa, diagonal - xa, xb, diagonal - xb)
        elif style == 20:
            box = max(1, (width + 39) // 40)
            blocks = [(left, bottom, min(width, left + box), min(height, bottom + box))
                      for bottom in range(0, height, box) for left in range(0, width, box)]
            sparkle = random.Random((width << 20) ^ (height << 8) ^ 0x4752)
            sparkle.shuffle(blocks)
            operations.extend(("r", *block) for block in blocks)
        elif style == 21:
            dx, dy = width - 1, height - 1
            if dy > dx:
                for i in range(dx + 1): line(i, 0, 0, i)
                for i in range(dy - dx + 1): line(0, dx + i, dx, i)
                for i in range(dx + 1): line(i, dy, dx, dy - dx + i)
            else:
                for i in range(dy + 1): line(i, 0, 0, i)
                for i in range(dx - dy + 1): line(dy + 1 + i, 0, i, dy)
                for i in range(dy + 1): line(dx - dy + i, dy, dx, i)
        elif style in (22, 23):
            radius = min((width - 1) >> 1, (height - 1) >> 1)
            iterator = range(radius + 1) if style == 22 else range(radius, -1, -1)
            for i in iterator:
                left, right = radius - i, width - 1 - radius + i
                bottom, top = radius - i, height - 1 - radius + i
                if self.r.edge_color is None:
                    edge_box = None
                elif style == 22:
                    edge_box = (left - 1, bottom - 1, right + 1, top + 1)
                else:
                    edge_box = (left + 1, bottom + 1, right - 1, top - 1)
                operations.append(("a", left, bottom, right, top, edge_box))
        elif style == 24:
            cx, cy = width >> 1, height >> 1
            for i in range(cx, width): line(cx, cy, i, height - 1)
            for i in range(height - 1, -1, -1): line(cx, cy, width - 1, i)
            for i in range(width - 1, -1, -1): line(cx, cy, i, 0)
            for i in range(height): line(cx, cy, 0, i)
            for i in range(cx): line(cx, cy, i, height - 1)
        elif style == 25:
            for i in range(width - 1, -1, -1):
                line(0, 0, i, height - 1); line(width - 1, height - 1, width - 1 - i, 0)
        else:
            raise fail(f"fade style {style} is outside 0..25")

        def put(px: int, py: int) -> None:
            if 0 <= px < width and 0 <= py < height:
                absolute_y = y2 - py
                at = absolute_y * self.r.width + x1 + px
                self.r.screen[at] = target[at]

        def edge_put(px: int, py: int) -> None:
            if self.r.edge_color is not None and 0 <= px < width and 0 <= py < height:
                absolute_y = y2 - py
                self.r.screen[absolute_y * self.r.width + x1 + px] = self.r.edge_color

        def edge_horizontal(xa: int, py: int, xb: int) -> None:
            for px in range(max(0, xa), min(width - 1, xb) + 1): edge_put(px, py)

        def edge_vertical(px: int, ya: int, yb: int) -> None:
            for py in range(max(0, ya), min(height - 1, yb) + 1): edge_put(px, py)

        def apply(operation: tuple) -> None:
            kind = operation[0]
            if kind == "v":
                _, px, ya, yb, step = operation
                for py in range(max(0, ya), min(height - 1, yb) + 1, step): put(px, py)
            elif kind == "h":
                _, xa, py, xb, step = operation
                for px in range(max(0, xa), min(width - 1, xb) + 1, step): put(px, py)
            elif kind == "ev":
                _, edge_x, px, ya, yb = operation
                edge_vertical(edge_x, ya, yb)
                for py in range(max(0, ya), min(height - 1, yb) + 1): put(px, py)
            elif kind == "eh":
                _, edge_y, py, xa, xb = operation
                edge_horizontal(xa, edge_y, xb)
                for px in range(max(0, xa), min(width - 1, xb) + 1): put(px, py)
            elif kind == "a":
                _, left, bottom, right, top, edge_box = operation
                if edge_box is not None:
                    el, eb, er, et = edge_box
                    edge_horizontal(el, eb, er); edge_horizontal(el, et, er)
                    edge_vertical(el, eb, et); edge_vertical(er, eb, et)
                for px in range(max(0, left), min(width - 1, right) + 1):
                    put(px, bottom); put(px, top)
                for py in range(max(0, bottom), min(height - 1, top) + 1):
                    put(left, py); put(right, py)
            elif kind == "r":
                _, left, bottom, right, top = operation
                for py in range(bottom, top):
                    absolute_y = y2 - py
                    at = absolute_y * self.r.width + x1 + left
                    self.r.screen[at:at + right - left] = target[at:at + right - left]
            else:
                _, xa, ya, xb, yb = operation
                dx, sx = abs(xb - xa), 1 if xa < xb else -1
                dy, sy = -abs(yb - ya), 1 if ya < yb else -1
                error = dx + dy
                while True:
                    put(xa, ya)
                    if xa == xb and ya == yb: break
                    twice = error * 2
                    if twice >= dy: error += dy; xa += sx
                    if twice <= dx: error += dx; ya += sy

        # GRASP divides the requested total fade time among its primitives.
        # An omitted/zero speed uses the deterministic hardware-minimum phase
        # count calculated above; a larger explicit speed remains visible for
        # the requested number of hundredths.
        for phase in range(1, phases + 1):
            start = len(operations) * (phase - 1) // phases
            end = len(operations) * phase // phases
            for operation in operations[start:end]: apply(operation)
            if phase == phases:
                self.r.screen[:] = target
            self.writer.frame()
        self.r.screen[:] = target


    def fade_raster(self, image: Raster, style: int, x: int, y: int, speed: int = 0) -> None:
        # CFADE is deliberately different from PUTUP/FLY: it ignores saved CLP
        # offsets, rounds x to a video-memory byte boundary, and pads the
        # right edge of non-byte-wide clippings with the last palette index.
        pixels_per_byte = 8 if self.r.colors in (2, 16) else 4 if self.r.colors == 4 else 1
        # CFADE uses the nearest video-byte boundary; an exact halfway value
        # rounds upward (the original manual's x=20 -> x=24 example in a
        # one-bit planar mode).
        x = ((x + pixels_per_byte // 2) // pixels_per_byte) * pixels_per_byte
        padded_width = ((image.width + pixels_per_byte - 1) // pixels_per_byte) * pixels_per_byte
        if padded_width != image.width:
            if image.packed_width == padded_width and image.packed_pixels is not None:
                padded = image.packed_pixels
            else:
                rows = []
                for row in range(image.height):
                    source = image.pixels[row * image.width:(row + 1) * image.width]
                    fill = source[-1] if source else 0
                    rows.append(source + bytes((fill,)) * (padded_width - image.width))
                padded = b"".join(rows)
            image = Raster(padded_width, image.height, 0, 0, padded, image.palette)
        # WINDOW clips PFADE, but the original command reference explicitly
        # states that it has no effect on CFADE. Several scripts deliberately
        # leave a small page-fade window active while revealing a larger clip.
        saved_window = self.r.window
        self.r.window = (0, 0, self.r.width - 1, self.r.height - 1)
        try:
            before = bytes(self.r.screen)
            self.r.paste(image, x, y, honor_transparency=False, use_offsets=False)
            left = x
            top = self.r.height - y - image.height
            self.fade_transition(before, style, (left, top, left + image.width - 1,
                                                 top + image.height - 1), speed)
        finally:
            self.r.window = saved_window


    def fade_page(self, image: Raster | None, style: int, speed: int = 0,
                  position: tuple[int, int] | None = None) -> None:
        before = bytes(self.r.screen)
        if image is None:
            self.r.rect(0, 0, self.r.width - 1, self.r.height - 1)
        else:
            # PIC origin fields are honored by clipping placement commands,
            # but a page is video memory: PFADE addresses it from the active
            # page/window origin. Applying the saved origin leaves strips of
            # the previous page and clips the new page at the opposite edges.
            window_width = self.r.window[2] - self.r.window[0] + 1
            window_height = self.r.window[3] - self.r.window[1] + 1
            if style == 0 and position is not None:
                # POSITION names the source pixel that appears at the active
                # window's lower-left corner. It is a viewport into a large
                # picture, not a destination displacement, and only instant
                # PFADE zero observes it.
                source_x, source_y = position
                dest_x, dest_y, dest_x2, dest_y2 = self.r.window
                for row in range(dest_y2 - dest_y + 1):
                    sy, dy = source_y + row, dest_y + row
                    if sy < 0 or sy >= image.height or dy < 0 or dy >= self.r.height:
                        continue
                    first = max(0, -source_x, -dest_x)
                    last = min(dest_x2 - dest_x + 1,
                               image.width - source_x, self.r.width - dest_x)
                    if first >= last:
                        continue
                    source = (image.height - 1 - sy) * image.width + source_x + first
                    target = (self.r.height - 1 - dy) * self.r.width + dest_x + first
                    self.r.screen[target:target + last - first] = image.pixels[
                        source:source + last - first]
            elif image.display_width == self.r.width and image.display_height == self.r.height \
                    and (image.width < self.r.width or image.height < self.r.height):
                self.r.paste(image, (self.r.width - image.width) // 2,
                             (self.r.height - image.height) // 2,
                             honor_transparency=False, use_offsets=False)
            elif image.width == window_width and image.height == window_height:
                self.r.paste(image, self.r.window[0], self.r.window[1],
                             honor_transparency=False, use_offsets=False)
            else:
                self.r.paste(image, 0, 0, honor_transparency=False, use_offsets=False)
        wx1, wy1, wx2, wy2 = self.r.bounds_top()
        self.fade_transition(before, style, (wx1, wy1, wx2, wy2), speed)


    def dff_frame(self, register: int, index: int, x: int, y: int) -> None:
        dff = self.dffs[register]
        if isinstance(dff, Flic):
            frame = dff.frames[index]
            self.r.install_palette(frame.palette)
            self.r.paste(frame, x, y, honor_transparency=False, use_offsets=False)
            return
        frame = dff.frames[index]
        if frame.width == 0 and frame.height == 0:
            return
        row_bytes = (frame.width * dff.bits + 7) // 8
        wanted = row_bytes * frame.height * dff.planes
        left, bottom = x + frame.xoff, y + frame.yoff
        # DFF skip opcodes preserve bytes already present in video memory at
        # this frame's destination rectangle. Frame rectangles may differ,
        # so a private animation-sized backing buffer is not equivalent.
        state = self.r.extract_planar(frame.width, frame.height, left, bottom,
                                      dff.bits, dff.planes)
        pos = virtual = 0
        commands = frame.commands
        while pos < len(commands):
            op = commands[pos]; pos += 1
            if op & 0x80:
                count = op & 0x7f
                if not count: count, pos = u16(commands, pos), pos + 2
                usable = max(0, min(count, wanted - virtual))
                if usable:
                    state[virtual:virtual + usable] = commands[pos:pos + usable]
                pos += count
            elif op & 0x40:
                count = op & 0x3f
                if not count: count, pos = u16(commands, pos), pos + 2
                usable = max(0, min(count, wanted - virtual))
                if usable:
                    state[virtual:virtual + usable] = bytes((commands[pos],)) * usable
                pos += 1
            else:
                count = op & 0x3f
                if not count: count, pos = u16(commands, pos), pos + 2
            virtual += count
        pixels = planar_pixels(bytes(state), frame.width, frame.height, dff.bits, dff.planes,
                               "DFF runtime frame")
        self.r.paste(Raster(frame.width, frame.height, 0, 0, pixels), left, bottom,
                     honor_transparency=False)


    def text_page(self, image: Raster) -> Raster:
        if self.text_mode is None:
            return image
        columns, rows = self.text_mode
        # Extended Pictor mode 0/1/2 members are expanded from character/
        # attribute pairs during structural decoding.
        if image.width == columns * 8 and image.height == rows * 16:
            return image
        if image.width != columns * 2 or image.height != rows:
            raise fail(f"text page is {image.width}x{image.height}, expected {columns * 2}x{rows}")
        font = text_mode_font()
        cell_width = max(1, OUT_WIDTH // columns)
        cell_height = max(1, OUT_HEIGHT // rows)
        used_width, used_height = cell_width * columns, cell_height * rows
        left, top = (OUT_WIDTH - used_width) // 2, (OUT_HEIGHT - used_height) // 2
        pixels = bytearray(OUT_WIDTH * OUT_HEIGHT)
        for row in range(rows):
            for column in range(columns):
                cell = row * image.width + column * 2
                character, attribute = image.pixels[cell], image.pixels[cell + 1]
                foreground, background = attribute & 15, (attribute >> 4) & 7
                glyph = font.glyphs[character]
                for py in range(cell_height):
                    glyph_y = py * font.height // cell_height
                    dest = (top + row * cell_height + py) * OUT_WIDTH + left + column * cell_width
                    for px in range(cell_width):
                        glyph_x = px * font.width // cell_width
                        on = glyph[glyph_y] & (0x80 >> glyph_x)
                        pixels[dest + px] = foreground if on else background
        return Raster(OUT_WIDTH, OUT_HEIGHT, 0, 0, bytes(pixels), tuple(EGA16))


    def execute_com(self, requested: str) -> None:
        key = resource_key(self.assets, self.string(requested), (".com",))
        data = self.assets.members[key].payload
        # Strictly recognize the Video Seven BIOS-mode helper form:
        # MOV AH,6F / MOV AL,05 / MOV BL,mode / INT 10 / INT 20.
        if len(data) != 10 or data[:2] != b"\xb4\x6f" or data[2:4] != b"\xb0\x05" \
                or data[4] != 0xb3 or data[6:] != b"\xcd\x10\xcd\x20":
            raise fail(f"EXEC member {requested!r} is not a supported declarative video-mode helper")
        self.variables["bios_video_submode"] = data[5]


    def run(self) -> None:
        while True:
            if not 0 <= self.pc < len(self.program.code):
                if self.leave_module():
                    break
                continue
            self.steps += 1
            if self.steps > MAX_STEPS:
                raise fail("program exceeds deterministic instruction limit")
            inst = self.program.code[self.pc]
            source_name = self.program.name
            self.pc += 1
            try:
                if self.execute(inst):
                    break
            except (ValueError, ZeroDivisionError, KeyError, IndexError) as exc:
                raise fail(f"{source_name}:{inst.line}: {inst.raw.strip()}: {exc}") from exc
        if self.pset_context is not None:
            raise fail("program ended while PSETBUF was still active")


    def execute(self, inst: Instruction) -> bool:
        op, a = inst.op, inst.args
        if op.startswith("@"):
            resolved_op = self.string(op).casefold()
            if resolved_op and resolved_op != op:
                return self.execute(Instruction(resolved_op, a, inst.line, inst.raw))
        if op not in SUPPORTED_COMMANDS and op in self.program.labels:
            self.push_call(self.pc, op, a)
            self.pc = self.program.labels[op]
            return False
        if op not in SUPPORTED_COMMANDS:
            for merged in reversed(self.merged_programs.get(self.program.name.casefold(), [])):
                if op in merged.labels:
                    self.enter_module(merged, merged.labels[op], a, op)
                    return False
        if op == "video":
            if not a: raise fail("VIDEO requires a mode")
            video_mode = self.string(a[0])
            if video_mode.casefold() in ("0", "1", "2"):
                columns = self.ivalue(a[1]) if len(a) > 1 else 80
                rows = self.ivalue(a[2]) if len(a) > 2 else 25
                if columns < 1 or rows < 1 or columns > 160 or rows > 100:
                    raise fail("text VIDEO dimensions are outside the supported hardware range")
                self.r.set_text_video(columns, rows)
                self.text_mode = (columns, rows)
            else:
                self.r.set_video(video_mode)
                if len(a) >= 3:
                    width, height = self.ivalue(a[1]), self.ivalue(a[2])
                    if width < 1 or height < 1 or width > 4096 or height > 4096:
                        raise fail("custom VIDEO dimensions exceed the supported framebuffer")
                    self.r.width = self.r.view_width = width
                    self.r.height = self.r.view_height = height
                    self.r.screen = bytearray(width * height)
                    self.r.window = (0, 0, width - 1, height - 1)
                self.text_mode = None
            self.text_x = self.r.window[0]
            self.text_y = self.r.window[3] - self.r.font.height + 1
            self.offset_x = self.offset_y = 0
            # FLOAT's saved background belongs to the video page on which it
            # was captured. A mode set discards that hardware page.
            self.float_background = None
            return False
        if op == "color":
            if not a: raise fail("COLOR requires a foreground")
            self.r.fg = self.ivalue(a[0]) & 255
            if len(a) > 1: self.r.bg = self.ivalue(a[1]) & 255
            self.variables["color"] = self.r.fg
        elif op == "clearscr":
            color = self.ivalue(a[0]) & 255 if a else self.r.fg
            self.r.screen[:] = bytes((color,)) * len(self.r.screen)
        elif op == "flood":
            if len(a) < 2:
                raise fail("FLOOD requires x and y")
            x, y = self.xy(a[0], a[1])
            if not (0 <= x < self.r.width and 0 <= y < self.r.height):
                return False
            top_y = self.r.height - 1 - y
            source = self.r.screen[top_y * self.r.width + x]
            target = self.r.fg & 255
            if source == target:
                return False
            wx1, wy1, wx2, wy2 = self.r.bounds_top()
            stack = [(x, top_y)]
            while stack:
                px, py = stack.pop()
                if not (wx1 <= px <= wx2 and wy1 <= py <= wy2):
                    continue
                at = py * self.r.width + px
                if self.r.screen[at] != source:
                    continue
                self.r.screen[at] = target
                stack.extend(((px - 1, py), (px + 1, py),
                              (px, py - 1), (px, py + 1)))
        elif op == "flushkey":
            self.pending_key = None
        elif op == "load":
            if not a:
                raise fail("LOAD requires a member name")
            requested = self.resource_name(a[0])
            if Path(requested).suffix:
                key = requested.casefold()
                if key not in self.assets.members:
                    raise fail(f"LOAD member {requested!r} is not embedded in this GL")
            else:
                key = resource_key(self.assets, requested,
                                   (".grp", ".snd", ".raw", ".cmf", ".mus", ".dat"))
            member = self.assets.members[key]
            stem = Path(requested).stem.casefold()
            pointer = self.named_register(stem)
            self.loaded_members[stem] = member
            self.loaded_members[key] = member
            self.loaded_members[str(pointer)] = member
            self.variables[stem] = pointer
        elif op == "free":
            for token in a:
                requested = self.string(token).lstrip("@").casefold()
                member = self.loaded_members.pop(requested, None)
                if member is not None:
                    for key in [key for key, value in self.loaded_members.items()
                                if value is member]:
                        self.loaded_members.pop(key, None)
        elif op in ("digpak", "@sound"):
            if not a:
                raise fail(f"{op.upper()} requires an operation")
            action = self.string(a[0]).casefold()
            if action in ("preloaded", "play") and len(a) > 1:
                reference = self.string(a[1]).lstrip("@").casefold()
                self.current_digital_sound = self.loaded_members.get(reference)
            if action == "find":
                self.variables["0"] = 1
            elif action == "play":
                if self.current_digital_sound is None:
                    # A single loaded PCM member is the implicit playback
                    # source used by both SOUND.GRP and older DIGPAK.GRP.
                    candidates = {id(member): member for member in self.loaded_members.values()
                                  if Path(member.name).suffix.casefold() in (".raw", ".snd")}
                    if len(candidates) == 1:
                        self.current_digital_sound = next(iter(candidates.values()))
                if self.current_digital_sound is None:
                    raise fail("digital PLAY has no loaded RAW/SND member")
                self.play_digital_member(self.current_digital_sound)
                self.variables["0"] = 0
            elif action == "done":
                self.variables["0"] = 0
            elif action in ("port", "use", "volume", "speed", "stop", "quit"):
                self.variables["0"] = 1
            elif action != "preloaded":
                raise fail(f"unsupported {op.upper()} operation {action!r}")
        elif op == "rect":
            x1, y1 = self.xy(a[0], a[1]); x2, y2 = self.xy(a[2], a[3])
            self.r.rect(x1, y1, x2, y2)
        elif op == "box":
            if len(a) < 4: raise fail("BOX requires four coordinates")
            x1, y1 = self.xy(a[0], a[1]); x2, y2 = self.xy(a[2], a[3])
            self.r.box(x1, y1, x2, y2, self.ivalue(a[4]) if len(a) > 4 else 1)
        elif op == "line":
            x1, y1 = self.xy(a[0], a[1]); x2, y2 = self.xy(a[2], a[3])
            self.r.line(x1, y1, x2, y2)
        elif op == "circle":
            if len(a) < 3: raise fail("CIRCLE requires center and radius")
            x, y = self.xy(a[0], a[1])
            rx = self.ivalue(a[2]); ry = self.ivalue(a[3]) if len(a) > 3 else rx
            self.r.circle(x, y, rx, ry)
        elif op == "point":
            if len(a) not in (2, 4): raise fail("POINT requires x,y and optionally x2,y2")
            x1, y1 = self.xy(a[0], a[1])
            if len(a) == 4:
                x2, y2 = self.xy(a[2], a[3])
                x1, x2 = sorted((x1, x2)); y1, y2 = sorted((y1, y2))
                x1, y1 = self.random.randint(x1, x2), self.random.randint(y1, y2)
            self.r.point(x1, y1)
        elif op == "getcolor":
            if len(a) < 2: raise fail("GETCOLOR requires x and y")
            x, y = self.xy(a[0], a[1])
            if not (0 <= x < self.r.width and 0 <= y < self.r.height):
                raise fail("GETCOLOR coordinate is outside the framebuffer")
            value = self.r.screen[(self.r.height - 1 - y) * self.r.width + x]
            if len(a) > 2:
                self.variables[a[2].casefold()] = value
            else:
                self.r.fg = value
        elif op == "move":
            if len(a) < 6: raise fail("MOVE requires source rectangle and destination")
            x1, y1 = self.xy(a[0], a[1]); x2, y2 = self.xy(a[2], a[3])
            dx, dy = self.xy(a[4], a[5])
            x1, x2 = sorted((x1, x2)); y1, y2 = sorted((y1, y2))
            width, height = x2 - x1 + 1, y2 - y1 + 1
            pixels = bytearray(width * height)
            for row in range(height):
                source_y = y2 - row
                for column in range(width):
                    source_x = x1 + column
                    if 0 <= source_x < self.r.width and 0 <= source_y < self.r.height:
                        pixels[row * width + column] = self.r.screen[
                            (self.r.height - 1 - source_y) * self.r.width + source_x]
            self.r.paste(Raster(width, height, 0, 0, bytes(pixels)), dx, dy,
                         honor_transparency=False, use_offsets=False)
            self.delay_arg(a, 6)
        elif op == "window":
            if not a: self.r.window = (0, 0, self.r.width - 1, self.r.height - 1)
            elif len(a) >= 4:
                values = tuple(self.ivalue(x) for x in a[:4])
                if len(a) > 4 and a[4].casefold() == "r":
                    values = tuple(old + change for old, change in zip(self.r.window, values))
                self.r.window = values
            else: raise fail("WINDOW needs zero or four coordinates")
            self.text_x = self.r.window[0]
            self.text_y = self.r.window[3] - self.r.font.height + 1
        elif op == "cload":
            if not a: raise fail("CLOAD requires a resource")
            requested = self.resource_name(a[0])
            register = self.ivalue(a[1]) if len(a) > 1 else 1
            self.clips[register] = self.raster(requested, (".clp", ".pic", ".pcc"))
            self.freed_clips.pop(register, None)
            if len(a) == 1:
                self.clips[self.named_register(requested)] = self.clips[register]
            shiftparm = self.ivalue(a[2]) if len(a) > 2 else 0
            if shiftparm not in (0, 1):
                raise fail("CLOAD shift parameter must be zero or one")
            if shiftparm: self.clip_unshifted_only.add(register)
            else: self.clip_unshifted_only.discard(register)
        elif op == "pload":
            if not a: raise fail("PLOAD requires a resource")
            requested = self.resource_name(a[0])
            register = self.ivalue(a[1]) if len(a) > 1 else 1
            self.pages[register] = self.raster(requested, (".pic", ".pcx", ".pcc", ".gif", ".clp"))
            self.freed_pages.pop(register, None)
            self.page_positions.pop(register, None)
            if len(a) == 1:
                named = self.named_register(requested)
                self.pages[named] = self.pages[register]
                self.freed_pages.pop(named, None)
        elif op in ("cfree", "pfree", "dfree"):
            table = self.clips if op == "cfree" else self.pages if op == "pfree" else self.dffs
            if any(value == "*" for value in a):
                if op == "pfree": self.freed_pages.update(self.pages)
                elif op == "cfree": self.freed_clips.update(self.clips)
                table.clear()
                if op == "cfree": self.clip_unshifted_only.clear()
                return False
            for register in integer_range(a, self.ivalue):
                if op == "pfree" and register in self.pages:
                    self.freed_pages[register] = self.pages[register]
                elif op == "cfree" and register in self.clips:
                    self.freed_clips[register] = self.clips[register]
                table.pop(register, None)
                if op == "cfree": self.clip_unshifted_only.discard(register)
        elif op == "putup":
            if not a: raise fail("PUTUP requires a buffer or x,y")
            # Evaluate left-to-right. DATABEGIN's @ cursor advances at each
            # argument, so looking up the clip before the coordinates changes
            # the meaning of PUTUP @,0,@.
            if len(a) == 1:
                x, y, register = 0, 0, self.ivalue(a[0])
            else:
                x, y = self.xy(a[0], a[1]); register = self.ivalue(a[2]) if len(a) > 2 else 1
            if register not in self.clips and register not in self.pages \
                    and register in self.freed_clips:
                self.clips[register] = self.freed_clips[register]
                note = f"reused released clipping buffer {register} before its memory was overwritten"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
            self.put_clip(register, x, y)
            self.delay_arg(a, 3)
        elif op == "cfade":
            if len(a) < 3: raise fail("CFADE requires style, position, and clip")
            style = self.ivalue(a[0])
            if len(a) == 3:
                x, y, register = self.ivalue(a[1]) + self.offset_x, self.offset_y, self.ivalue(a[2])
            else:
                x, y = self.xy(a[1], a[2]); register = self.ivalue(a[3])
            speed = self.ivalue(a[4]) if len(a) > 4 else 0
            image = self.clips.get(register) or self.pages.get(register)
            if image is None: raise fail(f"CFADE buffer {register} is not loaded")
            self.fade_raster(image, style, x, y, speed)
            self.delay_arg(a, 5)
        elif op in ("pfade", "fade"):
            if not a: raise fail("PFADE requires a style")
            style = self.ivalue(a[0]); register = self.ivalue(a[1]) if len(a) > 1 else 0
            speed = self.ivalue(a[2]) if len(a) > 2 else 0
            if register == 0:
                page = None
            elif register in self.pages:
                page = self.pages[register]
            elif register in self.freed_pages:
                page = self.freed_pages[register]
                note = f"reused released page buffer {register} after invalid PFREE"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
            else:
                raise fail(f"PFADE buffer {register} is not loaded")
            if page is not None: page = self.text_page(page)
            self.fade_page(page, style, speed, self.page_positions.get(register))
            self.delay_arg(a, 3)
        elif op == "palette":
            if a and not a[0].startswith("@") and not re.fullmatch(r"[-+]?\d+", a[0]):
                try:
                    source = self.raster(a[0], (".pic", ".pcx", ".pcc", ".gif", ".clp", ".pal"))
                except GraspError as exc:
                    if "is not present" not in str(exc):
                        raise
                    register = self.ivalue(a[0])
                    source = (self.pages.get(register) or self.clips.get(register)
                              or self.freed_pages.get(register)
                              or self.freed_clips.get(register))
                    if source is None:
                        note = f"PALETTE source {a[0]!r} is absent; active palette retained"
                        if note not in self.recovery_notes:
                            self.recovery_notes.append(note)
                        return False
            else:
                register = self.ivalue(a[0]) if a else 1
                source = (self.pages.get(register) or self.clips.get(register)
                          or self.freed_pages.get(register))
                if source is None:
                    note = f"PALETTE buffer {register} is not loaded; active palette retained"
                    if note not in self.recovery_notes:
                        self.recovery_notes.append(note)
                    return False
            self.r.install_palette(source.palette)
        elif op == "cycle":
            if len(a) < 3: raise fail("CYCLE requires cycles, start, and color count")
            cycles, start, count = (self.ivalue(value) for value in a[:3])
            delay = float(self.value(a[3])) if len(a) > 3 else 0.0
            if count < 2 or start < 0 or start + count > len(self.r.palette):
                raise fail("CYCLE palette range is invalid")
            direction = 1 if cycles >= 0 else -1
            total = abs(cycles)
            def rotate() -> None:
                part = self.r.palette[start:start + count]
                if direction > 0:
                    part = part[-1:] + part[:-1]
                else:
                    part = part[1:] + part[:1]
                self.r.palette[start:start + count] = part
            if delay <= 0 or total == 0:
                for _ in range(total): rotate()
                self.writer.frame()
            else:
                frames = max(1, int(round(total * delay * FPS / 100)))
                completed = 0
                for frame in range(1, frames + 1):
                    target = total * frame // frames
                    for _ in range(target - completed): rotate()
                    completed = target
                    self.writer.frame()
        elif op == "tile":
            register = self.ivalue(a[0]) if a else 1
            source = self.pages.get(register) or self.clips.get(register)
            if source is None: raise fail(f"TILE buffer {register} is not loaded")
            self.r.tiled(source)
        elif op == "dload":
            if not a: raise fail("DLOAD requires a resource")
            requested = self.resource_name(a[0])
            register = self.ivalue(a[1]) if len(a) > 1 else 1
            key = resource_key(self.assets, requested, (".dff", ".flc", ".fli"))
            try:
                self.dffs[register] = self.assets.dffs[key]
            except KeyError as exc:
                detail = self.assets.errors.get(key, "member is not a supported DFF")
                raise fail(f"{requested!r} is not a decoded DFF: {detail}") from exc
        elif op in ("pgetbuf", "cgetbuf"):
            if not a: raise fail(f"{op.upper()} requires a buffer register")
            register = self.ivalue(a[0])
            if len(a) == 1:
                x1, y1, x2, y2 = self.r.window
            elif len(a) >= 5:
                x1, y1 = self.xy(a[1], a[2]); x2, y2 = self.xy(a[3], a[4])
            else:
                raise fail(f"{op.upper()} requires a register and optionally four coordinates")
            x1, x2 = sorted((x1, x2)); y1, y2 = sorted((y1, y2))
            x1, x2 = max(0, x1), min(self.r.width - 1, x2)
            y1, y2 = max(0, y1), min(self.r.height - 1, y2)
            if x1 > x2 or y1 > y2: raise fail(f"{op.upper()} rectangle is outside the screen")
            width, height = x2 - x1 + 1, y2 - y1 + 1
            top = self.r.height - 1 - y2
            pixels = bytearray(width * height)
            for row in range(height):
                source = (top + row) * self.r.width + x1
                pixels[row * width:(row + 1) * width] = self.r.screen[source:source + width]
            # A captured clipping retains its screen origin, allowing
            # PUTUP 0,0 to restore it in place. A captured page is addressed
            # from its own (0,0), like other page buffers.
            xoff, yoff = (x1, y1) if op == "cgetbuf" else (0, 0)
            image = Raster(width, height, xoff, yoff, bytes(pixels), tuple(self.r.palette))
            if op == "pgetbuf":
                self.pages[register] = image
                self.page_positions.pop(register, None)
            else:
                self.clips[register] = image
                self.clip_unshifted_only.discard(register)
        elif op == "pnewbuf":
            if not a: raise fail("PNEWBUF requires a buffer")
            register = self.ivalue(a[0])
            if len(a) == 1:
                width, height = self.r.view_width, self.r.view_height
            elif len(a) >= 3:
                width, height = self.ivalue(a[1]), self.ivalue(a[2])
            else:
                raise fail("PNEWBUF dimensions require both x and y")
            if width < 1 or height < 1 or width > 4096 or height > 4096:
                raise fail("PNEWBUF dimensions are invalid")
            self.pages[register] = Raster(width, height, 0, 0,
                                          bytes((self.r.fg,)) * (width * height),
                                          tuple(self.r.palette))
            self.page_positions.pop(register, None)
        elif op == "psave":
            if len(a) < 2:
                raise fail("PSAVE requires a filename and page buffer")
            register = self.ivalue(a[1])
            if register not in self.pages and register not in self.freed_pages:
                raise fail(f"PSAVE buffer {register} is not loaded")
            # PSAVE serializes a page to the host filesystem. The saved member
            # is not part of the immutable input presentation and does not
            # alter pixels, palette, timing, or later commands in this profile.
        elif op == "position":
            if len(a) < 3: raise fail("POSITION requires a buffer and x,y")
            register = self.ivalue(a[0])
            image = self.pages.get(register) or self.clips.get(register)
            if image is None: raise fail(f"POSITION buffer {register} is not loaded")
            x, y = self.ivalue(a[1]), self.ivalue(a[2])
            if len(a) > 3 and a[3].casefold() == "r":
                old_x, old_y = self.page_positions.get(register, (image.xoff, image.yoff))
                x, y = old_x + x, old_y + y
            moved = Raster(image.width, image.height, x, y, image.pixels,
                           image.palette, image.packed_width, image.packed_pixels,
                           image.display_width, image.display_height)
            if register in self.pages:
                self.pages[register] = moved
                self.page_positions[register] = (x, y)
            else: self.clips[register] = moved
        elif op == "psetbuf":
            if a:
                if self.pset_context is not None:
                    raise fail("nested PSETBUF is invalid")
                register = self.ivalue(a[0])
                image = self.pages.get(register)
                if image is None and register in self.freed_pages:
                    image = self.freed_pages[register]
                    self.pages[register] = image
                    note = f"reused released page buffer {register} before its memory was overwritten"
                    if note not in self.recovery_notes:
                        self.recovery_notes.append(note)
                if image is None:
                    raise fail(f"PSETBUF page {register} is not loaded")
                self.pset_context = (register, self.r.width, self.r.height, self.r.colors,
                                     self.r.view_width, self.r.view_height,
                                     self.r.viewport_x, self.r.viewport_y,
                                     self.r.screen, self.r.palette, self.r.window,
                                     self.r.fg, self.r.bg)
                self.r.width, self.r.height = image.width, image.height
                self.r.view_width, self.r.view_height = image.width, image.height
                self.r.viewport_x = self.r.viewport_y = 0
                self.r.screen = bytearray(image.pixels)
                if image.palette is not None:
                    self.r.palette = list(image.palette) + [(0, 0, 0)] * (256 - len(image.palette))
                self.r.window = (0, 0, image.width - 1, image.height - 1)
            else:
                if self.pset_context is None:
                    raise fail("PSETBUF reset without an active picture buffer")
                (register, width, height, colors, view_width, view_height,
                 viewport_x, viewport_y, screen, palette, window, fg, bg) = self.pset_context
                source = self.pages[register]
                self.pages[register] = Raster(self.r.width, self.r.height, source.xoff, source.yoff,
                                               bytes(self.r.screen), source.palette,
                                               display_width=source.display_width,
                                               display_height=source.display_height)
                self.r.width, self.r.height, self.r.colors = width, height, colors
                self.r.view_width, self.r.view_height = view_width, view_height
                self.r.viewport_x, self.r.viewport_y = viewport_x, viewport_y
                self.r.screen, self.r.palette, self.r.window = screen, palette, window
                self.r.fg, self.r.bg = fg, bg
                self.pset_context = None
        elif op == "putdff":
            if not a: raise fail("PUTDFF requires a buffer")
            register = self.ivalue(a[0])
            dff = self.dffs[register]
            delay = self.ivalue(a[1]) if len(a) > 1 else 0
            start = self.ivalue(a[2]) if len(a) > 2 else 0
            end = self.ivalue(a[3]) if len(a) > 3 else len(dff.frames) - 1
            x, y = self.xy(a[4], a[5]) if len(a) > 5 else (0, 0)
            # The command language uses a deliberately oversized value (99 is
            # conventional) as its LAST sentinel in either direction.
            last = len(dff.frames) - 1
            start = min(max(0, start), last)
            end = min(max(0, end), last)
            step = 1 if end >= start else -1
            for index in range(start, end + step, step):
                self.dff_frame(register, index, x, y)
                default_delay = dff.delay if isinstance(dff, Flic) else 100 / FPS
                self.writer.delay(delay if delay > 0 else default_delay)
        elif op == "fload":
            if not a: raise fail("FLOAD requires a resource")
            requested = self.resource_name(a[0])
            register = self.ivalue(a[1]) if len(a) > 1 else 1
            try:
                key = resource_key(self.assets, requested, (".set", ".fnt"))
                self.fonts[register] = self.assets.fonts[key]
            except (GraspError, KeyError):
                self.fonts[register] = self.fonts[0]
                note = f"font resource {requested!r} is absent or damaged; resident font substituted"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
            self.r.font = self.fonts[register]
            if len(a) == 1:
                self.fonts[self.named_register(requested)] = self.fonts[register]
            self.font_names[requested.casefold()] = register
            self.font_names[Path(requested).stem.casefold()] = register
            self.r.char_gap = self.r.font.char_gap
            self.r.space_gap = self.r.font.space_gap
            self.r.line_gap = self.r.font.line_gap
        elif op == "font":
            if not a:
                register = 0
            else:
                selected = self.value(a[0])
                if isinstance(selected, str) and not re.fullmatch(r"[-+]?\d+", selected):
                    key = selected.casefold()
                    if key not in self.font_names:
                        resource = resource_key(self.assets, selected, (".set", ".fnt"))
                        register = max(self.fonts, default=0) + 1
                        self.fonts[register] = self.assets.fonts[resource]
                        self.font_names[key] = register
                        self.font_names[Path(key).stem] = register
                    register = self.font_names[key]
                else:
                    register = int(selected)
            if register not in self.fonts:
                note = f"FONT buffer {register} was not loaded; resident font substituted"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
                register = 0
            self.r.font = self.fonts[register]
            self.r.char_gap, self.r.space_gap, self.r.line_gap = (
                self.r.font.char_gap, self.r.font.space_gap, self.r.font.line_gap)
        elif op == "ffree":
            for register in integer_range(a or ("1",), self.ivalue):
                if register: self.fonts.pop(register, None)
            self.r.font = self.fonts.get(0, default_font())
        elif op == "fgaps":
            if not a:
                self.r.char_gap, self.r.space_gap, self.r.line_gap = (
                    self.r.font.char_gap, self.r.font.space_gap, self.r.font.line_gap)
            else:
                self.r.char_gap = self.ivalue(a[0])
                if len(a) > 1: self.r.space_gap = self.ivalue(a[1])
                if len(a) > 2: self.r.line_gap = self.ivalue(a[2])
        elif op == "fstyle":
            self.r.font_style = self.ivalue(a[0]) if a else 0
            if self.r.font_style < 0 or self.r.font_style > 8:
                raise fail("FSTYLE direction is outside 0..8")
            if len(a) > 1:
                self.r.font_offset_x = abs(self.ivalue(a[1]))
                self.r.font_offset_y = abs(self.ivalue(a[2])) if len(a) > 2 else self.r.font_offset_x
        elif op == "text":
            if not a: raise fail("TEXT requires arguments")
            if len(a) == 1:
                text, delay = self.string(a[0]), 0
                self.flowing_text(text)
            elif len(a) == 2:
                text, delay = self.string(a[0]), float(self.value(a[1]))
                self.flowing_text(text)
            elif len(a) >= 3:
                text = self.string(a[2])
                if self.text_mode is not None:
                    delay = 0
                    column, row = self.ivalue(a[0]), self.ivalue(a[1])
                    self.r.draw_text_mode(column, row, text)
                    self.text_x, self.text_y = (column + len(text)) * 8, row * 16
                else:
                    delay = float(self.value(a[3])) if len(a) > 3 else 0
                    x, y = self.xy(a[0], a[1])
                    self.text_x, self.text_y = x, y
                    self.flowing_text(text)
            else: raise fail("TEXT requires a string or x, y, string")
            if delay > 0: self.writer.delay(delay)
        elif op in ("fly", "float"):
            if len(a) < 7: raise fail(f"{op.upper()} requires coordinates, step, delay, and clips")
            xs, ys = self.xy(a[0], a[1]); xe, ye = self.xy(a[2], a[3])
            amount, delay = float(self.value(a[4])), float(self.value(a[5]))
            frames = integer_range(a[6:], self.ivalue)
            if not frames: raise fail(f"{op.upper()} has no clip sequence")
            distance = math.hypot(xe - xs, ye - ys)
            count = len(frames) if amount <= 0 or distance == 0 else max(1, int(math.ceil(distance / amount)) + 1)
            if op == "float" and self.float_background is not None:
                self.r.screen[:] = self.float_background
            background = bytes(self.r.screen)
            if op == "float":
                self.float_background = background
            for i in range(count):
                if op == "float": self.r.screen[:] = background
                t = 1 if count == 1 else i / (count - 1)
                x, y = round(xs + (xe - xs) * t), round(ys + (ye - ys) * t)
                self.put_clip(frames[i % len(frames)], x, y)
                self.writer.delay(delay if delay > 0 else 100 / FPS)
        elif op == "endfloat":
            if self.float_background is not None:
                self.r.screen[:] = self.float_background
                self.float_background = None
        elif op == "tran":
            if not a or a[0].casefold() == "off": self.r.transparent.clear()
            elif a[0].casefold() == "on": self.r.transparent = {self.ivalue(v) for v in a[1:]}
            else: raise fail("TRAN expects ON or OFF")
        elif op in ("wait", "waitkey"):
            duration = float(self.value(a[0])) if a else AUTO_WAIT
            if duration > 1000:
                duration = AUTO_WAIT
            if a and self.timer_frame is not None:
                elapsed = (self.writer.frames - self.timer_frame) * 100 / FPS
                duration = max(0.0, duration - elapsed)
            self.writer.delay(duration)
            if op == "waitkey" and not a:
                if self.pc < len(self.program.code) and self.program.code[self.pc].op == "getkey":
                    variable = self.program.code[self.pc].args[0] if self.program.code[self.pc].args else "key"
                    self.pending_key = self.choose_typed_value(variable, self.pc)
                else:
                    self.pending_key = self.choose_key(self.pc)
        elif op == "getkey":
            if len(a) != 1: raise fail("GETKEY requires one variable")
            if self.pending_key is None:
                # GETKEY polls; WAITKEY is the blocking command. With no
                # pending synthesized WAITKEY event, the DOS runtime returns
                # an empty string.
                self.pending_key = ""
            self.variables[a[0].casefold()] = self.pending_key
            self.pending_key = None
        elif op == "getmouse":
            if len(a) < 3: raise fail("GETMOUSE requires button, x, and y variables")
            self.variables[a[0].casefold()] = 0
            self.variables[a[1].casefold()] = self.mouse_x
            self.variables[a[2].casefold()] = self.mouse_y
        elif op == "ifkey":
            if self.pending_key is None:
                self.pending_key = self.choose_key(self.pc - 1)
            selected = str(self.pending_key).casefold()
            for key, label in zip(a[0::2], a[1::2]):
                if selected == key.casefold():
                    self.pending_key = None
                    self.allow_navigation_return = True
                    if label.casefold() in self.program.labels:
                        self.jump(label)
                    elif label.casefold() in SUPPORTED_COMMANDS:
                        if self.execute(Instruction(label.casefold(), (), inst.line, inst.raw)):
                            return True
                    else:
                        raise fail(f"unknown label {label.casefold()!r}")
                    break
        elif op == "ifmouse":
            if not a:
                raise fail("IFMOUSE requires a button")
            if len(a) == 1 or re.fullmatch(r"[-+]?\d+", a[1]):
                self.writer.delay(AUTO_WAIT)
                return False
            if self.pending_mouse is None:
                self.pending_mouse = self.choose_mouse_target(self.pc - 1)
                self.writer.delay(AUTO_WAIT)
            if self.synthetic_actions > 24:
                return True
            if self.pending_mouse and a[1].casefold() == self.pending_mouse.casefold():
                target = self.pending_mouse
                self.pending_mouse = None
                self.allow_navigation_return = True
                self.jump(target)
        elif op in ("ifmem", "ifvideo"):
            if not a: raise fail(f"{op.upper()} requires a test value")
            if op == "ifmem":
                condition = self.ivalue(a[0]) <= 640 * 1024
            else:
                requested = self.string(a[0]).casefold()
                condition = requested in MODE_INFO or requested in ("0", "1", "2")
            if len(a) > 1:
                if condition: self.jump(a[1])
            elif not condition:
                self.skip_false_block()
        elif op == "mouse":
            if len(a) >= 3 and a[0].casefold() == "position":
                self.mouse_x, self.mouse_y = self.ivalue(a[1]), self.ivalue(a[2])
            # Cursor shape, range, sensitivity, and visibility do not alter
            # captured framebuffer pixels until input is synthesized.
        elif op == "cursor":
            # The hardware text cursor lives outside video RAM and is not
            # present in a framebuffer capture.
            pass
        elif op == "when":
            # WHEN installs asynchronous input handlers. A finite conversion
            # follows the normal no-key path; WAITKEY/IFKEY synthesize their
            # own deterministic input when the program explicitly blocks.
            pass
        elif op == "timer":
            self.timer_frame = self.writer.frames
        elif op == "data":
            self.data_values, self.data_index, self.data_overread = a, 0, 0
        elif op == "dataskip":
            if len(a) != 1: raise fail("DATASKIP requires one displacement")
            destination = self.data_index + self.ivalue(a[0])
            if destination < 0 or destination > len(self.data_values):
                raise fail("DATASKIP moves beyond the active data list")
            self.data_index = destination
        elif op == "offset":
            if len(a) < 2: raise fail("OFFSET requires x and y")
            x, y = self.ivalue(a[0]), self.ivalue(a[1])
            if len(a) > 2 and a[2].casefold() == "r":
                self.offset_x += x; self.offset_y += y
            else:
                self.offset_x, self.offset_y = x, y
        elif op == "mark":
            count = self.ivalue(a[0]) if a else 1
            if count < 0: raise fail("MARK count must not be negative")
            if count == 0:
                depth = 1
                while self.pc < len(self.program.code) and depth:
                    probe = self.program.code[self.pc]
                    if probe.op == "mark": depth += 1
                    elif probe.op == "loop": depth -= 1
                    self.pc += 1
                return False
            self.loops.append([self.pc, count])
        elif op == "loop":
            if not self.loops: raise fail("LOOP without MARK")
            if self.pc == len(self.program.code) and self.loops[-1][0] <= 2:
                self.loops.pop(); return True
            self.loops[-1][1] -= 1
            if self.loops[-1][1] > 0: self.pc = self.loops[-1][0]
            else: self.loops.pop()
        elif op == "break":
            if self.loops:
                self.loops.pop()
            if a:
                self.jump(a[0])
        elif op == "merge":
            if not a: raise fail("MERGE requires a TXT module")
            requested = self.string(a[0]).casefold()
            module = (self.program_aliases.get(requested)
                      or self.program_aliases.get(Path(requested).stem))
            if module is None:
                raise fail(f"MERGE module {a[0]!r} is not embedded in this GL")
            merged = self.merged_programs.setdefault(self.program.name.casefold(), [])
            if module not in merged:
                merged.append(module)
        elif op in ("goto", "gosub", "call", "link"):
            if not a: raise fail(f"{op.upper()} requires a label")
            target = a[0]
            resolved = self.string(target).casefold()
            if op in ("call", "link"):
                module = (self.program_aliases.get(resolved)
                          or self.program_aliases.get(Path(resolved).stem))
                if module is not None and module is not self.program:
                    start, subroutine, arguments = 0, None, a[1:]
                    if len(a) > 1:
                        candidate = self.string(a[1]).casefold()
                        if candidate in module.labels:
                            start, subroutine, arguments = module.labels[candidate], candidate, a[2:]
                    if op == "link":
                        if module.name.casefold() in self.linked_program_visits:
                            return True
                        self.linked_program_visits.add(module.name.casefold())
                        self.link_module(module, start, arguments, subroutine)
                        return False
                    active = {self.program.name.casefold()}
                    active.update(saved[0].name.casefold() for saved in self.module_stack)
                    if module.name.casefold() in active:
                        return True
                    self.enter_module(module, start, arguments, subroutine)
                    return False
            destination = self.program.labels.get(resolved)
            destination_program = self.program
            arguments = a[1:]
            if destination is None and op in ("gosub", "call"):
                for merged in reversed(self.merged_programs.get(self.program.name.casefold(), [])):
                    if resolved in merged.labels:
                        destination, destination_program = merged.labels[resolved], merged
                        break
            if destination is None:
                if op in ("call", "link"):
                    module = self.program_aliases.get(resolved) or self.program_aliases.get(Path(resolved).stem)
                    if module is None:
                        note = f"{op.upper()} module {target!r} is not embedded in this GL; skipped"
                        if note not in self.recovery_notes:
                            self.recovery_notes.append(note)
                        return op == "link"
                    start, subroutine = 0, None
                    arguments = a[1:]
                    if len(a) > 1:
                        candidate = self.string(a[1]).casefold()
                        if candidate in module.labels:
                            start, subroutine, arguments = module.labels[candidate], candidate, a[2:]
                    if op == "link":
                        if module.name.casefold() in self.linked_program_visits:
                            return True
                        self.linked_program_visits.add(module.name.casefold())
                        self.link_module(module, start, arguments, subroutine)
                        return False
                    active = {self.program.name.casefold()}
                    active.update(saved[0].name.casefold() for saved in self.module_stack)
                    if module.name.casefold() in active:
                        return True
                    self.enter_module(module, start, arguments, subroutine)
                    return False
                raise fail(f"unknown label {target!r}")
            if destination_program is not self.program:
                self.enter_module(destination_program, destination, arguments, resolved)
                return False
            # An endlessly looping presentation maps to one complete traversal in
            # a finite video. Backward IF branches and MARK/LOOP remain functional.
            if op == "goto" and destination < self.pc and self.stop_after_navigation:
                self.stop_after_navigation = False
                return True
            if op == "goto" and destination < self.pc and not self.calls and not self.module_stack:
                if self.allow_navigation_return:
                    self.allow_navigation_return = False
                else:
                    loop_ops = {item.op for item in self.program.code[destination:self.pc]}
                    if "cycle" not in loop_ops:
                        return True
                    identity = (self.program.name.casefold(), destination)
                    signature = tuple(sorted((name, repr(value))
                                             for name, value in self.variables.items()))
                    first_frame, previous = self.color_loop_states.get(
                        identity, (self.writer.frames, signature))
                    elapsed = self.writer.frames - first_frame
                    # A stable palette-only loop gets a representative five
                    # seconds. Variable-controlled color loops may reach their
                    # own exit, with a ten-second ceiling for damaged sources.
                    if (signature == previous and elapsed >= 5 * FPS) or elapsed >= 10 * FPS:
                        return True
                    self.color_loop_states[identity] = (first_frame, signature)
            if op in ("gosub", "call", "link"):
                self.push_call(self.pc, resolved, arguments)
            self.pc = destination
        elif op == "return":
            result = self.value(a[0]) if a else 0
            if self.calls:
                self.pop_call(result)
            elif self.module_stack:
                self.variables["0"] = result
                self.leave_module()
            else:
                if self.writer.frames or any(self.r.screen):
                    return True
                raise fail("RETURN without GOSUB")
        elif op == "if":
            if not a: raise fail("IF requires an expression")
            if len(a) >= 2:
                condition = bool(self.value(a[0]))
                if condition: self.jump(a[1])
            else:
                condition = bool(self.value(a[0]))
                if not condition:
                    self.skip_false_block()
        elif op == "else":
            depth = 1
            while self.pc < len(self.program.code) and depth:
                probe = self.program.code[self.pc]
                if probe.op in ("if", "ifmem", "ifvideo") and len(probe.args) == 1: depth += 1
                elif probe.op == "endif": depth -= 1
                self.pc += 1
        elif op == "endif":
            pass
        elif op in ("set", "global", "local"):
            if not a: raise fail(f"{op.upper()} requires a name")
            assignments: list[tuple[str, str]]
            if len(a) >= 4 and len(a) % 2 == 0 \
                    and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.@-]*", a[index])
                            for index in range(0, len(a), 2)):
                assignments = [(a[index], a[index + 1])
                               for index in range(0, len(a), 2)]
            else:
                assignments = [(a[0], "".join(a[1:]) if len(a) > 1 else "on")]
            for raw_name, expression in assignments:
                name = self.variable_name(raw_name)
                if op == "local" and self.calls and name not in self.calls[-1].saved_locals:
                    self.calls[-1].saved_locals[name] = self.variables.get(name, _UNSET)
                elif op == "local" and self.module_local_scopes \
                        and name not in self.module_local_scopes[-1]:
                    self.module_local_scopes[-1][name] = self.variables.get(name, _UNSET)
                if name == "center":
                    enabled = expression.casefold() == "on"
                    self.r.center, self.r.right = enabled, False
                    self.variables["center"] = int(enabled)
                    self.variables["right"] = 0
                    self.variables["left"] = int(not enabled)
                elif name == "right":
                    enabled = expression.casefold() == "on"
                    self.r.right, self.r.center = enabled, False
                    self.variables["right"] = int(enabled)
                    self.variables["center"] = 0
                    self.variables["left"] = int(not enabled)
                elif name == "left":
                    enabled = expression.casefold() == "on"
                    if enabled:
                        self.r.center = self.r.right = False
                    self.variables["left"] = int(enabled)
                    if enabled:
                        self.variables["center"] = self.variables["right"] = 0
                elif name in ("retrace", "space", "esc", "abort"):
                    pass
                else:
                    self.variables[name] = self.value(expression)
        elif op == "chgcolor":
            index, register = self.ivalue(a[0]), self.ivalue(a[1])
            self.r.palette[index & 255] = ega_register(register & 63)
        elif op == "setcolor":
            for index, register in enumerate(integer_range(a, self.ivalue)[:16]):
                self.r.palette[index] = ega_register(register & 63)
        elif op == "setrgb":
            if len(a) < 4: raise fail("SETRGB requires index, red, green, blue")
            index = self.ivalue(a[0]) & 255
            dac = [self.ivalue(v) for v in a[1:4]]
            if any(value < 0 or value > 63 for value in dac):
                raise fail("SETRGB components must be in the VGA DAC range 0..63")
            relative = len(a) > 4 and a[4].casefold() == "r"
            range_at = 5 if relative else 4
            count = self.ivalue(a[range_at]) if len(a) > range_at else 1
            if count < 1 or index + count > 256:
                raise fail("SETRGB range exceeds the 256-entry palette")
            if relative:
                # The starting entry is unchanged; RGB values are increments
                # used to derive the remaining entries in the inclusive range.
                base = self.r.palette[index]
                increments = [value * 255 // 63 for value in dac]
                for offset in range(1, count):
                    self.r.palette[index + offset] = tuple(
                        min(255, base[channel] + increments[channel] * offset)
                        for channel in range(3))
            else:
                color = tuple(value * 255 // 63 for value in dac)
                for offset in range(count):
                    self.r.palette[index + offset] = color
        elif op == "spread":
            if not a: raise fail("SPREAD requires a destination palette")
            if len(a) == 1:
                source_palette = tuple(self.r.palette)
                target_register, steps = self.ivalue(a[0]), 64
            else:
                source_register, target_register = self.ivalue(a[0]), self.ivalue(a[1])
                if source_register == 0:
                    source_palette = tuple(self.r.palette)
                else:
                    source = self.pages.get(source_register) or self.freed_pages.get(source_register)
                    if source is None or source.palette is None:
                        raise fail(f"SPREAD source palette {source_register} is unavailable")
                    source_palette = source.palette
                    self.r.install_palette(source_palette)
                steps = self.ivalue(a[2]) if len(a) > 2 else 64
            target = self.pages.get(target_register) or self.freed_pages.get(target_register)
            if target is None or target.palette is None:
                raise fail(f"SPREAD destination palette {target_register} is unavailable")
            source_palette = tuple(source_palette) + tuple(self.r.palette[len(source_palette):])
            target_palette = tuple(target.palette) + tuple(self.r.palette[len(target.palette):])
            repeats = abs(steps) if steps < 0 else 1
            count = 64 if steps <= 0 else steps
            for step in range(1, count + 1):
                for index, (c1, c2) in enumerate(zip(source_palette, target_palette)):
                    self.r.palette[index] = tuple(c1[k] + (c2[k] - c1[k]) * step // count
                                                  for k in range(3))
                for _ in range(repeats):
                    self.writer.frame()
        elif op == "mode":
            if not a: raise fail("MODE requires a border color")
            border = self.ivalue(a[0]) & 15
            selection = self.ivalue(a[1]) if len(a) > 1 else 0
            if selection < 0 or selection >= 6:
                raise fail("CGA MODE palette selection is outside 0..5")
            self.r.palette[0] = EGA16[border]
            for index in range(1, 4):
                self.r.palette[index] = EGA16[CGA_PALETTE_REGISTERS[index - 1][selection]]
        elif op in ("noise", "note"):
            if len(a) < 3: raise fail(f"{op.upper()} requires three values")
            start, end, duration = float(self.value(a[0])), float(self.value(a[1])), float(self.value(a[2]))
            if op == "note":
                if (self.program.name.casefold(), self.pc - 1) in self.silent_chime_notes:
                    self.writer.delay(duration)
                    return False
                # NOTE supplies the two factors of the 8253 timer divisor.
                divisor = max(1.0, start * end)
                start = end = 1_193_180.0 / divisor
            self.writer.delay(duration, max(1, start), max(1, end))
        elif op == "pan":
            relative_at = next((i for i, value in enumerate(a) if value.casefold() == "r"), -1)
            if relative_at >= 0:
                if relative_at != 2: raise fail("relative PAN expects x,y,R")
                x1, y1 = self.r.viewport_x, self.r.viewport_y
                x2, y2 = x1 + self.ivalue(a[0]), y1 + self.ivalue(a[1])
            elif len(a) >= 4:
                x1, y1, x2, y2 = (self.ivalue(v) for v in a[:4])
            else:
                raise fail("PAN requires x,y,R or start/end coordinates")
            maximum_x = max(0, self.r.width - self.r.view_width)
            maximum_y = max(0, self.r.height - self.r.view_height)
            x1, x2 = max(0, min(maximum_x, x1)), max(0, min(maximum_x, x2))
            y1, y2 = max(0, min(maximum_y, y1)), max(0, min(maximum_y, y2))
            distance = max(abs(x2 - x1), abs(y2 - y1))
            frames = min(60, max(1, distance)) if distance else 0
            for step in range(1, frames + 1):
                self.r.viewport_x = round(x1 + (x2 - x1) * step / frames)
                self.r.viewport_y = round(y1 + (y2 - y1) * step / frames)
                self.writer.frame()
            self.r.viewport_x, self.r.viewport_y = x2, y2
        elif op == "setupscr":
            if len(a) == 1:
                selected = self.value(a[0])
                if not isinstance(selected, str) or re.fullmatch(r"[-+]?\d+", selected):
                    register = int(selected)
                    image = self.pages.get(register)
                    if image is None:
                        raise fail(f"SETUPSCR page {register} is not loaded")
                else:
                    image = self.raster(a[0], (".pic", ".pcx", ".pcc", ".gif", ".clp"))
                width, height = image.width, image.height
            elif len(a) >= 2:
                width, height = self.ivalue(a[0]), self.ivalue(a[1])
            else:
                raise fail("SETUPSCR requires a raster or width,height")
            if width < self.r.view_width or height < self.r.view_height or width > 4096 or height > 4096:
                raise fail("SETUPSCR virtual dimensions are invalid")
            self.r.width, self.r.height = width, height
            self.r.screen = bytearray(bytes((self.r.fg,)) * (width * height))
            self.r.viewport_x = self.r.viewport_y = 0
            self.r.window = (0, 0, width - 1, height - 1)
        elif op == "resetscr":
            width, height = self.r.view_width, self.r.view_height
            cropped = bytearray(width * height)
            for row in range(height):
                source = (self.r.viewport_y + row) * self.r.width + self.r.viewport_x
                cropped[row * width:(row + 1) * width] = self.r.screen[source:source + width]
            self.r.width, self.r.height = width, height
            self.r.screen = cropped
            self.r.viewport_x = self.r.viewport_y = 0
            self.r.window = (0, 0, width - 1, height - 1)
        elif op == "databegin":
            if not a: raise fail("inline DATABEGIN is unsupported by this parser")
            label = a[0].casefold()
            if label not in self.program.data_blocks:
                raise fail(f"unknown data block {label!r}")
            self.data_values = self.program.data_blocks[label]
            self.data_index = 0
            self.data_overread = 0
        elif op == "edge":
            if not a or a[0].casefold() == "off": self.r.edge_color = None
            elif a[0].casefold() == "on": self.r.edge_color = self.ivalue(a[1]) & 255 if len(a) > 1 else self.r.fg
            else: raise fail("EDGE expects ON or OFF")
        elif op == "opengl":
            if not a: raise fail("OPENGL requires a library name")
            # Packaged GLs commonly retain OPENGL as a namespace hint even
            # after the linker has embedded the referenced resources. Resource
            # lookup remains exact over the already validated member directory.
            self.open_gl = self.string(a[0]).casefold()
        elif op == "closegl":
            self.open_gl = None
        elif op == "resetgl":
            self.open_gl = None
        elif op == "setpage":
            if len(a) < 2: raise fail("SETPAGE requires view and drawing pages")
            view, draw = self.ivalue(a[0]), self.ivalue(a[1])
            pages = self.r.pages
            if self.r.view_screen is None:
                pages.setdefault(view, bytearray(self.r.screen))
            else:
                pages[view] = self.r.view_screen
            pages.setdefault(draw, bytearray(self.r.screen) if draw == view
                             else bytearray(self.r.width * self.r.height))
            if view == draw:
                self.r.screen = pages[draw]
                self.r.view_screen = None
            else:
                self.r.view_screen = pages[view]
                self.r.screen = pages[draw]
        elif op == "revpage":
            if self.r.view_screen is None:
                # GRASP starts graphics modes with two hardware pages when the
                # adapter has enough memory; presentations may REVPAGE before
                # an explicit SETPAGE. Materialize that identical second page
                # on first use.
                self.r.view_screen = bytearray(self.r.screen)
            self.r.screen, self.r.view_screen = self.r.view_screen, self.r.screen
            self.writer.frame()
        elif op == "int":
            if not a:
                raise fail("INT requires an interrupt number")
            if len(a) > 9:
                raise fail("INT accepts one interrupt and eight register values")
            interrupt = self.ivalue(a[0]) & 255
            names = ("ax", "bx", "cx", "dx", "si", "di", "ds", "es")
            registers = {name: 0 for name in names}
            for name, token in zip(names, a[1:]):
                if not token:
                    continue
                pointer = re.fullmatch(r"(?i)(?:ofs|seg)\((.*)\)", token)
                registers[name] = 0 if pointer else self.ivalue(token) & 0xffff
            flags = 0
            if interrupt == 0x21 and (registers["ax"] >> 8) == 0x3d:
                # DOS OPEN is used by self-running presentations to probe for
                # an optional adjacent library. A standalone GL has no such
                # external DOS namespace, so return the exact FILE NOT FOUND
                # result (CF set, AX=2) and let its own fallback path execute.
                registers["ax"], flags = 2, 1
            else:
                raise fail(f"INT {interrupt:#04x} service {registers['ax']:#06x} requires an external DOS host")
            self.variables.update(registers)
            self.variables["0"] = flags
        elif op == "exec":
            if not a: raise fail("EXEC requires a COM member")
            try:
                self.execute_com(a[0])
            except GraspError as exc:
                if "is not present" not in str(exc):
                    raise
                note = f"external EXEC {self.string(a[0])!r} is absent; hardware helper skipped"
                if note not in self.recovery_notes:
                    self.recovery_notes.append(note)
        elif op == "exit":
            return self.leave_module()
        else:
            raise fail(f"unsupported command {op!r}")
        return False


def select_entry_program(input_path: Path, programs: tuple[Program, ...]) -> Program:
    programs = tuple(program for program in programs if program.code)
    if not programs:
        raise fail("GL library contains no executable TXT presentation")
    wanted = input_path.stem.casefold()
    matching = [program for program in programs
                if Path(program.name).stem.casefold() == wanted]
    if matching:
        return matching[0]

    aliases: dict[str, Program] = {}
    for program in programs:
        aliases[program.name.casefold()] = program
        aliases.setdefault(Path(program.name).stem.casefold(), program)
    edges: dict[str, set[str]] = {program.name.casefold(): set() for program in programs}
    incoming: dict[str, set[str]] = {program.name.casefold(): set() for program in programs}
    for program in programs:
        source = program.name.casefold()
        for instruction in program.code:
            if instruction.op not in ("call", "link") or not instruction.args:
                continue
            raw = instruction.args[0].casefold()
            if any(marker in raw for marker in ("@", "$", "(", ")")):
                continue
            target = aliases.get(raw) or aliases.get(Path(raw).stem)
            if target is None or target is program:
                continue
            destination = target.name.casefold()
            edges[source].add(destination)
            incoming[destination].add(source)

    roots = [program for program in programs if not incoming[program.name.casefold()]]
    if len(roots) == 1:
        return roots[0]

    def reach(program: Program) -> int:
        seen: set[str] = set()
        pending = list(edges[program.name.casefold()])
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            pending.extend(edges[name] - seen)
        return len(seen)

    candidates = roots or list(programs)
    scores = [(reach(program), program) for program in candidates]
    best = max(score for score, _ in scores)
    winners = [program for score, program in scores if score == best]
    return winners[0] if len(winners) == 1 else programs[0]


def convert(input_path: Path, output_path: Path) -> str | None:
    # Parse and decode every member before creating even a temporary encoder stream.
    library = parse_library(input_path)
    assets = load_assets(library)
    if not assets.programs:
        raise fail("GL library contains no executable TXT presentation")
    parsed: list[Program] = []
    parse_errors: list[str] = []
    for name, payload in assets.programs:
        try:
            parsed.append(parse_program(name, payload))
        except (GraspError, UnicodeDecodeError) as exc:
            parse_errors.append(f"{name}: {exc}")
    programs = tuple(parsed)
    if not programs:
        detail = f": {'; '.join(parse_errors)}" if parse_errors else ""
        raise fail(f"GL library contains no decodable TXT presentation{detail}")
    # Linked libraries often alphabetize members, so directory order can put a
    # callable submodule before the presentation root. Prefer an exact GL/TXT
    # stem match, then the unique embedded call-graph root (or widest unique
    # root); only an irreducibly ambiguous library falls back to directory order.
    program = select_entry_program(input_path, programs)
    validate_program(program)
    renderer = Renderer()
    writer = MovieWriter(output_path, renderer)
    interpreter = Interpreter(assets, programs, program, writer)
    try:
        interpreter.run()
        writer.finish()
        return "; ".join(interpreter.recovery_notes) or None
    except GraspError as exc:
        # Preserve a presentation that reached valid visible output before a
        # damaged late resource or source command. Container/header failures
        # and errors before any visible rendering still fail without output.
        if writer.frames == 0 and any(renderer.screen):
            writer.frame()
        if writer.frames:
            try:
                writer.finish()
            except BaseException:
                writer.abort()
                raise
            return str(exc)
        writer.abort()
        raise
    except BaseException:
        writer.abort()
        raise


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="grasp.py",
        description="Natively decode a GRASP GL animation into a lossless FFV1 AVI.")
    parser.add_argument("inputFile", type=Path)
    parser.add_argument("outputFile", type=Path)
    args = parser.parse_args(argv)
    try:
        recovery = convert(args.inputFile, args.outputFile)
    except GraspError as exc:
        print(f"grasp.py: error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("grasp.py: interrupted", file=sys.stderr)
        return 130
    if recovery:
        print(f"grasp.py: warning: recovery applied: {recovery}",
              file=sys.stderr)
    print(f"Converted {args.inputFile} -> {args.outputFile}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

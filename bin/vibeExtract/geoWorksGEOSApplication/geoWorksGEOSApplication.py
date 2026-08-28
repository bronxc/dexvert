#!/usr/bin/env python3
# Vibe coded by Codex
"""Extract resources from PC/GEOS 2.x executable geode files."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import stat
import struct
import sys
import tempfile
from typing import Any, Optional
import zlib


SIGNATURE = b"\xc7\x45\xc1\x53"
COMMON_HEADER_SIZE = 256
GEODE_HEADER_SIZE = 344
IMPORTED_LIBRARY_ENTRY_SIZE = 14
EXPORTED_ENTRY_SIZE = 4
RESOURCE_DESCRIPTOR_SIZE = 10

GEOS_FILE_TYPES = {
    0: "not a GEOS file",
    1: "executable",
    2: "VM file",
    3: "byte-stream data",
    4: "directory information",
    5: "old PC/GEOS 1.x VM file",
}

GEODE_TYPE_NAMES = {
    1: "application search category",
    2: "library search category",
    3: "driver search category",
    4: "loader search category",
}

FILE_HEADER_FLAGS = {
    0x8000: "template",
    0x4000: "shared-multiple",
    0x2000: "shared-single",
    0x0800: "hidden",
    0x0400: "DBCS",
    0x0200: "unread",
    0x0100: "associated-notes",
}

GEODE_ATTRIBUTES = {
    0x8000: "process",
    0x4000: "library",
    0x2000: "driver",
    0x1000: "keep-file-open",
    0x0800: "system",
    0x0400: "multi-launchable",
    0x0200: "application",
    0x0100: "driver-initialized",
    0x0080: "library-initialized",
    0x0040: "geode-initialized",
    0x0020: "uses-coprocessor",
    0x0010: "requires-coprocessor",
    0x0008: "general-consumer-mode",
    0x0004: "C-entry-points",
    0x0002: "execute-in-place",
}

RESOURCE_FLAGS = {
    0x0001: "memory-swapped",
    0x0002: "discarded",
    0x0004: "debug",
    0x0008: "LMem",
    0x0010: "swapable",
    0x0020: "discardable",
    0x0040: "shared",
    0x0080: "fixed",
    0x0100: "conforming",
    0x0200: "code",
    0x0400: "object",
    0x0800: "read-only",
    0x1000: "UI",
    0x2000: "no-error",
    0x4000: "lock",
    0x8000: "zero-initialize",
}

RELOCATION_SOURCES = {
    0: "kernel",
    1: "imported-library",
    2: "geode-resource",
}

RELOCATION_TYPES = {
    0: "far-pointer",
    1: "offset",
    2: "segment",
    3: "handle",
    4: "call",
    5: "last-XIP-handle",
}

LMEM_TYPE_NAMES = {
    0: "general",
    1: "window",
    2: "object-block",
    3: "graphics-state",
    4: "font-block",
    5: "graphics-string",
    6: "database-items",
}

BITMAP_FORMAT_NAMES = {
    0: "monochrome",
    1: "4-bit indexed",
    2: "8-bit indexed",
    3: "24-bit RGB",
    4: "4-plane CMYK",
    5: "3-plane CMY",
}

BITMAP_COMPACTION_NAMES = {
    0: "uncompressed",
    1: "PackBits",
    2: "LZG",
}

GR_FILL_BITMAP = 76
GR_FILL_BITMAP_CP = 77
GR_DRAW_BITMAP = 80
GR_DRAW_BITMAP_CP = 81
INLINE_BITMAP_OPCODES = {
    GR_FILL_BITMAP,
    GR_FILL_BITMAP_CP,
    GR_DRAW_BITMAP,
    GR_DRAW_BITMAP_CP,
}


class UnsupportedFormat(Exception):
    """The input is not the supported PC/GEOS 2.x executable format."""


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def u16(data: bytes, offset: int) -> Optional[int]:
    if offset < 0 or offset + 2 > len(data):
        return None
    return struct.unpack_from("<H", data, offset)[0]


def u32(data: bytes, offset: int) -> Optional[int]:
    if offset < 0 or offset + 4 > len(data):
        return None
    return struct.unpack_from("<I", data, offset)[0]


def available_slice(data: bytes, offset: int, size: int) -> bytes:
    if offset < 0 or size <= 0 or offset >= len(data):
        return b""
    return data[offset:min(len(data), offset + size)]


def fixed_raw(data: bytes, offset: int, size: int) -> bytes:
    return available_slice(data, offset, size)


def decode_fixed(raw: bytes, dbcs: bool = False) -> str:
    if dbcs:
        even = len(raw) - (len(raw) % 2)
        words = raw[:even]
        terminator = None
        for index in range(0, len(words), 2):
            if words[index:index + 2] == b"\0\0":
                terminator = index
                break
        if terminator is not None:
            words = words[:terminator]
        return words.decode("utf-16le", errors="replace")
    # The PC/GEOS Extended BSW single-byte character set follows the classic
    # Macintosh Roman byte assignments for its printable high half.
    return raw.split(b"\0", 1)[0].decode("mac_roman", errors="replace")


def decode_ascii_fixed(raw: bytes) -> str:
    return raw.split(b"\0", 1)[0].decode("ascii", errors="replace").rstrip(" ")


def named_bits(value: Optional[int], definitions: dict[int, str]) -> dict[str, Any]:
    if value is None:
        return {"value": None, "names": [], "unknown_bits": None}
    known_mask = 0
    names = []
    for mask, name in definitions.items():
        known_mask |= mask
        if value & mask:
            names.append(name)
    return {
        "value": value,
        "hex": f"0x{value:04x}",
        "names": names,
        "unknown_bits": value & ~known_mask & 0xFFFF,
    }


def release_at(data: bytes, offset: int) -> Optional[dict[str, int | str]]:
    if offset + 8 > len(data):
        return None
    major, minor, change, engineering = struct.unpack_from("<4H", data, offset)
    return {
        "major": major,
        "minor": minor,
        "change": change,
        "engineering": engineering,
        "text": f"{major}.{minor}.{change}.{engineering}",
    }


def protocol_at(data: bytes, offset: int) -> Optional[dict[str, int | str]]:
    if offset + 4 > len(data):
        return None
    major, minor = struct.unpack_from("<2H", data, offset)
    return {"major": major, "minor": minor, "text": f"{major}.{minor}"}


def token_at(data: bytes, offset: int) -> Optional[dict[str, Any]]:
    if offset + 6 > len(data):
        return None
    chars = data[offset:offset + 4]
    manufacturer = struct.unpack_from("<H", data, offset + 4)[0]
    return {
        "chars": chars.decode("ascii", errors="replace"),
        "chars_raw_hex": chars.hex(),
        "manufacturer_id": manufacturer,
    }


def packed_timestamp(date_word: Optional[int], time_word: Optional[int]) -> dict[str, Any]:
    if date_word is None or time_word is None:
        return {"date_word": date_word, "time_word": time_word, "text": None, "valid": False}
    year = 1980 + ((date_word >> 9) & 0x7F)
    month = (date_word >> 5) & 0x0F
    day = date_word & 0x1F
    hour = (time_word >> 11) & 0x1F
    minute = (time_word >> 5) & 0x3F
    second = (time_word & 0x1F) * 2
    valid = 1 <= month <= 12 and 1 <= day <= 31 and hour <= 23 and minute <= 59 and second <= 59
    text = f"{year:04d}-{month:02d}-{day:02d}T{hour:02d}:{minute:02d}:{second:02d}" if valid else None
    return {
        "date_word": date_word,
        "time_word": time_word,
        "year": year,
        "month": month,
        "day": day,
        "hour": hour,
        "minute": minute,
        "second": second,
        "text": text,
        "valid": valid,
    }


def parse_relocations(
    relocation_bytes: bytes,
    declared_size: int,
    resource_bytes: bytes,
    resource_declared_size: int,
    import_count: int,
    resource_index: int,
    warnings: list[str],
) -> list[dict[str, Any]]:
    entries = []
    complete_size = len(relocation_bytes) - (len(relocation_bytes) % 4)
    for entry_offset in range(0, complete_size, 4):
        info, extra, target_offset = struct.unpack_from("<BBH", relocation_bytes, entry_offset)
        source = info >> 4
        relocation_type = info & 0x0F
        if source not in RELOCATION_SOURCES:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} has unknown source {source}"
            )
        if relocation_type not in RELOCATION_TYPES:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} has unknown type {relocation_type}"
            )
        if source == 1 and extra >= import_count:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} names missing import {extra}"
            )
        if source in (0, 2) and extra != 0:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} has nonzero reserved extra byte"
            )
        if target_offset >= resource_declared_size:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} target is outside the resource"
            )

        width = 4 if relocation_type == 0 else 2
        if relocation_type == 4:
            valid_target = target_offset >= 1 and target_offset + 4 <= resource_declared_size
        else:
            valid_target = target_offset + width <= resource_declared_size
        if not valid_target and target_offset < resource_declared_size:
            warnings.append(
                f"resource {resource_index}: relocation {entry_offset // 4} target is truncated at resource end"
            )

        target_word = None
        target_extra_word = None
        if target_offset + 2 <= len(resource_bytes):
            target_word = struct.unpack_from("<H", resource_bytes, target_offset)[0]
        if relocation_type in (0, 4) and target_offset + 4 <= len(resource_bytes):
            target_extra_word = struct.unpack_from("<H", resource_bytes, target_offset + 2)[0]

        entries.append({
            "index": entry_offset // 4,
            "info": info,
            "source": source,
            "source_name": RELOCATION_SOURCES.get(source, "unknown"),
            "type": relocation_type,
            "type_name": RELOCATION_TYPES.get(relocation_type, "unknown"),
            "extra": extra,
            "target_offset": target_offset,
            "target_word": target_word,
            "target_extra_word": target_extra_word,
        })

    if declared_size % 4:
        warnings.append(f"resource {resource_index}: relocation-table size is not divisible by four")
    if len(relocation_bytes) < declared_size:
        warnings.append(
            f"resource {resource_index}: relocation table is truncated "
            f"({len(relocation_bytes)} of {declared_size} bytes available)"
        )
    return entries


def default_geos_palette() -> list[tuple[int, int, int]]:
    """Return the documented 256-entry PC/GEOS default indexed palette."""
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
    palette.extend((value, value, value) for value in range(0, 256, 0x11))
    palette.extend([(0, 0, 0)] * 8)
    levels = (0x00, 0x33, 0x66, 0x99, 0xCC, 0xFF)
    palette.extend(
        (red, green, blue)
        for red in levels
        for green in levels
        for blue in levels
    )
    return palette


DEFAULT_GEOS_PALETTE = default_geos_palette()


def png_chunk(chunk_type: bytes, payload: bytes) -> bytes:
    checksum = zlib.crc32(chunk_type + payload) & 0xFFFFFFFF
    return struct.pack(">I", len(payload)) + chunk_type + payload + struct.pack(">I", checksum)


def rgba_png(width: int, height: int, pixels: bytes) -> bytes:
    if len(pixels) != width * height * 4:
        raise ValueError("RGBA pixel count does not match the PNG dimensions")
    scanlines = bytearray()
    stride = width * 4
    for row in range(height):
        scanlines.append(0)  # PNG filter type: None
        scanlines.extend(pixels[row * stride:(row + 1) * stride])
    header = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)
    return (
        b"\x89PNG\r\n\x1a\n"
        + png_chunk(b"IHDR", header)
        + png_chunk(b"IDAT", zlib.compress(bytes(scanlines), 9))
        + png_chunk(b"IEND", b"")
    )


def bitmap_line_sizes(width: int, bitmap_format: int, has_mask: bool) -> tuple[int, int]:
    mask_size = (width + 7) // 8
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
        raise ValueError(f"unknown GEOS bitmap format {bitmap_format}")
    return mask_size, pixel_size + (mask_size if has_mask else 0)


def unpack_packbits_row(payload: bytes, offset: int, expected_size: int) -> tuple[bytes, int]:
    """Decode one GEOS/Macintosh PackBits scan line."""
    result = bytearray()
    cursor = offset
    while len(result) < expected_size:
        if cursor >= len(payload):
            raise ValueError("truncated PackBits control byte")
        control = payload[cursor]
        cursor += 1
        if control < 0x80:
            count = control + 1
            if cursor + count > len(payload):
                raise ValueError("truncated PackBits literal packet")
            if len(result) + count > expected_size:
                raise ValueError("PackBits literal packet exceeds its scan line")
            result.extend(payload[cursor:cursor + count])
            cursor += count
        else:
            # The GEOS kernel treats 0x80 as a 129-byte repeat, rather than
            # the no-op assigned to it by some later PackBits descriptions.
            count = 257 - control
            if cursor >= len(payload):
                raise ValueError("truncated PackBits repeat packet")
            if len(result) + count > expected_size:
                raise ValueError("PackBits repeat packet exceeds its scan line")
            result.extend(payload[cursor:cursor + 1] * count)
            cursor += 1
    return bytes(result), cursor


def bit_at(payload: bytes, pixel: int) -> int:
    return 1 if payload[pixel // 8] & (0x80 >> (pixel & 7)) else 0


def decode_simple_geos_bitmap(bitmap: bytes, opcode: int) -> tuple[bytes, dict[str, Any]]:
    """Decode a complete simple GEOS Bitmap structure to an RGBA PNG."""
    if len(bitmap) < 6:
        raise ValueError("bitmap header is truncated")
    width, height, compaction, bitmap_type = struct.unpack_from("<HHBB", bitmap)
    if width == 0 or height == 0:
        raise ValueError("bitmap has a zero dimension")
    if width > 16384 or height > 16384 or width * height > 64_000_000:
        raise ValueError("bitmap dimensions are not safe to materialize")
    if bitmap_type & 0x80:
        raise ValueError("bitmap has a reserved high type bit")
    if bitmap_type & 0x20:
        raise ValueError("HugeArray bitmap data is external to this inline record")
    if bitmap_type & 0x08:
        raise ValueError("complex/sliced bitmap requires its CBitmap record chain")

    bitmap_format = bitmap_type & 0x07
    has_mask = bool(bitmap_type & 0x10)
    if bitmap_format not in BITMAP_FORMAT_NAMES:
        raise ValueError(f"unknown GEOS bitmap format {bitmap_format}")
    if compaction not in BITMAP_COMPACTION_NAMES:
        raise ValueError(f"unknown GEOS bitmap compaction {compaction}")
    if compaction == 2:
        raise ValueError("LZG-compressed inline bitmap decoding is not implemented")

    mask_size, line_size = bitmap_line_sizes(width, bitmap_format, has_mask)
    encoded = bitmap[6:]
    rows: list[bytes] = []
    cursor = 0
    if compaction == 0:
        expected = line_size * height
        if len(encoded) != expected:
            raise ValueError(
                f"uncompressed bitmap has {len(encoded)} data bytes; expected {expected}"
            )
        rows = [encoded[row * line_size:(row + 1) * line_size] for row in range(height)]
        cursor = len(encoded)
    else:
        for _row in range(height):
            decoded, cursor = unpack_packbits_row(encoded, cursor, line_size)
            rows.append(decoded)
        if cursor != len(encoded):
            raise ValueError("PackBits bitmap has trailing bytes after its final scan line")

    fill_operation = opcode in (GR_FILL_BITMAP, GR_FILL_BITMAP_CP)
    rgba = bytearray()
    for row in rows:
        mask = row[:mask_size] if has_mask else None
        pixel_data = row[mask_size:] if has_mask else row
        for x in range(width):
            if bitmap_format == 0:
                value = bit_at(pixel_data, x)
                red = green = blue = 0 if value else 255
                if fill_operation:
                    alpha = 255 if value else 0
                    if mask is not None and not bit_at(mask, x):
                        alpha = 0
                else:
                    alpha = 255 if mask is None or bit_at(mask, x) else 0
            elif bitmap_format == 1:
                packed = pixel_data[x // 2]
                palette_index = (packed >> 4) if x % 2 == 0 else (packed & 0x0F)
                red, green, blue = DEFAULT_GEOS_PALETTE[palette_index]
                alpha = 255 if mask is None or bit_at(mask, x) else 0
            elif bitmap_format == 2:
                red, green, blue = DEFAULT_GEOS_PALETTE[pixel_data[x]]
                alpha = 255 if mask is None or bit_at(mask, x) else 0
            elif bitmap_format == 3:
                red, green, blue = pixel_data[x * 3:x * 3 + 3]
                alpha = 255 if mask is None or bit_at(mask, x) else 0
            else:
                plane_size = mask_size
                cyan = 255 if bit_at(pixel_data[0 * plane_size:1 * plane_size], x) else 0
                magenta = 255 if bit_at(pixel_data[1 * plane_size:2 * plane_size], x) else 0
                yellow = 255 if bit_at(pixel_data[2 * plane_size:3 * plane_size], x) else 0
                black = (
                    255 if bitmap_format == 4
                    and bit_at(pixel_data[3 * plane_size:4 * plane_size], x) else 0
                )
                red = 255 - min(255, cyan + black)
                green = 255 - min(255, magenta + black)
                blue = 255 - min(255, yellow + black)
                alpha = 255 if mask is None or bit_at(mask, x) else 0
            rgba.extend((red, green, blue, alpha))

    details = {
        "width": width,
        "height": height,
        "compaction": compaction,
        "compaction_name": BITMAP_COMPACTION_NAMES[compaction],
        "bitmap_type": bitmap_type,
        "bitmap_type_hex": f"0x{bitmap_type:02x}",
        "format": bitmap_format,
        "format_name": BITMAP_FORMAT_NAMES[bitmap_format],
        "has_transparency_mask": has_mask,
        "inline_bitmap_size": len(bitmap),
        "decoded_scanline_bytes": line_size,
        "encoded_pixel_bytes": len(encoded),
    }
    return rgba_png(width, height, bytes(rgba)), details


def parse_lmem_chunks(payload: bytes) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]]]:
    if len(payload) < 16:
        return None, []
    values = struct.unpack_from("<8H", payload)
    segment, table_offset, flags, lmem_type, block_size, handle_count, free_offset, free_size = values
    if lmem_type not in LMEM_TYPE_NAMES:
        return None, []
    if table_offset < 16 or table_offset + handle_count * 2 > len(payload):
        return None, []
    header = {
        "segment": segment,
        "handle_table_offset": table_offset,
        "flags": flags,
        "type": lmem_type,
        "type_name": LMEM_TYPE_NAMES[lmem_type],
        "block_size": block_size,
        "handle_count": handle_count,
        "free_offset": free_offset,
        "free_size": free_size,
    }
    chunks = []
    for index in range(handle_count):
        handle = table_offset + index * 2
        data_offset = struct.unpack_from("<H", payload, handle)[0]
        if data_offset in (0, 0xFFFF) or data_offset <= table_offset or data_offset < 2:
            continue
        if data_offset > len(payload):
            continue
        allocated_size = struct.unpack_from("<H", payload, data_offset - 2)[0]
        if allocated_size < 2:
            continue
        data_size = allocated_size - 2
        chunk_end = data_offset + data_size
        chunks.append({
            "index": index,
            "handle": handle,
            "data_offset": data_offset,
            "declared_data_size": data_size,
            "complete": chunk_end <= len(payload),
            "data": payload[data_offset:min(chunk_end, len(payload))],
        })
    return header, chunks


def find_resource_graphics(resource_index: int, payload: bytes) -> tuple[list[dict[str, Any]], list[str]]:
    """Find structurally complete inline Bitmap VisMonikers in an LMem resource."""
    _header, chunks = parse_lmem_chunks(payload)
    graphics: list[dict[str, Any]] = []
    notices: list[str] = []
    for chunk in chunks:
        if not chunk["complete"]:
            continue
        content = chunk["data"]
        offset = 0
        while offset + 14 <= len(content):
            moniker_type = content[offset]
            if moniker_type & 0xC0 != 0x40:
                offset += 1
                continue
            moniker_width = struct.unpack_from("<H", content, offset + 1)[0]
            moniker_height = struct.unpack_from("<H", content, offset + 3)[0]
            opcode = content[offset + 5]
            if opcode not in INLINE_BITMAP_OPCODES or moniker_width == 0 or moniker_height == 0:
                offset += 1
                continue
            bitmap_offset = offset + (8 if opcode in (GR_FILL_BITMAP_CP, GR_DRAW_BITMAP_CP) else 12)
            if bitmap_offset > len(content):
                offset += 1
                continue
            bitmap_size = struct.unpack_from("<H", content, bitmap_offset - 2)[0]
            bitmap_end = bitmap_offset + bitmap_size
            if bitmap_offset + 6 > len(content):
                offset += 1
                continue
            bitmap_width, bitmap_height = struct.unpack_from("<HH", content, bitmap_offset)
            if bitmap_width != moniker_width or bitmap_height != moniker_height:
                offset += 1
                continue
            if bitmap_size < 6:
                notices.append(
                    f"resource {resource_index}, LMem handle 0x{chunk['handle']:04x}, "
                    f"chunk offset 0x{offset:04x}: inline bitmap size {bitmap_size} "
                    "is smaller than its 6-byte header"
                )
                break
            if bitmap_end > len(content):
                notices.append(
                    f"resource {resource_index}, LMem handle 0x{chunk['handle']:04x}, "
                    f"chunk offset 0x{offset:04x}: inline bitmap declares {bitmap_size} "
                    f"bytes but only {len(content) - bitmap_offset} remain in the chunk"
                )
                break
            # A one-command graphics moniker ends with GR_END_GSTRING. A
            # missing final byte at the exact chunk boundary is recoverable.
            end_present = bitmap_end < len(content) and content[bitmap_end] == 0
            if bitmap_end < len(content) and not end_present:
                offset += 1
                continue
            bitmap = content[bitmap_offset:bitmap_end]
            try:
                png, details = decode_simple_geos_bitmap(bitmap, opcode)
            except ValueError as error:
                notices.append(
                    f"resource {resource_index}, LMem handle 0x{chunk['handle']:04x}, "
                    f"chunk offset 0x{offset:04x}: {error}"
                )
                offset += 1
                continue
            graphic = {
                "resource": resource_index,
                "lmem_handle": chunk["handle"],
                "lmem_handle_hex": f"0x{chunk['handle']:04x}",
                "chunk_data_offset": chunk["data_offset"],
                "offset_within_chunk": offset,
                "offset_within_chunk_hex": f"0x{offset:04x}",
                "moniker_type": moniker_type,
                "moniker_type_hex": f"0x{moniker_type:02x}",
                "gstring_opcode": opcode,
                "gstring_end_present": end_present,
                **details,
                "_png": png,
            }
            graphics.append(graphic)
            offset = bitmap_end + (1 if end_present else 0)
    return graphics, notices


def text_byte(value: int) -> bool:
    if 0x20 <= value <= 0x7E:
        return True
    # The sample set is English and German. These are the Extended BSW letters
    # commonly occurring in its localized UI text; accepting every high glyph
    # would turn arbitrary binary and x86 operands into apparent prose.
    return value in {0x80, 0x85, 0x86, 0x8A, 0x9A, 0x9F, 0xA7}


def likely_readable_text(raw: bytes) -> Optional[str]:
    stripped = raw.strip(b" ")
    if len(stripped) < 6:
        return None
    decoded = stripped.decode("mac_roman", errors="replace")
    letters = [character for character in decoded if character.isalpha()]
    if len(letters) < 3:
        return None
    alphanumeric = [character.lower() for character in decoded if character.isalnum()]
    if alphanumeric and len(set(alphanumeric)) == 1 and not any(character.isspace() for character in decoded):
        return None
    if decoded.isalpha() and len(decoded) >= 6:
        for period in (1, 2, 3):
            repeated = (decoded[:period] * ((len(decoded) + period - 1) // period))[:len(decoded)]
            repeated_without_last = repeated[:-1]
            if decoded == repeated or decoded[:-1] == repeated_without_last:
                return None
    vowels = set("aeiouäöüAEIOUÄÖÜ")
    words: list[str] = []
    word = ""
    for character in decoded:
        if character.isalpha():
            word += character
        elif word:
            words.append(word)
            word = ""
    if word:
        words.append(word)
    if not any(len(item) >= 3 and any(character in vowels for character in item) for item in words):
        return None
    if not any(character.isspace() for character in decoded):
        uppercase = sum(character.isupper() for character in decoded)
        lowercase = sum(character.islower() for character in decoded)
        path_punctuation = any(character in "./_-" for character in decoded)
        path_punctuation = path_punctuation or ("\\" in decoded and ":" in decoded)
        if uppercase and not lowercase and not path_punctuation:
            return None
        if uppercase > 2 and uppercase * 2 >= max(1, lowercase) and not path_punctuation:
            return None
    return decoded


def readable_strings(payload: bytes) -> list[tuple[int, str]]:
    strings: list[tuple[int, str]] = []
    cursor = 0
    while cursor < len(payload):
        if not text_byte(payload[cursor]):
            cursor += 1
            continue
        start = cursor
        while cursor < len(payload) and text_byte(payload[cursor]):
            cursor += 1
        decoded = likely_readable_text(payload[start:cursor])
        if decoded is not None:
            strings.append((start, decoded))
    return strings


def lmem_text_monikers(resource_index: int, payload: bytes) -> list[dict[str, Any]]:
    """Return complete, explicitly typed text VisMoniker chunks."""
    _header, chunks = parse_lmem_chunks(payload)
    entries: list[dict[str, Any]] = []
    for chunk in chunks:
        if not chunk["complete"]:
            continue
        content = chunk["data"]
        if len(content) < 5 or content[0] & 0xC0:
            continue
        try:
            terminator = content.index(0, 4)
        except ValueError:
            continue
        raw = content[4:terminator]
        if not raw or not all(text_byte(value) for value in raw):
            continue
        mnemonic = content[3]
        if mnemonic not in (0xFD, 0xFE, 0xFF) and mnemonic >= len(raw):
            continue
        trailing = content[terminator + 1:]
        if len(trailing) > 3 or any(value not in (0, 0xCC) for value in trailing):
            continue
        entries.append({
            "source": (
                f"resource {resource_index:05d}, text VisMoniker handle "
                f"0x{chunk['handle']:04x}"
            ),
            "resource": resource_index,
            "lmem_handle": chunk["handle"],
            "text": raw.decode("mac_roman"),
        })
    return entries


def build_text_output(metadata: dict[str, Any]) -> tuple[bytes, list[dict[str, Any]]]:
    entries: list[dict[str, Any]] = []
    common = metadata["common_header"]
    for label, value in [
        ("long name", common.get("long_name")),
        ("user notes", common.get("user_notes")),
        ("copyright/notice", common.get("notice")),
    ]:
        if value:
            entries.append({"source": f"file header: {label}", "text": value})

    seen = {entry["text"] for entry in entries}
    for resource in metadata["resources"]:
        if "LMem" not in resource["allocation_flags"]["names"]:
            continue
        for entry in lmem_text_monikers(resource["index"], resource["_data"]):
            if entry["text"] in seen:
                continue
            seen.add(entry["text"])
            entries.append(entry)

    for resource in metadata["resources"]:
        for offset, value in readable_strings(resource["_data"]):
            if value in seen:
                continue
            seen.add(value)
            entries.append({
                "source": f"resource {resource['index']:05d} at 0x{offset:04x}",
                "resource": resource["index"],
                "offset": offset,
                "text": value,
            })

    lines: list[str] = []
    for entry in entries:
        lines.append(entry["text"])
        lines.append("")
    return ("\n".join(lines).rstrip() + "\n").encode("utf-8"), entries


def decode_friendly_content(metadata: dict[str, Any], detailed_names: bool) -> None:
    graphics: list[dict[str, Any]] = []
    notices: list[str] = []
    for resource in metadata["resources"]:
        if "LMem" not in resource["allocation_flags"]["names"]:
            continue
        found, found_notices = find_resource_graphics(resource["index"], resource["_data"])
        graphics.extend(found)
        notices.extend(found_notices)

    for number, graphic in enumerate(graphics, 1):
        graphic["number"] = number
        if detailed_names:
            graphic["filename"] = (
                f"resource_{graphic['resource']:05d}_"
                f"handle_{graphic['lmem_handle']:04x}_"
                f"offset_{graphic['offset_within_chunk']:05x}_"
                f"image_{number:04d}_{graphic['width']}x{graphic['height']}.png"
            )
        else:
            graphic["filename"] = f"{graphic['resource']:05d}_{number:04d}.png"

    text_payload, text_entries = build_text_output(metadata)
    metadata["decoded_content"] = {
        "graphic_count": len(graphics),
        "graphics": [
            {key: value for key, value in graphic.items() if not key.startswith("_")}
            for graphic in graphics
        ],
        "text_file": "text.txt",
        "text_entry_count": len(text_entries),
        "decode_notices": notices,
    }
    metadata["_graphics"] = graphics
    metadata["_text_payload"] = text_payload


def parse_geode(data: bytes, input_name: str) -> dict[str, Any]:
    if len(data) < 4 or data[:4] != SIGNATURE:
        raise UnsupportedFormat("not a PC/GEOS 2.x file (signature mismatch)")
    if len(data) < 42:
        raise UnsupportedFormat("signature matches, but the file is too short to prove it is executable")
    common_file_type = struct.unpack_from("<H", data, 40)[0]
    if common_file_type != 1:
        type_name = GEOS_FILE_TYPES.get(common_file_type, "unknown")
        raise UnsupportedFormat(f"PC/GEOS file type {common_file_type} ({type_name}) is not executable")

    warnings: list[str] = []
    if len(data) < COMMON_HEADER_SIZE:
        warnings.append(
            f"common header is truncated ({len(data)} of {COMMON_HEADER_SIZE} bytes available)"
        )

    common_flags = u16(data, 42)
    dbcs = bool(common_flags is not None and common_flags & 0x0400)
    long_name_raw = fixed_raw(data, 4, 36)
    user_notes_raw = fixed_raw(data, 68, 100)
    notice_raw = fixed_raw(data, 168, 32)
    password_raw = fixed_raw(data, 204, 8)
    desktop_raw = fixed_raw(data, 212, 16)
    reserved_raw = fixed_raw(data, 228, 28)

    common = {
        "signature_hex": data[:4].hex(),
        "long_name": decode_fixed(long_name_raw, dbcs),
        "long_name_raw_hex": long_name_raw.hex(),
        "file_type": common_file_type,
        "file_type_name": GEOS_FILE_TYPES[common_file_type],
        "flags": named_bits(common_flags, FILE_HEADER_FLAGS),
        "release": release_at(data, 44),
        "protocol": protocol_at(data, 52),
        "token": token_at(data, 56),
        "creator": token_at(data, 62),
        "user_notes": decode_fixed(user_notes_raw, dbcs),
        "user_notes_raw_hex": user_notes_raw.hex(),
        "notice": decode_ascii_fixed(notice_raw),
        "notice_raw_hex": notice_raw.hex(),
        "created": packed_timestamp(u16(data, 200), u16(data, 202)),
        "password": decode_ascii_fixed(password_raw),
        "password_raw_hex": password_raw.hex(),
        "desktop_info_raw_hex": desktop_raw.hex(),
        "reserved_raw_hex": reserved_raw.hex(),
    }

    if len(data) < GEODE_HEADER_SIZE:
        warnings.append(
            f"geode header is truncated ({max(0, len(data) - COMMON_HEADER_SIZE)} of "
            f"{GEODE_HEADER_SIZE - COMMON_HEADER_SIZE} tail bytes available)"
        )

    attributes = u16(data, 256)
    geode_type = u16(data, 258)
    heap_space = u16(data, 260)
    unused = u16(data, 262)
    resource_count = u16(data, 264)
    import_count = u16(data, 266)
    export_count = u16(data, 268)
    udata_size = u16(data, 270)

    executable = {
        "attributes": named_bits(attributes, GEODE_ATTRIBUTES),
        "geode_type": geode_type,
        "geode_type_name": GEODE_TYPE_NAMES.get(geode_type, "product-defined search category")
        if geode_type is not None else None,
        "heap_space_paragraphs": heap_space,
        "heap_space_bytes": heap_space * 16 if heap_space is not None else None,
        "unused": unused,
        "resource_count": resource_count,
        "import_library_count": import_count,
        "export_entry_count": export_count,
        "uninitialized_data_size": udata_size,
        "process_class_offset": u16(data, 272),
        "process_class_resource": u16(data, 274),
        "application_object_chunk": u16(data, 276),
        "application_object_resource": u16(data, 278),
    }

    core = {
        "runtime_geode_handle": u16(data, 280),
        "attributes_copy": named_bits(u16(data, 282), GEODE_ATTRIBUTES),
        "geode_type_copy": u16(data, 284),
        "release_copy": release_at(data, 286),
        "protocol_copy": protocol_at(data, 294),
        "build_serial": u16(data, 298),
        "permanent_name": decode_ascii_fixed(fixed_raw(data, 300, 8)),
        "permanent_name_raw_hex": fixed_raw(data, 300, 8).hex(),
        "permanent_extension": decode_ascii_fixed(fixed_raw(data, 308, 4)),
        "permanent_extension_raw_hex": fixed_raw(data, 308, 4).hex(),
        "token_copy": token_at(data, 312),
        "runtime_reference_count": u16(data, 318),
        "driver_table_offset": u16(data, 320),
        "driver_table_resource": u16(data, 322),
        "library_entry_offset": u16(data, 324),
        "library_entry_resource": u16(data, 326),
        "runtime_export_table_offset": u16(data, 328),
        "export_entry_count_copy": u16(data, 330),
        "import_library_count_copy": u16(data, 332),
        "runtime_import_table_offset": u16(data, 334),
        "resource_count_copy": u16(data, 336),
        "runtime_resource_handle_table_offset": u16(data, 338),
        "runtime_resource_position_table_offset": u16(data, 340),
        "runtime_resource_relocation_table_offset": u16(data, 342),
    }

    if unused not in (None, 0):
        warnings.append("ExecutableFileHeader2.unused is nonzero")

    duplicate_checks = [
        ("attributes", fixed_raw(data, 256, 2), fixed_raw(data, 282, 2)),
        ("geode type", fixed_raw(data, 258, 2), fixed_raw(data, 284, 2)),
        ("release", fixed_raw(data, 44, 8), fixed_raw(data, 286, 8)),
        ("protocol", fixed_raw(data, 52, 4), fixed_raw(data, 294, 4)),
        ("token", fixed_raw(data, 56, 6), fixed_raw(data, 312, 6)),
        ("export count", fixed_raw(data, 268, 2), fixed_raw(data, 330, 2)),
        ("import count", fixed_raw(data, 266, 2), fixed_raw(data, 332, 2)),
        ("resource count", fixed_raw(data, 264, 2), fixed_raw(data, 336, 2)),
    ]
    for label, first, second in duplicate_checks:
        if len(first) == len(second) and len(first) > 0 and first != second:
            warnings.append(f"duplicated {label} fields disagree")

    for label, value in [
        ("runtime geode handle", core["runtime_geode_handle"]),
        ("runtime reference count", core["runtime_reference_count"]),
        ("runtime export table offset", core["runtime_export_table_offset"]),
        ("runtime import table offset", core["runtime_import_table_offset"]),
        ("runtime resource handle table offset", core["runtime_resource_handle_table_offset"]),
        ("runtime resource position table offset", core["runtime_resource_position_table_offset"]),
        ("runtime resource relocation table offset", core["runtime_resource_relocation_table_offset"]),
    ]:
        if value not in (None, 0):
            warnings.append(f"{label} is nonzero in the on-disk header")

    imports: list[dict[str, Any]] = []
    exports: list[dict[str, Any]] = []
    resources: list[dict[str, Any]] = []
    accounting: list[dict[str, Any]] = []

    def add_accounting(kind: str, offset: int, size: int, **extra: Any) -> None:
        if size <= 0:
            return
        actual = available_slice(data, offset, size)
        record: dict[str, Any] = {
            "kind": kind,
            "offset": offset,
            "declared_size": size,
            "available_size": len(actual),
        }
        record.update(extra)
        accounting.append(record)

    add_accounting("common-header", 0, COMMON_HEADER_SIZE)
    if len(data) > COMMON_HEADER_SIZE:
        add_accounting(
            "geode-header-tail",
            COMMON_HEADER_SIZE,
            GEODE_HEADER_SIZE - COMMON_HEADER_SIZE,
        )

    tables: dict[str, Any] = {
        "imports_offset": GEODE_HEADER_SIZE,
        "exports_offset": None,
        "resource_tables_offset": None,
        "resource_sizes_offset": None,
        "resource_positions_offset": None,
        "relocation_sizes_offset": None,
        "allocation_flags_offset": None,
        "end_offset": None,
    }

    if import_count is not None and export_count is not None and resource_count is not None:
        import_start = GEODE_HEADER_SIZE
        import_end = import_start + import_count * IMPORTED_LIBRARY_ENTRY_SIZE
        export_start = import_end
        export_end = export_start + export_count * EXPORTED_ENTRY_SIZE
        table_start = export_end
        sizes_start = table_start
        positions_start = sizes_start + resource_count * 2
        reloc_sizes_start = positions_start + resource_count * 4
        flags_start = reloc_sizes_start + resource_count * 2
        table_end = flags_start + resource_count * 2
        tables.update({
            "exports_offset": export_start,
            "resource_tables_offset": table_start,
            "resource_sizes_offset": sizes_start,
            "resource_positions_offset": positions_start,
            "relocation_sizes_offset": reloc_sizes_start,
            "allocation_flags_offset": flags_start,
            "end_offset": table_end,
        })

        add_accounting("import-table", import_start, import_count * IMPORTED_LIBRARY_ENTRY_SIZE)
        add_accounting("export-table", export_start, export_count * EXPORTED_ENTRY_SIZE)
        add_accounting("resource-descriptor-tables", table_start, resource_count * RESOURCE_DESCRIPTOR_SIZE)

        if table_end > len(data):
            warnings.append(
                f"header tables are truncated ({max(0, len(data) - table_start)} of "
                f"{resource_count * RESOURCE_DESCRIPTOR_SIZE} resource-table bytes available)"
            )

        for index in range(import_count):
            offset = import_start + index * IMPORTED_LIBRARY_ENTRY_SIZE
            if offset + IMPORTED_LIBRARY_ENTRY_SIZE > len(data):
                break
            name_raw = data[offset:offset + 8]
            import_attributes, proto_major, proto_minor = struct.unpack_from("<3H", data, offset + 8)
            imports.append({
                "index": index,
                "name": decode_ascii_fixed(name_raw),
                "name_raw_hex": name_raw.hex(),
                "required_attributes": named_bits(import_attributes, GEODE_ATTRIBUTES),
                "required_protocol": {
                    "major": proto_major,
                    "minor": proto_minor,
                    "text": f"{proto_major}.{proto_minor}",
                },
            })
        if len(imports) < import_count:
            warnings.append(f"import table is truncated ({len(imports)} of {import_count} entries available)")

        for index in range(export_count):
            offset = export_start + index * EXPORTED_ENTRY_SIZE
            if offset + EXPORTED_ENTRY_SIZE > len(data):
                break
            entry_offset, resource = struct.unpack_from("<2H", data, offset)
            exports.append({"index": index, "offset": entry_offset, "resource": resource})
        if len(exports) < export_count:
            warnings.append(f"export table is truncated ({len(exports)} of {export_count} entries available)")

        descriptor_values: list[dict[str, Optional[int]]] = []
        for index in range(resource_count):
            descriptor_values.append({
                "size": u16(data, sizes_start + index * 2),
                "stored_position": u32(data, positions_start + index * 4),
                "relocation_size": u16(data, reloc_sizes_start + index * 2),
                "flags": u16(data, flags_start + index * 2),
            })

        previous_minimum_end = table_end
        known_positions = [
            item["stored_position"] + COMMON_HEADER_SIZE
            if item["stored_position"] is not None else None
            for item in descriptor_values
        ]

        for index, descriptor in enumerate(descriptor_values):
            size = descriptor["size"]
            stored_position = descriptor["stored_position"]
            relocation_size = descriptor["relocation_size"]
            allocation_flags = descriptor["flags"]
            absolute_position = (
                stored_position + COMMON_HEADER_SIZE if stored_position is not None else None
            )
            padding_size = ((-size) & 0x0F) if size is not None else None
            aligned_size = size + padding_size if size is not None and padding_size is not None else None

            resource_data = b""
            padding_data = b""
            relocation_data = b""
            relocation_entries: list[dict[str, Any]] = []
            gap_after_data = b""
            gap_after_offset = None
            declared_gap_after = None

            if size is not None and absolute_position is not None:
                resource_data = available_slice(data, absolute_position, size)
                if len(resource_data) < size:
                    warnings.append(
                        f"resource {index}: data is truncated ({len(resource_data)} of {size} bytes available)"
                    )
                padding_offset = absolute_position + size
                padding_data = available_slice(data, padding_offset, padding_size or 0)
                if len(padding_data) < (padding_size or 0):
                    warnings.append(
                        f"resource {index}: paragraph padding is truncated "
                        f"({len(padding_data)} of {padding_size} bytes available)"
                    )

                if relocation_size is not None and aligned_size is not None:
                    relocation_offset = absolute_position + aligned_size
                    relocation_data = available_slice(data, relocation_offset, relocation_size)
                    relocation_entries = parse_relocations(
                        relocation_data,
                        relocation_size,
                        resource_data,
                        size,
                        import_count,
                        index,
                        warnings,
                    )
                    minimum_end = relocation_offset + relocation_size
                    if index + 1 < resource_count:
                        next_position = known_positions[index + 1]
                    else:
                        next_position = len(data)
                    if next_position is not None:
                        declared_gap_after = next_position - minimum_end
                        gap_after_offset = minimum_end
                        if declared_gap_after < 0:
                            if index + 1 == resource_count:
                                # For the final resource, a negative remainder
                                # means EOF cut the record short, not that a
                                # following resource overlaps it.
                                pass
                            else:
                                zero_overlap = (
                                    size == 0
                                    and relocation_size == 0
                                    and absolute_position == next_position
                                )
                                if not zero_overlap:
                                    warnings.append(
                                        f"resource {index}: record overlaps the next resource by "
                                        f"{-declared_gap_after} bytes"
                                    )
                        elif declared_gap_after > 0:
                            gap_after_data = available_slice(data, minimum_end, declared_gap_after)
                            if len(gap_after_data) < declared_gap_after:
                                warnings.append(
                                    f"resource {index}: following layout slack is truncated"
                                )

                    if absolute_position < previous_minimum_end:
                        zero_alias = size == 0 and absolute_position == previous_minimum_end
                        if not zero_alias:
                            warnings.append(
                                f"resource {index}: position precedes the end of preceding structures"
                            )
                    elif absolute_position > previous_minimum_end:
                        add_accounting(
                            "layout-slack-before-resource",
                            previous_minimum_end,
                            absolute_position - previous_minimum_end,
                            resource=index,
                        )
                    add_accounting("resource-data", absolute_position, size, resource=index)
                    add_accounting(
                        "resource-paragraph-padding",
                        absolute_position + size,
                        padding_size or 0,
                        resource=index,
                    )
                    add_accounting(
                        "resource-relocations",
                        relocation_offset,
                        relocation_size,
                        resource=index,
                    )
                    previous_minimum_end = max(previous_minimum_end, minimum_end)
                    if declared_gap_after is not None and declared_gap_after > 0:
                        add_accounting(
                            "layout-slack-after-resource",
                            minimum_end,
                            declared_gap_after,
                            resource=index,
                        )
                        previous_minimum_end = max(previous_minimum_end, minimum_end + declared_gap_after)

            resources.append({
                "index": index,
                "size": size,
                "stored_position": stored_position,
                "absolute_position": absolute_position,
                "paragraph_padding_size": padding_size,
                "relocation_size": relocation_size,
                "allocation_flags": named_bits(allocation_flags, RESOURCE_FLAGS),
                "available_data_size": len(resource_data),
                "available_padding_size": len(padding_data),
                "available_relocation_size": len(relocation_data),
                "layout_slack_after_size": declared_gap_after,
                "available_layout_slack_after_size": len(gap_after_data),
                "data_sha256": sha256_bytes(resource_data) if size is not None else None,
                "relocations": relocation_entries,
                "relocation_trailing_bytes_hex": relocation_data[len(relocation_entries) * 4:].hex(),
                "_data": resource_data,
                "_padding": padding_data,
                "_relocation_data": relocation_data,
                "_gap_after": gap_after_data,
                "_gap_after_offset": gap_after_offset,
            })
    else:
        warnings.append("executable counts are unavailable; resource tables cannot be located")

    # Only count non-overlapping ranges. The healthy format is sequential; any
    # overlap already generated a damage warning above.
    intervals = []
    for item in accounting:
        start = item["offset"]
        end = start + item["available_size"]
        if end > start:
            intervals.append((start, end))
    intervals.sort()
    covered = 0
    cursor = 0
    overlap_bytes = 0
    for start, end in intervals:
        if end <= cursor:
            overlap_bytes += end - start
            continue
        if start < cursor:
            overlap_bytes += cursor - start
            start = cursor
        covered += end - start
        cursor = end

    metadata = {
        "format": "PC/GEOS 2.x executable geode",
        "input_name": input_name,
        "input_size": len(data),
        "input_sha256": sha256_bytes(data),
        "status": "damaged-or-truncated" if warnings else "complete",
        "warnings": warnings,
        "common_header": common,
        "executable_header": executable,
        "geode_core_header": core,
        "tables": tables,
        "imports": imports,
        "exports": exports,
        "resources": resources,
        "byte_accounting": {
            "ranges": accounting,
            "covered_input_bytes": covered,
            "input_bytes": len(data),
            "overlap_bytes": overlap_bytes,
            "all_bytes_accounted": covered == len(data) and overlap_bytes == 0,
        },
    }
    return metadata


def ensure_directory(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True, mode=0o775)
    current = stat.S_IMODE(path.stat().st_mode)
    os.chmod(path, current | 0o770)


def atomic_write(path: Path, payload: bytes) -> None:
    ensure_directory(path.parent)
    descriptor, temporary_name = tempfile.mkstemp(prefix=".geos-extract-", dir=path.parent)
    try:
        os.fchmod(descriptor, 0o664)
        with os.fdopen(descriptor, "wb") as output:
            output.write(payload)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary_name, path)
        current = stat.S_IMODE(path.stat().st_mode)
        os.chmod(path, current | 0o660)
    except Exception:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


def public_metadata(metadata: dict[str, Any]) -> dict[str, Any]:
    clone = {key: value for key, value in metadata.items() if not key.startswith("_")}
    public_resources = []
    for resource in metadata["resources"]:
        public_resources.append({key: value for key, value in resource.items() if not key.startswith("_")})
    clone["resources"] = public_resources
    return clone


def render_output_index(metadata: dict[str, Any], emitted_files: list[str]) -> str:
    common = metadata["common_header"]
    executable = metadata["executable_header"]
    resources = metadata["resources"]
    decoded = metadata.get("decoded_content", {})
    graphics = decoded.get("graphics", [])
    decode_notices = decoded.get("decode_notices", [])
    warning_html = "".join(f"<li>{html.escape(item)}</li>" for item in metadata["warnings"])
    file_links = "".join(
        f'<li><a href="{html.escape(name)}" target="_blank" rel="noopener">{html.escape(name)}</a></li>'
        for name in sorted(emitted_files)
        if name != "index.html"
    )
    resource_rows = []
    for resource in resources:
        index = resource["index"]
        data_name = f"resource_{index:05d}.bin"
        relocation_name = f"resource_{index:05d}.reloc.bin"
        data_link = (
            f'<a href="{data_name}" target="_blank" rel="noopener">{resource["available_data_size"]} bytes</a>'
            if data_name in emitted_files else "not available"
        )
        relocation_link = (
            f'<a href="{relocation_name}" target="_blank" rel="noopener">'
            f'{resource["available_relocation_size"]} bytes</a>'
            if relocation_name in emitted_files else "0 bytes"
        )
        flag_names = ", ".join(resource["allocation_flags"]["names"]) or "none"
        resource_rows.append(
            "<tr>"
            f"<td>{index}</td><td>{data_link}</td><td>{relocation_link}</td>"
            f"<td>{len(resource['relocations'])}</td><td>{html.escape(flag_names)}</td>"
            "</tr>"
        )
    warnings_block = (
        f"<section><h2>Warnings</h2><ul class=warnings>{warning_html}</ul></section>"
        if warning_html else ""
    )
    decode_notice_block = (
        "<section><h2>Skipped embedded graphics</h2><p>These structurally tagged "
        "graphic monikers were damaged or used an unsupported bitmap encoding.</p>"
        '<ul class="warnings">'
        + "".join(f"<li>{html.escape(item)}</li>" for item in decode_notices)
        + "</ul></section>"
        if decode_notices else ""
    )
    graphic_cards = "".join(
        '<a class="graphic" href="{filename}" target="_blank" rel="noopener">'
        '<img src="{filename}" alt="Decoded GEOS graphic {number}" loading="lazy">'
        '<span>#{number} · {width}×{height}<small>resource {resource}, handle {handle}</small></span>'
        "</a>".format(
            filename=html.escape(graphic["filename"]),
            number=graphic["number"],
            width=graphic["width"],
            height=graphic["height"],
            resource=graphic["resource"],
            handle=html.escape(graphic["lmem_handle_hex"]),
        )
        for graphic in graphics
    )
    graphics_block = (
        f"<section><h2>Decoded graphics</h2><p>{len(graphics)} native GEOS bitmap "
        f"VisMoniker{'s' if len(graphics) != 1 else ''} converted to PNG.</p>"
        f'<div class="graphics">{graphic_cards}</div></section>'
        if graphics else
        "<section><h2>Decoded graphics</h2><p>No structurally tagged inline bitmap VisMonikers were found.</p></section>"
    )
    text_link = (
        '<a href="text.txt" target="_blank" rel="noopener">Open consolidated text</a>'
        if "text.txt" in emitted_files else "not emitted"
    )
    status_class = "ok" if metadata["status"] == "complete" else "bad"
    return f"""<!doctype html>
<!-- Vibe coded by Codex -->
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(metadata['input_name'])} extraction</title>
<style>
:root {{ color-scheme: dark; --bg:#0b0f14; --panel:#121923; --line:#293548; --text:#dce7f3; --muted:#91a0b4; --link:#78b7ff; --ok:#65d39a; --bad:#ff8e8e; }}
* {{ box-sizing:border-box }}
body {{ margin:0; padding:2rem; background:var(--bg); color:var(--text); font:15px/1.5 ui-monospace,SFMono-Regular,Consolas,monospace }}
main {{ max-width:1200px; margin:auto }}
h1,h2 {{ font-family:system-ui,sans-serif }}
section {{ background:var(--panel); border:1px solid var(--line); border-radius:12px; padding:1rem 1.25rem; margin:1rem 0 }}
.facts {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(220px,1fr)); gap:.75rem }}
.fact {{ border-left:3px solid var(--line); padding-left:.75rem }}
.label {{ color:var(--muted); display:block; font-size:.8rem }}
.ok {{ color:var(--ok) }} .bad,.warnings {{ color:var(--bad) }}
a {{ color:var(--link) }}
table {{ width:100%; border-collapse:collapse }} th,td {{ text-align:left; border-bottom:1px solid var(--line); padding:.55rem }}
th {{ color:var(--muted) }} ul {{ columns:2; padding-left:1.25rem }}
.graphics {{ display:grid; grid-template-columns:repeat(auto-fill,minmax(130px,1fr)); gap:.75rem }}
.graphic {{ min-height:125px; display:flex; flex-direction:column; align-items:center; justify-content:space-between; gap:.6rem; padding:.75rem; border:1px solid var(--line); border-radius:9px; background:#0d131c; text-align:center }}
.graphic img {{ width:72px; height:72px; object-fit:contain; image-rendering:pixelated; background:repeating-conic-gradient(#bec8d2 0 25%,#788694 0 50%) 50%/12px 12px; border-radius:4px }}
.graphic span {{ overflow-wrap:anywhere }} .graphic small {{ display:block; color:var(--muted); font-size:.7rem }}
@media (max-width:700px) {{ body {{ padding:1rem }} ul {{ columns:1 }} table {{ font-size:.8rem }} }}
</style>
</head>
<body><main>
<h1>{html.escape(common['long_name'] or metadata['input_name'])}</h1>
<section class="facts">
<div class="fact"><span class="label">Input</span>{html.escape(metadata['input_name'])}</div>
<div class="fact"><span class="label">Status</span><span class="{status_class}">{html.escape(metadata['status'])}</span></div>
<div class="fact"><span class="label">Input size</span>{metadata['input_size']:,} bytes</div>
<div class="fact"><span class="label">Resources</span>{executable['resource_count']}</div>
<div class="fact"><span class="label">Decoded graphics</span>{len(graphics)}</div>
<div class="fact"><span class="label">Text entries</span>{decoded.get('text_entry_count', 0)}</div>
<div class="fact"><span class="label">Imports / exports</span>{executable['import_library_count']} / {executable['export_entry_count']}</div>
<div class="fact"><span class="label">Byte accounting</span>{metadata['byte_accounting']['covered_input_bytes']:,} / {metadata['input_size']:,}</div>
</section>
{warnings_block}
{decode_notice_block}
<section><h2>Extracted text</h2><p>{text_link}</p></section>
{graphics_block}
<section><h2>Resources</h2><table><thead><tr><th>#</th><th>Data</th><th>Relocations</th><th>Entries</th><th>Flags</th></tr></thead><tbody>{''.join(resource_rows)}</tbody></table></section>
<section><h2>All emitted files</h2><ul>{file_links}</ul></section>
</main></body></html>
"""


def extract(input_path: Path, output_directory: Path, include_all: bool) -> tuple[dict[str, Any], list[str]]:
    data = input_path.read_bytes()
    metadata = parse_geode(data, input_path.name)
    decode_friendly_content(metadata, detailed_names=include_all)

    # Format validation happens before this point, so unsupported inputs never
    # create or change the output directory.
    ensure_directory(output_directory)
    emitted_files: list[str] = []

    for graphic in metadata["_graphics"]:
        name = graphic["filename"]
        atomic_write(output_directory / name, graphic["_png"])
        emitted_files.append(name)

    atomic_write(output_directory / "text.txt", metadata["_text_payload"])
    emitted_files.append("text.txt")

    if include_all:
        for resource in metadata["resources"]:
            index = resource["index"]
            size = resource["size"]
            resource_data = resource["_data"]
            if size == 0 or resource_data:
                name = f"resource_{index:05d}.bin"
                atomic_write(output_directory / name, resource_data)
                emitted_files.append(name)

            relocation_data = resource["_relocation_data"]
            if relocation_data:
                name = f"resource_{index:05d}.reloc.bin"
                atomic_write(output_directory / name, relocation_data)
                emitted_files.append(name)

            padding_data = resource["_padding"]
            if padding_data:
                name = f"resource_{index:05d}.padding.bin"
                atomic_write(output_directory / name, padding_data)
                emitted_files.append(name)
            gap_data = resource["_gap_after"]
            if gap_data:
                name = f"resource_{index:05d}.layout_slack.bin"
                atomic_write(output_directory / name, gap_data)
                emitted_files.append(name)

    if include_all:
        before_gap_number = 0
        for byte_range in metadata["byte_accounting"]["ranges"]:
            if byte_range["kind"] != "layout-slack-before-resource":
                continue
            payload = available_slice(
                data,
                byte_range["offset"],
                byte_range["declared_size"],
            )
            if payload:
                resource_index = byte_range.get("resource", before_gap_number)
                name = f"layout_slack_before_resource_{resource_index:05d}.bin"
                atomic_write(output_directory / name, payload)
                emitted_files.append(name)
                before_gap_number += 1

        structural_files = [
            ("common_header.bin", 0, min(COMMON_HEADER_SIZE, len(data))),
            (
                "geode_header_tail.bin",
                COMMON_HEADER_SIZE,
                max(0, min(GEODE_HEADER_SIZE, len(data)) - COMMON_HEADER_SIZE),
            ),
        ]
        tables = metadata["tables"]
        import_count = metadata["executable_header"]["import_library_count"]
        export_count = metadata["executable_header"]["export_entry_count"]
        resource_count = metadata["executable_header"]["resource_count"]
        if import_count is not None:
            structural_files.append(
                ("imports.bin", GEODE_HEADER_SIZE, import_count * IMPORTED_LIBRARY_ENTRY_SIZE)
            )
        if export_count is not None and tables["exports_offset"] is not None:
            structural_files.append(
                ("exports.bin", tables["exports_offset"], export_count * EXPORTED_ENTRY_SIZE)
            )
        if resource_count is not None and tables["resource_tables_offset"] is not None:
            structural_files.append(
                (
                    "resource_descriptor_tables.bin",
                    tables["resource_tables_offset"],
                    resource_count * RESOURCE_DESCRIPTOR_SIZE,
                )
            )

        for name, offset, declared_size in structural_files:
            payload = available_slice(data, offset, declared_size)
            if declared_size == 0 or payload:
                atomic_write(output_directory / name, payload)
                emitted_files.append(name)

        public = public_metadata(metadata)
        metadata_payload = (json.dumps(public, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
        atomic_write(output_directory / "metadata.json", metadata_payload)
        emitted_files.append("metadata.json")

        emitted_files.append("index.html")
        index_payload = render_output_index(metadata, emitted_files).encode("utf-8")
        atomic_write(output_directory / "index.html", index_payload)

    return metadata, emitted_files


def parse_arguments(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Extract PC/GEOS 2.x executable geode resources, convert tagged native "
            "bitmap VisMonikers to PNG, and consolidate readable text."
        )
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help=(
            "also emit raw resources and relocation tables, decoded metadata, raw "
            "headers/tables, paragraph padding, layout slack, and an HTML index; "
            "use detailed PNG names"
        ),
    )
    parser.add_argument("inputFile", type=Path)
    parser.add_argument("outputDir", type=Path)
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    arguments = parse_arguments(sys.argv[1:] if argv is None else argv)
    try:
        metadata, emitted = extract(arguments.inputFile, arguments.outputDir, arguments.all)
    except UnsupportedFormat as error:
        print(f"unsupported input: {error}", file=sys.stderr)
        return 1
    except OSError as error:
        print(f"I/O error: {error}", file=sys.stderr)
        return 1

    resources_emitted = sum(
        1
        for name in emitted
        if name.startswith("resource_")
        and name.endswith(".bin")
        and name[len("resource_"):-len(".bin")].isdigit()
    )
    relocation_files = sum(1 for name in emitted if name.endswith(".reloc.bin"))
    graphics = metadata.get("decoded_content", {}).get("graphic_count", 0)
    text_entries = metadata.get("decoded_content", {}).get("text_entry_count", 0)
    raw_summary = (
        f"extracted {resources_emitted} raw resource payloads and "
        f"{relocation_files} relocation tables; "
        if arguments.all else ""
    )
    print(
        f"{metadata['status']}: {raw_summary}converted {graphics} graphics and "
        f"collected {text_entries} text entries into {arguments.outputDir}"
    )
    if metadata["warnings"]:
        for warning in metadata["warnings"]:
            print(f"warning: {warning}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

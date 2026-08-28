#!/usr/bin/env python3
# Vibe coded by Codex
"""Convert an HP COPYDISK container to a headerless raw disk image."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import struct
import sys
import tempfile
from typing import BinaryIO


SIGNATURE = b"COPYDISK\x00"
HEADER = struct.Struct("<9sHHHH15s")
HEADER_SIZE = HEADER.size
SUPPORTED_MAJOR_VERSION = 2
COPY_CHUNK_SIZE = 1024 * 1024
OUTPUT_MODE = 0o664


class CopyDiskError(Exception):
    """Raised when an input cannot be converted safely."""


def parse_header(source: BinaryIO) -> dict[str, int | bytes]:
    """Read and strictly validate an HP COPYDISK header."""
    header_bytes = source.read(HEADER_SIZE)
    if len(header_bytes) != HEADER_SIZE:
        raise CopyDiskError(
            f"input is too short for the {HEADER_SIZE}-byte COPYDISK header"
        )

    signature, major, minor, sector_size, sector_count, reserved = HEADER.unpack(
        header_bytes
    )
    if signature != SIGNATURE:
        raise CopyDiskError("missing the exact COPYDISK signature")
    if major != SUPPORTED_MAJOR_VERSION:
        raise CopyDiskError(
            f"unsupported COPYDISK major version {major}; "
            f"only version {SUPPORTED_MAJOR_VERSION}.x is supported"
        )
    if reserved != bytes(15):
        raise CopyDiskError("the 15 reserved header bytes are not all zero")
    if sector_size == 0:
        raise CopyDiskError("header declares a zero-byte sector size")
    if sector_count == 0:
        raise CopyDiskError("header declares zero sectors")

    return {
        "header_bytes": header_bytes,
        "major": major,
        "minor": minor,
        "sector_size": sector_size,
        "sector_count": sector_count,
        "payload_size": sector_size * sector_count,
    }


def paths_are_same(first: Path, second: Path) -> bool:
    """Compare paths without requiring the destination to exist."""
    try:
        return first.samefile(second)
    except (FileNotFoundError, OSError):
        return first.resolve(strict=False) == second.resolve(strict=False)


def make_temporary_path(destination: Path) -> tuple[int, Path]:
    """Create a temporary output beside its final destination."""
    try:
        descriptor, name = tempfile.mkstemp(
            prefix=f".{destination.name}.", suffix=".tmp", dir=destination.parent
        )
    except OSError as error:
        raise CopyDiskError(
            f"cannot create output in {destination.parent}: {error.strerror or error}"
        ) from error
    return descriptor, Path(name)


def write_metadata_file(destination: Path, metadata: dict[str, object]) -> Path:
    """Prepare a JSON metadata sidecar and return its temporary path."""
    descriptor, temporary = make_temporary_path(destination)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(metadata, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, OUTPUT_MODE)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise
    return temporary


def convert(input_path: Path, output_path: Path, include_metadata: bool) -> None:
    """Validate one complete container and atomically publish its raw payload."""
    if paths_are_same(input_path, output_path):
        raise CopyDiskError("input and output must be different files")

    metadata_path = Path(f"{output_path}.json")
    if include_metadata and paths_are_same(input_path, metadata_path):
        raise CopyDiskError("the --all metadata path would overwrite the input file")

    temporary_output: Path | None = None
    temporary_metadata: Path | None = None
    try:
        try:
            source = input_path.open("rb")
        except OSError as error:
            raise CopyDiskError(
                f"cannot open input {input_path}: {error.strerror or error}"
            ) from error

        with source:
            source_stat = os.fstat(source.fileno())
            if not stat.S_ISREG(source_stat.st_mode):
                raise CopyDiskError("input is not a regular file")

            header = parse_header(source)
            payload_size = int(header["payload_size"])
            expected_size = HEADER_SIZE + payload_size
            if source_stat.st_size != expected_size:
                relation = "truncated" if source_stat.st_size < expected_size else "has trailing data"
                raise CopyDiskError(
                    f"input {relation}: header requires exactly {expected_size} bytes, "
                    f"but the file has {source_stat.st_size}"
                )

            descriptor, temporary_output = make_temporary_path(output_path)
            input_digest = hashlib.sha256() if include_metadata else None
            raw_digest = hashlib.sha256() if include_metadata else None
            if input_digest is not None:
                input_digest.update(bytes(header["header_bytes"]))

            remaining = payload_size
            with os.fdopen(descriptor, "wb") as destination:
                while remaining:
                    chunk = source.read(min(COPY_CHUNK_SIZE, remaining))
                    if not chunk:
                        raise CopyDiskError("input became truncated while it was being read")
                    destination.write(chunk)
                    remaining -= len(chunk)
                    if input_digest is not None and raw_digest is not None:
                        input_digest.update(chunk)
                        raw_digest.update(chunk)

                if source.read(1):
                    raise CopyDiskError("input gained trailing data while it was being read")
                destination.flush()
                os.fsync(destination.fileno())

            os.chmod(temporary_output, OUTPUT_MODE)

        if include_metadata:
            assert input_digest is not None and raw_digest is not None
            metadata: dict[str, object] = {
                "byte_accounting": {
                    "header": HEADER_SIZE,
                    "payload": payload_size,
                    "total": expected_size,
                    "unaccounted": 0,
                },
                "format": "HP COPYDISK",
                "format_version": {
                    "major": int(header["major"]),
                    "minor": int(header["minor"]),
                },
                "input_file": str(input_path),
                "input_size": expected_size,
                "output_file": str(output_path),
                "output_size": payload_size,
                "sector_count": int(header["sector_count"]),
                "sector_size": int(header["sector_size"]),
                "sha256": {
                    "input_file": input_digest.hexdigest(),
                    "raw_image": raw_digest.hexdigest(),
                },
            }
            temporary_metadata = write_metadata_file(metadata_path, metadata)

        os.replace(temporary_output, output_path)
        temporary_output = None
        os.chmod(output_path, OUTPUT_MODE)

        if include_metadata:
            assert temporary_metadata is not None
            os.replace(temporary_metadata, metadata_path)
            temporary_metadata = None
            os.chmod(metadata_path, OUTPUT_MODE)
    except CopyDiskError:
        raise
    except OSError as error:
        raise CopyDiskError(error.strerror or str(error)) from error
    finally:
        if temporary_output is not None:
            temporary_output.unlink(missing_ok=True)
        if temporary_metadata is not None:
            temporary_metadata.unlink(missing_ok=True)


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Convert an HP COPYDISK image to a standard raw disk image."
    )
    parser.add_argument(
        "--all",
        action="store_true",
        dest="include_metadata",
        help="also write derived metadata to <outputFile>.json",
    )
    parser.add_argument("inputFile", type=Path, help="HP COPYDISK input file")
    parser.add_argument("outputFile", type=Path, help="raw disk image output file")
    return parser


def main(argv: list[str] | None = None) -> int:
    arguments = build_argument_parser().parse_args(argv)
    try:
        convert(
            arguments.inputFile,
            arguments.outputFile,
            arguments.include_metadata,
        )
    except CopyDiskError as error:
        print(f"hpCOPYDISK: error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

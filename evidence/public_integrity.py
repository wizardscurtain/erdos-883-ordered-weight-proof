"""Read-only, fail-closed integrity boundary for the public derivative.

Integrity is relative to the manifest in a trusted Git version or to an independently
supplied manifest digest. It is not a mathematical proof or a digital signature.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from enum import Enum
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Mapping

MANIFEST_NAME = "PUBLIC_MANIFEST.json"
SCHEMA = "erdos883-public-evidence-v1"
DIGEST = re.compile(r"[0-9a-f]{64}\Z")


class IntegrityError(ValueError):
    """Malformed package, unsafe path, missing artifact, or wrong bytes."""


class OriginKind(str, Enum):
    UNCHANGED = "unchanged"
    REVISED = "revised"
    NEW = "new"


@dataclass(frozen=True)
class Artifact:
    path: str
    size: int
    sha256: str
    origin: OriginKind
    source_sha256: str | None


@dataclass(frozen=True)
class VerifiedInventory:
    manifest_sha256: str
    files: int
    bytes: int
    original_bytes_preserved: int
    revised_files: int
    new_files: int

    def as_dict(self) -> dict[str, str | int]:
        return dict(self.__dict__)


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise IntegrityError(f"Duplicate JSON key: {key}")
        value[key] = item
    return value


def object_value(value: object, label: str) -> Mapping[str, object]:
    if not isinstance(value, dict) or any(not isinstance(k, str) for k in value):
        raise IntegrityError(f"{label}: expected an object")
    return value


def validate_path(value: object) -> str:
    if not isinstance(value, str) or not value or "\\" in value:
        raise IntegrityError("Artifact path must be a nonempty POSIX relative path")
    p = PurePosixPath(value)
    if (p.is_absolute() or p.as_posix() != value
            or any(part in ("", ".", "..") for part in value.split("/"))
            or any(ord(c) < 32 or ord(c) == 127 for c in value)
            or ":" in value or value == MANIFEST_NAME):
        raise IntegrityError(f"Unsafe or noncanonical artifact path: {value!r}")
    return value


def validate_digest(value: object) -> str:
    if not isinstance(value, str) or DIGEST.fullmatch(value) is None:
        raise IntegrityError("Expected a lowercase SHA-256 digest")
    return value


def parse_artifact(path: str, value: object) -> Artifact:
    item = object_value(value, path)
    if set(item) != {"bytes", "sha256", "origin", "source_sha256"}:
        raise IntegrityError(f"{path}: unexpected artifact fields")
    size = item["bytes"]
    if type(size) is not int or size < 0:
        raise IntegrityError(f"{path}: invalid byte length")
    digest = validate_digest(item["sha256"])
    try:
        origin = OriginKind(item["origin"])
    except (TypeError, ValueError):
        raise IntegrityError(f"{path}: invalid origin kind") from None
    source = item["source_sha256"]
    if origin is OriginKind.NEW:
        if source is not None:
            raise IntegrityError(f"{path}: a new file cannot claim historical bytes")
    else:
        source = validate_digest(source)
        if (origin is OriginKind.UNCHANGED) != (source == digest):
            raise IntegrityError(f"{path}: origin classification contradicts digests")
    return Artifact(validate_path(path), size, digest, origin, source)


def verify_package(root: Path, expected_manifest: str | None = None) -> VerifiedInventory:
    if root.is_symlink():
        raise IntegrityError("Package root cannot be a symlink")
    root = root.resolve(strict=True)
    manifest = root / MANIFEST_NAME
    if manifest.is_symlink() or not manifest.is_file():
        raise IntegrityError("Missing or unsafe public manifest")
    raw = manifest.read_bytes()
    manifest_digest = hashlib.sha256(raw).hexdigest()
    if expected_manifest is not None and manifest_digest != validate_digest(expected_manifest):
        raise IntegrityError("Public manifest digest does not match the trusted digest")
    try:
        data = object_value(json.loads(raw, object_pairs_hook=unique_object), "manifest")
    except (UnicodeError, json.JSONDecodeError) as error:
        raise IntegrityError(f"Invalid manifest JSON: {error}") from error
    if set(data) != {"schema", "release", "files"} or data["schema"] != SCHEMA:
        raise IntegrityError("Unknown public manifest schema or fields")
    if data["release"] != "public-derivative-20261012-v1":
        raise IntegrityError("Unknown public derivative release")
    entries = object_value(data["files"], "files")
    if not entries:
        raise IntegrityError("Empty public manifest")
    artifacts = tuple(parse_artifact(path, item) for path, item in entries.items())
    expected = {item.path for item in artifacts}
    if len({p.casefold() for p in expected}) != len(expected):
        raise IntegrityError("Case-colliding artifact paths")
    actual: set[str] = set()
    for p in root.rglob("*"):
        relative = p.relative_to(root).as_posix()
        if p.is_symlink():
            raise IntegrityError(f"Symlink is not an artifact: {relative}")
        if p.is_file():
            if relative != MANIFEST_NAME:
                actual.add(relative)
        elif not p.is_dir():
            raise IntegrityError(f"Special filesystem object: {relative}")
    if actual != expected:
        raise IntegrityError(
            f"Inventory differs; missing={sorted(expected - actual)[:8]}, "
            f"unexpected={sorted(actual - expected)[:8]}"
        )

    def check(item: Artifact) -> None:
        path = root / item.path
        if not path.resolve(strict=True).is_relative_to(root):
            raise IntegrityError(f"Artifact escapes package: {item.path}")
        if path.stat().st_size != item.size or sha_file(path) != item.sha256:
            raise IntegrityError(f"Artifact bytes differ: {item.path}")

    # Artifact reads are independent; the inventory is validated before this stage.
    with ThreadPoolExecutor(max_workers=4) as pool:
        tuple(pool.map(check, artifacts))
    return VerifiedInventory(
        manifest_digest, len(artifacts), sum(a.size for a in artifacts),
        sum(a.origin is OriginKind.UNCHANGED for a in artifacts),
        sum(a.origin is OriginKind.REVISED for a in artifacts),
        sum(a.origin is OriginKind.NEW for a in artifacts),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--expect-manifest")
    args = parser.parse_args()
    try:
        result = verify_package(args.root, args.expect_manifest)
    except (IntegrityError, OSError) as error:
        print(f"PUBLIC_INTEGRITY_FAILED: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"status": "PUBLIC_INTEGRITY_PASSED", **result.as_dict()}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Synthetic negative tests for the public packaging boundary, not theorem tests."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from public_integrity import IntegrityError, MANIFEST_NAME, SCHEMA, verify_package


class IntegrityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.data = b"mathematical fixture\n"
        (self.root / "record.txt").write_bytes(self.data)
        self.digest = hashlib.sha256(self.data).hexdigest()
        self.manifest = {
            "schema": SCHEMA,
            "release": "public-derivative-20261012-v1",
            "files": {"record.txt": {
                "bytes": len(self.data), "sha256": self.digest,
                "origin": "unchanged", "source_sha256": self.digest,
            }},
        }
        self.write()

    def write(self) -> None:
        (self.root / MANIFEST_NAME).write_text(json.dumps(self.manifest))

    def bad(self) -> None:
        self.write()
        with self.assertRaises((IntegrityError, OSError)):
            verify_package(self.root)

    def test_valid_package(self) -> None:
        r = verify_package(self.root)
        self.assertEqual((r.files, r.original_bytes_preserved), (1, 1))

    def test_trusted_digest(self) -> None:
        digest = hashlib.sha256((self.root / MANIFEST_NAME).read_bytes()).hexdigest()
        self.assertEqual(verify_package(self.root, digest).manifest_sha256, digest)

    def test_wrong_trusted_digest(self) -> None:
        with self.assertRaises(IntegrityError):
            verify_package(self.root, "0" * 64)

    def test_missing_artifact(self) -> None:
        (self.root / "record.txt").unlink()
        self.bad()

    def test_extra_artifact(self) -> None:
        (self.root / "extra.txt").write_text("not in inventory")
        self.bad()

    def test_changed_bytes(self) -> None:
        (self.root / "record.txt").write_bytes(b"x" * len(self.data))
        self.bad()

    def test_changed_length(self) -> None:
        (self.root / "record.txt").write_bytes(b"x")
        self.bad()

    def test_boolean_byte_count(self) -> None:
        self.manifest["files"]["record.txt"]["bytes"] = True
        self.bad()

    def test_negative_byte_count(self) -> None:
        self.manifest["files"]["record.txt"]["bytes"] = -1
        self.bad()

    def test_bad_digest(self) -> None:
        self.manifest["files"]["record.txt"]["sha256"] = "not-a-digest"
        self.bad()

    def test_inconsistent_unchanged_origin(self) -> None:
        self.manifest["files"]["record.txt"]["source_sha256"] = "0" * 64
        self.bad()

    def test_inconsistent_revised_origin(self) -> None:
        self.manifest["files"]["record.txt"]["origin"] = "revised"
        self.bad()

    def test_valid_new_origin(self) -> None:
        item = self.manifest["files"]["record.txt"]
        item["origin"], item["source_sha256"] = "new", None
        self.write()
        self.assertEqual(verify_package(self.root).new_files, 1)

    def test_new_origin_cannot_claim_source(self) -> None:
        self.manifest["files"]["record.txt"]["origin"] = "new"
        self.bad()

    def test_unknown_origin(self) -> None:
        self.manifest["files"]["record.txt"]["origin"] = "verified-theorem"
        self.bad()

    def test_unknown_schema(self) -> None:
        self.manifest["schema"] = "historical-manifest"
        self.bad()

    def test_unknown_release(self) -> None:
        self.manifest["release"] = "unknown"
        self.bad()

    def test_empty_inventory(self) -> None:
        self.manifest["files"] = {}
        self.bad()

    def test_unexpected_fields(self) -> None:
        self.manifest["files"]["record.txt"]["skip_hash"] = True
        self.bad()

    def test_duplicate_keys(self) -> None:
        (self.root / MANIFEST_NAME).write_text('{"schema":"x","schema":"y"}')
        with self.assertRaises(IntegrityError):
            verify_package(self.root)

    def test_invalid_json(self) -> None:
        (self.root / MANIFEST_NAME).write_text("{")
        with self.assertRaises(IntegrityError):
            verify_package(self.root)

    def test_unsafe_paths(self) -> None:
        item = self.manifest["files"]["record.txt"]
        for bad in ("../record.txt", "/record.txt", "./record.txt", "a//b", "a/../b",
                    "a\\b", "C:/b", "a\nb", MANIFEST_NAME):
            with self.subTest(path=bad):
                self.manifest["files"] = {bad: item}
                self.bad()

    def test_symlink_artifact(self) -> None:
        (self.root / "record.txt").unlink()
        (self.root / "record.txt").symlink_to("/dev/null")
        self.bad()

    def test_symlink_directory(self) -> None:
        (self.root / "link").symlink_to(self.root, target_is_directory=True)
        self.bad()

    def test_symlink_manifest(self) -> None:
        (self.root / MANIFEST_NAME).unlink()
        (self.root / MANIFEST_NAME).symlink_to(self.root / "record.txt")
        with self.assertRaises(IntegrityError):
            verify_package(self.root)

    def test_case_collision(self) -> None:
        self.manifest["files"]["Record.txt"] = self.manifest["files"]["record.txt"].copy()
        self.bad()


if __name__ == "__main__":
    unittest.main(verbosity=2)

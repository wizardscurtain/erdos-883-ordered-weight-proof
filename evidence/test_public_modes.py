"""Regression tests for verification-mode selection and failure propagation.

The LRAT negative control deliberately uses a fake checker that prints VERIFIED
but exits unsuccessfully. Passing this test means that fake success is rejected.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent
LEDGER = ROOT / "hall_tail_20261010/code/coverage_ledger2.py"


class ModeTests(unittest.TestCase):
    def run_ledger(self, *args: str, optimized: str | None = None,
                   tools: str | None = None) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env.pop("PYTHONOPTIMIZE", None)
        env.pop("DRAT_TOOLS", None)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        if tools is not None:
            env["DRAT_TOOLS"] = tools
        flags = ["-B"] + ([optimized] if optimized else [])
        return subprocess.run([sys.executable, *flags, str(LEDGER), *args],
                              env=env, text=True, capture_output=True, timeout=120)

    def test_typo_does_not_downgrade_deep_to_quick(self) -> None:
        result = self.run_ledger("--depe")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrecognized arguments", result.stderr)

    def test_unknown_option_rejected(self) -> None:
        result = self.run_ledger("--skip-integrity")
        self.assertNotEqual(result.returncode, 0)

    def test_scanner_unknown_argument_does_not_launch_full_replay(self) -> None:
        scanner = ROOT / "hall_tail_20261010/code/replay_scanners.py"
        result = subprocess.run(
            [sys.executable, "-B", str(scanner), "--n", "4025", "--out", "/tmp/not-used"],
            capture_output=True, text=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unrecognized arguments", result.stderr)
        self.assertNotIn("rows to compute", result.stdout)

    def test_scanner_output_cannot_pollute_manifest_tree(self) -> None:
        scanner = ROOT / "hall_tail_20261010/code/replay_scanners.py"
        result = subprocess.run(
            [sys.executable, "-B", str(scanner), "--out", str(ROOT / "not-created")],
            capture_output=True, text=True, timeout=10)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside evidence", result.stderr)
        self.assertFalse((ROOT / "not-created").exists())

    def test_optimized_python_rejected(self) -> None:
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = self.run_ledger(optimized=flag)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Optimization disables historical assertions", result.stderr)

    def test_missing_deep_tool_configuration_rejected(self) -> None:
        result = self.run_ledger("--deep")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires explicit DRAT_TOOLS", result.stderr)

    @unittest.skipUnless(os.name == "posix", "Shell checker fixture requires POSIX")
    def test_verified_marker_with_failure_exit_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            checker = Path(td) / "lrat-check"
            checker.write_text("#!/bin/sh\nprintf 'c VERIFIED\\n'\nexit 42\n")
            checker.chmod(0o700)
            result = self.run_ledger("--deep", tools=td)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("lrat-check failed", result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)

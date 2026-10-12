#!/usr/bin/env python3
"""WORKFLOW GATE: every tracked Python file under bgw/ and scripts/ compiles.

Generators and certificate scripts that no test imports could otherwise carry a syntax
error through both gates. This happened once: R28-R3 left an unterminated string in
bgw/endpoint/make_review.py, and the full gate passed because nothing imported it. This
test only compiles the source text (no import, no execution, no bytecode written).
"""
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def tracked_python():
    out = subprocess.run(["git", "ls-files", "bgw", "scripts"], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout.split()
    return [ROOT / p for p in out if p.endswith(".py")]


class Compiles(unittest.TestCase):
    def test_every_tracked_script_compiles(self):
        files = tracked_python()
        self.assertGreater(len(files), 0)
        bad = []
        for p in files:
            try:
                compile(p.read_text(), str(p.relative_to(ROOT)), "exec")
            except SyntaxError as e:
                bad.append(f"{p.relative_to(ROOT)}:{e.lineno}: {e.msg}")
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()

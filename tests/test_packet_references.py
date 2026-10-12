#!/usr/bin/env python3
"""WORKFLOW GATE: the review packet's factual references must resolve.

This is deliberately NOT the deleted prose suite. It asserts nothing about
wording, tone, or which claims are made. It checks one thing: that every file,
manifest and source path the packet points a reader at actually exists.

It was restored when the packet became something we intend to send. The 41
prose tests were deleted on the explicit bet that "a document nobody has sent
does not justify guarding its wording"; that bet ends the moment it is sent,
and a reviewer following a dead reference is a real cost, not a style issue.
The specific failure that motivates the first test is one the author committed:
in T-004-R5 two handoff filenames were invented and written into the evidence
index, and no check noticed.
"""

import pathlib
import re
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
PACKET = ROOT / "bgw" / "weighted_audit" / "REVIEW_PACKET.md"
HANDOFFS = ROOT / ".agent" / "handoffs"


class PacketReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = PACKET.read_text()

    def test_every_named_handoff_exists(self):
        """T-004-R5 invented `T-003-R3.md` and `T-003-R4.md`. Nothing caught it."""
        named = sorted(set(re.findall(r"`(T-\d{3}(?:-R\d)?(?:-[A-Z-]+)?\.md)`",
                                      self.text)))
        self.assertTrue(named, "expected the packet to name handoffs")
        missing = [n for n in named if not (HANDOFFS / n).exists()]
        self.assertEqual(missing, [],
                         "the packet sends a reviewer to handoffs that do not "
                         "exist")

    def test_every_named_repo_path_exists(self):
        """Source and evidence paths a reviewer is told to open."""
        paths = set(re.findall(
            r"`((?:bgw|tests|scripts|GW|docs|artifacts)/[\w./-]+?)`", self.text))
        # a trailing glob or wildcard is a family, not a file
        concrete = {p for p in paths if "*" not in p and not p.endswith("/")}
        missing = sorted(p for p in concrete if not (ROOT / p).exists())
        self.assertEqual(missing, [],
                         "the packet names repository paths that do not exist")

    def test_current_manifest_reference_matches_the_provenance_test(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "tpc", ROOT / "tests" / "test_provenance_committed.py")
        tpc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(tpc)
        current = [p.name for p in tpc.CURRENT_MANIFESTS]
        self.assertEqual(len(current), 1, "expected one current manifest")
        self.assertIn(f"bgw/weighted_audit/{current[0]}", self.text,
                      "the packet must name the manifest the provenance test "
                      "actually treats as current")

    def test_correction_rows_are_contiguously_numbered(self):
        rows = re.findall(r"^\| (\d+) \| .+ \| .+ \| .+ \|$", self.text,
                          flags=re.M)
        self.assertTrue(rows, "expected a correction table")
        self.assertEqual([int(n) for n in rows],
                         list(range(1, len(rows) + 1)),
                         "correction rows must be numbered contiguously")

    def test_unvalidated_material_is_flagged_as_such(self):
        """Structural: T-006 claims must sit under an explicit warning.

        Not a wording check -- it verifies the section exists and that each
        T-006 claim id appears inside it, so a reader cannot meet C12-C14
        without meeting the statement that they had no second reviewer.
        """
        head, sep, tail = self.text.partition(
            "## 4.9 T-006 material: NOT independently validated")
        self.assertTrue(sep, "the unvalidated-material section is missing")
        for claim in ("C12", "C13", "C14"):
            self.assertIn(claim, tail.split("## 6.")[0],
                          f"{claim} is not covered by the warning section")


if __name__ == "__main__":
    unittest.main(verbosity=2)

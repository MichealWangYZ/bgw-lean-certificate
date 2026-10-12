#!/usr/bin/env python3
"""WORKFLOW GATE: every test module is classified into exactly one gate.

Without this, adding `tests/test_something.py` and forgetting to list it in
`scripts/gates.py` would mean it runs under neither gate. The suite would look
green and the file would never execute -- the worst failure mode available to a
test system, because it is silent and looks like success.
"""

import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import gates  # noqa: E402


def discovered():
    return {f"tests.{p.stem}" for p in (ROOT / "tests").glob("test_*.py")}


class GatePartitionTests(unittest.TestCase):
    def test_every_module_is_classified(self):
        classified = set(gates.SCIENTIFIC) | set(gates.WORKFLOW)
        missing = discovered() - classified
        self.assertEqual(
            missing, set(),
            "these test modules are in neither gate, so they would not run "
            "under `verify.py --gate scientific` or `--gate workflow`; add "
            "them to scripts/gates.py")

    def test_no_module_is_in_both_gates(self):
        both = set(gates.SCIENTIFIC) & set(gates.WORKFLOW)
        self.assertEqual(both, set(), "a module must belong to exactly one gate")

    def test_no_gate_names_a_module_that_does_not_exist(self):
        stale = (set(gates.SCIENTIFIC) | set(gates.WORKFLOW)) - discovered()
        self.assertEqual(stale, set(),
                         "scripts/gates.py names test modules that are gone")




if __name__ == "__main__":
    unittest.main(verbosity=2)

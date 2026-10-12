#!/usr/bin/env python3
"""SCIENTIFIC GATE: LL-C2A, the arbitrary finite ring family.

The general claims are Lean theorems (`GW/LL/StructuralRing.lean`); this file
keeps the executable evidence deliberately small. It checks the structural
family's exact rational values at orders k = 0..4 against the independent
Python reference, and that the required adversarial mutations are detected.

Exact `fractions.Fraction` arithmetic; no tolerances. The reference never reads
the Lean output as an expected-answer column.
"""

from fractions import Fraction as F
from itertools import product
import importlib.util
import json
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "ll_ring_reference", ROOT / "ll" / "ring_reference.py")
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

_espec = importlib.util.spec_from_file_location(
    "ll_evidence", ROOT / "ll" / "evidence.py")
evidence = importlib.util.module_from_spec(_espec)
_espec.loader.exec_module(evidence)

EvidenceError = evidence.EvidenceError

# C2B opening cleanup. This module previously did its own reading: it keyed
# rows into a dict (losing a wrong duplicate), took its coverage from the
# candidate's own `orders`, and never read a row's N/i/j. All three are now the
# shared validator's job, and the coverage comes from the specification.
ORDERS = list(evidence.EXPECTED_C2A_ORDERS)

VALUES = ROOT / "artifacts" / "ll-c2a" / "structural_values.json"

#: Inputs duplicated from `LLC2AMain.lean`. Inputs only; no expected outputs.
FIXTURES = {
    "N2-pd": dict(G=ref.mat([[2, 1], [1, 2]]), v=ref.mat([[1, 2], [2, 3]]), i=0, j=1),
    "N2-rational": dict(
        G=ref.mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]),
        v=ref.mat([[F(2, 5), F(1, 7)], [F(1, 7), F(-4, 3)]]), i=1, j=0),
    "N3-pd": dict(
        G=ref.mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=ref.mat([[1, 2, 3], [2, 0, 1], [3, 1, 2]]), i=0, j=1),
}


def contract_edges(fx, k, edges, sign_offset=0, divide=True):
    """Contract an arbitrary edge set, for building mutants."""
    G, v, i, j = fx["G"], fx["v"], fx["i"], fx["j"]
    n = len(G)
    props, ints = edges
    internal = sorted({s for e in props + ints for s in e if s[0] != 'e'})
    total = F(0)
    for assignment in product(range(n), repeat=len(internal)):
        idx = dict(zip(internal, assignment))
        idx[('e', 0)], idx[('e', 1)] = i, j
        term = F(1)
        for (u, w) in props:
            term *= G[idx[u]][idx[w]]
        for (u, w) in ints:
            term *= v[idx[u]][idx[w]]
        total += term
    divisor = 2 ** k if divide else 1
    return ((-1) ** (len(ints) + sign_offset)) * total / divisor


class StructuralFamilyAgreement(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(VALUES.read_text())
        cls.rows = evidence.validate_c2a(cls.data, FIXTURES)
        cls.orders = ORDERS

    def test_fixture_sets_match(self):
        self.assertEqual(set(self.rows), set(FIXTURES))

    def test_orders_reach_at_least_three(self):
        """The coverage is the specification's, not the candidate's."""
        self.assertGreaterEqual(max(ORDERS), 3,
                                "the task requires exact evidence at k >= 3")
        self.assertIn(0, ORDERS)
        self.assertEqual(ORDERS, self.data["orders"],
                         "validator must have rejected a narrowed coverage")

    def test_a_nonscalar_fixture_is_present(self):
        self.assertTrue(any(len(fx["G"]) > 1 for fx in FIXTURES.values()))

    def test_v_and_B_do_not_commute_somewhere(self):
        found = any(ref.matmul(fx["v"], ref.hadamard_square(fx["G"]))
                    != ref.matmul(ref.hadamard_square(fx["G"]), fx["v"])
                    for fx in FIXTURES.values())
        self.assertTrue(found)

    def test_lean_matches_the_reference_exactly_at_every_order(self):
        for name, fx in FIXTURES.items():
            for k in self.orders:
                expected = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], k)
                got = F(self.rows[name][f"k{k}"])
                self.assertEqual(got, expected, f"{name} k={k}")

    def test_the_two_python_routes_agree_at_every_order(self):
        for name, fx in FIXTURES.items():
            for k in self.orders:
                a = ref.ring_contribution_matrix(fx["G"], fx["v"], fx["i"], fx["j"], k)
                b = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
                self.assertEqual(a, b, f"{name} k={k}")

    def test_symmetry_factor_is_two_to_the_k(self):
        for k in self.orders:
            self.assertEqual(ref.symmetry_factor(k), 2 ** k)


class MutationDetection(unittest.TestCase):
    """The four mutant classes the task requires, at k >= 3."""

    WITNESS = "N2-pd"
    KS = (3, 4)

    def fixture(self):
        return FIXTURES[self.WITNESS]

    def good(self, k):
        fx = self.fixture()
        return ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)

    def test_missing_bubble_factor_of_two_is_detected(self):
        fx = self.fixture()
        for k in self.KS:
            bad = contract_edges(fx, k, ref.ring_edges(k), divide=False)
            self.assertNotEqual(self.good(k), bad, f"k={k}")
            self.assertEqual(bad, self.good(k) * 2 ** k)

    def test_wrong_interaction_chain_attachment_is_detected(self):
        """Enter and leave each bubble on the same side."""
        for k in self.KS:
            extI, extJ = ('e', 0), ('e', 1)
            props = [(extI, extJ)]
            for m in range(k):
                props += [(('a', m), ('b', m))] * 2
            ints = ([(extI, ('a', 0))]
                    + [(('a', m), ('a', m + 1)) for m in range(k - 1)]
                    + [(('a', k - 1), extJ)])
            bad = contract_edges(self.fixture(), k, (props, ints))
            self.assertNotEqual(self.good(k), bad, f"k={k}")

    def test_a_duplicated_bubble_is_detected(self):
        """Same chain, but one bubble's propagators appear twice over."""
        for k in self.KS:
            props, ints = ref.ring_edges(k)
            bad_props = props + [(('a', 0), ('b', 0))] * 2
            bad = contract_edges(self.fixture(), k, (bad_props, ints))
            self.assertNotEqual(self.good(k), bad, f"k={k}")

    def test_a_dropped_bubble_is_detected(self):
        """One bubble reduced to a single propagator instead of two."""
        for k in self.KS:
            props, ints = ref.ring_edges(k)
            bad_props = list(props)
            bad_props.remove((('a', 0), ('b', 0)))
            bad = contract_edges(self.fixture(), k, (bad_props, ints))
            self.assertNotEqual(self.good(k), bad, f"k={k}")

    def test_the_family_is_not_accidentally_order_shifted(self):
        """`ring k` must not equal `ring (k±1)` on the witness."""
        for k in self.KS:
            self.assertNotEqual(self.good(k), self.good(k - 1), f"k={k}")

    def test_permitted_internal_relabeling_changes_nothing(self):
        """Renaming internal sites is a change of summation variable only."""
        for k in self.KS:
            props, ints = ref.ring_edges(k)
            swap = {}
            for m in range(k):
                swap[('a', m)] = ('b', m)
                swap[('b', m)] = ('a', m)
            rename = lambda s: swap.get(s, s)
            relabeled = ([(rename(u), rename(w)) for u, w in props],
                         [(rename(u), rename(w)) for u, w in ints])
            same = contract_edges(self.fixture(), k, relabeled)
            self.assertEqual(self.good(k), same, f"k={k}")


def synthetic_table(orders=None):
    """A correct C2A table built from the independent reference.

    Deliberately not the Lean artifact: these probe the reader, so they must
    run even when nothing has been generated, and the mutations below must not
    disturb a real file. The values are the reference's, so the control passes
    the numeric comparison as well as the structural one.
    """
    orders = list(evidence.EXPECTED_C2A_ORDERS) if orders is None else list(orders)
    values = []
    for name, fx in FIXTURES.items():
        row = {"name": name, "N": len(fx["G"]), "i": fx["i"], "j": fx["j"]}
        for k in orders:
            val = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], k)
            # the evaluators' own encoding: `s!"{x.num}/{x.den}"`
            row[f"k{k}"] = f"{val.numerator}/{val.denominator}"
        values.append(row)
    return {"orders": orders, "values": values}


class ReaderRejectsBadEvidence(unittest.TestCase):
    """The four false passes the C2A review measured, plus controls.

    Before the C2B cleanup this module read the table itself. All 13 tests
    passed on a wrong duplicate row, on `i = j = 999`, on a falsely declared
    `N = 999`, and on `orders = [0, 3]` that hid a wrong `k4`. Each of those
    inputs must now be rejected by `ll/evidence.py`.
    """

    def check(self, data):
        return evidence.validate_c2a(data, FIXTURES)

    def test_the_synthetic_control_validates(self):
        rows = self.check(synthetic_table())
        self.assertEqual(set(rows), set(FIXTURES))

    def test_wrong_duplicate_before_correct_row_is_rejected(self):
        data = synthetic_table()
        bad = dict(data["values"][0])
        bad["k3"] = "999/1"
        data["values"].insert(0, bad)          # wrong row first, correct after
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("duplicate", str(cm.exception))

    def test_impossible_external_indices_are_rejected(self):
        data = synthetic_table()
        row = data["values"][0]
        row["i"] = row["j"] = 999
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertRegex(str(cm.exception), "fixture says|out of bounds")

    def test_a_falsely_declared_dimension_is_rejected(self):
        data = synthetic_table()
        data["values"][0]["N"] = 999
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("fixture says", str(cm.exception))

    def test_narrowed_coverage_hiding_a_wrong_value_is_rejected(self):
        """`orders = [0, 3]` previously chose what the candidate was compared
        against; the wrong `k4` column was simply never read."""
        data = synthetic_table(orders=[0, 3])
        for row in data["values"]:
            row["k4"] = "999/1"                # wrong, and formerly unread
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_a_value_column_outside_the_coverage_is_rejected(self):
        data = synthetic_table()
        data["values"][0]["k9"] = "999/1"
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_a_missing_value_column_is_rejected(self):
        data = synthetic_table()
        del data["values"][1]["k4"]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("missing value columns", str(cm.exception))

    def test_boolean_cannot_masquerade_as_an_index(self):
        data = synthetic_table()
        row = next(r for r in data["values"] if r["i"] == 0)
        row["i"] = False
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("not int", str(cm.exception))

    def test_missing_and_extra_fixtures_are_rejected(self):
        data = synthetic_table()
        dropped = data["values"].pop()
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("inventory mismatch", str(cm.exception))
        data["values"].append(dropped)
        extra = dict(dropped)
        extra["name"] = "not-a-fixture"
        data["values"].append(extra)
        with self.assertRaises(EvidenceError):
            self.check(data)

    def test_an_ordinary_wrong_value_is_still_caught(self):
        """Structural validation must not have displaced the numbers."""
        data = synthetic_table()
        rows = self.check(data)                # structurally valid
        rows["N2-pd"]["k3"] = "0/1"
        fx = FIXTURES["N2-pd"]
        expected = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], 3)
        self.assertNotEqual(F(rows["N2-pd"]["k3"]), expected)


if __name__ == "__main__":
    unittest.main(verbosity=2)

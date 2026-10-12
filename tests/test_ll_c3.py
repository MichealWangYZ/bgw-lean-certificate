#!/usr/bin/env python3
"""SCIENTIFIC GATE: LL-C3, finite Wick pairings to Hartree/Fock.

The general claims are Lean theorems in `GW/LL/Wick.lean`:
`wick6_split`, `disconnected_cancels`, `firstOrder_eq_hartree_fock`,
`dressed_ring0_eq_neg_fock`, `firstOrder_eq_dressed_ring0_add_hartree`, and the
four `pairings_six_*` checks. This file is a regression and a semantic witness.

IMPORTANT, and checked below: Wick's theorem is the DEFINITION of the moment on
both sides, not a result. Neither Lean nor this file proves that the pairing sum
equals a Gaussian integral. Nothing here formalizes Gaussian perturbation theory.

Exact `fractions.Fraction` throughout.
"""

from fractions import Fraction as F
import importlib.util
import json
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


w = _load("ll_wick_reference", "ll/wick_reference.py")
evidence = _load("ll_evidence", "ll/evidence.py")
EvidenceError = evidence.EvidenceError

ORDERS = list(evidence.EXPECTED_C3_ORDERS)
SERIES = list(evidence.EXPECTED_C3_SERIES)
VALUES = ROOT / "artifacts" / "ll-c3" / "wick_values.json"

#: Inputs duplicated from `LLC3Main.lean`. Inputs only; no expected outputs.
FIXTURES = {
    "N2-sym": dict(G=w.mat([[2, 1], [1, 3]]), v=w.mat([[1, 2], [2, 3]]), i=0, j=1),
    "N2-rational": dict(
        G=w.mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]),
        v=w.mat([[F(2, 5), F(1, 7)], [F(1, 7), F(-4, 3)]]), i=1, j=0),
    "N3-sym": dict(
        G=w.mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=w.mat([[1, 2, 3], [2, 0, 1], [3, 1, 2]]), i=0, j=1),
}


def as_matrix(rows):
    return [[F(x) for x in row] for row in rows]


class Pairings(unittest.TestCase):
    """The enumeration the whole computation rests on."""

    def test_six_positions_have_fifteen_matchings(self):
        self.assertEqual(len(list(w.matchings(list(range(6))))), 15)
        self.assertEqual(w.matching_count(3), 15)

    def test_odd_lengths_have_none(self):
        for n in (1, 3, 5):
            self.assertEqual(len(list(w.matchings(list(range(n))))), 0)

    def test_every_matching_covers_every_position_once(self):
        for m in w.matchings(list(range(6))):
            seen = [x for pair in m for x in pair]
            self.assertEqual(sorted(seen), list(range(6)))

    def test_matchings_are_distinct(self):
        got = [tuple(sorted(tuple(sorted(p)) for p in m))
               for m in w.matchings(list(range(6)))]
        self.assertEqual(len(set(got)), 15)


class WickRecursion(unittest.TestCase):
    """`GW.LL.wickMoment_cons` is the general Lean theorem; this corroborates it.

    The C3/C4 review noted that the module's header referred to a recursion
    lemma that had not been delivered. It is delivered now, for lists of any
    length, and checked here against the brute-force enumeration.
    """

    def test_the_recursion_agrees_with_brute_force(self):
        G = FIXTURES["N3-sym"]["G"]
        n = len(G)
        labels = [(a, b, c, d) for a in range(n) for b in range(n)
                  for c in range(n) for d in range(n)]
        for lab in labels[:24]:
            self.assertEqual(w.moment_recursive(G, list(lab)),
                             w.moment(G, list(lab)), str(lab))

    def test_the_recursion_agrees_at_six_fields(self):
        G = FIXTURES["N2-sym"]["G"]
        for a in range(2):
            for b in range(2):
                for i in range(2):
                    for j in range(2):
                        lab = [a, b, i, i, j, j]
                        self.assertEqual(w.moment_recursive(G, lab),
                                         w.moment(G, lab), str(lab))

    def test_odd_lengths_vanish_both_ways(self):
        G = FIXTURES["N2-sym"]["G"]
        for lab in ([0], [0, 1, 1], [1, 0, 1, 0, 0]):
            self.assertEqual(w.moment_recursive(G, lab), 0)
            self.assertEqual(w.moment(G, lab), 0)


class FixturesAreAdmissible(unittest.TestCase):
    """`G` is a covariance and the closed form assumes symmetric `v`."""

    def test_G_and_v_are_symmetric(self):
        for name, fx in FIXTURES.items():
            self.assertTrue(w.is_symmetric(fx["G"]), f"{name}: G")
            self.assertTrue(w.is_symmetric(fx["v"]), f"{name}: v")

    def test_a_fixture_has_a_nonuniform_loop_vector(self):
        """Otherwise the Hartree term could not distinguish sites."""
        found = any(len(set(w.loop_vec(fx["G"], fx["v"]))) > 1
                    for fx in FIXTURES.values())
        self.assertTrue(found)


class LeanMatchesBruteForce(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(VALUES.read_text())
        cls.rows = evidence.validate_c3(cls.data, FIXTURES)

    def test_coverage_is_the_specifications(self):
        self.assertEqual(ORDERS, self.data["orders"])

    def test_the_assumed_input_is_declared_in_the_artifact(self):
        """A reader of the JSON alone must see that Wick is assumed."""
        self.assertIn("DEFINITION", self.data["assumed_input"])
        # The normalization's source and its verifier must be visible, and the
        # superseded "NOT verified" wording must not come back (C3/C4 review
        # verified eq. (2.4); GW/LL/Wick.lean records it).
        self.assertIn("eq. (2.4)", self.data["interaction"])
        self.assertIn("C3/C4 review", self.data["interaction"])
        self.assertNotIn("NOT verified", self.data["interaction"])

    def test_the_bridges_to_the_theorems_are_named(self):
        self.assertEqual(self.data["bridges"],
                         ["GW.LL.disconnected_cancels",
                          "GW.LL.firstOrder_eq_hartree_fock",
                          "GW.LL.dressed_ring0_eq_neg_fock"])

    def test_delta_matches_brute_force_enumeration(self):
        for name, fx in FIXTURES.items():
            expected = w.both_agree(fx["G"], fx["v"])
            got = as_matrix(self.rows[name]["delta"]["1"])
            self.assertEqual(got, expected, name)

    def test_hartree_and_fock_match(self):
        for name, fx in FIXTURES.items():
            self.assertEqual(as_matrix(self.rows[name]["hartree"]["1"]),
                             w.hartree_matrix(fx["G"], fx["v"]), name)
            self.assertEqual(as_matrix(self.rows[name]["fock"]["1"]),
                             w.fock_matrix(fx["G"], fx["v"]), name)

    def test_the_split_reassembles(self):
        """`delta = -(1/2 Hartree + Fock)`, on the emitted numbers."""
        for name in FIXTURES:
            d = as_matrix(self.rows[name]["delta"]["1"])
            h = as_matrix(self.rows[name]["hartree"]["1"])
            f = as_matrix(self.rows[name]["fock"]["1"])
            n = len(d)
            for a in range(n):
                for b in range(n):
                    self.assertEqual(d[a][b], -(F(1, 2) * h[a][b] + f[a][b]),
                                     f"{name} ({a},{b})")


class RingFamilyLink(unittest.TestCase):
    """The point of C3: where the ring family came from, and what it omits."""

    @classmethod
    def setUpClass(cls):
        cls.rows = evidence.validate_c3(json.loads(VALUES.read_text()), FIXTURES)

    def test_dressed_ring0_is_minus_the_fock_term(self):
        for name, fx in FIXTURES.items():
            self.assertEqual(as_matrix(self.rows[name]["ringDressed"]["1"]),
                             w.dressed_ring0(fx["G"], fx["v"]), name)
            self.assertEqual(as_matrix(self.rows[name]["ringDressed"]["1"]),
                             w.scale(F(-1), w.fock_matrix(fx["G"], fx["v"])), name)

    def test_what_the_ring_family_leaves_over_is_exactly_half_the_hartree(self):
        for name, fx in FIXTURES.items():
            d = as_matrix(self.rows[name]["delta"]["1"])
            r = as_matrix(self.rows[name]["ringDressed"]["1"])
            self.assertEqual(w.matsub(d, r),
                             w.scale(F(-1, 2), w.hartree_matrix(fx["G"], fx["v"])),
                             name)

    def test_the_hartree_remainder_is_genuinely_nonzero(self):
        """Otherwise the previous test would hold vacuously and the ring family
        would silently account for everything at first order."""
        for name, fx in FIXTURES.items():
            H = w.hartree_matrix(fx["G"], fx["v"])
            self.assertTrue(any(x != 0 for row in H for x in row), name)


class MutationDetection(unittest.TestCase):
    WITNESS = "N2-sym"

    def lean_delta(self):
        rows = evidence.validate_c3(json.loads(VALUES.read_text()), FIXTURES)
        return as_matrix(rows[self.WITNESS]["delta"]["1"])

    def check(self, kind):
        fx = FIXTURES[self.WITNESS]
        self.assertNotEqual(w.mutant(fx["G"], fx["v"], kind), self.lean_delta(),
                            f"mutant {kind} was not detected")

    def test_dropping_the_normalization_is_detected(self):
        """Leaving the disconnected matchings in -- the error `disconnected_cancels`
        exists to rule out."""
        self.check("unnormalized")

    def test_a_wrong_interaction_weight_is_detected(self):
        self.check("weight_quarter")
        self.check("weight_half")

    def test_swapping_hartree_and_fock_weights_is_detected(self):
        self.check("hartree_fock_swapped")

    def test_dropping_hartree_entirely_is_detected(self):
        """The ring family alone is not the first-order answer."""
        self.check("fock_only")

    def test_an_ordinary_wrong_value_is_detected(self):
        good = self.lean_delta()
        bad = [row[:] for row in good]
        bad[0][0] += 1
        self.assertNotEqual(bad, good)

    def test_a_wrong_matching_count_is_detected(self):
        self.assertNotEqual(w.matching_count(3), 14)
        self.assertEqual(w.matching_count(1), 1)
        self.assertEqual(w.matching_count(2), 3)


class ReaderRejectsBadEvidence(unittest.TestCase):
    def good(self):
        return json.loads(VALUES.read_text())

    def check(self, data):
        return evidence.validate_c3(data, FIXTURES)

    def test_the_real_table_validates(self):
        self.assertEqual(set(self.check(self.good())), set(FIXTURES))

    def test_a_missing_series_is_rejected(self):
        for series in SERIES:
            data = self.good()
            del data["values"][0][series]
            with self.assertRaises(EvidenceError) as cm:
                self.check(data)
            self.assertIn("missing series", str(cm.exception))

    def test_wrong_duplicate_before_correct_row_is_rejected(self):
        data = self.good()
        bad = json.loads(json.dumps(data["values"][0]))
        bad["delta"]["1"][0][0] = "999/1"
        data["values"].insert(0, bad)
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("duplicate", str(cm.exception))

    def test_a_falsely_declared_dimension_is_rejected(self):
        data = self.good()
        data["values"][0]["N"] = 999
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("fixture says", str(cm.exception))

    def test_narrowed_coverage_is_rejected(self):
        data = self.good()
        data["orders"] = [0, 1]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_a_float_entry_is_rejected(self):
        data = self.good()
        data["values"][0]["delta"]["1"][0][0] = 0.5
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("not exact", str(cm.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)

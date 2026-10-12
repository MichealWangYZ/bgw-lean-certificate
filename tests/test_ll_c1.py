#!/usr/bin/env python3
"""SCIENTIFIC GATE: LL-C1, the finite diagram-to-algebra bridge.

Checks that the Lean graph evaluator (`GW/LL/`, emitted by the `ll_c1_eval`
executable into `artifacts/ll-c1/lean_values.json`) agrees exactly with an
independently written Python rational reference (`ll/reference.py`), and that
deliberately broken variants of the reference are detected.

Exact rational arithmetic throughout. There are no tolerances, and the Python
side never reads the Lean output as an expected-answer column: it recomputes
every number from the formulas in Lin-Lindsey Part I, arXiv:1809.02900v1,
PDF section 4.7.1.
"""

from fractions import Fraction as F
from itertools import product
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]

# Loaded by explicit path rather than by putting `ll/` on sys.path: a bare
# `reference` module there would shadow `scripts/reference.py`, which
# tests/test_reference.py imports. That collision broke an unrelated test once.
_spec = importlib.util.spec_from_file_location(
    "ll_ring_reference", ROOT / "ll" / "ring_reference.py")
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

LEAN_VALUES = ROOT / "artifacts" / "ll-c1" / "lean_values.json"


_espec = importlib.util.spec_from_file_location(
    "ll_evidence", ROOT / "ll" / "evidence.py")
evidence = importlib.util.module_from_spec(_espec)
_espec.loader.exec_module(evidence)

# LL-C2A 2.1: tests and `ll/make_comparison.py` now share ONE validator, so the
# report generator cannot succeed on a table the tests would reject.
EvidenceError = evidence.EvidenceError
validate_rows = evidence.validate_rows


def lean_rows():
    data = json.loads(LEAN_VALUES.read_text())
    evidence.validate_symmetry_factors(data)
    return data, validate_rows(data, ref.FIXTURES)


class LeanPythonAgreement(unittest.TestCase):
    """The end-to-end comparison."""

    @classmethod
    def setUpClass(cls):
        cls.data, cls.rows = lean_rows()

    def test_every_fixture_is_present_on_both_sides(self):
        self.assertEqual(set(self.rows), set(ref.FIXTURES),
                         "the Lean and Python fixture sets must match")
        self.assertGreaterEqual(len(self.rows), 6)

    def test_symmetry_factors_are_the_proved_ones(self):
        self.assertEqual(self.data["symmetry_factors"],
                         evidence.EXPECTED_SYMMETRY_FACTORS)
        self.assertEqual(evidence.EXPECTED_SYMMETRY_FACTORS,
                         {"ring0": 1, "ring1": 2, "ring2": 4})
        for k in (0, 1, 2):
            self.assertEqual(ref.symmetry_factor(k), 2 ** k)

    def test_lean_matches_the_independent_reference_exactly(self):
        for name, fx in ref.FIXTURES.items():
            row = self.rows[name]
            for k in (0, 1, 2):
                expected = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], k)
                got = F(row[f"ring{k}"])
                self.assertEqual(got, expected,
                                 f"{name} ring{k}: Lean {got} != reference {expected}")

    def test_the_two_python_routes_agree(self):
        """Matrix formula vs graph contraction, written from different text."""
        for name, fx in ref.FIXTURES.items():
            for k in (0, 1, 2):
                a = ref.ring_contribution_matrix(fx["G"], fx["v"], fx["i"], fx["j"], k)
                b = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
                self.assertEqual(a, b, f"{name} ring{k}")

    def test_the_dimensions_actually_vary(self):
        self.assertEqual({row["N"] for row in self.rows.values()}, {1, 2, 3})

    def test_both_equal_and_unequal_external_indices_occur(self):
        pairs = {(row["i"], row["j"]) for row in self.rows.values()}
        self.assertTrue(any(i == j for i, j in pairs))
        self.assertTrue(any(i != j for i, j in pairs))

    def test_a_fixture_has_non_commuting_v_and_B(self):
        """`v * B != B * v` somewhere, so the chain order is actually tested."""
        found = False
        for fx in ref.FIXTURES.values():
            B = ref.hadamard_square(fx["G"])
            if ref.matmul(fx["v"], B) != ref.matmul(B, fx["v"]):
                found = True
        self.assertTrue(found, "no fixture distinguishes v*B from B*v")

    def test_a_non_scalar_positive_definite_G_is_present(self):
        """Leading principal minors positive, on a fixture with N > 1."""
        def minors_positive(M):
            n = len(M)
            for size in range(1, n + 1):
                sub = [row[:size] for row in M[:size]]
                if determinant(sub) <= 0:
                    return False
            return True

        def determinant(M):
            n = len(M)
            if n == 1:
                return M[0][0]
            total = F(0)
            for c in range(n):
                minor = [row[:c] + row[c + 1:] for row in M[1:]]
                total += ((-1) ** c) * M[0][c] * determinant(minor)
            return total

        ok = [name for name, fx in ref.FIXTURES.items()
              if len(fx["G"]) > 1 and minors_positive(fx["G"])]
        self.assertTrue(ok, "no non-scalar positive definite G among the fixtures")


class MutationDetection(unittest.TestCase):
    """Each mutant must visibly change a value at a fixed witness."""

    WITNESS = "N2-pd-unequal-ext"

    def fixture(self):
        return ref.FIXTURES[self.WITNESS]

    def test_wrong_sign_is_detected(self):
        """Recompute with the sign rule off by one interaction factor."""
        fx = self.fixture()
        for k in (0, 1, 2):
            good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
            bad = self.contract_with_edges(fx, k, ref.ring_edges(k), sign_offset=1)
            self.assertNotEqual(good, bad, f"ring{k} sign mutant not detected")
            self.assertEqual(good, -bad)
            # the witness must not be accidentally zero, or nothing is tested
            self.assertNotEqual(good, F(0), f"ring{k} witness value is zero")

    def test_missing_bubble_symmetry_factor_is_detected(self):
        """Recompute without dividing by `S = 2^k`."""
        fx = self.fixture()
        for k in (1, 2):
            good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
            bad = self.contract_with_edges(fx, k, ref.ring_edges(k), divide=False)
            self.assertNotEqual(good, bad, f"ring{k} symmetry-factor mutant not detected")
            self.assertEqual(bad, good * ref.symmetry_factor(k))
            self.assertNotEqual(good, F(0))

    def test_k0_has_no_symmetry_freedom(self):
        """`S = 1` at k=0, so omitting the divisor must change nothing there."""
        fx = self.fixture()
        good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], 0)
        same = self.contract_with_edges(fx, 0, ref.ring_edges(0), divide=False)
        self.assertEqual(good, same)

    def test_index_contraction_mistake_is_detected(self):
        """A genuine topology error: attach the chain to the wrong bubble site.

        The mutant wires interaction `m` from `a_m` instead of `b_m`, so the
        chain enters and leaves the same side of each bubble. This is not a
        relabeling and not a symmetry.
        """
        fx = self.fixture()
        for k in (1, 2):
            good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
            bad = self.contract_with_edges(fx, k, self.mutant_edges(k))
            self.assertNotEqual(good, bad, f"ring{k} mutant was not detected")

    @staticmethod
    def mutant_edges(k):
        extI, extJ = ('e', 0), ('e', 1)
        props = [(extI, extJ)]
        for m in range(k):
            props += [(('a', m), ('b', m)), (('a', m), ('b', m))]
        ints = [(extI, ('a', 0))]
        ints += [(('a', m), ('a', m + 1)) for m in range(k - 1)]   # was ('b', m)
        ints += [(('a', k - 1), extJ)]                              # was ('b', k-1)
        return props, ints

    @staticmethod
    def contract_with_edges(fx, k, edges, sign_offset=0, divide=True):
        G, v, i, j = fx["G"], fx["v"], fx["i"], fx["j"]
        n = len(G)
        props, ints = edges
        internal = [s for m in range(k) for s in (('a', m), ('b', m))]
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
        sign = (-1) ** (len(ints) + sign_offset)
        divisor = ref.symmetry_factor(k) if divide else 1
        return sign * total / divisor

    def test_permitted_internal_relabeling_changes_nothing(self):
        """Renaming internal sites is a change of summation variable only."""
        fx = self.fixture()
        for k in (1, 2):
            good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
            props, ints = ref.ring_edges(k)
            swap = {}
            for m in range(k):
                swap[('a', m)] = ('b', m)
                swap[('b', m)] = ('a', m)
            rename = lambda s: swap.get(s, s)
            relabeled = ([(rename(u), rename(w)) for u, w in props],
                         [(rename(u), rename(w)) for u, w in ints])
            same = self.contract_with_edges(fx, k, relabeled)
            self.assertEqual(good, same, f"ring{k} relabeling changed the value")


class EvidenceTableValidation(unittest.TestCase):
    """Regressions for the two false passes found by review of LL-C1.

    Migrated from the archival reproducer on `review/ll-c1-r1-20260914`, which
    is pinned to the reviewed commit and is not a production gate. These probe
    the repaired checker directly.
    """

    def good_table(self):
        return json.loads(LEAN_VALUES.read_text())

    def test_the_real_table_validates(self):
        validate_rows(self.good_table(), ref.FIXTURES)

    def test_wrong_duplicate_before_correct_row_is_rejected(self):
        """The old checker keyed rows by name, so a later correct row silently
        overwrote an earlier wrong duplicate."""
        data = self.good_table()
        bad = dict(data["values"][0])
        bad["ring0"] = "999/1"
        data["values"].insert(0, bad)            # wrong row first, correct after
        with self.assertRaises(EvidenceError) as cm:
            validate_rows(data, ref.FIXTURES)
        self.assertIn("duplicate", str(cm.exception))

    def test_out_of_bounds_external_indices_are_rejected(self):
        """The old checker never read the row's own `i`/`j`, so `i = j = 999`
        at `N = 1` passed."""
        data = self.good_table()
        row = next(r for r in data["values"] if r["N"] == 1)
        row["i"] = row["j"] = 999
        with self.assertRaises(EvidenceError) as cm:
            validate_rows(data, ref.FIXTURES)
        self.assertRegex(str(cm.exception), "fixture says|out of bounds")

    def test_metadata_disagreeing_with_its_fixture_is_rejected(self):
        data = self.good_table()
        data["values"][1]["N"] = 7
        with self.assertRaises(EvidenceError):
            validate_rows(data, ref.FIXTURES)

    def test_boolean_cannot_masquerade_as_an_index(self):
        """`bool` is a subclass of `int`; `isinstance` would have let it pass."""
        data = self.good_table()
        row = next(r for r in data["values"] if r["i"] == 0)
        row["i"] = False
        with self.assertRaises(EvidenceError) as cm:
            validate_rows(data, ref.FIXTURES)
        self.assertIn("not int", str(cm.exception))

    def test_float_index_is_rejected(self):
        data = self.good_table()
        data["values"][0]["j"] = 0.0
        with self.assertRaises(EvidenceError):
            validate_rows(data, ref.FIXTURES)

    def test_missing_and_extra_fixtures_are_rejected(self):
        data = self.good_table()
        dropped = data["values"].pop()
        with self.assertRaises(EvidenceError) as cm:
            validate_rows(data, ref.FIXTURES)
        self.assertIn("inventory mismatch", str(cm.exception))
        data["values"].append(dropped)
        extra = dict(dropped)
        extra["name"] = "not-a-fixture"
        data["values"].append(extra)
        with self.assertRaises(EvidenceError):
            validate_rows(data, ref.FIXTURES)

    def test_an_ordinary_wrong_value_is_still_caught(self):
        """Validation must not have displaced the numerical comparison."""
        data = self.good_table()
        rows = validate_rows(data, ref.FIXTURES)
        name = "N2-pd-unequal-ext"
        rows[name]["ring1"] = "0/1"
        fx = ref.FIXTURES[name]
        expected = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], 1)
        self.assertNotEqual(F(rows[name]["ring1"]), expected)


class ReportGeneratorRejectsBadEvidence(unittest.TestCase):
    """CLI-level regressions for `ll/make_comparison.py`.

    LL-C2A 2.1: the generator previously bypassed validation entirely and
    exited 0 on a duplicate row, on impossible `N/i/j`, and on forged symmetry
    metadata that it then relabelled as the paper's. Each probe below was
    measured to exit 0 before this repair.
    """

    def run_generator(self, mutate):
        data = json.loads(LEAN_VALUES.read_text())
        mutate(data)
        with tempfile.TemporaryDirectory() as tmp:
            bad = pathlib.Path(tmp) / "lean_values.json"
            bad.write_text(json.dumps(data))
            out = pathlib.Path(tmp) / "comparison.json"
            proc = subprocess.run(
                [sys.executable, str(ROOT / "ll" / "make_comparison.py"),
                 "--lean", str(bad), "--out", str(out)],
                capture_output=True, text=True)
            return proc

    def test_unmodified_table_still_succeeds(self):
        proc = self.run_generator(lambda d: None)
        self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_duplicate_row_is_rejected(self):
        def mutate(d):
            bad = dict(d["values"][0])
            bad["ring0"] = "999/1"
            d["values"].insert(0, bad)
        proc = self.run_generator(mutate)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("duplicate", proc.stderr)

    def test_invalid_indices_are_rejected(self):
        def mutate(d):
            row = next(r for r in d["values"] if r["N"] == 1)
            row["i"] = row["j"] = 999
        proc = self.run_generator(mutate)
        self.assertNotEqual(proc.returncode, 0)

    def test_forged_symmetry_metadata_is_rejected(self):
        """And is never relabelled as coming from the paper."""
        proc = self.run_generator(
            lambda d: d["symmetry_factors"].__setitem__("ring1", 999))
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("symmetry metadata", proc.stderr)

    def test_ordinary_wrong_value_is_rejected(self):
        proc = self.run_generator(
            lambda d: d["values"][2].__setitem__("ring1", "0/1"))
        self.assertNotEqual(proc.returncode, 0)

    def test_the_report_never_launders_candidate_metadata(self):
        """No emitted field may present candidate data as the paper's."""
        report = json.loads((ROOT / "artifacts" / "ll-c1" / "comparison.json").read_text())
        self.assertNotIn("symmetry_factors_from_paper", report)
        self.assertEqual(report["symmetry_factors_checked_against_paper"],
                         evidence.EXPECTED_SYMMETRY_FACTORS)


if __name__ == "__main__":
    unittest.main(verbosity=2)

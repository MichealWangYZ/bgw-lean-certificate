#!/usr/bin/env python3
"""SCIENTIFIC GATE: LL-C2B, formal screening of the ring family.

The arbitrary-order claims are Lean theorems in `GW/LL/Screening.lean`:
`PL_mul_W`, `W_mul_PR`, `W_eq_C_v_mul_SR`, `coeff_W`, `T_eq_neg_hadamardSeries_W`
and the degree lemmas. This file is a regression and a semantic witness, not
the proof.

What it checks is that the coefficients the Lean evaluator prints -- which are
the actual power-series coefficients, by the named bridges `GW.LL.coeff_W` and
`GW.LL.coeff_T_eq_Tcoeff` -- agree exactly with an independently written
Python reference that reaches them by four different routes, including generic
formal-series inversion that does not know the shape of `P_L`.

Exact `fractions.Fraction` throughout. Formal coefficients only: nothing is
evaluated at `z = 1` and no convergence is asserted.
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


sr = _load("ll_screening_reference", "ll/screening_reference.py")
evidence = _load("ll_evidence", "ll/evidence.py")
EvidenceError = evidence.EvidenceError

#: Specification-owned, as in `ll/evidence.py`. Never read from the artifact.
ORDERS = list(evidence.EXPECTED_C2B_ORDERS)
KMAX = max(ORDERS)

VALUES = ROOT / "artifacts" / "ll-c2b" / "screening_values.json"

#: Inputs duplicated from `LLC2BMain.lean`. Inputs only; no expected outputs.
FIXTURES = {
    "N2-pd": dict(G=sr.mat([[2, 1], [1, 2]]), v=sr.mat([[1, 2], [2, 3]]), i=0, j=1),
    "N2-rational": dict(
        G=sr.mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]),
        v=sr.mat([[F(2, 5), F(1, 7)], [F(1, 7), F(-4, 3)]]), i=1, j=0),
    "N3-pd": dict(
        G=sr.mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=sr.mat([[1, 2, 3], [2, 0, 1], [3, 1, 2]]), i=0, j=1),
}


def as_matrix(rows):
    return [[F(x) for x in row] for row in rows]


class ScreeningCoefficients(unittest.TestCase):
    """The Lean coefficients against four independent Python routes."""

    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(VALUES.read_text())
        cls.rows = evidence.validate_c2b(cls.data, FIXTURES)

    def test_coverage_is_the_specifications(self):
        self.assertEqual(ORDERS, self.data["orders"],
                         "validator must have rejected a narrowed coverage")
        self.assertGreaterEqual(KMAX, 4, "LL-C2B 5 requires degrees 0..4")

    def test_the_bridges_to_the_theorems_are_named(self):
        """A printed number stands for a coefficient only because a theorem
        says so. The artifact must name those theorems."""
        self.assertEqual(self.data["bridges"],
                         ["GW.LL.coeff_W", "GW.LL.coeff_T_eq_Tcoeff"])

    def test_all_four_python_routes_agree(self):
        for name, fx in FIXTURES.items():
            with self.subTest(name):
                sr.all_routes_agree(fx["G"], fx["v"], KMAX)

    def test_lean_W_matches_the_reference_at_every_degree(self):
        for name, fx in FIXTURES.items():
            expected = sr.all_routes_agree(fx["G"], fx["v"], KMAX)
            for k in ORDERS:
                got = as_matrix(self.rows[name]["W"][str(k)])
                self.assertEqual(got, expected[k], f"{name} W degree {k}")

    def test_lean_T_is_minus_G_hadamard_W(self):
        """`T = -H_G W`, the statement `GW.LL.T_eq_neg_hadamardSeries_W` proves
        for all degrees, checked here at the emitted ones."""
        for name, fx in FIXTURES.items():
            W = sr.all_routes_agree(fx["G"], fx["v"], KMAX)
            for k in ORDERS:
                got = as_matrix(self.rows[name]["T"][str(k)])
                self.assertEqual(got, sr.t_from_w(fx["G"], W[k]),
                                 f"{name} T degree {k}")

    def test_W_at_degree_zero_is_v(self):
        for name, fx in FIXTURES.items():
            self.assertEqual(as_matrix(self.rows[name]["W"]["0"]), fx["v"], name)


class ScreeningEquations(unittest.TestCase):
    """`P_L W = C(v)` and `W P_R = C(v)`, coefficientwise, through KMAX.

    The residuals are formed from the VALIDATED CANDIDATE `W` matrices, not
    from a Python recomputation, so a failure localizes to the degree and
    fixture whose emitted coefficient is wrong.
    """

    @classmethod
    def setUpClass(cls):
        cls.rows = evidence.validate_c2b(json.loads(VALUES.read_text()), FIXTURES)

    def candidate_W(self, name):
        return [as_matrix(self.rows[name]["W"][str(k)]) for k in ORDERS]

    def residual_vanishes(self, side):
        for name, fx in FIXTURES.items():
            W = self.candidate_W(name)
            P = (sr.pl_series(fx["G"], fx["v"], KMAX) if side == "left"
                 else sr.pr_series(fx["G"], fx["v"], KMAX))
            prod = (sr.convolve(P, W, KMAX) if side == "left"
                    else sr.convolve(W, P, KMAX))
            target = sr.const_series(fx["v"], KMAX)
            for d in ORDERS:
                for a, row in enumerate(prod[d]):
                    for b, x in enumerate(row):
                        self.assertEqual(x, target[d][a][b],
                                         f"{name} {side} degree {d} entry ({a},{b})")

    def test_left_screening_equation_holds_through_the_tested_degrees(self):
        self.residual_vanishes("left")

    def test_right_screening_equation_holds_through_the_tested_degrees(self):
        self.residual_vanishes("right")

    def test_the_first_omitted_degree_is_exactly_A_L_times_W_KMAX(self):
        """What truncation leaves behind is finite algebra, not convergence.

        An earlier version of this test said constraining degree KMAX+1 would
        be a convergence claim, and then asserted only the matrix's size. Both
        were wrong. Truncating `W` after `W_KMAX` simply drops the coefficient
        that cancels this term, so the residual is exactly `A_L W_KMAX`, and
        exactly `-W_{KMAX+1}`. The C2B review measured the same matrix.
        """
        for name, fx in FIXTURES.items():
            W = self.candidate_W(name)
            P = sr.pl_series(fx["G"], fx["v"], KMAX)
            beyond = sr.convolve(P, W, KMAX + 1)[KMAX + 1]
            expected = sr.first_omitted_residual(fx["G"], fx["v"], KMAX)
            self.assertEqual(beyond, expected, f"{name}: residual != A_L W_KMAX")
            # ... and the next true coefficient is what cancels it.
            nxt = sr.w_closed(fx["G"], fx["v"], KMAX + 1)
            for a in range(len(fx["G"])):
                for b in range(len(fx["G"])):
                    self.assertEqual(nxt[a][b] + beyond[a][b], 0, f"{name} ({a},{b})")

    def test_the_residual_is_actually_nonzero_somewhere(self):
        """Otherwise the test above would be satisfied vacuously."""
        fx = FIXTURES["N2-pd"]
        beyond = sr.first_omitted_residual(fx["G"], fx["v"], KMAX)
        self.assertTrue(any(x != 0 for row in beyond for x in row))


class NoncommutingWitness(unittest.TestCase):
    """The distinction between the left and right kernels must be real here."""

    def test_v_and_B_do_not_commute_somewhere(self):
        found = any(sr.matmul(fx["v"], sr.bubble(fx["G"]))
                    != sr.matmul(sr.bubble(fx["G"]), fx["v"])
                    for fx in FIXTURES.values())
        self.assertTrue(found, "no fixture distinguishes A_L from A_R")

    def test_A_L_and_A_R_differ_on_a_fixture(self):
        found = any(sr.a_left(fx["G"], fx["v"]) != sr.a_right(fx["G"], fx["v"])
                    for fx in FIXTURES.values())
        self.assertTrue(found)


class DegreeConvention(unittest.TestCase):
    """Bubble counting, not interaction counting."""

    def test_the_fock_term_sits_at_degree_zero(self):
        """`ring 0` has one interaction and no bubble. In this series it is the
        constant coefficient; shifting it to degree one is the coupling
        convention, which `Tcoupling` handles separately in Lean."""
        for name, fx in FIXTURES.items():
            rows = json.loads(VALUES.read_text())
            row = next(r for r in rows["values"] if r["name"] == name)
            self.assertEqual(as_matrix(row["T"]["0"]),
                             sr.t_from_w(fx["G"], fx["v"]), name)


class MutationDetection(unittest.TestCase):
    """Each required mutant class must disagree with the Lean coefficients."""

    WITNESS = "N2-pd"

    def lean_W(self):
        data = json.loads(VALUES.read_text())
        row = next(r for r in data["values"] if r["name"] == self.WITNESS)
        return [as_matrix(row["W"][str(k)]) for k in ORDERS]

    def check_mutant(self, kind):
        fx = FIXTURES[self.WITNESS]
        bad = sr.w_mutant(fx["G"], fx["v"], KMAX, kind)
        good = self.lean_W()
        self.assertNotEqual(bad, good, f"mutant {kind} was not detected")

    def test_a_wrong_sign_is_detected(self):
        self.check_mutant("sign")

    def test_a_missing_factor_of_one_half_is_detected(self):
        self.check_mutant("no_half")

    def test_a_wrong_matrix_ordering_is_detected(self):
        """`A_R` applied on the left. This mutant is only detectable because
        the witness fixture has `v B != B v`."""
        self.check_mutant("wrong_order")

    def test_a_degree_shift_is_detected(self):
        self.check_mutant("degree_shift")

    def test_an_ordinary_wrong_value_is_detected(self):
        good = self.lean_W()
        bad = [[row[:] for row in M] for M in good]
        bad[3][0][0] += 1
        self.assertNotEqual(bad, good)


class ReaderRejectsBadEvidence(unittest.TestCase):
    """The C2B reader must not repeat C1's and C2A's hole.

    Coverage and series names come from `ll/evidence.py`, so the table cannot
    choose what it is compared against.
    """

    def good(self):
        return json.loads(VALUES.read_text())

    def check(self, data):
        return evidence.validate_c2b(data, FIXTURES)

    def test_the_real_table_validates(self):
        self.assertEqual(set(self.check(self.good())), set(FIXTURES))

    def test_wrong_duplicate_before_correct_row_is_rejected(self):
        data = self.good()
        bad = json.loads(json.dumps(data["values"][0]))
        bad["W"]["3"][0][0] = "999/1"
        data["values"].insert(0, bad)
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("duplicate", str(cm.exception))

    def test_impossible_external_indices_are_rejected(self):
        data = self.good()
        data["values"][0]["i"] = data["values"][0]["j"] = 999
        with self.assertRaises(EvidenceError):
            self.check(data)

    def test_a_falsely_declared_dimension_is_rejected(self):
        data = self.good()
        data["values"][0]["N"] = 999
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("fixture says", str(cm.exception))

    def test_narrowed_coverage_is_rejected(self):
        data = self.good()
        data["orders"] = [0, 3]
        for row in data["values"]:
            for series in ("W", "T"):
                row[series] = {k: row[series][k] for k in ("0", "3")}
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_a_dropped_degree_inside_a_series_is_rejected(self):
        data = self.good()
        del data["values"][1]["W"]["4"]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_a_missing_series_is_rejected(self):
        data = self.good()
        del data["values"][0]["T"]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("missing series", str(cm.exception))

    def test_a_wrongly_shaped_matrix_is_rejected(self):
        data = self.good()
        data["values"][0]["W"]["2"] = [["1/1"]]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("matrix", str(cm.exception))

    def test_an_inexact_entry_is_rejected(self):
        data = self.good()
        data["values"][0]["W"]["2"][0][0] = "not-a-number"
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("not exact", str(cm.exception))

    def test_a_float_or_bool_entry_is_rejected(self):
        """`Fraction` converts both silently -- `Fraction(0.1)` is a 55-bit
        ratio and `Fraction(True)` is 1 -- so `Fraction`-convertibility was a
        weaker check than the validator's prose claimed. Raised by the C2B
        review; the encoding is now required to be an exact rational literal."""
        for junk in (0.1, 2.0, True):
            with self.subTest(junk=junk):
                data = self.good()
                data["values"][0]["W"]["2"][0][0] = junk
                with self.assertRaises(EvidenceError) as cm:
                    self.check(data)
                self.assertIn("not exact", str(cm.exception))

    def test_missing_and_extra_fixtures_are_rejected(self):
        data = self.good()
        dropped = data["values"].pop()
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("inventory mismatch", str(cm.exception))
        extra = json.loads(json.dumps(dropped))
        extra["name"] = "not-a-fixture"
        data["values"] += [dropped, extra]
        with self.assertRaises(EvidenceError):
            self.check(data)


if __name__ == "__main__":
    unittest.main(verbosity=2)

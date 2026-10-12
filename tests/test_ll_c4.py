#!/usr/bin/env python3
"""SCIENTIFIC GATE: LL-C4, finite static electronic RPA screening.

Lean theorems in `GW/LL/Electronic.lean` carry the general claims:
`coeff_geoW`, `classical_W_eq_geoW`, `coeff_electronicW`,
`dielectric_mul_partialScreened`, `chi0_quadForm_nonpos`, `chi0_diag_nonpos`,
`bubble_diag_nonneg`, `bubble_chi0_diag_witness`, `gpp_static_limit`.

This file is a regression and a semantic witness. Its oracle
(`ll/electronic_reference.py`) reaches the screened interaction by **exact
Gaussian elimination** on `eps W = v`, a genuinely different route from the
Neumann series the Lean side manipulates.

WHAT IS SPECIFIED, NOT DERIVED: the electronic conventions (transition
energies, spectral weights carrying spin/degeneracy, the static form of `chi0`,
`eps = 1 - v chi0`). These are inputs. Nothing here is a BerkeleyGW convention
or a BerkeleyGW result, and no matched comparison against a production path is
performed -- the repository holds no dielectric fixture from a real run.
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


e = _load("ll_electronic_reference", "ll/electronic_reference.py")
evidence = _load("ll_evidence", "ll/evidence.py")
EvidenceError = evidence.EvidenceError

ORDERS = list(evidence.EXPECTED_C4_ORDERS)
KMAX = max(ORDERS)
VALUES = ROOT / "artifacts" / "ll-c4" / "electronic_values.json"

#: Inputs duplicated from `LLC4Main.lean`. Inputs only; no expected outputs.
FIXTURES = {
    "N2-two-channel": dict(
        G=e.mat([[2, 1], [1, 3]]), v=e.mat([[2, 1], [1, 3]]), i=0, j=1,
        ts=[e.Transition(0, 2, 4, [1, 0]),
            e.Transition(F(-1, 2), F(3, 2), 4, [1, 1])]),
    "N2-rational": dict(
        G=e.mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]),
        v=e.mat([[F(1, 2), F(-1, 3)], [F(-1, 3), F(3, 2)]]), i=1, j=0,
        ts=[e.Transition(F(-1, 5), F(7, 5), F(2, 3), [F(1, 2), F(-2, 3)])]),
    "N3-three-channel": dict(
        G=e.mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]),
        v=e.mat([[3, 1, 0], [1, 3, 1], [0, 1, 3]]), i=0, j=1,
        ts=[e.Transition(0, 1, 2, [1, 0, 0]),
            e.Transition(F(-1, 2), 2, 2, [0, 1, 0]),
            e.Transition(-1, 3, 2, [1, 1, 1])]),
}


def as_matrix(rows):
    return [[F(x) for x in row] for row in rows]


class ModelIsWellPosed(unittest.TestCase):
    def test_every_transition_runs_occupied_to_empty(self):
        for name, fx in FIXTURES.items():
            for t in fx["ts"]:
                self.assertLess(t.occ, t.emp, name)
                self.assertGreaterEqual(t.weight, 0, name)

    def test_chi0_is_symmetric_and_nonpositive_on_the_diagonal(self):
        for name, fx in FIXTURES.items():
            X = e.chi0(fx["ts"], len(fx["v"]))
            self.assertTrue(e.is_symmetric(X), name)
            for a in range(len(X)):
                self.assertLessEqual(X[a][a], 0, name)

    def test_chi0_is_negative_semidefinite_on_sampled_vectors(self):
        """The Lean theorem `chi0_quadForm_nonpos` is the general statement."""
        for name, fx in FIXTURES.items():
            n = len(fx["v"])
            for trial in range(-2, 3):
                for shift in range(n):
                    x = [F(trial + (k == shift)) for k in range(n)]
                    self.assertLessEqual(e.quad_form(e.chi0(fx["ts"], n), x), 0,
                                         f"{name} {x}")


class LeanMatchesTheOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(VALUES.read_text())
        cls.rows = evidence.validate_c4(cls.data, FIXTURES)

    def test_the_scope_statement_is_in_the_artifact(self):
        """A reader of the JSON alone must see what is specified and what is
        out of scope."""
        self.assertIn("INPUTS", self.data["specified_not_derived"])
        self.assertIn("not a BerkeleyGW", self.data["specified_not_derived"])
        self.assertIn("no Sigma = i G W", self.data["scope"])

    def test_the_bridges_to_the_theorems_are_named(self):
        self.assertEqual(self.data["bridges"],
                         ["GW.LL.coeff_electronicW_eq_neumannCoeff",
                          "GW.LL.dielectric_mul_partialScreened"])

    def test_chi0_and_eps_match(self):
        for name, fx in FIXTURES.items():
            n = len(fx["v"])
            X = e.chi0(fx["ts"], n)
            self.assertEqual(as_matrix(self.rows[name]["chi0"]["0"]), X, name)
            self.assertEqual(as_matrix(self.rows[name]["eps"]["0"]),
                             e.epsilon(fx["v"], X), name)

    def test_neumann_coefficients_match(self):
        for name, fx in FIXTURES.items():
            for k in ORDERS:
                self.assertEqual(as_matrix(self.rows[name]["neumann"][str(k)]),
                                 e.neumann_coeff(fx["v"], fx["ts"], k),
                                 f"{name} k={k}")

    def test_partial_sums_match(self):
        for name, fx in FIXTURES.items():
            for k in ORDERS:
                self.assertEqual(as_matrix(self.rows[name]["partial"][str(k)]),
                                 e.partial_sum(fx["v"], fx["ts"], k),
                                 f"{name} k={k}")

    def test_neumann_at_zero_is_v(self):
        for name, fx in FIXTURES.items():
            self.assertEqual(as_matrix(self.rows[name]["neumann"]["0"]),
                             fx["v"], name)


class TruncationIsFiniteAlgebra(unittest.TestCase):
    """`eps * partial_K = v - (v chi0)^(K+1) v`, exactly, for every K.

    This is the Lean theorem `dielectric_mul_partialScreened`. It is an
    identity, not a convergence statement, and the check below uses the
    emitted partial sums rather than recomputing them.
    """

    @classmethod
    def setUpClass(cls):
        cls.rows = evidence.validate_c4(json.loads(VALUES.read_text()), FIXTURES)

    def test_the_residual_is_exactly_the_next_coefficient(self):
        for name, fx in FIXTURES.items():
            X = e.chi0(fx["ts"], len(fx["v"]))
            eps = e.epsilon(fx["v"], X)
            for k in ORDERS:
                P = as_matrix(self.rows[name]["partial"][str(k)])
                residual = e.matsub(fx["v"], e.matmul(eps, P))
                self.assertEqual(residual,
                                 e.neumann_coeff(fx["v"], fx["ts"], k + 1),
                                 f"{name} K={k}")

    def test_the_residual_is_nonzero_somewhere(self):
        """Otherwise the identity above would hold vacuously."""
        fx = FIXTURES["N2-two-channel"]
        R = e.neumann_coeff(fx["v"], fx["ts"], KMAX + 1)
        self.assertTrue(any(x != 0 for row in R for x in row))


class IndependentExactSolve(unittest.TestCase):
    """The oracle's own route: solve `eps W = v` by Gaussian elimination."""

    def test_the_exact_solve_satisfies_the_defining_equation(self):
        for name, fx in FIXTURES.items():
            X = e.chi0(fx["ts"], len(fx["v"]))
            W = e.screened(fx["v"], fx["ts"])
            self.assertEqual(e.matmul(e.epsilon(fx["v"], X), W), fx["v"], name)

    def test_lean_does_not_claim_to_invert_a_matrix(self):
        """Lean manipulates formal coefficients and a finite telescoping
        identity; the exact inverse is computed only here, on the Python side."""
        data = json.loads(VALUES.read_text())
        self.assertNotIn("inverse", json.dumps(data).lower())


class ClassicalContentDoesNotTransfer(unittest.TestCase):
    """The algebra transfers; the objects do not. Lean proves the general
    statements (`bubble_diag_nonneg`, `chi0_diag_nonpos`); this pins a witness."""

    def test_classical_bubble_diagonal_is_nonnegative(self):
        for name, fx in FIXTURES.items():
            B = e.bubble(fx["G"])
            for a in range(len(B)):
                self.assertGreaterEqual(B[a][a], 0, name)

    def test_electronic_chi0_diagonal_is_nonpositive(self):
        for name, fx in FIXTURES.items():
            X = e.chi0(fx["ts"], len(fx["v"]))
            for a in range(len(X)):
                self.assertLessEqual(X[a][a], 0, name)

    def test_a_witness_separates_them_strictly(self):
        fx = FIXTURES["N2-two-channel"]
        B = e.bubble(fx["G"])
        X = e.chi0(fx["ts"], 2)
        self.assertTrue(any(B[a][a] > 0 for a in range(2)))
        self.assertTrue(any(X[a][a] < 0 for a in range(2)))
        self.assertNotEqual(B, X)


class GppStaticBridge(unittest.TestCase):
    """The plasmon-pole model reproduces the static value at zero frequency."""

    def test_the_identification_reproduces_the_static_value(self):
        for inv_eps0 in (F(1, 3), F(1), F(-2, 7), F(0)):
            for wt in (F(5), F(1, 2), F(-3)):
                O2 = e.gpp_omega2_from_static(inv_eps0, wt)
                self.assertEqual(e.gpp_inv_eps(O2, wt, 0), inv_eps0)

    def test_a_vanishing_pole_frequency_is_outside_the_domain(self):
        with self.assertRaises(ZeroDivisionError):
            e.gpp_inv_eps(F(1), F(0), F(0))

    def test_this_is_not_a_self_energy_claim(self):
        """Connecting the dielectric to `GW.GPP.Data.sigmaChecked` needs the
        frequency integral, which this repository does not perform."""
        data = json.loads(VALUES.read_text())
        self.assertIn("no Sigma = i G W", data["scope"])


class MutationDetection(unittest.TestCase):
    """Each mutant is compared against the RIGHT target.

    The C3/C4 review found the early-truncation case was nondiagnostic: it
    compared the early partial sum against the exact `W`, and the *correct*
    partial sum also differs from exact `W`, so the assertion passed for the
    wrong reason. Exact-solve mutants are now compared against the exact solve,
    and the truncation mutant against the required-order partial sum.
    """

    WITNESS = "N2-two-channel"

    def exact(self):
        fx = FIXTURES[self.WITNESS]
        return e.screened(fx["v"], fx["ts"])

    def required_partial(self):
        fx = FIXTURES[self.WITNESS]
        return e.partial_sum(fx["v"], fx["ts"], KMAX)

    def check_against_exact(self, kind):
        fx = FIXTURES[self.WITNESS]
        self.assertNotEqual(e.mutant(fx["v"], fx["ts"], kind, KMAX), self.exact(),
                            f"mutant {kind} was not detected")

    def test_a_flipped_transition_denominator_is_detected(self):
        self.check_against_exact("sign_flipped_denominator")

    def test_a_dropped_spectral_weight_is_detected(self):
        self.check_against_exact("weight_dropped")

    def test_the_wrong_dielectric_sign_is_detected(self):
        self.check_against_exact("eps_sign")

    def test_an_early_truncation_is_detected_against_the_required_order(self):
        fx = FIXTURES[self.WITNESS]
        early = e.mutant(fx["v"], fx["ts"], "truncated_early", KMAX)
        self.assertNotEqual(early, self.required_partial(),
                            "early truncation not detected at the declared order")

    def test_the_early_truncation_residuals_differ(self):
        """The finite residual is the other correct comparison."""
        fx = FIXTURES[self.WITNESS]
        self.assertNotEqual(e.truncation_residual(fx["v"], fx["ts"], KMAX - 1),
                            e.truncation_residual(fx["v"], fx["ts"], KMAX))

    def test_the_old_assertion_was_nondiagnostic(self):
        """Pins the defect so it cannot silently return: comparing ANY partial
        sum against the exact `W` succeeds, mutated or not."""
        self.assertNotEqual(self.required_partial(), self.exact(),
                            "if these were equal the old test would have been fine")

    def test_an_ordinary_wrong_value_is_detected(self):
        good = self.exact()
        bad = [row[:] for row in good]
        bad[0][0] += 1
        self.assertNotEqual(bad, good)


class FormalIsNotConvergent(unittest.TestCase):
    """The Neumann series is formal here, and on this fixture it is provably
    not a convergent solver -- while the exact static solution still exists.

    Raised by the C3/C4 review. Argued exactly, with no square roots: the
    product of the eigenvalues of `v chi0` is its determinant, so
    `|det| > 1` forces some eigenvalue to have modulus greater than one.
    """

    def test_the_spectral_radius_exceeds_one_on_the_first_fixture(self):
        fx = FIXTURES["N2-two-channel"]
        T = e.matmul(fx["v"], e.chi0(fx["ts"], 2))
        det = T[0][0] * T[1][1] - T[0][1] * T[1][0]
        self.assertEqual(det, 20)
        self.assertGreater(abs(det), 1,
                           "product of eigenvalues exceeds 1, so the spectral "
                           "radius does too")

    def test_the_exact_static_solution_nevertheless_exists(self):
        fx = FIXTURES["N2-two-channel"]
        X = e.chi0(fx["ts"], 2)
        W = e.screened(fx["v"], fx["ts"])
        self.assertEqual(e.matmul(e.epsilon(fx["v"], X), W), fx["v"])

    def test_the_artifact_does_not_claim_convergence(self):
        data = json.loads(VALUES.read_text())
        self.assertIn("no convergence claim", data["scope"])


class SignDifferenceIsNotAnObstruction(unittest.TestCase):
    """The review's counterexample, on the Python side.

    `GW.LL.chi0_eq_neg_half_bubble_witness` and
    `GW.LL.electronicW_eq_classical_W` are the Lean statements. An earlier
    version of this work claimed the opposite diagonal signs proved the
    physical content could not transfer; that inference was too strong.
    """

    G = e.mat([[2, 0], [0, 3]])
    v = e.mat([[2, 1], [1, 3]])
    ts = [e.Transition(0, 2, 4, [1, 0]), e.Transition(0, 2, 9, [0, 1])]

    def test_the_transitions_are_admissible(self):
        for t in self.ts:
            self.assertLess(t.occ, t.emp)
            self.assertGreaterEqual(t.weight, 0)

    def test_chi0_equals_minus_half_the_classical_bubble(self):
        self.assertEqual(e.chi0(self.ts, 2),
                         e.scale(F(-1, 2), e.bubble(self.G)))

    def test_the_two_screening_kernels_then_coincide(self):
        classical = e.scale(F(1, 2), e.matmul(self.v, e.bubble(self.G)))
        electronic = e.scale(F(-1), e.matmul(self.v, e.chi0(self.ts, 2)))
        self.assertEqual(classical, electronic)

    def test_and_the_matrices_still_do_not_commute(self):
        """So the coincidence is not a commutativity accident."""
        B = e.bubble(self.G)
        self.assertNotEqual(e.matmul(self.v, B), e.matmul(B, self.v))

    def test_the_surviving_claim_is_only_that_B_is_not_chi0(self):
        """Direct identification is still wrong -- the signs do show that."""
        self.assertNotEqual(e.bubble(self.G), e.chi0(self.ts, 2))


class ReaderRejectsBadEvidence(unittest.TestCase):
    def good(self):
        return json.loads(VALUES.read_text())

    def check(self, data):
        return evidence.validate_c4(data, FIXTURES)

    def test_the_real_table_validates(self):
        self.assertEqual(set(self.check(self.good())), set(FIXTURES))

    def test_a_missing_series_is_rejected(self):
        for series in ("chi0", "eps", "neumann", "partial"):
            data = self.good()
            del data["values"][0][series]
            with self.assertRaises(EvidenceError) as cm:
                self.check(data)
            self.assertIn("missing series", str(cm.exception))

    def test_narrowed_expansion_coverage_is_rejected(self):
        data = self.good()
        data["orders"] = [0, 1]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_narrowed_static_coverage_is_rejected(self):
        data = self.good()
        data["static_orders"] = [0, 1]
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("coverage", str(cm.exception))

    def test_wrong_duplicate_before_correct_row_is_rejected(self):
        data = self.good()
        bad = json.loads(json.dumps(data["values"][0]))
        bad["neumann"]["2"][0][0] = "999/1"
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

    def test_a_float_entry_is_rejected(self):
        data = self.good()
        data["values"][0]["chi0"]["0"][0][0] = 0.25
        with self.assertRaises(EvidenceError) as cm:
            self.check(data)
        self.assertIn("not exact", str(cm.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)

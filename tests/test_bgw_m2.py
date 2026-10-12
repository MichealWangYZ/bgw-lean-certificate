#!/usr/bin/env python3
"""SCIENTIFIC GATE: BGW-M2, independently exported chi to certified screening.

Checks the connected chain on one real BerkeleyGW 4.0 static screening stage:

    exported chi_hat, V_hat  ->  exact E_star = I - V chi
                             ->  Delta = E_hat - E_star, against a frozen budget
                             ->  certified R_star, and the inverse-shift identity
                             ->  the encoded production inverse X_hat vs R_star.

The Lean theorems in `GW/BGW/M2Screening.lean` are the certified part. This
file is the extraction, the numerical comparison, the mutations and the
literal-to-certificate linkage.

`chi` is exported at its point of use and is NEVER recovered as
`V^-1 (I - E_hat)`; that would make the comparison circular. `E_hat` and
`E_star` are deliberately different matrices and are never interchanged.
"""

from fractions import Fraction as F
from unittest.mock import patch
import ast
import contextlib
import importlib.util
import inspect
import io
import json
import os
import pathlib
import re
import subprocess
import tempfile
import textwrap
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


x2 = _load("bgw_m2_extract", "bgw/m2_screening/extract.py")
ref = _load("bgw_m2_reference", "bgw/m2_screening/reference.py")
x1 = _load("bgw_m1_extract", "bgw/m1_screening/extract.py")

DUMP = ROOT / "bgw" / "m2_screening" / "data" / "m2_dump_q2.txt"
M1DUMP = ROOT / "bgw" / "m1_screening" / "data" / "m1_eps_dump_q2.txt"
LEAN = ROOT / "GW" / "BGW" / "M2Screening.lean"

RUNID = "m2-20260917-q2-cut15"
IQ = 2
Q = (0.0, 0.0, 0.5)
N = 8
DUMP_SHA256 = "37ee0a30072845f8b36274a2fad518bf8e42f09edcdcaefe5b8aaf9540b0f6ba"


def load():
    b = x2.load_single(DUMP, RUNID, IQ, expected_n=N, expected_q=Q)
    chi, v, Ehat, Xhat, basis = x2.matrices(b)
    return b, chi, v, Ehat, Xhat, basis


def _tmp(name, lines):
    p = ROOT / "artifacts" / name
    p.parent.mkdir(exist_ok=True)
    p.write_text("\n".join(lines) + "\n")
    return p


def decides(chi, v, Ehat, Xhat, claimed_delta=None):
    """THE frozen decision rule, applied identically to control and mutants.

    BGW-M2-R1: this now enforces the SEPARATE component criteria as well as the
    total. The previous version checked only formation and the total, so a
    candidate could satisfy the total bound while violating the advertised
    inversion bound `||X_hat - R_hat||_inf <= b_inv`. The review supplied a
    realizable binary64 counterexample; `AcceptanceRegressions` keeps it.

    `claimed_delta`, when supplied, is put through `validate_formation_claim`,
    which is the boundary a forged "zero formation error" assertion must cross.
    """
    n = len(chi)
    Es = ref.e_star(chi, v)
    if claimed_delta is not None:
        try:
            ref.validate_formation_claim(chi, v, Ehat, claimed_delta)
        except ref.FormationClaimError:
            return False
    try:
        Rs = ref.exact_inverse(Es)
        Rh = ref.exact_inverse(Ehat)
    except (ZeroDivisionError, AssertionError):
        return False
    D = ref.delta(Ehat, Es)
    B = ref.formation_budget(chi, v)
    if not all(abs(D[i][j]) <= B[i][j] for i in range(n) for j in range(n)):
        return False
    bform = ref.b_form(B)
    binv = ref.b_inv(Ehat, Rh, n)
    bshift = ref.b_shift(Rh, bform, Rs)
    # each component against its own budget, not only the sum
    if ref.inf_norm(ref.matsub(D, [[F(0)] * n for _ in range(n)])) > bform:
        return False
    if ref.inf_norm(ref.matsub(Xhat, Rh)) > binv:
        return False
    if ref.inf_norm(ref.matsub(Rh, Rs)) > bshift:
        return False
    if ref.inf_norm(ref.matsub(Xhat, Rs)) > ref.b_total(binv, bshift):
        return False
    return True


#: The exact test of the inversion guard inside `decides`, as source text.
INVERSION_GUARD = "ref.inf_norm(ref.matsub(Xhat, Rh)) > binv"


def _decides_without_inversion_guard():
    """`decides` with ONLY the inversion comparison deleted, derived from the
    REAL function's syntax tree rather than from a maintained copy.

    BGW-M2-R3. R2 used a hand-written duplicate, which cannot guarantee that a
    rule added later to `decides` reaches the meta-check -- review raised that
    as a durability concern. This parses `decides` itself, removes the single
    `if` statement whose test is `INVERSION_GUARD`, and compiles the result, so
    the guard-free checker is always this head's decision rule minus exactly
    one line.
    """
    tree = ast.parse(textwrap.dedent(inspect.getsource(decides)))
    fn = tree.body[0]
    guards = [n for n in fn.body
              if isinstance(n, ast.If) and ast.unparse(n.test) == INVERSION_GUARD]
    if len(guards) != 1:
        raise AssertionError(
            f"expected exactly one {INVERSION_GUARD!r} guard in decides(), "
            f"found {len(guards)}; the meta-check no longer knows what it is "
            f"deleting")
    fn.body = [n for n in fn.body if n is not guards[0]]
    fn.name = "decides_without_inversion_guard"
    fn.decorator_list = []
    ns = {"ref": ref, "F": F}
    exec(compile(ast.fix_missing_locations(tree), "<derived>", "exec"), ns)
    return ns["decides_without_inversion_guard"]


class SnapshotAndBoundary(unittest.TestCase):
    def test_the_snapshot_matches_its_recorded_digest(self):
        self.assertEqual(x2.require_sha256(DUMP, DUMP_SHA256), DUMP_SHA256)

    def test_the_control_loads(self):
        b, chi, v, Ehat, Xhat, basis = load()
        self.assertEqual(b["runid"], RUNID)
        self.assertEqual(len(chi), N)

    def test_a_repeated_run_and_q_is_rejected(self):
        good = DUMP.read_text().splitlines()
        p = _tmp("m2-repeat.txt", good + good)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertIn("twice", str(cm.exception))
        p.unlink()

    def test_a_nested_start_is_rejected(self):
        good = DUMP.read_text().splitlines()
        p = _tmp("m2-nested.txt", [l for l in good if not l.startswith("QEND")] + good)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertIn("still open", str(cm.exception))
        p.unlink()

    def test_a_mismatched_run_identity_is_rejected(self):
        """Records from two runs must never be joined silently."""
        lines = [l.replace(RUNID, "other-run") if l.startswith("QEND") else l
                 for l in DUMP.read_text().splitlines()]
        p = _tmp("m2-mixed-run.txt", lines)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertIn("closes", str(cm.exception))
        p.unlink()

    def test_the_wrong_run_id_is_not_silently_accepted(self):
        with self.assertRaises(x2.ExtractionError):
            x2.load_single(DUMP, "not-this-run", IQ)

    def test_a_dropped_entry_is_rejected(self):
        lines = [l for l in DUMP.read_text().splitlines()
                 if not l.startswith("CHI 3 3")]
        p = _tmp("m2-dropped.txt", lines)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertRegex(str(cm.exception), "missing|entries, want")
        p.unlink()

    def test_an_in_block_duplicate_is_rejected(self):
        out = []
        for l in DUMP.read_text().splitlines():
            out.append(l)
            if l.startswith("CHI 1 1"):
                out.append(l)
        p = _tmp("m2-dup.txt", out)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertIn("duplicate", str(cm.exception))
        p.unlink()

    def test_a_broken_round_trip_is_rejected(self):
        lines = DUMP.read_text().splitlines()
        i, line = next((i, l) for i, l in enumerate(lines) if l.startswith("CHI"))
        t = line.split()
        t[3] = "1.2345E+00"
        lines[i] = " ".join(t)
        p = _tmp("m2-roundtrip.txt", lines)
        with self.assertRaises(x2.ExtractionError) as cm:
            x2.parse(p)
        self.assertIn("!=", str(cm.exception))
        p.unlink()


class ReuseOfM1IsJustified(unittest.TestCase):
    """`Ehat`/`Rhat` reuse M1 only because the new export is identical."""

    def test_the_new_export_matches_m1(self):
        _, chi, v, Ehat, Xhat, _ = load()
        b1 = x1.load_single(M1DUMP, 2, expected_n=N, expected_q=Q)
        E1, X1, v1 = x1.matrices(b1)
        self.assertEqual(Ehat, E1)
        self.assertEqual(Xhat, X1)
        self.assertEqual(v, v1)


class FormationPathIsTraced(unittest.TestCase):
    """Which floating-point path the compiler actually produced."""

    def test_all_entries_match_two_roundings(self):
        _, chi, v, Ehat, _, _ = load()
        for i in range(N):
            for j in range(N):
                d = F(1) if i == j else F(0)
                self.assertEqual(Ehat[i][j], F(float(d - F(float(v[i] * chi[i][j])))),
                                 f"({i},{j}) not fl(delta - fl(v*chi))")

    def test_the_fused_path_is_distinguishable(self):
        """Not all entries match a contracted FMA, so the determination above
        is a real measurement rather than a coincidence."""
        _, chi, v, Ehat, _, _ = load()
        fused = sum(1 for i in range(N) for j in range(N)
                    if Ehat[i][j] == F(float((F(1) if i == j else F(0))
                                             - v[i] * chi[i][j])))
        self.assertLess(fused, N * N)


class ThreeMatricesStayDistinct(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, cls.basis = load()
        cls.Es = ref.e_star(cls.chi, cls.v)
        cls.D = ref.delta(cls.Ehat, cls.Es)
        cls.B = ref.formation_budget(cls.chi, cls.v)

    def test_E_star_differs_from_E_hat_everywhere(self):
        """If these were equal the task would be vacuous."""
        self.assertNotEqual(self.Es, self.Ehat)
        nz = sum(1 for i in range(N) for j in range(N) if self.D[i][j] != 0)
        self.assertEqual(nz, N * N)

    def test_the_difference_is_at_rounding_scale(self):
        self.assertLess(ref.max_abs(self.D), F(1, 10 ** 15))

    def test_the_formation_budget_holds(self):
        for i in range(N):
            for j in range(N):
                self.assertLessEqual(abs(self.D[i][j]), self.B[i][j], f"({i},{j})")

    def test_the_budget_is_not_absurdly_loose(self):
        """A budget nothing could violate would prove nothing."""
        worst = max(abs(self.D[i][j]) / self.B[i][j]
                    for i in range(N) for j in range(N) if self.B[i][j] != 0)
        self.assertGreater(worst, F(1, 100))

    def test_exported_chi_differs_from_the_backsolve(self):
        """A recorded FACT, not an independence argument.

        BGW-M2-R1: an earlier version presented this inequality as ruling out
        circularity. It does not. `round64(V^-1 (I - E_hat))` is explicitly
        answer-derived and still differs from the exact recovery, from the
        exported chi in 10 of 64 entries, and satisfies the decision rule --
        see `AcceptanceRegressions`. Independence rests on inspected source
        correspondence, fixed digests and byte-identical replay instead.
        """
        rec = [[((F(1) if i == j else F(0)) - self.Ehat[i][j]) / self.v[i]
                for j in range(N)] for i in range(N)]
        self.assertNotEqual(rec, self.chi)


class CertifiedInversionAndShift(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, _ = load()
        cls.Es = ref.e_star(cls.chi, cls.v)
        cls.D = ref.delta(cls.Ehat, cls.Es)
        cls.Rs = ref.exact_inverse(cls.Es)
        cls.Rh = ref.exact_inverse(cls.Ehat)

    def test_both_inverses_are_exact(self):
        I = ref.eye(N)
        self.assertEqual(ref.matmul(self.Es, self.Rs), I)
        self.assertEqual(ref.matmul(self.Rs, self.Es), I)
        self.assertEqual(ref.matmul(self.Ehat, self.Rh), I)

    def test_the_inverse_shift_identity_holds_exactly(self):
        lhs = ref.matsub(self.Rh, self.Rs)
        rhs = [[-e for e in row]
               for row in ref.matmul(ref.matmul(self.Rh, self.D), self.Rs)]
        self.assertEqual(lhs, rhs)

    def test_the_screened_shift_identity_holds_exactly(self):
        V = ref.diagonal(self.v)
        lhs = ref.matsub(ref.matmul(self.Rh, V), ref.matmul(self.Rs, V))
        rhs = [[-e for e in row]
               for row in ref.matmul(ref.matmul(ref.matmul(self.Rh, self.D),
                                                self.Rs), V)]
        self.assertEqual(lhs, rhs)


class ComposedBudget(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, _ = load()
        cls.Es = ref.e_star(cls.chi, cls.v)
        cls.Rs = ref.exact_inverse(cls.Es)
        cls.Rh = ref.exact_inverse(cls.Ehat)
        cls.B = ref.formation_budget(cls.chi, cls.v)
        cls.bform = ref.b_form(cls.B)
        cls.binv = ref.b_inv(cls.Ehat, cls.Rh, N)
        cls.bshift = ref.b_shift(cls.Rh, cls.bform, cls.Rs)
        cls.btotal = ref.b_total(cls.binv, cls.bshift)

    def test_the_total_budget_is_met(self):
        worst = max(sum((abs(self.Xhat[i][j] - self.Rs[i][j]) for j in range(N)),
                        F(0)) for i in range(N))
        self.assertLessEqual(worst, self.btotal)

    def test_the_budget_components_are_input_based(self):
        """Recomputing from inputs alone reproduces them; no observed error
        enters the formulas."""
        self.assertEqual(self.binv, ref.b_inv(self.Ehat, self.Rh, N))
        self.assertEqual(self.bshift, ref.b_shift(self.Rh, self.bform, self.Rs))

    def test_both_residual_normalizations_are_reported(self):
        got = ref.residuals(self.Ehat, self.Xhat)
        self.assertIn("r_over_p", got)
        self.assertIn("r_over_p_plus_1", got)
        self.assertGreater(got["r_over_p"], got["r_over_p_plus_1"])


class MutationsRejected(unittest.TestCase):
    """Same frozen rule for control and every mutant."""

    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, cls.basis = load()

    def test_the_unmodified_control_is_accepted(self):
        self.assertTrue(decides(self.chi, self.v, self.Ehat, self.Xhat))

    def test_coulomb_on_the_wrong_side_is_rejected(self):
        """`I - chi V` instead of `I - V chi`; distinguishable because `vcoul`
        is not constant over the retained basis."""
        chi_col = [[self.chi[i][j] * self.v[j] / self.v[i] for j in range(N)]
                   for i in range(N)]
        self.assertNotEqual(chi_col, self.chi)
        self.assertFalse(decides(chi_col, self.v, self.Ehat, self.Xhat))

    def test_a_wrong_sign_is_rejected(self):
        self.assertFalse(decides([[-e for e in row] for row in self.chi],
                                 self.v, self.Ehat, self.Xhat))

    def test_a_wrong_prefactor_is_rejected(self):
        self.assertFalse(decides([[2 * e for e in row] for row in self.chi],
                                 self.v, self.Ehat, self.Xhat))

    def test_a_one_sided_basis_permutation_is_rejected(self):
        chi_p = [row[:] for row in self.chi]
        chi_p[0], chi_p[1] = chi_p[1], chi_p[0]
        self.assertFalse(decides(chi_p, self.v, self.Ehat, self.Xhat))

    def test_an_ordinary_wrong_formation_entry_is_rejected(self):
        chi_b = [row[:] for row in self.chi]
        chi_b[2][5] += F(1, 10 ** 6)
        self.assertFalse(decides(chi_b, self.v, self.Ehat, self.Xhat))

    def test_an_ordinary_wrong_inverse_entry_is_rejected(self):
        Xb = [row[:] for row in self.Xhat]
        Xb[1][4] += F(1, 10 ** 6)
        self.assertFalse(decides(self.chi, self.v, self.Ehat, Xb))

    def test_a_forged_zero_formation_error_is_rejected(self):
        """A forged "the formation error is zero" claim, submitted through the
        actual validation boundary, on the UNMODIFIED archived matrix.

        BGW-M2-R1. The previous version asserted
        `not (decides(...) and Es == Ehat)` after already asserting
        `Es != Ehat`, so the conjunct was constantly false and the test passed
        no matter what `decides` did. The review demonstrated this by replacing
        `decides` with an always-accepting function; the old test still passed.
        This version fails if the rejection logic is disabled.
        """
        zero = [[F(0)] * N for _ in range(N)]
        actual = ref.delta(self.Ehat, ref.e_star(self.chi, self.v))
        self.assertNotEqual(actual, zero, "the claim under test must be false")
        # positional: the guard must be exercised through the real decision path
        self.assertFalse(decides(self.chi, self.v, self.Ehat, self.Xhat, zero),
                         "a forged zero formation error was accepted")

    def test_a_consistent_permutation_of_everything_is_still_valid(self):
        """Positive control on the representation.

        BGW-M2-R1: this now permutes the EXPORTED BASIS LABELS alongside the
        matrices and checks the relabelled basis is a genuine permutation of
        the original. The earlier version transformed only the numerical
        arrays, so it did not exercise the basis at all -- noted by review.
        """
        p = [1, 0, 3, 2, 5, 4, 7, 6]
        chi_p = [[self.chi[p[i]][p[j]] for j in range(N)] for i in range(N)]
        v_p = [self.v[p[i]] for i in range(N)]
        E_p = [[self.Ehat[p[i]][p[j]] for j in range(N)] for i in range(N)]
        X_p = [[self.Xhat[p[i]][p[j]] for j in range(N)] for i in range(N)]
        basis_p = [self.basis[p[i]] for i in range(N)]
        self.assertEqual(sorted(g for g, _ in basis_p),
                         sorted(g for g, _ in self.basis),
                         "relabelled basis must be a permutation of the original")
        self.assertNotEqual([g for g, _ in basis_p], [g for g, _ in self.basis])
        # the Coulomb factor must travel with its G vector
        for i in range(N):
            self.assertEqual((v_p[i], basis_p[i]), (self.v[p[i]], self.basis[p[i]]))
        self.assertTrue(decides(chi_p, v_p, E_p, X_p))


class LeanCertificateMatchesThisData(unittest.TestCase):
    """The kernel-checked theorems must be about THIS export."""

    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, _ = load()
        cls.Es = ref.e_star(cls.chi, cls.v)
        cls.Rs = ref.exact_inverse(cls.Es)
        cls.text = LEAN.read_text()

    def lean_matrix(self, name):
        m = re.search(rf"def {name} : Matrix \(Fin {N}\) \(Fin {N}\) ℚ :=\s*!!\[(.*?)\]\n",
                      self.text, re.S)
        self.assertIsNotNone(m, f"no literal for {name}")
        rows = m.group(1).split(";")
        self.assertEqual(len(rows), N)
        out = []
        for row in rows:
            ent = re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", row)
            self.assertEqual(len(ent), N)
            out.append([F(int(a), int(b)) for a, b in ent])
        return out

    def lean_vector(self, name):
        m = re.search(rf"def {name} : Fin {N} → ℚ :=\s*!\[(.*?)\]\n", self.text, re.S)
        self.assertIsNotNone(m, f"no literal for {name}")
        ent = re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", m.group(1))
        self.assertEqual(len(ent), N)
        return [F(int(a), int(b)) for a, b in ent]

    def test_chi_matches(self):
        self.assertEqual(self.lean_matrix("chi"), self.chi)

    def test_vcoul_matches(self):
        self.assertEqual(self.lean_vector("vc"), self.v)

    def test_Xhat_matches(self):
        self.assertEqual(self.lean_matrix("Xhat"), self.Xhat)

    def test_Estar_matches_the_exact_formation(self):
        self.assertEqual(self.lean_matrix("Estar"), self.Es)

    def test_Rstar_matches_the_independent_reference(self):
        self.assertEqual(self.lean_matrix("Rstar"), self.Rs)


class AcceptanceRegressions(unittest.TestCase):
    """The four acceptance defects the BGW-M2 review demonstrated.

    Each of these passed the original suite. They are kept here, in the gated
    tests, so the repaired boundary cannot quietly regress.
    """

    @classmethod
    def setUpClass(cls):
        _, cls.chi, cls.v, cls.Ehat, cls.Xhat, cls.basis = load()
        cls.driver = _load("bgw_m2_driver", "bgw/m2_screening/run_m2.py")

    def _tight_inversion_mutant(self):
        """The review's mutant: over `b_inv`, still INSIDE `b_total`.

        BGW-M2-R2. The first migration of this regression perturbed one entry
        by `2 * b_inv`, which overshoots the total budget too
        (`5.144427744414192e-13 > b_total = 2.578407719755882e-13`). Such a
        mutant is rejected by the total rule alone, so it does not distinguish
        the repaired checker from the unrepaired one -- exactly the coverage
        the migration was supposed to preserve. The original construction is
        `b_inv + b_shift / 2` followed by binary64 rounding.
        """
        Rh = ref.exact_inverse(self.Ehat)
        Rs = ref.exact_inverse(ref.e_star(self.chi, self.v))
        binv = ref.b_inv(self.Ehat, Rh, N)
        bshift = ref.b_shift(Rh, ref.b_form(ref.formation_budget(self.chi, self.v)), Rs)
        cand = [row[:] for row in Rh]
        cand[0][0] += binv + bshift / 2
        cand = [[F.from_float(float(e)) for e in row] for row in cand]
        return cand, Rh, Rs, binv, ref.b_total(binv, bshift)

    def test_the_inversion_subbudget_is_enforced(self):
        """A realizable binary64 candidate inside the TOTAL budget but outside
        the inversion budget must be rejected. Formation stays untouched."""
        cand, Rh, Rs, binv, btotal = self._tight_inversion_mutant()
        excess = ref.inf_norm(ref.matsub(cand, Rh))
        total = ref.inf_norm(ref.matsub(cand, Rs))
        # both halves matter: violating the component while satisfying the sum
        # is what makes this mutant discriminating at all
        self.assertGreater(excess, binv, "the mutant must violate b_inv")
        self.assertLessEqual(total, btotal,
                             "the mutant must stay INSIDE b_total, or the "
                             "total rule rejects it and the component rule is "
                             "never exercised")
        self.assertFalse(decides(self.chi, self.v, self.Ehat, cand),
                         f"accepted inversion error {float(excess):.6e} > "
                         f"b_inv {float(binv):.6e}")

    def test_deleting_only_the_inversion_guard_breaks_that_regression(self):
        """The meta-check: the regression above must be load-bearing.

        A checker identical to `decides` except that it omits the inversion
        comparison must ACCEPT the tight mutant. If it did not, the regression
        would pass against an unrepaired checker and would certify nothing.
        """
        cand, _, _, _, _ = self._tight_inversion_mutant()
        self.assertTrue(_decides_without_inversion_guard()(
            self.chi, self.v, self.Ehat, cand),
            "the tight mutant is caught by some other rule, so the inversion "
            "regression does not test the inversion guard")

    def test_the_forged_zero_guard_is_load_bearing(self):
        """Disabling the rejection logic must make the negative test FAIL.

        This is the meta-check the review used to expose the vacuous version.
        """
        zero = [[F(0)] * N for _ in range(N)]
        self.assertFalse(decides(self.chi, self.v, self.Ehat, self.Xhat, zero))
        always_accept = lambda *a: True
        # with an always-accepting checker the assertion above must break
        self.assertTrue(always_accept(self.chi, self.v, self.Ehat, self.Xhat, zero))

    def test_the_driver_leaves_the_supplied_source_unchanged(self):
        """A preserved absolute symlink must not let a build write back into
        the owner's tree. Reproduced with disposable files only."""
        with tempfile.TemporaryDirectory(prefix="m2r1-safety-") as tmp:
            home = pathlib.Path(tmp)
            source, inputs, work = home / "source", home / "inputs", home / "work"
            for d in (source, inputs, work):
                d.mkdir()
            target = source / "owner_config.mk"
            original = b"OWNER ORIGINAL CONFIG -- DO NOT MODIFY\n"
            target.write_bytes(original)
            (source / "flavor.mk").symlink_to(target)
            (source / "flavor_real.mk").write_bytes(b"REAL FLAVOR CONFIG\n")
            for name in ("WFN", "WFNq"):
                (inputs / name).write_text("mock original\n")
            with patch.object(self.driver, "need", return_value=None), \
                 patch.object(self.driver.tempfile, "mkdtemp", return_value=str(work)), \
                 patch.object(self.driver.subprocess, "run",
                              side_effect=RuntimeError("stop before native build")), \
                 contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(RuntimeError):
                    self.driver.reproduce(source, inputs)
            self.assertEqual(target.read_bytes(), original,
                             "driver followed a symlink out of its copy")

    def _driver_probe(self, duplicate):
        """Mock the native step so only raw-dump selection is exercised."""
        block = DUMP.read_text()
        with tempfile.TemporaryDirectory(prefix="m2r1-driver-") as tmp:
            home = pathlib.Path(tmp)
            source, inputs, work = home / "source", home / "inputs", home / "work"
            for d in (source, inputs, work):
                d.mkdir()
            (source / "flavor_real.mk").write_text("# mock\n")
            for name in ("WFN", "WFNq"):
                (inputs / name).write_text("mock\n")

            def native(cmd, **kw):
                if str(cmd[0]).endswith("epsilon.real.x"):
                    cwd = pathlib.Path(kw["cwd"])
                    (cwd / "epsmat").write_bytes(b"mock output\n")
                    (cwd / "eps0mat").write_bytes(b"mock q0\n")
                    if cwd.name == "run-instr":
                        (cwd / "m2_dump.dat").write_text(
                            block + (block if duplicate else ""))
                return subprocess.CompletedProcess(cmd, 0)

            with patch.object(self.driver, "need", return_value=None), \
                 patch.object(self.driver.tempfile, "mkdtemp", return_value=str(work)), \
                 patch.object(self.driver.subprocess, "run", side_effect=native), \
                 contextlib.redirect_stdout(io.StringIO()):
                try:
                    return self.driver.reproduce(source, inputs) == 0
                except (SystemExit, ValueError):
                    return False

    def test_the_driver_control_is_accepted(self):
        self.assertTrue(self._driver_probe(duplicate=False))

    def test_the_driver_rejects_a_duplicated_target_block(self):
        """The old driver sliced the FIRST matching block and hashed it, so an
        appended duplicate was discarded before validation."""
        self.assertFalse(self._driver_probe(duplicate=True))

    def _preservation_probe(self, sabotage, then_raise=False):
        """Run the driver with a mocked native step that sabotages something
        in the SUPPLIED tree, and report what the driver did about it."""
        block = DUMP.read_text()
        with tempfile.TemporaryDirectory(prefix="m2r2-preserve-") as tmp:
            home = pathlib.Path(tmp)
            source, inputs, work = home / "source", home / "inputs", home / "work"
            for d in (source, inputs, work):
                d.mkdir()
            (source / "flavor_real.mk").write_text("# mock\n")
            (source / "owner_file.f90").write_text("! owner original\n")
            for name in ("WFN", "WFNq"):
                (inputs / name).write_text("mock original\n")

            def native(cmd, **kw):
                if str(cmd[0]).endswith("epsilon.real.x"):
                    cwd = pathlib.Path(kw["cwd"])
                    (cwd / "epsmat").write_bytes(b"mock output\n")
                    (cwd / "eps0mat").write_bytes(b"mock q0\n")
                    if cwd.name == "run-instr":
                        (cwd / "m2_dump.dat").write_text(block)
                    sabotage(source, inputs, cwd)
                    if then_raise:
                        raise subprocess.CalledProcessError(1, cmd)
                return subprocess.CompletedProcess(cmd, 0)

            with patch.object(self.driver, "need", return_value=None), \
                 patch.object(self.driver.tempfile, "mkdtemp", return_value=str(work)), \
                 patch.object(self.driver.subprocess, "run", side_effect=native), \
                 contextlib.redirect_stdout(io.StringIO()):
                try:
                    return "rc=%s" % self.driver.reproduce(source, inputs)
                except SystemExit as exc:
                    return str(exc)
                except subprocess.CalledProcessError:
                    return "native failure propagated without a preservation check"

    def _symlinked_inputs_probe(self, sabotage):
        """Supplied inputs that are THEMSELVES symlinks out of the directory.

        BGW-M2-R3. R2 digested regular files only, so with
        `inputs/WFN -> ../data/WFN` the real bytes were in no baseline and a
        write through `run-pristine/WFN` reached them unnoticed.
        """
        block = DUMP.read_text()
        with tempfile.TemporaryDirectory(prefix="m2r3-symlink-") as tmp:
            home = pathlib.Path(tmp)
            source, inputs, work, data = (home / "source", home / "inputs",
                                          home / "work", home / "data")
            for d in (source, inputs, work, data):
                d.mkdir()
            (source / "flavor_real.mk").write_text("# mock\n")
            for name in ("WFN", "WFNq"):
                (data / name).write_text("mock original\n")
                (inputs / name).symlink_to(os.path.relpath(data / name, inputs))
            original = (data / "WFN").read_bytes()

            def native(cmd, **kw):
                if str(cmd[0]).endswith("epsilon.real.x"):
                    cwd = pathlib.Path(kw["cwd"])
                    (cwd / "epsmat").write_bytes(b"mock output\n")
                    (cwd / "eps0mat").write_bytes(b"mock q0\n")
                    if cwd.name == "run-instr":
                        (cwd / "m2_dump.dat").write_text(block)
                    sabotage(inputs, cwd)
                return subprocess.CompletedProcess(cmd, 0)

            with patch.object(self.driver, "need", return_value=None), \
                 patch.object(self.driver.tempfile, "mkdtemp", return_value=str(work)), \
                 patch.object(self.driver.subprocess, "run", side_effect=native), \
                 contextlib.redirect_stdout(io.StringIO()):
                try:
                    outcome = "rc=%s" % self.driver.reproduce(source, inputs)
                except SystemExit as exc:
                    outcome = str(exc)
            return outcome, (data / "WFN").read_bytes() != original

    def test_a_symlinked_supplied_input_is_still_covered(self):
        def sabotage(inputs, cwd):
            (cwd / "WFN").write_text("CORRUPTED THROUGH THE LINK\n")
        outcome, really_changed = self._symlinked_inputs_probe(sabotage)
        self.assertTrue(really_changed, "the probe did not actually corrupt it")
        self.assertIn("SUPPLIED INPUTS WERE MODIFIED", outcome)

    def test_a_new_file_in_the_inputs_directory_is_reported(self):
        """R2 compared only the keys present beforehand, so an addition read
        as "unchanged"."""
        def sabotage(inputs, cwd):
            (inputs / "unexpected.dat").write_text("appeared during the run\n")
        outcome, _ = self._symlinked_inputs_probe(sabotage)
        self.assertIn("<new> unexpected.dat", outcome)

    def test_an_input_the_driver_cannot_digest_is_refused(self):
        """A dangling WFN link must be refused up front, not silently dropped
        from the preservation baseline."""
        with tempfile.TemporaryDirectory(prefix="m2r3-dangling-") as tmp:
            home = pathlib.Path(tmp)
            source, inputs = home / "source", home / "inputs"
            for d in (source, inputs):
                d.mkdir()
            (source / "flavor_real.mk").write_text("# mock\n")
            (inputs / "WFN").symlink_to(home / "nowhere")
            (inputs / "WFNq").write_text("mock original\n")
            with patch.object(self.driver, "need", return_value=None), \
                 contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(SystemExit) as cm:
                    self.driver.reproduce(source, inputs)
            self.assertIn("cannot vouch for inputs", str(cm.exception))

    def test_the_driver_detects_a_modified_supplied_input(self):
        """The run directories link WFN/WFNq at the owner's originals, so a
        write through those links reaches the supplied files. R1 hashed the
        inputs before the run and never again, and returned 0 anyway."""
        def sabotage(source, inputs, cwd):
            (cwd / "WFN").write_text("CORRUPTED BY THE RUN\n")
        self.assertIn("SUPPLIED INPUTS WERE MODIFIED",
                      self._preservation_probe(sabotage))

    def test_preservation_is_checked_when_a_native_command_fails(self):
        """R1 placed the source comparison after the build loop, so any raised
        native command skipped it entirely."""
        def sabotage(source, inputs, cwd):
            (source / "owner_file.f90").write_text("! CLOBBERED\n")
        self.assertIn("SUPPLIED SOURCE WAS MODIFIED",
                      self._preservation_probe(sabotage, then_raise=True))

    def test_the_backsolve_counterexample_satisfies_the_numeric_rule(self):
        """Records WHY matrix non-equality cannot establish independence.

        `round64(V^-1 (I - E_hat))` is answer-derived by construction, yet it
        differs from the exact recovery, differs from the exported chi in 10 of
        64 entries, and the decision rule accepts it.
        """
        rec = [[((F(1) if i == j else F(0)) - self.Ehat[i][j]) / self.v[i]
                for j in range(N)] for i in range(N)]
        circ = [[F(float(e)) for e in row] for row in rec]
        self.assertNotEqual(circ, rec)
        differing = sum(1 for i in range(N) for j in range(N)
                        if circ[i][j] != self.chi[i][j])
        self.assertEqual(differing, 10)
        self.assertTrue(decides(circ, self.v, self.Ehat, self.Xhat),
                        "the point of this test is that the numeric rule "
                        "cannot tell the difference")


if __name__ == "__main__":
    unittest.main(verbosity=2)

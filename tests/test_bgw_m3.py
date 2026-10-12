#!/usr/bin/env python3
"""SCIENTIFIC GATE: BGW-M3, one chi block's transition-sum provenance.

M2 took `chi` as an input. This module checks the step above it: that the
exported chi entries are the sum over transitions of the UNWEIGHTED matrix
elements, the occupations and the energy denominators.

The distinction is the whole point. `Epsilon/mtxel.f90` says

    ! In the static case, we lump sqrt(eden) into the matrix elements gme.

so `pol%gme` is already weighted by the time the matrix product runs. An
export taken there would make "reconstructed from physical operands" vacuous.
`GMERAW` is taken immediately before that multiply.

The reference never reads the exported `eden` either: it recomputes the
quotient from `eval`, `econd`, `occ_v`, `occ_c`. `eden` is separately checked
to BE that quotient, correctly rounded.
"""

from fractions import Fraction as F
import copy
import hashlib
import importlib.util
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def _load(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


x3 = _load("bgw_m3_extract", "bgw/m3_chi/extract.py")
ref = _load("bgw_m3_reference", "bgw/m3_chi/reference.py")
x2 = _load("bgw_m2_extract", "bgw/m2_screening/extract.py")
gen = _load("bgw_m3_gen", "bgw/m3_chi/make_certificate.py")
link = _load("bgw_m3_link", "bgw/m3_chi/link_m2.py")
mut = _load("bgw_m3_mutate", "bgw/m3_chi/mutate_certificate.py")

DUMP = ROOT / "bgw" / "m3_chi" / "data" / "m3_dump_q2.txt"
CHIDUMP = ROOT / "bgw" / "m3_chi" / "data" / "m3_chi_q2.txt"
LEAN = ROOT / "GW" / "BGW" / "M3Chi.lean"
TRANSFER = ROOT / "GW" / "BGW" / "M3Transfer.lean"
MUTLOG = ROOT / "bgw" / "m3_chi" / "evidence" / "mutations.log"

RUNID = "m3-20260919-q2-cut15"
IQ, N, NRK = 2, 8, 5
Q = (0.0, 0.0, 0.5)
DUMP_SHA256 = "36ba3844d52c448c4ae6712372c46f627cc28f3c44dd97af7dad647a946b7fed"
CHI_SHA256 = "48b5f3f19b944d285820834af6e40e3fa063d958e24c996a04816da624776175"

#: The run's own inventory, stated here from the specification side so a
#: shrunken export cannot narrow what it is checked against.
EXPECTED_TRANSITIONS = 280
EXPECTED_COLUMNS = 1792


def load():
    b = x3.load_single(DUMP, RUNID, IQ, expected_n=N, expected_nrk=NRK)
    chi, _, _, _, _ = x2.matrices(
        x2.load_single(CHIDUMP, RUNID, IQ, expected_n=N, expected_q=Q))
    return b, chi


def decides(block, chi):
    """THE frozen decision rule, applied identically to control and mutants.

    Every entry of the reconstructed matrix must sit inside its own budget,
    the inventory must be the expected one, and every exported denominator
    must be the correctly rounded quotient of its own operands.
    """
    inv = ref.inventory(block)
    if inv["transitions"] != EXPECTED_TRANSITIONS:
        return False
    if inv["columns"] != EXPECTED_COLUMNS:
        return False
    if ref.occupation_check(block):
        return False
    X = ref.exact_matrix(block)
    B = ref.budget_matrix(block)
    n = block["n"]
    return all(abs(chi[i][j] - X[i][j]) <= B[i][j]
               for i in range(n) for j in range(n))


def _tmp(name, text):
    p = ROOT / "artifacts" / name
    p.parent.mkdir(exist_ok=True)
    p.write_text(text)
    return p


class SnapshotAndBoundary(unittest.TestCase):
    def test_both_snapshots_match_their_digests(self):
        self.assertEqual(x3.require_sha256(DUMP, DUMP_SHA256), DUMP_SHA256)
        self.assertEqual(x3.require_sha256(CHIDUMP, CHI_SHA256), CHI_SHA256)

    def test_the_control_loads(self):
        b, chi = load()
        self.assertEqual(b["runid"], RUNID)
        self.assertEqual(b["n"], N)
        self.assertEqual(b["nrk"], NRK)
        self.assertEqual(len(chi), N)

    def test_a_repeated_block_is_rejected(self):
        good = DUMP.read_text()
        p = _tmp("m3-repeat.txt", good + good)
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("twice", str(cm.exception))
        p.unlink()

    def test_an_unterminated_block_is_rejected(self):
        lines = [l for l in DUMP.read_text().splitlines()
                 if not l.startswith("TEND")]
        p = _tmp("m3-open.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("never closed", str(cm.exception))
        p.unlink()

    def test_a_record_outside_a_block_is_rejected(self):
        lines = DUMP.read_text().splitlines()
        p = _tmp("m3-outside.txt", "\n".join(lines + [lines[5]]) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("outside any q block", str(cm.exception))
        p.unlink()

    def test_an_unknown_record_is_rejected(self):
        lines = DUMP.read_text().splitlines()
        lines.insert(3, "SURPRISE 1 2 3")
        p = _tmp("m3-unknown.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("unknown record", str(cm.exception))
        p.unlink()

    def test_a_mismatched_closing_identity_is_rejected(self):
        lines = [l.replace(RUNID, "other-run") if l.startswith("TEND") else l
                 for l in DUMP.read_text().splitlines()]
        p = _tmp("m3-mixed.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("closes", str(cm.exception))
        p.unlink()

    def test_a_decimal_that_disagrees_with_its_bits_is_rejected(self):
        lines = DUMP.read_text().splitlines()
        for k, l in enumerate(lines):
            if l.startswith("GMERAW"):
                f = l.split()
                f[6] = "9.99999999999999999E+00"
                lines[k] = " ".join(f)
                break
        p = _tmp("m3-bits.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("does not match its bit pattern", str(cm.exception))
        p.unlink()

    def test_a_dropped_matrix_element_component_is_rejected(self):
        lines = [l for l in DUMP.read_text().splitlines()
                 if not l.startswith("GMERAW 1 1 1 5 3")]
        p = _tmp("m3-dropped-gme.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("missing components", str(cm.exception))
        p.unlink()

    def test_a_dropped_symmetry_map_row_is_rejected(self):
        lines = [l for l in DUMP.read_text().splitlines()
                 if not l.startswith("MAP 1 1 3 ")]
        p = _tmp("m3-dropped-map.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("missing", str(cm.exception))
        p.unlink()

    def test_a_dropped_transition_breaks_the_key_agreement(self):
        lines = [l for l in DUMP.read_text().splitlines()
                 if not l.startswith("EDEN 1 1 1 5 ")]
        p = _tmp("m3-dropped-eden.txt", "\n".join(lines) + "\n")
        with self.assertRaises(x3.ExtractionError) as cm:
            x3.parse(p)
        self.assertIn("disagree on transitions", str(cm.exception))
        p.unlink()


class TheInventoryIsComplete(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.b, cls.chi = load()

    def test_every_transition_is_accounted_for(self):
        inv = ref.inventory(self.b)
        self.assertEqual(inv["transitions"], EXPECTED_TRANSITIONS)
        self.assertEqual(inv["columns"], EXPECTED_COLUMNS)
        self.assertEqual(len(inv["kept"]) + len(inv["skipped"]),
                         EXPECTED_TRANSITIONS)

    def test_this_run_exercises_no_skipped_transition(self):
        """Stated as a LIMITATION, not as coverage.

        `get_eden` zeroes forbidden transitions. This run has none, so the
        reconstruction never exercises that branch, and nothing here is
        evidence that it would be handled correctly.
        """
        self.assertEqual(ref.inventory(self.b)["skipped"], [])

    def test_the_run_sits_far_from_both_branch_tolerances(self):
        """A transition near a branch boundary would make the reference's
        branch choice a guess rather than a determination."""
        m = ref.tolerance_margin(self.b)
        self.assertGreater(float(m["min_abs_energy_gap"]), 0.2)
        self.assertEqual(m["min_abs_occ_diff"], F(1))

    def test_the_star_inventory_matches_the_symmetry_map(self):
        self.assertEqual(sorted(self.b["nst"]), list(range(1, NRK + 1)))
        self.assertEqual(ref.star_count(self.b), EXPECTED_COLUMNS)


class TheDenominatorIsNotTakenOnTrust(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.b, cls.chi = load()

    def test_the_exported_denominator_matches_the_two_rounding_model(self):
        """PYTHON, EMPIRICAL. Not a Lean theorem and not a rounding proof.

        Lean proves a *bound* on `|edenHat - dStar|` (`rowOK` / `row_bound`);
        it does not formalize IEEE rounding at all. This check is the separate
        empirical statement: for this compiler and these operands, all 280
        exported denominators equal `fl(occ_diff / fl(eval - econd))`.
        """
        self.assertEqual(ref.occupation_check(self.b), [])

    def test_the_single_rounding_model_does_not_fit(self):
        """The empirical determination, recorded as a test.

        `eden` is NOT `fl(occ_diff / (eval - econd))` with the difference taken
        exactly: that fails on 69 of the 280 transitions. It is
        `fl(occ_diff / fl(eval - econd))` -- the subtraction is its own
        rounding -- which fits all 280. This is a measurement about this
        compiler and these operands, not a theorem about the compiled code.
        """
        one_rounding = 0
        for key in self.b["TRANS"]:
            if self.b["EDEN"][key] == F(float(ref.eden_exact(self.b, key))):
                one_rounding += 1
        self.assertEqual(one_rounding, 211)
        self.assertEqual(len(self.b["TRANS"]) - one_rounding, 69)

    def test_the_reference_does_not_read_the_exported_denominator(self):
        """Corrupting every exported `eden` must not change the reference."""
        b2 = copy.deepcopy(self.b)
        for key in b2["EDEN"]:
            b2["EDEN"][key] = F(-1, 3)
        self.assertEqual(ref.exact_matrix(b2), ref.exact_matrix(self.b))


class TheReconstructionMatches(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.b, cls.chi = load()
        cls.X = ref.exact_matrix(cls.b)
        cls.B = ref.budget_matrix(cls.b)

    def test_the_unmodified_control_is_accepted(self):
        self.assertTrue(decides(self.b, self.chi))

    def test_every_entry_is_inside_its_budget(self):
        bad = [(i, j) for i in range(N) for j in range(N)
               if abs(self.chi[i][j] - self.X[i][j]) > self.B[i][j]]
        self.assertEqual(bad, [])

    def test_the_budget_has_a_production_part_and_a_proved_transfer_part(self):
        """The two halves must both be present and the transfer must be the
        small one -- if the transfer dominated, the denominator rounding would
        be the limiting error and the analysis would need revisiting."""
        for (i, j) in gen.TARGETS:
            prod = ref.production_bound(self.b, i, j)
            tran = ref.transfer_bound(self.b, i, j)
            self.assertGreater(prod, 0)
            self.assertGreater(tran, 0)
            self.assertEqual(ref.budget(self.b, i, j), prod + tran)
            self.assertLess(tran, prod)

    def test_the_sqrt_rounding_is_charged_twice(self):
        """The single rounded `sqrt(-eden)` multiplies BOTH weighted matrix
        elements, so it enters each product squared. R1 review found the
        original M3 budget charged it once."""
        self.assertEqual(ref.ROUNDINGS_PER_TERM, 5)

    def test_the_budget_is_not_slack_enough_to_be_meaningless(self):
        """A budget that admitted anything would prove nothing. The worst
        entry uses a nonzero fraction of its allowance."""
        worst = max(float(abs(self.chi[i][j] - self.X[i][j]) / self.B[i][j])
                    for i in range(N) for j in range(N))
        self.assertGreater(worst, 1e-4)
        self.assertLess(worst, 1.0)

    def test_the_budget_never_reads_the_exported_value(self):
        """Scaling the production chi must not move the budget."""
        before = ref.budget_matrix(self.b)
        chi2 = [[2 * v for v in row] for row in self.chi]
        self.assertEqual(ref.budget_matrix(self.b), before)
        self.assertFalse(decides(self.b, chi2))

    def test_the_reconstruction_has_the_expected_term_count(self):
        self.assertEqual(len(ref.terms(self.b, 1, 1)), EXPECTED_COLUMNS)
        self.assertEqual(len(ref.terms(self.b, 1, 2)), EXPECTED_COLUMNS)


class MutationsRejected(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.b, cls.chi = load()

    def test_a_dropped_transition_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        key = sorted(b2["gme"])[0]
        for d in ("gme", "EDEN", "KFACT", "SLOT", "TRANS"):
            del b2[d][key]
        self.assertFalse(decides(b2, self.chi))

    def test_a_wrong_occupation_difference_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        key = sorted(b2["TRANS"])[0]
        ev, ec, ov, oc = b2["TRANS"][key]
        b2["TRANS"][key] = (ev, ec, ov * 2, oc)
        self.assertFalse(decides(b2, self.chi))

    def test_swapping_the_two_energies_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        key = sorted(b2["TRANS"])[0]
        ev, ec, ov, oc = b2["TRANS"][key]
        b2["TRANS"][key] = (ec, ev, ov, oc)
        self.assertFalse(decides(b2, self.chi))

    def test_dropping_a_phase_on_one_side_only_is_rejected(self):
        """A conjugation/transpose-style error that is NOT a symmetry here.

        The phase is flipped for ONE basis index only. That deliberately
        leaves the diagonal entry (1,1) unchanged -- the two factors cancel --
        so the rejection has to come from the off-diagonal entries, which is
        why the rule reads all 64 and not just the two certified ones.

        An earlier version of this mutation flipped only phases already equal
        to -1 at index 1, of which there are none, so it changed nothing and
        the test passed vacuously. The `flipped` guard below exists because
        that actually happened.
        """
        b2 = copy.deepcopy(self.b)
        flipped = 0
        for (irk, it, ia), (ind, ph) in list(b2["map"].items()):
            if ia == 1:
                b2["map"][(irk, it, ia)] = (ind, -ph)
                flipped += 1
        self.assertGreater(flipped, 0, "the mutation must actually change something")
        self.assertFalse(decides(b2, self.chi))

    def test_a_permuted_symmetry_map_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        for (irk, it, ia), (ind, ph) in list(b2["map"].items()):
            if ia == 1:
                other = b2["map"][(irk, it, 2)][0]
                b2["map"][(irk, it, ia)] = (other, ph)
        self.assertFalse(decides(b2, self.chi))

    def test_a_perturbed_matrix_element_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        key = sorted(b2["gme"])[0]
        b2["gme"][key][1] = b2["gme"][key][1] * F(1001, 1000)
        self.assertFalse(decides(b2, self.chi))

    def test_the_wrong_prefactor_is_rejected(self):
        b2 = copy.deepcopy(self.b)
        b2["scalars"]["FACT"] = b2["scalars"]["FACT"] * 2
        self.assertFalse(decides(b2, self.chi))


class TheChiBlockIsTheOneM2Consumed(unittest.TestCase):
    """BGW-M3-R1 item 6: executable, not prose in a log."""

    def test_the_two_blocks_are_the_same_data(self):
        info = link.check()
        self.assertEqual(info["lines"], 210)
        self.assertIn("chi", info["matrices"])

    def test_the_check_rejects_a_changed_value(self):
        """The linkage must not pass just because the files are both present."""
        text = link.M3_CHI.read_text().splitlines()
        for k, l in enumerate(text):
            if l.startswith("CHI 1 1"):
                f = l.split()
                f[3] = "1.0"
                text[k] = " ".join(f)
                break
        p = ROOT / "artifacts" / "m3-link-mutant.txt"
        p.parent.mkdir(exist_ok=True)
        p.write_text("\n".join(text) + "\n")
        real = link.M3_CHI
        try:
            link.M3_CHI = p
            with self.assertRaises(link.LinkError):
                link.check()
        finally:
            link.M3_CHI = real
            p.unlink()

    def test_the_check_rejects_a_foreign_run_id(self):
        with self.assertRaises(link.LinkError):
            link.normalised(link.M3_CHI, "not-this-run")


class LeanCertificateMatchesThisData(unittest.TestCase):
    def test_the_module_regenerates_from_the_committed_dump(self):
        rc = subprocess.run(
            [sys.executable, str(ROOT / "bgw/m3_chi/make_certificate.py"), "--check"],
            cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(rc.returncode, 0, rc.stdout + rc.stderr)

    def test_the_certified_entries_are_the_ones_measured_here(self):
        b, chi = load()
        text = LEAN.read_text()
        for (i, j) in gen.TARGETS:
            want = chi[i - 1][j - 1]
            needle = (f"def chiHat{i}{j} : ℚ := (({want.numerator} : ℚ) / "
                      f"{want.denominator})")
            self.assertIn(needle, text,
                          f"chiHat{i}{j} literal is not this run's exported value")

    def test_neither_lean_module_uses_a_forbidden_device(self):
        for path in (LEAN, TRANSFER):
            text = path.read_text()
            for bad in ("sorry", "admit", "native_decide", "axiom "):
                self.assertNotIn(bad, text, f"{path.name} contains {bad!r}")

    def test_the_endpoint_theorems_take_no_hypotheses(self):
        """The whole point of R1. An endpoint that still accepted an
        arbitrary `reconExact`, a denominator-transfer inequality, or an
        operand-to-product identity as a hypothesis would not close the
        chain."""
        text = LEAN.read_text()
        for (i, j) in gen.TARGETS:
            sig = (f"theorem entry{i}{j}_endpoint : "
                   f"absQ (chiHat{i}{j} - chiStar{i}{j}) ≤ finalBudget{i}{j} := by")
            self.assertIn(sig, text)
        self.assertNotIn("reconExact", text)

    def test_chi_star_is_defined_from_the_raw_operand_table(self):
        """The endpoint target must not read generated product/difference
        witnesses. `rawRows` recomputes them from matrix elements, maps,
        energies and occupations before `chiStar` is formed."""
        text = LEAN.read_text()
        for (i, j) in gen.TARGETS:
            self.assertIn(
                f"def chiStar{i}{j} : ℚ := "
                f"(rawRows{i}{j}.map (fun r => r.coefQ S * r.dStarQ S)).sum", text)
        self.assertIn("qw := qOf stars t.g", text)
        self.assertIn("dZ := t.evZ - t.ecZ", text)
        self.assertIn("oZ := t.ovZ - t.ocZ", text)
        self.assertIn(
            "theorem rows11_eq_rawRows11 : rows11 = rawRows11 := by rfl", text)
        self.assertIn(
            "theorem rows12_eq_rawRows12 : rows12 = rawRows12 := by rfl", text)

    def test_the_correspondence_obligations_are_present(self):
        text = LEAN.read_text()
        for name in ("theorem products_correct : qwOK = true := by rfl",
                     "theorem rows11_eq_rawRows11 : rows11 = rawRows11 := by rfl",
                     "theorem rows12_eq_rawRows12 : rows12 = rawRows12 := by rfl",
                     "theorem rows_ok11 : rows11.all (rowOK S) = true := by rfl",
                     "theorem rows_ok12 : rows12.all (rowOK S) = true := by rfl"):
            self.assertIn(name, text)

    def test_the_certificate_is_in_the_build_and_the_audit(self):
        gw = (ROOT / "GW.lean").read_text()
        self.assertIn("import GW.BGW.M3Transfer", gw)
        self.assertIn("import GW.BGW.M3Chi", gw)
        audit = (ROOT / "GW" / "Audit.lean").read_text()
        for name in ("entry11_endpoint", "entry12_endpoint", "products_correct",
                     "rows11_eq_rawRows11", "rows12_eq_rawRows12",
                     "rows_ok11", "rows_ok12", "transfer_bound11",
                     "table_transfer", "row_bound", "abs_sub_div_le"):
            self.assertIn(f"GW.BGW.M3.{name}", audit)


class DiscriminatingMutationsWereRun(unittest.TestCase):
    """BGW-M3-R1 item 5. The committed log is acceptable only when it is
    bound to the current sources, the pristine control elaborated, and each
    mutant first failed at the intended correspondence declaration."""

    @classmethod
    def setUpClass(cls):
        cls.text = MUTLOG.read_text() if MUTLOG.exists() else ""

    def test_the_classifier_does_not_blame_a_later_definition_on_a_theorem(self):
        source = (
            "theorem products_correct : True := by trivial\n"
            "\n"
            "def unrelatedDefinition : Nat := 0\n")
        output = "GW/BGW/M3Mutant.lean:3:5: error: synthetic failure\n"
        self.assertEqual(
            mut.attributed_to(output, source),
            ["def unrelatedDefinition"])

    def test_the_residual_mutation_breaks_only_the_residual_identity(self):
        mutant, expect = mut.mutate_residual(LEAN.read_text())
        self.assertEqual(expect, "theorem rows_ok11")
        checks = mut.first_residual_witness_checks(mutant)
        self.assertEqual(
            checks,
            {
                "energy_difference": True,
                "occupation_difference": True,
                "nonzero_denominator": True,
                "residual_identity": False,
                "allowance": True,
            })

    def test_the_log_exists(self):
        self.assertTrue(MUTLOG.exists(), f"{MUTLOG} was never generated")

    def test_the_log_is_bound_to_the_current_sources(self):
        lean_sha = hashlib.sha256(LEAN.read_bytes()).hexdigest()
        mut_sha = hashlib.sha256(
            (ROOT / "bgw/m3_chi/mutate_certificate.py").read_bytes()).hexdigest()
        self.assertIn(f"M3Chi.lean sha256: {lean_sha}", self.text)
        self.assertIn(f"mutate_certificate.py sha256: {mut_sha}", self.text)

    def test_the_unmodified_control_elaborated(self):
        self.assertIn("--- unmodified control ---", self.text)
        section = self.text.split("--- unmodified control ---", 1)[1].split(
            "--- product witness mutation ---", 1)[0]
        self.assertIn("lean exit code              : 0", section)
        self.assertIn("verdict                     : OK", section)

    def test_the_product_mutation_failed_first_at_product_correspondence(self):
        self.assertIn(
            "expected first declaration  : theorem products_correct", self.text)
        self.assertIn(
            "first failing declaration   : theorem products_correct", self.text)

    def test_the_residual_mutation_failed_first_at_residual_correspondence(self):
        self.assertIn(
            "expected first declaration  : theorem rows_ok11", self.text)
        self.assertIn(
            "first failing declaration   : theorem rows_ok11", self.text)

    def test_control_and_both_mutations_are_valid_evidence(self):
        self.assertEqual(self.text.count("verdict                     : OK"), 3)
        self.assertNotIn("CONTROL FAILED", self.text)
        self.assertNotIn("NOT DISCRIMINATING", self.text)


if __name__ == "__main__":
    unittest.main(verbosity=2)

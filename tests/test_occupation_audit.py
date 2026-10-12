#!/usr/bin/env python3
"""Tests for the T-003 occupation-reachability checker.

Extended under T-003-R1 to close review findings F1 and F2
(`.agent/handoffs/CODEX-T-003-REVIEW.md`). The negative cases are Codex's exact
mutations from `artifacts/t003-codex-review/checker-mutation-results.json`,
driven through the real entry point `check_occupation.main`, not through
assertions that a diagnostic scalar moved.

Positive cases guard the other direction: the archived records, the
supervisor's freshly generated records, and a legitimate one-ulp perturbation
must all still pass, so the repair is not a hair trigger.

These test the checker, not BerkeleyGW.
"""

from fractions import Fraction as F
import contextlib
import io
import json
import math
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "occupation_audit"))

import check_occupation as co  # noqa: E402

FIXTURES = ROOT / "bgw" / "occupation_audit" / "fixtures"
RECORDS = FIXTURES / "t003_nearpole_occ.dat"
PROBE = FIXTURES / "fermi_branch_occ_counts.dat"
CONTROL = FIXTURES / "control_branch_occ_counts.dat"
CODEX_FRESH = (ROOT / "artifacts" / "t003-codex-review" / "runs" / "fermi"
               / "t003_nearpole_occ.dat")
CODEX_CASES = (ROOT / "artifacts" / "t003-codex-review"
               / "checker-mutation-results.json")

RECORD_LINES = RECORDS.read_text().splitlines()


def run_main(argv):
    """Call the entry point, swallowing its JSON. Returns (exit, parsed)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = co.main(argv)
    return rc, json.loads(buf.getvalue())


def with_field(name, value, lines=None):
    """Archived records with field `name` of the FIRST record replaced."""
    lines = list(lines or RECORD_LINES)
    toks = lines[0].split()
    toks[co.FIELDS.index(name)] = value
    lines[0] = " ".join(toks)
    return "\n".join(lines) + "\n"


def write(tmp, name, text):
    p = pathlib.Path(tmp) / name
    p.write_text(text)
    return str(p)


def make_record(**over):
    """A self-consistent synthetic near-pole, occ != 1 record (29 fields).

    All derived intermediates are computed here so the record satisfies the
    repaired contract; each test then breaks exactly one thing.
    """
    wt, x, ieps, occ, iw = 12.0, 12.3, -0.002, 0.5, 2
    e_n1kq = -2.5
    e_lk = x + e_n1kq - (iw - 2) * co.SIG_DW
    wt2 = wt * wt
    omega2 = wt2 * ieps
    wdiff = x - wt
    delw = wt / wdiff
    den_np = 4 * wt2 * (delw + 0.5)
    ssx = -omega2 * delw / den_np
    f = dict(
        rec=1, n1true=1, iw=iw, igp=2, ig=4, branch=2,
        occ=occ, vcoul=0.01, ieps=ieps, wtilde_re=wt, wtilde_im=0.0,
        wtilde2=wt2, wxt=x, omega2=omega2, delw=delw,
        delwr=delw * delw, wdiffr=wdiff * wdiff,
        limittwo=co.LIMITTWO, limitone=co.LIMITONE,
        ssx_pre=ssx, ssx_post=ssx, sch=0.0,
        den_generic=x * x - wt2, den_nearpole=den_np,
        den_merged=2 * wt * (x + wt),
        e_lk=e_lk, e_n1kq=e_n1kq, efermi=e_n1kq, occ_broadening=0.1,
    )
    f.update(over)
    ints = " ".join(str(f[k]) for k in co.FIELDS[:co.N_INT])
    reals = " ".join(f"{f[k]:.17E}" for k in co.FIELDS[co.N_INT:])
    return ints + " " + reals


# ---------------------------------------------------------------- F1/F2 cases

class CodexMutationTests(unittest.TestCase):
    """Codex's exact review mutations, driven through `main`.

    Pre-repair every one of these exited 0. The baseline must still pass; the
    one-record case must fail full-fixture validation but pass explicitly
    labelled subset analysis.
    """

    #: values as stated in CODEX-T-003-REVIEW.md findings F1 and F2
    FIELD_MUTATIONS = {
        "corrupt_sch": ("sch", "1.00000000000000000E+00"),
        "corrupt_omega2": ("omega2", "9.99999000000000000E+05"),
        "corrupt_ssx_pre": ("ssx_pre", "9.99999000000000000E+05"),
        "corrupt_efermi": ("efermi", "9.99999000000000000E+05"),
        "corrupt_den_nearpole": ("den_nearpole", "0.00000000000000000E+00"),
    }

    def setUp(self):
        self.tmp = pathlib.Path(
            __import__("tempfile").mkdtemp(prefix="t003r1-"))

    def tearDown(self):
        __import__("shutil").rmtree(self.tmp, ignore_errors=True)

    def test_case_list_matches_the_review_evidence(self):
        """Count the cases from Codex's data, not from prose totals."""
        cases = json.loads(CODEX_CASES.read_text())
        names = [c["case"] for c in cases]
        self.assertIn("original_saved_witness", names)
        self.assertEqual(len(cases), 9)
        # every case name is covered by this test class
        covered = (set(self.FIELD_MUTATIONS)
                   | {"original_saved_witness", "one_record_only",
                      "same_record_duplicated_48_times", "negative_event_count"})
        self.assertEqual(set(names), covered)
        # all nine exited 0 before the repair
        self.assertTrue(all(c["exit_code"] == 0 for c in cases))

    def test_baseline_still_passes(self):
        rc, out = run_main([str(RECORDS), "--counts", str(PROBE),
                            "--control-counts", str(CONTROL)])
        self.assertEqual(rc, 0)
        self.assertTrue(out["coverage"]["full_fixture_validated"])
        self.assertEqual(out["records"], 48)

    def test_corrupted_fields_are_rejected(self):
        for case, (name, value) in self.FIELD_MUTATIONS.items():
            with self.subTest(case=case):
                p = write(self.tmp, case + ".dat", with_field(name, value))
                with self.assertRaises(co.RecordError):
                    run_main([p, "--counts", str(PROBE),
                              "--control-counts", str(CONTROL)])

    def test_one_record_fails_full_fixture_validation(self):
        p = write(self.tmp, "one.dat", RECORD_LINES[0] + "\n")
        with self.assertRaises(co.RecordError) as cm:
            run_main([p, "--counts", str(PROBE),
                      "--control-counts", str(CONTROL)])
        self.assertIn("--subset", str(cm.exception))

    def test_one_record_passes_labelled_subset_analysis(self):
        p = write(self.tmp, "one.dat", RECORD_LINES[0] + "\n")
        rc, out = run_main([p, "--counts", str(PROBE),
                            "--control-counts", str(CONTROL), "--subset"])
        self.assertEqual(rc, 0)
        self.assertEqual(out["coverage"]["mode"], "subset")
        self.assertFalse(out["coverage"]["full_fixture_validated"])

    def test_duplicated_record_is_rejected(self):
        p = write(self.tmp, "dup.dat", "\n".join([RECORD_LINES[0]] * 48) + "\n")
        with self.assertRaises(co.RecordError) as cm:
            run_main([p, "--counts", str(PROBE),
                      "--control-counts", str(CONTROL)])
        self.assertIn("duplicate record ids", str(cm.exception))

    def test_duplicated_record_is_rejected_in_subset_mode_too(self):
        p = write(self.tmp, "dup.dat", "\n".join([RECORD_LINES[0]] * 48) + "\n")
        with self.assertRaises(co.RecordError):
            run_main([p, "--counts", str(PROBE),
                      "--control-counts", str(CONTROL), "--subset"])

    def test_negative_event_count_is_rejected(self):
        bad = write(self.tmp, "neg.counts",
                    PROBE.read_text().replace("3702", "  -1"))
        with self.assertRaises(co.RecordError) as cm:
            run_main([str(RECORDS), "--counts", bad,
                      "--control-counts", str(CONTROL)])
        self.assertIn("negative count", str(cm.exception))


# --------------------------------------------------------------- positive side

class PositiveTests(unittest.TestCase):
    def test_archived_records_pass(self):
        rc, _ = run_main([str(RECORDS), "--counts", str(PROBE),
                          "--control-counts", str(CONTROL)])
        self.assertEqual(rc, 0)

    @unittest.skipUnless(CODEX_FRESH.exists(), "supervisor fresh run not present")
    def test_supervisor_fresh_records_pass(self):
        rc, out = run_main([str(CODEX_FRESH), "--counts", str(PROBE),
                            "--control-counts", str(CONTROL)])
        self.assertEqual(rc, 0)
        self.assertEqual(out["records"], 48)

    def test_accepted_numbers_are_preserved(self):
        """The repair must not change the accepted T-002/T-003 results."""
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        self.assertEqual(out["max_fp_residual"], 4.2435598287864196e-19)
        self.assertAlmostEqual(out["max_abs_mismatch_exact"], 6.557715697780925,
                               places=12)
        self.assertAlmostEqual(out["max_mismatch_over_local_value"],
                               13735.130950092715, places=6)
        self.assertEqual(out["probe_counts"]["branch2"], [76461, 3702])

    def test_exported_records_are_not_claimed_to_be_the_event_count(self):
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        d = out["exported_records_vs_counted_events"]
        self.assertEqual(d["exported_records"], 48)
        self.assertEqual(d["counted_qualifying_events"], 3702)

    def test_unmodeled_fields_are_labelled_not_claimed_verified(self):
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        self.assertIn("vcoul", out["unmodeled_fields"])
        self.assertIn("occ_broadening", out["unmodeled_fields"])
        # occ_broadening must be described as a stored default, not smearing
        self.assertIn("does NOT mean smearing is on",
                      out["unmodeled_fields"]["occ_broadening"])

    def test_residual_limits_have_headroom_over_observed_maxima(self):
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        for name, spec in out["residual_limits"].items():
            with self.subTest(field=name):
                observed = out["max_intermediate_residuals"][name]
                self.assertLess(observed, spec["limit"])
                self.assertGreater(spec["limit"] / max(observed, 1e-300), 10.0)


class NotAHairTriggerTests(unittest.TestCase):
    """A legitimate rounding-scale perturbation must still be accepted."""

    def setUp(self):
        self.tmp = pathlib.Path(
            __import__("tempfile").mkdtemp(prefix="t003r1-hair-"))

    def tearDown(self):
        __import__("shutil").rmtree(self.tmp, ignore_errors=True)

    def _omega2_perturbed(self, factor):
        rec0 = co.parse(RECORD_LINES[0] + "\n")[0]
        base = rec0["omega2"]
        return with_field("omega2", repr(base * (1.0 + factor)))

    def test_one_ulp_perturbation_is_accepted(self):
        p = write(self.tmp, "ulp.dat", self._omega2_perturbed(2 ** -52))
        rc, _ = run_main([p, "--counts", str(PROBE),
                          "--control-counts", str(CONTROL)])
        self.assertEqual(rc, 0)

    def test_relative_perturbation_just_under_the_limit_is_accepted(self):
        p = write(self.tmp, "under.dat", self._omega2_perturbed(1e-15))
        rc, _ = run_main([p, "--counts", str(PROBE),
                          "--control-counts", str(CONTROL)])
        self.assertEqual(rc, 0)

    def test_relative_perturbation_above_the_limit_is_rejected(self):
        p = write(self.tmp, "over.dat", self._omega2_perturbed(1e-12))
        with self.assertRaises(co.RecordError):
            run_main([p, "--counts", str(PROBE),
                      "--control-counts", str(CONTROL)])

    def test_den_generic_cancellation_is_not_flagged(self):
        """`wxt**2 - wtilde2` loses ~2700 ulps to cancellation legitimately."""
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        spec = out["residual_limits"]["den_generic"]
        self.assertIn("cancellation", spec["kind"])
        self.assertLess(out["max_intermediate_residuals"]["den_generic"],
                        spec["limit"])


# ---------------------------------------------------------------- unit pieces

class ParserTests(unittest.TestCase):
    def test_empty_input_is_rejected(self):
        for text in ("", "\n\n", "# only a comment\n"):
            with self.assertRaises(co.RecordError):
                co.parse(text)

    def test_wrong_field_count_is_rejected(self):
        """Exactly the Fortran format-reversion bug hit during T-003."""
        short = " ".join(make_record().split()[:26])
        with self.assertRaises(co.RecordError) as cm:
            co.parse(short + "\n")
        self.assertIn("format reversion", str(cm.exception))

    def test_nonfinite_is_rejected_not_reported(self):
        for bad in ("NaN", "Infinity", "-Infinity"):
            toks = make_record().split()
            toks[co.FIELDS.index("ssx_post")] = bad
            with self.assertRaises(co.RecordError) as cm:
                co.parse(" ".join(toks) + "\n")
            self.assertIn("not finite", str(cm.exception))

    def test_comments_and_blank_lines_are_skipped(self):
        self.assertEqual(len(co.parse("# header\n\n" + make_record() + "\n")), 1)

    def test_real_fixture_parses(self):
        self.assertEqual(len(co.parse(RECORDS.read_text())), 48)


class BranchPredicateTests(unittest.TestCase):
    def test_nearpole_via_small_wdiffr(self):
        b, _, _ = co.classify(F(123, 10), F(12), F(1, 4), F(250000))
        self.assertEqual(b, 2)

    def test_generic_when_both_conditions_hold(self):
        b, _, _ = co.classify(F(20), F(12), F(1, 4), F(250000))
        self.assertEqual(b, 1)

    def test_nearpole_via_limitone_with_large_wdiffr(self):
        """`limitone` matters: wdiffr > limittwo yet the branch is near-pole."""
        b, wdiffr, delwr = co.classify(F(1001), F(1000), F(1, 4), F(250000))
        self.assertGreater(wdiffr, F(1, 4))
        self.assertGreaterEqual(delwr, F(250000))
        self.assertEqual(b, 2)

    def test_zero_mode_far_from_the_pole_is_still_generic(self):
        """A zero mode does NOT automatically fall to branch 3."""
        b, _, _ = co.classify(F(5), F(0), F(1, 4), F(250000))
        self.assertEqual(b, 1)

    def test_zero_mode_near_the_pole_falls_to_branch_three(self):
        b, wdiffr, delwr = co.classify(F(1, 10), F(0), F(1, 4), F(250000))
        self.assertLessEqual(wdiffr, F(1, 4))
        self.assertEqual(delwr, 0)
        self.assertEqual(b, 3)

    def test_exact_pole_has_no_delw(self):
        b, _, delwr = co.classify(F(12), F(12), F(1, 4), F(250000))
        self.assertIsNone(b)
        self.assertIsNone(delwr)

    def test_exact_and_recorded_routes_agree_on_the_fixture(self):
        _, out = run_main([str(RECORDS), "--counts", str(PROBE),
                           "--control-counts", str(CONTROL)])
        self.assertTrue(out["exact_and_recorded_branch_agree"])


class AnalyseTests(unittest.TestCase):
    def analyse_one(self, **over):
        return co.analyse(co.parse(make_record(**over) + "\n")[0])

    def test_synthetic_record_is_accepted(self):
        out = self.analyse_one()
        self.assertEqual(out["branch_recomputed"], 2)
        self.assertTrue(out["mismatch_closed_equals_direct"])

    def test_occ_one_is_rejected(self):
        with self.assertRaises(co.RecordError):
            self.analyse_one(occ=1.0)

    def test_occ_outside_half_and_one_is_rejected(self):
        """Smearing is excluded from GPP, so occ can only be 0.5 or 1.0."""
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(occ=0.75)
        self.assertIn("smearing is excluded", str(cm.exception))

    def test_complex_mode_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(wtilde_im=1.0)
        self.assertIn("imaginary", str(cm.exception))

    def test_nonpositive_mode_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(wtilde_re=-12.0)
        self.assertIn("positive real mode", str(cm.exception))

    def test_wrong_threshold_constants_are_rejected(self):
        with self.assertRaises(co.RecordError):
            self.analyse_one(limittwo=0.3)
        with self.assertRaises(co.RecordError):
            self.analyse_one(limitone=1.0)

    def test_fermi_gap_inconsistent_with_half_occupation_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(efermi=5.0)
        self.assertIn("sig%tol", str(cm.exception))

    def test_wxt_inconsistent_with_its_energies_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(e_lk=500.0)
        self.assertIn("wxt", str(cm.exception))

    def test_clamp_must_not_fire_when_predicate_is_false(self):
        rec = co.parse(make_record() + "\n")[0]
        with self.assertRaises(co.RecordError) as cm:
            self.analyse_one(ssx_post=rec["ssx_post"] * 2.0)
        self.assertIn("clamp", str(cm.exception))

    def test_generic_branch_record_is_rejected(self):
        with self.assertRaises(co.RecordError):
            self.analyse_one(wxt=20.0, branch=1)

    def test_exported_branch_label_must_agree(self):
        with self.assertRaises(co.RecordError):
            self.analyse_one(branch=1)

    def test_mismatch_scales_with_one_minus_occ(self):
        m_half = self.analyse_one()["mismatch_exact"]
        rec = co.parse(RECORD_LINES[0] + "\n")[0]
        self.assertNotEqual(m_half, 0.0)
        # (1-occ) factor: at occ = 0.5 the prefactor is 0.5
        ieps, wt, x = F(rec["ieps"]), F(rec["wtilde_re"]), F(rec["wxt"])
        om2 = wt ** 2 * ieps
        full = om2 / (2 * wt * (x + wt)) + om2 / ((x - wt) * (x + wt))
        out = co.analyse(co.parse(RECORD_LINES[0] + "\n")[0])
        self.assertAlmostEqual(out["mismatch_exact"] / float(full), 0.5, places=12)


class TallyTests(unittest.TestCase):
    GOOD = ("branch1 10 1\nbranch2 20 2\nbranch3 30 3\nsexcut 5 0\n")

    def test_good_tally_parses(self):
        self.assertEqual(co.check_counts(self.GOOD)["branch2"], (20, 2))

    def test_malformed_line_is_rejected(self):
        with self.assertRaises(co.RecordError):
            co.check_counts("branch1 1\n")

    def test_missing_row_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            co.check_counts("branch1 1 2\nbranch2 3 4\nbranch3 5 6\n")
        self.assertIn("missing rows", str(cm.exception))

    def test_unknown_row_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            co.check_counts(self.GOOD + "branch9 1 1\n")
        self.assertIn("unknown row", str(cm.exception))

    def test_duplicate_row_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            co.check_counts(self.GOOD + "branch2 1 1\n")
        self.assertIn("duplicate row", str(cm.exception))

    def test_non_integer_count_is_rejected(self):
        with self.assertRaises(co.RecordError):
            co.check_counts("branch1 1.5 2\nbranch2 3 4\nbranch3 5 6\nsexcut 0 0\n")

    def test_negative_count_is_rejected(self):
        with self.assertRaises(co.RecordError):
            co.check_counts(self.GOOD.replace("branch2 20 2", "branch2 20 -1"))

    def test_sexcut_exceeding_total_is_rejected(self):
        with self.assertRaises(co.RecordError) as cm:
            co.check_counts(self.GOOD.replace("sexcut 5 0", "sexcut 999 0"))
        self.assertIn("exceeds the total", str(cm.exception))

    def test_all_zero_tally_is_rejected(self):
        with self.assertRaises(co.RecordError):
            co.check_counts("branch1 0 0\nbranch2 0 0\nbranch3 0 0\nsexcut 0 0\n")

    def test_control_with_partial_occupation_is_rejected(self):
        probe = co.check_counts(PROBE.read_text())
        with self.assertRaises(co.RecordError) as cm:
            co.check_tally_pair(probe, probe)
        self.assertIn("required to be occ == 1", str(cm.exception))

    def test_probe_without_partial_occupation_is_rejected(self):
        control = co.check_counts(CONTROL.read_text())
        with self.assertRaises(co.RecordError) as cm:
            co.check_tally_pair(control, control)
        self.assertIn("no occ != 1 near-pole events", str(cm.exception))

    def test_row_sum_invariant_catches_a_tampered_positive_count(self):
        """A count altered to another nonnegative value still breaks the sum."""
        probe = dict(co.check_counts(PROBE.read_text()))
        probe["branch2"] = (76461, 3701)
        control = co.check_counts(CONTROL.read_text())
        with self.assertRaises(co.RecordError) as cm:
            co.check_tally_pair(probe, control)
        self.assertIn("column sum", str(cm.exception))

    def test_real_pair_satisfies_the_invariants(self):
        out = co.check_tally_pair(co.check_counts(PROBE.read_text()),
                                  co.check_counts(CONTROL.read_text()))
        self.assertEqual(out["qualifying_events"], 3702)
        self.assertEqual(out["total_evaluations"], 12020388)


class SourceAlgebraTests(unittest.TestCase):
    """Regression for the two T-003-R1 report errors (CODEX-T-003-R1-REVIEW.md).

    These pin **source algebra**, evaluated over exact rationals. They are not
    executed material witnesses and involve no BerkeleyGW run.

    Both counterexamples are read from the supervisor's review evidence so the
    tests cannot drift from it.
    """

    CE_LIMIT = (ROOT / "artifacts" / "t003-r1-codex-review"
                / "sentinel-counterexample.json")
    CE_BRANCH = (ROOT / "artifacts" / "t003-r1-codex-review"
                 / "sentinel-branch-counterexample.json")

    @staticmethod
    def kernel(w, x, ieps, occ):
        """Generic-branch ssx, sch/2 and the mapped local combination.

        Mirrors Sigma/mtxel_cor.f90:1810-1812 and 1828-1834: Omega2 is
        RECOMPUTED as wtilde2*ieps, which is what makes ssx tend to -ieps
        rather than to zero.
        """
        w2 = w * w
        omega2 = w2 * ieps
        ssx = omega2 / (x * x - w2)
        half_sch = (w / (x - w)) * ieps / 2
        return ssx, half_sch, -occ * ssx + half_sch

    def test_error_one_ssx_does_not_tend_to_zero(self):
        ce = json.loads(self.CE_LIMIT.read_text())
        w, x = F(ce["w"]), F(ce["x"])
        ieps, occ = F(ce["ieps"]), F(ce["occ"])
        ssx, half_sch, local = self.kernel(w, x, ieps, occ)
        # the pre-correction report claimed ssx -> 0; it tends to -ieps
        self.assertAlmostEqual(float(ssx), ce["ssx_float"], places=12)
        self.assertAlmostEqual(float(ssx), float(-ieps), places=9)
        self.assertGreater(abs(float(ssx)), 0.1)
        self.assertAlmostEqual(float(half_sch), ce["half_sch_float"], places=12)
        self.assertAlmostEqual(
            float(local), ce["local_minus_occ_ssx_plus_half_sch_float"],
            places=12)

    def test_error_one_local_limit_is_occ_minus_half_times_ieps(self):
        ce = json.loads(self.CE_LIMIT.read_text())
        ieps = F(ce["ieps"])
        for occ in (F(1), F(1, 2), F(0)):
            with self.subTest(occ=float(occ)):
                _, _, local = self.kernel(F(10) ** 12, F(10), ieps, occ)
                self.assertAlmostEqual(float(local),
                                       float((occ - F(1, 2)) * ieps), places=9)

    def test_error_one_sexcut_clamp_does_not_suppress_the_limit(self):
        ce = json.loads(self.CE_LIMIT.read_text())
        w, x, ieps = F(ce["w"]), F(ce["x"]), F(ce["ieps"])
        ssx, _, _ = self.kernel(w, x, ieps, F(ce["occ"]))
        # clamp fires only if |ssx| > sexcut*|ieps| AND wxt < 0
        self.assertFalse(abs(ssx) > co.SIG_SEXCUT * abs(ieps))
        self.assertFalse(x < 0)

    def test_finite_sentinel_is_not_its_limit_and_depends_on_x(self):
        """The finite w=1e12 value approaches (occ-1/2)*ieps without attaining it.

        Exact rationals throughout. This is the claim REPORT.md section 2.1
        makes, and it is the one an earlier revision got wrong by presenting
        the finite value as equal to the limit.
        """
        w, ieps, occ = F(10) ** 12, F(-1, 4), F(1)
        limit = (occ - F(1, 2)) * ieps
        vals = {}
        for x in (F(1), F(10), F(100), F(1000)):
            _, _, local = self.kernel(w, x, ieps, occ)
            vals[x] = local
            # finite, close to the limit, but never equal to it
            self.assertNotEqual(local, limit)
            self.assertLess(abs(local - limit), F(1, 10**9))
        # the exact fractions quoted in REPORT.md
        self.assertEqual(vals[F(10)], F(-12500000000, 100000000001))
        self.assertEqual(vals[F(100)], F(-1250000000, 10000000001))
        # genuinely x-dependent, by about 1.1e-11 between x=10 and x=100
        self.assertNotEqual(vals[F(10)], vals[F(100)])
        self.assertAlmostEqual(float(vals[F(10)] - vals[F(100)]),
                               -1.12499999987625e-11, places=20)
        # monotone approach as x shrinks relative to w
        self.assertLess(abs(vals[F(1)] - limit), abs(vals[F(1000)] - limit))

    def test_sentinel_clamp_predicate_needs_both_conjuncts(self):
        """REPORT.md section 2.1: |ssx| > sexcut*|ieps| AND wxt < 0."""
        w, x, ieps = F(10) ** 12, F(10), F(-1, 4)
        ssx, _, _ = self.kernel(w, x, ieps, F(1))
        self.assertFalse(abs(ssx) > co.SIG_SEXCUT * abs(ieps))
        self.assertFalse(x < 0)

    def test_error_two_nearpole_without_the_half_eV_window(self):
        ce = json.loads(self.CE_BRANCH.read_text())
        w, x = F(ce["w"]), F(ce["x"])
        b, wdiffr, delwr = co.classify(x, w, F(1, 4), F(250000))
        self.assertEqual(b, 2)
        self.assertEqual(wdiffr, F(ce["wdiffr"]))
        self.assertEqual(delwr, F(ce["delwr"]))
        # the first generic test PASSES; the delwr test is what fails
        self.assertGreater(wdiffr, F(1, 4))
        self.assertGreaterEqual(delwr, F(250000))
        # and the distance is nine orders of magnitude beyond 0.5 eV
        self.assertGreater(abs(x - w), 1e6 - 1)

    def test_closed_form_predicate_matches_classify(self):
        """near-pole <=> d <= max(gamma, |w|/500) and delwr > TOL_Zero."""
        gamma, limittwo, limitone = F(1, 2), F(1, 4), F(250000)
        self.assertEqual(F(500) ** 2, limitone)
        bad = 0
        checked = 0
        for w_exp in range(-3, 14):
            w = F(10) ** w_exp
            window = max(gamma, abs(w) / 500)
            for mult in (F(1, 100), F(1, 2), F(9, 10), F(99, 100), F(1),
                         F(101, 100), F(11, 10), F(2), F(100)):
                d = window * mult
                for sign in (1, -1):
                    x = w + sign * d
                    b, _, delwr = co.classify(x, w, limittwo, limitone)
                    want = 2 if (d <= window and delwr is not None
                                 and delwr > co.TOL_ZERO) else 1
                    bad += (b != want)
                    checked += 1
        self.assertEqual(checked, 306)
        self.assertEqual(bad, 0)

    def test_crossover_between_the_two_routes(self):
        gamma, limittwo, limitone = F(1, 2), F(1, 4), F(250000)
        self.assertEqual(gamma * 500, F(250))       # crossover, in eV
        # below the crossover the gamma route sets the window
        b, _, _ = co.classify(F(100) + F(6, 10), F(100), limittwo, limitone)
        self.assertEqual(b, 1)                      # d = 0.6 > gamma
        # above it, the delwr route widens the window well past gamma
        b, _, _ = co.classify(F(1000) + F(1), F(1000), limittwo, limitone)
        self.assertEqual(b, 2)                      # d = 1.0 <= 1000/500 = 2

    def test_all_archived_records_used_the_wdiffr_route(self):
        rows = co.parse(RECORDS.read_text())
        for r in rows:
            with self.subTest(rec=r["rec"]):
                self.assertLess(r["wtilde_re"], 250.0)
                self.assertLessEqual(abs(r["wxt"] - r["wtilde_re"]), 0.5)


class SmearingRangeTests(unittest.TestCase):
    """The MP1 occupation is not confined to [0, 1].

    `occ(y) = 0.5*(1-erf(y)) - y/(2*sqrt(pi))*exp(-y^2)` at
    `Sigma/mtxel_cor.f90:1410` and `Common/input_utils.f90:381`.
    `d occ/dy = exp(-y^2)/sqrt(pi) * (y^2 - 3/2)`, so the extrema sit at
    `y = -+sqrt(3/2)`.

    These are the MATHEMATICAL extrema. The values below are the binary64
    evaluation of that formula at those points, which is what `math` returns;
    they are not a claim that the floating-point function attains the exact
    real extremum.
    """

    @staticmethod
    def occ(y):
        return 0.5 * (1 - math.erf(y)) - y / (2 * math.sqrt(math.pi)) * math.exp(-y * y)

    def test_exceeds_one(self):
        top = self.occ(-math.sqrt(1.5))
        self.assertGreater(top, 1.0)
        self.assertAlmostEqual(top, 1.0354579065701095, places=12)

    def test_goes_negative(self):
        bot = self.occ(math.sqrt(1.5))
        self.assertLess(bot, 0.0)
        self.assertAlmostEqual(bot, -0.03545790657010946, places=12)

    def test_extrema_are_stationary(self):
        for y in (-math.sqrt(1.5), math.sqrt(1.5)):
            h = 1e-6
            d = (self.occ(y + h) - self.occ(y - h)) / (2 * h)
            self.assertLess(abs(d), 1e-9)

    def test_limits(self):
        self.assertAlmostEqual(self.occ(-40.0), 1.0, places=15)
        self.assertAlmostEqual(self.occ(40.0), 0.0, places=15)

    def test_range_is_unreachable_in_the_gpp_path(self):
        """Documented as excluded, so no GPP record may carry such an occ."""
        with self.assertRaises(co.RecordError):
            co.analyse(co.parse(make_record(occ=1.0354579065701095) + "\n")[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)

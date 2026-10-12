#!/usr/bin/env python3
"""T-005: the source-level GPP branch-boundary and occupation sweep.

These tests check the saved evidence in `artifacts/t005/` and, when the pinned
compiler is available, that recompiling and rerunning the driver reproduces it
byte for byte. They are numerical and structural on purpose: there is no prose
or status surface here to regress.

Everything asserted below is about a standalone real-flavor driver that
re-executes the transcribed statements of `sigma_gpp_cpu`. None of it is
evidence about a BerkeleyGW production run or a material self-energy.
"""

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "branch_boundary"))
import analyze  # noqa: E402
import run_sweep  # noqa: E402

RAW = ROOT / "artifacts" / "t005" / "raw_sweep.txt"
SUMMARY = ROOT / "artifacts" / "t005" / "summary.json"
DRIVER = ROOT / "bgw" / "branch_boundary" / "branch_boundary.f90"

#: Boundary cases with `wxt > 0` on every row, where the `ssxcutoff` clamp of
#: `mtxel_cor.f90:1848` cannot fire.
UNCLAMPED_CASES = ("A+", "A-", "B+")
#: Boundary cases at `wxt < 0` where the clamp is observed to fire.
CLAMPED_CASES = ("C-",)
#: Every boundary case in the saved sweep.
CASES = UNCLAMPED_CASES + CLAMPED_CASES

#: One ULP of the binary64 significand.
EPS = 2.220446049250313e-16


def compiler_available():
    command = run_sweep.compile_command("/dev/null")
    return pathlib.Path(command[0]).exists()


class ProvenanceTests(unittest.TestCase):
    """The driver must say which immutable source it copied, and be right."""

    def test_driver_cites_the_accepted_mtxel_cor_digest(self):
        """The digest must come from accepted, committed T-002 material.

        `artifacts/` is gitignored, so a run artifact is not a usable reference
        for a fresh checkout; `GW/GPP/BerkeleyGWMap.lean` and
        `bgw/kernel_transcript.f90` are.
        """
        import json
        digest, lines = run_sweep.accepted_digest()
        self.assertEqual(lines, 3968)
        text = DRIVER.read_text()
        self.assertIn(digest, text)
        # The exact copied regions, not a vague "the GPP kernel".
        for lines in ("mtxel_cor.f90:1810-1848", "mtxel_cor.f90:1698-1699",
                      "mtxel_cor.f90:1746", "mtxel_cor.f90:772-795",
                      "inread.f90:151-152", "nrtype.f90:155,161-162"):
            self.assertIn(lines, text)
        self.assertEqual(
            json.loads(SUMMARY.read_text())["provenance"][
                "mtxel_cor_sha256_accepted"], digest)

    def test_driver_reproduces_the_real_flavor_MYCONJG_expansion(self):
        """`MYCONJG` is `(x)` in the real flavor, not `conjg(x)`.

        The near-pole branch therefore squares `cden`. Spelling it `CONJG`
        would be a silent change of operation, so the driver must not.
        """
        body = DRIVER.read_text()
        near_pole = body.split("cden = (4.0d0 * wtilde2 * (delw + 0.5D0 ))")
        self.assertGreaterEqual(len(near_pole), 3, "near-pole block missing")
        for block in near_pole[1:]:
            head = block[:block.index("ssx_pre") if "ssx_pre" in block else 200]
            self.assertIn("rden = cden*(cden)", head)
            self.assertNotIn("CONJG", head)

    def test_run_is_pinned_to_the_arch_mk_compiler(self):
        arch = run_sweep.arch_settings(relocate=False)
        command = run_sweep.compile_command("/tmp/unused", arch)
        self.assertIn(command[0], arch["F90free"])
        self.assertTrue(command[0].startswith("/tmp/mm/root/envs/bgw/bin/"))
        # BGW_TOOLCHAIN may move the prefix; it must not change anything else.
        moved = run_sweep.compile_command("/tmp/unused")
        self.assertEqual([c.replace(os.environ.get("BGW_TOOLCHAIN", run_sweep.ARCHIVED_PREFIX),
                                    run_sweep.ARCHIVED_PREFIX) for c in moved], command)
        import json
        recorded = json.loads(SUMMARY.read_text())["provenance"]
        self.assertEqual(recorded["compiler"], command[0])
        self.assertEqual(recorded["driver_sha256"], run_sweep.sha256(DRIVER))


class BoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parsed = analyze.parse(RAW)
        cls.summary = analyze.summarize(cls.parsed)

    def test_located_surfaces_are_ulp_tight(self):
        """The reported surface is between adjacent binary64 numbers."""
        for case in CASES:
            with self.subTest(case=case):
                b = self.summary["boundaries"][case]
                self.assertTrue(b["adjacent_representable"])
                self.assertEqual(
                    abs(analyze.bits(b["wxt_true"]) - analyze.bits(b["wxt_false"])), 1)
                self.assertEqual(b["branch_false"], 2)
                self.assertEqual(b["branch_true"], 1)

    def test_both_conjuncts_have_their_own_surface(self):
        """`wdiffr > gamma^2` decides at wt = 1; `delwr < limitone` at wt = 300.

        With the defaults the `delwr` conjunct is redundant whenever
        |wtilde| <= gamma/(2*sqrt(TOL_Small)) = 250, because it fails only for
        |wdiff| <= 2*sqrt(TOL_Small)*|wtilde|. The wt = 300 case is chosen
        purely to separate the two surfaces; it is not a claim about physical
        mode energies.
        """
        self.assertEqual(self.summary["boundaries"]["A+"]["deciding_conjunct"],
                         ["wdiffr"])
        self.assertEqual(self.summary["boundaries"]["A-"]["deciding_conjunct"],
                         ["wdiffr"])
        self.assertEqual(self.summary["boundaries"]["C-"]["deciding_conjunct"],
                         ["wdiffr"])
        # `C-` is the same |d| = gamma surface, reached from wxt < 0.
        self.assertLess(self.summary["boundaries"]["C-"]["wxt_false"], 0.0)
        self.assertAlmostEqual(self.summary["boundaries"]["C-"]["d_false"], -0.5,
                               places=15)
        b = self.summary["boundaries"]["B+"]
        self.assertEqual(b["deciding_conjunct"], ["delwr"])
        self.assertGreater(b["wdiffr_false"], self.parsed["meta"]["limittwo"])
        self.assertAlmostEqual(abs(b["d_false"]), 2e-3 * b["wt"], places=9)

    def test_exact_boundary_is_not_the_decimal_one_on_the_low_side(self):
        """`wxt - wtilde` is exact above the mode and inexact below it.

        On the `A+` side the surface sits exactly at wxt = 1.5, i.e. d = 0.5.
        On the `A-` side wxt = 0.5 is outside the Sterbenz range, the
        subtraction rounds, and the last predicate-false point is one ULP below
        0.5 while still reporting d = -0.5 exactly. The machine surface is
        therefore NOT at the decimal value wxt = 0.5.
        """
        plus = self.summary["boundaries"]["A+"]
        self.assertEqual(plus["wxt_false"], 1.5)
        self.assertEqual(plus["d_false"], 0.5)
        minus = self.summary["boundaries"]["A-"]
        self.assertLess(minus["wxt_false"], 0.5)
        self.assertEqual(minus["d_false"], -0.5)
        self.assertEqual(analyze.bits(0.5) - analyze.bits(minus["wxt_false"]), 1)

    def test_branch_flips_exactly_at_the_reported_neighbours(self):
        """Branch 1 on every predicate-true row, branch 2 on every false row."""
        for case in CASES:
            for occ in (1.0, 0.5):
                for row in analyze.sweep(self.parsed, case, occ):
                    with self.subTest(case=case, occ=occ, label=row["label"]):
                        selected = bool(row["c1"]) and bool(row["c2"])
                        self.assertEqual(row["branch"], 1 if selected else 2)

    def test_no_surviving_positive_real_mode_reaches_the_third_branch(self):
        """The preprocessing argument, stated in the source's own quantities.

        Line 774 keeps a mode only if `|wtilde2| >= TOL_Small`; if `wtilde2`
        is also positive then line 793 sets `wtilde = sqrt(wtilde2)`, so
        `wtilde >= sqrt(TOL_Small) = 1e-3`. Branch 3 needs both
        `wdiffr <= limittwo` (`|wdiff| <= gamma`) and `delwr <= TOL_Zero`
        (`wtilde <= sqrt(TOL_Zero)*|wdiff| <= 5e-7`). Those bounds are a factor
        2000 apart, so no such mode can reach it. The `minmode` row is the
        extremal witness: the smallest surviving positive-real mode, at the
        `wxt` that maximises `|wdiff|` while keeping the first conjunct false,
        still lands in branch 2.
        """
        b = self.summary["branch3"]
        meta = self.parsed["meta"]
        self.assertEqual(b["positive_mode_bound"]["min_surviving_wtilde"],
                         meta["TOL_Small"] ** 0.5)
        self.assertEqual(b["positive_mode_bound"]["max_wtilde_for_branch3"],
                         meta["TOL_Zero"] ** 0.5 * meta["sig_gamma"])
        self.assertGreater(b["positive_mode_bound"]["ratio"], 1000.0)
        minmode = next(r for r in b["rows"] if r["label"] == "minmode")
        self.assertEqual(minmode["wtilde2_in"], meta["TOL_Small"])
        self.assertEqual(minmode["cycled"], 0)
        self.assertAlmostEqual(minmode["wtilde_re"], 1e-3, places=15)
        self.assertLessEqual(minmode["wdiffr"], meta["limittwo"])
        self.assertGreater(minmode["delwr"], meta["TOL_Zero"])
        self.assertEqual(minmode["branch"], 2)
        # and no swept row of any boundary case selects it either
        for case in CASES:
            for occ in (1.0, 0.5):
                for row in analyze.sweep(self.parsed, case, occ):
                    self.assertNotEqual(row["branch"], 3)

    def test_the_invalid_mode_policy_zero_route_into_the_third_branch(self):
        """Branch 3 IS reachable, by the `invalid_gpp_mode = 0` path.

        Line 774 filters on `abs(wtilde2)`, so a sufficiently negative
        `wtilde2` survives it; lines 779-782 then assign `wtilde = (0,0)`.
        This test exists so that route cannot silently drop out of the claim
        again: for this supplied negative `wtilde2`, branch 3 must be reached
        by a zero mode under policy 0. The contribution is zero, which is what
        "skip invalid GPP mode" means -- not evidence that policy 0 is the only
        source route by which a zero-initialized array entry can reach the loop.
        """
        b = self.summary["branch3"]
        self.assertEqual(b["branch3_policies"], [0])
        self.assertTrue(b["branch3_requires_zero_mode"])
        self.assertTrue(b["invalid_mode_route"]["policy_zero_gives_zero_mode"])
        self.assertTrue(b["invalid_mode_route"]["other_policies_are_nonzero_modes"])
        self.assertEqual(b["zero_mode_contribution"], [0.0])

        p0 = next(r for r in b["rows"] if r["label"] == "policy0")
        self.assertLess(p0["wtilde2_in"], 0.0)
        self.assertGreaterEqual(abs(p0["wtilde2_in"]), self.parsed["meta"]["TOL_Small"])
        self.assertEqual(p0["cycled"], 0, "negative wtilde2 must survive line 774")
        self.assertEqual((p0["wtilde_re"], p0["wtilde_im"]), (0.0, 0.0))
        self.assertEqual(p0["branch"], 3)

        # Every other policy at this same wtilde2 produces a nonzero mode and a
        # different branch, so this particular route is policy-0 specific.
        for label, policy in (("policy1", 1), ("policy2", 2), ("policy3", 3),
                              ("policy9", 9)):
            with self.subTest(label=label):
                row = next(r for r in b["rows"] if r["label"] == label)
                self.assertEqual(row["policy"], policy)
                self.assertNotEqual(row["branch"], 3)
        # policy 1 really is the purely imaginary mode of line 784.
        p1 = next(r for r in b["rows"] if r["label"] == "policy1")
        self.assertEqual(p1["wtilde_re"], 0.0)
        self.assertGreater(p1["wtilde_im"], 0.0)

    def test_modes_below_tol_small_are_cycled_before_the_loop(self):
        """Line 774 is the filter, and it is two-sided in absolute value."""
        rows = {r["label"]: r for r in self.summary["branch3"]["rows"]}
        for label in ("cycled", "cycledneg"):
            with self.subTest(label=label):
                row = rows[label]
                self.assertLess(abs(row["wtilde2_in"]), self.parsed["meta"]["TOL_Small"])
                self.assertEqual(row["cycled"], 1)
                self.assertEqual(row["branch"], -1)


class FullOccupationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parsed = analyze.parse(RAW)
        cls.summary = analyze.summarize(cls.parsed)

    def test_crossing_is_continuous_at_the_observed_floating_scale(self):
        """At occ = 1 the branch change costs no more than ordinary adjacent-
        point variation inside a single branch.

        The bound is the measured within-branch step, not a tuned constant, and
        it is a floating-point observation about this driver -- not a proof and
        not a statement about production accuracy.
        """
        for case in UNCLAMPED_CASES:
            with self.subTest(case=case):
                c = self.summary["crossings"][case]["occ_1.0"]
                self.assertFalse(c["clamp_active"])
                self.assertLessEqual(c["jump"], c["within_branch_max"])
                self.assertLess(c["jump_over_scale"], 1e-11)

    def test_the_cancellation_conditioning_is_reported_not_hidden(self):
        """The `A` cases cancel to ~1e-16 relative; the `B` case only to ~1e-11.

        `-ssx + 0.5*sch` subtracts two O(250) numbers to make O(0.25) there, so
        the honest continuity scale differs by five orders of magnitude between
        the cases. Recording that is the point.
        """
        a = self.summary["crossings"]["A+"]["occ_1.0"]
        b = self.summary["crossings"]["B+"]["occ_1.0"]
        self.assertLess(a["jump_over_scale"], 1e-15)
        self.assertGreater(b["jump_over_scale"], 1e-13)
        self.assertLess(b["jump_over_scale"], 1e-11)


class ClampTests(unittest.TestCase):
    """The `ssxcutoff` clamp of `mtxel_cor.f90:1847-1848`, actually exercised.

    T-005 transcribed the clamp but every swept row had `wxt >= 0`, so it
    never fired and no observation of it was made. The `C-` case fixes that.
    """

    @classmethod
    def setUpClass(cls):
        cls.parsed = analyze.parse(RAW)
        cls.summary = analyze.summarize(cls.parsed)

    def test_the_unclamped_cases_really_never_touch_the_clamp(self):
        """Separating the two regimes only means something if it is true."""
        for case in UNCLAMPED_CASES:
            with self.subTest(case=case):
                entry = self.summary["clamp"][case]
                self.assertGreater(entry["min_wxt"], 0.0)
                self.assertEqual(entry["rows_clamped_selected"], 0)
                self.assertEqual(entry["rows_clamped_generic"], 0)
                self.assertEqual(entry["rows_clamped_near_pole"], 0)

    def test_the_clamp_is_genuinely_active_on_the_new_boundary_rows(self):
        """`ssx_pre != ssx` on every ULP row of `C-`, for a source-valid mode.

        The mode is a positive real `wtilde = 0.26`, i.e. `wtilde2 = 0.0676`,
        well above `TOL_Small`, so line 774 does not cycle it. The clamp fires
        because `wxt < 0` and `|ssx| > sig%sexcut*|I_eps| = 4`.
        """
        for case in CLAMPED_CASES:
            entry = self.summary["clamp"][case]
            self.assertEqual(len(entry["detail"]), 12,  # 6 ULP rows x 2 occ
                             "expected the clamp on every ULP row at both occ")
            for row in entry["detail"]:
                with self.subTest(case=case, label=row["label"], occ=row["occ"]):
                    self.assertLess(row["wxt"], 0.0)
                    self.assertGreater(abs(row["ssx_pre"]), row["ssxcutoff"])
                    self.assertNotEqual(row["ssx_pre"], row["ssx_post"])
                    self.assertEqual(row["ssx_post"], 0.0)
                    # both counterfactual candidates are clamped here too
                    self.assertGreater(abs(row["gen_ssx_pre"]), row["ssxcutoff"])
                    self.assertGreater(abs(row["np_ssx_pre"]), row["ssxcutoff"])
                    self.assertEqual((row["gen_ssx_post"], row["np_ssx_post"]),
                                     (0.0, 0.0))
        # A source-valid mode: it survives the line-774 filter.
        wt = self.summary["boundaries"]["C-"]["wt"]
        self.assertGreater(wt ** 2, self.parsed["meta"]["TOL_Small"])

    def test_the_clamp_breaks_full_occupation_continuity(self):
        """Observed, not tuned: at `occ = 1` the clamp makes the crossing jump.

        The unclamped algebra is continuous across this surface -- the
        pre-clamp values agree to ~1e-14 on a scale of 6.5. After the clamp,
        SX is zeroed on both sides while the generic branch keeps its nonzero
        `sch`, so the local value steps by `0.5*sch` between two adjacent
        representable `wxt`. That is a finite discontinuity at full
        occupation. It is preserved here rather than tuned away, and it is a
        statement about this driver's local accumulator, not a material
        self-energy error.
        """
        c = self.summary["crossings"]["C-"]["occ_1.0"]
        self.assertTrue(c["clamp_active"])
        # pre-clamp: continuous at the local floating scale
        self.assertLess(abs(c["signed_jump_pre_clamp"]),
                        1e-13 * c["value_scale_pre_clamp"])
        # post-clamp: a finite jump, of the order of the value itself
        self.assertGreater(c["jump"], 0.25)
        self.assertEqual(c["jump_over_scale"], 1.0)
        # ... and it is exactly the surviving 0.5*sch of the generic branch
        seq = {r["label"]: r for r in analyze.ulp_rows(self.parsed, "C-", 1.0)}
        self.assertEqual(seq["ulpF-0"]["value"], 0.0)
        self.assertEqual(seq["ulpT+0"]["value"], 0.5 * seq["ulpT+0"]["sch"])
        self.assertEqual(c["signed_jump"],
                         seq["ulpT+0"]["value"] - seq["ulpF-0"]["value"])

    def test_the_post_clamp_jump_does_not_depend_on_occupation(self):
        """And therefore is not what `branch_mismatch` describes.

        With `ssx` clamped to zero on both sides the occupation factor
        multiplies nothing, so the jump is the same at `occ = 1` and
        `occ = 0.5`, while the closed form is proportional to `1 - occ`. The
        analyzer marks these crossings `closed_form_applies = False`; the
        comparison is made only against the pre-clamp values.
        """
        one = self.summary["crossings"]["C-"]["occ_1.0"]
        half = self.summary["crossings"]["C-"]["occ_0.5"]
        self.assertEqual(one["signed_jump"], half["signed_jump"])
        self.assertFalse(one["closed_form_applies"])
        self.assertFalse(half["closed_form_applies"])
        self.assertIsNone(one["signed_jump_minus_predicted"])
        self.assertIsNone(half["signed_jump_minus_predicted"])
        # The closed form does describe the unclamped algebra at the same
        # inputs, and at occ = 0.5 it is half the size of the observed jump.
        self.assertLessEqual(abs(half["signed_jump_pre_clamp_minus_predicted"]),
                             1e-12 * abs(half["predicted_mismatch"]))
        self.assertNotAlmostEqual(half["signed_jump"], half["predicted_mismatch"],
                                  places=3)

    def test_the_clamp_switches_off_away_from_the_surface(self):
        """The clamp is a property of the inputs, not of the case label.

        At `|wxt| = 0.14` and `0.34` the same mode gives `|ssx| < 4` and the
        clamp does not fire, so those rows are ordinary unclamped algebra.
        """
        rows = {r["label"]: r for r in analyze.sweep(self.parsed, "C-", 1.0)}
        for label in ("far-1.0E-01", "far+1.0E-01"):
            with self.subTest(label=label):
                row = rows[label]
                self.assertLess(row["wxt"], 0.0)
                self.assertEqual(row["cut_sel"], 0)
                self.assertLess(abs(row["ssx_pre"]), row["ssxcutoff"])
                self.assertEqual(row["ssx"], row["ssx_pre"])


class PartialOccupationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.parsed = analyze.parse(RAW)
        cls.summary = analyze.summarize(cls.parsed)

    def test_half_occupation_crossing_matches_the_predicted_mismatch(self):
        """At occ = 0.5 the same one-ULP step moves the local value by the
        amount `GW.GPP.BGW4.branch_mismatch` predicts, with its sign.

        Only for the unclamped cases: the closed form is a statement about the
        branch algebra, and `mtxel_cor.f90:1848` is not part of that algebra.
        """
        for case in UNCLAMPED_CASES:
            with self.subTest(case=case):
                c = self.summary["crossings"][case]["occ_0.5"]
                self.assertTrue(c["closed_form_applies"])
                predicted = c["predicted_mismatch"]
                self.assertGreater(abs(predicted), 0.4)
                self.assertEqual(c["signed_jump"] > 0, predicted > 0)
                self.assertLessEqual(
                    abs(c["signed_jump_minus_predicted"]),
                    1e-11 * abs(predicted) + 1e-15)

    def test_the_sign_flips_with_the_side_of_the_mode(self):
        """Above the mode the discrepancy is positive, below it negative: the
        `1/((x-wt)(x+wt))` term changes sign while `1/(2*wt*(x+wt))` does not.
        """
        self.assertGreater(self.summary["crossings"]["A+"]["occ_0.5"]["signed_jump"], 0)
        self.assertLess(self.summary["crossings"]["A-"]["occ_0.5"]["signed_jump"], 0)

    def test_half_occupation_jump_dwarfs_within_branch_variation(self):
        for case in UNCLAMPED_CASES:
            with self.subTest(case=case):
                c = self.summary["crossings"][case]["occ_0.5"]
                self.assertGreater(c["jump_over_within_branch"], 1e10)
                self.assertGreater(c["jump_over_scale"], 0.5)

    def test_discrepancy_is_linear_in_one_minus_occupation(self):
        """`Delta(occ)/(1-occ)` is constant to a few ULP, and `Delta(1)` is at
        the rounding floor rather than exactly zero."""
        for point, r in self.summary["occupation_linearity"].items():
            with self.subTest(point=point):
                self.assertEqual(sorted(r["ratios"]), ["0.25", "0.5", "0.75"])
                # 8 ULP of the ratio: the three evaluations differ only by the
                # rounding of (1-occ) and of two sums of three terms.
                self.assertLess(r["max_relative_spread"], 8 * 2.220446049250313e-16)
                self.assertLessEqual(abs(r["delta_at_occ_one"]),
                                     4 * 2.220446049250313e-16 * abs(r["ratio_reference"]))
                self.assertEqual(r["max_relative_spread"], r["fortran_max_rel_spread"])

    def test_discrepancy_matches_the_lean_closed_form(self):
        """Compared against `branch_mismatch`, which this task does not change."""
        for point, r in self.summary["occupation_linearity"].items():
            with self.subTest(point=point):
                self.assertLess(r["max_relative_closed_form_error"], 1e-14)
        for occ in (0.75, 0.5, 0.25):
            row = next(r for r in self.parsed["rows"]["OCC"]
                       if r["point"] == "P1" and r["occ"] == occ)
            expected = analyze.closed_form(occ, row["ieps"], row["wt"], row["wxt"])
            self.assertAlmostEqual(row["delta"], expected, places=14)


class InvarianceTests(unittest.TestCase):
    """Secondary checks from the external review."""

    @classmethod
    def setUpClass(cls):
        cls.summary = analyze.summarize(analyze.parse(RAW))

    def test_common_energy_zero_shift_is_exact_until_the_subtraction_rounds(self):
        """Only `x = E - eps` enters the kernel, so a common shift is exactly
        invariant -- as long as `E + C` and `eps + C` still round to numbers
        whose difference is unchanged. At C = 1e17 that fails and `wxt`
        collapses to the TOL_Zero clamp. That is an input-construction limit,
        not a kernel asymmetry.
        """
        shift = self.summary["invariances"]["energy_zero_shift"]
        self.assertEqual(shift["largest_exact_shift"], 1e16)
        self.assertEqual(shift["inexact_shifts"], [1e17])
        for row in shift["rows"]:
            if row["shift"] <= 1e16:
                self.assertTrue(row["wxt_exact"] and row["value_exact"])

    def test_ieps_scaling_and_sign_flip_carry_through(self):
        scaling = self.summary["invariances"]["ieps_scaling"]
        self.assertLess(scaling["max_relative_deviation"], 4 * 2.220446049250313e-16)
        self.assertIn(-1.0, [r["lambda"] for r in scaling["rows"]])
        self.assertIn(-3.5, [r["lambda"] for r in scaling["rows"]])


class ReproducibilityTests(unittest.TestCase):
    def test_saved_summary_matches_the_saved_table(self):
        import json
        rebuilt = analyze.summarize(analyze.parse(RAW))
        saved = json.loads(SUMMARY.read_text())
        saved.pop("provenance")
        saved.pop("claim_boundary")
        self.assertEqual(json.loads(json.dumps(rebuilt, sort_keys=True)),
                         json.loads(json.dumps(saved, sort_keys=True)))

    def test_parser_rejects_a_truncated_or_widened_row(self):
        text = RAW.read_text()
        line = next(l for l in text.splitlines() if l.startswith("SWEEP"))
        for broken in (line.rsplit(" ", 1)[0], line + " 1.0"):
            with self.subTest(tail=broken[-20:]):
                with self.assertRaises(ValueError):
                    analyze.parse_text(text.replace(line, broken, 1))

    @unittest.skipUnless(compiler_available(),
                         "pinned arch.mk compiler is not present; run bgw/toolchain/setup.sh "
                         "and export BGW_TOOLCHAIN")
    def test_recompiling_reproduces_the_saved_table_byte_for_byte(self):
        with tempfile.TemporaryDirectory(dir="/tmp") as tmp:
            table, provenance = run_sweep.build_and_run(tmp)
        self.assertEqual(table, RAW.read_text())
        self.assertTrue(provenance["compiler_version"].startswith("GNU Fortran"))
        if provenance["pristine_present"]:
            self.assertEqual(provenance["pristine_sha256"],
                             provenance["mtxel_cor_sha256_accepted"])


if __name__ == "__main__":
    unittest.main()

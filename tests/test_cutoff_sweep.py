"""Tests for bgw/weighted_audit/cutoff_sweep.py.

These tests pin the sweep's behaviour and its agreement with the shipped
`weighted_mismatch.py` numbers. They deliberately do NOT re-derive or relax any
established value: 0.496, 9.356, 53 groups and 3702 records are asserted to be
reproduced, not recomputed under a new convention.
"""

from fractions import Fraction as F
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "weighted_audit"))

import cutoff_sweep as cs  # noqa: E402
import weighted_mismatch as wm  # noqa: E402

FIX = ROOT / "bgw" / "weighted_audit" / "fixtures"
RECORDS = FIX / "t004_nearpole_weighted.dat"
ACCUMULATORS = FIX / "t004_accumulators.dat"


class SweepFixtureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = cs.run(RECORDS, ACCUMULATORS)

    def test_population_matches_the_established_dataset(self):
        self.assertEqual(self.result["records"], 3702)
        self.assertEqual(self.result["groups_total"], 53)
        self.assertEqual(self.result["groups_usable"], 53)
        self.assertEqual(self.result["groups_unusable"], [])
        self.assertEqual(self.result["singular_records_excluded"], [])

    def test_shipped_cutoff_reproduces_the_published_headline(self):
        """At 1e-3 the sweep must give exactly the packet's 0.496 and its
        argmax group: call 107, iw=2, 134 events, accumulator -0.02903."""
        at_shipped = [r for r in self.result["curve"]
                      if r["relative_cutoff"] == 1e-3]
        self.assertEqual(len(at_shipped), 1)
        row = at_shipped[0]
        self.assertAlmostEqual(row["max_ratio"], 0.496, places=3)
        self.assertEqual(row["argmax_call_id"], 107)
        self.assertEqual(row["argmax_iw"], 2)
        self.assertEqual(row["argmax_events"], 134)
        self.assertEqual(row["argmax_icalc"], 1)
        self.assertEqual(row["argmax_band_in"], 8)
        self.assertAlmostEqual(row["argmax_accumulator"], 0.02903, places=5)
        self.assertEqual(row["groups_kept"], 47)
        self.assertEqual(row["groups_excluded"], 6)

    def test_agrees_with_weighted_mismatch_at_the_shipped_cutoff(self):
        """Independently recompute the shipped module's two headline maxima
        and require the sweep to reproduce both."""
        rows = wm.parse(RECORDS.read_text())
        acc = wm.parse_accumulators(ACCUMULATORS.read_text())
        groups, _s, _c, _t, _b = wm.analyse(rows)
        scale = max(abs(F(v["asxtemp"]) + F(v["achtemp"]))
                    for v in acc.values())
        cut = scale / 1000
        ratios = []
        for key, g in groups.items():
            a = abs(F(acc[key]["asxtemp"]) + F(acc[key]["achtemp"]))
            ratios.append((a, abs(F(g["signed"])) / a))
        expected_excl = max(r for a, r in ratios if a >= cut)
        expected_any = max(r for _a, r in ratios)

        shipped_row = next(r for r in self.result["curve"]
                           if r["relative_cutoff"] == 1e-3)
        self.assertEqual(shipped_row["max_ratio"], float(expected_excl))
        self.assertEqual(self.result["curve"][0]["max_ratio"],
                         float(expected_any))
        self.assertAlmostEqual(float(expected_any), 9.356, places=3)

    def test_headline_sits_on_a_wide_plateau(self):
        """The measured fact this analysis exists to report."""
        plateau = self.result["shipped_plateau"]
        self.assertIsNotNone(plateau)
        self.assertAlmostEqual(plateau["max_ratio"], 0.496, places=3)
        self.assertEqual(plateau["argmax_call_id"], 107)
        lo = plateau["relative_cutoff_lower_exclusive"]
        hi = plateau["relative_cutoff_upper"]
        self.assertLess(lo, 1e-3)
        self.assertGreater(hi, 1e-3)
        # the plateau spans more than two decades of cutoff
        self.assertGreater(hi / lo, 100.0)

    def test_curve_is_monotone_non_increasing(self):
        """Raising the cutoff can only remove groups, so the reported maximum
        can only fall or stay. A violation would mean the sweep is not
        evaluating a suffix of the accumulator-ordered groups."""
        seen = [r["max_ratio"] for r in self.result["curve"]
                if r["max_ratio"] is not None]
        for a, b in zip(seen, seen[1:]):
            self.assertLessEqual(b, a + 0.0)

    def test_breakpoints_reproduce_the_grid(self):
        """Every grid point must land on the plateau the exact step structure
        predicts. This is what licenses quoting the step table as the whole
        curve."""
        bps = self.result["breakpoints"]
        for row in self.result["curve"]:
            plateau = cs.plateau_containing(bps, row["relative_cutoff"])
            self.assertIsNotNone(plateau, row)
            self.assertEqual(plateau["max_ratio"], row["max_ratio"], row)
            self.assertEqual(plateau["argmax_call_id"], row["argmax_call_id"])

    def test_breakpoints_cover_zero_to_one_without_gaps(self):
        bps = self.result["breakpoints"]
        self.assertEqual(bps[0]["relative_cutoff_lower_exclusive"], 0.0)
        self.assertEqual(bps[-1]["relative_cutoff_upper"], 1.0)
        for a, b in zip(bps, bps[1:]):
            self.assertEqual(a["relative_cutoff_upper"],
                             b["relative_cutoff_lower_exclusive"])

    def test_small_reference_artefact_only_appears_below_the_plateau(self):
        """9.356 is the known small-reference artefact. It must be confined to
        the lowest plateau and must never be the reported value at or above
        the shipped cutoff."""
        for row in self.result["curve"]:
            if row["relative_cutoff"] >= 1e-3:
                self.assertLess(row["max_ratio"], 1.0, row)

    def test_grid_is_exact_at_integer_decades(self):
        grid = cs.default_grid()
        self.assertIn(F(1, 1000), grid)
        self.assertIn(F(1, 10 ** 6), grid)
        self.assertIn(F(1), grid)

    def test_documentation_states_the_limits_of_the_result(self):
        text = self.result["interpretation_limits"]
        self.assertIn("does NOT show the headline is physically meaningful",
                      text)
        self.assertIn("robustness diagnostic", self.result["what"].lower())


class SweepContractTest(unittest.TestCase):
    def test_rejects_a_population_with_no_usable_reference(self):
        groups = {(1, 2): dict(signed=F(1), ident=(1, 1, 1, 1, 1, 0, 0, 0),
                               n=1)}
        acc = {(1, 2): dict(asxtemp=1.0, achtemp=-1.0, subtotal=0.0,
                            ident=(1, 1, 1, 1, 0, 0, 0))}
        with self.assertRaises(cs.SweepError):
            cs.group_table(groups, acc)

    def test_missing_accumulator_row_is_reported_not_dropped(self):
        groups = {
            (1, 2): dict(signed=F(1, 2), ident=(1, 1, 1, 1, 1, 0, 0, 0), n=3),
            (9, 2): dict(signed=F(1, 4), ident=(1, 1, 1, 1, 1, 0, 0, 0), n=3),
        }
        acc = {(1, 2): dict(asxtemp=1.0, achtemp=0.0, subtotal=0.0,
                            ident=(1, 1, 1, 1, 0, 0, 0))}
        usable, unusable = cs.group_table(groups, acc)
        self.assertEqual(len(usable), 1)
        self.assertEqual(len(unusable), 1)
        self.assertEqual(unusable[0]["call_id"], 9)

    def test_evaluate_is_exact_at_the_boundary(self):
        """A group whose reference is exactly at the cutoff is KEPT: the
        shipped module excludes on strict `<`, and the sweep must match it or
        the curve would be off by one group at every breakpoint."""
        usable = [dict(key=(1, 2), call_id=1, iw=2, icalc=1, band_in=1, il=1,
                       iband=1, ispin=1, events=1,
                       abs_accumulator=F(1, 1000), ratio=F(5)),
                  dict(key=(2, 2), call_id=2, iw=2, icalc=1, band_in=1, il=1,
                       iband=1, ispin=1, events=1,
                       abs_accumulator=F(1), ratio=F(1, 2))]
        got = cs.evaluate(usable, F(1), F(1, 1000))
        self.assertEqual(got["groups_kept"], 2)
        self.assertEqual(got["max_ratio"], 5.0)

    def test_empty_keep_set_is_reported_not_crashed(self):
        usable = [dict(key=(1, 2), call_id=1, iw=2, icalc=1, band_in=1, il=1,
                       iband=1, ispin=1, events=1,
                       abs_accumulator=F(1, 10), ratio=F(5))]
        got = cs.evaluate(usable, F(1), F(1))
        self.assertEqual(got["groups_kept"], 0)
        self.assertIsNone(got["max_ratio"])


class SweepCliTest(unittest.TestCase):
    def test_table_and_json_run(self):
        import io
        import contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = cs.main([str(RECORDS), "--accumulators", str(ACCUMULATORS)])
        self.assertEqual(rc, 0)
        out = buf.getvalue()
        self.assertIn("0.495974", out)
        self.assertIn("relative cutoff", out)


if __name__ == "__main__":
    unittest.main()

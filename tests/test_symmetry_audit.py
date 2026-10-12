"""Tests for bgw/weighted_audit/symmetry_audit.py.

The headline assertion is a NEGATIVE result: the exported dataset cannot test
the band-index symmetry of Sigma, because BerkeleyGW never computed the
transposed matrix elements. These tests pin that negative result and the
evidence behind it, so a later change that quietly makes the module claim a
positive result has to break a test first.
"""

import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "weighted_audit"))

import symmetry_audit as sa  # noqa: E402

FIX = ROOT / "bgw" / "weighted_audit" / "fixtures"
RECORDS = FIX / "t004_nearpole_weighted.dat"
ACCUMULATORS = FIX / "t004_accumulators.dat"
SIGMA_INP = FIX / "fermi_sigma.inp"


class OffdiagBlockTest(unittest.TestCase):
    def test_parses_the_probe_input(self):
        got = sa.parse_offdiag_block(SIGMA_INP.read_text())
        self.assertEqual(got, [(1, 1, 1), (1, 8, 1), (2, 1, 2)])

    def test_ignores_comments_and_requires_a_closing_end(self):
        text = "begin offdiag\n 3 4 3 # trailing\nend\n"
        self.assertEqual(sa.parse_offdiag_block(text), [(3, 4, 3)])
        with self.assertRaises(sa.SymmetryError):
            sa.parse_offdiag_block("begin offdiag\n 3 4 3\n")

    def test_rejects_a_malformed_row(self):
        with self.assertRaises(sa.SymmetryError):
            sa.parse_offdiag_block("begin offdiag\n 3 4\nend\n")


class TestabilityLogicTest(unittest.TestCase):
    """The verdict logic, exercised away from the fixture."""

    def test_self_transpose_pair_alone_is_not_testable(self):
        v = sa.testability({(2, 1, 1): {}})
        self.assertFalse(v["testable"])
        self.assertIn("NOT TESTABLE", v["verdict"])
        self.assertEqual(v["testable_pairs"], [])

    def test_one_sided_pair_is_not_testable_and_names_the_missing_side(self):
        v = sa.testability({(2, 1, 8): {}, (2, 2, 1): {}})
        self.assertFalse(v["testable"])
        self.assertEqual(v["transposed_partners_missing"], [(1, 2), (8, 1)])

    def test_a_genuine_transposed_pair_would_be_testable(self):
        """Guards against a verdict that is hard-coded negative."""
        v = sa.testability({(2, 1, 8): {}, (2, 8, 1): {}})
        self.assertTrue(v["testable"])
        self.assertEqual(v["verdict"], "TESTABLE")
        self.assertEqual(v["testable_pairs"], [(1, 8), (8, 1)])


class FixtureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = sa.run(RECORDS, ACCUMULATORS, SIGMA_INP)

    def test_dataset_is_the_established_one(self):
        self.assertEqual(self.result["records"], 3702)
        self.assertEqual(self.result["accumulator_rows"], 456)

    def test_call_blocks_are_derived_and_uniform(self):
        self.assertEqual(self.result["call_blocks"], 24)
        self.assertEqual(self.result["calls_per_block"], [11])

    def test_fingerprinting_recovers_the_ket_band(self):
        """The ket band m is not an exported field. Recovering it, and having
        the recovered pairs equal the sigma.inp offdiag block exactly, is the
        evidence that the inventory below is the real one."""
        self.assertTrue(self.result["inventory_agrees_with_sigma_inp"])
        offdiag = {(e["n"], e["m"])
                   for e in self.result["band_pair_inventory"]
                   if e["icalc"] == sa.ICALC_OFFDIAGONAL}
        self.assertEqual(offdiag, {(1, 1), (1, 8), (2, 1)})

    def test_diagonal_calls_fingerprint_to_their_own_band(self):
        for e in self.result["band_pair_inventory"]:
            if e["icalc"] == sa.ICALC_DIAGONAL:
                self.assertEqual(e["n"], e["m"], e)

    def test_headline_verdict_is_not_testable(self):
        v = self.result["hermiticity_testability"]
        self.assertFalse(v["testable"])
        self.assertIn("NOT TESTABLE", v["verdict"])
        self.assertEqual(v["testable_pairs"], [])
        self.assertEqual(v["distinct_band_pairs_present"], [(1, 8), (2, 1)])
        self.assertEqual(v["transposed_partners_missing"], [(1, 2), (8, 1)])

    def test_the_missing_input_is_named_as_a_run_not_a_field(self):
        v = self.result["hermiticity_testability"]
        self.assertIn("NOT an additional export field",
                      v["what_would_be_required"])
        self.assertIn("sigma_matrix", v["what_would_be_required"])
        self.assertIn("asxtemp+achtemp", v["also_required_even_then"])

    def test_unresolved_calls_are_reported_not_guessed(self):
        self.assertEqual(self.result["calls_with_unresolved_bands"], [11])
        self.assertIn("rather than guessed", self.result["unresolved_note"])

    def test_source_reading_names_the_real_flavor_consequence(self):
        self.assertIn("MYCONJG is the identity",
                      self.result["source_reading"]["flavor"])
        self.assertIn("Sigma_nm = Sigma_mn",
                      self.result["source_reading"]["flavor"])


class GGDiagnosticTest(unittest.TestCase):
    """The (G, G') diagnostic is a DIFFERENT measurement. These tests exist
    mainly to keep it labelled as one."""

    @classmethod
    def setUpClass(cls):
        cls.result = sa.run(RECORDS, ACCUMULATORS, SIGMA_INP)
        cls.g = cls.result["gg_transpose_diagnostic"]

    def test_it_disclaims_being_the_band_index_test(self):
        text = self.g["THIS_IS_NOT_THE_BAND_INDEX_TEST"]
        self.assertIn("does NOT establish Sigma_nm != Sigma_mn", text)
        self.assertIn("near-pole occ != 1 subset only", text)

    def test_accounting_is_complete(self):
        total = (self.g["ordered_pairs_with_both_orderings_exported"]
                 + self.g["ordered_pairs_whose_transpose_was_not_exported"]
                 + self.g["records_with_ig_equal_igp"])
        self.assertEqual(total, self.result["records"])

    def test_measured_values(self):
        self.assertEqual(self.g["pairs_compared"], 3568)
        self.assertEqual(self.g["exactly_symmetric_pairs"], 0)
        self.assertAlmostEqual(self.g["max_relative_antisymmetry"],
                               4.705672493995905e-02, places=12)
        self.assertAlmostEqual(self.g["median_relative_antisymmetry"],
                               2.126205388175242e-03, places=12)


class CliTest(unittest.TestCase):
    def test_report_runs_and_states_the_verdict(self):
        import io
        import contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = sa.main([str(RECORDS), "--accumulators", str(ACCUMULATORS),
                          "--sigma-inp", str(SIGMA_INP)])
        self.assertEqual(rc, 0)
        out = buf.getvalue()
        self.assertIn("NOT TESTABLE", out)
        self.assertIn("NOT the band-index test", out)


if __name__ == "__main__":
    unittest.main()

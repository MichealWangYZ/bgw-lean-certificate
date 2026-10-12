import contextlib
import copy
import io
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw"))
import oracle
import reproduce as rep
import verify_export as v

# Two assertions copied verbatim from BerkeleyGW 4.0 testsuite/Si-EPM/Si.test,
# plus deliberate traps: a `Precision` change and a match after the block ends.
GPP_BLOCK = """\
Executable : sigma.real.x
Output : sig_GPP.out
Input  : sig_GPP.inp sigma.inp

Precision : 2e-5
match ; n2, k1 Exchange             ; GREP(sigma_hp.log, "ik =   1",  4, 4); -14.234668
Precision : 1e-6
match ; n2 x n1 k1 Exchange         ; GREP(sigma_hp.log, "2   1   2   real",  5, 0);   0.000000

Copy : Si.nnkp
match ; outside the GPP block      ; GREP(sigma_hp.log, "ik =   1",  4, 4); 999.0
"""


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.path = ROOT / "bgw/export/gpp_kernel_dump.dat"
        self.rows = v.load(self.path)

    def check(self, rows):
        return v.verify_rows(rows, self.path.name)

    def test_saved_evidence(self):
        self.assertEqual(v.check_manifest(self.path.parent), 11)
        self.assertEqual(self.check(self.rows)["s1_comparisons"], 16)
        near = v.verify_rows(v.load(self.path.with_name("gpp_nearpole_dump.dat")),
                             "gpp_nearpole_dump.dat")
        self.assertEqual(near["s1_comparisons"], 32)
        self.assertEqual(near["capture_stage"], "before_sexcut")

    def test_reject_missing_rows(self):
        for rows in ([], self.rows[:-1]):
            with self.subTest(count=len(rows)), self.assertRaises(ValueError):
                self.check(rows)

    def test_reject_malformed_files(self):
        line = self.path.read_text().splitlines()[0]
        for contents in ("", " ", " ".join(line.split()[:-1]), line + " 99",
                         line.replace(line.split()[5], "nan", 1), line + "\n" + line):
            with self.subTest(contents=contents[:40]), tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "sample.dat"
                path.write_text(contents)
                with self.assertRaises(ValueError):
                    v.load(path)

    def test_reject_corrupt_outputs_and_domain(self):
        for field, value in (("omega2", 999.0), ("ssx", 999.0), ("sch", 999.0),
                             ("occ", 0.5), ("wtilde", -1.0),
                             ("wxt", self.rows[0]["wtilde"])):
            rows = copy.deepcopy(self.rows)
            rows[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.check(rows)

    def test_reject_only_placeholders(self):
        rows = [dict(self.rows[1], rec=i + 1) for i in range(64)]
        with self.assertRaises(ValueError):
            self.check(rows)

    def test_capture_stage_matters_for_clamp(self):
        row = dict(ieps=1, wtilde=1, wxt=-1.01)
        before, after = v.predict(row, "before_sexcut"), v.predict(row, "after_sexcut")
        self.assertTrue(before[4])
        self.assertNotEqual(before[1], 0)
        self.assertEqual(after[1], 0)

    def test_reject_truncated_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "SHA256SUMS").write_text("")
            with self.assertRaises(ValueError):
                v.check_manifest(tmp)

    def test_transcript_rejects_empty_and_extra_columns(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "scan.out"
            for content in ("", "1 2 1 1 1 1 1 1 99\n"):
                path.write_text(content)
                with self.assertRaises(ValueError), contextlib.redirect_stdout(io.StringIO()):
                    oracle.main(path)

    def test_residual_threshold_is_neither_vacuous_nor_hair_trigger(self):
        for delta, rejected in ((float(v.ABS_TOL) / 100, False),
                                (float(v.ABS_TOL) * 100, True)):
            rows = copy.deepcopy(self.rows)
            rows[0]["ssx"] += delta
            with self.subTest(delta=delta):
                if rejected:
                    with self.assertRaises(ValueError):
                        self.check(rows)
                else:
                    self.assertGreater(self.check(rows)["max_abs_error_ssx"], 0)

    def test_manifest_rejects_tampering_and_extra_evidence(self):
        def copied(tmp):
            for path in (ROOT / "bgw/export").iterdir():
                shutil.copy2(path, Path(tmp) / path.name)
            return Path(tmp)

        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(v.check_manifest(copied(tmp)), 11)
        for name, contents in (("gpp_branch_counts.dat", "tampered\n"),
                               ("unexpected.dat", "extra\n")):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                (copied(tmp) / name).write_text(contents)
                with self.assertRaises(ValueError):
                    v.check_manifest(Path(tmp))


class UpstreamBenchmarkTests(unittest.TestCase):
    """The upstream GPP assertions are parsed, not re-encoded by hand."""

    def setUp(self):
        self.log = (ROOT / "bgw/export/sigma_hp.log").read_text()
        self.assertions = rep.parse_assertions(GPP_BLOCK)

    def test_block_boundaries_and_precision_in_force(self):
        self.assertEqual([a["name"] for a in self.assertions],
                         ["n2, k1 Exchange", "n2 x n1 k1 Exchange"])
        self.assertEqual([a["tolerance"] for a in self.assertions], [2e-5, 1e-6])

    def test_saved_log_satisfies_the_parsed_assertions(self):
        results = rep.evaluate_assertions(self.assertions, self.log)
        self.assertEqual(len(results), 2)
        self.assertLess(max(r["absolute_error"] for r in results), 2e-5)

    def test_nonfinite_benchmark_values_are_rejected(self):
        base = dict(name="finite", needle="sample", column=2, offset=0,
                    expected=1.0, tolerance=1e-6)
        for value in ("nan", "inf", "-inf"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                rep.evaluate_assertions([base], "sample " + value)

    def test_value_mutants_are_rejected_but_in_tolerance_shifts_are_not(self):
        for shift, rejected in ((1e-7, False), (1e-3, True)):
            mutated = [dict(self.assertions[0],
                            expected=self.assertions[0]["expected"] + shift)]
            with self.subTest(shift=shift):
                if rejected:
                    with self.assertRaises(ValueError):
                        rep.evaluate_assertions(mutated, self.log)
                else:
                    self.assertEqual(len(rep.evaluate_assertions(mutated, self.log)), 1)

    def test_unresolvable_greps_are_rejected(self):
        for mutation in ({"needle": "no such line"}, {"column": 99},
                         {"offset": 10 ** 6}):
            with self.subTest(**mutation), self.assertRaises(ValueError):
                rep.evaluate_assertions(
                    [dict(self.assertions[0], **mutation)], self.log)

    def test_unsupported_or_missing_upstream_syntax_is_rejected(self):
        for label, block in (
                ("no block", ""),
                ("not GREP", GPP_BLOCK.replace("GREP(sigma_hp.log,", "LINE(sigma_hp.log,")),
                ("no precision", GPP_BLOCK.replace("Precision : 2e-5\n", "")),
                ("wrong arity", GPP_BLOCK.replace(',  4, 4)', ',  4)')),
                ("missing field", GPP_BLOCK.replace("match ; n2, k1 Exchange             ;",
                                                    "match ;"))):
            with self.subTest(label=label), self.assertRaises(ValueError):
                rep.parse_assertions(block)


class ReproductionDiagnosisTests(unittest.TestCase):
    """A failed reproduction must be diagnosable, not just reported as unequal."""

    def test_identical_files(self):
        saved = ROOT / "bgw/export/gpp_kernel_dump.dat"
        self.assertEqual(rep.diagnose("dump", saved, saved),
                         {"file": "dump", "identical": True})

    def test_perturbed_dump_reports_the_column_and_line(self):
        saved = ROOT / "bgw/export/gpp_kernel_dump.dat"
        with tempfile.TemporaryDirectory() as tmp:
            fresh = Path(tmp) / saved.name
            lines = saved.read_text().splitlines()
            fields = lines[0].split()
            fields[8] = repr(float(fields[8]) * (1 + 1e-13))
            lines[0] = " ".join(fields)
            fresh.write_text("\n".join(lines) + "\n")
            record = rep.diagnose(saved.name, fresh, saved)
        self.assertFalse(record["identical"])
        self.assertEqual(record["differing_line_numbers"], [1])
        self.assertIn("wtilde", record["numeric_deviation"])
        self.assertLess(record["numeric_deviation"]["wtilde"]["max_rel"], 1e-12)


if __name__ == "__main__":
    unittest.main()

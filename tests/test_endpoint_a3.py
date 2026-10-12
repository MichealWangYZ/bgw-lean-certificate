"""Approximation layer A3(b) (docs/ENDPOINT.md): exact vs G0W0@HF gap of the
half-filled Hubbard dimer. Checks the independent numerical/symbolic route,
the committed evidence, and the proof-integrity of the Lean files. Does not
run Lean (the build and `GW/Audit.lean` run in scripts/verify.py)."""
import hashlib
import json
import math
import pathlib
import re
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint/a3_dimer"))
import dimer  # noqa: E402

LEAN = {k: ROOT / f"GW/Endpoint/HubbardDimer{k}.lean" for k in ("Fock", "Exact", "")}
LOG = ROOT / "bgw/endpoint/a3_dimer/mutations.log"


class CrossCheck(unittest.TestCase):
    def test_numeric_and_symbolic_routes_agree(self):
        """ED, numerical RPA inversion, imaginary-axis frequency quadrature and
        bracketing QP root finding reproduce every closed form stated in Lean."""
        out = pathlib.Path(tempfile.mkdtemp(prefix="a3-")) / "x.json"
        self.assertEqual(dimer.main(["--out", str(out)]), 0)
        r = json.loads(out.read_text())
        self.assertTrue(r["ok"])
        self.assertEqual(r["symbolic"]["gap_exact"], "-2*t + sqrt(U**2 + 16*t**2)")
        self.assertEqual(r["symbolic"]["series_err_gw"].split(" + ")[-1], "u**2/8")

    def test_bounds_hold_on_a_grid_and_are_tight(self):
        """The inequalities of `gw_error_bounds`/`hf_error_bounds`, numerically,
        and the leading coefficients +-1/8 (so the bound's constant is sharp)."""
        for t in (0.3, 1.0, 2.5):
            for k in range(1, 401):
                U = t * k / 400
                e = dimer.gap_gw(t, U) - dimer.gap_exact(t, U)
                f = dimer.gap_hf(t, U) - dimer.gap_exact(t, U)
                self.assertLessEqual(U * U / (8 * t) - 3 * U**3 / (16 * t * t), e + 1e-13)
                self.assertLessEqual(e, U * U / (8 * t) - U**3 / (16 * t * t) + 1e-13)
                self.assertLessEqual(abs(e), U * U / (8 * t) + 1e-13)
                self.assertLessEqual(-U * U / (8 * t), f + 1e-13)
                self.assertLessEqual(f, -U * U / (8 * t) + U**4 / (512 * t**3) + 1e-13)
                self.assertLess(abs(e), abs(f))
            U = 1e-4 * t
            self.assertAlmostEqual((dimer.gap_gw(t, U) - dimer.gap_exact(t, U)) / U**2 * 8 * t, 1, 3)
            self.assertAlmostEqual((dimer.gap_hf(t, U) - dimer.gap_exact(t, U)) / U**2 * 8 * t, -1, 3)

    def test_committed_crosscheck(self):
        r = json.loads((ROOT / "bgw/endpoint/a3_dimer/crosscheck.json").read_text())
        self.assertTrue(r["ok"])
        for p in r["numeric"]:
            self.assertAlmostEqual(p["gap_exact_ED"], dimer.gap_exact(p["t"], p["U"]), places=11)
            self.assertAlmostEqual(p["gap_gw_numeric"], dimer.gap_gw(p["t"], p["U"]), places=8)


class LeanIntegrity(unittest.TestCase):
    def test_no_escape_hatches(self):
        for p in LEAN.values():
            body = re.sub(r"/-.*?-/", "", p.read_text(), flags=re.S)
            body = re.sub(r"--.*", "", body)
            for bad in ("sorry", "admit", "native_decide", "axiom ", "unsafe"):
                self.assertNotIn(bad, body, f"{bad} in {p.name}")

    def test_every_theorem_is_audited(self):
        audit = (ROOT / "GW/Audit.lean").read_text()
        for p in LEAN.values():
            for name in re.findall(r"^theorem\s+([\w.]+)", p.read_text(), re.M):
                self.assertIn(f"#print axioms GW.Endpoint.HubbardDimer.{name}\n", audit, name)

    def test_closed_forms_match_lean(self):
        exact = LEAN["Exact"].read_text()
        gw = LEAN[""].read_text()
        self.assertIn("noncomputable def gapExact (t U : ℝ) : ℝ := Real.sqrt (U ^ 2 + 16 * t ^ 2) - 2 * t", exact)
        self.assertIn("Real.sqrt ((2 * t + hRPA t U) ^ 2 + 4 * t * U ^ 2 / hRPA t U)", gw)
        self.assertIn("noncomputable def hRPA (t U : ℝ) : ℝ := Real.sqrt (4 * t ^ 2 + 4 * t * U)", gw)
        self.assertIn("noncomputable def gapGW (t U : ℝ) : ℝ := Dgw t U - hRPA t U", gw)
        t, U = 1.3, 0.7
        h = math.sqrt(4 * t * t + 4 * t * U)
        self.assertAlmostEqual(dimer.gap_gw(t, U), math.sqrt((2 * t + h) ** 2 + 4 * t * U * U / h) - h)

    def test_mutation_log_is_current_and_green(self):
        """The committed mutation log was produced from the current Lean files
        and every mutant was rejected by Lean for the expected reason."""
        log = LOG.read_text()
        for p in LEAN.values():
            sha = hashlib.sha256(p.read_bytes()).hexdigest()
            self.assertIn(f"{p.relative_to(ROOT)} sha256: {sha}", log)
        self.assertTrue(log.rstrip().endswith("ALL OK"))
        rows = [ln for ln in log.splitlines() if ln.endswith((" OK", " FAIL"))]
        self.assertGreaterEqual(len(rows), 15)
        self.assertTrue(all(ln.endswith(" OK") for ln in rows))


if __name__ == "__main__":
    unittest.main()

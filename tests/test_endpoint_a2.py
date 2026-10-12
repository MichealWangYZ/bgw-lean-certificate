"""A2 gates: the contour-deformation (CD) self-energy.

Step 1: spec_cd reproduces the pristine production CD run's sigma_hp.log
columns (Res, Int, Cor, Sig and primed, real and imaginary) to print
precision. Step 2 (fast version): the exact-frequency residue and the
converged imaginary-axis quadrature, checked against the recorded
data/a2_exact.json values and for quadrature refinement.
Skips if the pristine tree or the run directory is missing. Float evidence.
"""
import functools
import json
import pathlib
import sys
import unittest

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import run_production as prod  # noqa: E402

RUN = pathlib.Path.home() / "bgw-e-runs/a2-cd"
HAVE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES) and \
    all((RUN / f).exists() for f in ("eps0mat", "epsmat", "sigma_hp.log", "WFN_inner", "WFN", "WFNq"))
DATA = ROOT / "bgw/endpoint/data/a2_exact.json"


@functools.lru_cache(maxsize=None)
def setup():
    import spec_cd
    return spec_cd.CDSetup(RUN)


@functools.lru_cache(maxsize=None)
def direct():
    import a2_exact
    return a2_exact.DirectEps(setup(), RUN)


@unittest.skipUnless(HAVE, "pristine BerkeleyGW tree or ~/bgw-e-runs/a2-cd missing")
class A2Step1Reproduction(unittest.TestCase):
    def check(self, ik, bands):
        import a2_repro
        rows = a2_repro.compare(setup(), RUN, ik, bands)
        for r in rows:
            for c in a2_repro.COLS:
                self.assertLessEqual(abs(r["diff"][c]), a2_repro.HALF_ULP[c] * 1.0001,
                                     (ik, r["bands"], c, r["ours"][c], r["prod"][c]))
        return rows

    def test_X_and_L(self):
        rX = self.check(2, [5, 6])[0]
        rL = self.check(1, [5])[0]
        # the O1 correlation contribution as printed (+145.003 meV)
        self.assertAlmostEqual((rX["ours"]["ReCor"] - rL["ours"]["ReCor"]) * 1e3, 145.003, delta=2e-3)

    def test_gamma_all_bands(self):
        """Occupied bands take residues with wx < 0 (the other selection branch)."""
        self.check(0, list(range(1, 9)))

    def test_grid_facts(self):
        cd = setup()
        self.assertEqual((cd.nreal, cd.nimag, cd.nfreqeval), (400, 30, 241))
        self.assertEqual(cd.eta, 0.05)

    def test_direct_eps_matches_file(self):
        """spec_cd.epsinv_ff reproduces the file's eps^-1 at real and imaginary
        grid frequencies of every irreducible q."""
        import spec
        import spec_cd
        cd = setup()
        idx = [0, 57, 399, 400, 413, 429]
        for qi, b, is0 in cd.scr.irr:
            W = cd.run.eps0["freq_grid"][idx] + cd.run.eps0["freq_brd"][idx]
            Gs, E = spec_cd.epsinv_ff(direct().er, b["q"], W, q0=is0)
            Gf = cd.run.eps["gvec"][b["isrtx"][:b["nmtx"]] - 1]
            pos = spec.gindex(Gs)
            ii = np.array([pos[tuple(g)] for g in Gf])
            self.assertLess(np.abs(E[:, ii][:, :, ii] - b["epsinv"][idx]).max(), 1e-10)


@unittest.skipUnless(HAVE and DATA.is_file(), "run directory or recorded a2_exact.json missing")
class A2Step2Fast(unittest.TestCase):
    """L state only (one band): exact residue, exact integral."""

    def test_exact_L_matches_record_and_refines(self):
        import a2_exact
        cd = setup()
        rec = json.loads(DATA.read_text())["states"]["L"]
        ik, bands = 1, [5]
        k = cd.run.kpts[ik]
        coarse = a2_exact.Exact(cd, direct(), quad=(1e-4, 1e5, 2, 8))
        t = a2_exact.summary(a2_exact.terms(cd, k, bands, residue=coarse.residue,
                                            integral=coarse.integral, static=coarse.static))
        ref = rec["exact"]["0.05"]
        for key in ("ReRes", "ImRes", "Int", "achcor", "Cor"):
            # coarse quadrature vs the recorded medium one: quadrature converged
            self.assertAlmostEqual(t[key], ref[key], delta=1e-8, msg=key)
        # the recorded production reproduction differs from the exact value by
        # the interpolation + quadrature error, which is not zero
        self.assertGreater(abs(rec["production_repro"]["Cor"] - ref["Cor"]), 1e-5)

    def test_lorentz_quadrature_analytic(self):
        """The Lorentzian quadrature on sW(iw) = A/(1 + w^2/b^2), whose integral
        is A b sgn(wx) / (2 (|wx| + b)), for |wx| from 1e-6 to 30 eV."""
        import a2_exact
        lo, hi = 1e-4, 1e5
        w, dw = a2_exact.log_nodes(lo, hi, 4, 12)
        A, b = 1.7, 5.3
        for wx in (1e-6, -1e-6, 0.03, -0.7, 4.0, -30.0):
            sW = A / (1 + (w / b) ** 2)
            got = a2_exact.lorentz_integral(A, sW - A, wx, w, dw, lo, hi)
            exact = 0.5 * A * b / (abs(wx) + b) * np.sign(wx)
            self.assertAlmostEqual(got, exact, delta=1e-9 * A, msg=wx)


if __name__ == "__main__":
    unittest.main()

"""BRIDGE-DISC: the theory GPP kernel at (x, Omega^2) = (0, 0) and the ideal fcc metric
(GW/Bridge/Disc.lean, bgw/bridge_disc/disc.py, docs/BRIDGE.md last section).

Independent oracle: plain numpy / integer arithmetic from the physics definitions. It
never reads Lean output and does not use disc.py's census code:

* the HL pole term R/(x -+ w), R = Omega2/(2w), w = sqrt(Omega2/I) near (0, 0) --
  always run;
* the exported bdot (from the committed coulomb_cert.json header) against the ideal fcc
  metric, and the committed D3 result data/disc.json -- always run;
* on a fresh pinned run: the Cartesian-orthogonal (q+G, q+G') pairs counted in INTEGER
  Cartesian coordinates (not via a metric), the binary64 Omega2 BerkeleyGW's wpeff
  formula gives on them, and the census of disc.json -- needs the pristine tree.
"""
import functools
import itertools
import json
import pathlib
import sys
import tempfile
import unittest
from fractions import Fraction as Fr

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import run_production as prod  # noqa: E402

DATA = json.loads((ROOT / "bgw/bridge_disc/data/disc.json").read_text())
COUL = json.loads((ROOT / "bgw/endpoint/data/coulomb_cert.json").read_text())
HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)
TS = 4722366482869645 / 2 ** 72


def pole_term(Iv, Ov, x, occ):
    """B1 closed form of one HL mode: R/(x + w) occupied, R/(x - w) empty."""
    w = np.sqrt(Ov / Iv)
    R = Ov / (2 * w)
    return R / (x + w) if occ else R / (x - w)


class Kernel(unittest.TestCase):
    def test_x0_is_minus_half_I_for_every_small_Omega2(self):
        for Iv in (0.3, 1.7, -0.8):
            for e in range(1, 30, 3):
                Ov = np.sign(Iv) * 10.0 ** (-e)
                self.assertAlmostEqual(pole_term(Iv, Ov, 0.0, False), -Iv / 2, delta=1e-12)
                self.assertAlmostEqual(pole_term(Iv, Ov, 0.0, True), Iv / 2, delta=1e-12)

    def test_vanishes_for_x_nonzero(self):
        for x in (1e-3, -0.5, 2.0):
            vals = [max(abs(pole_term(0.7, 10.0 ** (-e), x, occ)) for occ in (0, 1)) for e in (10, 20, 30)]
            self.assertTrue(vals[0] > vals[1] > vals[2])
            self.assertLess(vals[-1], 1e-12)

    def test_residue_and_pole_vanish_together(self):
        Iv = 0.9
        for e in (4, 8, 12):
            Ov = 10.0 ** (-e)
            w = np.sqrt(Ov / Iv)
            self.assertAlmostEqual(Ov / (2 * w) / w, Iv / 2, delta=1e-12)
            self.assertLess(w, 10.0 ** (-e / 2 + 0.1))

    def test_every_value_near_origin(self):
        """thK_cluster's construction: x = t w, Omega2 = w^2 I, t = 1 + I/(2c)."""
        rng = np.random.default_rng(7)
        for _ in range(50):
            Iv = rng.uniform(0.1, 2.0) * rng.choice([-1, 1])
            c = rng.uniform(-100, 100)
            t = 1 + Iv / (2 * c)
            w = 1e-9
            x, Ov = t * w, w * w * Iv
            self.assertLess(max(abs(x), abs(Ov)), 1e-6)
            self.assertAlmostEqual(pole_term(Iv, Ov, x, False) / c, 1.0, delta=1e-6)

    def test_zero_strength_W_is_zero_but_limit_is_not(self):
        """gppC = Omega2/(omega^2 - Omega2/I): 0 at Omega2 = 0 for every omega, -I at
        omega = 0 for every Omega2 != 0."""
        Iv = 0.6
        g = lambda O, om: O / (om * om - O / Iv)  # noqa: E731
        self.assertEqual(g(0.0, 0.3), 0.0)
        for e in (3, 9, 15):
            self.assertAlmostEqual(g(10.0 ** (-e), 0.0), -Iv, delta=1e-12)
        self.assertLess(abs(g(1e-15, 0.3)), 1e-13)


class Metric(unittest.TestCase):
    def test_exported_bdot_is_ideal_up_to_one_ulp(self):
        B = COUL["bdot"]                                  # the WFN header values
        d, o = Fr(B[0][0]), Fr(B[0][1])
        self.assertEqual(d, Fr(5065758257150985, 2 ** 52))
        self.assertEqual(o, Fr(-6754344342867979, 2 ** 54))
        for i, j in itertools.product(range(3), repeat=2):
            self.assertEqual(Fr(B[i][j]), d if i == j else o)
        c = d / 3
        self.assertEqual(Fr(float(c)), c)                 # the ideal metric is binary64
        self.assertEqual(np.nextafter(B[0][1], -np.inf), float(-c))   # one ulp, towards larger |.|

    def test_d3_ideal_metric(self):
        cmp = DATA["compare"]
        self.assertTrue(cmp["overlap"])
        self.assertLessEqual(cmp["max_abs_difference_meV"], cmp["width_specA_meV"] + cmp["width_ideal_meV"])
        # the +28 meV switch: its class is empty with the ideal metric, so the switched
        # O1 is the baseline (the enclosure of 0 has the baseline's width)
        lo, hi = cmp["switch_drop_O_x0_ideal_meV"]
        self.assertTrue(lo <= 0.0 <= hi)
        self.assertLessEqual(hi - lo, 2 * cmp["width_ideal_meV"] + 1e-12)   # [o1] - [o1]
        self.assertGreater(cmp["switch_drop_O_x0_specA_meV"][0], 28.0)
        MEAS = json.loads((ROOT / "bgw/bridge_measure/data/measure.json").read_text())
        for t in ("tally_X", "tally_L"):
            d3, sa = DATA["d3"][t], MEAS[t]
            self.assertEqual(d3["drop_O"]["count"], 0)
            # every rounded-metric drop_O mode is an exact Omega2 = 0 mode here
            self.assertEqual(d3["drop_O_O0"]["count"], sa["drop_O_O0"]["count"] + sa["drop_O"]["count"])
            for c in ("generic_ok", "occ_near_ok", "invalid", "emp_near", "zero_mode"):
                self.assertEqual(d3[c]["count"], sa[c]["count"], c)

    def test_census(self):
        c = DATA["census"]
        self.assertEqual(c["min_nonzero_ideal_over_c"], "1/4")
        self.assertLess(c["max_bound_over_TS"], 1.0)
        self.assertEqual(c["orth_rho_zero"], 0)
        self.assertTrue(c["spheres"]["same"])


@functools.lru_cache(maxsize=None)
def fresh():
    d = pathlib.Path(tempfile.mkdtemp(prefix="bd-")) / "run"
    prod.run(d)
    return d


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class FreshRun(unittest.TestCase):
    def test_orthogonal_pairs_integer_cartesian(self):
        """Count (q+G) perp (q+G') with INTEGER Cartesian coordinates 2 b(q+G), b rows
        (-1,1,1), (1,-1,1), (1,1,-1); check BerkeleyGW's binary64 wpeff Omega2 on them is
        below TOL_Small, and the per-q counts of disc.json."""
        import spec
        import bgwio
        run = spec.Run(fresh())
        rho = bgwio.read_rho(fresh() / "RHO")
        ridx = spec.gindex(rho["gvec"])
        b = np.array([[-1, 1, 1], [1, -1, 1], [1, 1, -1]])
        wpsq_over = 13.60569253 ** 2 * 16 * np.pi / run.cr.celvol / (8 * np.pi)
        counts, maxO = [], 0.0
        for q in run.qlist:
            Gs, _ = run.sphere(q, run.ecuts)
            V = np.rint(2 * (q[None, :] + Gs)).astype(np.int64) @ b     # 2 x Cartesian, integer
            D = V @ V.T
            B = run.cr.bdot
            qG = q[None, :] + Gs
            dotf = qG @ B @ qG.T                                         # binary64, as the source
            n = 0
            for i, j in zip(*np.nonzero(D == 0)):
                if not q.any() and not Gs[i].any():
                    continue
                n += 1
                k = tuple(Gs[i] - Gs[j])
                r = rho["rho"][ridx[k]]
                v = 8 * np.pi / (qG[i] @ B @ qG[i])                     # point value, scale only
                O = wpsq_over * v * dotf[j, i] * r
                maxO = max(maxO, abs(O))
            counts.append(n)
        self.assertEqual(counts, [p["orth"] for p in DATA["census"]["per_q"]])
        self.assertLess(maxO, TS)
        self.assertGreater(maxO, 0.0)   # the rounding residue is really there


if __name__ == "__main__":
    unittest.main()

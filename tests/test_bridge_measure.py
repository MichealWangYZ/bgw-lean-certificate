"""BRIDGE-MEASURE: the measured size of `GW.Bridge.sigA_eq_theory`'s departures on
Si-EPM (docs/BRIDGE.md, last section; bgw/bridge_measure/measure.py).

Three layers:

* unit checks of the per-mode classifier and values of measure.py against the
  Compare.lean statements (mode_eq, occ_pole_point / discrepancy_witness,
  bgw_invalid_mode) on synthetic modes -- always run;
* checks of the committed measurement `bgw/bridge_measure/data/measure.json`
  against the committed E1 certificate `cert_o1.json` -- always run;
* a fresh pinned production run reproducing the counts and the baseline --
  needs the pristine BerkeleyGW tree, skipped otherwise.
"""
import functools
import json
import pathlib
import sys
import tempfile
import types
import unittest

from fractions import Fraction as Fr

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
sys.path.insert(0, str(ROOT / "bgw/bridge_measure"))
import measure as M  # noqa: E402
import run_production as prod  # noqa: E402
from iv import I  # noqa: E402

DATA = json.loads((ROOT / "bgw/bridge_measure/data/measure.json").read_text())
CERT = json.loads((ROOT / "bgw/endpoint/data/cert_o1.json").read_text())
HAVE_TREE = all((prod.DEFAULT_TREE / b).is_file() for b in prod.BINARIES)
SELF = types.SimpleNamespace(bgw_value=M.Measure.bgw_value)


def mode(Iv, Ov, xv, occ):
    Ie, O = I.exact(np.array([[Iv]])), I.exact(np.array([[Ov]]))
    x = I.exact(np.array([[xv]]))
    cl = M.Measure.classify(SELF, Ie, O, x, occ)
    cls = [k for k, m in cl["c"].items() if m[0, 0]]
    return cl, cls[0], Ie, O, x


def thK(Iv, Ov, xv, occ):
    w = np.sqrt(Ov / Iv)
    return Ov / (2 * w * (xv + w)) if occ else Ov / (2 * w * (xv - w))


class ModeRules(unittest.TestCase):
    def test_mode_eq_on_random_modeok(self):
        """Compare.mode_eq: on ModeOK modes the BGW value equals thK."""
        rng = np.random.default_rng(20260929)
        hits = {"generic_ok": 0, "occ_near_ok": 0}
        for _ in range(400):
            Iv = rng.uniform(0.01, 1.0) * rng.choice([-1, 1])
            w = rng.uniform(0.6, 30.0)
            Ov = w * w * Iv
            occ = bool(rng.integers(2))
            xv = rng.uniform(-40, 40) if rng.random() < 0.7 else w + rng.uniform(-0.4, 0.4)
            cl, c, *_ = mode(Iv, Ov, xv, occ)
            if c in hits:
                hits[c] += 1
                v = cl["val"]
                self.assertAlmostEqual(float(v.mid()[0, 0]), thK(Iv, Ov, xv, occ), delta=1e-9 * (1 + abs(thK(Iv, Ov, xv, occ))))
        self.assertGreater(hits["generic_ok"], 50)
        self.assertGreater(hits["occ_near_ok"], 20)

    def test_discrepancy_witness(self):
        """Compare.discrepancy_witness: I = Omega2 = 1, x = 1 = wtilde, occupied: theory 1/4.
        The rigorous classifier cannot place x = wtilde on either side of the near-pole
        test and refuses (raises) -- so a completed production pass certifies that no
        x = wtilde coincidence occurs anywhere in its scope. One step off it the mode is
        ModeOK (occ_near_ok) with the theory value."""
        with self.assertRaises(NotImplementedError):
            mode(1.0, 1.0, 1.0, True)
        self.assertAlmostEqual(thK(1.0, 1.0, 1.0, True), 0.25, delta=1e-15)
        cl, c, *_ = mode(1.0, 1.0, 1.0 + 1e-9, True)
        self.assertEqual(c, "occ_near_ok")
        self.assertAlmostEqual(float(cl["val"].mid()[0, 0]), 0.25, delta=1e-8)

    def test_invalid_mode_is_static(self):
        """GPPModel.bgw_invalid_mode: wt2 < 0 -> wtilde = 1e12, value -> -I (static COHSEX)."""
        cl, c, *_ = mode(0.3, -2.0, 3.0, True)
        self.assertEqual(c, "invalid")
        # CH/2 - SX -> (-I)/2 - (-I) = I/2
        self.assertAlmostEqual(float(cl["val"].mid()[0, 0]), 0.3 / 2, delta=1e-9)

    def test_empty_near_pole_zeroed(self):
        """Compare.emp_near_zero: empty band, valid, not Generic -> 0."""
        cl, c, *_ = mode(0.5, 0.5 * 4.0, 2.1, False)
        self.assertEqual(c, "emp_near")
        self.assertLess(float(cl["val"].mag()[0, 0]), 1e-300)

    def test_x0_discontinuity(self):
        """The theory kernel at x = 0 is -I/2 for every Omega2 > 0 (emptyTerm(w^2 I, 0, w)),
        but its Omega2 = 0 value is 0: the dropped-mode switch at x = 0 is discontinuous."""
        for Ov in (1e-2, 1e-8, 1e-15):
            self.assertAlmostEqual(thK(0.02, Ov, 0.0, False), -0.01, delta=1e-12)

    def test_classes_partition(self):
        rng = np.random.default_rng(7)
        Ie = I.exact(rng.normal(0, 0.3, (9, 9)) * (rng.random((9, 9)) < 0.8))
        O = I.exact(rng.normal(0, 3.0, (9, 9)) * (rng.random((9, 9)) < 0.8))
        for occ in (True, False):
            cl = M.Measure.classify(SELF, Ie, O, I.exact(np.full((9, 9), 1.37)), occ)
            self.assertTrue(np.all(sum(m.astype(int) for m in cl["c"].values()) == 1))


class IntervalSerialization(unittest.TestCase):
    def test_mev_is_outward(self):
        """measure.mev (also used by disc.py) contains the exact meV image of its input;
        the old scalar 1e3 * float(.) form returned [100, 100] for I.exact(0.1)."""
        lo, hi = M.mev(I.exact(0.1))
        exact = Fr(0.1) * 1000
        self.assertLessEqual(Fr(lo), exact)
        self.assertLessEqual(exact, Fr(hi))
        self.assertGreater(hi, 100.0)
        for a, b in ((-4.0424001883438985, -3.514062828664954), (0.014889706193, 0.015405753667)):
            lo, hi = M.mev(I(a, b))
            self.assertLessEqual(Fr(lo), Fr(a) * 1000)
            self.assertLessEqual(Fr(b) * 1000, Fr(hi))


class CommittedMeasurement(unittest.TestCase):
    def test_counts_match_certificate(self):
        """The independent float classifier over cert.py's accumulation scope reproduces
        cert_o1.json branch_stats exactly."""
        fc, bs = DATA["float_cross_check"], CERT["branch_stats"]
        for k in ("invalid_modes", "near_pole_modes", "sexcut_clamped"):
            self.assertEqual(fc[k], bs[k], k)
        self.assertEqual(fc["wdiff_zero_exact"], 0)
        self.assertEqual(bs["wdiff_zero_possible"], 0)

    def test_interval_and_float_classifiers_agree(self):
        """On the O1 scope the interval classifier (tally) and the float one agree."""
        o1 = DATA["float_cross_check"]["O1_scope"]
        for lab in ("X", "L"):
            t = DATA["tally_" + lab]
            self.assertEqual(o1[lab]["invalid"], t["invalid"]["count"], lab)
            self.assertEqual(o1[lab]["occ_near"], t["occ_near_ok"]["count"] + t["occ_clampN"]["count"]
                             + t["occ_other"]["count"], lab)

    def test_baseline_inside_certificate(self):
        """measure.py's own interval Sigma reproduces the E1 enclosure (overlap)."""
        b = DATA["baseline"]
        for mine, theirs in ((b["Eqp1_X"], CERT["Eqp1_X"]), (b["Eqp1_L"], CERT["Eqp1_L"])):
            self.assertLessEqual(max(mine[0], theirs[0]), min(mine[1], theirs[1]))
        o = b["O1_meV"]
        self.assertLessEqual(max(o[0], 1e3 * CERT["O1_lo"]), min(o[1], 1e3 * CERT["O1_hi"]))

    def test_modeok_rows_are_zero(self):
        """mode_eq measured: switching a ModeOK class to thK moves O1 by < 1e-5 meV
        (enclosure contains 0)."""
        for k in ("generic_ok", "occ_near_ok", "tolzero_exact", "wings_q0_theory"):
            lo, hi = DATA["rows"][k]["dO1_meV"]
            self.assertLessEqual(lo, 0.0, k)
            self.assertGreaterEqual(hi, 0.0, k)
            self.assertLess(hi - lo, 1e-5, k)

    def test_no_x_eq_w_and_no_clamp(self):
        for t in ("tally_X", "tally_L"):
            for c in ("occ_other", "occ_clampG", "occ_clampN"):
                self.assertEqual(DATA[t][c]["count"], 0, (t, c))

    def test_cor_linear(self):
        a, b = DATA["rows"]["COR_off"]["dO1_meV"], DATA["rows"]["COR_factor_1"]["dO1_meV"]
        self.assertAlmostEqual(a[0], -b[1], delta=1e-4)

    def test_drop_O_is_metric_rounding(self):
        """Every |I| >= TOL_Small, 0 < |Omega2| < TOL_Small mode has Omega2 = 0 exactly
        in the ideal fcc metric (its nonzero value comes from binary64 bdot)."""
        for t in ("tally_X", "tally_L"):
            self.assertEqual(DATA[t]["drop_O"]["count"],
                             DATA[t]["drop_O_ideal_metric_Omega2_zero"]["count"])


@functools.lru_cache(maxsize=None)
def fresh():
    d = pathlib.Path(tempfile.mkdtemp(prefix="bm-")) / "run"
    prod.run(d)
    return d


@unittest.skipUnless(HAVE_TREE, "pristine BerkeleyGW tree with epm2bgw.x not built")
class FreshRun(unittest.TestCase):
    def test_counts_and_baseline(self):
        m = M.Measure(fresh(), str(ROOT / "bgw/endpoint/data/coulomb_cert.json"))
        fc = M.float_counts(m)
        self.assertEqual(fc, DATA["float_cross_check"])
        base = dict(coul="avg", wings="spec", tolzero="spec")
        t = {}
        rL = m.state(m.run.kpts[1], [5], base, t)
        _, eL, _ = M.eqp1(rL)
        lo, hi = DATA["baseline"]["Eqp1_L"]
        self.assertLessEqual(max(float(eL.lo), lo), min(float(eL.hi), hi))
        for c in M.CLASSES:
            self.assertEqual(t[c]["count"], DATA["tally_L"][c]["count"], c)


if __name__ == "__main__":
    unittest.main()

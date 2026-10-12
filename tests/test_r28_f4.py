"""R28-F4: the static remainder that the spec's Sigma with all bands keeps
(GW/Bridge/CorResidual.lean; bgw/r28_f4/residual.py; docs/reviews/R28-F4.md).

Independent oracle. It uses numpy and fractions only, is written from the definitions
(BerkeleyGW's static CH term CSq with rho_aa and Gch, and the band terms ACq =
1/4 sum M_i v_i M_j IeU_ji), and never reads Lean output. It checks:

* the reviewer's two witnesses in exact rationals: complete bands with
  COR = -1/8, and (kappa - 1) I/4 under scaled closure;
* on random finite systems with CompleteK kappa: CSq + sum over all bands of ACq =
  scale + shift + Gch, and each term vanishes under its own condition, but not
  otherwise;
* the committed Si-EPM numbers `bgw/r28_f4/data/residual.json`: the decomposition
  equals the direct value; it agrees with the BRIDGE-COR file `cor.json` (2 COR -
  static tail = 2 CORall), which was computed separately; and the O1 effect follows
  from the linearised Eqp1.
"""
import importlib.util
import json
import pathlib
import unittest
from fractions import Fraction as Q

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
RES = json.loads((ROOT / "bgw/r28_f4/data/residual.json").read_text())
CORJ = json.loads((ROOT / "bgw/bridge_cor/data/cor.json").read_text())


def _load_residual():
    spec = importlib.util.spec_from_file_location("r28_residual_module", ROOT / "bgw/r28_f4/residual.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class IntervalSerialization(unittest.TestCase):
    def test_mev_is_outward_for_binary64_point(self):
        residual = _load_residual()
        x = residual.I.exact(0.1)
        lo, hi = residual.mev(x)
        exact = Q(0.1) * 1000
        self.assertLessEqual(Q(lo), exact)
        self.assertLessEqual(exact, Q(hi))
        self.assertGreater(hi, 100.0)

    def test_from_mev_to_mev_are_outward(self):
        """The module-level meV <-> eV conversions (used for O1_168, residual_removed and
        the lowdin block) contain the exact rational image of their input."""
        residual = _load_residual()
        for pair in ([-4.0424001883438985, -3.514062828664954], [0.1, 0.3], [-1e-3, 7.7]):
            v = residual.from_mev(pair)
            self.assertLessEqual(Q(float(v.lo)), Q(pair[0]) / 1000)
            self.assertLessEqual(Q(pair[1]) / 1000, Q(float(v.hi)))
            lo, hi = residual.to_mev(v)
            self.assertLessEqual(Q(lo), Q(float(v.lo)) * 1000)
            self.assertLessEqual(Q(float(v.hi)) * 1000, Q(hi))
        self.assertGreater(residual.to_mev(residual.I.exact(0.1))[1], 100.0)


# ----------------------------------------------------------------- the definitions

def pair_density(Gk, ca, Gq, cn, G):
    """M(G) = sum_{u, v: Gk_u - Gq_v = G} ca_u cn_v."""
    s = 0
    for u, gu in enumerate(Gk):
        for v, gv in enumerate(Gq):
            if tuple(np.subtract(gu, gv)) == tuple(G):
                s += ca[u] * cn[v]
    return s


def rho(Gk, ca, G):
    return pair_density(Gk, ca, Gk, ca, G)


def static_remainder(Gk, ca, Gq, bands, Gs, Ie, v, Gch, ts=0.0):
    """CSq + sum_n ACq over the given rows (computed and omitted together)."""
    n = len(Gs)
    IeU = [[Ie[j][i] if abs(Ie[j][i]) >= ts else 0 for i in range(n)] for j in range(n)]
    cs = 0
    for j in range(n):
        for i in range(n):
            d = tuple(np.subtract(Gs[j], Gs[i]))
            if IeU[j][i] != 0 and d in Gch:
                cs += -v[i] * IeU[j][i] * rho(Gk, ca, tuple(np.subtract(Gs[i], Gs[j]))) / 4
    ac = 0
    for row in bands:
        M = [pair_density(Gk, ca, Gq, row, g) for g in Gs]
        ac += sum(M[i] * v[i] * M[j] * IeU[j][i] for i in range(n) for j in range(n)) / 4
    return cs + ac


def three_terms(Gk, ca, Gq, Gs, Ie, v, Gch, kappa):
    n = len(Gs)
    A = [[sum(ca[u] for u, gu in enumerate(Gk) if tuple(np.subtract(gu, gq)) == tuple(g))
          for g in Gs] for gq in Gq]
    clo = [[sum(A[w][i] * A[w][j] for w in range(len(Gq))) for j in range(n)] for i in range(n)]
    w = [[v[i] * Ie[j][i] / 4 for i in range(n)] for j in range(n)]
    r = [[rho(Gk, ca, tuple(np.subtract(Gs[i], Gs[j]))) for j in range(n)] for i in range(n)]
    sc = (kappa - 1) * sum(w[j][i] * clo[i][j] for i in range(n) for j in range(n))
    sh = sum(w[j][i] * (clo[i][j] - r[i][j]) for i in range(n) for j in range(n))
    gc = sum(w[j][i] * r[i][j] for i in range(n) for j in range(n)
             if tuple(np.subtract(Gs[j], Gs[i])) not in Gch)
    return sc, sh, gc


class Witnesses(unittest.TestCase):
    def test_reviewer_complete_bands_cor_minus_eighth(self):
        Gk, ca = [(0, 0, 0)], [Q(1)]
        Gq, bands = [(0, 0, 0)], [[Q(1)]]                  # one band, complete
        Gs = [(0, 0, 0), (1, 0, 0)]
        Ie = [[Q(0), Q(0)], [Q(0), Q(1, 2)]]
        v = [Q(1), Q(1)]
        Gch = {(0, 0, 0)}
        cor = static_remainder(Gk, ca, Gq, bands, Gs, Ie, v, Gch)
        self.assertEqual(cor, Q(-1, 8))
        self.assertEqual(three_terms(Gk, ca, Gq, Gs, Ie, v, Gch, Q(1)), (0, Q(-1, 8), 0))

    def test_scaled_closure_kappa_minus_one(self):
        for I0 in (Q(1), Q(-3, 7)):
            for r in (Q(1, 3), Q(2)):
                kappa = 1 + r * r
                Gk = Gq = Gs = [(0, 0, 0)]
                cor = static_remainder(Gk, [Q(1)], Gq, [[Q(1)], [r]], Gs, [[I0]], [Q(1)],
                                       {(0, 0, 0)})
                self.assertEqual(cor, (kappa - 1) * I0 / 4)
                self.assertEqual(three_terms(Gk, [Q(1)], Gq, Gs, [[I0]], [Q(1)], {(0, 0, 0)}, kappa),
                                 ((kappa - 1) * I0 / 4, 0, 0))


def box(m):
    return [(a, b, c) for a in range(-m, m + 1) for b in range(-m, m + 1) for c in range(-m, m + 1)
            if a * a + b * b + c * c <= m * m]


class RandomSystems(unittest.TestCase):
    def system(self, rng, closed, kappa):
        Gk = box(1)
        ca = rng.normal(size=len(Gk))
        ca /= np.linalg.norm(ca)
        Gs = [(0, 0, 0), (1, 0, 0), (0, -1, 0), (1, 1, 0)]
        if closed:
            Gq = sorted({tuple(np.subtract(gu, g)) for gu in Gk for g in Gs})
        else:
            Gq = box(1)
        L = len(Gq)
        Qm, _ = np.linalg.qr(rng.normal(size=(L, L)))
        rows = list(Qm) + list(np.sqrt(kappa - 1.0) * np.eye(L))   # sum rows^T rows = kappa I
        n = len(Gs)
        Ie = rng.normal(size=(n, n))
        v = rng.uniform(0.5, 2.0, size=n)
        return Gk, ca, Gq, rows, Gs, Ie, v

    def test_decomposition_and_vanishing(self):
        rng = np.random.default_rng(7)
        for closed in (False, True):
            for kappa in (1.0, 1.3):
                Gk, ca, Gq, rows, Gs, Ie, v = self.system(rng, closed, kappa)
                diffs = {tuple(np.subtract(a, b)) for a in Gs for b in Gs}
                for Gch in ({(0, 0, 0)}, diffs):
                    tot = static_remainder(Gk, ca, Gq, rows, Gs, Ie, v, Gch)
                    sc, sh, gc = three_terms(Gk, ca, Gq, Gs, Ie, v, Gch, kappa)
                    self.assertAlmostEqual(tot, sc + sh + gc, delta=1e-12)
                    self.assertEqual(kappa == 1.0, abs(sc) < 1e-14)
                    self.assertEqual(closed, abs(sh) < 1e-12)
                    self.assertEqual(Gch == diffs, abs(gc) < 1e-14)
                    if kappa == 1.0 and closed and Gch == diffs:
                        self.assertAlmostEqual(tot, 0.0, delta=1e-12)
                    else:
                        self.assertGreater(abs(tot), 1e-6)

    def test_terms_do_not_depend_on_the_bands(self):
        """corShift, corGch use no band at k - q: a different complete band set gives the
        same total at kappa = 1 (so adding bands cannot remove them)."""
        rng = np.random.default_rng(8)
        Gk, ca, Gq, rows, Gs, Ie, v = self.system(rng, False, 1.0)
        rows2 = list(np.linalg.qr(rng.normal(size=(len(Gq), len(Gq))))[0])
        a = static_remainder(Gk, ca, Gq, rows[:len(Gq)], Gs, Ie, v, {(0, 0, 0)})
        b = static_remainder(Gk, ca, Gq, rows2, Gs, Ie, v, {(0, 0, 0)})
        self.assertAlmostEqual(a, b, delta=1e-12)
        self.assertGreater(abs(a), 1e-6)


def mid(x):
    return 0.5 * (x[0] + x[1])


class SiEPM(unittest.TestCase):
    def test_decomposition_equals_direct(self):
        for lab in ("X", "L"):
            for r in RES["per_band_meV"][lab]:
                d, s = r["CORall_direct18"], r["CORall_decomp18"]
                self.assertLessEqual(max(d[0], s[0]), min(d[1], s[1]) + 1e-12)
                self.assertAlmostEqual(mid(r["CORall_decomp168"]), mid(s), delta=1e-9)
                self.assertLess(abs(mid(r["scale18"])), 1e-9)
                self.assertLess(abs(mid(r["scale168"])), 1e-9)
                self.assertAlmostEqual(mid(r["shift168"]), mid(r["shift"]), delta=1e-9)

    def test_agrees_with_bridge_cor_bookkeeping(self):
        """cor.json (BRIDGE-COR) gives 2 COR and the finite-basis static tail; their
        difference is 2 CORall."""
        for lab in ("X", "L"):
            for r, b in zip(RES["per_band_meV"][lab], CORJ["per_band"][lab]):
                c2 = 1e3 * (mid(b["twice_COR_rho_closure_eV"]) - mid(b["static_tail_finite_basis_eV"]))
                self.assertAlmostEqual(c2 / 2, mid(r["CORall_decomp18"]), delta=1e-6)

    def test_sizes(self):
        X, L = RES["per_band_meV"]["X"], RES["per_band_meV"]["L"]
        for r in X:
            self.assertTrue(-2.3 < mid(r["shift"]) < -2.28 and 0.06 < mid(r["gch"]) < 0.07)
        self.assertTrue(-3.95 < mid(L[0]["shift"]) < -3.94 and 0.19 < mid(L[0]["gch"]) < 0.2)

    def test_o1_effect(self):
        for nb, src in (("18", CORJ["rows"]["baseline_COR_half"]), ("168", CORJ["all_bands"]["nb_168"])):
            e = RES["O1_effect"][nb]
            cX = np.mean([mid(r["CORall_decomp" + nb]) for r in RES["per_band_meV"]["X"]])
            cL = mid(RES["per_band_meV"]["L"][0]["CORall_decomp" + nb])
            dX, dL = mid(src["X"]["dSigma_dE"]), mid(src["L"]["dSigma_dE"])
            self.assertAlmostEqual(cX / (1 - dX) - cL / (1 - dL), mid(e["O1_contribution_meV"]), delta=1e-6)
            parts = e["O1_contribution_by_term_meV"]
            self.assertAlmostEqual(sum(mid(parts[k]) for k in parts), mid(e["O1_contribution_meV"]), delta=1e-6)
        a = RES["all_band_O1_meV"]
        com, rem = a["with_residual_as_committed"], a["residual_removed"]
        # containment, not equality: residual.py widens the committed meV pair outward
        # (meV -> eV -> meV), so a regenerated file differs from cor.json by ulps
        c168 = CORJ["all_bands"]["nb_168"]["O1_meV"]
        self.assertTrue(com[0] <= c168[0] and c168[1] <= com[1])
        # residual_removed contains the exact rational difference of the committed
        # cor.json enclosure and the committed O1 contribution. residual.py guarantees
        # rem ⊇ c168 - 1000·dO1 (eV, iv.py); the committed meV contribution d168 is itself
        # widened outward, so this check relies on from_mev's 2-ulp widening (slack about
        # 2e-15 meV), not on an exact identity.
        d168 = RES["O1_effect"]["168"]["O1_contribution_meV"]
        self.assertLessEqual(Q(rem[0]), Q(c168[0]) - Q(d168[1]))
        self.assertLessEqual(Q(c168[1]) - Q(d168[0]), Q(rem[1]))
        self.assertAlmostEqual(mid(com) - mid(rem), mid(RES["O1_effect"]["168"]["O1_contribution_meV"]), delta=1e-6)
        # removing the residual moves O1 outside the committed +-0.3 meV enclosure
        self.assertLess(rem[1], com[0])

    def test_o1_effect_lowdin(self):
        """R28-R2: the residual-free all-band O1 from R28-F3's Löwdin enclosure is that
        enclosure minus the shift + Gch part of CORall, taken with R28-F3's own dSigma/dE
        (corScale = 0 at kappa = 1). The result is outward, and the documented decimals
        [-5.25, -4.71] and [-5.2499, -4.7189] meV contain it."""
        f3 = json.loads((ROOT / "bgw/r28_f3/data/f3.json").read_text())
        lw = RES["all_band_O1_meV"]["lowdin"]
        # exact equality is safe here: residual.py copies this pair verbatim from f3.json
        self.assertEqual(lw["with_residual"], f3["all_bands_nb_168"]["O1_meV"])
        # the same shift + Gch per-state averages, recombined with F3's d (oracle, floats)
        cX = {k: np.mean([mid(r[k]) for r in RES["per_band_meV"]["X"]]) for k in ("shift168", "gch")}
        cL = {k: mid(RES["per_band_meV"]["L"][0][k]) for k in ("shift168", "gch")}
        dX, dL = mid(f3["all_bands_nb_168"]["X"]["dSigma_dE"]), mid(f3["all_bands_nb_168"]["L"]["dSigma_dE"])
        sg_mid = (cX["shift168"] + cX["gch"]) / (1 - dX) - (cL["shift168"] + cL["gch"]) / (1 - dL)
        sg = lw["residual_shift_plus_gch"]
        self.assertTrue(sg[0] <= sg_mid <= sg[1])
        lo, hi = lw["residual_removed"]
        self.assertLessEqual(lo, lw["with_residual"][0] - sg[1])
        self.assertGreaterEqual(hi, lw["with_residual"][1] - sg[0])
        self.assertTrue(-5.25 <= lo and hi <= -4.71)
        self.assertTrue(-5.2499 <= lo and hi <= -4.7189)


if __name__ == "__main__":
    unittest.main()

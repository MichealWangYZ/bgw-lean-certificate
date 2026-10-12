"""BRIDGE-COR: the proved enclosure of the omitted-band dynamic CH tail
(GW/Bridge/Cor.lean; bgw/bridge_cor/cor.py; docs/BRIDGE.md, last section).

Independent oracle: numpy only, written from the physics (the GPP empty-band term
A/(2w(x-w)), completeness of a band set, Cauchy-Schwarz), never reading Lean output.

* per-mode C1 statements on random modes;
* closure: on random finite complete band sets, sum_n M_n(G) M_n(G') equals
  sum_v A_v(G) A_v(G') with no shift-closure, and differs from rho_aa(G - G') when the
  k - q sphere is not shift-closed;
* the whole tail enclosure by brute force on random complete systems with random omitted
  energies >= D, including mixed-sign weights, invalid modes and the energy step; and a
  counterexample showing the uniform 1/2 is not implied (it falls outside the enclosure);
* the committed Si-EPM numbers `bgw/bridge_cor/data/cor.json`: the baseline equals the E1
  certificate, and the spec's all-band O1 (SigAall, residual CORall included; R28-F4) lies inside every enclosure.
"""
import importlib.util
import json
import pathlib
import unittest
from fractions import Fraction as Fr

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA_P = ROOT / "bgw/bridge_cor/data/cor.json"
CERT = json.loads((ROOT / "bgw/endpoint/data/cert_o1.json").read_text())


def _load_cor():
    spec = importlib.util.spec_from_file_location("bridge_cor_module", ROOT / "bgw/bridge_cor/cor.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class IntervalSerialization(unittest.TestCase):
    def test_mev_is_outward_for_binary64_point(self):
        cor = _load_cor()
        x = cor.I.exact(0.1)
        lo, hi = cor.mev(x)
        exact = Fr(0.1) * 1000
        self.assertLessEqual(Fr(lo), exact)
        self.assertLessEqual(exact, Fr(hi))
        self.assertGreater(hi, 100.0)  # old scalar multiplication returned [100, 100]

    # Radius reporting (R28-R3-CLOSEOUT item 1): the reported eV radius must bound
    # Fraction(r) * 13.60569253 (the decimal constant of Common/nrtype.f90) from above.
    RYD_DEC = Fr("13.60569253")
    TINY = float(np.nextafter(0.0, 1.0))

    @staticmethod
    def _old_radius_eV(cor, r):
        return r * cor.RYD_F * (1 + 1e-12)  # the padded scalar form removed by the closeout

    def _radii(self):
        return [0.0, 2 * self.TINY, self.TINY, 3 * self.TINY, 2.0 ** -1050, 2.0 ** -1023,
                2.2250738585072014e-308, 1e-300, 1e-17, 3.7e-9, 0.1, 1.0, 12.5, 1e6]

    def test_radius_eV_is_outward(self):
        cor = _load_cor()
        for r in self._radii():
            with self.subTest(r=r):
                self.assertLessEqual(Fr(r) * self.RYD_DEC, Fr(cor.radius_eV(r)))

    def test_old_padded_radius_was_inward_at_two_subnormals(self):
        cor = _load_cor()
        r = 2 * self.TINY
        old = self._old_radius_eV(cor, r)
        self.assertEqual(Fr(old) / Fr(self.TINY), 27)  # 27 s < 27.21138506 s: inward
        self.assertLess(Fr(old), Fr(r) * self.RYD_DEC)
        self.assertGreaterEqual(Fr(cor.radius_eV(r)), Fr(r) * self.RYD_DEC)

    def test_old_padded_radius_was_outward_in_normal_range(self):
        # Why the committed cor.json radii (all >= 9.9e-5 eV, produced by the old form)
        # stay valid upper bounds: for normal r the 1e-12 pad exceeds the three roundings.
        cor = _load_cor()
        rng = np.random.default_rng(0)
        rs = [2.0 ** -1022, 2.0 ** -1021 * 3, 1e-300, 7e-6, 1e-4, 0.11, 1.5968212349348354]
        rs += [float(x) for x in 10.0 ** rng.uniform(-307, 3, 2000)]
        for r in rs:
            self.assertLessEqual(Fr(r) * self.RYD_DEC, Fr(self._old_radius_eV(cor, r)), r)

    def test_committed_radii_are_in_the_normal_range(self):
        d = json.loads(DATA_P.read_text())
        vals = []

        def walk(x, k=""):
            if isinstance(x, dict):
                for kk, v in x.items():
                    walk(v, kk)
            elif isinstance(x, list):
                for v in x:
                    walk(v, k)
            elif k.startswith("radius") and k.endswith("eV"):
                vals.append(x)
        walk(d)
        self.assertEqual(len(vals), 30)
        self.assertGreater(min(vals), 1e-300)

    def test_reporting_sites_use_radius_eV(self):
        src = (ROOT / "bgw/bridge_cor/cor.py").read_text()
        self.assertNotIn("1e-12", src)
        self.assertEqual(src.count("radius_eV(tl[\"acc\"][kd][1])"), 1)
        self.assertEqual(src.count("radius_eV(t[\"acc\"][kind][1])"), 1)



def empty_term(A, x, w):
    return A / (2 * w * (x - w))


def theta(w, y):
    return w / (w + y)


def psi(w, D):
    return w / ((w + D - 1) * (w + D))


class OneMode(unittest.TestCase):
    def test_ratio_and_bounds(self):
        rng = np.random.default_rng(1)
        for _ in range(2000):
            I = rng.uniform(-2, 2)
            w = rng.uniform(0.1, 200.0)
            O = w * w * I
            D = rng.uniform(0.01, 100.0)
            x = -D - rng.exponential(50.0)
            dyn = empty_term(O, x, w)
            th = dyn / (-I / 2)
            self.assertAlmostEqual(th, w / (w - x), delta=1e-12 * max(1, th))
            self.assertGreater(th, 0)
            self.assertLessEqual(th, w / (w + D) * (1 + 1e-13))
            c, r = w / (w + D) / 2 * (-I / 2), w / (w + D) / 2 * abs(I) / 2
            self.assertLessEqual(abs(dyn - c), r * (1 + 1e-12) + 1e-300)
            self.assertLessEqual(abs(dyn), abs(I) / 2 * (1 + 1e-12))

    def test_no_positive_lower_bound_from_D(self):
        """theta -> 0 as the omitted band goes up: D alone gives no theta_lo > 0."""
        w, D = 20.0, 30.0
        ths = [theta(w, y) for y in (D, 1e2, 1e4, 1e8)]
        self.assertTrue(all(a > b for a, b in zip(ths, ths[1:])))
        self.assertLess(ths[-1], 1e-6)

    def test_bgw_rule_invalid_mode_is_static_limit(self):
        """Invalid mode, BerkeleyGW rule w = 1e12: generic branch, 1/2 CH = theta (-I/2)
        with theta = 1e12/(1e12 - x) ~ 1 for realistic omitted energies."""
        W, I = 1e12, 0.3
        for x in (-2.0, -30.0, -150.0):
            d = x - W
            self.assertTrue(d * d > 0.25 and W * W < d * d * 250000)
            half_ch = 0.5 * W * I / (x - W)
            self.assertAlmostEqual(half_ch / (-I / 2), W / (W - x), places=12)

    def test_energy_step(self):
        rng = np.random.default_rng(2)
        for _ in range(1000):
            I = rng.uniform(-2, 2)
            w = rng.uniform(0.1, 200.0)
            D = rng.uniform(1.01, 80.0)
            x = -D - rng.exponential(40.0)
            step = empty_term(w * w * I, x + 1, w) - empty_term(w * w * I, x, w)
            p = psi(w, D)
            self.assertLessEqual(abs(step - p / 2 * (-I / 2)), p / 2 * abs(I) / 2 * (1 + 1e-10) + 1e-15)


def random_system(rng, nk=9, nq=11, ns=5, span=2, shift_closed=False):
    """Random integer G-vectors: state `a` on Gk, a complete orthonormal band set on Gq,
    `ns` sphere vectors G_i. Returns the pieces for M_n(G) = sum c_a(u) C_n(v)."""
    def vecs(n):
        out = set()
        while len(out) < n:
            out.add(tuple(rng.integers(-span, span + 1, size=3)))
        return [np.array(v) for v in out]
    Gk = vecs(nk)
    Gs = vecs(ns)
    if shift_closed:
        Gq = list({tuple(g - s) for g in Gk for s in Gs})
        Gq = [np.array(v) for v in Gq]
    else:
        Gq = vecs(nq)
    ca = rng.normal(size=len(Gk))
    ca /= np.linalg.norm(ca)
    C, _ = np.linalg.qr(rng.normal(size=(len(Gq), len(Gq))))   # rows = bands, complete
    Gk_idx = {tuple(g): u for u, g in enumerate(Gk)}
    A = np.zeros((len(Gq), ns))
    for v, g2 in enumerate(Gq):
        for i, g in enumerate(Gs):
            u = Gk_idx.get(tuple(g2 + g))
            if u is not None:
                A[v, i] = ca[u]
    M = C @ A          # M[n, i] = sum_v C[n, v] A[v, i]
    return Gk, Gq, Gs, ca, C, A, M


def rho(Gk, ca, G):
    idx = {tuple(g): u for u, g in enumerate(Gk)}
    return sum(ca[u] * ca[idx[tuple(g - G)]] for u, g in enumerate(Gk) if tuple(g - G) in idx)


class Closure(unittest.TestCase):
    def test_pd_closure_amp(self):
        rng = np.random.default_rng(3)
        for sc in (False, True):
            for _ in range(20):
                Gk, Gq, Gs, ca, C, A, M = random_system(rng, shift_closed=sc)
                # M from the definition (sum over u, v with Gk_u - Gq_v = G)
                Md = np.zeros_like(M)
                for n in range(len(Gq)):
                    for i, G in enumerate(Gs):
                        Md[n, i] = sum(ca[u] * C[n, v] for u, gk in enumerate(Gk)
                                       for v, gq in enumerate(Gq) if np.all(gk - gq == G))
                np.testing.assert_allclose(Md, M, atol=1e-13)
                np.testing.assert_allclose(M.T @ M, A.T @ A, atol=1e-12)
                R = np.array([[rho(Gk, ca, Gi - Gj) for Gj in Gs] for Gi in Gs])
                if sc:
                    np.testing.assert_allclose(A.T @ A, R, atol=1e-12)

    def test_rho_closure_needs_shift_closure(self):
        rng = np.random.default_rng(4)
        worst = 0.0
        for _ in range(20):
            Gk, Gq, Gs, ca, C, A, M = random_system(rng, shift_closed=False)
            R = np.array([[rho(Gk, ca, Gi - Gj) for Gj in Gs] for Gi in Gs])
            worst = max(worst, np.abs(A.T @ A - R).max())
        self.assertGreater(worst, 1e-2)


def tail_enclosure(M, nb, v, Iq, Oq, D, kind="thK"):
    """Centre and radius of Cor.lean's enclosure (index [j, i] for the mode kernel)."""
    T = (M[nb:].T @ M[nb:])                 # the true omitted pair sums ...
    ns = len(v)
    cen = rad = 0.0
    sd = np.sqrt(np.clip(np.diag(T), 0, None))
    for i in range(ns):
        for j in range(ns):
            I, O = Iq[j, i], Oq[j, i]
            if O / I > 0:
                w = np.sqrt(O / I)
                f = theta(w, D) if kind == "thK" else psi(w, D)
                c, r = f / 2 * (-I / 2), f / 2 * abs(I) / 2
            else:
                c = r = 0.0
            cen += v[i] * T[i, j] * c
            rad += abs(v[i]) * sd[i] * sd[j] * r
    return cen, rad, T


def thK(I, O, x):
    return empty_term(O, x, np.sqrt(O / I)) if O / I > 0 else 0.0


class TailEnclosure(unittest.TestCase):
    def test_brute_force(self):
        rng = np.random.default_rng(5)
        n_inside = 0
        for trial in range(60):
            Gk, Gq, Gs, ca, C, A, M = random_system(rng, nk=12, nq=14, ns=6)
            nb = int(rng.integers(1, len(Gq) - 2))
            ns = len(Gs)
            v = rng.uniform(0.1, 3.0, size=ns)
            Iq = rng.normal(scale=0.5, size=(ns, ns))
            Oq = np.abs(rng.normal(scale=200, size=(ns, ns))) * np.sign(Iq)
            Oq[rng.random((ns, ns)) < 0.3] *= -1          # invalid modes (O/I < 0)
            D = rng.uniform(1.5, 40.0)
            y = D + rng.exponential(rng.uniform(1, 200), size=len(Gq))
            y[nb] = D                                      # the lowest omitted band at D
            for kind in ("thK", "step"):
                true = 0.0
                for n in range(nb, len(Gq)):
                    for i in range(ns):
                        for j in range(ns):
                            if kind == "thK":
                                k = thK(Iq[j, i], Oq[j, i], -y[n])
                            else:
                                k = thK(Iq[j, i], Oq[j, i], -y[n] + 1) - thK(Iq[j, i], Oq[j, i], -y[n])
                            true += M[n, i] * v[i] * M[n, j] * k
                cen, rad, T = tail_enclosure(M, nb, v, Iq, Oq, D, kind)
                # the omitted pair sums are computable from completeness
                np.testing.assert_allclose(T, A.T @ A - M[:nb].T @ M[:nb], atol=1e-12)
                self.assertLessEqual(abs(true - cen), rad * (1 + 1e-9) + 1e-14)
                n_inside += 1
        self.assertEqual(n_inside, 120)

    def test_half_is_not_implied(self):
        """All omitted bands far above (D >> w): the true tail is tiny, the enclosure is
        tight around it, and the uniform-1/2 static remainder lies OUTSIDE."""
        rng = np.random.default_rng(6)
        Gk, Gq, Gs, ca, C, A, M = random_system(rng, nk=12, nq=14, ns=6)
        ns, nb = len(Gs), 3
        v = np.ones(ns)
        B = rng.normal(size=(ns, ns))
        Iq = B @ B.T / ns + np.eye(ns) * 0.1            # positive definite: static tail < 0
        Oq = Iq * 25.0 ** 2                             # every mode valid, w = 25
        D = 2000.0
        cen, rad, T = tail_enclosure(M, nb, v, Iq, Oq, D)
        static = sum(v[i] * T[i, j] * (-Iq[j, i] / 2) for i in range(ns) for j in range(ns))
        self.assertLess(static, 0)
        self.assertGreater(abs(0.5 * static - cen), rad)


@unittest.skipUnless(DATA_P.is_file(), "no committed cor.json")
class SiEPM(unittest.TestCase):
    D = json.loads(DATA_P.read_text()) if DATA_P.is_file() else None

    def test_baseline_is_certificate(self):
        lo, hi = self.D["rows"]["baseline_COR_half"]["O1_meV"]
        self.assertLessEqual(CERT["O1_lo"] * 1e3 - 1e-6, lo)
        self.assertLessEqual(hi, CERT["O1_hi"] * 1e3 + 1e-6)
        self.assertAlmostEqual(0.5 * (lo + hi), 15.4058, places=3)

    def test_heuristic_half_inside_rigorous(self):
        lo, hi = self.D["rows"]["spec_rule_tail"]["O1_meV"]
        blo, bhi = self.D["rows"]["baseline_COR_half"]["O1_meV"]
        self.assertTrue(lo <= blo and bhi <= hi)

    def test_uniform_theta_family_is_linearish(self):
        fam = self.D["rows"]["uniform_theta_O1_meV"]
        m = {float(k): 0.5 * (v[0] + v[1]) for k, v in fam.items()}
        self.assertAlmostEqual(m[0.5], 15.4058, places=3)
        self.assertLess(m[0.0], 0)
        self.assertGreater(m[1.0], m[0.5])

    @unittest.skipUnless(DATA_P.is_file() and "bgw_cross_check" in
                         json.loads(DATA_P.read_text()).get("all_bands", {}), "no BGW cross-check")
    def test_added_bands_match_berkeleygw(self):
        """SigA with 164 bands here vs BerkeleyGW's own Sigma run with number_bands 164:
        agreement at the E1 level (5.2 ueV for the 18-band run)."""
        x = self.D["all_bands"]["bgw_cross_check"]
        lo, hi = x["O1_here_meV"]
        self.assertLess(abs(0.5 * (lo + hi) - x["O1_BerkeleyGW_sigma_hp_meV"]), 0.01)

    @unittest.skipUnless(DATA_P.is_file() and "all_bands" in json.loads(DATA_P.read_text()),
                         "no all-band diagnostic")
    def test_exact_all_band_inside_every_enclosure(self):
        ab = self.D["all_bands"]
        tlo, thi = ab["nb_168"]["O1_meV"]
        self.assertLess(thi - tlo, 1.0)            # the all-band value is sharp
        for key in (k for k in ab if k.startswith("nb_") and not k.endswith("_theory_kernel")):
            lo, hi = ab[key]["O1_meV"]
            self.assertTrue(lo <= tlo and thi <= hi, key)
        lo18, hi18 = self.D["rows"]["spec_rule_tail"]["O1_meV"]
        self.assertTrue(lo18 <= tlo and thi <= hi18)
        # the same with the theory kernel on the omitted bands
        tlo, thi = ab["nb_168_theory_kernel"]["O1_meV"]
        lo, hi = self.D["rows"]["theory_kernel_tail"]["O1_meV"]
        self.assertTrue(lo <= tlo and thi <= hi)
        widths = [ab[f"nb_{n}"]["O1_meV"][1] - ab[f"nb_{n}"]["O1_meV"][0] for n in (18, 30, 60, 100)]
        self.assertTrue(all(a > b for a, b in zip(widths, widths[1:])))


if __name__ == "__main__":
    unittest.main()

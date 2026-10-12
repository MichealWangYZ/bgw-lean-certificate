#!/usr/bin/env python3
"""BRIDGE: independent numerical oracle for the theory-to-BerkeleyGW bridge.

Nothing here reads Lean output or the project's BerkeleyGW transcriptions
(`bgw/endpoint/cert.py`, `spec.py`). Every check recomputes the physics from
its textbook definition with numpy on random small instances:

* B1  the damped Fourier transform of i G0(tau) W_c(tau), integrated
      numerically on a grid, against the closed form of `GW/Bridge/FreqIntegral`
      (and the eta -> 0 limit), and the HL SX + CH rewriting;
* B2  the HL plasmon-pole model: static value, f-sum tail, Kramers-Kronig
      consistency of its spectral weight, the validity criterion by brute
      force, and the w -> infinity (invalid-mode) static limit;
* B3  pair-density closure with a complete orthonormal band set, and its
      failure with a truncated one;
* B4  BerkeleyGW's per-mode GPP kernel re-implemented from the Fortran
      branch logic in IEEE binary64 (numpy, NaN semantics included) against
      the theory kernel: equal in the generic and occupied near-pole branches,
      and the x = wtilde point where IEEE gives 0 and theory gives I/4.

These are numerical experiments; they are evidence for, not proofs of, the
Lean statements.
"""

import unittest

import numpy as np

RNG = np.random.default_rng(20260929)


# ---------------------------------------------------------------- B1 -------
def g0(tau, eps, f):
    """Time-ordered T=0 G0_n(tau) = -i[theta(tau)(1-f) - theta(-tau) f] e^{-i eps tau}."""
    step = np.where(tau > 0, 1.0 - f, -f)
    return -1j * step * np.exp(-1j * eps * tau)


def wc(tau, R, w):
    """Time-ordered pole sum W_c(tau) = sum_k -i R_k e^{-i w_k |tau|}."""
    return sum(-1j * Rk * np.exp(-1j * wk * np.abs(tau)) for Rk, wk in zip(R, w))


def damped_ft(fun, E, eta, T=None, dt=2e-3):
    """int e^{i E tau - eta |tau|} fun(tau) d tau, trapezoid on each half line."""
    if T is None:
        T = 36.0 / eta
    n = int(T / dt)
    tp = np.linspace(0.0, T, n + 1)
    tp[0] = 1e-300  # right limit at 0
    tm = -np.linspace(0.0, T, n + 1)  # left side, value at 0 from the left
    fp = np.exp(1j * E * tp - eta * tp) * fun(tp)
    fm = np.exp(1j * E * tm - eta * np.abs(tm)) * fun(tm)
    return np.trapezoid(fp, tp) + np.trapezoid(fm[::-1], tm[::-1])


def random_system(no=3, npole=2):
    eps = np.sort(RNG.uniform(-3, 3, no))
    f = (np.arange(no) < no // 2 + 1).astype(float)
    R = RNG.uniform(-1, 1, (no, npole))
    w = RNG.uniform(0.5, 2.5, (no, npole))
    return eps, f, R, w


def sigma_time(tau, eps, f, R, w):
    return 1j * sum(g0(tau, eps[n], f[n]) * wc(tau, R[n], w[n]) for n in range(len(eps)))


def closed_form(E, eps, f, R, w, eta=0.0):
    """B1 closed form; at eta > 0 the exact damped value (poles shifted by -+ i eta)."""
    s = 0.0
    for n in range(len(eps)):
        for k in range(R.shape[1]):
            s += R[n, k] * (f[n] / (E - eps[n] + w[n, k] - 1j * eta)
                            + (1 - f[n]) / (E - eps[n] - w[n, k] + 1j * eta))
    return s


class B1FrequencyIntegral(unittest.TestCase):
    def test_damped_transform_matches_closed_form(self):
        for _ in range(3):
            eps, f, R, w = random_system()
            E = RNG.uniform(-1, 1)
            for eta in (0.2, 0.05):
                num = damped_ft(lambda t: sigma_time(t, eps, f, R, w), E, eta)
                ref = closed_form(E, eps, f, R, w, eta)
                self.assertLess(abs(num - ref), 2e-4 * max(1, abs(ref)))

    def test_limit_signs(self):
        """eta -> 0: occupied poles at E = eps - w, empty at E = eps + w, residue +R."""
        eps, f, R, w = random_system()
        poles = np.concatenate([(eps[:, None] - w)[f == 1].ravel(), (eps[:, None] + w)[f == 0].ravel()])
        grid = np.linspace(-6, 6, 12001)
        E = grid[np.argmax(np.min(np.abs(grid[:, None] - poles[None, :]), axis=1))]
        vals = [closed_form(E, eps, f, R, w, eta) for eta in (1e-3, 1e-5)]
        lim = closed_form(E, eps, f, R, w, 0.0)
        self.assertLess(abs(vals[-1] - lim), 1e-3)
        # a wrong-sign variant (occupied at eps + w) is far away
        wrong = sum(R[n, k] / (E - eps[n] - w[n, k]) for n in range(len(eps)) for k in range(2))
        self.assertGreater(abs(wrong - lim), 1e-3)

    def test_wc_transform_is_gpp_form(self):
        R, w = RNG.uniform(-1, 1, 2), RNG.uniform(0.5, 2, 2)
        om, eta = 0.37, 0.05
        num = damped_ft(lambda t: wc(t, R, w), om, eta)
        ref = sum(Rk * (1 / (om - wk + 1j * eta) - 1 / (om + wk - 1j * eta)) for Rk, wk in zip(R, w))
        self.assertLess(abs(num - ref), 2e-4)
        lim = sum(Rk * 2 * wk / (om ** 2 - wk ** 2) for Rk, wk in zip(R, w))
        self.assertLess(abs(ref - lim), 0.2)  # O(eta)

    def test_hl_rewriting(self):
        for _ in range(20):
            eps, f, R, w = random_system()
            E = RNG.uniform(-4, 4)
            A = 2 * w * R
            x = E - eps[:, None]
            sx = sum((-A[n] / (x[n] ** 2 - w[n] ** 2)).sum() for n in range(len(eps)) if f[n] == 1)
            ch = (A / (2 * w * (x - w))).sum()
            ref = closed_form(E, eps, f, R, w).real
            self.assertAlmostEqual(sx + ch, ref, delta=1e-7 * (1 + abs(ref)))


# ---------------------------------------------------------------- B2 -------
def gpp(I, O, om):
    """HL correlation part eps^-1(om) - delta = O / (om^2 - O/I)."""
    return O / (om ** 2 - O / I)


class B2PlasmonPole(unittest.TestCase):
    def test_static_and_tail(self):
        for _ in range(20):
            I, O = RNG.uniform(0.05, 1), RNG.uniform(0.1, 5)
            self.assertAlmostEqual(gpp(I, O, 0.0), -I, places=12)
            big = 1e6
            self.assertAlmostEqual(big ** 2 * gpp(I, O, big) / O, 1.0, places=6)

    def test_kramers_kronig_fsum(self):
        """Broadened spectral weight -pi R [d(om-w) - d(om+w)], R = O/(2w): KK gives the
        real part O/(om^2 - w^2), and the first moment is -(pi/2) O."""
        I, O = 0.4, 2.0
        w = np.sqrt(O / I)
        R = O / (2 * w)
        sig = 0.01
        om = np.linspace(0, 10 * w, 400001)
        gauss = lambda x: np.exp(-x ** 2 / (2 * sig ** 2)) / np.sqrt(2 * np.pi * sig ** 2)
        im = -np.pi * R * (gauss(om - w) - gauss(om + w))
        moment = np.trapezoid(om * im, om)
        self.assertAlmostEqual(moment / (-(np.pi / 2) * O), 1.0, places=4)
        for om0 in (0.3 * w, 2.5 * w):
            den = om ** 2 - om0 ** 2
            integrand = np.where(np.abs(den) > 1e-12, om * im / np.where(den == 0, 1, den), 0.0)
            kk = (2 / np.pi) * np.trapezoid(integrand, om)
            self.assertAlmostEqual(kk / gpp(I, O, om0), 1.0, places=3)

    def test_validity_criterion_brute_force(self):
        """A pole R 2w/(om^2-w^2), w>0, with static -I and tail O exists iff
        (I = O = 0) or O/I > 0: from static 2R/w = I and tail 2Rw = O."""
        ws = np.geomspace(1e-6, 1e3, 20001)
        for I, O, expect in [(0.5, 1.0, True), (-0.5, -1.0, True), (0.5, -1.0, False),
                             (-0.5, 1.0, False), (0.0, 1.0, False), (0.5, 0.0, False),
                             (0.0, 0.0, True)]:
            g = I * ws ** 2 - O  # (2Rw - O) after the static match R = I w / 2
            found = bool(np.all(g == 0) or np.any(np.sign(g[:-1]) * np.sign(g[1:]) < 0))
            self.assertEqual(found, expect, (I, O))
            self.assertEqual(expect, (I == 0 and O == 0) or (I != 0 and O / I > 0))

    def test_invalid_mode_static_limit(self):
        I, x = 0.3, 0.7
        for w in (1e6, 1e12):
            self.assertAlmostEqual(w * I / (x - w), -I, places=5)
            self.assertAlmostEqual(w ** 2 * I / (x ** 2 - w ** 2), -I, places=5)
            self.assertAlmostEqual(abs(w * I / (x - w) + I), abs(I) * abs(x) / abs(w - x),
                                   delta=1e-15)


# ---------------------------------------------------------------- B3 -------
def pair_density(Gk, ca, Gq, cn, G):
    return sum(ca[u] * cn[v] for u in range(len(Gk)) for v in range(len(Gq))
               if Gk[u] - Gq[v] == G)


class B3Closure(unittest.TestCase):
    def setUp(self):
        self.Gk = list(range(-2, 3))
        self.Gq = list(range(-6, 7))
        self.ca = RNG.normal(size=len(self.Gk))
        Q, _ = np.linalg.qr(RNG.normal(size=(len(self.Gq), len(self.Gq))))
        self.C = Q  # rows = bands, orthonormal and complete

    def rho(self, G):
        return pair_density(self.Gk, self.ca, self.Gk, self.ca, G)

    def test_complete_closure(self):
        for G in range(-2, 3):
            for Gp in range(-2, 3):
                s = sum(pair_density(self.Gk, self.ca, self.Gq, self.C[n], G)
                        * pair_density(self.Gk, self.ca, self.Gq, self.C[n], Gp)
                        for n in range(len(self.Gq)))
                self.assertAlmostEqual(s, self.rho(G - Gp), places=10)
                self.assertAlmostEqual(self.rho(G - Gp), self.rho(Gp - G), places=12)

    def test_truncated_bands_break_closure(self):
        nb = 4
        G, Gp = 1, -1
        s = sum(pair_density(self.Gk, self.ca, self.Gq, self.C[n], G)
                * pair_density(self.Gk, self.ca, self.Gq, self.C[n], Gp) for n in range(nb))
        self.assertGreater(abs(s - self.rho(G - Gp)), 1e-6)


# ---------------------------------------------------------------- B4 -------
LIMITTWO, LIMITONE, TOL_ZERO, SEXCUT = 0.25, 250000.0, 1e-12, 4.0


def bgw_mode(I, wt, x, occ):
    """BerkeleyGW 4.0 real-flavour GPP kernel of one kept, valid mode, written from the
    Fortran branch logic in binary64: returns CH/2 - [occ] SX per unit weight."""
    with np.errstate(divide="ignore", invalid="ignore"):
        I, wt, x = np.float64(I), np.float64(wt), np.float64(x)
        cden = x - wt
        rden = np.float64(1.0) / (cden * cden)
        delw = wt * cden * rden
        delwr = delw * delw
        wdiffr = cden * cden
        Omega2 = wt * wt * I
        if wdiffr > LIMITTWO and delwr < LIMITONE:
            sch = delw * I
            ssx = Omega2 / (x * x - wt * wt)
        elif delwr > TOL_ZERO:
            sch = np.float64(0.0)
            ssx = -Omega2 * delw / (4 * wt * wt * (delw + 0.5))
        else:
            sch = np.float64(0.0)
            ssx = np.float64(0.0)
        if abs(ssx) > SEXCUT * abs(I) and x < 0:
            ssx = np.float64(0.0)
    return 0.5 * sch - (ssx if occ else 0.0)


def theory_mode(I, wt, x, occ):
    O = wt * wt * I
    return O / (2 * wt * (x + wt)) if occ else O / (2 * wt * (x - wt))


class B4Kernel(unittest.TestCase):
    def test_generic_branch_equal(self):
        n = 0
        while n < 200:
            I, wt, x = RNG.uniform(-1, 1), RNG.uniform(0.5, 30), RNG.uniform(-60, 60)
            if (x - wt) ** 2 <= LIMITTWO or wt ** 2 >= (x - wt) ** 2 * LIMITONE:
                continue
            clamp = abs(x * x - wt * wt) < wt * wt / SEXCUT and x < 0
            for occ in (False, True):
                if occ and clamp:
                    continue
                self.assertAlmostEqual(bgw_mode(I, wt, x, occ), theory_mode(I, wt, x, occ),
                                       delta=1e-9 * (1 + abs(theory_mode(I, wt, x, occ))))
            n += 1

    def test_occupied_near_pole_equal(self):
        for _ in range(200):
            I, wt = RNG.uniform(-1, 1), RNG.uniform(1, 30)
            x = wt + RNG.uniform(-0.5, 0.5)
            if x == wt:
                continue
            self.assertAlmostEqual(bgw_mode(I, wt, x, True), theory_mode(I, wt, x, True),
                                   delta=1e-9)

    def test_empty_near_pole_dropped(self):
        I, wt = 0.4, 3.0
        x = wt + 0.2
        self.assertEqual(bgw_mode(I, wt, x, False), 0.0)
        self.assertNotAlmostEqual(theory_mode(I, wt, x, False), 0.0)

    def test_x_equals_wtilde_discrepancy(self):
        """IEEE binary64: delw = NaN at x = wtilde, both branch tests fail, SX = CH = 0.
        Theory: the removable-singularity value I/4."""
        for I, wt in [(1.0, 1.0), (0.3, 7.25), (-0.8, 2.5)]:
            self.assertEqual(bgw_mode(I, wt, wt, True), 0.0)
            self.assertAlmostEqual(theory_mode(I, wt, wt, True), I / 4, places=12)
            # one ulp away the source already agrees with the theory
            xn = np.nextafter(wt, np.inf)
            self.assertAlmostEqual(bgw_mode(I, wt, xn, True), I / 4, delta=1e-9)

    def test_generic_clamp_keeps_ch(self):
        I, wt = 0.5, 3.0
        x = -wt + 0.1  # near the hole pole, x < 0, generic branch
        self.assertTrue(abs(x * x - wt * wt) < wt * wt / SEXCUT)
        self.assertAlmostEqual(bgw_mode(I, wt, x, True), 0.5 * wt * I / (x - wt), places=12)

    def test_static_remainder_factor(self):
        """COR = CSq + sum ACq with CSq = (1/4) sum rho v (eps - 1) and ACq = -(1/4) M v (-I) M:
        with complete bands COR = 0; truncated, COR = (1/2)(exact - partial)."""
        c = B3Closure()
        c.setUp()
        v = RNG.uniform(0.1, 1, 5)
        Gs = list(range(-2, 3))
        epsm = np.eye(5) - RNG.uniform(0, 0.3, (5, 5))
        exact = 0.5 * sum(v[i] * c.rho(Gs[i] - Gs[j]) * (epsm[j, i] - (i == j))
                          for i in range(5) for j in range(5))

        def partial(nb):
            s = 0.0
            for n in range(nb):
                M = [pair_density(c.Gk, c.ca, c.Gq, c.C[n], G) for G in Gs]
                s += 0.5 * sum(M[i] * v[i] * M[j] * (epsm[j, i] - (i == j))
                               for i in range(5) for j in range(5))
            return s

        full = partial(len(c.Gq))
        self.assertAlmostEqual(full, exact, places=10)
        cor_full = 0.5 * exact - 0.5 * full
        self.assertAlmostEqual(cor_full, 0.0, places=10)
        p4 = partial(4)
        self.assertGreater(abs(0.5 * (exact - p4)), 1e-6)


if __name__ == "__main__":
    unittest.main()

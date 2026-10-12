#!/usr/bin/env python3
"""BRIDGE-EPS: independent numerical oracle for the static RPA dielectric matrix.

Nothing here reads Lean output or the project's BerkeleyGW transcriptions
(`bgw/endpoint/cert.py`, `spec.py`). Every check recomputes the physics from
its textbook definition with numpy:

* E1  the damped Fourier transform of chi0(tau) = -i G0(tau) G0(-tau), integrated
      numerically on a time grid, against the closed form; and the static closed form
      against a finite-difference static density response of a non-interacting system
      (first-order perturbation theory never appears);
* E2  a 1D crystal (Ry units, H = -d^2/dx^2 + V(x), V even), an N_k-cell
      Born-von Karman supercell: chi(q+G, q+G') from the finite-difference density
      response of the SUPERCELL to a static cosine perturbation (spin 2), against the
      Bloch formula 4/(N_k Omega) sum_k sum_v sum_c M M / (E_v(k+q) - E_c(k)) with real
      plane-wave coefficients; the factor 2 and the (v at k, c at k+q) convention fail;
* E3  eps = 1 - v chi, W = eps^-1 v: Dyson, exact Neumann remainder, symmetrised
      form, symmetry of W, and the omega -> 0 limit of the dynamic W;
* E4  the whole chain on the 1D crystal: EpsSpec-style eps and eps^-1 against the
      supercell-response eps and eps^-1.

These are numerical experiments; they are evidence for, not proofs of, the Lean
statements.
"""

import unittest

import numpy as np

RNG = np.random.default_rng(20260929)


# ---------------------------------------------------------------- E1 -------
def g0(tau, eps, f):
    step = np.where(tau > 0, 1.0 - f, -f)
    return -1j * step * np.exp(-1j * eps * tau)


def damped_ft(fun, om, eta, dt=2e-3):
    T = 40.0 / eta
    n = int(T / dt)
    tp = np.linspace(0.0, T, n + 1)
    tp[0] = 1e-300
    tm = -np.linspace(0.0, T, n + 1)
    fp = np.exp(1j * om * tp - eta * tp) * fun(tp)
    fm = np.exp(1j * om * tm - eta * np.abs(tm)) * fun(tm)
    return np.trapezoid(fp, tp) + np.trapezoid(fm[::-1], tm[::-1])


def random_orbital_system(nb=6, nocc=3):
    """Real orthonormal orbitals on nb sites (eigenvectors of a random real H)."""
    A = RNG.normal(size=(nb, nb))
    H = (A + A.T) / 2
    e, phi = np.linalg.eigh(H)
    return H, e, phi, nocc


def pair_amp(phi, g):
    """P[m, m'] = <g | phi_m' phi_m> = sum_r g(r) phi_m'(r) phi_m(r)."""
    return np.einsum("r,rm,rn->mn", g, phi, phi)


def chi_static_closed(e, phi, nocc, g, gp):
    Pg, Pgp = pair_amp(phi, g), pair_amp(phi, gp)
    s = 0.0
    for v in range(nocc):
        for c in range(nocc, len(e)):
            s += (Pg[c, v] * Pgp[c, v] + Pg[v, c] * Pgp[v, c]) / (e[v] - e[c])
    return s


class E1Chi0FromG0(unittest.TestCase):
    def test_damped_transform_limit(self):
        _, e, phi, nocc = random_orbital_system(nb=4, nocc=2)
        f = (np.arange(len(e)) < nocc).astype(float)
        g, gp = RNG.normal(size=4), RNG.normal(size=4)
        Pg, Pgp = pair_amp(phi, g), pair_amp(phi, gp)

        def chi_tau(t):
            out = 0.0
            for m in range(len(e)):
                for mp in range(len(e)):
                    w = Pg[m, mp] * Pgp[m, mp]
                    if w != 0.0:
                        out = out + w * (-1j) * g0(t, e[m], f[m]) * g0(-t, e[mp], f[mp])
            return out

        for om in (0.0, 0.123):
            vals = [damped_ft(chi_tau, om, eta) for eta in (0.04, 0.02)]
            extrap = 2 * vals[1] - vals[0]  # O(eta) Richardson
            ref = sum(Pg[m, mp] * Pgp[m, mp] * ((1 - f[m]) * f[mp] - f[m] * (1 - f[mp]))
                      / (om - (e[m] - e[mp])) for m in range(4) for mp in range(4) if f[m] != f[mp])
            self.assertLess(abs(extrap - ref), 2e-3 * max(1.0, abs(ref)))
            if om == 0.0:
                self.assertAlmostEqual(ref, chi_static_closed(e, phi, nocc, g, gp), places=10)

    def test_static_response_by_finite_differences(self):
        """chi(g, g') = d/dlam <g | n_lam> with H = H0 + lam diag(g'), n = sum_occ phi^2."""
        for _ in range(5):
            H, e, phi, nocc = random_orbital_system()
            g, gp = RNG.normal(size=len(e)), RNG.normal(size=len(e))

            def dens(lam):
                _, ph = np.linalg.eigh(H + lam * np.diag(gp))
                return (ph[:, :nocc] ** 2).sum(axis=1)

            lam = 1e-5
            fd = g @ (dens(lam) - dens(-lam)) / (2 * lam)
            ref = chi_static_closed(e, phi, nocc, g, gp)
            self.assertAlmostEqual(fd, ref, delta=1e-6 * max(1.0, abs(ref)))
            # both time orderings are needed: a single ordering is half
            one = sum(pair_amp(phi, g)[v, c] * pair_amp(phi, gp)[v, c] / (e[v] - e[c])
                      for v in range(nocc) for c in range(nocc, len(e)))
            self.assertGreater(abs(fd - one), 1e-3 * abs(fd))
            self.assertLessEqual(chi_static_closed(e, phi, nocc, g, g), 0.0)


# ---------------------------------------------------------------- E2 -------
class Crystal1D:
    """H = -d^2/dx^2 + sum_n 2 V_n cos(n x), a = 2 pi (RL vectors are integers), Ry."""

    def __init__(self, Nk=4, Kc=6.0, V=(0.0, 0.6, 0.8), nv=2):
        self.Nk, self.Kc, self.V, self.nv = Nk, Kc, V, nv
        self.a = 2 * np.pi
        self.Om = self.a

    def vG(self, d):
        d = int(round(d))
        return self.V[abs(d)] if 0 < abs(d) < len(self.V) else 0.0

    def basis(self, k):
        """Absolute wavevectors k + G with |k + G| <= Kc (the ecut-sphere convention)."""
        G = np.arange(-int(self.Kc) - 2, int(self.Kc) + 3)
        return G[np.abs(k + G) <= self.Kc + 1e-12]

    def bloch(self, k):
        G = self.basis(k)
        H = np.diag((k + G) ** 2).astype(float)
        for i, gi in enumerate(G):
            for j, gj in enumerate(G):
                if i != j:
                    H[i, j] = self.vG(gi - gj)
        e, c = np.linalg.eigh(H)  # real symmetric: real coefficients (real flavour)
        return G, e, c

    def chi_bloch(self, q, Gs, factor=4.0, swap=False):
        """factor/(N_k Om) sum_k sum_v sum_c M_vc(k,G) M_vc(k,G') / (E_v(k+q) - E_c(k)),
        M_vc(k, G) = sum_{G1 - G2 = G} c_v(k+q, G1) c_c(k, G2). With swap: v at k, c at k+q."""
        n = len(Gs)
        chi = np.zeros((n, n))
        for j in range(self.Nk):
            k = j / self.Nk
            Gk, ek, ck = self.bloch(k)
            Gq, eq, cq = self.bloch(k + q)
            if not swap:
                Gv, ev, cv, Gc, ec, cc = Gq, eq, cq, Gk, ek, ck
            else:
                Gv, ev, cv, Gc, ec, cc = Gk, ek, ck, Gq, eq, cq
            for v in range(self.nv):
                for c in range(self.nv, len(ec)):
                    M = np.zeros(n)
                    for a, G in enumerate(Gs):
                        # the index rule of the formula: G1 - G2 = G (coefficients of
                        # e^{i(k_v + G1)x} and e^{i(k_c + G2)x}); momentum-conserving
                        # for <v, k+q| e^{i(q+G)x} |c, k> exactly when k_v = k_c + q
                        for i1, g1 in enumerate(Gv):
                            for i2, g2 in enumerate(Gc):
                                if g1 - g2 == G:
                                    M[a] += cv[i1, v] * cc[i2, c]
                    chi += np.outer(M, M) / (ev[v] - ec[c])
        return factor / (self.Nk * self.Om) * chi

    def chi_supercell(self, q, Gs, lam=1e-5):
        """<q+G| chi |q+G'> from the density response of the N_k-cell supercell (spin 2) to
        dV = lam (e^{i(q+G')x} + e^{-i(q+G')x}); L = N_k a."""
        Nk = self.Nk
        m = np.arange(-int(self.Kc * Nk) - 1, int(self.Kc * Nk) + 2)
        kap = m / Nk
        kap = kap[np.abs(kap) <= self.Kc + 1e-12]
        nb = len(kap)
        nocc = self.nv * Nk
        H0 = np.diag(kap ** 2)
        D = kap[:, None] - kap[None, :]
        for d in range(1, len(self.V)):
            H0 = H0 + self.V[d] * (np.abs(np.abs(D) - d) < 1e-9)
        L = Nk * self.a
        chi = np.zeros((len(Gs), len(Gs)))
        for b, Gp in enumerate(Gs):
            p = q + Gp
            W = (np.abs(D - p) < 1e-9) + (np.abs(D + p) < 1e-9)

            def nft(sign):
                _, c = np.linalg.eigh(H0 + sign * lam * W)
                c = c[:, :nocc]
                # int_L e^{-i p' x} n(x) dx = 2 sum_occ sum_{kap2 - kap1 = p'} c1 c2
                out = np.zeros(len(Gs))
                for a, G in enumerate(Gs):
                    pp = q + G
                    S = (np.abs(-D - pp) < 1e-9).astype(float)  # kap2 - kap1 = pp
                    out[a] = 2 * np.einsum("io,ij,jo->", c, S, c)
                return out

            chi[:, b] = (nft(+1) - nft(-1)) / (2 * lam * L)
        return chi


class E2BlochSpecialisation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cr = Crystal1D()
        cls.q = 1.0 / cls.cr.Nk
        cls.Gs = np.array([0, 1, -1, 2, -2])
        cls.ref = cls.cr.chi_supercell(cls.q, cls.Gs)

    def test_gap(self):
        eks = [self.cr.bloch(j / self.cr.Nk)[1] for j in range(self.cr.Nk)]
        top = max(e[self.cr.nv - 1] for e in eks)
        bot = min(e[self.cr.nv] for e in eks)
        self.assertGreater(bot - top, 0.05)

    def test_factor_four_normalisation_and_k_plus_q(self):
        chi = self.cr.chi_bloch(self.q, self.Gs)
        scale = np.abs(self.ref).max()
        self.assertLess(np.abs(chi - self.ref).max(), 1e-6 * scale)
        self.assertLess(self.ref[0, 0], 0.0)

    def test_factor_two_is_wrong(self):
        chi2 = self.cr.chi_bloch(self.q, self.Gs, factor=2.0)
        self.assertGreater(np.abs(chi2 - self.ref).max(), 0.3 * np.abs(self.ref).max())

    def test_swapped_k_convention_differs(self):
        """Valence at k and conduction at k+q (same index rule) is NOT chi(q)."""
        chis = self.cr.chi_bloch(self.q, self.Gs, swap=True)
        self.assertGreater(np.abs(chis - self.ref).max(), 1e-3 * np.abs(self.ref).max())

    def test_symmetric(self):
        self.assertLess(np.abs(self.ref - self.ref.T).max(), 1e-6 * np.abs(self.ref).max())


# ---------------------------------------------------------------- E3 -------
def rand_chi(n):
    A = RNG.normal(size=(n, n))
    return -(A @ A.T) / n - 0.1 * np.eye(n)


class E3RPA(unittest.TestCase):
    def test_dyson_neumann_symmetrised(self):
        for _ in range(10):
            n = 5
            chi = rand_chi(n)
            v = RNG.uniform(0.2, 1.5, n)
            D = np.diag(v)
            eps = np.eye(n) - D @ chi
            W = np.linalg.solve(eps, D)
            self.assertLess(np.abs(W - (D + D @ chi @ W)).max(), 1e-10)
            for K in (0, 3, 7):
                ps = sum(np.linalg.matrix_power(D @ chi, k) @ D for k in range(K + 1))
                rem = np.linalg.solve(eps, np.linalg.matrix_power(D @ chi, K + 1) @ D)
                self.assertLess(np.abs(W - ps - rem).max(), 1e-9 * max(1, np.abs(W).max()))
            S = np.diag(np.sqrt(v))
            epst = np.eye(n) - S @ chi @ S
            self.assertAlmostEqual(np.linalg.det(epst), np.linalg.det(eps), delta=1e-9)
            self.assertLess(np.abs(S @ np.linalg.inv(epst) @ S - W).max(), 1e-10)
            self.assertLess(np.abs(W - W.T).max(), 1e-10)
            # W_ji = eps^-1_ji v_i (column scaling)
            self.assertLess(np.abs(W - np.linalg.inv(eps) * v[None, :]).max(), 1e-12)

    def test_static_limit_of_dynamic_W(self):
        _, e, phi, nocc = random_orbital_system()
        gs = RNG.normal(size=(3, len(e)))
        v = np.array([0.7, 0.4, 1.1])
        f = (np.arange(len(e)) < nocc).astype(float)

        def chiw(om):
            P = [pair_amp(phi, g) for g in gs]
            M = np.zeros((3, 3))
            for i in range(3):
                for j in range(3):
                    M[i, j] = sum(P[i][m, mp] * P[j][m, mp] * ((1 - f[m]) * f[mp] - f[m] * (1 - f[mp]))
                                  / (om - (e[m] - e[mp])) for m in range(len(e)) for mp in range(len(e))
                                  if f[m] != f[mp])
            return M

        W0 = np.linalg.solve(np.eye(3) - np.diag(v) @ chiw(0.0), np.diag(v))
        errs = [np.abs(np.linalg.solve(np.eye(3) - np.diag(v) @ chiw(om), np.diag(v)) - W0).max()
                for om in (1e-2, 1e-4)]
        self.assertLess(errs[1], errs[0])
        self.assertLess(errs[1], 1e-5)


# ---------------------------------------------------------------- E4 -------
class E4EpsilonChain(unittest.TestCase):
    def test_eps_and_inverse(self):
        cr = Crystal1D(Nk=5, V=(0.0, 0.5, 0.9))
        q = 2.0 / cr.Nk
        Gs = np.array([0, 1, -1, 2])
        chi_th = cr.chi_supercell(q, Gs)
        chi_spec = cr.chi_bloch(q, Gs)
        v = 8 * np.pi / (q + Gs) ** 2  # Rydberg Coulomb form, q + G != 0
        eps_th = np.eye(len(Gs)) - np.diag(v) @ chi_th
        eps_spec = np.eye(len(Gs)) - v[:, None] * chi_spec  # row scaling eps_ij = d_ij - v_i chi_ij
        self.assertLess(np.abs(eps_th - eps_spec).max(), 1e-6 * np.abs(eps_th).max())
        inv_th, inv_spec = np.linalg.inv(eps_th), np.linalg.inv(eps_spec)
        self.assertLess(np.abs(inv_th - inv_spec).max(), 1e-6 * np.abs(inv_th).max())
        W = inv_spec * v[None, :]
        self.assertLess(np.abs(W - W.T).max(), 1e-6 * np.abs(W).max())
        self.assertTrue(np.all(np.diag(eps_th) > 1.0))


if __name__ == "__main__":
    unittest.main()

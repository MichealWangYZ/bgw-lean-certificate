#!/usr/bin/env python3
"""A3(a) numeric cross-check (G4): low-order structure of the exact self-energy
of a general finite fermion system, and of G0W0, before any Lean proof.

    python3 bgw/endpoint/manybody/check_sigma2.py [--seed S] [--n N] [--nocc K]

Model (spin-orbitals p = 0..n-1, Jordan-Wigner, bit p of a basis index = n_p):
  H(lam) = H0 + lam V,  H0 = sum_p eps_p c_p^+ c_p,
  V = 1/2 sum_{pqrs} v[p,q,r,s] c_p^+ c_q^+ c_s c_r,
  v real with v[p,q,r,s] = v[q,p,s,r] (particle exchange) and
  v[p,q,r,s] = v[r,s,p,q] (V symmetric).  <pq||rs> = v[p,q,r,s] - v[p,q,s,r].
  Occupied set O = the nocc lowest eps (strict gap), Phi = Slater determinant.

Exact G (N0 = nocc sector ground state psi, energy E, real omega):
  G_pq = <psi| c_p (w - (H-E))^-1 c_q^+ |psi> + <psi| c_q^+ (w + (H-E))^-1 c_p |psi>
  Sigma = G0^-1 - G^-1, G0 = diag 1/(w - eps).
Taylor coefficients in lam are extracted by finite differences (5-point).

Formulas compared (a, b in O; r, s not in O):
  Sigma1_pq = sum_a <pa||qa>                                  (HF)
  dir_pq  = sum_{ars} v[p,a,r,s] v[r,s,q,a] / (w + e_a - e_r - e_s)
          + sum_{abr} v[p,r,a,b] v[a,b,q,r] / (w + e_r - e_a - e_b)
  sox_pq  = -sum_{ars} v[p,a,r,s] v[r,s,a,q] / (...) - sum_{abr} v[p,r,a,b] v[a,b,r,q] / (...)
  (dir + sox = 1/2 sum <pa||rs><rs||qa>/(..) + 1/2 sum <pr||ab><ab||qr>/(..))
  relax_pq = sum_{a r} (<pa||qr> + <pr||qa>) Sigma1_ra / (e_a - e_r)
  Claim: Sigma2 = dir + sox + relax  (relax = 0 under the Brillouin condition
  Sigma1_ra = 0).
GW (G0W0 from G0, RPA W = lam v + lam^2 v chi0 v + ...): Sigma_GW,2 = dir,
checked by numerical imaginary-frequency convolution of G0 with v chi0 v.
"""
import argparse
import itertools
import numpy as np


def ops(n):
    dim = 1 << n
    c = np.zeros((n, dim, dim))
    for p in range(n):
        for s in range(dim):
            if s >> p & 1:
                sign = (-1) ** bin(s & ((1 << p) - 1)).count("1")
                c[p, s ^ (1 << p), s] = sign
    return c


def model(n, nocc, rng, brillouin=False):
    eps = np.sort(rng.normal(size=n)) * 2.0
    eps[nocc:] += 1.0  # open the gap
    v = rng.normal(size=(n, n, n, n))
    v = v + v.transpose(1, 0, 3, 2)
    v = v + v.transpose(2, 3, 0, 1)
    if brillouin:
        # impose a symmetry that kills the occupied-empty block of Sigma1:
        # a Z2 parity pi_p, v nonzero only if total parity even, with occupied
        # and empty orbitals of opposite parity.
        par = np.array([0] * nocc + [1] * (n - nocc))
        for idx in itertools.product(range(n), repeat=4):
            if (par[list(idx)].sum()) % 2:
                v[idx] = 0.0
    return eps, v


def exact_sigma(eps, v, nocc, c, lam, w):
    n = len(eps)
    cd = c.transpose(0, 2, 1)
    H0 = sum(eps[p] * cd[p] @ c[p] for p in range(n))
    V = np.zeros_like(H0)
    for p, q, r, s in itertools.product(range(n), repeat=4):
        if v[p, q, r, s] != 0.0:
            V += 0.5 * v[p, q, r, s] * (cd[p] @ cd[q] @ c[s] @ c[r])
    H = H0 + lam * V
    num = np.array([bin(s).count("1") for s in range(1 << n)])
    idx = np.where(num == nocc)[0]
    Hs = H[np.ix_(idx, idx)]
    ev, U = np.linalg.eigh(Hs)
    psi = np.zeros(1 << n)
    psi[idx] = U[:, 0]
    E = ev[0]
    one = np.eye(1 << n)
    Rp = np.linalg.inv(w * one - (H - E * one))
    Rm = np.linalg.inv(w * one + (H - E * one))
    G = np.zeros((n, n))
    for p in range(n):
        for q in range(n):
            G[p, q] = psi @ c[p] @ Rp @ cd[q] @ psi + psi @ cd[q] @ Rm @ c[p] @ psi
    G0inv = np.diag(w - eps)
    return G0inv - np.linalg.inv(G), (H0, V, psi, E)


def formulas(eps, v, nocc, w):
    n = len(eps)
    O = range(nocc)
    X = range(nocc, n)
    A = v - v.transpose(0, 1, 3, 2)
    S1 = np.zeros((n, n))
    for p, q in itertools.product(range(n), repeat=2):
        S1[p, q] = sum(A[p, a, q, a] for a in O)
    dt = np.result_type(eps, w)
    dr, sx, rl, half = (np.zeros((n, n), dt) for _ in range(4))
    for p, q in itertools.product(range(n), repeat=2):
        for a in O:
            for r in X:
                for s in X:
                    den = w + eps[a] - eps[r] - eps[s]
                    dr[p, q] += v[p, a, r, s] * v[r, s, q, a] / den
                    sx[p, q] -= v[p, a, r, s] * v[r, s, a, q] / den
                    half[p, q] += 0.5 * A[p, a, r, s] * A[r, s, q, a] / den
        for a in O:
            for b in O:
                for r in X:
                    den = w + eps[r] - eps[a] - eps[b]
                    dr[p, q] += v[p, r, a, b] * v[a, b, q, r] / den
                    sx[p, q] -= v[p, r, a, b] * v[a, b, r, q] / den
                    half[p, q] += 0.5 * A[p, r, a, b] * A[a, b, q, r] / den
        for a in O:
            for r in X:
                rl[p, q] += (A[p, a, q, r] + A[p, r, q, a]) * S1[r, a] / (eps[a] - eps[r])
    return S1, dr, sx, rl, half


def gw_second_order_imag(eps, v, nocc, nu, ngrid=200001, L=4000.0):
    """Sigma_c^(2)(i nu) = -(1/2pi) int G0(i nu - i x) [v chi0 v](i x) dx
    in the orbital-pair representation, with Sigma(t) = i G0(t) W(t), hence
      Sigma_pq(w) = i int dw'/2pi sum_m G0_m(w - w') W_{p m, m q}(w')
    (w - w', not w + w': W_{pm,mq}(t) is not even in t for general orbitals),
      W_{(pm),(nq)} = v[p,n,m,q] (electron 1: p -> m, electron 2: n -> q),
      [v chi0 v]_{(pm),(mq)}(w') = sum_{a r} v[p,a,m,r] v[r,m,a,q] / (w' - D + i0)
                                 - sum_{a r} v[p,r,m,a] v[a,m,r,q] / (w' + D - i0),
      D = e_r - e_a (the forward / backward halves of the time-ordered chi0 =
      -i G0(t) G0(-t) carry different orbital pairs unless the orbitals are real).
    Evaluated on the imaginary axis w' = i x, G0_m(i y) = 1/(i y - e_m)."""
    n = len(eps)
    O = range(nocc)
    X = range(nocc, n)
    x = np.linspace(-L, L, ngrid)
    dx = x[1] - x[0]
    S = np.zeros((n, n), complex)
    for p, q in itertools.product(range(n), repeat=2):
        tot = 0.0
        for m in range(n):
            g = 1.0 / (1j * (nu - x) - eps[m])
            wc = np.zeros_like(x, dtype=complex)
            for a in O:
                for r in X:
                    D = eps[r] - eps[a]
                    wc = wc + (v[p, a, m, r] * v[r, m, a, q] / (1j * x - D)
                               - v[p, r, m, a] * v[a, m, r, q] / (1j * x + D))
            # i * int dw'/2pi with w' = i x: dw' = i dx  ->  i * i/(2pi) = -1/(2pi)
            tot += -(g * wc).sum() * dx / (2 * np.pi)
        S[p, q] = tot
    return S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=5)
    ap.add_argument("--nocc", type=int, default=2)
    ap.add_argument("--omega", type=float, default=0.37)
    ap.add_argument("--h", type=float, default=2e-3)
    ap.add_argument("--brillouin", action="store_true")
    ap.add_argument("--gw", action="store_true")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    eps, v = model(a.n, a.nocc, rng, a.brillouin)
    c = ops(a.n)
    w, h = a.omega, a.h
    f = {k: exact_sigma(eps, v, a.nocc, c, k * h, w)[0] for k in (-2, -1, 0, 1, 2)}
    c0 = f[0]
    c1 = (8 * (f[1] - f[-1]) - (f[2] - f[-2])) / (12 * h)
    c2 = (-f[2] + 16 * f[1] - 30 * f[0] + 16 * f[-1] - f[-2]) / (24 * h * h)
    S1, dr, sx, rl, half = formulas(eps, v, a.nocc, w)
    print("eps", np.round(eps, 4))
    print("max|Sigma0|                  ", np.abs(c0).max())
    print("max|Sigma1 - HF|             ", np.abs(c1 - S1).max(), " scale", np.abs(S1).max())
    print("max|dir+sox - half-antisym|  ", np.abs(dr + sx - half).max())
    print("max|Sigma2 - (dir+sox)|      ", np.abs(c2 - dr - sx).max(), " scale", np.abs(c2).max())
    print("max|Sigma2 - (dir+sox+relax)|", np.abs(c2 - dr - sx - rl).max())
    print("max|relax|                   ", np.abs(rl).max())
    print("max|S1 occ-emp block|        ", np.abs(S1[a.nocc:, :a.nocc]).max())
    if a.gw:
        nu = 0.8
        Sgw = gw_second_order_imag(eps, v, a.nocc, nu)
        _, drI, _, _, _ = formulas(eps.astype(complex), v, a.nocc, 1j * nu)
        print("max|Sigma_GW2(i nu) - dir(i nu)|", np.abs(Sgw - drI).max(), " scale", np.abs(drI).max())


if __name__ == "__main__":
    main()

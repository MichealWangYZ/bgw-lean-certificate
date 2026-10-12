#!/usr/bin/env python3
"""G3: exact self-energy of the half-filled Hubbard dimer, checked numerically
before the Lean proofs in GW/Endpoint/HubbardDimerExactSigma.lean.

    python3 bgw/endpoint/a3_dimer/exact_sigma_dimer.py

Independent of the Lean closed forms:
1. Builds the 16x16 Fock-space H from Jordan-Wigner operators (same mode order
   as HubbardDimerFock.lean: 0 = 1up, 1 = 1dn, 2 = 2up, 3 = 2dn), diagonalises
   it with numpy, takes the N = 2 ground state Psi0 and ALL N = 1, N = 3
   eigenstates, and forms the spin-up Lehmann Green's function in the
   bonding/antibonding orbital basis (B = (1,1)/sqrt2, A = (1,-1)/sqrt2).
2. Checks G_BA = G_AB = 0 (parity) and G against the closed form used in Lean.
3. Sigma_p(w) = (w - eps0_p) - 1/G_pp(w) with the U = 0 reference
   (eps0_B = -t, eps0_A = +t), compared with
     U/2 + sig2dir_p(w) + sig2x_p(w)
   where sig2dir/sig2x are the closed-shell second-order formulas of
   HubbardDimerSecondOrder.lean (spin factors 2 and -1, HF denominators),
   evaluated with ERIs transformed from the site tensor.
4. Finite differences in U at fixed w: Sigma1 = 1/2 and
   Sigma2(w) = 1/(4(w -+ 3t)).
5. Negative controls: the direct ("2") term alone, or exchange factor -2,
   does NOT reproduce Sigma.
"""
import itertools
import sys

import numpy as np

ok = True


def check(name, err, tol):
    global ok
    flag = err <= tol
    ok &= flag
    print(f"{'OK ' if flag else 'BAD'} {name}: {err:.3e} (tol {tol:.0e})")


def ann(m):
    A = np.zeros((16, 16))
    for s in range(16):
        if s >> m & 1:
            sign = (-1) ** bin(s & ((1 << m) - 1)).count("1")
            A[s - (1 << m), s] = sign
    return A


c = [ann(m) for m in range(4)]
cd = [x.T for x in c]
num = [cd[m] @ c[m] for m in range(4)]
hop = cd[0] @ c[2] + cd[2] @ c[0] + cd[1] @ c[3] + cd[3] @ c[1]
dbl = num[0] @ num[1] + num[2] @ num[3]
Nop = sum(num)
s2 = 1 / np.sqrt(2)
orb = np.array([[s2, s2], [s2, -s2]])  # orb[p, i]


def cup(p):
    return orb[p, 0] * c[0] + orb[p, 1] * c[2]


def lehmann(t, U, w):
    H = -t * hop + U * dbl
    pop = np.diag(Nop).round().astype(int)
    sec = {N: np.where(pop == N)[0] for N in (1, 2, 3)}
    eig = {}
    for N, idx in sec.items():
        e, v = np.linalg.eigh(H[np.ix_(idx, idx)])
        V = np.zeros((16, len(idx)))
        V[idx, :] = v
        eig[N] = (e, V)
    e2, V2 = eig[2]
    E0, psi = e2[0], V2[:, 0]
    assert e2[1] - e2[0] > 1e-9  # nondegenerate
    G = np.zeros((2, 2))
    for p, q in itertools.product(range(2), repeat=2):
        e3, V3 = eig[3]
        e1, V1 = eig[1]
        a = (V3.T @ (cup(p).T @ psi)) * (V3.T @ (cup(q).T @ psi)) / (w - (e3 - E0))
        b = (V1.T @ (cup(q) @ psi)) * (V1.T @ (cup(p) @ psi)) / (w - (E0 - e1))
        G[p, q] = a.sum() + b.sum()
    return G, E0


def G_closed(t, U, w):
    r = np.sqrt(U * U + 16 * t * t)
    E0 = (U - r) / 2
    # weights: particle weight of B = (1 - 4t/r)/2 etc. (see Lean `wP`)
    wm = (1 - 4 * t / r) / 2
    wp = (1 + 4 * t / r) / 2
    GB = wp / (w - (E0 + t)) + wm / (w - (U + t - E0))
    GA = wm / (w - (E0 - t)) + wp / (w - (U - t - E0))
    return GB, GA


def eri(U):
    v = np.zeros((2,) * 4)
    for i in range(2):
        v[i, i, i, i] = U
    return np.einsum("pi,qj,rk,sl,ijkl->pqrs", orb, orb, orb, orb, v)


def sig2(t, U, p, E, direct_factor=2.0, exch_factor=-1.0):
    g = eri(U)
    eps = [-t + U / 2, t + U / 2]
    occ, vir = [0], [1]
    tot = 0.0
    for a in occ:
        for r_ in vir:
            for s in vir:
                tot += g[p, a, r_, s] * (direct_factor * g[r_, s, p, a] + exch_factor * g[r_, s, a, p]) / (
                    E + eps[a] - eps[r_] - eps[s])
    for a in occ:
        for b in occ:
            for r_ in vir:
                tot += g[p, r_, a, b] * (direct_factor * g[a, b, p, r_] + exch_factor * g[a, b, r_, p]) / (
                    E + eps[r_] - eps[a] - eps[b])
    return tot


eps0 = lambda t: [-t, t]
pts = [(1.0, 0.3, 0.7), (1.0, 1.7, -2.3), (0.6, 2.5, 0.1), (1.3, 0.05, 5.0)]
worst_par = worst_cf = worst_sig = worst_x = 0.0
for t, U, w in pts:
    G, E0 = lehmann(t, U, w)
    worst_par = max(worst_par, abs(G[0, 1]), abs(G[1, 0]))
    GB, GA = G_closed(t, U, w)
    worst_cf = max(worst_cf, abs(G[0, 0] - GB), abs(G[1, 1] - GA))
    for p in range(2):
        sig = w - eps0(t)[p] - 1 / G[p, p]
        worst_sig = max(worst_sig, abs(sig - (U / 2 + sig2(t, U, p, w))))
        worst_x = max(worst_x, abs(sig - (U / 2 + (U * U / 4) / (w - (3 * t if p == 0 else -3 * t) - U / 2))))
check("parity: G_BA = G_AB = 0", worst_par, 1e-12)
check("Lehmann G vs closed form", worst_cf, 1e-12)
check("Sigma_exact - U/2 == sig2dir + sig2x (all U)", worst_sig, 1e-10)
check("Sigma_exact == U/2 + (U^2/4)/(w -+ 3t - U/2)", worst_x, 1e-10)

# finite differences in U at fixed w
t, w = 1.0, 0.7
for p in range(2):
    f = lambda U: w - eps0(t)[p] - 1 / lehmann(t, U, w)[0][p, p]
    h = 1e-3
    s1 = (f(h) - f(-h)) / (2 * h)
    s2c = (f(h) - 2 * f(0.0) + f(-h)) / (2 * h * h)
    want2 = 1 / (4 * (w - (3 * t if p == 0 else -3 * t)))
    check(f"p={p}: dSigma/dU at 0 = 1/2", abs(s1 - 0.5), 1e-6)
    check(f"p={p}: (1/2) d2Sigma/dU2 at 0 = 1/(4(w-+3t))", abs(s2c - want2), 1e-5)
    # negative control: direct term only is off by a factor 2 in the U^2 coefficient
    d_only = (sig2(t, 1e-3, p, w, exch_factor=0.0)) / 1e-6
    bad = abs(d_only - want2) > 0.1 * abs(want2)
    ok &= bad
    print(f"{'OK ' if bad else 'BAD'} p={p}: direct-only U^2 coeff {d_only:.5f} != exact {want2:.5f}")

# negative control: wrong exchange spin factor (-2 instead of -1) breaks the exact identity
t, U, w = 1.0, 0.8, 0.7
G, _ = lehmann(t, U, w)
sig = w - eps0(t)[0] - 1 / G[0, 0]
err = abs(sig - (U / 2 + sig2(t, U, 0, w, exch_factor=-2.0)))
bad = err > 1e-3
ok &= bad
print(f"{'OK ' if bad else 'BAD'} exchange factor -2: identity violated by {err:.3e}")

print("ALL OK" if ok else "FAILURES")
sys.exit(0 if ok else 1)

#!/usr/bin/env python3
"""A3 dimer, part 2: numeric/symbolic checks before the Lean proofs in
GW/Endpoint/HubbardDimerSigma.lean and GW/Endpoint/HubbardDimerSecondOrder.lean.

    python3 bgw/endpoint/a3_dimer/second_order_dimer.py

1. Time domain (Task 3). Sigma_c(tau) = i G0(tau) W_c(tau) with
     G0_ij(tau) = -i sum_k phi_k(i) phi_k(j) [theta(tau)(1-f_k) - theta(-tau) f_k] e^{-i eps_k tau}
     W_c,ij(tau) = -i R_ij e^{-i Omega |tau|}
   Its damped transform  int dtau e^{i w tau - eta |tau|} Sigma_c(tau)  is computed by
   numerical quadrature and compared with the closed form
     sum_k phi phi R [(1-f)/(w - eps - Omega + i eta) + f/(w - eps + Omega - i eta)],
   whose eta -> 0 limit is `sigmaSinglePole`. Same for W_c(tau) -> W_c(w).
2. Second order (Task 4). Two-electron integrals <pq|rs> in the orbital basis
   are obtained by transforming the site tensor v_ijkl = U d_ij d_ik d_il; the
   second-order direct (ring) and exchange (SOX) self-energies of
   bgw/endpoint/second_order.py are evaluated at the HF energies, and their gap
   contributions are compared with the U^2 Taylor coefficients (sympy) of the
   exact, G0W0@HF and HF gaps.
"""
import math
import sys

import numpy as np
import sympy as sp
from scipy.integrate import quad

ok = True


def check(name, err, tol):
    global ok
    flag = err <= tol
    ok &= flag
    print(f"{'OK ' if flag else 'BAD'} {name}: {err:.3e} (tol {tol:.0e})")


# ------------------------------------------------------------------ Task 3
def ft_damped(f, w, eta, T=None):
    """int_R e^{i w tau - eta|tau|} f(tau) dtau, split at 0, truncated where e^{-eta tau} < 1e-17."""
    T = T or 40.0 / eta
    re = lambda s: lambda x: (np.exp(1j * w * s * x - eta * x) * f(s * x)).real
    im = lambda s: lambda x: (np.exp(1j * w * s * x - eta * x) * f(s * x)).imag
    tot = 0j
    for s in (1.0, -1.0):
        tot += quad(re(s), 0, T, limit=4000)[0] + 1j * quad(im(s), 0, T, limit=4000)[0]
    return tot


def task3(t, U, w, eta):
    s2 = 1 / math.sqrt(2)
    orbs = [(np.array([s2, s2]), -t + U / 2, 1), (np.array([s2, -s2]), t + U / 2, 0)]
    h = math.sqrt(4 * t * t + 4 * t * U)
    sg = np.array([1, -1])
    R = np.outer(sg, sg) * t * U * U / h
    worst = 0.0
    for i in range(2):
        for j in range(2):
            def G0(tau):
                return -1j * sum(p[i] * p[j] * ((1 - f) if tau > 0 else -f) * np.exp(-1j * e * tau)
                                 for p, e, f in orbs)

            def Wc(tau):
                return -1j * R[i, j] * np.exp(-1j * h * abs(tau))

            sig = ft_damped(lambda tau: 1j * G0(tau) * Wc(tau), w, eta)
            closed = sum(p[i] * p[j] * R[i, j] * ((1 - f) / (w - e - h + 1j * eta) + f / (w - e + h - 1j * eta))
                         for p, e, f in orbs)
            wc = ft_damped(Wc, w, eta)
            wclosed = R[i, j] * (1 / (w - h + 1j * eta) - 1 / (w + h - 1j * eta))
            worst = max(worst, abs(sig - closed), abs(wc - wclosed))
    return worst


# ------------------------------------------------------------------ Task 4
def eri_orbital(U, C):
    """<pq|rs> = sum_{ijkl} C_ip C_jq C_kr C_ls v_ijkl, v_ijkl = U d_ij d_ik d_il (site basis)."""
    v = np.zeros((2, 2, 2, 2))
    for i in range(2):
        v[i, i, i, i] = U
    return np.einsum("ip,jq,kr,ls,ijkl->pqrs", C, C, C, C, v)


def sigma2(eri, e, occ, vir, p, E):
    d = x = 0.0
    for a in occ:
        for r in vir:
            for s in vir:
                den = E + e[a] - e[r] - e[s]
                d += eri[p, a, r, s] * 2 * eri[r, s, p, a] / den
                x += -eri[p, a, r, s] * eri[r, s, a, p] / den
    for a in occ:
        for b in occ:
            for r in vir:
                den = E + e[r] - e[a] - e[b]
                d += eri[p, r, a, b] * 2 * eri[a, b, p, r] / den
                x += -eri[p, r, a, b] * eri[a, b, r, p] / den
    return d, x


def task4_numeric(t, U):
    s2 = 1 / math.sqrt(2)
    C = np.array([[s2, s2], [s2, -s2]])  # columns: B (0), A (1)
    eri = eri_orbital(U, C)
    # closed form used in Lean: <pq|rs> = U/2 if #A even else 0
    closed = np.zeros_like(eri)
    for idx in np.ndindex(2, 2, 2, 2):
        closed[idx] = U / 2 if sum(idx) % 2 == 0 else 0.0
    e = np.array([-t + U / 2, t + U / 2])
    dB, xB = sigma2(eri, e, [0], [1], 0, e[0])
    dA, xA = sigma2(eri, e, [0], [1], 1, e[1])
    return np.abs(eri - closed).max(), dA - dB, xA - xB


def task4_symbolic():
    t, U = sp.symbols("t U", positive=True)
    h = sp.sqrt(4 * t ** 2 + 4 * t * U)
    ex = sp.sqrt(U ** 2 + 16 * t ** 2) - 2 * t
    gw = sp.sqrt((2 * t + h) ** 2 + 4 * t * U ** 2 / h) - h
    c = lambda f: sp.simplify(sp.series(f, U, 0, 3).removeO().coeff(U, 2))
    return c(ex), c(gw), sp.simplify(sp.series(ex, U, 0, 2).removeO().coeff(U, 1)), \
        sp.simplify(sp.series(gw, U, 0, 2).removeO().coeff(U, 1)), t


def main():
    for (t, U, w, eta) in [(1.0, 0.7, 0.3, 0.5), (0.5, 1.3, -2.2, 0.8), (1.0, 0.2, 5.0, 1.0)]:
        check(f"Task3 damped FT of iG0Wc and of Wc vs closed form t={t} U={U} w={w} eta={eta}",
              task3(t, U, w, eta), 1e-7)
    cex, cgw, lex, lgw, tt = task4_symbolic()
    print(f"U^2 coefficient: exact {cex}, G0W0@HF {cgw}, HF 0; U^1: exact {lex}, GW {lgw}")
    for t, U in [(1.0, 0.1), (0.5, 0.3), (2.0, 1.7)]:
        err, gdir, gx = task4_numeric(t, U)
        check(f"ERI transform vs closed form t={t} U={U}", err, 1e-14)
        check(f"direct gap = U^2/(4t)  t={t} U={U}", abs(gdir - U * U / (4 * t)), 1e-13)
        check(f"SOX gap = -U^2/(8t)  t={t} U={U}", abs(gx + U * U / (8 * t)), 1e-13)
        check("GW coeff = direct/U^2", abs(float(cgw.subs(tt, t)) - gdir / U ** 2), 1e-12)
        check("exact coeff = (direct+SOX)/U^2", abs(float(cex.subs(tt, t)) - (gdir + gx) / U ** 2), 1e-12)
    print("ALL OK" if ok else "FAILURES")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

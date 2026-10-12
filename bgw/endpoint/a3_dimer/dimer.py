#!/usr/bin/env python3
"""A3(b): two-site Hubbard dimer at half filling -- exact vs G0W0@HF gap.

    python3 bgw/endpoint/a3_dimer/dimer.py [--out FILE]

Two independent routes to every closed form used in GW/Endpoint/HubbardDimer.lean:

1. symbolic (sympy): build the 16x16 Jordan-Wigner Fock-space Hamiltonian
   symbolically, diagonalise each particle-number sector, and derive the RPA W,
   its pole/residue, the single-pole GW self-energy and the QP roots; compare
   with the closed forms transcribed below (the ones stated in Lean).
2. numeric (numpy/scipy): dense exact diagonalisation at several (t, U);
   RPA W by numerical 2x2 matrix inversion; RPA pole by root finding on
   det(1 - v chi0); Sigma_c from the pole formula AND, independently, from the
   imaginary-axis frequency convolution  Sigma(mu+i nu) = -(1/2pi) Int G0 W_c
   (this checks the residue step that Lean takes as the definition); full QP
   equation solved by bracketing root finding (no linearisation).

Conventions (same as the Lean file): modes 0=1up, 1=1dn, 2=2up, 3=2dn;
basis state s in 0..15 has mode m occupied iff bit m of s is set;
c_m |s> = (-1)^(#occupied modes below m) |s - 2^m>.
G0 = G_HF (restricted HF: bonding orbital doubly occupied; HF eigenvalues
-t + U/2, t + U/2), W = RPA from the spin-summed chi0 of that G0 with
v_ij = U delta_ij, Sigma_c = i G0 W_c, QP equation E = eps_HF + Sigma_c(E).
"""
import argparse
import json
import math
import pathlib
import sys

import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq

HERE = pathlib.Path(__file__).resolve().parent


# ---------------------------------------------------------------- Fock space
def occ(s, m):
    return (s >> m) & 1


def ann(m, lib=np):
    c = [[0] * 16 for _ in range(16)]
    for s in range(16):
        if occ(s, m):
            sign = (-1) ** sum(occ(s, k) for k in range(m))
            c[s - (1 << m)][s] = sign
    return np.array(c, dtype=float) if lib is np else sp.Matrix(c)


def hamiltonian(t, U, lib=np):
    a = [ann(m, lib) for m in range(4)]
    cr = [x.T for x in a]
    hop = cr[0] @ a[2] + cr[2] @ a[0] + cr[1] @ a[3] + cr[3] @ a[1] if lib is np else \
        cr[0] * a[2] + cr[2] * a[0] + cr[1] * a[3] + cr[3] * a[1]
    n = [cr[m] @ a[m] if lib is np else cr[m] * a[m] for m in range(4)]
    dbl = n[0] @ n[1] + n[2] @ n[3] if lib is np else n[0] * n[1] + n[2] * n[3]
    return -t * hop + U * dbl


def popcount(s):
    return bin(s).count("1")


def sector(N):
    return [s for s in range(16) if popcount(s) == N]


# ---------------------------------------------------------------- closed forms (as in Lean)
def gap_exact(t, U):
    return math.sqrt(U * U + 16 * t * t) - 2 * t


def h_rpa(t, U):
    return math.sqrt(4 * t * t + 4 * t * U)


def e_rem_gw(t, U):
    h = h_rpa(t, U)
    return U / 2 - t + ((2 * t + h) - math.sqrt((2 * t + h) ** 2 + 4 * t * U * U / h)) / 2


def gap_gw(t, U):
    h = h_rpa(t, U)
    return math.sqrt((2 * t + h) ** 2 + 4 * t * U * U / h) - h


def gap_hf(t, U):
    return 2 * t


# ---------------------------------------------------------------- symbolic route
def symbolic():
    t, U = sp.symbols("t U", positive=True)
    w, E = sp.symbols("omega E")
    H = hamiltonian(t, U, lib=sp)
    out = {}
    # particle-number conservation and sector ground energies
    Nop = sp.diag(*[popcount(s) for s in range(16)])
    assert sp.simplify(H * Nop - Nop * H) == sp.zeros(16, 16)
    e0 = {}
    for N in (1, 2, 3):
        idx = sector(N)
        eig = H.extract(idx, idx).eigenvals()
        e0[N] = [sp.simplify(k) for k in eig]
    r = sp.sqrt(U**2 + 16 * t**2)
    want = {1: -t, 2: (U - r) / 2, 3: U - t}
    for N in (1, 2, 3):
        assert any(sp.simplify(k - want[N]) == 0 for k in e0[N]), (N, e0[N])
        # it is the lowest: every other eigenvalue minus it is >= 0 (checked at many points)
        for k in e0[N]:
            f = sp.lambdify((t, U), k - want[N])
            for tv, Uv in [(1, 0), (1, 0.3), (1, 1), (0.7, 2.5), (2, 10)]:
                assert f(tv, Uv) >= -1e-12
    gapx = sp.simplify(want[3] + want[1] - 2 * want[2])
    assert sp.simplify(gapx - (r - 2 * t)) == 0
    out["sector_eigenvalues"] = {N: [str(k) for k in e0[N]] for N in e0}
    out["gap_exact"] = str(gapx)

    # one-body: h0, orbitals, restricted HF
    h0 = sp.Matrix([[0, -t], [-t, 0]])
    phib = sp.Matrix([1, 1]) / sp.sqrt(2)
    phia = sp.Matrix([1, -1]) / sp.sqrt(2)
    rho = phib * phib.T                              # per-spin density matrix
    ntot = [2 * rho[i, i] for i in range(2)]
    F = h0 + U * sp.diag(*ntot) - U * sp.diag(rho[0, 0], rho[1, 1])
    assert sp.simplify(F - (h0 + U / 2 * sp.eye(2))) == sp.zeros(2, 2)
    eb, ea = -t + U / 2, t + U / 2
    assert sp.simplify(F * phib - eb * phib) == sp.zeros(2, 1)
    assert sp.simplify(F * phia - ea * phia) == sp.zeros(2, 1)
    # chi0 (spin-summed), W = (1 - v chi0)^-1 v
    D = ea - eb
    pair = sp.Matrix([phib[i] * phia[i] for i in range(2)])
    chi0 = 2 * pair * pair.T * (1 / (w - D) - 1 / (w + D))
    v = U * sp.eye(2)
    W = sp.simplify((sp.eye(2) - v * chi0).inv() * v)
    h = sp.sqrt(4 * t**2 + 4 * t * U)
    s = sp.Matrix([1, -1])
    Wc = sp.simplify(W - v)
    assert sp.simplify(Wc - s * s.T * 2 * t * U**2 / (w**2 - h**2)) == sp.zeros(2, 2)
    R = s * s.T * t * U**2 / h                        # residue matrix
    assert sp.simplify(Wc - R * (1 / (w - h) - 1 / (w + h))) == sp.zeros(2, 2)
    # single-pole GW self-energy (residue evaluation of i Int G0 W_c)
    orb = [(phib, eb, 1), (phia, ea, 0)]
    Sig = sp.zeros(2, 2)
    for i in range(2):
        for j in range(2):
            Sig[i, j] = sum(ph[i] * ph[j] * R[i, j] * (f / (w - ek + h) + (1 - f) / (w - ek - h))
                            for ph, ek, f in orb)
    Sbb = sp.simplify((phib.T * Sig * phib)[0])
    Saa = sp.simplify((phia.T * Sig * phia)[0])
    Sab = sp.simplify((phia.T * Sig * phib)[0])
    assert sp.simplify(Sbb - t * U**2 / h / (w - ea - h)) == 0
    assert sp.simplify(Saa - t * U**2 / h / (w - eb + h)) == 0
    assert Sab == 0
    # QP equations: E = eb + Sbb(E), E = ea + Saa(E); solve the quadratics
    rem = sp.solve(sp.Eq((E - eb) * (E - ea - h), t * U**2 / h), E)
    add = sp.solve(sp.Eq((E - ea) * (E - eb + h), t * U**2 / h), E)
    Dq = sp.sqrt((2 * t + h) ** 2 + 4 * t * U**2 / h)
    Erem = U / 2 - t + ((2 * t + h) - Dq) / 2
    Eadd = U / 2 + t - ((2 * t + h) - Dq) / 2
    # the closed forms are roots: reduce modulo Dq^2 = (2t+h)^2 + 4tU^2/h and h^2 = 4t^2+4tU
    Ds, hs = sp.symbols("D_s h_s", positive=True)

    def reduces_to_zero(expr):
        e = sp.together(expr.subs(Dq, Ds).subs(h, hs))
        num = sp.expand(sp.numer(e))
        num = sp.rem(num, Ds**2 - ((2 * t + hs) ** 2 + 4 * t * U**2 / hs), Ds)
        num = sp.expand(sp.numer(sp.together(num)))
        return sp.rem(num, hs**2 - (4 * t**2 + 4 * t * U), hs) == 0

    assert reduces_to_zero((Erem - eb) * (Erem - ea - h) - t * U**2 / h)
    assert reduces_to_zero((Eadd - ea) * (Eadd - eb + h) - t * U**2 / h)
    assert len(rem) == 2 and len(add) == 2
    gapgw = sp.simplify(Eadd - Erem)
    assert sp.simplify(gapgw - (Dq - h)) == 0
    out["gap_gw"] = str(Dq - h)
    # series in u = U/t (t = 1)
    u = sp.symbols("u", positive=True)
    ser = lambda f: str(sp.series(f.subs({t: 1, U: u}), u, 0, 6).removeO())  # noqa: E731
    out["series_gap_exact"] = ser(r - 2 * t)
    out["series_gap_gw"] = ser(Dq - h)
    out["series_err_gw"] = ser(Dq - h - (r - 2 * t))
    out["series_err_hf"] = ser(2 * t - (r - 2 * t))
    return out


# ---------------------------------------------------------------- numeric route
def numeric(t, U):
    H = hamiltonian(t, U)
    assert np.allclose(H, H.T)
    E0 = {N: np.linalg.eigvalsh(H[np.ix_(sector(N), sector(N))]).min() for N in (1, 2, 3)}
    gx = E0[3] + E0[1] - 2 * E0[2]
    # one-body and HF self-consistency (iterate from U=0 orbitals)
    h0 = np.array([[0, -t], [-t, 0]], float)
    ev, C = np.linalg.eigh(h0)
    for _ in range(200):
        rho = np.outer(C[:, 0], C[:, 0])
        F = h0 + U * np.diag(2 * np.diag(rho)) - U * np.diag(np.diag(rho))
        ev, C = np.linalg.eigh(F)
    eb, ea = ev
    pb, pa = C[:, 0], C[:, 1]
    pair = pb * pa
    D = ea - eb
    v = U * np.eye(2)

    def chi0(z):
        return 2 * np.outer(pair, pair) * (1 / (z - D) - 1 / (z + D))

    def Wc(z):
        return np.linalg.inv(np.eye(2) - v @ chi0(z)) @ v - v

    if U > 0:
        Om = brentq(lambda x: np.linalg.det(np.eye(2) - v @ chi0(x)), D * (1 + 1e-12), 10 * (D + U))
        dz = 1e-6 * Om
        Res = np.real(Wc(Om + 1j * dz) * (1j * dz))     # residue at +Omega
    else:
        Om, Res = D, np.zeros((2, 2))
    orb = [(pb, eb, 1.0), (pa, ea, 0.0)]

    def sigma_pole(z):
        S = np.zeros((2, 2), complex)
        for ph, ek, f in orb:
            S += np.outer(ph, ph) * Res * (f / (z - ek + Om) + (1 - f) / (z - ek - Om))
        return S

    mu = (eb + ea) / 2
    conv_err = 0.0
    if U > 0:
        for nu in (0.3 * t, 1.1 * t):
            z = mu + 1j * nu
            S = np.zeros((2, 2), complex)
            for i in range(2):
                for j in range(2):
                    def integrand(x, part):
                        G = sum(ph[i] * ph[j] / (z + 1j * x - ek) for ph, ek, _ in orb)
                        val = -G * Wc(1j * x)[i, j] / (2 * math.pi)
                        return val.real if part == 0 else val.imag
                    re = quad(integrand, -np.inf, np.inf, args=(0,), limit=400, epsabs=1e-13)[0]
                    im = quad(integrand, -np.inf, np.inf, args=(1,), limit=400, epsabs=1e-13)[0]
                    S[i, j] = re + 1j * im
            conv_err = max(conv_err, np.abs(S - sigma_pole(z)).max())
    sbb = lambda E: (pb @ sigma_pole(E) @ pb).real  # noqa: E731
    saa = lambda E: (pa @ sigma_pole(E) @ pa).real  # noqa: E731
    pole_b, pole_a = ea + Om, eb - Om
    if U > 0:
        Er = brentq(lambda E: E - eb - sbb(E), eb - 10 * (t + U), pole_b - 1e-9 * Om, xtol=1e-15)
        Ea = brentq(lambda E: E - ea - saa(E), pole_a + 1e-9 * Om, ea + 10 * (t + U), xtol=1e-15)
    else:
        Er, Ea = eb, ea
    return {"t": t, "U": U,
            "E0": {str(k): float(x) for k, x in E0.items()},
            "gap_exact_ED": float(gx), "gap_exact_closed": gap_exact(t, U),
            "Omega_numeric": float(Om), "Omega_closed": h_rpa(t, U),
            "residue_numeric": float(Res[0, 0]),
            "residue_closed": t * U * U / h_rpa(t, U),
            "freq_integral_vs_pole_formula": float(conv_err),
            "E_rem_numeric": float(Er), "E_rem_closed": e_rem_gw(t, U),
            "gap_gw_numeric": float(Ea - Er), "gap_gw_closed": gap_gw(t, U),
            "gap_hf": float(ea - eb),
            "err_gw": gap_gw(t, U) - gap_exact(t, U),
            "err_hf": gap_hf(t, U) - gap_exact(t, U),
            "bound_gw_upper": U * U / (8 * t) - U**3 / (16 * t * t),
            "bound_gw_lower": U * U / (8 * t) - 3 * U**3 / (16 * t * t)}


POINTS = [(1.0, 0.0), (1.0, 0.1), (1.0, 0.37), (1.0, 1.0), (0.5, 0.2), (2.0, 1.3),
          (1.0, 3.0), (0.25, 4.0)]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(HERE / "crosscheck.json"))
    ap.add_argument("--no-symbolic", action="store_true")
    a = ap.parse_args(argv)
    res = {"symbolic": None if a.no_symbolic else symbolic(), "numeric": []}
    worst = {}
    for t, U in POINTS:
        r = numeric(t, U)
        res["numeric"].append(r)
        checks = {"ED_vs_closed": abs(r["gap_exact_ED"] - r["gap_exact_closed"]),
                  "Omega": abs(r["Omega_numeric"] - r["Omega_closed"]),
                  "residue": abs(r["residue_numeric"] - r["residue_closed"]),
                  "freq_integral": r["freq_integral_vs_pole_formula"],
                  "E_rem": abs(r["E_rem_numeric"] - r["E_rem_closed"]),
                  "gap_gw": abs(r["gap_gw_numeric"] - r["gap_gw_closed"])}
        for k, x in checks.items():
            worst[k] = max(worst.get(k, 0.0), x)
        if U <= t:
            assert r["bound_gw_lower"] - 1e-12 <= r["err_gw"] <= r["bound_gw_upper"] + 1e-12, r
        print(f"t={t:<5} U={U:<5} exact={r['gap_exact_ED']:.12f} gw={r['gap_gw_numeric']:.12f} "
              f"hf={r['gap_hf']:.6f} err_gw={r['err_gw']:+.3e} err_hf={r['err_hf']:+.3e}")
    res["worst_abs_deviation"] = worst
    print("worst deviations:", json.dumps(worst))
    tol = {"ED_vs_closed": 1e-12, "Omega": 1e-9, "residue": 1e-5, "freq_integral": 1e-8,
           "E_rem": 1e-9, "gap_gw": 1e-9}
    ok = all(worst[k] <= tol[k] for k in tol)
    res["tolerances"] = tol
    res["ok"] = ok
    if res["symbolic"]:
        print("symbolic:", json.dumps(res["symbolic"], indent=1))
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print("ALL OK" if ok else "CROSS-CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

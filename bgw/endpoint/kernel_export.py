#!/usr/bin/env python3
"""G2 stage 1: export the eps^-1 certificate of cert.py for kernel checking.

    python3 bgw/endpoint/kernel_export.py RUNDIR [--npz OUT.npz] [--lean]
                                           [--only 0,1,2] [--block N]

Capture (no code copied from cert.py): `cert.epsinv_iv` is run unchanged on
each of the three q-points cert.py uses (q0 first, then the eps q-points).
During the call

  * `iv.inverse_cw` is wrapped: the wrapper reads, from the calling frame
    (`epsinv_iv`), the interval matrix `eps` and the balancing vector `s`
    exactly as cert.py computed them, and records the argument `epsb`;
  * `numpy.linalg.inv` is wrapped for the duration of the `inverse_cw` call so
    the approximate inverse `R` that inverse_cw used is recorded as returned
    (not recomputed);
  * the return value `inv` of `epsinv_iv` is the claimed enclosure of eps^-1.

Every float is an exact dyadic rational. For one matrix all entries are
written as integers over one common power of two 2^S (S = the largest
denominator exponent in the matrix), which is exact.

Hints (the kernel checks them, it does not trust them): with K fixed-point
bits, F >= |1 - R A'| (A' = balanced eps, exact interval), T0 >= F |R|,
T(k+1) >= F T(k) (k < 2), all rounded UP to multiples of 2^-K from exact
integer arithmetic here; tail >= beta^3 rho / (1 - beta). The Lean checker
(GW/Endpoint/Kernel/Check.lean) recomputes every product exactly and only
compares, so a wrong hint makes the check fail, never makes it pass.

`--lean` writes GW/Endpoint/Kernel/Data/Q{i}.lean (and Q{i}Rows.lean proofs).
`--block N` restricts every matrix to its leading N x N block (the claimed
enclosure is then recomputed for that block's own inverse by the same
inverse_cw; used only for scaling measurements).
"""
import argparse
import json
import math
import pathlib
import random
import sys
import time
from fractions import Fraction as Fr

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))

K = 128          # fixed-point bits of the hints
TERMS = 2        # inverse_cw default (cert.py calls inverse_cw(epsb))


# ------------------------------------------------------------------ capture

def capture(rundir, only=None):
    import cert
    import iv
    import spec
    run = spec.Run(rundir)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    out = []
    orig_cw = iv.inverse_cw
    for iq, (q, q0) in enumerate(qs):
        if only is not None and iq not in only:
            continue
        rec = {}

        def wrapped(A, terms=2, _rec=rec):
            fr = sys._getframe(1)
            assert fr.f_code is cert.epsinv_iv.__code__, "inverse_cw not called from epsinv_iv"
            eps, s = fr.f_locals["eps"], fr.f_locals["s"]
            _rec.update(eps_lo=eps.lo.copy(), eps_hi=eps.hi.copy(), s=np.array(s, dtype=float),
                        epsb_lo=A.lo.copy(), epsb_hi=A.hi.copy(), terms=terms)
            real_inv = np.linalg.inv

            def rinv(M):
                r = real_inv(M)
                _rec["R"] = np.array(r, copy=True)
                return r
            np.linalg.inv = rinv
            try:
                res = orig_cw(A, terms)
            finally:
                np.linalg.inv = real_inv
            _rec["invb_lo"], _rec["invb_hi"] = res[0].lo.copy(), res[0].hi.copy()
            _rec["beta"], _rec["Bmax"] = res[1], res[2]
            return res

        iv.inverse_cw = wrapped
        try:
            t0 = time.time()
            Gs, inv, beta, delta = cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, q0)
        finally:
            iv.inverse_cw = orig_cw
        rec.update(q=np.array(q, dtype=float), q0=q0, Gs=Gs, out_lo=inv.lo.copy(),
                   out_hi=inv.hi.copy(), seconds=time.time() - t0)
        print(f"q{iq} {tuple(q)} n={len(Gs)} beta={beta:.6g} B={delta:.3g} "
              f"({rec['seconds']:.1f}s)", flush=True)
        out.append((iq, rec))
    return out


# ------------------------------------------------------------- exact data

def dyadic_scale(a):
    """Smallest S >= 0 with every entry of a an integer multiple of 2^-S."""
    S = 0
    for x in np.asarray(a, dtype=float).ravel():
        _, d = float(x).as_integer_ratio()
        S = max(S, d.bit_length() - 1)
    return S


def to_int(a, S):
    res = []
    for row in np.asarray(a, dtype=float):
        r = []
        for x in row:
            p, d = float(x).as_integer_ratio()
            e = d.bit_length() - 1
            assert d == 1 << e and e <= S
            r.append(p << (S - e))
        res.append(r)
    return res


def ceil_shift(x, d):
    """ceil(x / 2^d) for integer x >= 0, d >= 0."""
    return -((-x) >> d)


def hints(eps_lo, SE, eps_hi, f, R, SR, n):
    """Exact integer computation of the hint matrices, following the Lean
    checker's formulas (`Cert.chkE`, `Cert.chkMul`, `Cert.chkGlobal`)."""
    G = max(f)
    S1 = SR + SE + G + 1
    mid = [[eps_lo[k][j] + eps_hi[k][j] for j in range(n)] for k in range(n)]
    rad = [[eps_hi[k][j] - eps_lo[k][j] for j in range(n)] for k in range(n)]
    F = []
    for i in range(n):
        c = [R[i][k] << (G - f[k]) for k in range(n)]
        X, Y = [0] * n, [0] * n
        for k in range(n):
            ck, ak = c[k], abs(c[k])
            mk, rk = mid[k], rad[k]
            for j in range(n):
                X[j] += ck * mk[j]
                Y[j] += ak * rk[j]
        row = []
        for j in range(n):
            d = (1 << S1) if i == j else 0
            v = abs(d - (X[j] << f[j])) + (Y[j] << f[j])      # >= 2^S1 |E0_ij|
            row.append(ceil_shift(v << K, S1))
        F.append(row)
    absR = [[abs(x) for x in r] for r in R]

    def mul_up(Fm, Y, SY):
        """ceil(F Y) with F at scale K, Y at scale SY; result at scale K."""
        res = []
        for i in range(n):
            acc = [0] * n
            for k in range(n):
                fk = Fm[i][k]
                if fk:
                    yk = Y[k]
                    for j in range(n):
                        acc[j] += fk * yk[j]
            res.append([ceil_shift(x, SY) for x in acc])
        return res
    T = [mul_up(F, absR, SR)]
    for _ in range(TERMS):
        T.append(mul_up(F, T[-1], K))
    beta = max(sum(r) for r in F)
    rho = max(sum(r) for r in T[0])
    # tail >= beta^(m+1) rho / (1 - beta), all at scale K:
    # tail (2^K - beta) 2^(K m) >= beta^(m+1) rho
    one_k = 1 << K
    assert beta < one_k
    num = beta ** (TERMS + 1) * rho
    den = (one_k - beta) << (K * TERMS)
    tail = -((-num) // den)
    M = max(max(abs(x) for x in r) for r in mid)
    MR = max(abs(R[i][k] << (G - f[k])) for i in range(n) for k in range(n))
    mid2 = [[x + M for x in r] for r in mid]
    colM = [sum(mid2[k][j] for k in range(n)) for j in range(n)]
    return dict(F=F, T=T, beta=beta, rho=rho, tail=tail, M=M, MR=MR, mid2=mid2, rad2=rad,
                colM=colM, Rabs=absR)


# -------------------------------------------------------------- Lean text

def lit_int(x):
    return f"(.ofNat {x})" if x >= 0 else f"(.negSucc {-x - 1})"


def lean_list(items):
    """`a :: b :: … :: []`: the `[a, b, …]` macro elaborates long lists into
    nested `let`s, which the kernel re-instantiates on every unfolding."""
    return "(" + " :: ".join(items) + " :: [])"


def lean_mat(name, M, ty):
    """One definition per row (a single huge literal parses quadratically:
    27 s for one 76 x 76 matrix, against 3 s row by row)."""
    lit = lit_int if ty == "Int" else str
    out = [f"noncomputable def {name}_{i} : List {ty} := " + lean_list([lit(x) for x in r])
           for i, r in enumerate(M)]
    out.append(f"noncomputable def {name} : List (List {ty}) :=\n  "
               + lean_list([f"{name}_{i}" for i in range(len(M))]))
    return "\n".join(out) + "\n"


def lean_data(iq, rec, n):
    s = rec["s"][:n]
    e = [int(round(math.log2(x))) for x in s]
    assert all(2.0 ** ei == x for ei, x in zip(e, s))
    emin = min(e)
    f = [ei - emin for ei in e]                    # s_i = 2^emin * 2^f_i; only ratios matter
    lo, hi = rec["eps_lo"][:n, :n], rec["eps_hi"][:n, :n]
    R = rec["R"]
    olo, ohi = rec["out_lo"], rec["out_hi"]
    SE = max(dyadic_scale(lo), dyadic_scale(hi))
    SR = dyadic_scale(R)
    SO = max(dyadic_scale(olo), dyadic_scale(ohi))
    Elo, Ehi, Ri = to_int(lo, SE), to_int(hi, SE), to_int(R, SR)
    Olo, Ohi = to_int(olo, SO), to_int(ohi, SO)
    t0 = time.time()
    h = hints(Elo, SE, Ehi, f, Ri, SR, n)
    th = time.time() - t0
    ns = f"GW.Endpoint.Kernel.Q{iq}"
    parts = [f"/-\nGenerated by bgw/endpoint/kernel_export.py (do not edit).\n"
             f"q = {rec['q'].tolist()}, n = {n}; eps, R, out are cert.py's floats, exact.\n"
             f"Hints at scale 2^-{K} (checked by the kernel, not trusted).\n-/\n"
             f"import GW.Endpoint.Kernel.Check\n\nnamespace {ns}\nopen GW.Endpoint.Kernel\n\n"]
    parts.append(f"noncomputable def f : List Nat := {lean_list([str(x) for x in f])}\n")
    parts.append(f"noncomputable def colM : List Nat := {lean_list([str(x) for x in h['colM']])}\n")
    for name, M_, ty in [("epsLo", Elo, "Int"), ("epsHi", Ehi, "Int"), ("mid2", h["mid2"], "Nat"),
                         ("rad2", h["rad2"], "Nat"), ("R", Ri, "Int"), ("Rabs", h["Rabs"], "Nat"),
                         ("outLo", Olo, "Int"), ("outHi", Ohi, "Int"), ("F", h["F"], "Nat"),
                         ("T0", h["T"][0], "Nat"), ("T1", h["T"][1], "Nat"), ("T2", h["T"][2], "Nat")]:
        parts.append(lean_mat(name, M_, ty))
    parts.append(
        f"noncomputable def cert : Cert where\n  n := {n}\n  K := {K}\n  SE := {SE}\n  SR := {SR}\n"
        f"  SO := {SO}\n  G := {max(f)}\n  M := {h['M']}\n  MR := {h['MR']}\n  f := f\n"
        f"  epsLo := epsLo\n  epsHi := epsHi\n  mid2 := mid2\n  rad2 := rad2\n  colM := colM\n"
        f"  R := R\n  Rabs := Rabs\n  outLo := outLo\n  outHi := outHi\n  F := F\n  T0 := T0\n"
        f"  T1 := T1\n  T2 := T2\n  beta := {h['beta']}\n  rho := {h['rho']}\n  tail := {h['tail']}\n"
        f"\nend {ns}\n")
    beta, rho, tail = h["beta"], h["rho"], h["tail"]
    info = dict(n=n, SE=SE, SR=SR, SO=SO, K=K, G=max(f), hint_seconds=th,
                beta=beta / 2 ** K, rho=rho / 2 ** K, tail=tail / 2 ** K)
    return "\n".join(parts), info


CHUNK = 6   # rows per kernel-check module (memory grows ~0.2-0.3 GB per row in one process)


def lean_proof(iq, n, name):
    """The kernel checks of one certificate: one `decide +kernel` theorem per
    row and check, in modules of CHUNK rows chained by imports (so they build
    one at a time and each process stays at a few GB), then a collector module
    with `cert.Valid` and the enclosure theorem. Returns {module: text}."""
    ns = f"GW.Endpoint.Kernel.{name}"
    checks = [("e", "cert.chkE {i}"), ("m0", "cert.chkMul cert.SR cert.Rabs cert.T0 {i}"),
              ("m1", "cert.chkMul cert.K cert.T0 cert.T1 {i}"),
              ("m2", "cert.chkMul cert.K cert.T1 cert.T2 {i}"), ("r", "cert.chkRow {i}")]
    files = {}
    prev = f"GW.Endpoint.Kernel.Data.{name}"
    starts = list(range(0, n, CHUNK))
    for c, a in enumerate(starts):
        mod = f"{name}R{c}"
        L = [f"/- Generated by bgw/endpoint/kernel_export.py (do not edit): kernel checks of rows "
             f"{a}..{min(a + CHUNK, n) - 1} of `{ns}.cert`. -/",
             f"import {prev}\n", f"namespace {ns}\nopen GW.Endpoint.Kernel\n"]
        if c == 0:
            L.append("theorem g : cert.chkGlobal = true := by decide +kernel")
        for i in range(a, min(a + CHUNK, n)):
            for tag, t in checks:
                L.append(f"theorem {tag}_{i} : {t.format(i=i)} = true := by decide +kernel")
        L.append(f"\nend {ns}\n")
        files[mod] = "\n".join(L)
        prev = f"GW.Endpoint.Kernel.Data.{mod}"
    L = [f"/-\nGenerated by bgw/endpoint/kernel_export.py (do not edit): the eps⁻¹ enclosure at\n"
         f"q-point {iq} (n = {n}), from the kernel-checked rows and `Cert.sound`.\n-/",
         f"import {prev}\nimport GW.Endpoint.Kernel.Sound\n",
         f"namespace {ns}\nopen GW.Endpoint.Kernel\n",
         "theorem rows : ∀ i < cert.n, cert.chkE i = true ∧ cert.chkMul cert.SR cert.Rabs cert.T0 i = true ∧\n"
         "    cert.chkMul cert.K cert.T0 cert.T1 i = true ∧ cert.chkMul cert.K cert.T1 cert.T2 i = true ∧\n"
         "    cert.chkRow i = true := by\n  show ∀ i < " + str(n) + ", _\n  exact"]
    term = "(forall_lt_zero _)"
    for i in range(n):
        term = f"(forall_lt_succ_of (k := {i}) {term} ⟨e_{i}, m0_{i}, m1_{i}, m2_{i}, r_{i}⟩)"
    L.append("    " + term + "\n")
    L.append("theorem valid : cert.Valid := ⟨g, rows⟩\n")
    L.append(f"/-- **Kernel-checked eps⁻¹ enclosure, q-point {iq}** (n = {n}): every real matrix in\n"
             f"cert.py's interval matrix `eps` is invertible and its inverse lies entrywise in\n"
             f"cert.py's claimed enclosure `inv` (all data exact dyadics of cert.py's floats). -/\n"
             f"theorem epsinv_enclosure_q{iq} (A0 : Matrix (Fin cert.n) (Fin cert.n) ℝ)\n"
             f"    (hA : ∀ i j, A0 i j ∈ Set.Icc (cert.mat cert.SE cert.epsLo i j)\n"
             f"      (cert.mat cert.SE cert.epsHi i j)) :\n"
             f"    IsUnit A0 ∧ ∀ i j, A0⁻¹ i j ∈ Set.Icc (cert.mat cert.SO cert.outLo i j)\n"
             f"      (cert.mat cert.SO cert.outHi i j) :=\n  cert.sound valid A0 hA\n")
    L.append(f"end {ns}\n")
    files[f"{name}Check"] = "\n".join(L)
    return files


def block_rec(rec, N):
    """Leading N x N block with its own inverse_cw enclosure (scaling runs)."""
    import iv
    from iv import I
    s = rec["s"][:N]
    lo, hi = rec["eps_lo"][:N, :N], rec["eps_hi"][:N, :N]
    eps = I(lo, hi)
    scale = s[None, :] / s[:, None]
    epsb = eps * I.exact(scale)
    real_inv, box = np.linalg.inv, {}

    def rinv(M):
        box["R"] = real_inv(M)
        return box["R"]
    np.linalg.inv = rinv
    try:
        invb, _, _ = iv.inverse_cw(epsb)
    finally:
        np.linalg.inv = real_inv
    inv = invb * I.exact(s[:, None] / s[None, :])
    r = dict(rec)
    r.update(eps_lo=lo, eps_hi=hi, s=s, R=box["R"], out_lo=inv.lo, out_hi=inv.hi)
    return r


# ================================================================ stage 2
#
# G2 stage 2: the eps interval itself from the wavefunction coefficients.
#
# Capture (no code copied from cert.py): `cert.epsinv_iv` is run unchanged on one
# q-point. `cert.mtxel_iv` is wrapped; each call records its arguments exactly as
# cert.py passes them -- (Gv, cv[:nv]) the valence G-vectors/coefficients at k+q,
# (Gc, cc[nv:nbands]) the conduction ones at k, Gout = the sphere Gs -- and reads
# from the calling frame the energies Ev[:nv], Ec[nv:nbands] and the k-point.
# `iv.inverse_cw` is wrapped to read `er` (bdot, celvol, the 32-point kfull), `q`
# and `Gs`. The symmetry unfolding (`cert.real_coeffs`, `spec.Wfn.find`, the
# per-G signs, `EpsilonRun.kfull`) is therefore Python's: a recorded trust gap.
#
# Hints (checked by the kernel, never trusted): m_vc(G_j) = the exact integer
# pair density at scale 2^-(2 SC), one list of n per (k, v, c).

EPS_SD = 64      # bits of 1/(E_c - E_v)
EPS_SU = 128     # bits of v(q+G) * 4/(N_k Omega)


def capture_eps(rundir, iq):
    import cert
    import iv
    import spec
    run = spec.Run(rundir)
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    q, q0 = qs[iq]
    rec = {"pairs": [], "q0": q0}
    orig_m, orig_cw = cert.mtxel_iv, iv.inverse_cw

    def wm(Gk, ck, Gq, cq, Gout):
        fr = sys._getframe(1)
        assert fr.f_code is cert.epsinv_iv.__code__, "mtxel_iv not called from epsinv_iv"
        L = fr.f_locals
        nv, nb = L["nv"], L["nbands"]
        assert ck.shape[0] == nv and cq.shape[0] == nb - nv
        rec["pairs"].append(dict(k=np.array(L["k"], dtype=float), Gv=np.array(Gk), cv=np.array(ck),
                                 Gc=np.array(Gq), cc=np.array(cq), Gout=np.array(Gout),
                                 Ev=np.array(L["Ev"][:nv], dtype=float),
                                 Ec=np.array(L["Ec"][nv:nb], dtype=float)))
        return orig_m(Gk, ck, Gq, cq, Gout)

    def wc(A, terms=2):
        fr = sys._getframe(1)
        assert fr.f_code is cert.epsinv_iv.__code__
        L = fr.f_locals
        rec.update(eps_lo=L["eps"].lo.copy(), eps_hi=L["eps"].hi.copy(),
                   bdot=np.array(L["er"].cr.bdot, dtype=float), celvol=float(L["er"].cr.celvol),
                   nk=len(L["er"].kfull), Gs=np.array(L["Gs"]), q=np.array(L["q"], dtype=float))
        return orig_cw(A, terms)

    cert.mtxel_iv, iv.inverse_cw = wm, wc
    try:
        cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, q0)
    finally:
        cert.mtxel_iv, iv.inverse_cw = orig_m, orig_cw
    assert len(rec["pairs"]) == rec["nk"]
    for p in rec["pairs"]:
        assert np.array_equal(p["Gout"], rec["Gs"])
    return rec


def _dexp(x):
    _, d = float(x).as_integer_ratio()
    e = d.bit_length() - 1
    assert d == 1 << e
    return e


def _dint(x, S):
    p, d = float(x).as_integer_ratio()
    e = d.bit_length() - 1
    assert d == 1 << e and e <= S
    return p << (S - e)


def _pair_density(Gv, cv, Gc, cc, Gs):
    """Exact integer m_vc(G) = sum_{Gv_i - Gc_j = G} cv_vi cc_cj (the definition
    `GW.Endpoint.Kernel.Eps.Mint`), independent of the Lean packing."""
    idx = {tuple(int(x) for x in g): i for i, g in enumerate(Gv)}
    Gc_t = [tuple(int(x) for x in g) for g in Gc]
    out = []
    for v in range(len(cv)):
        rows = []
        for c in range(len(cc)):
            m = []
            for G in Gs:
                s = 0
                for j, g2 in enumerate(Gc_t):
                    i = idx.get((g2[0] + int(G[0]), g2[1] + int(G[1]), g2[2] + int(G[2])))
                    if i is not None:
                        s += cv[v][i] * cc[c][j]
                m.append(s)
            rows.append(m)
        out.append(rows)
    return out


def eps_data(rec, SD=EPS_SD):
    """Exact integer data, hints and checker parameters of one q-point."""
    P = rec["pairs"]
    Gs = [tuple(int(x) for x in g) for g in rec["Gs"]]
    SC = max(_dexp(x) for p in P for a in (p["cv"], p["cc"]) for x in a.ravel())
    SEn = max(_dexp(x) for p in P for a in (p["Ev"], p["Ec"]) for x in a)
    SB = max(_dexp(x) for x in rec["bdot"].ravel())
    SOm = _dexp(rec["celvol"])
    SQ = max(_dexp(x) for x in rec["q"])
    ks = []
    for p in P:
        ks.append(dict(Gv=[tuple(int(x) for x in g) for g in p["Gv"]],
                       cv=[[_dint(x, SC) for x in r] for r in p["cv"]],
                       Ev=[_dint(x, SEn) for x in p["Ev"]],
                       Gc=[tuple(int(x) for x in g) for g in p["Gc"]],
                       cc=[[_dint(x, SC) for x in r] for r in p["cc"]],
                       Ec=[_dint(x, SEn) for x in p["Ec"]]))
    for k in ks:   # distinct G-vectors: then cert.py's dict lookup in mtxel_iv is the sum of Mint
        assert len(set(k["Gv"])) == len(k["Gv"]) and len(set(k["Gc"])) == len(k["Gc"])
    assert len(set(Gs)) == len(Gs)
    comps = [x for k in ks for g in k["Gv"] + k["Gc"] for x in g]
    lo, hi = min(comps), max(comps)
    H = hi - lo
    assert all(abs(x) <= H for g in Gs for x in g)
    L = 2 * H + 1
    W = 2
    for k in ks:
        for a in k["cv"]:
            for b in k["cc"]:
                W = max(W, (sum(map(abs, a)) * sum(map(abs, b))).bit_length() + 1)
    hints = [_pair_density(k["Gv"], k["cv"], k["Gc"], k["cc"], Gs) for k in ks]
    Mmax = max(abs(x) for h in hints for hv in h for m in hv for x in m)
    SDE = SD + SEn
    sumD = sum((1 << SDE) // (ec - ev) for k in ks for ev in k["Ev"] for ec in k["Ec"])
    W2 = (sumD * Mmax * Mmax).bit_length() + 1
    return dict(Gs=Gs, SC=SC, SEn=SEn, SB=SB, SOm=SOm, SQ=SQ,
                qn=tuple(_dint(x, SQ) for x in rec["q"]),
                B=[[_dint(x, SB) for x in r] for r in rec["bdot"]], Om=_dint(rec["celvol"], SOm),
                ks=ks, hints=hints, cfg=dict(L=L, lo=lo, H=H, W=W, W2=W2, SD=SD, SU=EPS_SU,
                                              Mmax=Mmax), nk=rec["nk"])


def simulate_chi(d, eps_lo, eps_hi, SE):
    """Python mirror of `Eps.chiOK` (exact integers): returns the number of
    entries outside the stage-1 box and the smallest relative margin."""
    from fractions import Fraction as Fr
    cf, Gs, n = d["cfg"], d["Gs"], len(d["Gs"])
    SDE = cf["SD"] + d["SEn"]
    X = [[0] * n for _ in range(n)]
    cnt = 0
    for k, h in zip(d["ks"], d["hints"]):
        for ev, hv in zip(k["Ev"], h):
            for ec, m in zip(k["Ec"], hv):
                D = (1 << SDE) // (ec - ev)
                cnt += 1
                for i in range(n):
                    a = D * m[i]
                    if a:
                        Xi = X[i]
                        for j in range(n):
                            Xi[j] += a * m[j]
    E = cnt * cf["Mmax"] ** 2
    P = cf["SU"] + cf["SD"] + 4 * d["SC"]
    bad, marg = 0, None
    for i in range(n):
        s = 1 << d["SQ"]
        w = [Gs[i][a] * s + d["qn"][a] for a in range(3)]
        N = sum(w[a] * d["B"][a][b] * w[b] for a in range(3) for b in range(3))
        den = 10 ** 20 * d["nk"] * d["Om"] * N
        num = 32 << (d["SOm"] + 2 * d["SQ"] + d["SB"] + cf["SU"])
        ulo, uhi = num * 314159265358979323846 // den, num * 314159265358979323847 // den + 1
        for j in range(n):
            dl = Fr(1 if i == j else 0)
            el = dl + min(Fr(ulo * (X[i][j] - E), 2 ** P), Fr(uhi * (X[i][j] - E), 2 ** P))
            eh = dl + max(Fr(ulo * (X[i][j] + E), 2 ** P), Fr(uhi * (X[i][j] + E), 2 ** P))
            lo, hi = Fr(eps_lo[i][j], 2 ** SE), Fr(eps_hi[i][j], 2 ** SE)
            if not (lo <= el and eh <= hi):
                bad += 1
            elif hi > lo:
                m_ = min(el - lo, hi - eh) / (hi - lo)
                marg = m_ if marg is None else min(marg, m_)
    return bad, (None if marg is None else float(marg))


def _lv(g):
    return f"({lit_int(g[0])}, {lit_int(g[1])}, {lit_int(g[2])})"


def lit_z(x):
    """An integer literal as `odd <<< t`. Measured: the Lean 4.19 kernel's cache
    keys of literals that agree in their low 64 bits collide (every term with
    ≥ 64 trailing zero bits hashes alike), which made one check over 16 lists of
    such numbers 27x slower (3.1 s vs 0.11 s). Writing the odd part as the literal
    keeps the low limbs distinct; the value is the same integer (`Eps.zp`, `Eps.zn`;
a function application elaborates ~5x faster than `m <<< t`)."""
    if x == 0:
        return "(.ofNat 0)"
    a = abs(x)
    t = (a & -a).bit_length() - 1
    m = a >> t
    return f"(zp {m} {t})" if x > 0 else f"(zn {m} {t})"


def lean_eps(iq, d, stage1, outdir, per_module=2, chains=2, rows=19, rchains=1):
    """Write Data/E{iq}Cfg.lean (global data), Data/E{iq}K{m}.lean (k-point data,
    hints and one `kOK` theorem per k, `per_module` k-points per module, in
    `chains` import chains), Data/E{iq}Inp.lean (the `Input`, the hint table, the
    row-independent check), Data/E{iq}R{c}.lean (the chi/eps check of `rows` rows
    against the stage-1 box of Data/Q{iq}) and Data/E{iq}Check.lean (the composed
    theorems)."""
    od = pathlib.Path(outdir)
    ns = f"GW.Endpoint.Kernel.E{iq}"
    cf = d["cfg"]
    head = (f"/- Generated by bgw/endpoint/kernel_export.py --eps {iq} (do not edit).\n"
            f"q = {stage1['q']}, n = {len(d['Gs'])}. Coefficients, energies, bdot, celvol and\n"
            f"q are cert.py's floats, exact; the hints `H*` are checked, not trusted. -/\n")
    files = {}
    # build order (memory): stage 1 first, then q0, q1, q2 one after another; inside a
    # q-point two k-point chains (~3.3 GB each), then one chain of row blocks (~7 GB)
    after = {0: [f"GW.Endpoint.Kernel.Data.Q{i}Check" for i in range(3)]}.get(
        iq, [f"GW.Endpoint.Kernel.Data.E{iq - 1}Check"])
    files[f"E{iq}Cfg"] = (head + "import GW.Endpoint.Kernel.EpsCheck\n" +
        "".join(f"import {m}\n" for m in after) + "\n"
        f"namespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n\n"
        f"noncomputable def Gs : List V3 := {lean_list([_lv(g) for g in d['Gs']])}\n\n"
        f"/-- Checker parameters (they do not enter any statement). -/\n"
        f"noncomputable def cf : Cfg where\n  L := {cf['L']}\n  lo := {lit_int(cf['lo'])}\n"
        f"  H := {cf['H']}\n  W := {cf['W']}\n  W2 := {cf['W2']}\n  SD := {cf['SD']}\n"
        f"  SU := {cf['SU']}\n  Mmax := {cf['Mmax']}\n\nend {ns}\n")
    nk = len(d["ks"])
    groups = [list(range(a, min(a + per_module, nk))) for a in range(0, nk, per_module)]
    prev = [f"GW.Endpoint.Kernel.Data.E{iq}Cfg"] * chains
    ends = []
    for gi, grp in enumerate(groups):
        ch = gi % chains
        mod = f"E{iq}K{gi}"
        L = [head + f"import {prev[ch]}\n", f"namespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n"]
        for t in grp:
            k, h = d["ks"][t], d["hints"][t]
            L.append(f"noncomputable def k{t}Gv : List V3 := {lean_list([_lv(g) for g in k['Gv']])}")
            L.append(f"noncomputable def k{t}Gc : List V3 := {lean_list([_lv(g) for g in k['Gc']])}")
            for v, r in enumerate(k["cv"]):
                L.append(f"noncomputable def k{t}v{v} : List ℤ := {lean_list([lit_z(x) for x in r])}")
            for c, r in enumerate(k["cc"]):
                L.append(f"noncomputable def k{t}c{c} : List ℤ := {lean_list([lit_z(x) for x in r])}")
            L.append(f"noncomputable def k{t} : KPair where\n  Gv := k{t}Gv\n"
                     f"  cv := {lean_list([f'k{t}v{v}' for v in range(len(k['cv']))])}\n"
                     f"  Ev := {lean_list([lit_z(x) for x in k['Ev']])}\n  Gc := k{t}Gc\n"
                     f"  cc := {lean_list([f'k{t}c{c}' for c in range(len(k['cc']))])}\n"
                     f"  Ec := {lean_list([lit_z(x) for x in k['Ec']])}")
            for v, hv in enumerate(h):
                for c, m in enumerate(hv):
                    L.append(f"noncomputable def H{t}_{v}_{c} : List ℤ := {lean_list([lit_z(x) for x in m])}")
                L.append(f"noncomputable def H{t}_{v} : List (List ℤ) := "
                         f"{lean_list([f'H{t}_{v}_{c}' for c in range(len(hv))])}")
            L.append(f"noncomputable def H{t} : List (List (List ℤ)) := "
                     f"{lean_list([f'H{t}_{v}' for v in range(len(h))])}")
            L.append(f"theorem kok{t} : kOK cf Gs k{t} H{t} = true := by decide +kernel\n")
        L.append(f"end {ns}\n")
        files[mod] = "\n".join(L)
        prev[ch] = f"GW.Endpoint.Kernel.Data.{mod}"
    B = d["B"]
    n = len(d["Gs"])
    imports = "\n".join(f"import {m}" for m in sorted(set(prev))) + f"\nimport GW.Endpoint.Kernel.Data.Q{iq}\n"
    files[f"E{iq}Inp"] = (head + imports + f"\nnamespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n\n"
        f"/-- The exact input data of q-point {iq}. -/\n"
        f"noncomputable def inp : Input where\n  SC := {d['SC']}\n  SEn := {d['SEn']}\n  SB := {d['SB']}\n"
        f"  SOm := {d['SOm']}\n  SQ := {d['SQ']}\n  qn := {_lv(d['qn'])}\n"
        f"  B := {lean_list([lean_list([lit_int(x) for x in r]) for r in B])}\n  Om := {d['Om']}\n"
        f"  Gs := Gs\n  ks := {lean_list([f'k{t}' for t in range(nk)])}\n\n"
        f"/-- The hints `H t v c j = m_vc(k_t, G_j)`. -/\n"
        f"noncomputable def H : List (List (List (List ℤ))) := {lean_list([f'H{t}' for t in range(nk)])}\n\n"
        f"theorem glob : chiGlobal cf inp H = true := by decide +kernel\n\nend {ns}\n")
    chunks = [(a, min(rows, n - a)) for a in range(0, n, rows)]
    prevr = [f"GW.Endpoint.Kernel.Data.E{iq}Inp"] * rchains
    for ci, (a, L) in enumerate(chunks):
        ch = ci % rchains
        mod = f"E{iq}R{ci}"
        files[mod] = (head + f"import {prevr[ch]}\n\nnamespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n\n"
            f"theorem rows{ci} : chiRows cf inp H Q{iq}.cert.SE Q{iq}.cert.epsLo Q{iq}.cert.epsHi {a} {L} = true := by\n"
            f"  decide +kernel\n\nend {ns}\n")
        prevr[ch] = f"GW.Endpoint.Kernel.Data.{mod}"
    # the composed theorems
    kterm = "(forall_lt_zero _)"
    for t in range(nk):
        kterm = f"(forall_lt_succ_of (k := {t}) {kterm} kok{t})"
    cases = []
    for ci, (a, L) in enumerate(chunks):
        cases.append((a, L, ci))
    split = " ∨ ".join(f"({a} ≤ i ∧ i < {a + L})" for a, L, _ in cases)
    arms = []
    for a, L, ci in cases:
        arms.append(f"  · have h := sound_rows hk glob rows{ci} (i - {a}) (by omega) j hj\n"
                    f"    rwa [show {a} + (i - {a}) = i by omega] at h")
    L_ = [head + "\n".join(f"import {m}" for m in sorted(set(prevr))) +
          f"\nimport GW.Endpoint.Kernel.EpsSound\nimport GW.Endpoint.Kernel.Data.Q{iq}Check\n",
          f"namespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n",
          "/-- Every k-point's pair densities are the hints (kernel-checked, one theorem per k). -/",
          "theorem kall : ∀ t < inp.ks.length, kOK cf inp.Gs (inp.ks.getD t default) (H.getD t []) = true := by",
          f"  show ∀ t < {nk}, _\n  exact {kterm}\n",
          f"theorem Gs_length : inp.Gs.length = {n} := by decide +kernel\n",
          f"/-- **The true static RPA eps of q-point {iq} lies in stage 1's box**: every entry of\n"
          f"`epsR inp` (the real dielectric matrix of spec A computed from the unfolded\n"
          f"wavefunction coefficients, `EpsSpec.lean`) is in `[epsLo, epsHi] / 2^SE` of `Q{iq}.cert`. -/",
          f"theorem eps_in_box : ∀ i < inp.Gs.length, ∀ j < inp.Gs.length,\n"
          f"    ((ent Q{iq}.cert.epsLo i j : ℤ) : ℝ) / 2 ^ Q{iq}.cert.SE ≤ epsR inp i j ∧\n"
          f"      epsR inp i j ≤ ((ent Q{iq}.cert.epsHi i j : ℤ) : ℝ) / 2 ^ Q{iq}.cert.SE := by\n"
          f"  intro i hi j hj\n  have hk := kall\n  rw [Gs_length] at hi\n"
          f"  rcases (by omega : {split}) with {' | '.join('h' for _ in cases)}\n" + "\n".join(arms) + "\n",
          f"/-- The true eps of q-point {iq} as a matrix on stage 1's index set. -/",
          f"noncomputable def epsTrue : Matrix (Fin Q{iq}.cert.n) (Fin Q{iq}.cert.n) ℝ :=\n"
          f"  Matrix.of fun i j => epsR inp i j\n",
          f"theorem n_eq : Q{iq}.cert.n = inp.Gs.length := by rw [Gs_length]; rfl\n",
          f"theorem epsTrue_mem : ∀ i j, epsTrue i j ∈ Set.Icc (Q{iq}.cert.mat Q{iq}.cert.SE Q{iq}.cert.epsLo i j)\n"
          f"    (Q{iq}.cert.mat Q{iq}.cert.SE Q{iq}.cert.epsHi i j) := fun i j =>\n"
          f"  eps_in_box i (n_eq ▸ i.2) j (n_eq ▸ j.2)\n",
          f"/-- **Kernel-checked eps⁻¹ enclosure of the true eps, q-point {iq}** (n = {n}): the static\n"
          f"RPA dielectric matrix computed from the wavefunction coefficients is invertible and\n"
          f"its inverse lies entrywise in cert.py's enclosure `Q{iq}.cert.outLo/outHi`. -/",
          f"theorem epsinv_true_q{iq} : IsUnit epsTrue ∧ ∀ i j, epsTrue⁻¹ i j ∈\n"
          f"    Set.Icc (Q{iq}.cert.mat Q{iq}.cert.SO Q{iq}.cert.outLo i j) (Q{iq}.cert.mat Q{iq}.cert.SO Q{iq}.cert.outHi i j) :=\n"
          f"  Q{iq}.epsinv_enclosure_q{iq} epsTrue epsTrue_mem\n",
          f"end {ns}\n"]
    files[f"E{iq}Check"] = "\n".join(L_)
    # negative controls: one flipped bit of one wavefunction coefficient (the hints of
    # that k-point no longer match), and a collapsed box (the enclosure cannot fit)
    k0 = d["ks"][0]
    x = k0["cc"][0][0]
    b = max(abs(x).bit_length() - 20, 0)
    flipped = [x ^ (1 << b)] + k0["cc"][0][1:]
    assert flipped[0] != x
    files[f"E{iq}Tamper"] = (head + f"import GW.Endpoint.Kernel.Data.E{iq}Check\n\n"
        f"namespace {ns}\nopen GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps\n\n"
        f"/-- Conduction coefficient 0 of band 0 at k-point 0 with bit {b} flipped. -/\n"
        f"noncomputable def k0c0flip : List ℤ := {lean_list([lit_z(v) for v in flipped])}\n\n"
        f"/-- The flipped coefficient is rejected: the kernel proves the k-point check `false`. -/\n"
        f"theorem tamper_coef : kOK cf Gs {{ k0 with cc := k0c0flip :: k0.cc.tail }} H0 = false := by\n"
        f"  decide +kernel\n\n"
        f"/-- The untampered k-point passes with the same hints (control for `tamper_coef`). -/\n"
        f"theorem control_coef : kOK cf Gs {{ k0 with cc := k0c0 :: k0.cc.tail }} H0 = true := by\n"
        f"  decide +kernel\n\n"
        f"/-- A box collapsed to its upper ends cannot contain the enclosure: row 0 is rejected. -/\n"
        f"theorem tamper_box : chiRows cf inp H Q{iq}.cert.SE Q{iq}.cert.epsHi Q{iq}.cert.epsHi 0 1 = false := by\n"
        f"  decide +kernel\n\nend {ns}\n")
    for old in od.glob(f"E{iq}*.lean"):
        old.unlink()
    for mod, text in files.items():
        (od / f"{mod}.lean").write_text(text)
    return list(files), len(groups)



# ================================================================ stage 3
#
# G2 stage 3: spec A's linearised QP energies Eqp1(X), Eqp1(L) and O1 on the TRUE
# eps^-1 (stage 1 + 2), from the unfolded wavefunction coefficients.
#
# Capture (no code copied from cert.py): cert.py's own flow (`epsinv_iv` for the three
# blocks, then `SigmaIV.parts` for X (bands 5, 6) and L (band 5) with the production op
# rule) is run unchanged. `cert.mtxel_iv` is wrapped: each call records its arguments
# exactly as cert.py passes them -- from `SigmaIV.prepare` (Gk, ck[bands], Gch) and from
# `SigmaIV.qpart` (Gk, ck, Gq, cq[:nocc], Gb) and (Gk, ck, Gq, cq[:nbands], Gs) -- and
# reads the energies (Ek, Eq) and q from the calling frame. `SigmaIV.eps_at` is wrapped
# to record the symmetry map of the sphere at q onto its irreducible block
# (`Screening.mapping`: block, row indices, relative signs +-1, wing index). The
# unfolding (`real_coeffs`, `spec.Wfn.find`, `Screening.mapping`) is therefore Python's:
# a recorded trust gap, as in stage 2. cert.py's own interval results (modes, parts,
# Eqp1) are recorded only to cross-check the exact recomputation below.

SIG_STATES = (("X", 2, (5, 6)), ("L", 1, (5,)))     # (name, sigma.inp k index, bands)


def capture_sigma(rundir):
    import bgwio
    import cert
    import spec
    run = spec.Run(rundir)
    rho = bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    coul = cert.CertCoulomb(str(HERE / "data/coulomb_cert.json"))
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    blocks, st1 = [], []
    for q, q0 in qs:
        Gs, E, _, _ = cert.epsinv_iv(rundir, run.nbands, run.ecuts, q, q0)
        blocks.append((Gs, E))
        st1.append(dict(q=np.array(q, dtype=float), Gs=np.array(Gs), out_lo=E.lo.copy(),
                        out_hi=E.hi.copy()))
    sig = cert.SigmaIV(run, coul, blocks, rho)
    rec = dict(stage1=st1, rho_G=np.array(rho["gvec"]), rho=np.array(rho["rho"], dtype=float),
               bdot=np.array(run.cr.bdot, dtype=float), celvol=float(run.cr.celvol),
               nq=len(run.qlist), nbands=run.nbands, nocc=run.nocc, ecuts=float(run.ecuts),
               ecutb=float(run.ecutb), qlist=[np.array(q, dtype=float) for q in run.qlist],
               states=[])
    cur = {}
    orig_m, orig_e = cert.mtxel_iv, cert.SigmaIV.eps_at

    def wm(Gk, ck, Gq, cq, Gout):
        fr = sys._getframe(1)
        L = fr.f_locals
        if fr.f_code is cert.SigmaIV.prepare.__code__:
            nb = np.array(L["bands"]) - 1
            cur["prep"] = dict(Gk=np.array(Gk), ck=np.array(ck), Gch=np.array(Gout),
                               Ek=np.array(L["Ek"][nb], dtype=float), bands=list(L["bands"]))
            assert np.array_equal(Gk, Gq) and np.array_equal(ck, cq)
        elif fr.f_code is cert.SigmaIV.qpart.__code__:
            q = tuple(float(x) for x in L["q"])
            d = cur["q"].setdefault(q, {})
            if "Gb" not in d:
                assert Gout is L["Gb"] and cq.shape[0] == run.nocc
                d.update(Gb=np.array(Gout), Gq=np.array(Gq), Eq=np.array(L["Eq"][:run.nbands], dtype=float))
            else:
                assert Gout is L["Gs"] and cq.shape[0] == run.nbands
                assert np.array_equal(Gq, d["Gq"])
                m = L["m"]
                d.update(Gs=np.array(Gout), cq=np.array(cq),
                         cert_eps=(L["eps"].lo.copy(), L["eps"].hi.copy()),
                         cert_Ie=(m["Ie"].lo.copy(), m["Ie"].hi.copy()),
                         cert_wt=(m["wt"].lo.copy(), m["wt"].hi.copy()), cert_keep=m["keep"].copy())
            assert np.array_equal(Gk, cur["prep"]["Gk"]) and np.array_equal(ck, cur["prep"]["ck"])
        else:
            raise AssertionError("mtxel_iv called from an unexpected frame")
        return orig_m(Gk, ck, Gq, cq, Gout)

    def we(self, q, choose=None):
        assert choose is None
        Gs, b, is0, iop, g0, Gi, phase, nops, qi = self.scr.mapping(q)
        ib = [i for i, (_, bb, _) in enumerate(self.scr.irr) if bb is b]
        assert len(ib) == 1
        pos = spec.gindex(b["G"])
        idx = [pos[tuple(g)] for g in Gi]
        rel = phase / phase[0]
        ph = np.rint(rel.real)
        assert np.allclose(rel, ph, atol=1e-12)
        z = int(np.flatnonzero(np.all(Gs == g0, axis=1))[0])
        cur["q"].setdefault(tuple(float(x) for x in q), {}).update(
            map=dict(iq=ib[0], idx=idx, neg=[bool(x < 0) for x in ph], z=z, is0=bool(is0),
                     Gs=np.array(Gs)))
        return orig_e(self, q, choose)

    cert.mtxel_iv, cert.SigmaIV.eps_at = wm, we
    try:
        for name, ik, bands in SIG_STATES:
            cur.clear()
            cur["q"] = {}
            k = run.kpts[ik]
            pre, parts, _ = sig.parts(k, list(bands), all_q0_ops=False)
            e, c = sig.eqp1(pre, cert.total(parts))
            qd = [cur["q"][tuple(float(x) for x in q)] for q in run.qlist]
            for d, q in zip(qd, run.qlist):
                assert np.array_equal(d["map"]["Gs"], d["Gs"])
                d["cert_parts"] = [(p.lo.copy(), p.hi.copy()) for p in parts[tuple(q)]]
            rec["states"].append(dict(name=name, k=np.array(k, dtype=float), prep=cur["prep"], q=qd,
                                      cert_eqp1=(float(e.lo), float(e.hi)),
                                      cert_constituents={kk: (float(v.lo), float(v.hi)) for kk, v in c.items()}))
    finally:
        cert.mtxel_iv, cert.SigmaIV.eps_at = orig_m, orig_e
    rec["coulomb"] = json.loads((HERE / "data/coulomb_cert.json").read_text())
    return rec


# ---------------------------------------------------------------- stage 3: exact data, hints,
# Python mirror of every check of GW/Endpoint/Kernel/SigmaCheck.lean, and the Lean modules.
#
# Hints are rounded outward by random amounts below 2^62 so that no two distinct hint
# literals share their low 64 bits (Lean 4.19 kernel cache-key collisions, measured up to
# ~50x slower); every rounding is outward, so a hint only widens an enclosure.

RN, RD = 1360569253, 10 ** 8
TSN, TSE = 4722366482869645, 72
TZN, TZE = 4951760157141521, 92
LIM1 = 250000
WINV = 10 ** 12
PILO, PIHI = 314159265358979323846, 314159265358979323847
SX = 92                 # energy unit 1 / (10^8 2^SX) eV
DEN = RD << SX
SI = 128                # I_eps hints
SF = 128                # wing factors
SQ = 128                # |q|
SOUT = 200              # output hints
H7 = 7                  # table box [-7, 7]^3
RNG = random.Random(20260925)


def rlo(v):
    """An outward (down) rounding of the integer v with random low 64 bits."""
    return v - (RNG.getrandbits(62) | 1)


def rhi(v):
    return v + (RNG.getrandbits(62) | 1)


def fdiv(a, b):
    return a // b


def cdiv(a, b):
    return -((-a) // b)


def ipos(x): return x if x >= 0 else 0
def ineg(x): return -x if x < 0 else 0


def tslot(h, g):
    L = 2 * h + 1
    v = (g[0] + h) + L * ((g[1] + h) + L * (g[2] + h))
    return max(v, 0)


def tpack(W, h, b, l):
    P = 0
    for g, v in l:
        P += (b + v) << (W * tslot(h, g))
    return P


def tget(W, h, P, g):
    return (P >> (W * tslot(h, g))) % (1 << W)


def in_box(h, g):
    return all(-h <= x <= h for x in g)


def keys_ok(h, ks):
    return all(in_box(h, g) for g in ks) and len(set(tslot(h, g) for g in ks)) == len(ks)


def vals_ok(W, b, vs):
    return all(abs(v) < b and b + abs(v) < (1 << W) for v in vs)


# ---------------------------------------------------------------- data

def V(g):
    return tuple(int(x) for x in g)


def sigma_data(rec):
    """Exact integers of the whole Sigma input."""
    SC = 0
    SEn = 0
    for st in rec['states']:
        for a in [st['prep']['ck']] + [d['cq'] for d in st['q']]:
            SC = max(SC, max(_dexp(x) for x in a.ravel()))
        for a in [st['prep']['Ek']] + [d['Eq'] for d in st['q']]:
            SEn = max(SEn, max(_dexp(x) for x in a))
    SB = max(_dexp(x) for x in rec['bdot'].ravel())
    B = [[_dint(x, SB) for x in r] for r in rec['bdot']]
    SOm = _dexp(rec['celvol'])
    OmN = _dint(rec['celvol'], SOm)
    SR = max(_dexp(x) for x in rec['rho'])
    rho = [(V(g), _dint(x, SR)) for g, x in zip(rec['rho_G'], rec['rho'])]
    coul = rec['coulomb']
    SV = max(_dexp(x) for k, (lo, hi, _) in list(coul['vbar'].items()) + list(coul['oneoverq'].items())
             for x in (lo, hi))

    def k2(s):
        return tuple(int(2 * Fr(x)) for x in s.split(','))
    vbT = [(k2(k), _dint(lo, SV), _dint(hi, SV)) for k, (lo, hi, _) in coul['vbar'].items()]
    oqT = [(k2(k), _dint(lo, SV), _dint(hi, SV)) for k, (lo, hi, _) in coul['oneoverq'].items()]
    assert all(lo <= hi and lo > 0 for _, lo, hi in vbT + oqT)
    qs = []
    st0 = rec['states'][0]
    for t, q in enumerate(rec['qlist']):
        m = st0['q'][t]['map']
        qh = tuple(int(round(2 * x)) for x in q)
        assert all(abs(2 * x - y) < 1e-12 for x, y in zip(q, qh))
        for st in rec['states']:        # q data are state independent
            d = st['q'][t]
            assert np.array_equal(d['Gs'], st0['q'][t]['Gs']) and np.array_equal(d['Gb'], st0['q'][t]['Gb'])
            assert d['map']['idx'] == m['idx'] and d['map']['neg'] == m['neg'] and d['map']['z'] == m['z']
        assert m['is0'] == (qh == (0, 0, 0))
        qs.append(dict(qh=qh, Gs=[V(g) for g in st0['q'][t]['Gs']], Gb=[V(g) for g in st0['q'][t]['Gb']],
                       iq=m['iq'], idx=list(m['idx']), neg=list(m['neg']), z=m['z']))
    states = []
    for st in rec['states']:
        p = st['prep']
        states.append(dict(name=st['name'], bands=list(p['bands']), Gk=[V(g) for g in p['Gk']],
                           ck=[[_dint(x, SC) for x in r] for r in p['ck']],
                           Ek=[_dint(x, SEn) for x in p['Ek']], Gch=[V(g) for g in p['Gch']],
                           kq=[dict(Gq=[V(g) for g in d['Gq']], cq=[[_dint(x, SC) for x in r] for r in d['cq']],
                                    Eq=[_dint(x, SEn) for x in d['Eq']]) for d in st['q']]))
        for k in [states[-1]['Gk']] + [kq['Gq'] for kq in states[-1]['kq']]:
            assert len(set(k)) == len(k)
    Gch = states[0]['Gch']
    assert all(s['Gch'] == Gch for s in states)
    st1 = []
    for b in rec['stage1']:
        SO = max(dyadic_scale(b['out_lo']), dyadic_scale(b['out_hi']))
        st1.append(dict(SO=SO, lo=to_int(b['out_lo'], SO), hi=to_int(b['out_hi'], SO)))
    return dict(SC=SC, SEn=SEn, SB=SB, B=B, SOm=SOm, OmN=OmN, SR=SR, rho=rho, SV=SV, vbT=vbT, oqT=oqT,
                qs=qs, states=states, Gch=Gch, st1=st1, nocc=rec['nocc'], nq=len(qs))


def dotN(B, qh, G, Gp):
    u = [qh[a] + 2 * G[a] for a in range(3)]
    w = [qh[a] + 2 * Gp[a] for a in range(3)]
    return sum(u[a] * B[a][c] * w[c] for a in range(3) for c in range(3))


def gsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


# ---------------------------------------------------------------- tables, alignment, wings

def tables(D):
    Wr = max(abs(v) for _, v in D['rho']).bit_length() + 2
    br = 1 << (Wr - 1)
    Wv = max(x for _, lo, hi in D['vbT'] for x in (lo, hi)).bit_length() + 2
    bv = 1 << (Wv - 1)
    assert keys_ok(H7, [g for g, _ in D['rho']]) and vals_ok(Wr, br, [v for _, v in D['rho']])
    assert keys_ok(H7, [g for g, _, _ in D['vbT']])
    assert vals_ok(Wv, bv, [x for _, lo, hi in D['vbT'] for x in (lo, hi)])
    assert keys_ok(H7, D['Gch'])
    T = dict(Wr=Wr, br=br, Wv=Wv, bv=bv)
    T['Prho'] = tpack(Wr, H7, br, D['rho'])
    T['Pvlo'] = tpack(Wv, H7, bv, [(g, lo) for g, lo, _ in D['vbT']])
    T['Pvhi'] = tpack(Wv, H7, bv, [(g, hi) for g, _, hi in D['vbT']])
    return T


def key(qd, G):
    return tuple(qd['qh'][a] + 2 * G[a] for a in range(3))


def vb_align(D, T, qd, Gl):
    out = []
    for G in Gl:
        k = key(qd, G)
        lo = tget(T['Wv'], H7, T['Pvlo'], k) - T['bv']
        hi = tget(T['Wv'], H7, T['Pvhi'], k) - T['bv']
        assert tget(T['Wv'], H7, T['Pvlo'], k) != 0 and lo > 0
        out.append((lo, hi))
    return out


def wing(D, qd, vbS):
    """Certified wing factors of q != 0 (scale 2^-SF) and |q| (2^-SQ); mirror of wingOK."""
    q2N = dotN(D['B'], qd['qh'], (0, 0, 0), (0, 0, 0))
    S = 4 << D['SB']
    # |q| in [ql, qu] / 2^SQ:  ql^2 S <= q2N 2^(2SQ) <= qu^2 S
    x = (q2N << (2 * SQ)) // S
    ql = rlo(math.isqrt(x))
    qu = rhi(math.isqrt(x) + 1)
    assert ql > 0 and ql * ql * S <= q2N << (2 * SQ) <= qu * qu * S
    ol, oh = [(lo, hi) for g, lo, hi in D['oqT'] if g == qd['qh']][0]
    vl, vh = vbS[0]
    SV = D['SV']
    frl = rlo(fdiv(ol * ql * (1 << SF) * 10 ** 20, (1 << SV) * (1 << SQ) * 8 * PIHI))
    frh = rhi(cdiv(oh * qu * (1 << SF) * 10 ** 20, (1 << SV) * (1 << SQ) * 8 * PILO))
    fcl = rlo(fdiv(ol * (1 << SQ) * (1 << SF), vh * qu))
    fch = rhi(cdiv(oh * (1 << SQ) * (1 << SF), vl * ql))
    w = dict(frl=frl, frh=frh, fcl=fcl, fch=fch, ql=ql, qu=qu)
    assert wing_ok(D, w, qd, ol, oh, vl, vh)
    return w, (ol, oh)


def wing_ok(D, w, qd, ol, oh, vl, vh):
    q2N = dotN(D['B'], qd['qh'], (0, 0, 0), (0, 0, 0))
    SB, SV = D['SB'], D['SV']
    return (0 < w['ql'] and 0 < vl and 0 < ol and
            w['ql'] ** 2 * (4 * 2 ** SB) <= q2N * 2 ** (2 * SQ) <= w['qu'] ** 2 * (4 * 2 ** SB) and
            w['frl'] * 2 ** SV * 2 ** SQ * 8 * PIHI <= ol * w['ql'] * 2 ** SF * 10 ** 20 and
            oh * w['qu'] * 2 ** SF * 10 ** 20 <= w['frh'] * 2 ** SV * 2 ** SQ * 8 * PILO and
            w['fcl'] * vh * w['qu'] <= ol * 2 ** SQ * 2 ** SF and
            oh * 2 ** SQ * 2 ** SF <= w['fch'] * vl * w['ql'])


# ---------------------------------------------------------------- entries

def eg_of(D, T):
    return dict(SF=SF, SI=SI, SV=D['SV'], RN=RN, SB=D['SB'], B=D['B'], SR=D['SR'], SOm=D['SOm'], OmN=D['OmN'],
                W=T['Wr'], h=H7, bias=T['br'], tsn=TSN, tse=TSE, Den=DEN, winv=WINV)


def DO(g):
    return 10 ** 36 * 4 * 2 ** (g['SB'] + g['SR'] + g['SV']) * g['OmN']


def om2(g, qd, vbS, P, j, i):
    gj, gi = qd['Gs'][j], qd['Gs'][i]
    tg = tget(g['W'], g['h'], P, gsub(gj, gi))
    rv = tg - g['bias']
    if tg == 0:
        return (False, False, 0, 0)
    if qd['qh'] == (0, 0, 0) and gj == (0, 0, 0):
        if gi == (0, 0, 0):
            c = 16 * g['RN'] ** 2 * abs(rv) * 2 ** g['SOm'] * 4 * 2 ** (g['SB'] + g['SV'])
            return (rv != 0, rv < 0, PILO * c, PIHI * c)
        return (False, False, 0, 0)
    pr = dotN(g['B'], qd['qh'], gi, gj) * rv
    v = vbS[j]
    c = 2 * g['RN'] ** 2 * abs(pr) * 2 ** g['SOm'] * 10 ** 20
    return (pr != 0, pr < 0, c * v[0], c * v[1])


def pmul(el, eh, fl, fh):
    return (el * fl if el >= 0 else el * fh, eh * fh if eh >= 0 else eh * fl)


def ie_box(g, SO, w, qd, Elo, Ehi, j, i):
    a, b = qd['idx'][j], qd['idx'][i]
    lo, hi = Elo[a][b], Ehi[a][b]
    s = qd['neg'][j] != qd['neg'][i]
    el, eh = (-hi, -lo) if s else (lo, hi)
    F = 1 << g['SF']
    z = qd['z']
    wr = j == z and i != z
    wc = i == z and j != z
    if qd['qh'] == (0, 0, 0):
        e = (0, 0) if (wr or wc) else (el * F, eh * F)
    elif wr:
        e = pmul(el, eh, w['frl'], w['frh'])
    elif wc:
        e = pmul(el, eh, w['fcl'], w['fch'])
    else:
        e = (el * F, eh * F)
    d = (1 << (SO + g['SF'])) if j == i else 0
    return (d - e[1], d - e[0])


def ent_chk(g, SO, w, qd, Elo, Ehi, vbS, P, j, i, r):
    cls, IL, IH, tl, th = r
    S1 = SO + g['SF']
    bx = ie_box(g, SO, w, qd, Elo, Ehi, j, i)
    ieok = IL * 2 ** S1 <= bx[0] * 2 ** g['SI'] and bx[1] * 2 ** g['SI'] <= IH * 2 ** S1
    tsI = g['tsn'] * 2 ** g['SI']
    u = tsI <= IL * 2 ** g['tse'] or IH * 2 ** g['tse'] <= -tsI
    uf = -tsI < IL * 2 ** g['tse'] and IH * 2 ** g['tse'] < tsI
    al = abs(IL) if 0 < IL else abs(IH)
    ah = abs(IH) if 0 < IL else abs(IL)
    nz, on, olo, ohi = om2(g, qd, vbS, P, j, i)
    D = DO(g)
    k1 = nz and g['tsn'] * D <= olo * 2 ** g['tse']
    k1f = (not nz) or ohi * 2 ** g['tse'] < g['tsn'] * D
    wtt = g['tsn'] * D * ah <= olo * 2 ** g['SI'] * 2 ** g['tse']
    wtf = ohi * 2 ** g['SI'] * 2 ** g['tse'] < g['tsn'] * D * al
    sgnEq = on == (IL < 0)
    D2 = g['Den'] ** 2
    if not (ieok and IL <= IH):
        return False
    if cls == 0:
        return uf
    if cls == 1:
        return u and (k1f or wtf)
    if cls == 2:
        return (u and k1 and wtt and sgnEq and 0 < tl and tl * tl * D * ah <= D2 * olo * 2 ** g['SI'] and
                D2 * ohi * 2 ** g['SI'] <= th * th * D * al)
    if cls == 3:
        return u and k1 and wtt and (not sgnEq) and 0 < tl and tl <= g['winv'] * g['Den'] <= th
    return False


def make_ent(g, SO, w, qd, Elo, Ehi, vbS, P, j, i):
    """The record of entry (j, i): decided from the exact boxes (fails loudly when a
    decision is not certain), rounded outward with random low bits."""
    bx = ie_box(g, SO, w, qd, Elo, Ehi, j, i)
    S1 = SO + g['SF']
    IL = rlo(fdiv(bx[0] << g['SI'], 1 << S1)) if S1 >= 0 else None
    IH = rhi(cdiv(bx[1] << g['SI'], 1 << S1))
    tsI = g['tsn'] * 2 ** g['SI']
    u = tsI <= IL * 2 ** g['tse'] or IH * 2 ** g['tse'] <= -tsI
    uf = -tsI < IL * 2 ** g['tse'] and IH * 2 ** g['tse'] < tsI
    if not (u or uf):
        raise ValueError(f"undecided |I| threshold at {j},{i}")
    if uf:
        r = (0, IL, IH, 0, 0)
    else:
        al = abs(IL) if 0 < IL else abs(IH)
        ah = abs(IH) if 0 < IL else abs(IL)
        nz, on, olo, ohi = om2(g, qd, vbS, P, j, i)
        D = DO(g)
        k1 = nz and g['tsn'] * D <= olo * 2 ** g['tse']
        k1f = (not nz) or ohi * 2 ** g['tse'] < g['tsn'] * D
        if not (k1 or k1f):
            raise ValueError("undecided Omega2 threshold")
        if k1f:
            r = (1, IL, IH, 0, 0)
        else:
            wtt = g['tsn'] * D * ah <= olo * 2 ** g['SI'] * 2 ** g['tse']
            wtf = ohi * 2 ** g['SI'] * 2 ** g['tse'] < g['tsn'] * D * al
            if not (wtt or wtf):
                raise ValueError("undecided wt2 threshold")
            if wtf:
                r = (1, IL, IH, 0, 0)
            elif on == (IL < 0):
                D2 = g['Den'] ** 2
                tl = rlo(math.isqrt(fdiv(D2 * olo * 2 ** g['SI'], D * ah)))
                th = rhi(math.isqrt(cdiv(D2 * ohi * 2 ** g['SI'], D * al)) + 1)
                r = (2, IL, IH, tl, th)
            else:
                WD = g['winv'] * g['Den']
                r = (3, IL, IH, rlo(WD), rhi(WD))
    assert ent_chk(g, SO, w, qd, Elo, Ehi, vbS, P, j, i, r), (j, i, r)
    return r


# ---------------------------------------------------------------- hot path mirror

def subT(sx, X, tl, th):
    if sx: return (True, True, X + tl, X + th)
    if th < X: return (True, False, X - th, X - tl)
    if X < tl: return (True, True, tl - X, th - X)
    return (False, False, 0, 0)


def nsub(a, b): return max(a - b, 0)


def addT(sx, X, tl, th):
    if not sx: return (True, False, X + tl, X + th)
    if X < tl: return (True, False, tl - X, th - X)
    if th < X: return (True, True, X - th, X - tl)
    return (False, False, 0, max(nsub(th, X), nsub(X, tl)))


def sq2(X2, tl2, th2):
    if th2 < X2: return (True, False, X2 - th2, X2 - tl2)
    if X2 < tl2: return (True, True, tl2 - X2, th2 - X2)
    return (False, False, 0, max(nsub(th2, X2), nsub(X2, tl2)))


DEN2 = DEN * DEN


def genT(dl, dh, tl2, th2):
    if DEN2 < 4 * (dl * dl) and th2 < dl * dl * LIM1: return (True, True)
    if 4 * (dh * dh) <= DEN2 or dh * dh * LIM1 <= tl2: return (True, False)
    return (False, False)


FAIL = (False, False, 0, 0)
ZERO = (True, False, 0, 0)
STATS = {}


def cnt(k):
    STATS[k] = STATS.get(k, 0) + 1


def schK(e, x):
    kept, sI, al, ah, tl, th, tl2, th2 = e
    sx, X, X2 = x
    d = subT(sx, X, tl, th)
    if not d[0]: return FAIL
    g = genT(d[2], d[3], tl2, th2)
    if not g[0]: return FAIL
    if g[1]: return (True, sI != d[1], tl * al // d[3], th * ah // d[2] + 1)
    cnt('sch0')
    return ZERO


def ssxK(e, x):
    kept, sI, al, ah, tl, th, tl2, th2 = e
    sx, X, X2 = x
    d = subT(sx, X, tl, th)
    if not d[0]: return FAIL
    g = genT(d[2], d[3], tl2, th2)
    if not g[0]: return FAIL
    if g[1]:
        q = sq2(X2, tl2, th2)
        if sx and 4 * q[3] < tl2:
            cnt('gclamp'); return ZERO
        if q[0] and ((not sx) or th2 <= 4 * q[2]):
            return (True, sI != q[1], tl2 * al // q[3], th2 * ah // q[2] + 1)
        return FAIL
    if th2 <= (d[2] * d[2] * TZN) >> TZE:
        cnt('ssx0'); return ZERO
    if (d[3] * d[3] * TZN) >> TZE < tl2:
        s = addT(sx, X, tl, th)
        if sx and 8 * s[3] < tl:
            cnt('nclamp'); return ZERO
        if s[0] and ((not sx) or th <= 8 * s[2]):
            cnt('near')
            return (True, not (sI != s[1]), tl * al // (2 * s[3]), th * ah // (2 * s[2]) + 1)
        return FAIL
    return FAIL


def entD(r):
    cls, IL, IH, tl, th = r
    if IL >= 0: return (2 <= cls, False, IL, ipos(IH), tl, th, tl * tl, th * th)
    return (2 <= cls, True, ineg(IH), ineg(IL), tl, th, tl * tl, th * th)


A0 = (0, 0, 0, 0)


def addA(a, b): return tuple(x + y for x, y in zip(a, b))


def smA(neg, c, lo, hi):
    return (0, c * hi, 0, c * lo) if neg else (c * lo, 0, c * hi, 0)


def ivA(s, c, IL, IH):
    if s: return (c * ineg(IH), c * ipos(IH), c * ineg(IL), c * ipos(IL))
    return (c * ipos(IL), c * ineg(IL), c * ipos(IH), c * ineg(IH))


CS0 = (True, A0, A0, A0)


def addCS(a, b): return (a[0] and b[0], addA(a[1], b[1]), addA(a[2], b[2]), addA(a[3], b[3]))


def contrib(occ, e0, e1, sj, cj, r):
    ac = ivA(sj, cj, r[1], r[2]) if 1 <= r[0] else A0
    d = entD(r)
    if not d[0]:
        return (True, A0, A0, ac)
    a0, a1 = schK(d, e0), schK(d, e1)
    if occ:
        b0, b1 = ssxK(d, e0), ssxK(d, e1)
        return (a0[0] and a1[0] and b0[0] and b1[0],
                addA(smA(sj != a0[1], cj, a0[2], a0[3]), smA(not (sj != b0[1]), 2 * cj, b0[2], b0[3])),
                addA(smA(sj != a1[1], cj, a1[2], a1[3]), smA(not (sj != b1[1]), 2 * cj, b1[2], b1[3])), ac)
    return (a0[0] and a1[0], smA(sj != a0[1], cj, a0[2], a0[3]), smA(sj != a1[1], cj, a1[2], a1[3]), ac)


def colSum(occ, e0, e1, xs, rs):
    s = CS0
    for x, r in zip(xs, rs):
        s = addCS(s, CS0 if x[1] == 0 else contrib(occ, e0, e1, x[0], x[1], r))
    return s


def mulV(vl, vh, a):
    lp, ln, hp, hn = a
    return (vl * (lp - ln) if ln <= lp else 0, 0 if ln <= lp else vh * (ln - lp),
            vh * (hp - hn) if hn <= hp else 0, 0 if hn <= hp else vl * (hn - hp))


def sgnA(s, c, a):
    lp, ln, hp, hn = a
    return (c * hn, c * hp, c * ln, c * lp) if s else (c * lp, c * ln, c * hp, c * hn)


def colFin(x, v, c):
    return (c[0], sgnA(x[0], x[1], mulV(v[0], v[1], c[1])), sgnA(x[0], x[1], mulV(v[0], v[1], c[2])),
            sgnA(x[0], x[1], mulV(v[0], v[1], c[3])))


def accval(a): return (a[0] - a[1], a[2] - a[3])


def acc_in(a, sh, lo, hi):
    L, H = accval(a)
    return lo * 2 ** sh <= L and H <= hi * 2 ** sh


def mkEn(ek, eq, iw, SEn):
    sh = SX - SEn
    x = RN * (ek - eq) * 2 ** sh + iw * DEN
    tz = TZN * RD * 2 ** (SX - TZE)
    if abs(x) < tz: return (False, tz, tz * tz)
    return (x < 0, abs(x), x * x)


def xs_of(T, l):
    return [(h < 0, abs(h) >> T) for h in l]


def nOK_T(occ, e0, e1, xs, vbS, cols):
    T = CS0
    for x, v, rs in zip(xs, vbS, cols):
        T = addCS(T, colFin(x, v, colSum(occ, e0, e1, xs, rs)))
    return T


def out_hints(T, sh):
    """Outward-rounded claims at scale 2^-SOUT of the three accumulators."""
    o = []
    for a in (T[1], T[2], T[3]):
        L, H = accval(a)
        o += [rlo(L >> sh), rhi(-((-H) >> sh))]
    return o


def cs_col(W, h, b, PA, qd, j, rs):
    acc = A0
    for i, r in enumerate(rs):
        tg = tget(W, h, PA, gsub(qd['Gs'][i], qd['Gs'][j]))
        A = tg - b
        if 1 <= r[0] and tg != 0:
            acc = addA(acc, ivA(0 < A, abs(A), r[1], r[2]))
    return acc


def csOK_T(W, h, b, PA, qd, vbS, cols):
    T = A0
    for j, (v, rs) in enumerate(zip(vbS, cols)):
        T = addA(T, sgnA(False, 1, mulV(v[0], v[1], cs_col(W, h, b, PA, qd, j, rs))))
    return T


def ex_T(Hb, vbB):
    Al = sum(h * h * v[0] for row in Hb for h, v in zip(row, vbB))
    Ah = sum(h * h * v[1] for row in Hb for h, v in zip(row, vbB))
    return (-Ah, -Al)


# ---------------------------------------------------------------- driver

def build(rec, only_states=None, only_q=None):
    D = sigma_data(rec)
    T = tables(D)
    g = eg_of(D, T)
    Q = []
    for t, qd in enumerate(D['qs']):
        vbS = vb_align(D, T, qd, qd['Gs'])
        vbB = vb_align(D, T, qd, qd['Gb'])
        if qd['qh'] != (0, 0, 0):
            w, oq = wing(D, qd, vbS)
        else:
            w, oq = dict(frl=0, frh=0, fcl=0, fch=0, ql=0, qu=0), None
        b = D['st1'][qd['iq']]
        n = len(qd['Gs'])
        cols = [[make_ent(g, b['SO'], w, qd, b['lo'], b['hi'], vbS, T['Prho'], j, i) for j in range(n)]
                for i in range(n)]
        Q.append(dict(vbS=vbS, vbB=vbB, w=w, oq=oq, cols=cols))
    return D, T, g, Q


# ---------------------------------------------------------------- Lean emission

NS = "GW.Endpoint.Kernel.S3"
OPEN = "open GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig"
HEAD = ("/- Generated by bgw/endpoint/kernel_export.py --sigma (do not edit). G2 stage 3:\n"
        "spec A's Sigma data (cert.py's inputs, exact dyadics) and kernel-checked hints. -/\n")
LL = lean_list


def lz(x):
    return lit_z(x)


def lv(g):
    return _lv(g)


def lb(b):
    return "true" if b else "false"


def lent(r):
    return f"⟨{r[0]}, {lz(r[1])}, {lz(r[2])}, {r[3]}, {r[4]}⟩"


def lqd(qd, name):
    return (f"noncomputable def {name}Gs : List V3 := {LL([lv(g) for g in qd['Gs']])}\n"
            f"noncomputable def {name}Gb : List V3 := {LL([lv(g) for g in qd['Gb']])}\n"
            f"noncomputable def {name} : QD where\n  qh := {lv(qd['qh'])}\n  Gs := {name}Gs\n  Gb := {name}Gb\n"
            f"  iq := {qd['iq']}\n  idx := {LL([str(x) for x in qd['idx']])}\n"
            f"  neg := {LL([lb(x) for x in qd['neg']])}\n  z := {qd['z']}\n")


def kcfg(Gv, Gc, Gs, cv, cc):
    comps = [x for g in Gv + Gc for x in g]
    lo, hi = min(comps), max(comps)
    H = max(hi - lo, max(abs(x) for g in Gs for x in g))
    L = 2 * H + 1
    W = 2
    for a in cv:
        for b in cc:
            W = max(W, (sum(map(abs, a)) * sum(map(abs, b))).bit_length() + 1)
    return dict(L=L, lo=lo, H=H, W=W)


def lcfg(c):
    return f"⟨{c['L']}, {lit_int(c['lo'])}, {c['H']}, {c['W']}, 0, 0, 0, 0⟩"


def hints_state(D, T, Q, s):
    """Per (state, q): pair-density hints, kOK configurations, and the claimed output
    enclosures of every hot-path / exchange / static check."""
    st = D['states'][s]
    res = []
    HA = _pair_density(st['Gk'], st['ck'], st['Gk'], st['ck'], D['Gch'])
    cfA = kcfg(st['Gk'], st['Gk'], D['Gch'], st['ck'], st['ck'])
    for t, qd in enumerate(D['qs']):
        q = Q[t]
        kq = st['kq'][t]
        H = _pair_density(st['Gk'], st['ck'], kq['Gq'], kq['cq'], qd['Gs'])
        Hb = _pair_density(st['Gk'], st['ck'], kq['Gq'], kq['cq'][:D['nocc']], qd['Gb'])
        cf = kcfg(st['Gk'], kq['Gq'], qd['Gs'], st['ck'], kq['cq'])
        cfb = kcfg(st['Gk'], kq['Gq'], qd['Gb'], st['ck'], kq['cq'][:D['nocc']])
        bands = []
        for a in range(len(st['ck'])):
            Xl, Xh = ex_T(Hb[a], q['vbB'])
            SXs = 4 * D['SC'] + D['SV']
            shx = SXs - SOUT
            xo = (rlo(Xl >> shx), rhi(-((-Xh) >> shx)))
            Avals = HA[a][a]
            WA = max(abs(v) for v in Avals).bit_length() + 2
            bA = 1 << (WA - 1)
            PA = tpack(WA, H7, bA, list(zip(D['Gch'], Avals)))
            CL, CH = accval(csOK_T(WA, H7, bA, PA, qd, q['vbS'], q['cols']))
            SCS = SI + 2 * D['SC'] + D['SV']
            shc = SCS - SOUT
            co = (rlo(CL >> shc), rhi(-((-CH) >> shc)))
            ns = []
            for n1 in range(len(kq['cq'])):
                h = H[a][n1]
                Tx = min(((abs(x) & -abs(x)).bit_length() - 1) for x in h if x)
                xs = xs_of(Tx, h)
                e0 = mkEn(st['Ek'][a], kq['Eq'][n1], 0, D['SEn'])
                e1 = mkEn(st['Ek'][a], kq['Eq'][n1], 1, D['SEn'])
                TT = nOK_T(n1 < D['nocc'], e0, e1, xs, q['vbS'], q['cols'])
                assert TT[0]
                ST = SI + 2 * (2 * D['SC'] - Tx) + D['SV']
                sh = ST - SOUT
                o = out_hints(TT, sh)
                for k in range(3):
                    assert acc_in(TT[1 + k], sh, o[2 * k], o[2 * k + 1])
                ns.append(dict(Tx=Tx, sh=sh, o=o))
            bands.append(dict(xo=xo, shx=shx, co=co, shc=shc, WA=WA, bA=bA, n1=ns))
        res.append(dict(H=H, Hb=Hb, cf=cf, cfb=cfb, bands=bands))
    return dict(HA=HA, cfA=cfA, q=res)


def chunked_list(name, ty, items, per=100):
    """A long list as chunk definitions `name_k` joined by `++`-free cons (one def per chunk)."""
    out = []
    ch = [items[i:i + per] for i in range(0, len(items), per)]
    for k, c in enumerate(ch):
        out.append(f"noncomputable def {name}_{k} : List ({ty}) := {LL(c)}")
    # join: nested append is slow in the kernel; build one list of chunks and flatten by a
    # List.rec-based append (flatL)
    out.append(f"noncomputable def {name} : List ({ty}) := flatL {LL([f'{name}_{k}' for k in range(len(ch))])}")
    return "\n".join(out) + "\n"


def emit_glob(D, T, g):
    L = [HEAD, "import GW.Endpoint.Kernel.SigmaCheck\n", f"namespace {NS}\n{OPEN}\n"]
    L.append(chunked_list("rhoT", "V3 × ℤ", [f"({lv(k)}, {lz(v)})" for k, v in D['rho']]))
    L.append(f"noncomputable def Gch : List V3 := {LL([lv(k) for k in D['Gch']])}\n")
    L.append(f"noncomputable def B : List (List ℤ) := {LL([LL([lit_int(x) for x in r]) for r in D['B']])}\n")
    for t, qd in enumerate(D['qs']):
        L.append(lqd(qd, f"qd{t}"))
    L.append(f"noncomputable def qs : List QD := {LL([f'qd{t}' for t in range(len(D['qs']))])}\n")
    L.append(f"/-- The run data of spec A. -/\nnoncomputable def gl : Gl where\n  SC := {D['SC']}\n  SEn := {D['SEn']}\n"
             f"  SB := {D['SB']}\n  B := B\n  SOm := {D['SOm']}\n  Om := {D['OmN']}\n  SR := {D['SR']}\n"
             f"  rho := rhoT\n  Gch := Gch\n  qs := qs\n  nocc := {D['nocc']}\n")
    L.append(chunked_list("vbT", "V3 × ℤ × ℤ", [f"({lv(k)}, {lz(lo)}, {lz(hi)})" for k, lo, hi in D['vbT']]))
    L.append(f"noncomputable def oqT : List (V3 × ℤ × ℤ) := {LL([f'({lv(k)}, {lz(lo)}, {lz(hi)})' for k, lo, hi in D['oqT']])}\n")
    L.append(f"/-- Entry-check constants. -/\nnoncomputable def eg : EG where\n  SF := {SF}\n  SI := {SI}\n  SV := {D['SV']}\n"
             f"  RN := {RN}\n  SB := {D['SB']}\n  B := B\n  SR := {D['SR']}\n  SOm := {D['SOm']}\n  OmN := {D['OmN']}\n"
             f"  W := {T['Wr']}\n  h := {H7}\n  bias := {T['br']}\n  tsn := {TSN}\n  tse := {TSE}\n  Den := {DEN}\n"
             f"  winv := {WINV}\n")
    L.append(f"/-- Kernel constants. -/\nnoncomputable def kc : KC := ⟨{DEN2}, {LIM1}, {TZN}, {TZE}⟩\n")
    br, Wv, bv = T['br'], T['Wv'], T['bv']
    L.append(chunked_list("rhoS", "ℕ × ℕ", [f"({tslot(H7, k)}, {br + v})" for k, v in D['rho']]))
    L.append(chunked_list("vloS", "ℕ × ℕ", [f"({tslot(H7, k)}, {bv + lo})" for k, lo, hi in D['vbT']]))
    L.append(chunked_list("vhiS", "ℕ × ℕ", [f"({tslot(H7, k)}, {bv + hi})" for k, lo, hi in D['vbT']]))
    L.append(f"end {NS}\n")
    return "\n".join(L)


def emit_tabs(D, T):
    Wv, bv = T['Wv'], T['bv']
    L = [HEAD, f"import {'GW.Endpoint.Kernel.Data.S3G'}\n", f"namespace {NS}\n{OPEN}\n",
         "theorem rhoS_eq : tslots eg.h eg.bias rhoT = rhoS := by decide +kernel",
         f"theorem vloS_eq : tslots 7 {bv} (mapL (fun p => (p.1, p.2.1)) vbT) = vloS := by decide +kernel",
         f"theorem vhiS_eq : tslots 7 {bv} (mapL (fun p => (p.1, p.2.2)) vbT) = vhiS := by decide +kernel",
         "theorem rho_keys : keysOK 7 (mapL Prod.fst rhoT) = true := by decide +kernel",
         "theorem vb_keys : keysOK 7 (mapL Prod.fst vbT) = true := by decide +kernel",
         "theorem gch_keys : keysOK 7 Gch = true := by decide +kernel",
         "theorem rho_vals : valsOK eg.W eg.bias (mapL Prod.snd rhoT) = true := by decide +kernel",
         f"theorem vb_vals : valsOK {Wv} {bv} (mapL (fun p => p.2.1) vbT) = true ∧ "
         f"valsOK {Wv} {bv} (mapL (fun p => p.2.2) vbT) = true := by decide +kernel",
         f"\nend {NS}\n"]
    return "\n".join(L)


def lvb(l):
    return LL([f"({a}, {b})" for a, b in l])


def emit_v(D, T, Q):
    Wv, bv = T['Wv'], T['bv']
    L = [HEAD, "import GW.Endpoint.Kernel.Data.S3G\n", f"namespace {NS}\n{OPEN}\n"]
    for t, q in enumerate(Q):
        L.append(f"noncomputable def vbS{t} : List (ℕ × ℕ) := {lvb(q['vbS'])}")
        L.append(f"noncomputable def vbB{t} : List (ℕ × ℕ) := {lvb(q['vbB'])}")
        w = q['w']
        L.append(f"noncomputable def w{t} : Wing := ⟨{w['frl']}, {w['frh']}, {w['fcl']}, {w['fch']}, {w['ql']}, {w['qu']}⟩")
        L.append(f"theorem vbS{t}_ok : vbOK {Wv} 7 {bv} (tpackS {Wv} vloS) (tpackS {Wv} vhiS) qd{t} qd{t}.Gs vbS{t} = true := by decide +kernel")
        L.append(f"theorem vbB{t}_ok : vbOK {Wv} 7 {bv} (tpackS {Wv} vloS) (tpackS {Wv} vhiS) qd{t} qd{t}.Gb vbB{t} = true := by decide +kernel")
        if q['oq'] is not None:
            ol, oh = q['oq']
            vl, vh = q['vbS'][0]
            L.append(f"theorem w{t}_ok : wingOK eg {SQ} w{t} qd{t} oqT {ol} {oh} vbS{t} = true := by decide +kernel")
        L.append(f"theorem gs{t}_box : qd{t}.Gs.all (inBox (-3) 3) = true := by decide +kernel")
        L.append("")
    L.append(f"end {NS}\n")
    return "\n".join(L)


def lrows(name, rows, lit=None):
    """One definition per row (List ℤ), then the list of rows."""
    lit = lit or lz
    out = [f"noncomputable def {name}_{k} : List ℤ := {LL([lit(x) for x in r])}" for k, r in enumerate(rows)]
    out.append(f"noncomputable def {name} : List (List ℤ) := {LL([f'{name}_{k}' for k in range(len(rows))])}")
    return "\n".join(out) + "\n"


def lhint3(name, H):
    """[a][n1][j] hints: one definition per (a, n1)."""
    out = []
    for a, Ha in enumerate(H):
        out.append(lrows(f"{name}_{a}", Ha))
    out.append(f"noncomputable def {name} : List (List (List ℤ)) := {LL([f'{name}_{a}' for a in range(len(H))])}\n")
    return "\n".join(out)


def emit_st(D, HS, s):
    st = D['states'][s]
    nm = st['name']
    L = [HEAD, "import GW.Endpoint.Kernel.Data.S3G\n", f"namespace {NS}\n{OPEN}\n"]
    L.append(f"noncomputable def Gk{nm} : List V3 := {LL([lv(g) for g in st['Gk']])}")
    L.append(lrows(f"ck{nm}", st['ck']))
    L.append(f"noncomputable def Ek{nm} : List ℤ := {LL([lz(x) for x in st['Ek']])}")
    L.append(lhint3(f"HA{nm}", HS['HA']))
    L.append(f"noncomputable def cfA{nm} : Cfg := {lcfg(HS['cfA'])}")
    L.append(f"theorem kokA{nm} : kOK cfA{nm} Gch ⟨Gk{nm}, ck{nm}, Ek{nm}, Gk{nm}, ck{nm}, Ek{nm}⟩ HA{nm} = true := by decide +kernel\n")
    L.append(f"end {NS}\n")
    return "\n".join(L)




# ---------------------------------------------------------------- stage 3 module layout

def S3mod(name):
    return f"GW.Endpoint.Kernel.Data.{name}"


def emit_e_data(D, Q, t, prev):
    """S3E{t}: the entry records of q-point t (data only)."""
    qd = D['qs'][t]
    n = len(qd['Gs'])
    L = [HEAD, f"import {prev}\n", f"namespace {NS}\n{OPEN}\n"]
    cols = Q[t]['cols']
    for i in range(n):
        L.append(f"noncomputable def c{t}_{i} : List Ent := {LL([lent(r) for r in cols[i]])}")
    L.append(f"noncomputable def cols{t} : List (List Ent) := {LL([f'c{t}_{i}' for i in range(n)])}\n")
    L.append(f"end {NS}\n")
    return "\n".join(L)


def emit_e_chk(D, t, cols_range, prevs):
    """S3E{t}C{k}: the entry checks of the columns `cols_range` (one theorem per column)."""
    qd = D['qs'][t]
    iq = qd['iq']
    L = [HEAD, "".join(f"import {p}\n" for p in prevs), f"namespace {NS}\n{OPEN}\n"]
    for i in cols_range:
        L.append(f"theorem e{t}_{i} : entCol eg Q{iq}.cert.SO w{t} qd{t} Q{iq}.cert.outLo Q{iq}.cert.outHi vbS{t} "
                 f"(tpackS eg.W rhoS) {i} (cols{t}.getD {i} []) = true := by decide +kernel")
    L.append(f"\nend {NS}\n")
    return "\n".join(L)


def emit_k2(D, HS, s, t, prev):
    """S3K{s}{t}: the states at k - q, the pair-density hints and their checks, and the
    claimed enclosures of the heavy checks."""
    st = D['states'][s]
    nm = st['name']
    kq = st['kq'][t]
    h = HS['q'][t]
    tag = f"{nm}{t}"
    L = [HEAD, f"import {prev}\n", f"namespace {NS}\n{OPEN}\n"]
    L.append(f"noncomputable def Gq{tag} : List V3 := {LL([lv(g) for g in kq['Gq']])}")
    L.append(lrows(f"cq{tag}", kq['cq']))
    L.append(f"noncomputable def Eq{tag} : List ℤ := {LL([lz(x) for x in kq['Eq']])}")
    L.append(f"noncomputable def kq{tag} : KQ := ⟨Gq{tag}, cq{tag}, Eq{tag}⟩")
    L.append(lhint3(f"H{tag}", h['H']))
    L.append(lhint3(f"Hb{tag}", h['Hb']))
    L.append(f"noncomputable def cf{tag} : Cfg := {lcfg(h['cf'])}")
    L.append(f"noncomputable def cfb{tag} : Cfg := {lcfg(h['cfb'])}")
    L.append(f"noncomputable def Tx{tag} : List (List ℕ) := {LL([LL([str(m['Tx']) for m in b['n1']]) for b in h['bands']])}")
    L.append(f"noncomputable def sh{tag} : List (List ℕ) := {LL([LL([str(m['sh']) for m in b['n1']]) for b in h['bands']])}")
    L.append(f"noncomputable def O{tag} : List (List (List ℤ)) := "
             f"{LL([LL([LL([lz(x) for x in m['o']]) for m in b['n1']]) for b in h['bands']])}")
    L.append(f"noncomputable def XO{tag} : List (ℤ × ℤ) := {LL([f'({lz(b[chr(120)+chr(111)][0])}, {lz(b[chr(120)+chr(111)][1])})' for b in h['bands']])}")
    L.append(f"noncomputable def CO{tag} : List (ℤ × ℤ) := {LL([f'({lz(b[chr(99)+chr(111)][0])}, {lz(b[chr(99)+chr(111)][1])})' for b in h['bands']])}")
    L.append(f"noncomputable def WA{tag} : List ℕ := {LL([str(b['WA']) for b in h['bands']])}")
    L.append(f"noncomputable def bA{tag} : List ℕ := {LL([str(b['bA']) for b in h['bands']])}")
    L.append(f"theorem kok{tag} : kOK cf{tag} qd{t}.Gs ⟨Gk{nm}, ck{nm}, Ek{nm}, Gq{tag}, cq{tag}, Eq{tag}⟩ H{tag} = true := by decide +kernel")
    L.append(f"theorem kokb{tag} : kOK cfb{tag} qd{t}.Gb ⟨Gk{nm}, ck{nm}, Ek{nm}, Gq{tag}, cq{tag}.take {D['nocc']}, "
             f"Eq{tag}.take {D['nocc']}⟩ Hb{tag} = true := by decide +kernel")
    L.append(f"theorem xs{tag} : all2 (fun hs txs => all2 (fun h tx => xsExact tx h) hs txs) H{tag} Tx{tag} = true := by decide +kernel")
    L.append(f"theorem sh{tag}_ok : shOK {SOUT} {SI} {D['SC']} {D['SV']} sh{tag} Tx{tag} = true := by decide +kernel\n")
    L.append(f"end {NS}\n")
    return "\n".join(L)


def sq_fields(D, HS, s, t):
    nm = D['states'][s]['name']
    tag = f"{nm}{t}"
    qd = D['qs'][t]
    iq = qd['iq']
    b0 = HS['q'][t]['bands'][0]
    return (f"⟨qd{t}, kq{tag}, cols{t}, vbS{t}, vbB{t}, w{t},\n"
            f"    Q{iq}.cert.SO, Q{iq}.cert.outLo, Q{iq}.cert.outHi, H{tag}, Hb{tag},\n"
            f"    cf{tag}, cfb{tag}, Tx{tag}, sh{tag}, O{tag}, XO{tag}, CO{tag},\n"
            f"    WA{tag}, bA{tag}, {b0['shx']}, {b0['shc']}⟩")


def emit_pre(D, HS_all, prevs):
    """S3Pre: the two states and the per-(state, q) records of the checks."""
    L = [HEAD, "".join(f"import {p}\n" for p in prevs), "import GW.Endpoint.Kernel.SigmaStq\n",
         f"namespace {NS}\n{OPEN}\n"]
    L.append("instance : Inhabited SQ := ⟨⟨default, default, [], [], [], ⟨0, 0, 0, 0, 0, 0⟩, 0, [], [], [], [], "
             "⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩, [], [], [], [], [], [], [], 0, 0⟩⟩\n")
    for s, st in enumerate(D['states']):
        nm = st['name']
        L.append(f"/-- The multiplet `{nm}` (bands {st['bands']}) with its states at `k - q`. -/")
        L.append(f"noncomputable def st{nm} : St := ⟨Gk{nm}, ck{nm}, Ek{nm}, "
                 f"{LL([f'kq{nm}{t}' for t in range(len(D['qs']))])}⟩\n")
        for t in range(len(D['qs'])):
            L.append(f"noncomputable def d{nm}{t} : SQ := {sq_fields(D, HS_all[s], s, t)}\n")
        L.append(f"noncomputable def ds{nm} : List SQ := {LL([f'd{nm}{t}' for t in range(len(D['qs']))])}")
        L.append(f"noncomputable def d{nm} (t : ℕ) : SQ := ds{nm}.getD t default\n")
    L.append(f"end {NS}\n")
    return "\n".join(L)


def en_stmt(D, s, t, a, n1, iw):
    nm = D['states'][s]['name']
    tz = TZN * RD * 2 ** (SX - TZE)
    return (f"(mkEn {RN} eg.Den {SX - D['SEn']} {tz} (st{nm}.Ek.getD {a} 0) ((d{nm} {t}).kq.Eq.getD {n1} 0) {iw})")


def nstmt2(D, s, t, a, n1):
    nm = D['states'][s]['name']
    d = f"(d{nm} {t})"
    return (f"nOK kc (decide ({n1} < gl.nocc)) {en_stmt(D, s, t, a, n1, 0)} {en_stmt(D, s, t, a, n1, 1)} "
            f"(xsOf (({d}.Tx.getD {a} []).getD {n1} 0) (({d}.H.getD {a} []).getD {n1} [])) {d}.vbS {d}.cols "
            f"(({d}.sh.getD {a} []).getD {n1} 0) (({d}.O.getD {a} []).getD {n1} []) = true")


def emit_n2(D, s, t, items, prevs):
    nm = D['states'][s]['name']
    L = [HEAD, "".join(f"import {p}\n" for p in prevs), f"namespace {NS}\n{OPEN}\n"]
    for a, n1 in items:
        L.append(f"theorem n{nm}{t}_{a}_{n1} : {nstmt2(D, s, t, a, n1)} := by decide +kernel")
    L.append(f"\nend {NS}\n")
    return "\n".join(L)


def emit_c2(D, HS, s, t, prevs):
    nm = D['states'][s]['name']
    d = f"(d{nm} {t})"
    L = [HEAD, "".join(f"import {p}\n" for p in prevs), f"namespace {NS}\n{OPEN}\n"]
    for a, b in enumerate(HS['q'][t]['bands']):
        L.append(f"theorem x{nm}{t}_{a} : exOK ({d}.Hb.getD {a} []) {d}.vbB {d}.shx ({d}.XO.getD {a} (0, 0)).1 "
                 f"({d}.XO.getD {a} (0, 0)).2 = true := by decide +kernel")
        L.append(f"theorem c{nm}{t}_{a} : csOK ({d}.WA.getD {a} 0) 7 ({d}.bA.getD {a} 0) "
                 f"(zipW Prod.mk gl.Gch ((HA{nm}.getD {a} []).getD {a} [])) {d}.qd {d}.vbS {d}.cols {d}.shc "
                 f"({d}.CO.getD {a} (0, 0)).1 ({d}.CO.getD {a} (0, 0)).2 = true := by decide +kernel")
    L.append(f"\nend {NS}\n")
    return "\n".join(L)


def plan_modules(D, Q, HS_all, ecols=12, nper=5):
    """All stage-3 modules {name: text} with the import chains: one light data chain,
    then two heavy chains (entry checks + hot path of L; hot path of X + exchange/static)."""
    files = {}
    prev = "GW.Endpoint.Kernel.SigmaCheck"
    T = D['_T']
    g = eg_of(D, T)
    files['S3G'] = emit_glob(D, T, g)
    files['S3T'] = emit_tabs(D, T)
    files['S3V'] = emit_v(D, T, Q)
    prev = S3mod('S3V')
    for t in range(len(D['qs'])):
        files[f'S3E{t}'] = emit_e_data(D, Q, t, prev)
        prev = S3mod(f'S3E{t}')
    for s, st in enumerate(D['states']):
        files[f"S3St{st['name']}"] = emit_st(D, HS_all[s], s).replace("import GW.Endpoint.Kernel.Data.S3G\n",
                                                                     f"import {prev}\n")
        prev = S3mod(f"S3St{st['name']}")
    for s, st in enumerate(D['states']):
        for t in range(len(D['qs'])):
            files[f"S3K{st['name']}{t}"] = emit_k2(D, HS_all[s], s, t, prev)
            prev = S3mod(f"S3K{st['name']}{t}")
    files['S3Pre'] = emit_pre(D, HS_all, [prev, S3mod('S3T')] + [S3mod(f'Q{i}') for i in range(3)])
    base = [S3mod('S3Pre')] + [S3mod(f"Q{i}") for i in range(3)]
    # heavy chain A: entry checks, then the hot path of the second state
    pa = None
    for t in range(len(D['qs'])):
        n = len(D['qs'][t]['Gs'])
        for k, a0 in enumerate(range(0, n, ecols)):
            nm = f"S3E{t}C{k}"
            files[nm] = emit_e_chk(D, t, range(a0, min(a0 + ecols, n)), base + ([pa] if pa else []))
            pa = S3mod(nm)
    chains = {1: pa, 0: None}      # state 0 (X) on chain B, state 1 (L) on chain A
    for s in (1, 0):
        st = D['states'][s]
        nb = len(st['ck'])
        nbq = len(st['kq'][0]['cq'])
        for t in range(len(D['qs'])):
            for a in range(nb):
                occ = [n1 for n1 in range(nbq) if n1 < D['nocc']]
                unocc = [n1 for n1 in range(nbq) if n1 >= D['nocc']]
                groups = [occ] + [unocc[i:i + nper] for i in range(0, len(unocc), nper)]
                for k, grp in enumerate(groups):
                    nm = f"S3N{st['name']}{t}_{a}_{k}"
                    pv = base + ([chains[s]] if chains[s] else [])
                    files[nm] = emit_n2(D, s, t, [(a, n1) for n1 in grp], pv)
                    chains[s] = S3mod(nm)
    for s, st in enumerate(D['states']):
        for t in range(len(D['qs'])):
            nm = f"S3C{st['name']}{t}"
            files[nm] = emit_c2(D, HS_all[s], s, t, base + [chains[0]])
            chains[0] = S3mod(nm)
    return files, [chains[1], chains[0]]


def ltotz(HS, nq, nb, nbq, iw, k):
    """Python value of `Sig.LtotZ` (the hint total of one state)."""
    tot = 0
    for t in range(nq):
        for a in range(nb):
            b = HS['q'][t]['bands'][a]
            tot += 4 * b['xo'][k] + b['co'][k]
            for n1 in range(nbq):
                o = b['n1'][n1]['o']
                tot += o[4 + k] + 2 * o[2 * iw + k]
    return tot


def final_bounds(D, HS_all):
    """The Eqp1 / O1 enclosure the Lean assembly derives from the hint totals (exact)."""
    RY = Fr(RN, RD)
    X = Fr(D['nq']) * Fr(D['OmN'], 2 ** D['SOm'])
    out = []
    for s, st in enumerate(D['states']):
        nb = len(st['ck'])
        nbq = len(st['kq'][0]['cq'])
        L = {(iw, k): ltotz(HS_all[s], D['nq'], nb, nbq, iw, k) for iw in (0, 1) for k in (0, 1)}
        c = RY / (nb * X * 4 * 2 ** SOUT)
        eo = sum(RY * Fr(e, 2 ** D['SEn']) for e in st['Ek']) / nb
        assert c * L[0, 1] < 0 and c * L[1, 1] - c * L[0, 0] < 1
        lo = eo + c * L[0, 0] / (1 - (c * L[1, 1] - c * L[0, 0]))
        hi = eo + c * L[0, 1] / (1 - (c * L[1, 0] - c * L[0, 1]))
        out.append(dict(L=L, lo=lo, hi=hi))
    return out


def main_sigma(a):
    import pickle
    sys.set_int_max_str_digits(0)
    t0 = time.time()
    if a.sigma_pkl and pathlib.Path(a.sigma_pkl).exists():
        rec = pickle.loads(pathlib.Path(a.sigma_pkl).read_bytes())
    else:
        rec = capture_sigma(a.rundir)
        if a.sigma_pkl:
            pathlib.Path(a.sigma_pkl).write_bytes(pickle.dumps(rec))
    print(f"captured ({time.time() - t0:.1f}s)", flush=True)
    D, T, g, Q = build(rec)
    D['_T'] = T
    print(f"entries ({time.time() - t0:.1f}s):",
          {c: sum(r[0] == c for q in Q for col in q['cols'] for r in col) for c in range(4)}, flush=True)
    HS_all = [hints_state(D, T, Q, s) for s in range(len(D['states']))]
    print(f"hints ({time.time() - t0:.1f}s)", flush=True)
    fb = final_bounds(D, HS_all)
    o1 = (fb[0]['lo'] - fb[1]['hi'], fb[0]['hi'] - fb[1]['lo'])
    clo, chi = Fr(0.015405752349084699), Fr(0.015405753672648183)
    print(f"Eqp1 X in [{float(fb[0]['lo'])!r}, {float(fb[0]['hi'])!r}], L in [{float(fb[1]['lo'])!r}, "
          f"{float(fb[1]['hi'])!r}]; O1 in [{float(o1[0])!r}, {float(o1[1])!r}] eV, "
          f"inside cert_o1: {clo <= o1[0] and o1[1] <= chi}", flush=True)
    if a.lean:
        files, ends = plan_modules(D, Q, HS_all, ecols=a.sigma_ecols, nper=a.sigma_nper)
        files['S3Check'] = emit_check(D, HS_all, fb, ends)
        files['S3Tamper'] = emit_tamper(D, Q, HS_all)
        od = pathlib.Path(a.outdir)
        for old in od.glob("S3*.lean"):
            old.unlink()
        for mod, text in files.items():
            (od / f"{mod}.lean").write_text(text)
        print(f"wrote {len(files)} modules; chain ends {ends}", flush=True)
    return 0


def chain_term(n, name_of):
    t = "(forall_lt_zero _)"
    for k in range(n):
        t = f"(forall_lt_succ_of (k := {k}) {t} {name_of(k)})"
    return t


def emit_check(D, HS_all, fb, ends):
    """S3Check: the TRUE eps⁻¹ blocks, the per-(state, q) facts, the state totals, Eqp1
    and the final theorem."""
    T = D['_T']
    tz = TZN * RD * 2 ** (SX - TZE)
    she = SX - D['SEn']
    params = f"eg kc {SQ} {SOUT} {RN} {she} {tz} {T['Wv']} {T['bv']} vbT oqT"
    L = [HEAD, "".join(f"import {e}\n" for e in ends),
         "import GW.Endpoint.Kernel.Data.E0Check\nimport GW.Endpoint.Kernel.Data.E1Check\n"
         "import GW.Endpoint.Kernel.Data.E2Check\nimport GW.Endpoint.Kernel.SigmaAsm\n",
         f"namespace {NS}\n{OPEN} Finset\n"]
    L.append('''/-- The TRUE eps⁻¹ of the three irreducible blocks (stage 2: `E{i}.epsTrue` is the static RPA
eps computed from the wavefunction coefficients), as a function (`0` outside the block). -/
noncomputable def Etrue (iq a b : ℕ) : ℝ :=
  if iq = 0 then (if h : a < Q0.cert.n ∧ b < Q0.cert.n then E0.epsTrue⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else if iq = 1 then (if h : a < Q1.cert.n ∧ b < Q1.cert.n then E1.epsTrue⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else if iq = 2 then (if h : a < Q2.cert.n ∧ b < Q2.cert.n then E2.epsTrue⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else 0
''')
    for i in range(3):
        L.append(f'''theorem shp{i} : Q{i}.cert.outLo.length = Q{i}.cert.n ∧ Q{i}.cert.outHi.length = Q{i}.cert.n ∧
    Q{i}.cert.outLo.all (fun r => r.length == Q{i}.cert.n) = true ∧
    Q{i}.cert.outHi.all (fun r => r.length == Q{i}.cert.n) = true := by decide +kernel

theorem hE{i} : EHyp Etrue {i} Q{i}.cert.SO Q{i}.cert.outLo Q{i}.cert.outHi :=
  EHyp_block Q{i}.cert E{i}.epsTrue⁻¹ E{i}.epsinv_true_q{i}.2 shp{i}.1 shp{i}.2.1
    (fun r hr => by simpa using List.all_eq_true.mp shp{i}.2.2.1 r hr)
    (fun r hr => by simpa using List.all_eq_true.mp shp{i}.2.2.2 r hr) Etrue {i}
    (fun a b => by unfold Etrue; simp)
''')
    # global facts
    L.append(f'''theorem rhoP : tpackS eg.W (tslots 7 eg.bias gl.rho) = tpackS eg.W rhoS := by rw [← rhoS_eq]; rfl
theorem g_rk : keysOK 7 (gl.rho.map Prod.fst) = true := by rw [← mapL_eq]; exact rho_keys
theorem g_rv : valsOK eg.W eg.bias (gl.rho.map Prod.snd) = true := by rw [← mapL_eq]; exact rho_vals
theorem g_vk : keysOK 7 (vbT.map Prod.fst) = true := by rw [← mapL_eq]; exact vb_keys
theorem g_vl : valsOK {T['Wv']} {T['bv']} (vbT.map (fun p => p.2.1)) = true := by rw [← mapL_eq]; exact vb_vals.1
theorem g_vh : valsOK {T['Wv']} {T['bv']} (vbT.map (fun p => p.2.2)) = true := by rw [← mapL_eq]; exact vb_vals.2
theorem g_dig0 : tget eg.W 7 (tpackS eg.W rhoS) 0 ≠ 0 ∧ tget eg.W 7 (tpackS eg.W rhoS) 0 ≠ eg.bias := by
  decide +kernel
theorem g_nel : nelec gl ≠ 0 := by
  have h := rho_dig (d := 0) g_rk g_rv (by decide)
  rw [rhoP] at h
  exact nelec_ne h g_dig0.1 g_dig0.2
theorem g_ts : TS = (eg.tsn : ℝ) / 2 ^ eg.tse := by unfold TS; norm_num [eg]
theorem g_tz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze := by unfold TZ; norm_num [kc]
theorem g_k2 : (kc.Den2 : ℝ) = (eg.Den : ℝ) ^ 2 := by
  have : kc.Den2 = eg.Den ^ 2 := by decide +kernel
  rw [this]; push_cast; ring
theorem g_RN : ((1360569253 : ℕ) : ℝ) / 10 ^ 8 = RYD := by unfold RYD; norm_num
theorem g_D1 : (eg.Den : ℝ) = 10 ^ 8 * 2 ^ (gl.SEn + {she}) := by
  have : eg.Den = 10 ^ 8 * 2 ^ (gl.SEn + {she}) := by decide +kernel
  rw [this]; push_cast; ring
theorem g_tz' : (({tz} : ℕ) : ℝ) = TZ * eg.Den := by
  have : eg.Den = 10 ^ 8 * 2 ^ {SX} := by decide +kernel
  rw [this]; unfold TZ; push_cast; norm_num
''')
    for s, st in enumerate(D['states']):
        nm = st['name']
        nb = len(st['ck'])
        nbq = len(st['kq'][0]['cq'])
        for t, qd in enumerate(D['qs']):
            n = len(qd['Gs'])
            tag = f"{nm}{t}"
            if qd['qh'] == (0, 0, 0):
                wing = "fun h => absurd rfl h"
            else:
                ol, oh = [(lo, hi) for g_, lo, hi in D['oqT'] if g_ == qd['qh']][0]
                wing = f"fun _ => ⟨{ol}, {oh}, w{t}_ok⟩"
            hn = chain_term(nb, lambda a: "(" + chain_term(nbq, lambda n1, a=a: f"n{nm}{t}_{a}_{n1}") + ")")
            L.append(f'''theorem ok{tag} : StqOK gl st{nm} {t} (d{nm} {t}) {params} HA{nm} cfA{nm} where
  hq := rfl
  hkq := rfl
  hSB := rfl
  hB := rfl
  hSR := rfl
  hSOm := rfl
  hOm := rfl
  hOm0 := by decide
  hRN := rfl
  hts := g_ts
  htsn := by decide
  hwinv := rfl
  hDen0 := by decide
  hh := rfl
  hk2 := g_k2
  hl := rfl
  htz := g_tz
  hRNe := g_RN
  hD1 := g_D1
  htz' := g_tz'
  hrk := g_rk
  hrv := g_rv
  hnel := g_nel
  hvk := g_vk
  hvl := g_vl
  hvh := g_vh
  hvbS := by rw [vloS_eq, vhiS_eq]; exact vbS{t}_ok
  hvbB := by rw [vloS_eq, vhiS_eq]; exact vbB{t}_ok
  hwing := {wing}
  hgs := gs{t}_box
  hent := by
    rw [rhoP]
    show ∀ i < {n}, _
    exact {chain_term(n, lambda i: f"e{t}_{i}")}
  hkok := kok{tag}
  hkokb := kokb{tag}
  hkokA := kokA{nm}
  hxs := xs{tag}
  hsh := sh{tag}_ok
  hn := by
    show ∀ a < {nb}, ∀ n1 < {nbq}, _
    exact {hn}
  hex := by
    show ∀ a < {nb}, _
    exact {chain_term(nb, lambda a: f"x{tag}_{a}")}
  hshx := rfl
  hcs := by
    show ∀ a < {nb}, _
    exact {chain_term(nb, lambda a: f"c{tag}_{a}")}
  hshc := rfl
  hgk := gch_keys
  hnocc := by decide
''')
        nq = len(D['qs'])
        Lv = fb[s]['L']
        L.append(f'''theorem ok{nm} : ∀ t < gl.qs.length, StqOK gl st{nm} t (d{nm} t) {params} HA{nm} cfA{nm} := by
  show ∀ t < {nq}, _
  exact {chain_term(nq, lambda t: f"ok{nm}{t}")}

theorem hE{nm} : ∀ t < gl.qs.length, EHyp Etrue (d{nm} t).qd.iq (d{nm} t).SO (d{nm} t).Elo (d{nm} t).Ehi := by
  show ∀ t < {nq}, _
  exact {chain_term(nq, lambda t: f"hE{D['qs'][t]['iq']}")}
''')
        for iw in (0, 1):
            for k in (0, 1):
                L.append(f"noncomputable def L{nm}{iw}{k}v : ℤ := {ke_int(Lv[iw, k])}")
                L.append(f"theorem L{nm}{iw}{k} : LtotZ d{nm} gl.qs.length st{nm}.ck.length (nbq st{nm}) {iw} {k} = "
                         f"L{nm}{iw}{k}v := by decide +kernel")
        RY = Fr(RN, RD)
        X = Fr(D['nq']) * Fr(D['OmN'], 2 ** D['SOm'])
        c = RY / (nb * X * 4 * 2 ** SOUT)
        eo = sum(RY * Fr(e, 2 ** D['SEn']) for e in st['Ek']) / nb
        L.append(f"noncomputable def c{nm}v : ℝ := {c.numerator} / {c.denominator}")
        L.append(f"noncomputable def eo{nm}v : ℝ := {ke_int(eo.numerator)} / {eo.denominator}")
        L.append(f"theorem c{nm}_eq : RYD / (st{nm}.ck.length * (Nq gl * vol gl) * 4 * 2 ^ {SOUT}) = c{nm}v := by")
        L.append(f"  have hl : st{nm}.ck.length = {nb} := by decide +kernel")
        L.append(f"  have hq : gl.qs.length = {D['nq']} := by decide +kernel")
        L.append(f"  rw [hl]; unfold RYD Nq vol dy c{nm}v; rw [hq]; norm_num [gl]")
        hs = [f"  have h{a} : st{nm}.Ek.getD {a} 0 = {ke_int(e)} := by decide +kernel" for a, e in enumerate(st['Ek'])]
        L.append(f"theorem eo{nm}_eq : avg st{nm} (fun a => RYD * dy gl.SEn (st{nm}.Ek.getD a 0)) = eo{nm}v := by")
        L.append(f"  have hl : st{nm}.ck.length = {nb} := by decide +kernel")
        L.extend(hs)
        L.append(f"  unfold avg; rw [hl]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, "
                 + ", ".join(f"h{a}" for a in range(nb)) + f"]; unfold RYD dy eo{nm}v; norm_num [gl]")
        L.append("")
    L.append(emit_final(D, fb))
    L.append(f"end {NS}\n")
    return "\n".join(L)


def ke_int(x):
    return str(x) if x >= 0 else f"({x})"


def dy_lit(x):
    """A double as an exact Lean rational literal `m / 2^e`."""
    p, q = float(x).as_integer_ratio()
    e = q.bit_length() - 1
    assert q == 1 << e
    return p, e


def emit_final(D, fb):
    lo_p, lo_e = dy_lit(0.015405752349084699)
    hi_p, hi_e = dy_lit(0.015405753672648183)
    L = []
    L.append(f'''/-- The Coulomb hypothesis on `oneoverq`, scaled. -/
theorem oq_scaled {{oq : V3 → ℝ}} (h : VbHyp oqT eg.SV oq) :
    ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ eg.SV ∧ oq p.1 * 2 ^ eg.SV ≤ p.2.2 := h.scaled

theorem hX : 0 < Nq gl * vol gl := by
  unfold Nq vol dy; norm_num [gl, qs]
''')
    for s, st in enumerate(D['states']):
        nm = st['name']
        L.append(f'''/-- **Eqp1 of `{nm}`** in the kernel-derived enclosure. -/
theorem eqp{nm} (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) :
    let c := RYD / (st{nm}.ck.length * (Nq gl * vol gl) * 4 * 2 ^ {SOUT})
    let eo := avg st{nm} (fun a => RYD * dy gl.SEn (st{nm}.Ek.getD a 0))
    eo + c * (L{nm}00v : ℝ) / (1 - (c * L{nm}11v - c * L{nm}00v)) ≤ eqp1 gl Etrue vb oq st{nm} ∧
      eqp1 gl Etrue vb oq st{nm} ≤ eo + c * (L{nm}01v : ℝ) / (1 - (c * L{nm}10v - c * L{nm}01v)) := by
  have s0 := sig_bounds d{nm} ok{nm} hE{nm} hvb (oq_scaled hoq) hX 0 (by norm_num)
  have s1 := sig_bounds d{nm} ok{nm} hE{nm} hvb (oq_scaled hoq) hX 1 (by norm_num)
  rw [Ltot_cast, Ltot_cast, L{nm}00, L{nm}01] at s0
  rw [Ltot_cast, Ltot_cast, L{nm}10, L{nm}11] at s1
  exact eqp1_bounds gl Etrue vb oq st{nm} {SOUT} (by decide) hX s0 s1
    (by rw [c{nm}_eq]; norm_num [L{nm}01v, c{nm}v]) (by rw [c{nm}_eq]; norm_num [L{nm}11v, L{nm}00v, c{nm}v])
''')
    L.append(f'''/-- **O1 enclosure (spec A, kernel-checked).** For every value of the mini-BZ Coulomb
averages `vb` and `oneoverq` inside their certified boxes (`coulomb_cert.json`), the
observable `O1 = Eqp1(X, bands 5-6 avg) - Eqp1(L, band 5)` of spec A, evaluated on the TRUE
eps⁻¹ (stage 2, from the wavefunction coefficients), lies in cert.py's enclosure
`[0.015405752349084699, 0.015405753672648183]` eV (the binary64 bounds of `cert_o1.json`). -/
theorem o1_enclosure (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) :
    O1 gl stX stL Etrue vb oq ∈ Set.Icc (({lo_p} : ℝ) / 2 ^ {lo_e}) (({hi_p} : ℝ) / 2 ^ {hi_e}) := by
  have hx := eqpX vb oq hvb hoq
  have hl := eqpL vb oq hvb hoq
  simp only [] at hx hl
  rw [cX_eq, eoX_eq] at hx
  rw [cL_eq, eoL_eq] at hl
  obtain ⟨x1, x2⟩ := hx
  obtain ⟨l1, l2⟩ := hl
  unfold O1
  constructor
  · have : (({lo_p} : ℝ) / 2 ^ {lo_e}) ≤ eoXv + cXv * (LX00v : ℝ) / (1 - (cXv * LX11v - cXv * LX00v)) -
        (eoLv + cLv * (LL01v : ℝ) / (1 - (cLv * LL10v - cLv * LL01v))) := by
      norm_num [eoXv, eoLv, cXv, cLv, LX00v, LX11v, LL01v, LL10v]
    linarith
  · have : eoXv + cXv * (LX01v : ℝ) / (1 - (cXv * LX10v - cXv * LX01v)) -
        (eoLv + cLv * (LL00v : ℝ) / (1 - (cLv * LL11v - cLv * LL00v))) ≤ (({hi_p} : ℝ) / 2 ^ {hi_e}) := by
      norm_num [eoXv, eoLv, cXv, cLv, LX01v, LX10v, LL00v, LL11v]
    linarith

/-- **C1 for spec A**: `Eqp1(X) > Eqp1(L)`. The theorem compares X and L only; that the
minimum over ALL sampled k-points (Γ included) is at L is the Python `CBM_certainly_at_L`
of `cert_o1.json`, not a Lean statement. -/
theorem o1_pos (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) :
    0 < O1 gl stX stL Etrue vb oq :=
  lt_of_lt_of_le (by norm_num) (o1_enclosure vb oq hvb hoq).1
''')
    return "\n".join(L)


def emit_tamper(D, Q, HS_all):
    """S3Tamper: negative controls -- one perturbed input or claim makes a check false."""
    s, t = 1, 1                       # state L, q-point 1
    st = D['states'][s]
    nm = st['name']
    tag = f"{nm}{t}"
    qd = D['qs'][t]
    iq = qd['iq']
    cols = Q[t]['cols']
    j = next(j for j in range(len(cols[0])) if cols[0][j][0] == 2)
    r = cols[0][j]
    w = r[2] - r[1]
    rt = (r[0], r[2] + 2 * w + 1, r[2] + 3 * w + 3, r[3], r[4])   # the I box moved above the truth
    kq = st['kq'][t]
    x = kq['cq'][0][0]
    b = max(abs(x).bit_length() - 20, 0)
    cq0 = [x ^ (1 << b)] + kq['cq'][0][1:]
    vb0 = Q[t]['vbS'][0]
    vbt = [(vb0[0] + 2, vb0[1] + 2)] + Q[t]['vbS'][1:]
    o = HS_all[s]['q'][t]['bands'][0]['n1'][5]['o']
    ot = [o[1], o[1]] + o[2:]
    d = f"(d{nm} {t})"
    L = [HEAD, "import GW.Endpoint.Kernel.Data.S3Check\n", f"namespace {NS}\n{OPEN}\n"]
    L.append(f"/-- Entry `({j}, 0)` of q-point {t} with its `I_eps` box moved above the true value. -/")
    L.append(f"theorem tamper_ent : entChk eg Q{iq}.cert.SO w{t} qd{t} Q{iq}.cert.outLo Q{iq}.cert.outHi vbS{t} "
             f"(tpackS eg.W rhoS) {j} 0 {lent(rt)} = false := by decide +kernel")
    L.append(f"theorem control_ent : entChk eg Q{iq}.cert.SO w{t} qd{t} Q{iq}.cert.outLo Q{iq}.cert.outHi vbS{t} "
             f"(tpackS eg.W rhoS) {j} 0 {lent(r)} = true := by decide +kernel\n")
    L.append(f"/-- Band 0 of the states at `k - q` (q-point {t}, state {nm}), coefficient 0 with bit {b} flipped. -/")
    L.append(f"noncomputable def cq0flip : List ℤ := {LL([lz(v) for v in cq0])}")
    L.append(f"theorem tamper_coef : kOK cf{tag} qd{t}.Gs ⟨Gk{nm}, ck{nm}, Ek{nm}, Gq{tag}, cq0flip :: cq{tag}.tail, "
             f"Eq{tag}⟩ H{tag} = false := by decide +kernel\n")
    L.append(f"/-- The Coulomb box of `Gs₀` shifted by two units of the last place. -/")
    L.append(f"theorem tamper_vb : vbOK {D['_T']['Wv']} 7 {D['_T']['bv']} (tpackS {D['_T']['Wv']} vloS) "
             f"(tpackS {D['_T']['Wv']} vhiS) qd{t} qd{t}.Gs {lvb(vbt)} = false := by decide +kernel\n")
    L.append(f"/-- The claimed enclosure of `2 P0` (band 0, inner band 5) collapsed to its upper end. -/")
    L.append(f"theorem tamper_out : nOK kc (decide (5 < gl.nocc)) {en_stmt(D, s, t, 0, 5, 0)} {en_stmt(D, s, t, 0, 5, 1)} "
             f"(xsOf (({d}.Tx.getD 0 []).getD 5 0) (({d}.H.getD 0 []).getD 5 [])) {d}.vbS {d}.cols "
             f"(({d}.sh.getD 0 []).getD 5 0) {LL([lz(v) for v in ot])} = false := by decide +kernel")
    L.append(f"\nend {NS}\n")
    return "\n".join(L)


# ------------------------------------------------------------ G2 unfolding (--unfold)
#
# The irreducible data of WFN / WFNq / WFN_inner (bgwio's reader, exact dyadics of the
# file's binary64 numbers), the eps q-points and cutoffs (eps0mat / epsmat headers) and
# Sigma's k-points (sigma.inp), as Lean data for GW/Endpoint/Kernel/Unfold.lean, plus
# the modules that kernel-check that stage 2's and stage 3's inputs ARE the Lean
# unfolding of that data (`decide +kernel` equalities), and the composed theorems.
# An exact Python mirror of the Lean definitions is run first (asserted equal to
# cert.real_coeffs / spec's spheres and mapping) so a mismatch shows here, not after a
# long build.

U_SK = 64


def u_dy(x):
    p, d = float(x).as_integer_ratio()
    e = d.bit_length() - 1
    assert d == 1 << e
    return (p < 0, abs(p), e)


def u_ldy(d):
    return f"⟨{'true' if d[0] else 'false'}, {d[1]}, {d[2]}⟩"


def u_enc(S, d):
    neg, m, e = d
    assert e <= S
    v = m << (S - e)
    return -v if neg else v


def u_kn(S, x):
    return tuple(u_enc(S, u_dy(v)) for v in x)


def u_mv(M, g):
    return tuple(sum(int(M[a][b]) * g[b] for b in range(3)) for a in range(3))


def u_near(S, x, tol, strict):
    g = (2 * x + (1 << S)) // (1 << (S + 1))
    r = tol * abs(x - g * (1 << S))
    return g if (r < (1 << S) if strict else r <= (1 << S)) else None


def u_near3(S, x, tol, strict):
    g = [u_near(S, v, tol, strict) for v in x]
    return None if any(v is None for v in g) else tuple(g)


class UWfn:
    """Exact mirror of `Unf.Wfn` and its functions."""

    def __init__(self, path):
        import bgwio
        w = bgwio.read_wfn(path)
        self.w = w
        self.M = [tuple(tuple(int(v) for v in r) for r in m) for m in w['mtrx']]
        assert all(np.array_equal(np.array(a), m) for a, m in zip(self.M, w['mtrx']))
        t2 = w['tnp'] / np.pi
        assert np.allclose(t2, np.rint(t2), atol=1e-12)
        self.t2 = [tuple(int(round(v)) for v in r) for r in t2]
        self.tnp = [tuple(u_dy(v) for v in r) for r in w['tnp']]
        self.kpt = [tuple(u_dy(v) for v in k) for k in w['kpt']]
        self.k = [tuple(u_enc(U_SK, d) for d in k) for k in self.kpt]
        self.kw = [u_dy(v) for v in w['kw']]
        self.kg = [[tuple(int(v) for v in g) for g in G] for G in w['kg']]
        self.coef = [[[u_dy(v) for v in r] for r in c] for c in w['coef']]
        self.en = [[u_dy(v) for v in r] for r in w['energies'][0]]
        self.bdot = [[u_dy(v) for v in r] for r in w['bdot']]
        self.celvol = u_dy(w['celvol'])
        self.gvec = [tuple(int(v) for v in g) for g in w['gvec']]
        for ik in range(len(self.kg)):
            assert all(len(r) == len(self.kg[ik]) for r in self.coef[ik])

    def find(self, kp):
        for ik, k in enumerate(self.k):
            for iop, M in enumerate(self.M):
                Mk = u_mv(M, k)
                g = u_near3(U_SK, tuple(a - b for a, b in zip(kp, Mk)), 10 ** 9, True)
                if g is not None:
                    return ik, iop, g
        return None

    def st(self, kp):
        ik, iop, g = self.find(kp)
        M, t2 = self.M[iop], self.t2[iop]
        G = self.kg[ik]
        s = [sum(a * b for a, b in zip(u_mv(M, x), t2)) % 2 == 1 for x in G]
        Gn = [tuple(a - b for a, b in zip(u_mv(M, x), g)) for x in G]
        c = [[(d[0] ^ f, d[1], d[2]) for f, d in zip(s, r)] for r in self.coef[ik]]
        return Gn, c, self.en[ik]

    def images(self, k):
        S = U_SK
        return [tuple(x - (1 << S) * ((10 ** 9 * x + (1 << S)) // (10 ** 9 * (1 << S))) for x in u_mv(M, k))
                for M in self.M]

    @staticmethod
    def dedup(l):
        out = []
        for p in l:
            if p not in out:
                out.append(p)
        return out

    def kfull(self):
        return self.dedup([p for k in self.k for p in self.images(k)])

    def n2(self, SB, q, G):
        u = [q[a] + (G[a] << U_SK) for a in range(3)]
        B = [[u_enc(SB, d) for d in r] for r in self.bdot]
        return sum(u[a] * B[a][b] * u[b] for a in range(3) for b in range(3))

    def sphere(self, SB, q, ecut):
        c = u_enc(2 * U_SK + SB, u_dy(ecut))
        return [G for G in self.gvec if self.n2(SB, q, G) < c]

    def bgw(self, SB, q, ecut):
        g = np.array(self.gvec)
        E = tuple(int(v) for v in g.max(axis=0) - np.minimum(g.min(axis=0), 0) + 1) if False else None
        mx = [max([0] + [x[a] for x in self.gvec]) for a in range(3)]
        mn = [min([0] + [x[a] for x in self.gvec]) for a in range(3)]
        E = [mx[a] - mn[a] + 1 for a in range(3)]
        S = 2 * U_SK + SB
        byn = sorted([(self.n2(SB, q, G), G) for G in self.sphere(SB, q, ecut)], key=lambda t: t[0])
        gid, out = 0, []
        for i, (a, G) in enumerate(byn):
            if i and (1 << S) < 10 ** 12 * (a - byn[i - 1][0]):
                gid += 1
            out.append(((gid, G[2] + E[2] * (G[1] + E[1] * G[0])), G))
        keyed = sorted(out, key=lambda t: t[0])
        ties = all(10 ** 14 * (b[0] - a[0]) <= (1 << S) or (1 << S) < 10 ** 10 * (b[0] - a[0])
                   for a, b in zip(byn, byn[1:]))
        return [G for _, G in keyed], ties


def u_adj(M):
    a, b, c = M
    return ((b[1] * c[2] - b[2] * c[1], a[2] * c[1] - a[1] * c[2], a[1] * b[2] - a[2] * b[1]),
            (b[2] * c[0] - b[0] * c[2], a[0] * c[2] - a[2] * c[0], a[2] * b[0] - a[0] * b[2]),
            (b[0] * c[1] - b[1] * c[0], a[1] * c[0] - a[0] * c[1], a[0] * b[1] - a[1] * b[0]))


def u_det(M):
    a, b, c = M
    return a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0])


def u_qd(wi, SB, irr, ecuts, ecutb, qh):
    q = tuple(x << (U_SK - 1) for x in qh)
    Gs, ties = wi.bgw(SB, q, ecuts)
    Gb = wi.sphere(SB, q, ecutb)
    last = None
    for iq, (qi, G) in enumerate(irr):
        for iop, M in enumerate(wi.M):
            g = u_near3(U_SK, tuple(a - b for a, b in zip(u_mv(M, qi), q)), 10 ** 6, False)
            if g is not None:
                last = (iq, iop, g)
    iq, iop, g0 = last
    M, t2 = wi.M[iop], wi.t2[iop]
    d = u_det(M)
    Mi = tuple(tuple(d * x for x in r) for r in u_adj(M))
    Gi = [u_mv(Mi, tuple(a - b for a, b in zip(G, g0))) for G in Gs]
    G0 = Gi[0]
    idx = [irr[iq][1].index(g) for g in Gi]
    neg = [sum(a * b for a, b in zip(u_mv(M, tuple(x - y for x, y in zip(g, G0))), t2)) % 2 == 1 for g in Gi]
    return dict(qh=qh, Gs=Gs, Gb=Gb, iq=iq, idx=idx, neg=neg, z=Gs.index(g0), ties=ties, iop=iop)


def unfold_mirror(rundir):
    """Exact mirror of the Lean definitions, asserted equal to cert.py / spec.py."""
    import cert
    import spec
    R = pathlib.Path(rundir)
    W = {n: UWfn(R / n) for n in ("WFN", "WFNq", "WFN_inner")}
    w, wq, wi = W["WFN"], W["WFNq"], W["WFN_inner"]
    for x in (wq, wi):
        assert x.M == w.M and x.t2 == w.t2
    run = spec.Run(rundir)
    er = spec.EpsilonRun(rundir, run.nbands, run.ecuts)
    kf = w.kfull()
    assert [tuple(u_kn(U_SK, k)) for k in er.kfull] == kf
    qs = [(run.eps0["q"][0]["q"], True)] + [(b["q"], False) for b in run.eps["q"]]
    SB = max(_dexp(x) for x in w.w['bdot'].ravel())

    def same(a, b):
        Ga, ca, Ea = a
        Gb, cb, Eb = b
        f = lambda d: (-1 if d[0] else 1) * Fr(d[1], 1 << d[2])
        return ([tuple(int(v) for v in g) for g in Gb] == Ga
                and all(f(x) == Fr(float(y)) for r, rb in zip(ca, cb) for x, y in zip(r, rb))
                and len(ca) == len(cb) and all(f(x) == Fr(float(y)) for x, y in zip(Ea, Eb)))
    blocks = []
    for q, q0 in qs:
        qn = u_kn(U_SK, q)
        src, psrc = (wq, er.wfq) if q0 else (w, er.wf)
        for k, kk in zip(er.kfull, kf):
            assert same(w.st(kk), cert.real_coeffs(er.wf, tuple(k)))
            kp = tuple(a + b for a, b in zip(kk, qn))
            assert same(src.st(kp), cert.real_coeffs(psrc, tuple(np.round(k + q, 12))))
        Gs = w.sphere(SB, qn, run.ecuts)
        Gpy, _ = spec.sphere_of(er.cr, er.gvec, q, run.ecuts)
        assert Gs == [tuple(int(v) for v in g) for g in Gpy]
        blocks.append(((0, 0, 0) if q0 else qn, Gs))
    qd = []
    for t, q in enumerate(run.qlist):
        qh = tuple(int(round(2 * x)) for x in q)
        d = u_qd(wi, SB, blocks, run.ecuts, run.ecutb, qh)
        m = spec.Screening(run, None, None, blocks=[(np.array(G), None) for _, G in blocks]).mapping(q)
        Gs_py, b, is0, iop, g0, Gi, phase, nops, qi = m
        rel = phase / phase[0]
        Gpy_ = [tuple(int(v) for v in g) for g in Gs_py]
        if d['Gs'] != Gpy_ or not d['ties']:
            bad = [i for i, (x, y) in enumerate(zip(d['Gs'], Gpy_)) if x != y]
            print('MISMATCH', t, qh, d['ties'], len(d['Gs']), len(Gpy_), bad[:10], [(d['Gs'][i], Gpy_[i], wi.n2(SB, tuple(x << (U_SK - 1) for x in qh), d['Gs'][i]), wi.n2(SB, tuple(x << (U_SK - 1) for x in qh), Gpy_[i])) for i in bad[:4]])
            raise AssertionError
        assert d['iop'] == iop and d['z'] == int(np.flatnonzero(np.all(Gs_py == g0, axis=1))[0])
        assert d['neg'] == [bool(x < 0) for x in np.rint(rel.real)]
        assert d['Gb'] == [tuple(int(v) for v in g) for g in run.sphere(q, run.ecutb)[0]]
        qd.append(d)
    for ik in (1, 2):
        k = run.kpts[ik]
        kk = u_kn(U_SK, k)
        assert same(wi.st(kk), cert.real_coeffs(run.wf, tuple(k)))
        for q in run.qlist:
            assert same(wi.st(u_kn(U_SK, k - q)), cert.real_coeffs(run.wf, tuple(k - q)))
    Gch = wi.sphere(SB, (0, 0, 0), max(run.ecuts, run.ecutb))
    assert Gch == [tuple(int(v) for v in g) for g in run.sphere(np.zeros(3), max(run.ecuts, run.ecutb))[0]]
    print(f"unfold mirror: kfull {len(kf)} points, 3 eps q-points x 32 k, 8 Sigma q-points: all equal "
          f"to cert.real_coeffs / spec (SB={SB})", flush=True)
    return dict(W=W, run=run, qs=qs, kf=kf, qd=qd, SB=SB)


def u_lv(g):
    return f"({lit_int(g[0])}, {lit_int(g[1])}, {lit_int(g[2])})"


def u_wfn_lean(name, x):
    """One `Unf.Wfn` as definitions (one per band row)."""
    out = []
    ops = [f"⟨({u_lv(M[0])}, {u_lv(M[1])}, {u_lv(M[2])}), {u_lv(t)}⟩" for M, t in zip(x.M, x.t2)]
    out.append(f"noncomputable def {name}ops : List Op := " + lean_list(ops))
    out.append(f"noncomputable def {name}tnp : List (Dy × Dy × Dy) := "
               + lean_list([f"({u_ldy(a)}, {u_ldy(b)}, {u_ldy(c)})" for a, b, c in x.tnp]))
    ch = [x.gvec[i:i + 100] for i in range(0, len(x.gvec), 100)]
    for i, c in enumerate(ch):
        out.append(f"noncomputable def {name}gvec_{i} : List V3 := " + lean_list([u_lv(g) for g in c]))
    out.append(f"noncomputable def {name}gvec : List V3 := " + " ++ ".join(f"{name}gvec_{i}" for i in range(len(ch))))
    kg, co, en = [], [], []
    for ik in range(len(x.kg)):
        out.append(f"noncomputable def {name}kg{ik} : List V3 := " + lean_list([u_lv(g) for g in x.kg[ik]]))
        rows = []
        for b, r in enumerate(x.coef[ik]):
            out.append(f"noncomputable def {name}c{ik}_{b} : List Dy := " + lean_list([u_ldy(d) for d in r]))
            rows.append(f"{name}c{ik}_{b}")
        out.append(f"noncomputable def {name}c{ik} : List (List Dy) := " + lean_list(rows))
        out.append(f"noncomputable def {name}e{ik} : List Dy := " + lean_list([u_ldy(d) for d in x.en[ik]]))
        kg.append(f"{name}kg{ik}")
        co.append(f"{name}c{ik}")
        en.append(f"{name}e{ik}")
    bd = lean_list([lean_list([u_ldy(d) for d in r]) for r in x.bdot])
    out.append(f"""/-- The irreducible data of `{x.path}` (exact). -/
noncomputable def {name} : Wfn where
  ops := {name}ops
  tnp := {name}tnp
  kpt := {lean_list([f"({u_ldy(a)}, {u_ldy(b)}, {u_ldy(c)})" for a, b, c in x.kpt])}
  kw := {lean_list([u_ldy(d) for d in x.kw])}
  kg := {lean_list(kg)}
  coef := {lean_list(co)}
  en := {lean_list(en)}
  bdot := {bd}
  celvol := {u_ldy(x.celvol)}
  gvec := {name}gvec
""")
    return "\n".join(out) + "\n"


U_HDR = """/- Generated by bgw/endpoint/kernel_export.py --unfold (do not edit). G2 unfolding:
{what} -/
"""


def u_mod(what, imports, body, ns="GW.Endpoint.Kernel.U"):
    imp = "\n".join(f"import {m}" for m in imports)
    return (U_HDR.format(what=what) + imp + f"\n\nnamespace {ns}\nopen GW.Endpoint.Kernel "
            "GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Unf\n\n" + body
            + f"\nend {ns}\n")


def u_dy3(q):
    return "(" + ", ".join(u_ldy(u_dy(v)) for v in q) + ")"


def lean_unfold(M, outdir):
    """The modules UW (data), UE{i} (stage 2 equalities, composed theorems), US (stage 3),
    UTamper."""
    W, run, qs, kf, SB = M["W"], M["run"], M["qs"], M["kf"], M["SB"]
    od = pathlib.Path(outdir)
    files = {}
    names = {"WFN": "wfn", "WFNq": "wfnq", "WFN_inner": "wfni"}
    prev = ["GW.Endpoint.Kernel.Unfold"]
    for fn, nm in names.items():
        W[fn].path = fn
        mod = f"UW{nm.upper()[3:] or 'N'}"
        files[mod] = u_mod(f"the irreducible data of {fn}, as read by bgwio (exact dyadics).",
                           prev, u_wfn_lean(nm, W[fn]))
        prev = [f"GW.Endpoint.Kernel.Data.{mod}"]
    # run constants and the header / grid checks
    kX, kL = run.kpts[2], run.kpts[1]
    body = [f"""/-- The eps q-points (eps0mat, epsmat headers): q0, q1, q2. -/
noncomputable def q0 : Dy × Dy × Dy := {u_dy3(qs[0][0])}
noncomputable def q1 : Dy × Dy × Dy := {u_dy3(qs[1][0])}
noncomputable def q2 : Dy × Dy × Dy := {u_dy3(qs[2][0])}
/-- `epsilon_cutoff` (eps headers) and the bare-exchange cutoff (`ecutwfc` of WFN_inner). -/
noncomputable def ecuts : Dy := {u_ldy(u_dy(run.ecuts))}
noncomputable def ecutb : Dy := {u_ldy(u_dy(run.ecutb))}
/-- Sigma's k-points X, L (sigma.inp). -/
noncomputable def kX : Dy × Dy × Dy := {u_dy3(kX)}
noncomputable def kL : Dy × Dy × Dy := {u_dy3(kL)}
/-- The full k-grid of Epsilon (checked equal to `kfull wfn`). -/
noncomputable def KL : List V3 := {lean_list([u_lv(p) for p in kf])}
""",
            "theorem kfull_eq : kfull wfn = KL := by decide +kernel",
            "theorem wfn_closed : closedOK wfn = true := by decide +kernel",
            "theorem wfn_kw : kwOK wfn = true := by decide +kernel",
            "theorem wfn_sep : sepOK wfn = true := by decide +kernel",
            "theorem wfni_closed : closedOK wfni = true := by decide +kernel",
            "theorem wfni_kw : kwOK wfni = true := by decide +kernel",
            "theorem t_ok : tOK wfn = true ∧ tOK wfnq = true ∧ tOK wfni = true := by decide +kernel",
            "theorem ops_same : wfnq.ops = wfn.ops ∧ wfni.ops = wfn.ops := by decide +kernel",
            ]
    files["UWR"] = u_mod("run constants; header and k-grid checks.", prev, "\n".join(body) + "\n")
    prev = ["GW.Endpoint.Kernel.Data.UWR"]
    D = pathlib.Path(outdir)

    def scales(path, keys):
        txt = (D / path).read_text()
        import re
        out = {}
        for k in keys:
            m = re.search(rf"^  {k} := (\d+)$", txt, re.M)
            out[k] = int(m.group(1))
        return out

    def chain(n, name):
        t = "(forall_lt_zero _)"
        for i in range(n):
            t = f"(forall_lt_succ_of (k := {i}) {t} {name(i)})"
        return t
    per = 8
    for iq in range(3):
        sc = scales(f"E{iq}Inp.lean", ["SC", "SEn", "SB", "SOm", "SQ"])
        wv = "wfnq" if iq == 0 else "wfn"
        args = f"4 18 {sc['SC']} {sc['SEn']} {sc['SB']} {sc['SOm']} {sc['SQ']}"
        nk = len(kf)
        mods = []
        for m in range(0, nk, per):
            mod = f"UE{iq}K{m // per}"
            body = []
            if m == 0:
                body.append(f"""/-- **Stage 2's input of q-point {iq}, computed from the irreducible data**: the
unfolded states of WFN (conduction, at k) and {'WFNq' if iq == 0 else 'WFN'} (valence, at k + q) on
`kfull wfn`, the sphere and the header's `bdot`, `celvol` (`Unf.epsIn`). -/
noncomputable def inp{iq} : Input := epsIn wfn {wv} q{iq} ecuts {args}
""")
            for t in range(m, min(m + per, nk)):
                body.append(f"theorem e{iq}k{t} : inp{iq}.ks.getD {t} default = E{iq}.inp.ks.getD {t} default := by\n"
                            "  decide +kernel")
            imports = prev + ([f"GW.Endpoint.Kernel.Data.E{iq}Check"] if m == 0 else [])
            files[mod] = u_mod(f"stage 2, q-point {iq}: the unfolded states equal the stage-2 input "
                               f"(k-points {m}..{min(m + per, nk) - 1}).", imports, "\n".join(body) + "\n")
            prev = [f"GW.Endpoint.Kernel.Data.{mod}"]
        n = {0: "Q0", 1: "Q1", 2: "Q2"}[iq]
        body = f"""theorem e{iq}_ks : inp{iq}.ks = E{iq}.inp.ks :=
  list_eq_of_getD _ _ {nk} (by decide +kernel) (by decide +kernel) {chain(nk, lambda t: f"e{iq}k{t}")}

theorem e{iq}_Gs : inp{iq}.Gs = E{iq}.inp.Gs := by decide +kernel
theorem e{iq}_B : inp{iq}.B = E{iq}.inp.B := by decide +kernel
theorem e{iq}_Om : inp{iq}.Om = E{iq}.inp.Om := by decide +kernel
theorem e{iq}_qn : inp{iq}.qn = E{iq}.inp.qn := by decide +kernel

/-- The input computed from the irreducible WFN data IS stage 2's input. -/
theorem e{iq}_inp : inp{iq} = E{iq}.inp :=
  Input.eq_of _ _ rfl rfl rfl rfl rfl e{iq}_qn e{iq}_B e{iq}_Om e{iq}_Gs e{iq}_ks

/-- The true static RPA eps of q-point {iq} computed from the IRREDUCIBLE wavefunctions. -/
noncomputable def epsI{iq} : Matrix (Fin {n}.cert.n) (Fin {n}.cert.n) ℝ :=
  Matrix.of fun a b => epsR inp{iq} a b

theorem epsI{iq}_eq : epsI{iq} = E{iq}.epsTrue := by
  unfold epsI{iq} E{iq}.epsTrue; rw [e{iq}_inp]

/-- **Kernel-checked eps⁻¹ enclosure of q-point {iq} from the irreducible WFN data**: the static
RPA eps built from the irreducible coefficients of WFN{'/WFNq' if iq == 0 else ''} by the symmetry
unfolding `Unf.epsIn` (rotations, fractional-translation signs, `kfull`, the sphere) is
invertible and its inverse lies in cert.py's enclosure `{n}.cert.outLo/outHi`. -/
theorem epsinv_irr_q{iq} : IsUnit epsI{iq} ∧ ∀ a b, epsI{iq}⁻¹ a b ∈
    Set.Icc ({n}.cert.mat {n}.cert.SO {n}.cert.outLo a b) ({n}.cert.mat {n}.cert.SO {n}.cert.outHi a b) := by
  rw [epsI{iq}_eq]; exact E{iq}.epsinv_true_q{iq}
"""
        files[f"UE{iq}"] = u_mod(f"stage 2, q-point {iq}: assembly and the composed theorem.", prev, body)
        prev = [f"GW.Endpoint.Kernel.Data.UE{iq}"]
    # ---- stage 3
    sc = scales("S3G.lean", ["SC", "SEn", "SB", "SOm", "SR"])
    SC3, SEn3 = sc["SC"], sc["SEn"]
    gargs = f"{sc['SC']} {sc['SEn']} {sc['SB']} {sc['SOm']} {sc['SR']}"
    S = 2 * U_SK + sc["SB"]
    body = [f"""/-- The irreducible eps blocks: q (`0` for the q0 block, as Sigma matches it) and the
block's G-list, the stage-2 sphere of WFN. -/
noncomputable def irr : List IrrQ := [⟨0, inp0.Gs⟩, ⟨kn SK q1, inp1.Gs⟩, ⟨kn SK q2, inp2.Gs⟩]

/-- **Stage 3's run data computed from the irreducible data** (`Unf.glOf`). -/
noncomputable def glI : Gl := glOf wfni irr ecuts ecutb {gargs} S3.rhoT 4
"""]
    for t in range(8):
        body.append(f"theorem g_q{t} : glI.qs.getD {t} default = S3.gl.qs.getD {t} default := by decide +kernel")
        body.append(f"theorem g_gap{t} : gapOK {S} (byNorm {sc['SB']} wfni.bdot wfni.gvec (smul (2 ^ (SK - 1)) "
                    f"(qh8.getD {t} 0)) ecuts) = true := by decide +kernel")
    body.append(f"""theorem g_Gch : glI.Gch = S3.gl.Gch := by decide +kernel
theorem g_B : glI.B = S3.gl.B := by decide +kernel
theorem g_Om : glI.Om = S3.gl.Om := by decide +kernel

theorem gl_eq : glI = S3.gl :=
  Gl.eq_of _ _ rfl rfl rfl g_B rfl g_Om rfl rfl g_Gch
    (list_eq_of_getD _ _ 8 (by decide +kernel) (by decide +kernel) {chain(8, lambda t: f"g_q{t}")}) rfl
""")
    files["USG"] = u_mod("stage 3: the q-point data (spheres, BerkeleyGW order, eps index map).",
                         prev + ["GW.Endpoint.Kernel.Data.S3Check"], "\n".join(body) + "\n")
    prev = ["GW.Endpoint.Kernel.Data.USG"]
    for nm, kk, bands in (("X", "kX", "[5, 6]"), ("L", "kL", "[5]")):
        body = [f"""/-- **Sigma state {nm} computed from the irreducible WFN_inner data** (`Unf.stOf`). -/
noncomputable def st{nm}I : St := stOf wfni {bands} 18 {SC3} {SEn3} {kk} qh8
"""]
        for t in range(8):
            body.append(f"theorem s{nm}_q{t} : st{nm}I.kq.getD {t} default = S3.st{nm}.kq.getD {t} default := by\n"
                        "  decide +kernel")
        body.append(f"""theorem s{nm}_G : st{nm}I.Gk = S3.st{nm}.Gk := by decide +kernel
theorem s{nm}_c : st{nm}I.ck = S3.st{nm}.ck := by decide +kernel
theorem s{nm}_E : st{nm}I.Ek = S3.st{nm}.Ek := by decide +kernel

theorem st{nm}_eq : st{nm}I = S3.st{nm} :=
  St.eq_of _ _ s{nm}_G s{nm}_c s{nm}_E
    (list_eq_of_getD _ _ 8 (by decide +kernel) (by decide +kernel) {chain(8, lambda t: f"s{nm}_q{t}")})
""")
        files[f"US{nm}"] = u_mod(f"stage 3: the states of {nm} and at k - q.", prev, "\n".join(body) + "\n")
        prev = [f"GW.Endpoint.Kernel.Data.US{nm}"]
    body = """/-- The true eps⁻¹ of the three irreducible blocks, from the IRREDUCIBLE wavefunctions
(`epsI{i}`), as a function (`0` outside the block); `S3.Etrue` with `epsI` for `epsTrue`. -/
noncomputable def EIrr (iq a b : ℕ) : ℝ :=
  if iq = 0 then (if h : a < Q0.cert.n ∧ b < Q0.cert.n then epsI0⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else if iq = 1 then (if h : a < Q1.cert.n ∧ b < Q1.cert.n then epsI1⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else if iq = 2 then (if h : a < Q2.cert.n ∧ b < Q2.cert.n then epsI2⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩ else 0)
  else 0

theorem EIrr_eq : EIrr = S3.Etrue := by
  unfold EIrr S3.Etrue; rw [epsI0_eq, epsI1_eq, epsI2_eq]

/-- **O1 enclosure (spec A) from the irreducible WFN / WFNq / WFN_inner data.** The unfolded
spheres, coefficient rows, energies and eps index maps of Sigma and of the three eps blocks
are computed in Lean from the irreducible coefficients and headers by the symmetry
unfolding (`Unf.glOf`, `Unf.stOf`, `Unf.epsIn`); the density list (RHO) and the run
parameters are literals of the export. For every value of the mini-BZ Coulomb averages in
their certified boxes, `O1` lies in cert.py's enclosure (`Headline` discharges the boxes). -/
theorem o1_enclosure_irr (vb oq : V3 → ℝ) (hvb : VbHyp S3.vbT S3.eg.SV vb)
    (hoq : VbHyp S3.oqT S3.eg.SV oq) :
    O1 glI stXI stLI EIrr vb oq ∈
      Set.Icc ((8880811588953599 : ℝ) / 2 ^ 59) ((8880812351936001 : ℝ) / 2 ^ 59) := by
  rw [gl_eq, stX_eq, stL_eq, EIrr_eq]; exact S3.o1_enclosure vb oq hvb hoq

/-- C1 for spec A from the irreducible data. -/
theorem o1_pos_irr (vb oq : V3 → ℝ) (hvb : VbHyp S3.vbT S3.eg.SV vb)
    (hoq : VbHyp S3.oqT S3.eg.SV oq) : 0 < O1 glI stXI stLI EIrr vb oq := by
  rw [gl_eq, stX_eq, stL_eq, EIrr_eq]; exact S3.o1_pos vb oq hvb hoq
"""
    files["US"] = u_mod("stage 3: the composed theorem.", prev, body)
    # ---- negative controls
    w = W["WFN"]
    tph = None
    for t, kk in enumerate(kf):
        ik, iop, g = w.find(kk)
        if any(w.t2[iop]) and any(sum(a * b for a, b in zip(u_mv(w.M[iop], x), w.t2[iop])) % 2 == 1 and
                                  any(w.coef[ik][b][i][1] for b in range(4, 18))
                                  for i, x in enumerate(w.kg[ik])):
            tph = t
            break
    assert tph is not None
    assert w.find(kf[0])[0] == 0 and w.coef[0][4][0][1] != 0
    body = f"""/-- `E1.k0` with the sign of ONE rotated coefficient flipped (conduction band 4, entry 0). -/
noncomputable def kT : KPair :=
  ⟨E1.k0.Gv, E1.k0.cv, E1.k0.Ev, E1.k0.Gc,
    (match E1.k0.cc with | (x :: r) :: l => (-x :: r) :: l | l => l), E1.k0.Ec⟩

/-- Control: the unfolding reproduces the untampered k-point. -/
theorem control_rot : decide (inp1.ks.getD 0 default = E1.inp.ks.getD 0 default) = true := by
  decide +kernel

/-- A wrong sign on one rotated coefficient is detected. -/
theorem tamper_rot : decide (inp1.ks.getD 0 default = kT) = false := by decide +kernel

/-- WFN without the fractional translations (`t2 = 0`): the unfolded states at k-point {tph}
(whose operation is non-symmorphic) no longer match stage 2's input. -/
noncomputable def wfnT : Wfn := {{ wfn with ops := wfn.ops.map (fun op => ⟨op.M, 0⟩) }}

theorem tamper_phase :
    decide ((epsIn wfnT wfnT q1 ecuts 4 18 113 59 54 43 1).ks.getD {tph} default =
      E1.inp.ks.getD {tph} default) = false := by decide +kernel

/-- One irreducible coefficient of WFN negated (k-point 0, band 4, entry 0). -/
noncomputable def wfnC : Wfn :=
  {{ wfn with coef := match wfn.coef with
    | c0 :: l => (match c0 with
      | b0 :: b1 :: b2 :: b3 :: (d :: r) :: l' => b0 :: b1 :: b2 :: b3 :: (Dy.flip true d :: r) :: l'
      | x => x) :: l
    | l => l }}

theorem tamper_irr :
    decide ((epsIn wfnC wfnC q1 ecuts 4 18 113 59 54 43 1).ks.getD 0 default =
      E1.inp.ks.getD 0 default) = false := by decide +kernel

/-- Swapped k-point weights fail the orbit check. -/
theorem tamper_kw : kwOK {{ wfn with kw := wfn.kw.reverse }} = false := by decide +kernel

/-- Sigma's q-point 1 with one relative eps phase sign flipped is detected. -/
theorem tamper_neg :
    decide (glI.qs.getD 1 default =
      {{ S3.qd1 with neg := (match S3.qd1.neg with | b :: l => (!b) :: l | l => l) }}) = false := by
  decide +kernel
"""
    files["UTamper"] = u_mod("negative controls.", ["GW.Endpoint.Kernel.Data.US"], body)
    for f, t in files.items():
        (od / f"{f}.lean").write_text(t)
    return list(files)


def main_unfold(a):
    sys.set_int_max_str_digits(0)
    t0 = time.time()
    M = unfold_mirror(a.rundir)
    print(f"mirror ({time.time() - t0:.1f}s)", flush=True)
    if a.lean:
        print("wrote", lean_unfold(M, a.outdir), flush=True)
    return 0


# ================================================================ G2 roots (A1 in Lean)
#
# Root brackets of the full GPP quasiparticle equation f(E) = Emf + Sigma(E) - E of each O1
# state (bgw/endpoint/qp_unique.py, data/qp_unique.json), kernel-checked on stage 3's data:
# the derivative check `dOK` (GW/Endpoint/Kernel/RootCheck.lean) over the bracket [Ea, Eb]
# and stage 3's `nOK` at two sign points Ec < Ed inside it, for every (q-point, band,
# inner band). Exact Python mirrors of both checks produce the claimed enclosures (rounded
# outward with random low bits); the kernel only compares.
#
# The energies are integers C in units 1 / DEN eV (DEN = 10^8 2^92, stage 3's energy
# unit): the qp_unique bracket endpoints moved outward, and the sign points mid -+ delta of
# its bisected root interval, each perturbed by a random amount < 2^62 / DEN ~ 1e-17 eV
# (distinct low 64 bits, see `rlo`).

R_NS = "GW.Endpoint.Kernel.R"
R_OPEN = "open GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.QP"
R_HEAD = ("/- Generated by bgw/endpoint/kernel_export.py --roots (do not edit). G2 roots: kernel-checked\n"
          "root brackets of spec A's full GPP quasiparticle equation. -/\n")
TZ_DEN = TZN * RD * 2 ** (SX - TZE)


def r_mkEnP(C, eq, sh):
    x = C - RN * eq * 2 ** sh
    if abs(x) < TZ_DEN:
        return (False, TZ_DEN, TZ_DEN * TZ_DEN)
    return (x < 0, abs(x), x * x)


def r_mkEI(Ca, Cb, eq, sh):
    xa = Ca - RN * eq * 2 ** sh
    xb = Cb - RN * eq * 2 ** sh
    if TZ_DEN <= xa <= xb:
        return (False, xa, xb, xa * xa, xb * xb), True
    if xb <= -TZ_DEN and xa <= xb:
        return (True, -xb, -xa, xb * xb, xa * xa), True
    return (False, 0, 0, 0, 0), False


def r_subI(sx, XL, XH, tl, th):
    if sx: return (True, True, XL + tl, XH + th)
    if th < XL: return (True, False, XL - th, XH - tl)
    if XH < tl: return (True, True, tl - XH, th - XL)
    return FAIL


def r_addI(sx, XL, XH, tl, th):
    if not sx: return (True, False, XL + tl, XH + th)
    if XH < tl: return (True, False, tl - XH, th - XL)
    if th < XL: return (True, True, XL - th, XH - tl)
    return (False, False, 0, max(nsub(th, XL), nsub(XH, tl)))


def r_sq2I(XL2, XH2, tl2, th2):
    if th2 < XL2: return (True, False, XL2 - th2, XH2 - tl2)
    if XH2 < tl2: return (True, True, tl2 - XH2, th2 - XL2)
    return (False, False, 0, max(nsub(th2, XL2), nsub(XH2, tl2)))


def r_dschK(e, x):
    kept, sI, al, ah, tl, th, tl2, th2 = e
    sx, XL, XH, XL2, XH2 = x
    d = r_subI(sx, XL, XH, tl, th)
    if not d[0]: return FAIL
    g = genT(d[2], d[3], tl2, th2)
    if not g[0]: return FAIL
    if g[1]: return (True, not sI, tl * al * DEN // (d[3] * d[3]), th * ah * DEN // (d[2] * d[2]) + 1)
    return ZERO


def r_dssxK(e, x):
    kept, sI, al, ah, tl, th, tl2, th2 = e
    sx, XL, XH, XL2, XH2 = x
    d = r_subI(sx, XL, XH, tl, th)
    if not d[0]: return FAIL
    g = genT(d[2], d[3], tl2, th2)
    if not g[0]: return FAIL
    if g[1]:
        q = r_sq2I(XL2, XH2, tl2, th2)
        if not q[0]: return FAIL
        if sx and 4 * q[3] < tl2: return ZERO
        if (not sx) or th2 <= 4 * q[2]:
            return (True, not (sx != sI), 2 * XL * tl2 * al * DEN // (q[3] * q[3]),
                    2 * XH * th2 * ah * DEN // (q[2] * q[2]) + 1)
        return FAIL
    if th2 <= (d[2] * d[2] * TZN) >> TZE: return ZERO
    if (d[3] * d[3] * TZN) >> TZE < tl2:
        s = r_addI(sx, XL, XH, tl, th)
        if not s[0]: return FAIL
        if sx and 8 * s[3] < tl: return ZERO
        if (not sx) or th <= 8 * s[2]:
            return (True, sI, tl * al * DEN // (2 * (s[3] * s[3])), th * ah * DEN // (2 * (s[2] * s[2])) + 1)
        return FAIL
    return FAIL


def r_dcontrib(occ, x, sj, cj, r):
    d = entD(r)
    if not d[0]: return CS0
    a = r_dschK(d, x)
    if occ:
        b = r_dssxK(d, x)
        return (a[0] and b[0], addA(smA(sj != a[1], cj, a[2], a[3]), smA(not (sj != b[1]), 2 * cj, b[2], b[3])), A0, A0)
    return (a[0], smA(sj != a[1], cj, a[2], a[3]), A0, A0)


def r_dOK_T(occ, Ca, Cb, eq, sh, xs, vbS, cols):
    """Mirror of `dOK` (without the claim test): (ok, accumulator)."""
    xi, ok = r_mkEI(Ca, Cb, eq, sh)
    if not ok:
        return False, A0
    T = CS0
    for w, v, rs in zip(xs, vbS, cols):
        s = CS0
        for wj, r in zip(xs, rs):
            s = addCS(s, r_dcontrib(occ, xi, wj[0], wj[1], r))
        T = addCS(T, colFin(w, v, s))
    return T[0], T[1]


def r_claim(acc, sh):
    L, H = accval(acc)
    return (rlo(L >> sh), rhi(-((-H) >> sh)))


def r_energies(E):
    lo, hi = E
    return lo, hi


def r_bracket_hints(D, Q, HS, s, Ca, Cb, Cc, Cd):
    """All claims of one state's bracket: per q-point t: DH[a][n1], PO[a][n1]; plus the totals."""
    st = D['states'][s]
    she = SX - D['SEn']
    out = []
    for t in range(D['nq']):
        kq = st['kq'][t]
        h = HS['q'][t]
        DH, PO = [], []
        for a in range(len(st['ck'])):
            dr, pr = [], []
            for n1 in range(len(kq['cq'])):
                m = h['bands'][a]['n1'][n1]
                xs = xs_of(m['Tx'], h['H'][a][n1])
                occ = n1 < D['nocc']
                ok, acc = r_dOK_T(occ, Ca, Cb, kq['Eq'][n1], she, xs, Q[t]['vbS'], Q[t]['cols'])
                if not ok:
                    raise ValueError(f"dOK fails at state {s} q {t} band {a} n1 {n1}")
                dl, dh = r_claim(acc, m['sh'])
                assert acc_in(acc, m['sh'], dl, dh)
                dr.append((dl, dh))
                TT = nOK_T(occ, r_mkEnP(Cc, kq['Eq'][n1], she), r_mkEnP(Cd, kq['Eq'][n1], she), xs,
                           Q[t]['vbS'], Q[t]['cols'])
                if not TT[0]:
                    raise ValueError(f"nOK fails at state {s} q {t} band {a} n1 {n1}")
                o = out_hints(TT, m['sh'])
                for k in range(3):
                    assert acc_in(TT[1 + k], m['sh'], o[2 * k], o[2 * k + 1])
                pr.append(o)
            DH.append(dr)
            PO.append(pr)
        out.append(dict(DH=DH, PO=PO))
    return out


def r_totals(D, HS, s, R):
    st = D['states'][s]
    nb = len(st['ck'])
    nbq = len(st['kq'][0]['cq'])
    L = {}
    for iw in (0, 1):
        for k in (0, 1):
            tot = 0
            for t in range(D['nq']):
                for a in range(nb):
                    b = HS['q'][t]['bands'][a]
                    tot += 4 * b['xo'][k] + b['co'][k]
                    for n1 in range(nbq):
                        o = R[t]['PO'][a][n1]
                        tot += o[4 + k] + 2 * o[2 * iw + k]
            L[iw, k] = tot
    Dt = {k: sum(2 * R[t]['DH'][a][n1][k] for t in range(D['nq']) for a in range(nb) for n1 in range(nbq))
          for k in (0, 1)}
    return L, Dt


def r_consts(D, s):
    st = D['states'][s]
    nb = len(st['ck'])
    RY = Fr(RN, RD)
    X = Fr(D['nq']) * Fr(D['OmN'], 2 ** D['SOm'])
    c = RY / (nb * X * 4 * 2 ** SOUT)
    eo = sum(RY * Fr(e, 2 ** D['SEn']) for e in st['Ek']) / nb
    return c, eo


def r_plan(qpu, delta):
    """Integer energies of the brackets: (state index, name, bracket index, Ca, Cb, Cc, Cd)."""
    out = []
    for s, nm in ((0, 'X'), (1, 'L')):
        for bi, r in enumerate(qpu[nm]['roots']):
            a, b = r['bracket']
            lo, hi = r['root']
            mid = (Fr(lo) + Fr(hi)) / 2
            Ca = rlo(math.floor(Fr(a) * DEN))
            Cb = rhi(math.ceil(Fr(b) * DEN))
            Cc = rlo(math.floor((mid - Fr(delta)) * DEN))
            Cd = rhi(math.ceil((mid + Fr(delta)) * DEN))
            out.append((s, nm, bi, Ca, Cb, Cc, Cd))
    return out


def r_lrq(R):
    DH = LL([LL([f"({lz(lo)}, {lz(hi)})" for lo, hi in row]) for row in R['DH']])
    PO = LL([LL([LL([lz(x) for x in o]) for o in row]) for row in R['PO']])
    return f"⟨{DH}, {PO}⟩"


def r_modules(D, HS_all, plans, Rs):
    """All root modules {name: text} and the list of final modules."""
    files = {}
    she = SX - D['SEn']
    tz = TZ_DEN
    ends = []
    last = None            # brackets are chained too: one serial build
    for (s, nm, bi, Ca, Cb, Cc, Cd), R in zip(plans, Rs):
        tag = f"{nm}{bi}"
        H = [R_HEAD, "import GW.Endpoint.Kernel.Data.S3Check\nimport GW.Endpoint.Kernel.RootAsm\n" +
             (f"import {last}\n" if last else ""),
             f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3\n"]
        for k, v in (("a", Ca), ("b", Cb), ("c", Cc), ("d", Cd)):
            H.append(f"noncomputable def C{k}{tag} : ℤ := {lit_int(v)}")
        for t in range(D['nq']):
            H.append(f"noncomputable def rq{tag}_{t} : RQ := {r_lrq(R[t])}")
        H.append(f"noncomputable def rqs{tag} : List RQ := {LL([f'rq{tag}_{t}' for t in range(D['nq'])])}")
        H.append(f"noncomputable def rq{tag} (t : ℕ) : RQ := rqs{tag}.getD t default\n")
        H.append(f"end {R_NS}\n")
        hname = f"RH{tag}"
        files[hname] = "\n".join(H)
        st = D['states'][s]
        nb = len(st['ck'])
        nbq = len(st['kq'][0]['cq'])
        prev = S3mod(hname)
        # one check per module (peak RSS: one dOK ~4.4 GB, one nOK ~5.9 GB; 6 pairs in one
        # module reached 9.3 GB), one serial import chain
        for t in range(D['nq']):
            d = f"(d{nm} {t})"
            for a in range(nb):
                for n1 in range(nbq):
                    xs = f"(xsOf (({d}.Tx.getD {a} []).getD {n1} 0) (({d}.H.getD {a} []).getD {n1} []))"
                    shv = f"(({d}.sh.getD {a} []).getD {n1} 0)"
                    eq = f"({d}.kq.Eq.getD {n1} 0)"
                    stmts = {
                        f"RD{tag}_{t}_{a}_{n1}":
                            f"theorem rd{tag}_{t}_{a}_{n1} : dOK kc eg.Den {RN} {she} {tz} (decide ({n1} < gl.nocc)) "
                            f"Ca{tag} Cb{tag} {eq} {xs} {d}.vbS {d}.cols {shv} "
                            f"(((rq{tag} {t}).DH.getD {a} []).getD {n1} (0, 0)).1 "
                            f"(((rq{tag} {t}).DH.getD {a} []).getD {n1} (0, 0)).2 = true := by decide +kernel",
                        f"RP{tag}_{t}_{a}_{n1}":
                            f"theorem rp{tag}_{t}_{a}_{n1} : nOK kc (decide ({n1} < gl.nocc)) "
                            f"(mkEnP {RN} {she} {tz} Cc{tag} {eq}) (mkEnP {RN} {she} {tz} Cd{tag} {eq}) "
                            f"{xs} {d}.vbS {d}.cols {shv} (((rq{tag} {t}).PO.getD {a} []).getD {n1} []) = true "
                            f":= by decide +kernel"}
                    for mname, th in stmts.items():
                        files[mname] = "\n".join([R_HEAD, f"import {prev}\n",
                                                   f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3\n", th,
                                                   f"\nend {R_NS}\n"])
                        prev = S3mod(mname)
        files[f"R{tag}"] = r_final(D, s, nm, tag, prev, plans, R, HS_all[s])
        ends.append(S3mod(f"R{tag}"))
        last = S3mod(f"R{tag}")
    return files, ends


def r_final(D, s, nm, tag, prev, plans, R, HS):
    st = D['states'][s]
    nb = len(st['ck'])
    nbq = len(st['kq'][0]['cq'])
    she = SX - D['SEn']
    tz = TZ_DEN
    L_, Dt = r_totals(D, HS, s, R)
    L = [R_HEAD, f"import {prev}\n", f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3 Finset Set\n"]
    for t in range(D['nq']):
        hd = chain_term(nb, lambda a: "(" + chain_term(nbq, lambda n1, a=a: f"rd{tag}_{t}_{a}_{n1}") + ")")
        hp = chain_term(nb, lambda a: "(" + chain_term(nbq, lambda n1, a=a: f"rp{tag}_{t}_{a}_{n1}") + ")")
        L.append(f"theorem rok{tag}_{t} : RqOK st{nm} (d{nm} {t}) eg kc gl.nocc {RN} {she} {tz} "
                 f"Ca{tag} Cb{tag} Cc{tag} Cd{tag} (rq{tag} {t}) := by\n"
                 f"  refine ⟨?_, ?_⟩\n"
                 f"  · show ∀ a < {nb}, ∀ n1 < {nbq}, _\n    exact {hd}\n"
                 f"  · show ∀ a < {nb}, ∀ n1 < {nbq}, _\n    exact {hp}\n")
    L.append(f"theorem rok{tag} : ∀ t < gl.qs.length, RqOK st{nm} (d{nm} t) eg kc gl.nocc {RN} {she} {tz} "
             f"Ca{tag} Cb{tag} Cc{tag} Cd{tag} (rq{tag} t) := by\n"
             f"  show ∀ t < {D['nq']}, _\n  exact {chain_term(D['nq'], lambda t: f'rok{tag}_{t}')}\n")
    for (iw, k), v in L_.items():
        L.append(f"noncomputable def L{tag}{iw}{k}v : ℤ := {lit_int(v)}")
        L.append(f"theorem L{tag}{iw}{k} : LtZ d{nm} rq{tag} gl.qs.length st{nm}.ck.length (nbq st{nm}) {iw} {k} = "
                 f"L{tag}{iw}{k}v := by decide +kernel")
    for k, v in Dt.items():
        L.append(f"noncomputable def D{tag}{k}v : ℤ := {lit_int(v)}")
        L.append(f"theorem D{tag}{k} : DtZ rq{tag} gl.qs.length st{nm}.ck.length (nbq st{nm}) {k} = "
                 f"D{tag}{k}v := by decide +kernel")
    den = f"(10 ^ 8 * 2 ^ {SX} : ℝ)"
    L.append(f"theorem den_eq{tag} : ((eg.Den : ℕ) : ℝ) = {den} := by\n"
             f"  have : eg.Den = 10 ^ 8 * 2 ^ {SX} := by decide +kernel\n  rw [this]; push_cast; ring\n")
    L.append(f"theorem emf{tag} : emf gl st{nm} = eo{nm}v := eo{nm}_eq\n")
    L.append(f'''/-- **Root bracket `{tag}` of the full GPP QP equation of `{nm}` (spec A, TRUE eps⁻¹).** For
every value of the Coulomb averages in their certified boxes and either convention at
`wx = wtilde`: `f` is continuous on `[Ea, Eb]` with derivative `f'` in the stated enclosure (< 0),
has exactly one zero in `[Ea, Eb]`, and it lies in `[Ec, Ed]` (an isolating bracket); no point
of `[Ea, Eb]` is one where the source divides by zero. -/
theorem root{tag} (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) :
    SrcDefOn gl Etrue vb oq st{nm} ((Ca{tag} : ℝ) / {den}) ((Cb{tag} : ℝ) / {den}) ∧
    (∀ E ∈ Icc ((Ca{tag} : ℝ) / {den}) ((Cb{tag} : ℝ) / {den}),
      c{nm}v * D{tag}0v - 1 ≤ dfQP gl Etrue vb oq st{nm} E ∧ dfQP gl Etrue vb oq st{nm} E ≤ c{nm}v * D{tag}1v - 1) ∧
    ∀ cv : Bool,
      IsolatingBracket (fQP gl Etrue vb oq st{nm} cv) (dfQP gl Etrue vb oq st{nm})
        ((Cc{tag} : ℝ) / {den}) ((Cd{tag} : ℝ) / {den}) ∧
      (∃! E, E ∈ Icc ((Ca{tag} : ℝ) / {den}) ((Cb{tag} : ℝ) / {den}) ∧ fQP gl Etrue vb oq st{nm} cv E = 0) ∧
      ∀ E ∈ Icc ((Ca{tag} : ℝ) / {den}) ((Cb{tag} : ℝ) / {den}), fQP gl Etrue vb oq st{nm} cv E = 0 →
        E ∈ Icc ((Cc{tag} : ℝ) / {den}) ((Cd{tag} : ℝ) / {den}) := by
  have hc := c{nm}_eq
  have H := root_bracket d{nm} rq{tag} ok{nm} hE{nm} hvb (oq_scaled hoq) hX (by decide) (by decide) rok{tag}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [hc, D{tag}1]; norm_num [c{nm}v, D{tag}1v])
    (by rw [hc, L{tag}00, emf{tag}, den_eq{tag}]; norm_num [c{nm}v, L{tag}00v, eo{nm}v, Cc{tag}])
    (by rw [hc, L{tag}11, emf{tag}, den_eq{tag}]; norm_num [c{nm}v, L{tag}11v, eo{nm}v, Cd{tag}])
  simp only [] at H
  rw [hc, D{tag}0, D{tag}1, den_eq{tag}] at H
  exact H
''')
    L.append(f"end {R_NS}\n")
    return "\n".join(L)


def main_roots(a):
    import pickle
    sys.set_int_max_str_digits(0)
    t0 = time.time()
    rec = pickle.loads(pathlib.Path(a.sigma_pkl).read_bytes()) if a.sigma_pkl and pathlib.Path(a.sigma_pkl).exists() \
        else capture_sigma(a.rundir)
    D, T, g, Q = build(rec)
    D['_T'] = T
    HS_all = [hints_state(D, T, Q, s) for s in range(len(D['states']))]
    print(f"stage 3 data ({time.time() - t0:.1f}s)", flush=True)
    qpu = json.loads((HERE / "data/qp_unique.json").read_text())
    plans = [p for p in r_plan(qpu, a.roots_delta) if f"{p[1]}{p[2]}" in a.roots.split(",")]
    Rs = []
    for s, nm, bi, Ca, Cb, Cc, Cd in plans:
        R = r_bracket_hints(D, Q, HS_all[s], s, Ca, Cb, Cc, Cd)
        Rs.append(R)
        Lt, Dt = r_totals(D, HS_all[s], s, R)
        c, eo = r_consts(D, s)
        E = [Fr(x, DEN) for x in (Ca, Cb, Cc, Cd)]
        fc = (eo + c * Lt[0, 0] - E[2], eo + c * Lt[0, 1] - E[2])
        fd = (eo + c * Lt[1, 0] - E[3], eo + c * Lt[1, 1] - E[3])
        fp = (c * Dt[0] - 1, c * Dt[1] - 1)
        ok = fc[0] > 0 and fd[1] < 0 and fp[1] < 0
        print(f"{nm}{bi}: [Ea, Eb] = [{float(E[0])!r}, {float(E[1])!r}], [Ec, Ed] = [{float(E[2])!r}, "
              f"{float(E[3])!r}]; f(Ec) in [{float(fc[0]):.3e}, {float(fc[1]):.3e}], f(Ed) in "
              f"[{float(fd[0]):.3e}, {float(fd[1]):.3e}], f' in [{float(fp[0])!r}, {float(fp[1])!r}], "
              f"Z in [{float(-1 / fp[0])!r}, {float(-1 / fp[1])!r}]; certified: {ok} ({time.time() - t0:.1f}s)",
              flush=True)
        assert ok
    pl = {f"{p[1]}{p[2]}": p for p in plans}
    if "X0" in pl and "L0" in pl:
        x, l = pl["X0"], pl["L0"]
        o1 = (Fr(x[5] - l[6], DEN), Fr(x[6] - l[5], DEN))
        print(f"principal O1 in [{float(o1[0]) * 1e3!r}, {float(o1[1]) * 1e3!r}] meV; inside "
              f"[68.9856742, 68.9856744]: {Fr(689856742, 10 ** 10) <= o1[0] and o1[1] <= Fr(689856744, 10 ** 10)}",
              flush=True)
    if a.lean:
        files, ends = r_modules(D, HS_all, plans, Rs)
        if "X0" in pl and "L0" in pl:
            files["RO1"] = r_o1(ends)
            ends = [S3mod("RO1")]
            files["RTamper"], tv = r_tamper(D, plans, ends[0])
            # mirror of the controls
            st0 = D['states'][0]
            she = SX - D['SEn']
            h = HS_all[0]['q'][1]
            m = h['bands'][0]['n1'][2]
            xs = xs_of(m['Tx'], h['H'][0][2])
            ok_w, _ = r_dOK_T(True, tv['Cw'], pl['X0'][4], st0['kq'][1]['Eq'][2], she, xs, Q[1]['vbS'], Q[1]['cols'])
            _, xi_ok = r_mkEI(tv['Z1'], tv['Z2'], st0['kq'][0]['Eq'][0], she)
            assert not ok_w and not xi_ok
            ends.append(S3mod("RTamper"))
            files["RIrr"] = r_irr(S3mod("RO1"))
            ends.append(S3mod("RIrr"))
        od = pathlib.Path(a.outdir)
        for mod, text in files.items():
            (od / f"{mod}.lean").write_text(text)
        print(f"wrote {len(files)} modules; ends {ends}", flush=True)
    return 0


def r_tamper(D, plans, end):
    """RTamper: negative controls of the root checks (each `= false` by the kernel)."""
    she = SX - D['SEn']
    tz = TZ_DEN
    pl = {f"{p[1]}{p[2]}": p for p in plans}
    x = pl["X0"]
    # the X0 bracket widened by 1 meV to the left: at q-point 1, inner band 2 a sexcut clamp
    # switches inside, so the branch is undecided and dOK must fail (checked by the mirror)
    Cw = rlo(x[3] - DEN // 1000)
    st = D['states'][0]
    d = "(dX 1)"
    xs = f"(xsOf (({d}.Tx.getD 0 []).getD 2 0) (({d}.H.getD 0 []).getD 2 []))"
    shv = f"(({d}.sh.getD 0 []).getD 2 0)"
    eq = f"({d}.kq.Eq.getD 2 0)"
    dh = "(((rqX0 1).DH.getD 0 []).getD 2 (0, 0))"
    po = "(((rqX0 1).PO.getD 0 []).getD 2 [])"
    # an interval around e_n1 (|wx| < TOL_Zero possible): mkEI rejects it
    d0 = "(dX 0)"
    eq0v = st['kq'][0]['Eq'][0]
    c0 = RN * eq0v * 2 ** she
    Z1, Z2 = rlo(c0 - 10 ** 30), rhi(c0 + 10 ** 30)
    xs0 = f"(xsOf (({d0}.Tx.getD 0 []).getD 0 0) (({d0}.H.getD 0 []).getD 0 []))"
    sh0 = f"(({d0}.sh.getD 0 []).getD 0 0)"
    # mirror: the tampered checks fail
    h = None
    L = [R_HEAD, f"import {end}\n", f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3\n"]
    L.append(f"""/-- The X0 bracket widened by 1 meV to the left contains a sexcut switch of a mode at
q-point 1, inner band 2: the derivative check rejects it (continuity is not certifiable). -/
theorem tamper_wide : dOK kc eg.Den {RN} {she} {tz} (decide (2 < gl.nocc)) {lit_int(Cw)} CbX0 {eq} {xs} {d}.vbS
    {d}.cols {shv} {dh}.1 {dh}.2 = false := by decide +kernel

/-- The derivative claim of the same check with its upper end moved below its lower end. -/
theorem tamper_der : dOK kc eg.Den {RN} {she} {tz} (decide (2 < gl.nocc)) CaX0 CbX0 {eq} {xs} {d}.vbS
    {d}.cols {shv} {dh}.1 ({dh}.1 - 1) = false := by decide +kernel

/-- The point claim at `Ec` collapsed to its lower end. -/
theorem tamper_pt : nOK kc (decide (2 < gl.nocc)) (mkEnP {RN} {she} {tz} CcX0 {eq}) (mkEnP {RN} {she} {tz} CdX0 {eq})
    {xs} {d}.vbS {d}.cols {shv}
    ({po}.getD 0 0 :: {po}.getD 0 0 :: {po}.getD 2 0 :: {po}.getD 3 0 :: {po}.getD 4 0 :: {po}.getD 5 0 :: [])
    = false := by decide +kernel

/-- An energy interval around `e_n1(k - q)` (where `|wx| < TOL_Zero` is possible) is rejected. -/
theorem tamper_tz : dOK kc eg.Den {RN} {she} {tz} (decide (0 < gl.nocc)) {lit_int(Z1)} {lit_int(Z2)}
    ({d0}.kq.Eq.getD 0 0) {xs0} {d0}.vbS {d0}.cols {sh0} 0 0 = false := by decide +kernel
""")
    L.append(f"end {R_NS}\n")
    return "\n".join(L), dict(Cw=Cw, Z1=Z1, Z2=Z2)


def r_irr(prev):
    """RIrr: the principal-root O1 with every Sigma / eps input computed from the irreducible
    WFN data (G2 unfolding: `U.gl_eq`, `U.stX_eq`, `U.stL_eq`, `U.EIrr_eq`)."""
    den = f"(10 ^ 8 * 2 ^ {SX} : ℝ)"
    return "\n".join([R_HEAD, f"import {prev}\nimport GW.Endpoint.Kernel.Data.US\n",
                      f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3 GW.Endpoint.Kernel.U Set\n", f"""
/-- **Full-QP O1 for the roots in the brackets (that they are the principal roots is the
Python `qp_unique.py`), from the irreducible WFN / WFNq / WFN_inner data**: `o1_fullQP` with the
inputs `glI`, `stXI`, `stLI`, `EIrr` computed in Lean by the symmetry unfolding. -/
theorem o1_fullQP_irr (vb oq : V3 → ℝ) (hvb : VbHyp S3.vbT S3.eg.SV vb) (hoq : VbHyp S3.oqT S3.eg.SV oq)
    (cv : Bool) (EX EL : ℝ)
    (hX : EX ∈ Icc ((CaX0 : ℝ) / {den}) ((CbX0 : ℝ) / {den}) ∧ fQP glI EIrr vb oq stXI cv EX = 0)
    (hL : EL ∈ Icc ((CaL0 : ℝ) / {den}) ((CbL0 : ℝ) / {den}) ∧ fQP glI EIrr vb oq stLI cv EL = 0) :
    EX - EL ∈ Icc ((689856742 : ℝ) / 10 ^ 10) ((689856744 : ℝ) / 10 ^ 10) ∧ 0 < EX - EL := by
  rw [gl_eq, stX_eq, EIrr_eq] at hX
  rw [gl_eq, stL_eq, EIrr_eq] at hL
  exact o1_fullQP vb oq hvb hoq cv EX EL hX hL

/-- The roots exist and are unique in their brackets (irreducible data; that they are the
principal roots is the Python `qp_unique.py`). -/
theorem roots_exist_irr (vb oq : V3 → ℝ) (hvb : VbHyp S3.vbT S3.eg.SV vb) (hoq : VbHyp S3.oqT S3.eg.SV oq)
    (cv : Bool) :
    (∃! E, E ∈ Icc ((CaX0 : ℝ) / {den}) ((CbX0 : ℝ) / {den}) ∧ fQP glI EIrr vb oq stXI cv E = 0) ∧
    (∃! E, E ∈ Icc ((CaL0 : ℝ) / {den}) ((CbL0 : ℝ) / {den}) ∧ fQP glI EIrr vb oq stLI cv E = 0) := by
  rw [gl_eq, stX_eq, stL_eq, EIrr_eq]; exact roots_exist vb oq hvb hoq cv
""", f"end {R_NS}\n"])


def r_o1(ends):
    den = f"(10 ^ 8 * 2 ^ {SX} : ℝ)"
    L = [R_HEAD, "".join(f"import {e}\n" for e in ends), f"namespace {R_NS}\n{R_OPEN} GW.Endpoint.Kernel.S3 Set\n"]
    L.append(f'''/-- **The full-QP O1 for the roots in the brackets (spec A, TRUE eps⁻¹; that these are the
principal roots is the Python `qp_unique.py`).** For every
value of the Coulomb averages in their certified boxes and either convention at `wx = wtilde`:
the zero `EX` of `f_X` in bracket `X0` and the zero `EL` of `f_L` in bracket `L0` (each unique
there, `rootX0`, `rootL0`) satisfy `EX - EL ∈ [68.9856742, 68.9856744]` meV (qp_cert.py's value),
so `EX > EL`. -/
theorem o1_fullQP (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) (cv : Bool)
    (EX EL : ℝ) (hX : EX ∈ Icc ((CaX0 : ℝ) / {den}) ((CbX0 : ℝ) / {den}) ∧ fQP gl Etrue vb oq stX cv EX = 0)
    (hL : EL ∈ Icc ((CaL0 : ℝ) / {den}) ((CbL0 : ℝ) / {den}) ∧ fQP gl Etrue vb oq stL cv EL = 0) :
    EX - EL ∈ Icc ((689856742 : ℝ) / 10 ^ 10) ((689856744 : ℝ) / 10 ^ 10) ∧ 0 < EX - EL := by
  have x := ((rootX0 vb oq hvb hoq).2.2 cv).2.2 EX hX.1 hX.2
  have l := ((rootL0 vb oq hvb hoq).2.2 cv).2.2 EL hL.1 hL.2
  obtain ⟨x1, x2⟩ := x
  obtain ⟨l1, l2⟩ := l
  have e1 : (689856742 : ℝ) / 10 ^ 10 ≤ (CcX0 : ℝ) / {den} - (CdL0 : ℝ) / {den} := by
    norm_num [CcX0, CdL0]
  have e2 : (CdX0 : ℝ) / {den} - (CcL0 : ℝ) / {den} ≤ (689856744 : ℝ) / 10 ^ 10 := by
    norm_num [CdX0, CcL0]
  refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- **The bracketed root pair exists and is unique** (principal per the Python `qp_unique.py`):
for either convention, each of `f_X`, `f_L`
has exactly one zero in its bracket. -/
theorem roots_exist (vb oq : V3 → ℝ) (hvb : VbHyp vbT eg.SV vb) (hoq : VbHyp oqT eg.SV oq) (cv : Bool) :
    (∃! E, E ∈ Icc ((CaX0 : ℝ) / {den}) ((CbX0 : ℝ) / {den}) ∧ fQP gl Etrue vb oq stX cv E = 0) ∧
    (∃! E, E ∈ Icc ((CaL0 : ℝ) / {den}) ((CbL0 : ℝ) / {den}) ∧ fQP gl Etrue vb oq stL cv E = 0) :=
  ⟨((rootX0 vb oq hvb hoq).2.2 cv).2.1, ((rootL0 vb oq hvb hoq).2.2 cv).2.1⟩
''')
    L.append(f"end {R_NS}\n")
    return "\n".join(L)



def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir", nargs="?")
    ap.add_argument("--npz", default=None, help="capture cache (read if exists, else written)")
    ap.add_argument("--lean", action="store_true")
    ap.add_argument("--only", default=None)
    ap.add_argument("--block", type=int, default=None)
    ap.add_argument("--outdir", default=str(ROOT / "GW/Endpoint/Kernel/Data"))
    ap.add_argument("--suffix", default="")
    ap.add_argument("--eps", type=int, default=None,
                    help="stage 2: export the eps data of this q-point (needs --lean)")
    ap.add_argument("--eps-npz", default=None, help="stage 2 capture cache (pickle)")
    ap.add_argument("--simulate", action="store_true", help="stage 2: exact Python mirror of chiOK")
    ap.add_argument("--eps-sd", type=int, default=EPS_SD, help="stage 2: bits of 1/(E_c - E_v)")
    ap.add_argument("--eps-rows", type=int, default=19, help="stage 2: rows per chi module")
    ap.add_argument("--sigma", action="store_true", help="stage 3: Sigma / Eqp1 / O1 data and checks")
    ap.add_argument("--sigma-pkl", default=None, help="stage 3 capture cache (pickle)")
    ap.add_argument("--sigma-ecols", type=int, default=12, help="stage 3: entry columns per module")
    ap.add_argument("--sigma-nper", type=int, default=5, help="stage 3: unoccupied inner bands per module")
    ap.add_argument("--unfold", action="store_true", help="G2 unfolding: irreducible WFN data and checks")
    ap.add_argument("--roots", default=None, help="G2 roots: brackets to check, e.g. X0,L0 (needs --sigma-pkl)")
    ap.add_argument("--roots-delta", type=float, default=4e-11, help="G2 roots: half-width of the sign points (eV)")
    a = ap.parse_args(argv)
    if a.roots:
        return main_roots(a)
    if a.unfold:
        return main_unfold(a)
    if a.sigma:
        return main_sigma(a)
    if a.eps is not None:
        return main_eps(a)
    only = None if a.only is None else {int(x) for x in a.only.split(",")}
    recs = None
    if a.npz and pathlib.Path(a.npz).exists():
        z = np.load(a.npz, allow_pickle=True)
        recs = [(int(k[1:]), z[k].item()) for k in sorted(z.files)]
        recs = [(i, r) for i, r in recs if only is None or i in only]
    else:
        recs = capture(a.rundir, only)
        if a.npz:
            np.savez(a.npz, **{f"q{i}": np.array(r, dtype=object) for i, r in recs})
    if a.lean:
        od = pathlib.Path(a.outdir)
        od.mkdir(parents=True, exist_ok=True)
        for iq, rec in recs:
            if a.block:
                rec = block_rec(rec, a.block)
            n = rec["R"].shape[0]
            text, info = lean_data(iq, rec, n)
            name = f"Q{iq}{a.suffix}"
            text = text.replace(f"GW.Endpoint.Kernel.Q{iq}", f"GW.Endpoint.Kernel.{name}")
            (od / f"{name}.lean").write_text(text)
            for old in od.glob(f"{name}R*.lean"):
                old.unlink()
            for mod, t in lean_proof(iq, n, name).items():
                (od / f"{mod}.lean").write_text(t)
            print(name, info, flush=True)
    return 0


def main_eps(a):
    import pickle
    iq = a.eps
    if a.eps_npz and pathlib.Path(a.eps_npz).exists():
        rec = pickle.loads(pathlib.Path(a.eps_npz).read_bytes())
    else:
        t0 = time.time()
        rec = capture_eps(a.rundir, iq)
        print(f"captured q{iq} ({time.time() - t0:.1f}s)", flush=True)
        if a.eps_npz:
            pathlib.Path(a.eps_npz).write_bytes(pickle.dumps(rec))
    t0 = time.time()
    d = eps_data(rec, a.eps_sd)
    print(f"data q{iq}: n={len(d['Gs'])} nk={len(d['ks'])} cfg={d['cfg']} SC={d['SC']} SEn={d['SEn']} "
          f"({time.time() - t0:.1f}s)", flush=True)
    lo, hi = rec["eps_lo"], rec["eps_hi"]
    SE = max(dyadic_scale(lo), dyadic_scale(hi))
    if a.simulate:
        t0 = time.time()
        bad, marg = simulate_chi(d, to_int(lo, SE), to_int(hi, SE), SE)
        print(f"simulate: {bad} entries outside the stage-1 box, min margin {marg} "
              f"({time.time() - t0:.1f}s)", flush=True)
    if a.lean:
        mods, ng = lean_eps(iq, d, dict(q=rec["q"].tolist()), a.outdir, rows=a.eps_rows)
        print("wrote", mods, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())

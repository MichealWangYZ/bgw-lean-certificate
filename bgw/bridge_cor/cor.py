#!/usr/bin/env python3
"""BRIDGE-COR: a rigorous enclosure of the omitted-band (dynamic) Coulomb-hole tail on the
Si-EPM O1 run, replacing the empirical factor 1/2 of the static remainder COR.

    python3 bgw/bridge_cor/cor.py RUNDIR [--all-bands RUNDIR_ALL] [--out F]

What is evaluated (all in iv.py interval arithmetic unless labelled "float"):

`GW/Bridge/Cor.lean` proves, for the spec's Sigma with ALL bands at every k - q
(`sigA_all_bands`, `sigA_diff_all_bands`; the omitted bands are a real completion of the
computed ones, `CompleteK kappa`):

    | SigAall - SigA - sum_t sum_{i,j} v_i T_ij cS_ji |
        <= sum_t sum_{i,j} |v_i| sqrt(T_ii) sqrt(T_jj) rS_ji

where SigA is the run's Sigma (nb = number_bands = 18 computed bands, WITH its COR),
T_ij = kappa sum_v A_v(G_i) A_v(G_j) - sum_{n<nb} M_n(G_i) M_n(G_j) is the omitted-band
pair sum (completeness, `tailK_eq`; kappa >= ||R||_2^2 of the computed rows, a rigorous
Gershgorin bound, makes the completion exist), and per mode (I = Iq[j,i], O = Oq[j,i]):

    cS = IeU/4 + [keepM] theta(wtM, D)/2 (-I/2),   rS = [keepM] theta(wtM, D)/2 |I|/2,
    theta(w, D) = w / (w + D),

with D_t = RYD e_{nb-1}(k - q_t) - E: the highest COMPUTED band at k - q bounds every
omitted band from below (the EPM eigenvalues are sorted), so every omitted band has
x = E - e_n <= -D_t. The energy step Sigma(Eo + 1 eV) - Sigma(Eo) has the same form with
psi(w, D) = w/((w + D - 1)(w + D)) (`cSd`, `rSd`). Eqp1 and O1 are then evaluated from
the enclosures with the spec's linearised formula (interval arithmetic).

The same machinery with the theory kernel thK in place of BerkeleyGW's mode rules on the
omitted bands (invalid modes -> 0, dropped modes -> their HL value; `thK_tail_mode`,
`thK_diff_mode`, `thK_empty_abs` for sign-undecided modes) is reported as a diagnostic.

Diagnostics (clearly not part of the bound): with `--all-bands`, a second pinned EPM run
whose WFN_inner carries 168 bands gives the omitted bands' actual energies and
coefficients; the spec's all-band Sigma SigAall (BerkeleyGW's rule on every band; it still
contains the static residual CORall, R28-F4 / GW.Bridge.CorResidual) is evaluated and checked to lie inside the enclosure, and the enclosure is
re-evaluated with more computed bands (nb = 18, 30, 60, 100, 168) to show how it shrinks.

Units: energies eV; Sigma multiplet averaged (X: bands 5,6; L: band 5).
"""
import argparse
import json
import pathlib
import sys
import time

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
EP = ROOT / "bgw/endpoint"
sys.path.insert(0, str(EP))
sys.path.insert(0, str(ROOT / "bgw/bridge_measure"))
import cert  # noqa: E402
import iv  # noqa: E402
import measure as ms  # noqa: E402
import spec  # noqa: E402
from iv import I  # noqa: E402

RYD = cert.RYD
RYD_F = ms.RYD_F
TS = ms.TS
WINV = ms.WINV
dec = ms.dec


def ivl(x):
    return [float(x.lo), float(x.hi)]


def mev(x):
    """Convert an eV interval to meV without narrowing it in binary64."""
    y = x * I.exact(1000.0)
    return [float(y.lo), float(y.hi)]


def radius_eV(r):
    """Upper bound in eV for a radius r in Ry (a float taken as exact): the hi endpoint of
    I.exact(r) * RYD. A relative pad on the float product is not outward for subnormal r."""
    return float((I.exact(r) * RYD).hi)


def nonneg_sqrt(x):
    """sqrt of a real known to be >= 0 (a sum of squares); Real.sqrt is 0 below 0, so
    [sqrt(max(lo,0)), sqrt(max(hi,0))] encloses Real.sqrt of every point of x."""
    return I(np.maximum(x.lo, 0.0), np.maximum(x.hi, 0.0)).sqrt()


class Modes:
    """Per-q, x-independent mode data per SigmaSpec: Iq, Oq (= OmT, `om2S_eq`), vS,
    keepM, wt2, wtM, IeU; plus the theory w~ = sqrt(O/I) where sign(O/I) is decided."""

    def __init__(self, m, q):
        coul = m.coul["avg"]
        Gs, eraw, z, is0 = m.eps_raw(q)
        eps = m.eps_spec(q, Gs, eraw, z, is0, coul, "spec")
        n = len(Gs)
        Ie = I.exact(np.eye(n)) - eps
        ez = (eps.lo == 0) & (eps.hi == 0) & ~np.eye(n, dtype=bool)
        Ie.lo[ez] = 0.0
        Ie.hi[ez] = 0.0
        O, _, _ = m.omega2(q, Gs, coul)
        self.Gs, self.n, self.Ie, self.O = Gs, n, Ie, O
        self.v = coul.vvec(q, Gs) * m.sig.fact
        aI, aO = Ie.abs(), O.abs()
        kI = dec(aI.certainly_ge(TS), aI.certainly_lt(TS), "|I| >= TS")
        kO = dec(aO.certainly_ge(TS), aO.certainly_lt(TS), "|O| >= TS")
        kIO = kI & kO
        wt2 = iv.select(kIO, ~kIO, O / iv.select(kIO, ~kIO, Ie, 1.0), 0.0)
        aw = wt2.abs()
        kw = dec(aw.certainly_ge(TS), aw.certainly_lt(TS), "|wt2| >= TS", kIO)
        keep = kIO & kw
        pos = dec(wt2.certainly_gt(0.0), wt2.certainly_lt(0.0), "wt2 sign", keep)
        valid, inval = keep & pos, keep & ~pos
        w = iv.select(valid, ~valid, iv.select(valid, ~valid, wt2, 1.0).sqrt(), 1.0)
        self.wtM = iv.select(inval, ~inval, WINV, w)       # meaningful on `keep`
        self.keep, self.valid, self.inval = keep, valid, inval
        self.IeU = iv.select(kI, ~kI, Ie, 0.0)
        # theory: sign(O/I) decided?  (O = 0 or I = 0 exactly -> O/I = 0 <= 0: invalid)
        Ip, In = Ie.certainly_gt(0.0), Ie.certainly_lt(0.0)
        Op, On = O.certainly_gt(0.0), O.certainly_lt(0.0)
        zero = ms.isexact0(O) | ms.isexact0(Ie)
        self.th_valid = (Ip & Op) | (In & On)
        self.th_invalid = (Ip & On) | (In & Op) | zero
        self.th_undec = ~self.th_valid & ~self.th_invalid
        r = O / iv.select(self.th_valid, ~self.th_valid, Ie, 1.0)
        self.wT = iv.select(self.th_valid, ~self.th_valid,
                            iv.select(self.th_valid, ~self.th_valid, r, 1.0).sqrt(), 1.0)


def theta(w, D):
    return w / (w + I.exact(D))


def psi(w, D):
    return w / ((w + I.exact(D - 1.0)) * (w + I.exact(D)))


def mode_cr(md, D, kind):
    """Per-mode centre / radius (n x n, index [j, i]) of Cor.lean for the omitted-band
    kernel `kind`: 'S' (specK, cS/rS), 'Sd' (energy step, cSd/rSd), 'T' (thK, cK/rK;
    sign-undecided modes: c = 0, r = |I|/2 by thK_empty_abs), 'Td' (thK step, cKd/rKd;
    undecided: c = 0, r = 2 |I|/2 -- each of the two thK values is within |I|/2).
    'S' and 'T' include the omitted bands' ACq = IeU/4 per mode (the spec's Sigma with all
    bands keeps the residual CORall = shift + Gch + scale terms, R28-F4; the truncated run's COR is kept in SigA(trunc) and this term
    removes its static half band by band); in the energy steps it cancels."""
    Ie, half = md.Ie, I.exact(0.5)
    zero = I.exact(np.zeros(Ie.shape))
    if kind in ("S", "Sd"):
        f = theta(md.wtM, D) if kind == "S" else psi(md.wtM, D)
        c = iv.select(md.keep, ~md.keep, f * half * (-Ie * half), 0.0)
        r = iv.select(md.keep, ~md.keep, f * half * (Ie.abs() * half), 0.0)
        if kind == "S":
            c = c + md.IeU * I.exact(0.25)
        return c, r.hi
    f = theta(md.wT, D) if kind == "T" else psi(md.wT, D)
    c = iv.select(md.th_valid, ~md.th_valid, f * half * (-Ie * half), 0.0)
    r = iv.select(md.th_valid, ~md.th_valid, f * half * (Ie.abs() * half), 0.0).hi
    und = md.th_undec
    c = iv.select(und, ~und, zero, c)
    if kind == "T":
        c = c + md.IeU * I.exact(0.25)
    r = np.where(und, Ie.mag() * (0.5 if kind == "T" else 1.0), r)
    return c, np.nextafter(r, np.inf)


def amp(Gk, ca, Gq, Gs):
    """A[v, i] = c_a(Gq_v + Gs_i) (`Cor.amp`; exact: a selection of stored coefficients)."""
    idx = spec.gindex(Gk)
    A = np.zeros((len(Gq), len(Gs)))
    for v, g2 in enumerate(Gq):
        for i, g in enumerate(Gs):
            u = idx.get(tuple(g2 + g), -1)
            if u >= 0:
                A[v, i] = ca[u]
    return A


class Cor:
    def __init__(self, rundir, coulomb, rundir_all=None):
        self.m = ms.Measure(rundir, coulomb)
        self.run = self.m.run
        self.modes = {tuple(q): Modes(self.m, q) for q in self.run.qlist}
        self.all = spec.Run(rundir_all) if rundir_all else None
        self._kap = {}

    # ------------------------------------------------------------- the enclosure
    def tail(self, k, bands, nb, wf=None, kinds=("S", "Sd", "T", "Td")):
        """Per band a: centre (interval) and radius (upper bound) of every kernel kind, in
        Ry, summed over q; the finite-basis static tail sum v T (-IeU/2); D per q."""
        run = self.run
        wf = wf or run.wf
        pre = self.m.sig.prepare(k, bands)
        Gk, ck, elk = pre["Gk"], pre["ck"], pre["e_lk"]
        out = []
        for a in range(len(bands)):
            acc = {kd: [I.exact(0.0), 0.0] for kd in kinds}
            stat = I.exact(0.0)
            Ds, minT, kmax = [], np.inf, 1.0
            for q in run.qlist:
                md = self.modes[tuple(q)]
                Gq, cq, Eq = cert.real_coeffs(wf, tuple(k - q))
                if len(cq) < nb:
                    raise ValueError("fewer stored bands than nb")
                A = amp(Gk, ck[a], Gq, md.Gs)
                clo = iv.matmul(I.exact(A.T), I.exact(A))
                M = cert.mtxel_iv(Gk, ck[a:a + 1], Gq, cq[:nb], md.Gs)
                M = I(M.lo[0], M.hi[0])                               # (n1, G)
                kappa = self.kappa(wf, k - q, cq[:nb])
                kmax = max(kmax, kappa)
                T = clo * I.exact(kappa) - iv.matmul(M.T, M)            # tailK: T[i, j]
                sd = nonneg_sqrt(I(np.diag(T.lo), np.diag(T.hi)))
                minT = min(minT, float(np.diag(T.lo).min()))
                Dx = I.exact(Eq[nb - 1]) * RYD - elk[a]                 # iw = 0
                D = float(Dx.lo)
                Ds.append(D)
                if not D > 1.5:
                    raise AssertionError("D <= 3/2: hypothesis of the theorems fails")
                # weight matrix  v_i T_ij  at [j, i]  (quad: sum_i sum_j M_i v_i M_j F_ji)
                VT = (T * md.v.reshape(-1, 1)).T                        # [j, i] = v_i T_ij
                Wabs = (sd.reshape(1, -1) * sd.reshape(-1, 1) * md.v.abs().reshape(1, -1)).hi
                stat = stat + (VT * (-md.IeU * I.exact(0.5))).sum(axis=0).sum(axis=0)
                for kd in kinds:
                    c, r = mode_cr(md, D, kd)
                    acc[kd][0] = acc[kd][0] + (VT * c).sum(axis=0).sum(axis=0)
                    acc[kd][1] = float(np.nextafter(acc[kd][1] + float(
                        (I.exact(Wabs) * I.exact(r)).sum(axis=0).sum(axis=0).hi), np.inf))
            out.append(dict(acc=acc, stat=stat, D=Ds, minTdiag=minT, kappa_minus_1=kmax - 1.0))
        return out

    def kappa(self, wf, kq, R):
        """`CompleteK kappa`: a real completion of the computed rows R exists iff
        kappa I - R^T R is PSD; kappa >= lambda_max(R R^T) suffices. Rigorous upper bound
        by Gershgorin on the interval Gram R R^T (binary64 eigenvector rows have
        ||R||_2^2 slightly ABOVE 1, so kappa = 1 would be unsatisfiable)."""
        key = (id(wf), tuple(np.round(kq, 9)), R.shape[0])
        if key not in self._kap:
            G = iv.matmul(I.exact(R), I.exact(R.T))
            off = G.abs().hi.copy()
            np.fill_diagonal(off, 0.0)
            row = I(np.diag(G.hi)) + I(off).sum(axis=1)
            self._kap[key] = float(np.nextafter(row.hi.max(), np.inf))
        return self._kap[key]

    # ------------------------------------------------------------- truncated Sigma
    def cut(self, k, bands, nb=None, wf=None):
        """SigA(trunc nb) per band and iw (Ry): the spec's X + C + COR (Measure.state),
        and its COR alone. For nb > 18 the extra bands 18..nb-1 are added from `wf`."""
        r = self.m.state(k, bands, dict(coul="avg", wings="spec", tolzero="spec"))
        base = [r["X"] + r["C"][iw] + r["COR"] for iw in range(2)]
        return base, r["COR"], r["pre"]

    def exact_extra(self, k, bands, n_from, n_to, wf, kind="S"):
        """Diagnostic (uses the omitted bands' energies): the exact spec contribution
        ACq + Pq of every band n_from <= n < n_to present in `wf`, per n, a and iw (Ry),
        with BerkeleyGW's rule on each band (generic branch, asserted; kind 'S') or with
        the theory kernel thK (kind 'T': invalid modes 0, sign-undecided modes enclosed by
        +-|I|/2). Returns
        cum[a][iw][m] = sum over n_from <= n < n_from + m."""
        run = self.run
        pre = self.m.sig.prepare(k, bands)
        Gk, ck, elk = pre["Gk"], pre["ck"], pre["e_lk"]
        nn = n_to - n_from
        per = [[[I.exact(0.0) for _ in range(nn)] for _ in range(2)] for _ in bands]
        for q in run.qlist:
            md = self.modes[tuple(q)]
            Gq, cq, Eq = cert.real_coeffs(wf, tuple(k - q))
            hi = min(n_to, len(cq))
            M = cert.mtxel_iv(Gk, ck, Gq, cq[n_from:hi], md.Gs)          # (a, n1, G)
            for a in range(len(bands)):
                for j, n1 in enumerate(range(n_from, hi)):
                    x = M[a, j]
                    W = x.reshape(-1, 1) * x.reshape(1, -1) * md.v.reshape(1, -1)  # [r,c]=M_r M_c v_c
                    for iw in range(2):
                        y = I.exact(Eq[n1]) * RYD - elk[a] - I.exact(float(iw))
                        if not y.lo > 0.5:
                            raise AssertionError("omitted band not below E - 1/2")
                        # specK = IeU/4 + theta(wtM, y) (-I/2) on kept modes (schM_tail_ratio)
                        if kind == "S":
                            th = md.wtM / (md.wtM + y)
                            kern = md.IeU * I.exact(0.25) + iv.select(
                                md.keep, ~md.keep, th * (-md.Ie * I.exact(0.5)), 0.0)
                        else:
                            th = md.wT / (md.wT + y)
                            b = md.Ie.mag() * 0.5
                            kern = md.IeU * I.exact(0.25) + iv.select(
                                md.th_valid, ~md.th_valid, th * (-md.Ie * I.exact(0.5)),
                                iv.select(md.th_invalid, ~md.th_invalid, 0.0, I(-b, b)))
                        per[a][iw][j] = per[a][iw][j] + (W * kern).sum(axis=0).sum(axis=0)
        cum = []
        for a in range(len(bands)):
            ca = []
            for iw in range(2):
                acc, lst = I.exact(0.0), [I.exact(0.0)]
                for j in range(nn):
                    acc = acc + per[a][iw][j]
                    lst.append(acc)
                ca.append(lst)
            cum.append(ca)
        return cum


def completable_exact(R):
    """Exact rational test of whether rows R (binary64, taken as exact reals) can be the
    first rows of an exactly complete set (kappa = 1): iff I - R R^T is PSD. LDL^T in
    fractions.Fraction; returns (all pivots > 0, smallest pivot, float)."""
    from fractions import Fraction as Fr
    Rf = [[Fr(float(x)) for x in row] for row in R]
    n = len(Rf)
    A = [[(1 if i == j else 0) - sum(p * q for p, q in zip(Rf[i], Rf[j])) for j in range(n)]
         for i in range(n)]
    piv = []
    for c in range(n):
        p = A[c][c]
        piv.append(p)
        if p <= 0:
            return False, float(p)
        for i in range(c + 1, n):
            f = A[i][c] / p
            for j in range(c + 1, n):
                A[i][j] -= f * A[c][j]
    return True, float(min(piv))


def eqp1_iv(s0, d, eo):
    """The spec's linearised Eqp1 = eo + s0 + d/(1-d) s0 = eo + s0/(1-d) (eV; the identity
    is `Compare.eqp1_linear`, 1 - d certainly nonzero here), in the single-occurrence form
    so that the interval evaluation has no dependency overestimate."""
    return eo + s0 / (I.exact(1.0) - d)


def assemble(cut, tails, kd_s, kd_d, pre):
    """Multiplet-averaged enclosures of Sigma(Eo), dSigma = Sigma(Eo+1)-Sigma(Eo) and Eqp1.
    cut: [iw] interval arrays (Ry) of the truncated Sigma; tails: per a."""
    nb = len(tails)
    s0 = d = I.exact(0.0)
    for a in range(nb):
        c0, r0 = tails[a]["acc"][kd_s]
        cd, rd = tails[a]["acc"][kd_d]
        s0 = s0 + cut[0][a] + c0 + I(-r0, r0)
        d = d + (cut[1][a] - cut[0][a]) + cd + I(-rd, rd)
    n = I.exact(float(nb))
    s0 = s0 / n * RYD
    d = d / n * RYD
    eo = pre["e_lk"].sum() / n
    return s0, d, eqp1_iv(s0, d, eo)


def run_all(rundir, coulomb, rundir_all=None, bgw_run=None):
    t0 = time.time()
    c = Cor(rundir, coulomb, rundir_all)
    run = c.run
    kX, kL = run.kpts[2], run.kpts[1]
    nb0 = run.nbands
    out = dict(inputs=dict(rundir_files=["WFN_inner", "RHO", "eps0mat", "epsmat", "sigma.inp"],
                           coulomb=pathlib.Path(coulomb).name, number_bands=nb0,
                           D_source=f"RYD * e_{nb0}(k - q) - E: the highest computed band "
                                    f"(band {nb0}, 1-based) at each k - q of WFN_inner"))
    st = {}
    for lab, k, bands in (("X", kX, [5, 6]), ("L", kL, [5])):
        cut, cor, pre = c.cut(k, bands)
        tails = c.tail(k, bands, nb0)
        st[lab] = dict(cut=cut, cor=cor, pre=pre, tails=tails, k=k, bands=bands)
    rows = {}
    # baseline (the run's O1, COR with 1/2)
    base = {}
    brow = {}
    for lab in ("X", "L"):
        s = st[lab]
        n = I.exact(float(len(s["bands"])))
        s0 = s["cut"][0].sum() / n * RYD
        d = (s["cut"][1].sum() - s["cut"][0].sum()) / n * RYD
        base[lab] = eqp1_iv(s0, d, s["pre"]["e_lk"].sum() / n)
        brow[lab] = dict(Sigma_Eo_eV=ivl(s0), dSigma_dE=ivl(d), Eqp1_eV=ivl(base[lab]),
                         COR_eV=ivl(s["cor"].sum() / n * RYD))
    rows["baseline_COR_half"] = dict(O1_meV=mev(base["X"] - base["L"]), **brow)
    # the heuristic family: COR with a uniform factor theta in place of 1/2
    fam = {}
    for th in (0.0, 0.25, 0.5, 0.75, 1.0):
        e = {}
        for lab in ("X", "L"):
            s = st[lab]
            n = I.exact(float(len(s["bands"])))
            f = I.exact(2.0 * th - 1.0)
            sg = [s["cut"][iw] + s["cor"] * f for iw in range(2)]
            s0 = sg[0].sum() / n * RYD
            d = (sg[1].sum() - sg[0].sum()) / n * RYD
            e[lab] = eqp1_iv(s0, d, s["pre"]["e_lk"].sum() / n)
        fam[str(th)] = mev(e["X"] - e["L"])
    rows["uniform_theta_O1_meV"] = fam
    for name, kd, kdd in (("spec_rule_tail", "S", "Sd"), ("theory_kernel_tail", "T", "Td")):
        e = {}
        row = {}
        for lab in ("X", "L"):
            s = st[lab]
            s0, d, eq = assemble(s["cut"], s["tails"], kd, kdd, s["pre"])
            e[lab] = eq
            row[lab] = dict(Sigma_Eo_eV=ivl(s0), dSigma_dE=ivl(d), Eqp1_eV=ivl(eq))
        row["O1_meV"] = mev(e["X"] - e["L"])
        rows[name] = row
    # per-band bookkeeping: static tail (finite-basis closure) vs 2 COR (BerkeleyGW's
    # rho_aa closure), centres, radii, and the uniform theta consistent with the enclosure
    book = {}
    for lab in ("X", "L"):
        s = st[lab]
        per = []
        for a, tl in enumerate(s["tails"]):
            cS, rS = tl["acc"]["S"]
            cor = s["cor"][a]
            # uniform theta (float): SigA_cut + (2 theta - 1) COR in [cut + cS - rS, cut + cS + rS]
            thr = sorted([0.5 + 0.5 * float((cS.lo - rS) / cor.mid()),
                          0.5 + 0.5 * float((cS.hi + rS) / cor.mid())])
            per.append(dict(
                D_eV=[min(tl["D"]), max(tl["D"])],
                static_tail_finite_basis_eV=ivl(tl["stat"] * RYD),
                twice_COR_rho_closure_eV=ivl(cor * I.exact(2.0) * RYD),
                min_T_diag=tl["minTdiag"],
                kappa_minus_1_max=tl["kappa_minus_1"],
                **{f"centre_{kd}_eV": ivl(tl["acc"][kd][0] * RYD) for kd in tl["acc"]},
                **{f"radius_{kd}_eV": radius_eV(tl["acc"][kd][1]) for kd in tl["acc"]},
                uniform_theta_range_iw0=thr))
        book[lab] = per
    out["per_band"] = book
    # is kappa = 1 satisfiable for the stored computed rows? (exact rationals)
    chk = []
    for lab in ("X", "L"):
        for q in run.qlist:
            Gq, cq, Eq = cert.real_coeffs(run.wf, tuple(st[lab]["k"] - q))
            ok, p = completable_exact(cq[:nb0])
            chk.append(dict(state=lab, q=q.tolist(), kappa1_completable=ok, first_nonpositive_or_min_pivot=p))
    out["completeness_check"] = dict(
        note="kappa = 1 needs I - R R^T PSD for the stored rows R (binary64 as exact reals)",
        all_kappa1_completable=all(x["kappa1_completable"] for x in chk), cases=chk)
    out["rows"] = rows
    if rundir_all:
        out["all_bands"] = all_bands(c, st, bgw_run)
    out["seconds"] = time.time() - t0
    return out


NBS = (18, 30, 60, 100, 168)


def all_bands(c, st, bgw_run=None):
    """Diagnostic with the 168-band WFN_inner: the enclosure with nb computed bands for nb
    in NBS (bands 18..nb-1 added exactly); nb = 168 is the spec's all-band SigAall
    (static residual CORall included, R28-F4) up to the rigorous enclosure of the (at most 6) basis bands beyond 168 at the
    174-vector k - q spheres. Kernel 'S': BerkeleyGW's rule on every added band; 'T':
    the theory kernel thK on the added bands (nb = 168 only)."""
    wf = c.all.wf
    nb0 = c.run.nbands
    res = {}
    for kind, nbs in (("S", NBS), ("T", (max(NBS),))):
        cums = {lab: c.exact_extra(st[lab]["k"], st[lab]["bands"], nb0, max(NBS), wf, kind)
                for lab in ("X", "L")}
        if kind == "S" and bgw_run:
            # cross-check of the added bands against the Fortran: BerkeleyGW's own Sigma with
            # number_bands = nbx (its COR included) vs SigA of the first nbx bands here
            import observable
            kv, _ = spec.parse_sigma_inp((pathlib.Path(bgw_run) / "sigma.inp").read_text())
            nbx = int(kv["number_bands"][0])
            e = {}
            for lab in ("X", "L"):
                s = st[lab]
                n = I.exact(float(len(s["bands"])))
                sg = [sum((s["cut"][iw][a] + cums[lab][a][iw][nbx - nb0] for a in range(len(s["bands"]))),
                          I.exact(0.0)) for iw in range(2)]
                e[lab] = eqp1_iv(sg[0] / n * RYD, (sg[1] - sg[0]) / n * RYD, s["pre"]["e_lk"].sum() / n)
            prod = observable.observables((pathlib.Path(bgw_run) / "sigma_hp.log").read_text())["O1_Delta_XL"]
            res["bgw_cross_check"] = dict(number_bands=nbx, O1_here_meV=mev(e["X"] - e["L"]),
                                          O1_BerkeleyGW_sigma_hp_meV=1e3 * prod)
        for nb in nbs:
            e = {}
            row = {}
            for lab in ("X", "L"):
                s = st[lab]
                tails = c.tail(s["k"], s["bands"], nb, wf=wf, kinds=(kind, kind + "d"))
                cut = [s["cut"][iw].copy() for iw in range(2)]
                for a in range(len(s["bands"])):
                    for iw in range(2):
                        cut[iw][a] = cut[iw][a] + cums[lab][a][iw][nb - nb0]
                s0, d, eq = assemble(cut, tails, kind, kind + "d", s["pre"])
                e[lab] = eq
                # effective uniform theta: Sigma_all = Sigma_cut + (2 theta - 1) COR (avg, iw = 0)
                n = float(len(s["bands"]))
                s0c = float(s["cut"][0].sum().mid()) / n * RYD_F
                corv = float(s["cor"].sum().mid()) / n * RYD_F
                row[lab] = dict(Sigma_Eo_eV=ivl(s0), dSigma_dE=ivl(d), Eqp1_eV=ivl(eq),
                                radius_eV=[radius_eV(t["acc"][kind][1]) for t in tails],
                                kappa_minus_1_max=max(t["kappa_minus_1"] for t in tails),
                                D_eV=[min(t["D"]) for t in tails],
                                theta_eff_float=0.5 + (float(s0.mid()) - s0c) / (2 * corv))
            row["O1_meV"] = mev(e["X"] - e["L"])
            res[f"nb_{nb}" + ("" if kind == "S" else "_theory_kernel")] = row
    return res


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--all-bands", default=None, help="run dir whose WFN_inner has 168 bands")
    ap.add_argument("--bgw-run", default=None,
                    help="a production run with WFN_inner of 168 bands and sigma number_bands "
                         "< 168 (cross-check of the added bands against BerkeleyGW)")
    ap.add_argument("--coulomb", default=str(EP / "data/coulomb_cert.json"))
    ap.add_argument("--out", default=str(ROOT / "bgw/bridge_cor/data/cor.json"))
    a = ap.parse_args(argv)
    res = run_all(a.rundir, a.coulomb, a.all_bands, a.bgw_run)
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res["rows"], indent=1), res["seconds"])
    return 0


if __name__ == "__main__":
    sys.exit(main())

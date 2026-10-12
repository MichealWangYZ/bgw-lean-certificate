#!/usr/bin/env python3
"""R28-F3: the BRIDGE-COR all-band enclosure for an EXACTLY orthonormal system near the
stored rows, with the explicit propagation term (GW/Bridge/CorPerturb.lean), on Si-EPM.

    python3 bgw/r28_f3/f3.py RUNDIR [--all-bands RUNDIR_ALL] [--out F]

What `CorPerturb.lean` proves (`sigA_all_bands_lowdin`, `sigA_all_bands_true`,
`sigA_diff_all_bands_true`). At each q_t, let R be the stored computed rows (N_b x L, the
binary64 coefficients read as exact reals) and

    eta_t = || R R^T - 1 ||_F^2                                         (gramDef)

If eta_t < 1, there are exactly orthonormal rows R* (Loewdin) with every row within
d_t = sqrt(eta_t) of the stored row (RowDist), completed by exactly L - N_b rows. For
EVERY exactly orthonormal completion of R* with omitted bands at x <= -D_t:

    | SigAall(R*, C) - SigA(stored) - cen |  <=  radP + cenErr + compErr

where, with u_n(G) = M_n(G) the stored pair densities, A_v(G) the amplitudes of state a,
e(G) = sqrt(sum_v A_v(G)^2) d_t (eP), and T = sum_v A A - sum_{n<N_b} u u (Cor.tailK at
kappa = 1):

    dT_ij  = sum_n e_i |u_nj| + |u_ni| e_j + e_i e_j                          (dT)
    cen    = sum_t sum_ij v_i T_ij c_ji                         (Cor.cenK, kappa = 1)
    radP   = sum_t sum_ij |v_i| sqrt(T_ii + dT_ii) sqrt(T_jj + dT_jj) r_ji    (radP)
    cenErr = sum_t sum_ij |v_i| dT_ij |c_ji|                                 (cenErr)
    compErr= sum_t [ sum_{n<nocc} sum_g |vx_g| (2 e_g |u_ng| + e_g^2)          (xErr)
                     + sum_ij |v_i| 751 |IeU_ji| dT_ij ]                    (compErrA)

The energy step has the same form with (cSd, rSd) and 2 compErr. The enclosures
(Sigma_Eo_eV, dSigma_dE, Eqp1_eV, O1_meV and the kappa = 1 comparison) are iv.py
interval arithmetic with outward rounding. The bounds are upper bounds, and the
centres are intervals. Three reported diagnostics are NOT computed that way:
propagation_Sigma_Eo_eV, propagation_dSigma_eV and O1_width_change_meV are plain
binary64 floats (round-to-nearest differences of upper bounds and of widths). They
are not themselves bounds; the JSON key "float_diagnostics_note" says so.

The "propagation term" reported is radP - radK1 + cenErr + compErr, where radK1 is
Cor's radius at kappa = 1 (sqrt clamped at 0, as Real.sqrt is). It is the whole
difference from the kappa = 1 version of the BRIDGE-COR enclosure.

With --all-bands (the 168-band WFN_inner of BRIDGE-COR) the same is evaluated with
N_b = 30, 60, 100, 168 computed bands. This is a diagnostic, as in BRIDGE-COR: it uses
the omitted bands' stored rows and energies.
"""
import argparse
import json
import pathlib
import sys
import time

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
sys.path.insert(0, str(ROOT / "bgw/bridge_measure"))
sys.path.insert(0, str(ROOT / "bgw/bridge_cor"))
import cert  # noqa: E402
import cor  # noqa: E402
import iv  # noqa: E402
from iv import I  # noqa: E402

RYD = cert.RYD
RYD_F = cor.RYD_F
KB = 751.0          # specKc_abs_le: |ACq + Pq kernel| <= 751 |IeU| per mode
NBS = (18, 30, 60, 100, 168)


def up(x):
    return float(np.nextafter(float(x), np.inf))


def gram_defect(R):
    """Upper bound of eta = ||R R^T - 1||_F^2 (rows R as exact reals)."""
    G = iv.matmul(I.exact(R), I.exact(R.T)) - I.exact(np.eye(R.shape[0]))
    m = I(G.mag())
    return up(m.sqr().sum(axis=0).sum(axis=0).hi)


def hi(x):
    return x.hi if isinstance(x, I) else x


class F3:
    def __init__(self, rundir, coulomb, rundir_all=None):
        self.c = cor.Cor(rundir, coulomb, rundir_all)
        self.m = self.c.m
        self.run = self.c.run
        self._eta = {}

    def eta(self, wf, kq, R):
        key = (id(wf), tuple(np.round(kq, 9)), R.shape[0])
        if key not in self._eta:
            self._eta[key] = gram_defect(R)
        return self._eta[key]

    def tail(self, k, bands, nb, wf=None):
        """Per band a, summed over q (Ry): the kappa = 1 centres (kinds S, Sd), Cor's kappa = 1
        radius radK1, the inflated radius radP, cenErr (S, Sd), compErr; and eta, d, D."""
        run, m = self.run, self.m
        wf = wf or run.wf
        pre = m.sig.prepare(k, bands)
        Gk, ck, elk = pre["Gk"], pre["ck"], pre["e_lk"]
        fact = m.sig.fact
        out = []
        for a in range(len(bands)):
            acc = {kd: dict(cen=I.exact(0.0), radK1=0.0, radP=0.0, cenErr=0.0)
                   for kd in ("S", "Sd")}
            comp = xerr = 0.0
            etas, ds, Ds = [], [], []
            for q in run.qlist:
                md = self.c.modes[tuple(q)]
                Gq, cq, Eq = cert.real_coeffs(wf, tuple(k - q))
                if len(cq) < nb:
                    raise ValueError("fewer stored bands than nb")
                R = cq[:nb]
                eta = self.eta(wf, k - q, R)
                if not eta < 1.0:
                    raise AssertionError("Gram defect >= 1: hypothesis of lowdin fails")
                d = float(I(np.array([eta])).sqrt().hi[0])
                etas.append(eta)
                ds.append(d)
                # amplitudes, pair densities, T (kappa = 1)
                A = cor.amp(Gk, ck[a], Gq, md.Gs)
                clo = iv.matmul(I.exact(A.T), I.exact(A))
                M = cert.mtxel_iv(Gk, ck[a:a + 1], Gq, R, md.Gs)
                M = I(M.lo[0], M.hi[0])                                  # (n, G)
                T = clo - iv.matmul(M.T, M)                              # [i, j]
                e = (I(np.diag(clo.hi)).sqrt() * I.exact(d)).hi          # e(G_i), upper
                S = I(M.mag()).sum(axis=0).hi                            # sum_n |u_ni|
                Ie, Se = I.exact(e), I.exact(S)
                dT = (Ie.reshape(-1, 1) * Se.reshape(1, -1) + Se.reshape(-1, 1) * Ie.reshape(1, -1)
                      + Ie.reshape(-1, 1) * Ie.reshape(1, -1) * I.exact(float(nb))).hi  # [i, j]
                Td = I(np.diag(T.lo), np.diag(T.hi))
                sd1 = cor.nonneg_sqrt(Td).hi
                sdP = cor.nonneg_sqrt(Td + I.exact(np.diag(dT))).hi
                va = md.v.abs().hi                                       # |v_i|
                VT = (T * md.v.reshape(-1, 1)).T                         # [j, i] = v_i T_ij
                W1 = (I.exact(sd1.reshape(1, -1)) * I.exact(sd1.reshape(-1, 1))
                      * I.exact(va.reshape(1, -1))).hi                   # [j, i]
                WP = (I.exact(sdP.reshape(1, -1)) * I.exact(sdP.reshape(-1, 1))
                      * I.exact(va.reshape(1, -1))).hi
                VdT = (I.exact(dT.T) * I.exact(va.reshape(1, -1))).hi    # [j, i] = |v_i| dT_ij
                Dx = I.exact(Eq[nb - 1]) * RYD - elk[a]
                D = float(Dx.lo)
                Ds.append(D)
                if not D > 1.5:
                    raise AssertionError("D <= 3/2")
                for kd in ("S", "Sd"):
                    c, r = cor.mode_cr(md, D, kd)
                    s = acc[kd]
                    s["cen"] = s["cen"] + (VT * c).sum(axis=0).sum(axis=0)
                    s["radK1"] = up(s["radK1"] + float((I.exact(W1) * I.exact(r)).sum(axis=0).sum(axis=0).hi))
                    s["radP"] = up(s["radP"] + float((I.exact(WP) * I.exact(r)).sum(axis=0).sum(axis=0).hi))
                    s["cenErr"] = up(s["cenErr"] + float(
                        (I.exact(VdT) * I.exact(c.mag())).sum(axis=0).sum(axis=0).hi))
                # computed-band correlation: 751 sum_ij |v_i| |IeU_ji| dT_ij
                comp = up(comp + float((I.exact(VdT) * (I.exact(md.IeU.mag()) * I.exact(KB))).sum(axis=0).sum(axis=0).hi))
                # exchange: sum_{n<nocc} sum_g |vx_g| (2 e_g |u_ng| + e_g^2), on the Gb sphere
                Gb, _ = run.sphere(q, run.ecutb)
                Ab = cor.amp(Gk, ck[a], Gq, Gb)
                eb = (I(I.exact(Ab).sqr().sum(axis=0).hi).sqrt() * I.exact(d)).hi
                Mb = cert.mtxel_iv(Gk, ck[a:a + 1], Gq, cq[:run.nocc], Gb)
                Mb = I(Mb.lo[0], Mb.hi[0]).mag()                         # (nocc, Gb)
                vbx = (I(np.array([m.sig.coul.vbar(q + g).lo for g in Gb]),
                         np.array([m.sig.coul.vbar(q + g).hi for g in Gb])) * fact).mag()
                ebI = I.exact(eb).reshape(1, -1)
                xe = (I.exact(vbx).reshape(1, -1)
                      * (I.exact(2.0) * ebI * I.exact(Mb) + ebI * ebI)).sum(axis=1).sum(axis=0)
                xerr = up(xerr + float(xe.hi))
            out.append(dict(acc=acc, comp=up(comp + xerr), xerr=xerr, corr_comp=comp,
                            eta=etas, d=ds, D=Ds))
        return out


def assemble(cut, tails):
    """Multiplet averages (eV): Sigma(Eo), dSigma, Eqp1 enclosures, and the parts."""
    n = len(tails)
    s0 = dd = I.exact(0.0)
    parts = dict(radK1_S=0.0, radP_S=0.0, cenErr_S=0.0, radK1_Sd=0.0, radP_Sd=0.0,
                 cenErr_Sd=0.0, compErr=0.0, xErr=0.0)
    for a, tl in enumerate(tails):
        S, Sd, comp = tl["acc"]["S"], tl["acc"]["Sd"], tl["comp"]
        r0 = up(S["radP"] + S["cenErr"] + comp)
        rd = up(Sd["radP"] + Sd["cenErr"] + 2 * comp)
        s0 = s0 + cut[0][a] + S["cen"] + I(-r0, r0)
        dd = dd + (cut[1][a] - cut[0][a]) + Sd["cen"] + I(-rd, rd)
        for kd, s in (("S", S), ("Sd", Sd)):
            for key in ("radK1", "radP", "cenErr"):
                parts[f"{key}_{kd}"] += s[key]
        parts["compErr"] += comp
        parts["xErr"] += tl["xerr"]
    nI = I.exact(float(n))
    s0 = s0 / nI * RYD
    dd = dd / nI * RYD
    parts = {k: v / n * RYD_F * (1 + 1e-12) for k, v in parts.items()}
    return s0, dd, parts


def evaluate(f, st, nb, wf=None, cums=None, nb0=18):
    e, rows = {}, {}
    for lab in ("X", "L"):
        s = st[lab]
        tails = f.tail(s["k"], s["bands"], nb, wf=wf)
        cut = [s["cut"][iw].copy() for iw in range(2)]
        if cums is not None:
            for a in range(len(s["bands"])):
                for iw in range(2):
                    cut[iw][a] = cut[iw][a] + cums[lab][a][iw][nb - nb0]
        s0, dd, parts = assemble(cut, tails)
        eo = s["pre"]["e_lk"].sum() / I.exact(float(len(s["bands"])))
        eq = cor.eqp1_iv(s0, dd, eo)
        e[lab] = eq
        prop0 = parts["radP_S"] - parts["radK1_S"] + parts["cenErr_S"] + parts["compErr"]
        propd = parts["radP_Sd"] - parts["radK1_Sd"] + parts["cenErr_Sd"] + 2 * parts["compErr"]
        rows[lab] = dict(
            eta_max=max(max(t["eta"]) for t in tails), d_max=max(max(t["d"]) for t in tails),
            D_min_eV=min(min(t["D"]) for t in tails),
            Sigma_Eo_eV=cor.ivl(s0), dSigma_dE=cor.ivl(dd), Eqp1_eV=cor.ivl(eq),
            propagation_Sigma_Eo_eV=prop0, propagation_dSigma_eV=propd,
            parts_eV=parts)
        # the same without the propagation term (kappa = 1 radius radK1), for comparison
        s0k = ddk = I.exact(0.0)
        for a, tl in enumerate(tails):
            S, Sd = tl["acc"]["S"], tl["acc"]["Sd"]
            s0k = s0k + cut[0][a] + S["cen"] + I(-S["radK1"], S["radK1"])
            ddk = ddk + (cut[1][a] - cut[0][a]) + Sd["cen"] + I(-Sd["radK1"], Sd["radK1"])
        nI = I.exact(float(len(tails)))
        rows[lab]["kappa1_no_propagation"] = dict(
            Eqp1_eV=cor.ivl(cor.eqp1_iv(s0k / nI * RYD, ddk / nI * RYD, eo)))
        rows[lab]["_eqk"] = cor.eqp1_iv(s0k / nI * RYD, ddk / nI * RYD, eo)
    o1 = e["X"] - e["L"]
    o1k = rows["X"].pop("_eqk") - rows["L"].pop("_eqk")
    return dict(O1_meV=cor.mev(o1), O1_kappa1_no_propagation_meV=cor.mev(o1k),
                O1_width_change_meV=1e3 * (float(o1.hi - o1.lo) - float(o1k.hi - o1k.lo)),
                **rows)


def run_all(rundir, coulomb, rundir_all=None):
    t0 = time.time()
    f = F3(rundir, coulomb, rundir_all)
    run = f.run
    kX, kL = run.kpts[2], run.kpts[1]
    nb0 = run.nbands
    st = {}
    for lab, k, bands in (("X", kX, [5, 6]), ("L", kL, [5])):
        cut, corv, pre = f.c.cut(k, bands)
        st[lab] = dict(cut=cut, pre=pre, k=k, bands=bands)
    out = dict(inputs=dict(rundir_files=["WFN_inner", "RHO", "eps0mat", "epsmat", "sigma.inp"],
                           coulomb=pathlib.Path(coulomb).name, number_bands=nb0,
                           kernel_bound="751 |IeU| (specKc_abs_le)"),
               float_diagnostics_note=(
                   "propagation_Sigma_Eo_eV, propagation_dSigma_eV and O1_width_change_meV "
                   "are plain binary64 float diagnostics (round-to-nearest differences of "
                   "upper bounds and of interval widths), not iv.py outward-rounded bounds. "
                   "parts_eV are plain float sums of upper bounds with a 1e-12 relative safety "
                   "factor (radP, radK1, cenErr, compErr, xErr). The enclosures Sigma_Eo_eV, "
                   "dSigma_dE, Eqp1_eV and O1_meV, and eta_max / d_max (delta_t), are iv.py "
                   "outward intervals or bounds."))
    out["nb_18"] = evaluate(f, st, nb0)
    if rundir_all:
        wf = f.c.all.wf
        cums = {lab: f.c.exact_extra(st[lab]["k"], st[lab]["bands"], nb0, max(NBS), wf, "S")
                for lab in ("X", "L")}
        for nb in NBS:
            out[f"all_bands_nb_{nb}"] = evaluate(f, st, nb, wf=wf, cums=cums, nb0=nb0)
    out["seconds"] = time.time() - t0
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--all-bands", default=None, help="run dir whose WFN_inner has 168 bands")
    ap.add_argument("--coulomb", default=str(ROOT / "bgw/endpoint/data/coulomb_cert.json"))
    ap.add_argument("--out", default=str(ROOT / "bgw/r28_f3/data/f3.json"))
    a = ap.parse_args(argv)
    res = run_all(a.rundir, a.coulomb, a.all_bands)
    pathlib.Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(a.out).write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: (v["O1_meV"] if isinstance(v, dict) and "O1_meV" in v else v)
                      for k, v in res.items()}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())

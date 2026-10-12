#!/usr/bin/env python3
"""R28-F4: the static remainder that the spec's Sigma with ALL bands keeps, on Si-EPM.

    python3 bgw/r28_f4/residual.py RUNDIR RUNDIR_ALL [--out F]

RUNDIR is the pinned 18-band O1 run, and RUNDIR_ALL is the run with a 168-band
WFN_inner (`run_production.py ... --set WFN_co.in:NumberOfBands=168`). These are the
same inputs as `bgw/bridge_cor/cor.py`.

`GW/Bridge/CorResidual.lean` proves the following. Under `CompleteK kappa`, the static
remainder of `SigAall` (`CORall`: CSq plus the static CH terms ACq of every computed and
omitted band) equals

    sum_q [ corScale + corShift + corGch ],     w[j, i] = v_i IeU(I_ji) / 4,
    corScale = (kappa - 1) sum_ij w[j,i] clo[i,j]          (closure scale)
    corShift = sum_ij w[j,i] (clo[i,j] - rho(G_i - G_j))     (shift-closure defect)
    corGch   = sum_ij w[j,i] [G_j - G_i not in Gch] rho(G_i - G_j)   (Gch coverage)

where clo[i,j] = sum_v A_v(G_i) A_v(G_j) and A_v(G) = c_a(Gq_v + G). corShift and
corGch use no band at k - q at all, so they are identical for 18 and 168 computed bands.
This script evaluates the three terms in iv.py interval arithmetic, both at N_b = 18
(kappa from the 18 stored rows) and at N_b = 168 (kappa from the 168 rows). It also
checks them against the direct value of CORall:

    CORall = COR(run, 18 bands) + sum_ij w[j,i] T[i,j],   T = kappa clo - M^T M,

which uses the run's own COR from `measure.Measure.state` (CSq + sum_{n<18} ACq).

It then gives the effect on O1. CORall does not depend on the energy, so it leaves
dSigma/dE unchanged. With the linearised Eqp1 = Eo + Sigma/(1 - dSigma/dE)
(`Compare.eqp1_linear`), removing it moves Eqp1 by exactly -CORall_avg / (1 - d). For d
we use the enclosures that `cor.py` committed in `bgw/bridge_cor/data/cor.json`
(18 bands: the run; 168 bands: the all-band diagnostic), except in the R28-R2 `lowdin`
block, which uses R28-F3's own enclosure in `bgw/r28_f3/data/f3.json`.

Units: eV (meV in the output); Sigma is multiplet averaged (X: bands 5,6; L: band 5).
"""
import argparse
import json
import pathlib
import sys
import time

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "bgw/bridge_cor"))
sys.path.insert(0, str(ROOT / "bgw/endpoint"))
import cor  # noqa: E402
import cert  # noqa: E402
import iv  # noqa: E402
from iv import I  # noqa: E402

RYD = cert.RYD
F3_JSON = ROOT / "bgw/r28_f3/data/f3.json"
COR_JSON = ROOT / "bgw/bridge_cor/data/cor.json"


def ssum(x):
    """Sum of every entry of an interval array (iv.py ordered reductions)."""
    while x.lo.ndim > 0:
        x = x.sum(axis=0)
    return x


def mev(x):
    """Convert an eV interval to meV without narrowing it in binary64."""
    y = x * I.exact(1000.0)
    return [float(y.lo), float(y.hi)]


def from_mev(pair):
    """Committed meV float pair -> eV interval, widened outward by two ulps."""
    lo, hi = (np.float64(pair[0]) / np.float64(1e3), np.float64(pair[1]) / np.float64(1e3))
    for _ in range(2):
        lo, hi = np.nextafter(lo, -np.inf), np.nextafter(hi, np.inf)
    return I(lo, hi)


def to_mev(v):
    """eV interval -> meV float pair, widened outward by one ulp."""
    lo = np.float64(v.lo) * np.float64(1e3)
    hi = np.float64(v.hi) * np.float64(1e3)
    return [float(np.nextafter(lo, -np.inf)), float(np.nextafter(hi, np.inf))]


def rho_matrix(Gk, ca, Gs):
    """rho_aa(G_i - G_j) for every pair (rigorous, `Sig.pd Gk ca Gk ca`)."""
    diffs = {}
    for i, g in enumerate(Gs):
        for j, gp in enumerate(Gs):
            diffs.setdefault(tuple(g - gp), []).append((i, j))
    keys = list(diffs)
    r = cert.mtxel_iv(Gk, ca[None, :], Gk, ca[None, :], np.array(keys))  # (1,1,K)
    n = len(Gs)
    lo, hi = np.zeros((n, n)), np.zeros((n, n))
    for kk, key in enumerate(keys):
        for i, j in diffs[key]:
            lo[i, j], hi[i, j] = r.lo[0, 0, kk], r.hi[0, 0, kk]
    return I(lo, hi)


def terms(c, k, bands, wf_all):
    """Per band a (Ry, summed over q): the three terms at 18 and at 168 bands and the
    direct CORall at 18 bands."""
    run = c.run
    pre = c.m.sig.prepare(k, bands)
    Gk, ck = pre["Gk"], pre["ck"]
    chidx = pre["chidx"]
    nb0 = run.nbands
    _, cor18, _ = c.cut(k, bands)
    out = []
    for a in range(len(bands)):
        acc = {key: I.exact(0.0) for key in
               ("scale18", "scale168", "shift", "shift168", "gch", "tailA18")}
        kap = {"18": 1.0, "168": 1.0}
        for q in run.qlist:
            md = c.modes[tuple(q)]
            Gs, n = md.Gs, md.n
            w = md.IeU * md.v.reshape(1, -1) * I.exact(0.25)          # w[j, i]
            Gq, cq, _ = cert.real_coeffs(run.wf, tuple(k - q))
            A = cor.amp(Gk, ck[a], Gq, Gs)
            clo = iv.matmul(I.exact(A.T), I.exact(A))                 # clo[i, j]
            rho = rho_matrix(Gk, ck[a], Gs)                           # rho(G_i - G_j)
            out_g = np.array([[chidx.get(tuple(Gs[jj] - Gs[ii]), -1) < 0 for ii in range(n)]
                              for jj in range(n)])                    # [j, i]: G_j - G_i not in Gch
            wclo = ssum(w * clo.T)
            k18 = c.kappa(run.wf, k - q, cq[:nb0])
            kap["18"] = max(kap["18"], k18)
            acc["scale18"] = acc["scale18"] + (I.exact(k18) - I.exact(1.0)) * wclo
            acc["shift"] = acc["shift"] + ssum(w * (clo - rho).T)
            rho_out = iv.select(out_g, ~out_g, rho.T, 0.0)            # [j, i]
            acc["gch"] = acc["gch"] + ssum(w * rho_out)
            # direct: the omitted bands' ACq with T = kappa clo - M^T M (18 bands)
            M = cert.mtxel_iv(Gk, ck[a:a + 1], Gq, cq[:nb0], Gs)
            M = I(M.lo[0], M.hi[0])                                   # (n1, G)
            T = clo * I.exact(k18) - iv.matmul(M.T, M)
            acc["tailA18"] = acc["tailA18"] + ssum(w * T.T)
            # 168 bands: same Gk, the 168-band file's k - q sphere and rows
            Gq2, cq2, _ = cert.real_coeffs(wf_all, tuple(k - q))
            A2 = cor.amp(Gk, ck[a], Gq2, Gs)
            clo2 = iv.matmul(I.exact(A2.T), I.exact(A2))
            k168 = c.kappa(wf_all, k - q, cq2[:168])
            kap["168"] = max(kap["168"], k168)
            acc["scale168"] = acc["scale168"] + (I.exact(k168) - I.exact(1.0)) * ssum(w * clo2.T)
            acc["shift168"] = acc["shift168"] + ssum(w * (clo2 - rho).T)
        row = {key: v * RYD for key, v in acc.items()}
        row["COR18_run"] = cor18[a] * RYD
        row["CORall_direct18"] = (cor18[a] + acc["tailA18"]) * RYD
        row["CORall_decomp18"] = (acc["scale18"] + acc["shift"] + acc["gch"]) * RYD
        row["CORall_decomp168"] = (acc["scale168"] + acc["shift168"] + acc["gch"]) * RYD
        row["kappa_minus_1_max"] = {s: v - 1.0 for s, v in kap.items()}
        out.append(row)
    return out


def avg(rows, key):
    s = I.exact(0.0)
    for r in rows:
        s = s + r[key]
    return s / I.exact(float(len(rows)))


def run_all(rundir, rundir_all, coulomb):
    t0 = time.time()
    c = cor.Cor(rundir, coulomb, rundir_all)
    run = c.run
    kX, kL = run.kpts[2], run.kpts[1]
    cj = json.loads(COR_JSON.read_text())
    dX18 = I(*cj["rows"]["baseline_COR_half"]["X"]["dSigma_dE"])
    dL18 = I(*cj["rows"]["baseline_COR_half"]["L"]["dSigma_dE"])
    dX168 = I(*cj["all_bands"]["nb_168"]["X"]["dSigma_dE"])
    dL168 = I(*cj["all_bands"]["nb_168"]["L"]["dSigma_dE"])
    O1_168 = from_mev(cj["all_bands"]["nb_168"]["O1_meV"])  # outward meV -> eV
    res = {"inputs": dict(rundir_number_bands=run.nbands, all_bands_file="WFN_inner (168 bands)",
                          d_source="bgw/bridge_cor/data/cor.json (rows.baseline_COR_half, "
                                   "all_bands.nb_168)")}
    st = {}
    for lab, k, bands in (("X", kX, [5, 6]), ("L", kL, [5])):
        st[lab] = terms(c, k, bands, c.all.wf)
    per = {}
    for lab in ("X", "L"):
        per[lab] = [{key: (mev(v) if isinstance(v, I) else v) for key, v in r.items()}
                    for r in st[lab]]
    res["per_band_meV"] = per
    one = I.exact(1.0)
    eff, dO1_eV = {}, {}
    for nbk, dX, dL, key in (("18", dX18, dL18, "CORall_decomp18"),
                             ("168", dX168, dL168, "CORall_decomp168")):
        cX, cL = avg(st["X"], key), avg(st["L"], key)
        dO1 = cX / (one - dX) - cL / (one - dL)
        parts = {}
        for t in ("shift", "gch"):
            tt = t if (nbk == "18" or t == "gch") else t + "168"
            parts[t] = mev(avg(st["X"], tt) / (one - dX) - avg(st["L"], tt) / (one - dL))
        sc = "scale" + nbk
        parts["scale"] = mev(avg(st["X"], sc) / (one - dX) - avg(st["L"], sc) / (one - dL))
        dO1_eV[nbk] = dO1
        eff[nbk] = dict(CORall_X_avg_meV=mev(cX), CORall_L_avg_meV=mev(cL),
                        O1_contribution_meV=mev(dO1), O1_contribution_by_term_meV=parts)
    res["O1_effect"] = eff
    res["all_band_O1_meV"] = dict(
        with_residual_as_committed=mev(O1_168),
        residual_removed=mev(O1_168 - dO1_eV["168"]),
        note="the committed -3.8 meV diagnostic is SigAall-based and INCLUDES CORall; "
             "residual_removed subtracts the CORall contribution (interval, outward; "
             "iv.py arithmetic in eV, meV conversions widened outward)")
    # Post-review R2: the same subtraction from R28-F3's enclosure. That enclosure covers
    # every exact completion (kappa = 1, the physical row count) of the Löwdin rows R* near
    # the stored rows, widened by the propagation term. For a kappa = 1 completion,
    # corScale = 0, and corShift and corGch read no band at k - q. So the CORall
    # contribution is the shift + Gch part, here with R28-F3's OWN dSigma/dE enclosure
    # (f3.json), all in iv.py interval arithmetic. The conversions of the committed
    # floats are widened outward: meV -> eV by two ulps, eV -> meV by one ulp. That this part carries over
    # unchanged to the R* completion is argued here (it reads no k - q band), not proved
    # in Lean.
    fj = json.loads(F3_JSON.read_text())
    f168 = fj["all_bands_nb_168"]

    dXP = I(*f168["X"]["dSigma_dE"])
    dLP = I(*f168["L"]["dSigma_dE"])
    sgX = avg(st["X"], "shift168") + avg(st["X"], "gch")
    sgL = avg(st["L"], "shift168") + avg(st["L"], "gch")
    sg = sgX / (one - dXP) - sgL / (one - dLP)
    O1_168P = from_mev(f168["O1_meV"])
    rr = O1_168P - sg
    res["all_band_O1_meV"]["lowdin"] = dict(
        with_residual=f168["O1_meV"],
        residual_shift_plus_gch=to_mev(sg),
        residual_removed=to_mev(rr),
        d_source="bgw/r28_f3/data/f3.json all_bands_nb_168.{X,L}.dSigma_dE (R28-F3's own)",
        source="bgw/r28_f3/data/f3.json all_bands_nb_168.O1_meV (R28-F3, every exact "
               "L - N_b completion of the Löwdin rows, propagation included)")
    res["seconds"] = time.time() - t0
    return res


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("rundir_all")
    ap.add_argument("--coulomb", default=str(ROOT / "bgw/endpoint/data/coulomb_cert.json"))
    ap.add_argument("--out", default=str(ROOT / "bgw/r28_f4/data/residual.json"))
    a = ap.parse_args(argv)
    res = run_all(a.rundir, a.rundir_all, a.coulomb)
    p = pathlib.Path(a.out)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: res[k] for k in ("O1_effect", "all_band_O1_meV")}, indent=1),
          res["seconds"])
    return 0


if __name__ == "__main__":
    sys.exit(main())

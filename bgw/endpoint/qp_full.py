#!/usr/bin/env python3
"""Approximation layer A1: the full GPP quasiparticle equation versus Eqp1.

    python3 bgw/endpoint/qp_full.py RUNDIR [--emin -12 --emax 2 --de 0.05]

BerkeleyGW's Eqp1 is one Newton step of  E = Emf - Vxc + Sigma(E)  from
E = Emf, with dSigma/dE a forward difference over 1 eV. This module evaluates
the same GPP Sigma(E) (production conventions: spec.py, replicated Monte Carlo
Coulomb averages) on a grid of E for a degenerate multiplet, and lists every
sign change of f(E) = Emf + Sigma(E) - E, classifying each as a root (the GPP
kernel takes the same branch for every mode on the bracket, so f is continuous
there) or as a jump (a mode changes branch inside the bracket). Float; the
certified version is in qp_cert.py.
"""
import argparse
import functools
import json
import pathlib
import sys

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import coulomb  # noqa: E402
import spec  # noqa: E402
from spec import RYD, TOL_SMALL, TOL_ZERO, gindex, gpp_kernel, gpp_modes, mtxel  # noqa: E402


def sigma_curve(run, k, bands, Es, scr, rho, vbar):
    """Multiplet-averaged Sigma(E) (eV) and per-E branch signatures.

    Returns (sigma[E], X, cor, flips[E]) where flips[i] counts the
    (q, n1, band, mode) whose GPP branch differs between E[i-1] and E[i]."""
    Gk, ck, Ek = run.wf.at(tuple(k))
    nb = np.array(bands) - 1
    Es = np.asarray(Es, float)
    # bare exchange for these bands only
    Xv = np.zeros(len(nb))
    for q in run.qlist:
        Gb, _ = run.sphere(q, run.ecutb)
        Gq, cq, _ = run.wf.at(tuple(k - q))
        Mb = mtxel(Gk, ck[nb], Gq, cq[:run.nocc], Gb)
        vv = np.array([vbar(tuple(q + g)) for g in Gb])
        Xv -= run.fact * np.einsum("nmg,g->n", np.abs(Mb) ** 2, vv)
    nelec = rho["rho"][gindex(rho["gvec"])[(0, 0, 0)]]
    wpsq = RYD * RYD * 16.0 * np.pi * nelec / run.cr.celvol
    S = np.zeros((len(Es), len(nb)))
    cor = np.zeros(len(nb))
    flips = np.zeros(len(Es), dtype=np.int64)     # modes changing branch between E[i-1] and E[i]
    Gch, _ = run.sphere(np.zeros(3), max(run.ecuts, run.ecutb))
    rho_n = mtxel(Gk, ck[nb], Gk, ck[nb], Gch)
    rho_n = np.array([rho_n[i, i] for i in range(len(nb))])
    chidx = gindex(Gch)
    for q in run.qlist:
        Gs, eps, _ = scr.at(q)
        m = gpp_modes(run, q, Gs, eps, scr.vbar, rho, wpsq, nelec)
        v, Ie, wt = m["v"], m["Ieps"], m["wt"]
        Iex = eps.real - np.eye(len(Gs))
        pos = np.array([[chidx.get(tuple(g - gp), -1) for gp in Gs] for g in Gs])
        ok = (np.abs(Iex) >= TOL_SMALL) & (pos >= 0)
        for a in range(len(nb)):
            A = np.where(ok, rho_n[a][np.where(pos >= 0, pos, 0)], 0.0)
            cor[a] += 0.25 * np.real(np.sum((A * Iex).sum(axis=0) * v))
        Gq, cq, Eq = run.wf.at(tuple(k - q))
        M = mtxel(Gk, ck[nb], Gq, cq[:run.nbands], Gs)
        for n1 in range(run.nbands):
            e1 = Eq[n1] * RYD
            occ = n1 < run.nocc
            for a in range(len(nb)):
                x = M[a, n1]
                xc = np.conj(x) * v
                cor[a] -= 0.25 * np.real(np.sum(xc * (-(x @ Ie))))
                prev = None
                for i, E in enumerate(Es):
                    wx = E - e1
                    if abs(wx) < TOL_ZERO:
                        wx = TOL_ZERO
                    ssx, sch, br = gpp_kernel(wx, wt, Ie, occ)
                    if occ:
                        S[i, a] -= np.real(np.sum((x @ ssx) * xc))
                    S[i, a] += 0.5 * np.real(np.sum((x @ sch) * xc))
                    if prev is not None:
                        flips[i] += int(np.count_nonzero(br != prev))
                    prev = br
    sigma = (S + Xv[None, :] + cor[None, :]).mean(axis=1) * RYD
    return sigma, Xv.mean() * RYD, cor.mean() * RYD, flips


def roots(Es, f, sig):
    """Sign changes of f on the grid, each labelled 'root' (same branch
    signature at both ends: continuous) or 'jump'."""
    out = []
    for i in range(len(Es) - 1):
        if np.sign(f[i]) != np.sign(f[i + 1]):
            kind = "root" if sig[i + 1] == 0 else f"bracket-with-{sig[i + 1]}-branch-flips"
            # linear interpolation inside the bracket (float estimate)
            e = Es[i] - f[i] * (Es[i + 1] - Es[i]) / (f[i + 1] - f[i])
            out.append({"bracket": [float(Es[i]), float(Es[i + 1])], "E": float(e), "kind": kind})
    return out


def study(rundir, emin=-12.0, emax=2.0, de=0.05):
    run = spec.Run(rundir)
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    vb = functools.lru_cache(None)(lambda qk: mb.production(np.array(qk)))
    oq = functools.lru_cache(None)(lambda q: mb.oneoverq_production(np.array(q)))
    rho = spec.bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    scr = spec.Screening(run, vb, oq)
    res = {}
    for name, k, bands in (("X", run.kpts[2], [5, 6]), ("L", run.kpts[1], [5])):
        emf = float(np.mean(run.wf.at(tuple(k))[2][np.array(bands) - 1])) * RYD
        Es = emf + np.arange(emin, emax + 1e-9, de)
        s, x, c, sig = sigma_curve(run, k, bands, Es, scr, rho, vb)
        f = emf + s - Es
        res[name] = {"Emf": emf, "E": Es.tolist(), "Sigma": s.tolist(),
                     "roots": roots(Es, f, sig)}
    return res


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rundir")
    ap.add_argument("--emin", type=float, default=-12.0)
    ap.add_argument("--emax", type=float, default=2.0)
    ap.add_argument("--de", type=float, default=0.05)
    ap.add_argument("--out")
    a = ap.parse_args()
    r = study(a.rundir, a.emin, a.emax, a.de)
    for n, d in r.items():
        print(n, "Emf", round(d["Emf"], 6), "roots:", [(round(x["E"], 5), x["kind"]) for x in d["roots"]])
    if a.out:
        pathlib.Path(a.out).write_text(json.dumps(r))

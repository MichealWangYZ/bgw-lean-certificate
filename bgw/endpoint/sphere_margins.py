#!/usr/bin/env python3
"""Exact margins of every cutoff sphere the calculation uses (E1.5).

    python3 bgw/endpoint/sphere_margins.py RUNDIR

For each sphere |q+G|^2 < ecut (bdot and q taken as the exact rationals of the
file doubles), the smallest | |q+G|^2 - ecut | over all G, computed in rational
arithmetic. A margin far above double rounding (~1e-15 relative) means sphere
membership cannot depend on how the production code rounds |q+G|^2.
"""
import pathlib
import sys
from fractions import Fraction as Fr

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import bgwio  # noqa: E402


def margins(rundir):
    d = pathlib.Path(rundir)
    w = bgwio.read_wfn(d / "WFN_inner")
    B = [[Fr(float(x)) for x in r] for r in w["bdot"]]
    G = w["gvec"]

    def n2(v):
        return sum(v[i] * B[i][j] * v[j] for i in range(3) for j in range(3))

    def m(qs, ecut, Gs=G):
        best = None
        for q in qs:
            qf = np.array([float(x) for x in q])
            near = Gs[np.abs(np.einsum("ni,ij,nj->n", qf + Gs, w["bdot"], qf + Gs) - ecut) < 0.5]
            for g in near:
                dd = abs(n2([q[i] + int(g[i]) for i in range(3)]) - Fr(ecut))
                best = dd if best is None or dd < best else best
        return float(best)

    qgrid = [(Fr(i, 2), Fr(j, 2), Fr(l, 2)) for i in range(2) for j in range(2) for l in range(2)]
    eps0 = bgwio.read_eps(d / "eps0mat")
    q0 = tuple(Fr(float(x)) for x in eps0["q"][0]["q"])
    ecuts, ecutb = float(eps0["ecuts"]), float(w["ecutwfc"])
    out = {"sigma exchange sphere": m(qgrid, ecutb), "sigma screened sphere": m(qgrid, ecuts),
           "epsilon q0 sphere": m([q0], ecuts),
           "epsilon q spheres": m([(Fr(0), Fr(0), Fr(1, 2)), (Fr(0), Fr(1, 2), Fr(1, 2))], ecuts)}
    for f in ("WFN_inner", "WFN", "WFNq"):
        ww = bgwio.read_wfn(d / f)
        ks = [tuple(Fr(float(x)) for x in k) for k in ww["kpt"]]
        out[f"{f} wavefunction spheres"] = m(ks, float(ww["ecutwfc"]), ww["gvec"])
    return out


if __name__ == "__main__":
    for k, v in margins(sys.argv[1]).items():
        print(f"{k:28s} min | |q+G|^2 - ecut | = {v:.3e} Ry")

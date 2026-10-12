#!/usr/bin/env python3
"""ARCHIVED (2026-10-02): E2 convergence layer, withdrawn from scope by owner decision 2026-09-23 (docs/ENDPOINT.md); kept with data/e2_results.jsonl, not extended. See docs/CODEMAP.md. -- E2 gate 5: the E1 float reproducer against production at a sweep point.

    python3 bgw/endpoint/e2_layer1.py RUNDIR

Prints the largest deviation over all diagonal-table states and columns
(X, SX-X, CH, Sig, Eqp1, Z) between spec.py (production conventions,
replicated Monte Carlo) and the run's sigma_hp.log.
"""
import functools
import json
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import coulomb  # noqa: E402
import observable  # noqa: E402
import spec  # noqa: E402


def check(rundir):
    run = spec.Run(rundir)
    mb = coulomb.MiniBZ(run.cr.bdot, run.qgrid, run.cr.celvol)
    vb = functools.lru_cache(None)(lambda qk: mb.production(np.array(qk)))
    oq = functools.lru_cache(None)(lambda q: mb.oneoverq_production(np.array(q)))
    rho = spec.bgwio.read_rho(pathlib.Path(rundir) / "RHO")
    scr = spec.Screening(run, vb, oq)
    tables = observable.parse((pathlib.Path(rundir) / "sigma_hp.log").read_text())
    worst = 0.0
    for k in run.kpts:
        prod = {r["n"]: r for r in tables[tuple(k)]}
        for r in spec.quasiparticle(run, k, vb, scr, rho):
            p = prod[r["bands"][0]]
            for a, b in [("X", "X"), ("SXX", "SX-X"), ("CH", "CH"), ("Sig", "Sig"),
                         ("Eqp1", "Eqp1"), ("Z", "Znk")]:
                worst = max(worst, abs(r[a] - p[b]))
    return {"rundir": str(rundir), "max_table_deviation_eV": worst,
            "nbands": run.nbands, "qgrid": [int(x) for x in run.qgrid], "ecuts": run.ecuts,
            "ecutb": run.ecutb}


if __name__ == "__main__":
    print(json.dumps(check(sys.argv[1])))

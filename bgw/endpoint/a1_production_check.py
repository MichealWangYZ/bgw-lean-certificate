#!/usr/bin/env python3
"""A1 production-side check: QP-equation roots from production's own Sigma(E).

    python3 bgw/endpoint/a1_production_check.py GRID_RUNDIR REF_RUNDIR

GRID_RUNDIR: a sigma run of the pinned inputs with `finite_difference_form -3`,
`delta_frequency_eval 0.001`, `max_frequency_eval 8.0` (spectrum.dat holds the
GPP Sigma on Eo +- 8 eV). REF_RUNDIR: the standard run (for Emf).

spectrum.dat columns: Re(SX) = X + (SX - X), Re(CH) includes the static
remainder (checked at E = Eo against the standard table). Two output quirks
of the production file are handled: blank separator lines, and the i4 iw
field that overflows to '****' beyond 9999 points (rows are counted instead).
Note: in this mode the Eqp1 column of sigma_hp.log is NOT a root of the QP
equation (source comment "Not ideal for fdf -3", write_result.f90:129).
"""
import collections
import json
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import observable  # noqa: E402


def roots(grid, ref):
    seq = collections.defaultdict(list)
    for l in (pathlib.Path(grid) / "spectrum.dat").read_text().splitlines():
        if l.startswith("#") or not l.strip():
            continue
        k = tuple(round(float(l[i:i + 12]), 5) for i in (0, 12, 24))
        seq[(k, int(l[42:46]))].append([float(x) for x in l[50:].split()])
    std = observable.parse((pathlib.Path(ref) / "sigma_hp.log").read_text())
    out = {}
    for name, k, bands in (("X", (0.0, 0.5, 0.5), [5, 6]), ("L", (0.0, 0.0, 0.5), [5])):
        A = np.array([seq[(k, b)] for b in bands]).mean(axis=0)
        Ew, SX, CH = A[:, 0], A[:, 1], A[:, 2]
        s = observable.state(std[k], bands[0])
        j = int(np.argmin(abs(Ew - s["Emf"])))
        assert abs(CH[j] - s["CH"]) < 2e-5 and abs(SX[j] - (s["X"] + s["SX-X"])) < 2e-5
        f = s["Emf"] + SX + CH - Ew
        idx = np.flatnonzero(np.sign(f[:-1]) != np.sign(f[1:]))
        out[name] = {"window": [float(Ew[0]), float(Ew[-1])], "n_points": len(Ew),
                     "roots": [float(Ew[i] - f[i] * (Ew[i + 1] - Ew[i]) / (f[i + 1] - f[i])) for i in idx]}
    out["O1_meV"] = (out["X"]["roots"][0] - out["L"]["roots"][0]) * 1e3
    return out


if __name__ == "__main__":
    print(json.dumps(roots(sys.argv[1], sys.argv[2]), indent=1))

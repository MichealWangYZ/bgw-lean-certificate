#!/usr/bin/env python3
"""E0 observables of the Si-EPM GPP run, read from `sigma_hp.log`.

    python3 bgw/endpoint/observable.py RUNDIR_OR_LOG [--json]

O1  Delta_XL = Eqp1(X, c) - Eqp1(L, c)   conclusion C1: Delta_XL > 0 (CBM at L)
O2  E_g      = min_k Eqp1(k, c) - Eqp1(Gamma, v)

`c` is the lowest conduction multiplet, `v` the highest valence multiplet
(4 occupied bands). Every per-state quantity is the average over the
degenerate multiplet containing the state, where the multiplet is read off the
mean-field energies Emf; `multiplet_spread` records how far the production
values vary inside each multiplet (BerkeleyGW symmetrises its diagonal table,
so this is expected to be 0 at print precision; it is a check, not an
assumption). Energies in eV, as printed (9 decimals).
"""
import argparse
import json
import pathlib
import sys

COLUMNS = ["n", "Emf", "Eo", "X", "SX-X", "CH", "Sig", "Vxc", "Eqp0", "Eqp1",
           "CH'", "Sig'", "Eqp0'", "Eqp1'", "Znk"]
NOCC = 4
# BerkeleyGW groups states within TOL_Degeneracy = 1e-6 Ry (Common/nrtype.f90:163)
# of each other; on the printed eV values that is 1.36e-5 eV.
DEGEN_TOL_EV = 1.0e-6 * 13.60569253
KPOINTS = {"Gamma": (0.0, 0.0, 0.0), "L": (0.0, 0.0, 0.5), "X": (0.0, 0.5, 0.5)}


def parse(log_text):
    """Return {k-tuple: [row dict, ...]} for the diagonal tables."""
    out, lines, i = {}, log_text.splitlines(), 0
    while i < len(lines):
        s = lines[i].split()
        if len(s) >= 4 and s[0] == "k" and s[1] == "=":
            k = tuple(float(x) for x in s[2:5])
            while not lines[i].split()[:2] == ["n", "Emf"]:
                i += 1
            if lines[i].split() != ["n", "Emf", "Eo", "X", "SX-X", "CH", "Sig", "Vxc", "Eqp0",
                                    "Eqp1", "CH`", "Sig`", "Eqp0`", "Eqp1`", "Znk"]:
                raise ValueError("unexpected diagonal-table header: " + lines[i])
            rows, i = [], i + 1
            while lines[i].strip():
                f = lines[i].split()
                rows.append({c: (int(f[0]) if c == "n" else float(v))
                             for c, v in zip(COLUMNS, f)})
                i += 1
            if k in out:
                raise ValueError(f"k-point {k} appears twice")
            out[k] = rows
        i += 1
    return out


def multiplets(rows):
    groups = []
    for r in sorted(rows, key=lambda r: r["n"]):
        if groups and abs(r["Emf"] - groups[-1][-1]["Emf"]) <= DEGEN_TOL_EV:
            groups[-1].append(r)
        else:
            groups.append([r])
    return groups


def state(rows, band):
    """Multiplet average of every column for the multiplet containing `band`."""
    for g in multiplets(rows):
        if band in [r["n"] for r in g]:
            avg = {c: sum(r[c] for r in g) / len(g) for c in COLUMNS[1:]}
            spread = max(max(r[c] for r in g) - min(r[c] for r in g) for c in COLUMNS[1:])
            avg.update(bands=[r["n"] for r in g], multiplet_spread=spread)
            return avg
    raise KeyError(band)


def observables(log_text):
    tables = parse(log_text)
    kn = {name: tables[k] for name, k in KPOINTS.items() if k in tables}
    if set(kn) != set(KPOINTS):
        raise ValueError(f"missing k-points: {set(KPOINTS) - set(kn)}")
    for name, rows in kn.items():
        # a multiplet touching the last computed band could extend beyond the
        # window, and then its average would not be basis-invariant
        if any(r["n"] in (NOCC, NOCC + 1) for r in multiplets(rows)[-1]):
            raise ValueError(f"band window at {name} ends inside the band-edge multiplet")
    c = {name: state(rows, NOCC + 1) for name, rows in kn.items()}
    v = state(kn["Gamma"], NOCC)
    # the multiplets must not straddle the gap
    for name, s in c.items():
        if min(s["bands"]) <= NOCC:
            raise ValueError(f"conduction multiplet at {name} contains a valence band")
    if max(v["bands"]) > NOCC:
        raise ValueError("valence multiplet at Gamma contains a conduction band")
    cbm_k = min(c, key=lambda n: c[n]["Eqp1"])
    return {
        "O1_Delta_XL": c["X"]["Eqp1"] - c["L"]["Eqp1"],
        "C1_CBM_at_L": c["X"]["Eqp1"] - c["L"]["Eqp1"] > 0,
        "O2_gap": c[cbm_k]["Eqp1"] - v["Eqp1"],
        "O2_cbm_k": cbm_k,
        "meanfield_Delta_XL": c["X"]["Emf"] - c["L"]["Emf"],
        "states": {"v_Gamma": v, **{f"c_{n}": s for n, s in c.items()}},
        "max_multiplet_spread": max([v["multiplet_spread"]] +
                                    [s["multiplet_spread"] for s in c.values()]),
    }


def load(path):
    p = pathlib.Path(path)
    return (p / "sigma_hp.log" if p.is_dir() else p).read_text()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    o = observables(load(a.run))
    if a.json:
        print(json.dumps(o, indent=2))
    else:
        print(f"O1 Delta_XL = {o['O1_Delta_XL']*1000:+.6f} meV   (mean field "
              f"{o['meanfield_Delta_XL']*1000:+.3f} meV)   C1 (CBM at L): {o['C1_CBM_at_L']}")
        print(f"O2 gap      = {o['O2_gap']:.9f} eV   (CBM at {o['O2_cbm_k']})")
        for n, s in o["states"].items():
            print(f"  {n:8s} bands {s['bands']}  X {s['X']:+.6f}  SX-X {s['SX-X']:+.6f}  "
                  f"CH {s['CH']:+.6f}  Z {s['Znk']:.6f}  Eqp1 {s['Eqp1']:+.6f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

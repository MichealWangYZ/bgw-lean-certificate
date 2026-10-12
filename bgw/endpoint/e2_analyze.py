#!/usr/bin/env python3
"""ARCHIVED (2026-10-02): E2 convergence layer, withdrawn from scope by owner decision 2026-09-23 (docs/ENDPOINT.md); kept with data/e2_results.jsonl, not extended. See docs/CODEMAP.md. -- E2 tables from data/e2_results.jsonl (empirical; see docs/ENDPOINT.md).

    python3 bgw/endpoint/e2_analyze.py [--N 2] [--ecutwfc 11] [--field O1]
"""
import argparse
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def load(path=HERE / "data/e2_results.jsonl"):
    return [json.loads(l) for l in pathlib.Path(path).read_text().splitlines() if l.strip()]


def get(r, field):
    if field in ("O1", "O1_noremainder", "O2"):
        return r[field] * (1e3 if field != "O2" else 1)
    st, col = field.split(".", 1)          # e.g. X.CH, L.SX-X, dXL.CH
    if st == "dXL":
        return (r["X"][col] - r["L"][col]) * 1e3
    return r[st][col]


def table(rows, field, N=2, ecutwfc=11.0, default_eb=True):
    sel = [r for r in rows if r["N"] == N and r["ecutwfc"] == ecutwfc
           and (not default_eb or r["ecutb"] == max(r["ecutwfc"], r["ecuts"]))]
    # rows keyed by the band count actually used (the requested one is raised
    # to the first window that does not cut a degenerate multiplet)
    nbs = sorted({r["nb_used"] for r in sel})
    ecs = sorted({r["ecuts"] for r in sel})
    idx = {(r["nb_used"], r["ecuts"]): r for r in sel}
    out = [f"{field} (N={N}, ecutwfc={ecutwfc:g}); rows nb used, cols ecuts",
           "nb\\ec " + "".join(f"{e:>9g}" for e in ecs)]
    for nb in nbs:
        out.append(f"{nb:5d} " + "".join(f"{get(idx[(nb, e)], field):9.2f}" if (nb, e) in idx else f"{'':>9}"
                                        for e in ecs))
    return "\n".join(out)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=2)
    ap.add_argument("--ecutwfc", type=float, default=11.0)
    ap.add_argument("--field", nargs="+", default=["O1", "O1_noremainder"])
    a = ap.parse_args()
    rows = load()
    for f in a.field:
        print(table(rows, f, a.N, a.ecutwfc))
        print()

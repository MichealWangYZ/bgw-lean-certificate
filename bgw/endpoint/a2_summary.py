#!/usr/bin/env python3
"""A2 summary: production CD vs the exact CD formula, eta dependence, and the
plasmon-pole model error on Sigma_c(X) - Sigma_c(L) at E = Eo.

    python3 bgw/endpoint/a2_summary.py [--out bgw/endpoint/data/a2_summary.json]

Reads data/a2_repro.json (Step 1), data/a2_exact.json (Step 2) and the static
GPP run ~/bgw-e-runs/e0-default/sigma_hp.log (Step 3: Sigma_c = SX-X + CH,
unprimed = with the static remainder, same mean field, bands and cutoffs).
All numbers are float evidence; meV.
"""
import argparse
import json
import pathlib

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
DATA = HERE / "data"
GPP_LOG = pathlib.Path.home() / "bgw-e-runs/e0-default/sigma_hp.log"
STATES = {"X": (3, 5), "L": (2, 5)}             # sigma_hp ik, first band


def read_gpp(path, ik, band):
    lines = pathlib.Path(path).read_bytes().decode("latin1").splitlines()
    inblk = False
    for ln in lines:
        if ln.strip().startswith("k =") and f"ik = {ik:3d}" in ln:
            inblk = True
        elif inblk and ln.split()[:1] == [str(band)] and len(ln.split()) > 10:
            a = ln.split()
            return dict(X=float(a[3]), SXX=float(a[4]), CH=float(a[5]), Sig=float(a[6]))
    raise KeyError((ik, band))


def main(out=None):
    ex = json.loads((DATA / "a2_exact.json").read_text())
    rp = json.loads((DATA / "a2_repro.json").read_text())
    res = {"units": "meV unless stated", "per_state": {}, "O1_c": {}}
    etas = sorted((float(e) for e in ex["states"]["X"]["exact"]), reverse=True)
    for name in ("X", "L"):
        st = ex["states"][name]
        pr = st["production_repro"]
        e05 = st["exact"]["0.05"]
        g = read_gpp(GPP_LOG, *STATES[name])
        qd = list(st["exact_integral_only"].values())
        res["per_state"][name] = {
            "Cor_production_eV": pr["Cor"],
            "Cor_exact_eta0.05_eV": e05["Cor"],
            "production_minus_exact": (pr["Cor"] - e05["Cor"]) * 1e3,
            "  of which residue interpolation": (pr["ReRes"] - st["exact_residue_only"]["ReRes"]) * 1e3,
            "  of which imaginary quadrature": (pr["Int"] - qd[1]["Int"]) * 1e3,
            "quadrature refinement spread": (max(q["Int"] for q in qd) - min(q["Int"] for q in qd)) * 1e3,
            "Cor_exact_vs_eta_eV": {f"{e:g}": st["exact"][f"{e:g}"]["Cor"] for e in etas},
            "ImRes_exact_vs_eta_eV": {f"{e:g}": st["exact"][f"{e:g}"]["ImRes"] for e in etas},
            "GPP_Sigma_c_eV": g["SXX"] + g["CH"],
        }
    O = ex["O1_correlation"]
    o = {f"{e:g}": O["exact"][f"{e:g}"]["Cor"] * 1e3 for e in etas}
    # eta -> 0: fit v0 - a eta^2 through the two smallest eta, check the others
    e1, e2 = etas[-2], etas[-1]
    a = (o[f"{e2:g}"] - o[f"{e1:g}"]) / (e1 ** 2 - e2 ** 2)
    v0 = o[f"{e2:g}"] + a * e2 ** 2
    resid = {f"{e:g}": o[f"{e:g}"] - (v0 - a * e * e) for e in etas}
    gpp = (res["per_state"]["X"]["GPP_Sigma_c_eV"] - res["per_state"]["L"]["GPP_Sigma_c_eV"]) * 1e3
    prod = O["production_repro"]["Cor"] * 1e3
    res["O1_c"] = {
        "production_CD_eta0.05_reproduced": prod,
        "exact_CD_vs_eta": o,
        "production_minus_exact_eta0.05": prod - o["0.05"],
        "  residue interpolation": (O["production_repro"]["ReRes"] - O["exact_residue_only"]["ReRes"]) * 1e3,
        "  imaginary quadrature": (O["production_repro"]["Int"]
                                   - list(O["exact_integral_only"].values())[1]["Int"]) * 1e3,
        "eta_fit": {"form": "v0 - a eta^2 (eta in eV)", "v0": v0, "a_meV_per_eV2": a,
                    "residuals": resid},
        "production_variants": {k: {"eta": v["eta"], "nimag": v["nimag"], "step": v["step"],
                                    "O1_c_production": v["O1_cor_prod_meV"],
                                    "O1_c_reproduced": v["O1_cor_ours_meV"],
                                    "minus_exact_same_eta": v["O1_cor_prod_meV"]
                                    - o.get(f"{v['eta']:g}", np.nan)}
                                for k, v in rp["variants"].items()},
        "GPP": gpp,
        "PPM_error_GPP_minus_exactCD_eta0": gpp - v0,
        "PPM_error_per_state": {n: (res["per_state"][n]["GPP_Sigma_c_eV"]
                                    - res["per_state"][n]["Cor_exact_vs_eta_eV"][f"{e2:g}"]) * 1e3
                                for n in ("X", "L")},
    }
    print(json.dumps(res, indent=1))
    if out:
        pathlib.Path(out).write_text(json.dumps(res, indent=1) + "\n")
    return res


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out")
    main(ap.parse_args().out)

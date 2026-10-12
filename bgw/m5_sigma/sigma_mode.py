#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M4/M5 lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and Data.S3*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- BGW-M5: the M4-R1 target mode carried through `sigma_gpp_cpu`.

    python3 bgw/m5_sigma/sigma_mode.py [--json]

Input `data/m5_dump.dat.gz` comes from one serial run of the
`instrument_m5.py` build, with M5_IG=2 and M5_IGP=1: the M4-R1 target's
consumer (ig, igp). Every float in it is a raw IEEE-754 bit pattern.

Checked here:
  m4      The dump without its SGP/SGQ lines is byte-identical to the
          committed M4-R1 dump, and `bridge.run` on it reproduces the M4
          target (occurrence 1913).
  link    The kernel records used are those of the SAME Sigma call as that
          setup occurrence: the first SGP block after it, with matching band
          `in`/`il`, `my_igp`, `indigp` and `ig`. The kernel's `wtilde` and
          `I_eps` are bit-identical to the setup's exported `wtilde` and
          `I_epsggp`, and imag(wtilde) = 0.
  rule    The first occupied band n1 at iw = 2, fixed in `.agent/tasks/BGW-M5.md`
          before this data existed. It must take the generic branch and not be
          `sexcut`-clamped, or the result is BLOCKED.
  local   For EVERY exported kernel record (all calls), wtilde2, Omega2,
          wdiff, delw, sch and the pre-clamp ssx (and wx at iw = 2) equal their
          binary64 re-evaluation in source order (observed agreement).
"""
import argparse
import gzip
import hashlib
import json
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "bgw" / "m4_gpp"))
import bridge  # noqa: E402

DUMP = HERE / "data" / "m5_dump.dat.gz"
M4_TARGET_OCC = 1913
TOL_ZERO = 1.0e-12          # Common/nrtype.f90:162
U = bridge.U
f64, q64, gamma = bridge.f64, bridge.q64, bridge.gamma

# A-priori budget model, fixed before any M5 residual was computed.
SQRT_SLACK = 2              # |fl(sqrt P) - sqrt P| <= 2u*w, checked by exact squaring
N_LOC = 8                   # multiplicative roundings on each kernel path, rounded up
N_SCH_D = 2                 # wdiff = x - w and its square
N_SSX_D = 4                 # x*x, w*w, the subtraction, its square


class M5Error(Exception):
    pass


def read_lines(path=DUMP):
    with gzip.open(path, "rt") as fh:
        return fh.read().splitlines()


def m4_lines(lines):
    return [l for l in lines if not l.startswith(("SGP ", "SGQ "))]


def all_kernel_records(lines):
    """Every SGP/SGQ pair in the dump, for the local re-evaluation check."""
    out, i = [], 0
    while i < len(lines):
        if lines[i].startswith("SGP "):
            out.append(_pair(lines, i))
            i += 2
        else:
            i += 1
    return out


def _pair(lines, i):
    p, qline = lines[i].split(), lines[i + 1].split()
    if p[0] != "SGP" or qline[0] != "SGQ":
        raise M5Error(f"line {i + 1}: SGP/SGQ out of step")
    pi = [int(x) for x in p[1:]]
    qi = [int(x) for x in qline[1:]]
    if (qi[0], qi[1]) != (pi[2], pi[4]):
        raise M5Error(f"line {i + 2}: SGQ belongs to another (n1, iw)")
    return {
        "line": i + 1, "in": pi[0], "il": pi[1], "n1": pi[2], "n1true": pi[3],
        "iw": pi[4], "my_igp": pi[5], "indigp": pi[6], "ig": pi[7],
        "wxt": pi[8], "e_lk": pi[9], "e_n1kq": pi[10], "w_re": pi[11],
        "w_im": pi[12], "w2": pi[13], "om": pi[14], "ieps": pi[15],
        "wdiff": pi[16], "delw": pi[17], "delwr": pi[18], "wdiffr": pi[19],
        "sch": qi[2], "ssx0": qi[3], "ssx": qi[4], "cut": qi[5], "aqsn": qi[6],
        "aqsm": qi[7], "vcoul": qi[8], "occ": qi[9], "sexcut": qi[10],
        "limittwo": qi[11], "limitone": qi[12]}


def kernel_records(lines):
    """SGP/SGQ pairs of the Sigma call containing M4's setup occurrence."""
    start = next((i for i, l in enumerate(lines)
                  if l.startswith(f"GPP {M4_TARGET_OCC} ")), None)
    if start is None:
        raise M5Error("M4 target setup occurrence not in the dump")
    # The setup loop visits my_igp in increasing order within one call; a new
    # call (same q or not) restarts it. So between the target's setup record
    # and its call's kernel block, every COL must advance my_igp.
    last_igp = int(lines[start].split()[4])
    i = start + 1
    while i < len(lines) and not lines[i].startswith("SGP "):
        t = lines[i].split()
        if t[0] == "RQ":
            raise M5Error("next q visit began before any kernel record")
        if t[0] == "COL":
            if int(t[4]) <= last_igp:
                raise M5Error(f"line {i + 1}: a new Sigma call began before any kernel record")
            last_igp = int(t[4])
        i += 1
    out = []
    while i < len(lines) and lines[i].startswith(("SGP ", "SGQ ")):
        out.append(_pair(lines, i))
        i += 2
    if not out:
        raise M5Error("no kernel records after the target setup")
    return out


def check_link(recs, target):
    col = target["col"]
    for r in recs:
        if (r["in"], r["il"], r["my_igp"], r["indigp"], r["ig"]) != (
                col["in"], col["il"], target["my_igp"], target["indigp"], target["ig"]):
            raise M5Error(f"line {r['line']}: kernel record from another call or mode")
        if r["w_re"] != target["wtilde_bits"] or f64(r["w_im"]) != 0.0:
            raise M5Error(f"line {r['line']}: kernel wtilde is not the setup's pole")
        if r["ieps"] != target["ieps_bits"]:
            raise M5Error(f"line {r['line']}: kernel I_eps is not the setup's I_epsggp")


def check_local(r):
    w, ie, x = f64(r["w_re"]), f64(r["ieps"]), f64(r["wxt"])
    w2 = w * w
    om = w2 * ie
    wd = x - w
    delw = w * wd * (1.0 / (wd * wd))
    cden = x * x - w2
    want = {"w2": w2, "om": om, "wdiff": wd, "delw": delw, "sch": delw * ie,
            "ssx0": om * cden * (1.0 / (cden * cden))}
    if r["iw"] == 2:   # wx = e_lk + dw*(iw-2) - e_n1kq; dw is not exported
        wx = f64(r["e_lk"]) - f64(r["e_n1kq"])
        if abs(wx) < TOL_ZERO:      # mtxel_cor.f90: wx_array(iw) = TOL_Zero
            wx = TOL_ZERO
        want["wxt"] = wx
    for k, v in want.items():
        if f64(r[k]) != v:
            raise M5Error(f"line {r['line']}: {k} is not its binary64 re-evaluation")


def select(recs):
    cands = [r for r in recs if r["iw"] == 2 and f64(r["occ"]) != 0.0]
    if not cands:
        raise M5Error("BLOCKED: no occupied iw=2 record for the target mode")
    r = min(cands, key=lambda r: r["n1true"])
    if f64(r["occ"]) != 1.0:
        raise M5Error(f"BLOCKED: selected band n1={r['n1true']} has occ={f64(r['occ'])}, "
                      "not the full occupation the -ssx + sch/2 endpoint assumes")
    generic = f64(r["wdiffr"]) > f64(r["limittwo"]) and f64(r["delwr"]) < f64(r["limitone"])
    clamped = r["ssx"] != r["ssx0"] or (abs(f64(r["ssx0"])) > f64(r["cut"]) and f64(r["wxt"]) < 0)
    if not generic:
        raise M5Error(f"BLOCKED: selected band n1={r['n1true']} is not in the generic branch")
    if clamped:
        raise M5Error(f"BLOCKED: selected band n1={r['n1true']} is sexcut-clamped")
    return r


def certificate(r, m4c):
    """Exact references and a-priori budgets (all rational)."""
    w, ih, xh = q64(r["w_re"]), q64(r["ieps"]), q64(r["wxt"])
    p_hat = m4c["p_hat"]
    delta = SQRT_SLACK * U * w
    b_p, b_i = m4c["b_p"], m4c["b_i"]
    b_w = delta + b_p / (w - delta)
    x_star = q64(r["e_lk"]) - q64(r["e_n1kq"])
    b_x = U * abs(xh)
    sch_loc = w * ih / (xh - w)
    ssx_loc = w * w * ih / (xh * xh - w * w)
    b_sch_loc = abs(sch_loc) * (gamma(N_LOC) + gamma(N_SCH_D) * (abs(xh) + w) / abs(xh - w))
    b_ssx_loc = abs(ssx_loc) * (gamma(N_LOC) + gamma(N_SSX_D) * (xh * xh + w * w) / abs(xh * xh - w * w))
    i_star, o_star, p_star = m4c["i_star"], m4c["o_star"], m4c["p_star"]
    ssx_star = o_star / (x_star * x_star - p_star)
    return {"w_hat": w, "i_hat": ih, "x_hat": xh, "x_star": x_star, "p_hat": p_hat,
            "delta": delta, "b_w": b_w, "b_x": b_x, "b_p": b_p, "b_i": b_i,
            "sch_hat": q64(r["sch"]), "ssx_hat": q64(r["ssx"]), "ssx0_hat": q64(r["ssx0"]),
            "sch_loc": sch_loc, "ssx_loc": ssx_loc,
            "b_sch_loc": b_sch_loc, "b_ssx_loc": b_ssx_loc,
            "i_star": i_star, "o_star": o_star, "p_star": p_star, "ssx_star": ssx_star,
            "wdiffr": q64(r["wdiffr"]), "delwr": q64(r["delwr"]),
            "limittwo": q64(r["limittwo"]), "limitone": q64(r["limitone"]),
            "cut": q64(r["cut"]), "rec": r}


def run(lines=None):
    lines = lines if lines is not None else read_lines()
    base = m4_lines(lines)
    committed = bridge.read_lines()
    if base != committed:
        raise M5Error("the non-kernel records differ from the committed M4-R1 dump")
    res = bridge.run(base)
    t = res["target"]
    if t["occ"] != M4_TARGET_OCC:
        raise M5Error("M4 target moved")
    recs = kernel_records(lines)
    check_link(recs, t)
    every = all_kernel_records(lines)
    for r in every:
        check_local(r)
    r = select(recs)
    return {"m4": res, "records": len(recs), "all_records": len(every), "sel": r, "cert": certificate(r, res["cert"])}


def summary(res):
    c, r = res["cert"], res["sel"]
    return {"kernel_records_same_call": res["records"],
            "selected": {"n1": r["n1true"], "iw": r["iw"], "band_in": r["in"]},
            "values": {k: float(c[k]) for k in ("w_hat", "x_hat", "x_star", "sch_hat",
                                                  "ssx_hat", "ssx_star")},
            "budgets": {k: float(c[k]) for k in ("delta", "b_w", "b_x", "b_sch_loc",
                                                  "b_ssx_loc")}}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    try:
        res = run()
    except (M5Error, bridge.BridgeError) as e:
        print(f"FAIL: {e}")
        return 1
    s = summary(res)
    print(json.dumps(s, indent=2) if a.json else "\n".join(f"{k}: {v}" for k, v in s.items()))
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M4/M5 lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and Data.S3*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- BGW-M4-R1: bind Sigma's consumed GPP operands to the M2-certified block.

    python3 bgw/m4_gpp/bridge.py            # checks + frozen target summary
    python3 bgw/m4_gpp/bridge.py --json     # the same, machine-readable

Input: `data/m4r1_dump.dat.gz`, written by the write-only instrumentation of
`instrument_r1.py` in one serial real-flavor Sigma run. Every float in the
dump is a raw IEEE-754 bit pattern; nothing here parses a decimal rendering.

What is checked, for EVERY surviving GPP record that reads stored block
nm = 2 (the M2 block, q = (0, 0, 1/2)), not only the target:

  map     The row label BerkeleyGW uses, `G_eps(ind(ig))`, equals M2's pinned
          basis label at position `ind(ig)`; and it equals S^-1 (G_rq + kg)
          recomputed here from the exported integer symmetry, so the index
          map is not taken on BerkeleyGW's word. The phase is exactly +/-1
          and has the sign of cos((G_rq + kg) . tau), recomputed here.
          The column read (`indigp`) is the image of the consumer G' under
          the same map, so rows and columns are transformed together.
  operand The consumed `epstemp(ind(ig))` has exactly the bits of M2's
          exported inverse entry `Xhat[ind(ig), indigp]`.
  local   `epsggp`, `I_epsggp`, `Omega2 = wpmtx` and `wtilde2` equal their
          binary64 re-evaluation in source order. This is observed agreement
          for these operands, not a theorem about the compiled code.

Then one target is frozen by a rule that never looks at a certificate
residual: among eligible records (off-diagonal, real sqrt branch taken,
nonzero Omega2 and I_eps, positive exact squared-pole reference), the
lexicographically first source pair `(ind(ig), indigp)` in M2's basis order,
then the smallest runtime occurrence number.
"""
import argparse
import gzip
import importlib.util
import json
import math
import pathlib
import struct
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DUMP = HERE / "data" / "m4r1_dump.dat.gz"
M2_DUMP = ROOT / "bgw" / "m2_screening" / "data" / "m2_dump_q2.txt"
M2_RUNID = "m2-20260917-q2-cut15"
M2_NM = 2
M2_Q = (F(0), F(0), F(1, 2))
U = F(1, 2 ** 53)
TOL_SMALL = 1.0e-6          # Common/nrtype.f90:161, as the binary64 literal 1.0d-6

# A-priori rounding counts, fixed from the operation trace before any
# certificate discrepancy was computed (see PROVENANCE.md, "Budgets").
N_OMEGA = 16                # 13 roundings on the longest term path, rounded up
N_FORMATION = 3             # ph*ph, *eps, 0 - x
N_MAP = 4                   # wing normalization: at most 4 roundings (fixwings.f90)


class BridgeError(Exception):
    pass


def f64(bits):
    return struct.unpack("<d", struct.pack("<q", int(bits)))[0]


def q64(bits):
    return F(f64(bits))


def gamma(n):
    return n * U / (1 - n * U)


def _load(name, rel):
    s = importlib.util.spec_from_file_location(name, ROOT / rel)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


# ---------------------------------------------------------------- inputs

def load_m2():
    """M2's basis labels, exported inverse bits, and exact reference."""
    labels, xbits = [], {}
    for line in M2_DUMP.read_text().splitlines():
        t = line.split()
        if t[0] == "GVEC":
            labels.append(tuple(int(v) for v in t[2:5]))
        elif t[0] == "EPSINV":
            xbits[(int(t[1]), int(t[2]))] = int(t[4])
    x = _load("m2x", "bgw/m2_screening/extract.py")
    ref = _load("m2r", "bgw/m2_screening/reference.py")
    b = x.load_single(M2_DUMP, M2_RUNID, 2, expected_n=8,
                      expected_q=(0.0, 0.0, 0.5))
    chi, v, _E, _X, _ = x.matrices(b)
    rstar = ref.exact_inverse(ref.e_star(chi, v))
    if len(labels) != 8 or len(xbits) != 64:
        raise BridgeError("M2 dump does not hold one 8x8 block")
    return {"labels": labels, "xbits": xbits, "rstar": rstar}


def read_lines(path=DUMP):
    with gzip.open(path, "rt") as fh:
        return fh.read().splitlines()


def parse(lines):
    """Attach to each GPP record the map, column and wpeff context it used.

    The run is serial, so records appear in execution order: RQ, SYM, MAP*
    once per q visit; then per G' a COL, the wpeff block (WPG, WPF, WP*),
    and the GPP records of the modes that survived.
    """
    rq = col = wpg = wpf = wing = None
    maps, wp, out = {}, {}, []
    for n, line in enumerate(lines, 1):
        t = line.split()
        tag = t[0]
        if tag == "WING":
            v = [int(a) for a in t[1:]]
            wing = {"irq": v[0], "nm": v[1], "iout": v[2], "icutv": v[3],
                    "iscreen": v[4], "averagew": v[5], "q0_branch": v[6],
                    "avg_branch": v[7],
                    "vcoul1": q64(v[8]), "qlen": q64(v[9]), "q0len": q64(v[10]),
                    "oneoverq": q64(v[11]), "fact": q64(v[12]),
                    "avgcut": q64(v[13]), "pi_d": q64(v[14])}
        elif tag == "RQ":
            v = [int(a) for a in t[1:]]
            rq = {"irq": v[0], "nm": v[1], "itran": v[2], "kg": tuple(v[3:6]),
                  "ncouls": v[6], "nmtx": v[7], "nrq": v[8],
                  "rq": tuple(q64(b) for b in v[9:12]),
                  "qk": tuple(q64(b) for b in v[12:15])}
            if wing is None or wing["irq"] != rq["irq"] or wing["nm"] != rq["nm"]:
                raise BridgeError(f"line {n}: RQ without the wing record of its visit")
            rq["wing"], wing = wing, None
            maps = {}
        elif tag == "SYM":
            v = [int(a) for a in t[1:]]
            if v[0] != rq["irq"]:
                raise BridgeError(f"line {n}: SYM for a different irq")
            rq["S"] = [v[1:4], v[4:7], v[7:10]]
            rq["tnp_bits"] = tuple(v[10:13])
        elif tag == "MAP":
            v = [int(a) for a in t[1:]]
            if v[0] != rq["irq"]:
                raise BridgeError(f"line {n}: MAP for a different irq")
            maps[v[1]] = {"ind": v[2], "g_rq": tuple(v[3:6]),
                          "g_eps": tuple(v[6:9]), "ph_bits": v[9]}
        elif tag == "MAPNONE":
            raise BridgeError(f"line {n}: a G vector fell outside the eps sphere")
        elif tag == "COL":
            v = [int(a) for a in t[1:]]
            col = {"in": v[0], "il": v[1], "ispin": v[2], "my_igp": v[3],
                   "indigp": v[4], "igp": v[5], "coulfact_bits": v[6],
                   "qk_bits": tuple(v[7:10])}
            wp = {}
        elif tag == "WPG":
            v = [int(a) for a in t[1:]]
            wpg = {"igp": v[0], "ncouls": v[1], "nspin": v[2],
                   "bdot_bits": [v[3:6], v[6:9], v[9:12]], "coulfact_bits": v[12]}
        elif tag == "WPF":
            v = [int(a) for a in t[1:]]
            wpf = {"igp": v[0], "wpsq_bits": v[1], "nelec_bits": v[2],
                   "fact_bits": v[3], "q_nonzero": v[4], "qk_bits": tuple(v[5:8])}
        elif tag == "WP":
            v = [int(a) for a in t[1:]]
            wp[v[1]] = {"igp": v[0], "g": tuple(v[2:5]), "gp": tuple(v[5:8]),
                        "vcoul_bits": v[8], "rho_bits": v[9], "wpmtx_bits": v[10]}
        elif tag == "WPNONE":
            v = [int(a) for a in t[1:]]
            wp[v[1]] = {"igp": v[0], "none": True, "wpmtx_bits": v[2]}
        elif tag == "GPP":
            v = [int(a) for a in t[1:]]
            rec = {"line": n, "occ": v[0], "ig": v[1], "igp": v[2], "my_igp": v[3],
                   "indigp": v[4], "ind": v[5], "real_branch": v[6],
                   "phg_bits": v[7], "phgp_bits": v[8], "eps_bits": v[9],
                   "epsggp_bits": v[10], "ieps_bits": v[11], "omega2_bits": v[12],
                   "wtilde2_bits": v[13], "wtilde_bits": v[14]}
            if col is None or col["igp"] != rec["igp"] or col["indigp"] != rec["indigp"]:
                raise BridgeError(f"line {n}: GPP record without its COL context")
            if wpg is None or wpg["igp"] != rec["igp"] or wpf["igp"] != rec["igp"]:
                raise BridgeError(f"line {n}: GPP record without its wpeff context")
            rec.update(rq=rq, maps=dict(maps), col=col, wpg=wpg, wpf=wpf,
                       wp=wp.get(rec["ig"]))
            out.append(rec)
        else:
            raise BridgeError(f"line {n}: unknown record {tag!r}")
    return out


# ---------------------------------------------------------------- checks

def _inv3(S):
    a = S
    det = (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
           - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
           + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))
    if det not in (1, -1):
        raise BridgeError(f"symmetry matrix has determinant {det}")
    cof = [[(a[(r + 1) % 3][(c + 1) % 3] * a[(r + 2) % 3][(c + 2) % 3]
             - a[(r + 1) % 3][(c + 2) % 3] * a[(r + 2) % 3][(c + 1) % 3])
            for r in range(3)] for c in range(3)]
    return [[cof[r][c] * det for c in range(3)] for r in range(3)]


def check_map(rq, maps, m2):
    """The finite map T for one q visit onto the M2 block, checked entrywise."""
    if rq["nm"] != M2_NM or rq["qk"] != M2_Q:
        raise BridgeError(f"irq {rq['irq']}: not the M2 block")
    if rq["ncouls"] != 8 or rq["nmtx"] != 8 or sorted(maps) != list(range(1, 9)):
        raise BridgeError(f"irq {rq['irq']}: consumer basis is not the 8-vector block")
    sinv = _inv3(rq["S"])
    tnp = [f64(b) for b in rq["tnp_bits"]]
    image = []
    for ig in range(1, 9):
        m = maps[ig]
        if not 1 <= m["ind"] <= 8:
            raise BridgeError(f"irq {rq['irq']} ig {ig}: ind {m['ind']} outside block")
        if m["g_eps"] != m2["labels"][m["ind"] - 1]:
            raise BridgeError(f"irq {rq['irq']} ig {ig}: eps label {m['g_eps']} is not "
                              f"M2 basis label {m2['labels'][m['ind'] - 1]}")
        kgv = [m["g_rq"][k] + rq["kg"][k] for k in range(3)]
        rot = tuple(sum(sinv[r][c] * kgv[c] for c in range(3)) for r in range(3))
        if rot != m["g_eps"]:
            raise BridgeError(f"irq {rq['irq']} ig {ig}: S^-1(G+kg) = {rot}, "
                              f"BerkeleyGW used {m['g_eps']}")
        ph = f64(m["ph_bits"])
        want = math.copysign(1.0, math.cos(sum(kgv[k] * tnp[k] for k in range(3))))
        if ph not in (1.0, -1.0) or ph != want:
            raise BridgeError(f"irq {rq['irq']} ig {ig}: phase {ph!r}, recomputed {want!r}")
        image.append(m["ind"])
    if sorted(image) != list(range(1, 9)):
        raise BridgeError(f"irq {rq['irq']}: ind is not a permutation of the block")


def wing_factor(rq, row, col):
    """The source-level normalization fixwings applies to eps(row, col).

    Common/fixwings.f90, icutv = TRUNC_NONE, iscreen = SCREEN_SEMICOND,
    q0flag = .false. (the `qlen**2 < avgcut` call in sigma_main, which passes
    `qlen` as `q0len`):
        row = G0, col != G0:  x*oneoverq*qlen/(8*PI_D)
        col = G0, row != G0:  x*fact*oneoverq/(vcoul(1)*qlen)
        head, and every non-wing entry: unchanged.
    Returns (kind, exact factor, binary64 evaluator in source order).
    """
    w = rq["wing"]
    g0 = w["iout"]
    if row != g0 and col != g0:
        return "bulk", F(1), lambda x: x
    if (w["icutv"], w["iscreen"], w["q0_branch"], w["avg_branch"]) != (0, 0, 0, 1):
        raise BridgeError(f"irq {rq['irq']}: wing branch outside this reconstruction")
    if row == g0 and col == g0:
        return "head", F(1), lambda x: x
    oq, ql, pi = float(w["oneoverq"]), float(w["qlen"]), float(w["pi_d"])
    fa, vc = float(w["fact"]), float(w["vcoul1"])
    if row == g0:
        k = w["oneoverq"] * w["qlen"] / (8 * w["pi_d"])
        return "row-wing", k, lambda x: x * oq * ql / (8.0 * pi)
    k = w["fact"] * w["oneoverq"] / (w["vcoul1"] * w["qlen"])
    return "col-wing", k, lambda x: x * fa * oq / (vc * ql)


def check_record(rec, m2):
    """Operand identity and local binary64 agreement for one surviving mode."""
    maps, ig, igp = rec["maps"], rec["ig"], rec["igp"]
    where = f"GPP occ {rec['occ']} (line {rec['line']})"
    if maps[ig]["ind"] != rec["ind"]:
        raise BridgeError(f"{where}: row index disagrees with the map")
    if maps[igp]["ind"] != rec["indigp"]:
        raise BridgeError(f"{where}: column {rec['indigp']} is not the image "
                          f"{maps[igp]['ind']} of G' under the same map")
    if rec["phg_bits"] != maps[ig]["ph_bits"] or rec["phgp_bits"] != maps[igp]["ph_bits"]:
        raise BridgeError(f"{where}: phase differs from the map")
    kind, _k, apply = wing_factor(rec["rq"], rec["ind"], rec["indigp"])
    want = apply(f64(m2["xbits"][(rec["ind"], rec["indigp"])]))
    if f64(rec["eps_bits"]) != want or (want == 0 and rec["eps_bits"] != m2["xbits"][(rec["ind"], rec["indigp"])]):
        raise BridgeError(f"{where}: consumed operand is not the {kind} image of "
                          f"M2's Xhat[{rec['ind']},{rec['indigp']}]")
    phg, phgp, eps = f64(rec["phg_bits"]), f64(rec["phgp_bits"]), f64(rec["eps_bits"])
    epsggp = phg * phgp * eps
    ieps = (1.0 if ig == igp else 0.0) - epsggp
    w = rec["wp"]
    if w is None or w.get("none") or (w["igp"], ) != (igp, ):
        raise BridgeError(f"{where}: no wpeff operands for this G")
    om = f64(rec["omega2_bits"])
    checks = [("epsggp", rec["epsggp_bits"], epsggp), ("I_epsggp", rec["ieps_bits"], ieps),
              ("wtilde2", rec["wtilde2_bits"], om / f64(rec["ieps_bits"]))]
    for name, bits, val in checks:
        if f64(bits) != val:
            raise BridgeError(f"{where}: {name} is not its binary64 re-evaluation")
    if rec["omega2_bits"] != w["wpmtx_bits"]:
        raise BridgeError(f"{where}: Omega2 is not the wpeff output")


# ---------------------------------------------------------------- reference

def primitives(rec):
    """The exact operands of wpmtx(ig) for this G' (all decoded, none derived)."""
    wpg, wpf, w = rec["wpg"], rec["wpf"], rec["wp"]
    if wpg["nspin"] != 1 or wpf["q_nonzero"] != 1:
        raise BridgeError("wpeff took a branch outside this reconstruction")
    if wpf["qk_bits"] != rec["col"]["qk_bits"] or wpg["coulfact_bits"] != rec["col"]["coulfact_bits"]:
        raise BridgeError("wpeff and mtxel_cor disagree on q or coulfact")
    return {"bdot": [[q64(b) for b in row] for row in wpg["bdot_bits"]],
            "coulfact": q64(wpg["coulfact_bits"]),
            "wpsq": q64(wpf["wpsq_bits"]), "nelec": q64(wpf["nelec_bits"]),
            "q": tuple(q64(b) for b in wpf["qk_bits"]),
            "g": w["g"], "gp": w["gp"],
            "vcoul": q64(w["vcoul_bits"]), "rho": q64(w["rho_bits"])}


def omega_star(p):
    """wpeff's real-flavor, q != 0, nspin = 1 expression, in exact arithmetic.

    fact = wpsq/nelec; precalc_j = fact*vcoul*(G+q)_j/coulfact;
    Omega2 = sum_i (G'+q)_i sum_j bdot_ij precalc_j * rho(G-G').
    Returns (value, the same expression with every operand in absolute value).
    """
    fact = p["wpsq"] / p["nelec"]
    qg = [p["g"][k] + p["q"][k] for k in range(3)]
    qgp = [p["gp"][k] + p["q"][k] for k in range(3)]
    pre = [fact * p["vcoul"] * qg[k] / p["coulfact"] for k in range(3)]
    val = sum(qgp[i] * sum(p["bdot"][i][j] * pre[j] for j in range(3))
              for i in range(3)) * p["rho"]
    mag = sum(abs(qgp[i]) * sum(abs(p["bdot"][i][j]) * abs(pre[j]) for j in range(3))
              for i in range(3)) * abs(p["rho"])
    return val, mag


def certificate(rec, m2):
    """References, measured values and a-priori budgets for one target."""
    i, j = rec["ind"], rec["indigp"]
    pha, phb = q64(rec["phg_bits"]), q64(rec["phgp_bits"])
    delta = F(1) if rec["ig"] == rec["igp"] else F(0)
    kind, kappa, _apply = wing_factor(rec["rq"], i, j)
    xhat = q64(m2["xbits"][(i, j)])
    eps_hat = q64(rec["eps_bits"])
    rstar = m2["rstar"][i - 1][j - 1]
    s_star = pha * phb * kappa * rstar
    i_star = delta - s_star
    p = primitives(rec)
    o_star, o_mag = omega_star(p)
    o_hat, i_hat, p_hat = q64(rec["omega2_bits"]), q64(rec["ieps_bits"]), q64(rec["wtilde2_bits"])
    b_m2 = m2_btotal()
    l_t = abs(pha * phb * kappa)
    b_map = F(0) if kind in ("bulk", "head") else gamma(N_MAP) * abs(kappa * xhat)
    b_form = gamma(N_FORMATION) * abs(eps_hat)
    b_i = b_map + b_form + l_t * b_m2
    b_omega = gamma(N_OMEGA) * o_mag
    b_div = U * abs(o_hat / i_hat)
    d = abs(i_star) - b_i
    b_p = b_div + b_omega / d + abs(o_star) * b_i / (abs(i_star) * d)
    return {"src": (i, j), "ph": (pha, phb), "kind": kind, "kappa": kappa,
            "wing": rec["rq"]["wing"], "eps_hat": eps_hat, "xhat": xhat, "rstar": rstar,
            "i_star": i_star, "o_star": o_star, "p_star": o_star / i_star,
            "o_mag": o_mag, "o_hat": o_hat, "i_hat": i_hat, "p_hat": p_hat,
            "b_m2": b_m2, "l_t": l_t, "b_map": b_map, "b_form": b_form, "b_i": b_i,
            "b_omega": b_omega, "b_div": b_div, "d": d, "b_p": b_p, "prims": p}


def m2_btotal(_ref=None):
    """M2's Lean `bTotal`, from the frozen constants in M2Screening.lean.

    The M4 composition in Lean uses `M2.total_error_bound`, so the budget must
    be that definition's value, not a re-derivation of it.
    """
    import re
    text = (ROOT / "GW" / "BGW" / "M2Screening.lean").read_text()
    def const(name):
        m = re.search(rf"def {name} : ℚ := \((-?\d+) / (\d+) : ℚ\)", text)
        if not m:
            raise BridgeError(f"M2Screening.lean: constant {name} not found")
        return F(int(m.group(1)), int(m.group(2)))
    for pat in (r"def bInv : ℚ := 100 \* 8 \* \(1 / 2 \^ 53\) \* nrmEhat \* nrmRhat \^ 2",
                r"def bShift : ℚ := nrmRhat \* bForm \* nrmRstar",
                r"def bTotal : ℚ := bInv \+ bShift"):
        if not re.search(pat, text):
            raise BridgeError(f"M2Screening.lean: budget definition changed ({pat})")
    e, r, rs, bf = (const(n) for n in ("nrmEhat", "nrmRhat", "nrmRstar", "bForm"))
    return 100 * 8 * F(1, 2 ** 53) * e * r ** 2 + r * bf * rs


def eligible(rec, m2):
    if rec["rq"]["nm"] != M2_NM or rec["ig"] == rec["igp"] or rec["real_branch"] != 1:
        return False
    om, ie, wt = (f64(rec[k]) for k in ("omega2_bits", "ieps_bits", "wtilde2_bits"))
    if om == 0 or ie == 0 or not wt > 0:
        return False
    p = primitives(rec)
    o_star, _ = omega_star(p)
    pha, phb = q64(rec["phg_bits"]), q64(rec["phgp_bits"])
    _kind, kappa, _a = wing_factor(rec["rq"], rec["ind"], rec["indigp"])
    i_star = -pha * phb * kappa * m2["rstar"][rec["ind"] - 1][rec["indigp"] - 1]
    return i_star != 0 and o_star / i_star > 0


def run(lines=None, m2=None):
    m2 = m2 or load_m2()
    recs = parse(lines if lines is not None else read_lines())
    # One entry per q VISIT (an irq recurs once per k-point), not per irq.
    visits = {}
    for r in recs:
        if r["rq"]["nm"] == M2_NM:
            visits.setdefault(id(r["rq"]), (r["rq"], r["maps"]))
    if not visits:
        raise BridgeError("BLOCKED: no q visit reads the M2 block")
    for rq, maps in visits.values():
        check_map(rq, maps, m2)
    m2recs = [r for r in recs if r["rq"]["nm"] == M2_NM]
    for r in m2recs:
        check_record(r, m2)
    cands = [r for r in m2recs if eligible(r, m2)]
    if not cands:
        raise BridgeError("BLOCKED: no eligible mapped target")
    target = min(cands, key=lambda r: (r["ind"], r["indigp"], r["occ"]))
    return {"visits": sorted({rq["irq"] for rq, _ in visits.values()}),
            "n_visits": len(visits), "checked": len(m2recs),
            "eligible": len(cands), "target": target,
            "cert": certificate(target, m2)}


def summary(res):
    t, c = res["target"], res["cert"]
    rq = t["rq"]
    return {
        "q_visits_reading_M2_block": res["visits"],
        "records_checked": res["checked"], "eligible": res["eligible"],
        "target": {"occ": t["occ"], "irq": rq["irq"], "itran": rq["itran"],
                   "kg": rq["kg"], "rq": [str(x) for x in rq["rq"]],
                   "consumer_ig_igp": (t["ig"], t["igp"]),
                   "G": t["wp"]["g"], "Gp": t["wp"]["gp"],
                   "source_pair": c["src"],
                   "source_labels": (M2_LABELS(c["src"][0]), M2_LABELS(c["src"][1])),
                   "phases": [str(x) for x in c["ph"]], "map_kind": c["kind"],
                   "kappa": float(c["kappa"]), "band_in": t["col"]["in"]},
        "values": {k: float(c[k]) for k in
                   ("o_hat", "o_star", "i_hat", "i_star", "p_hat", "p_star")},
        "budgets": {k: float(c[k]) for k in
                    ("b_omega", "b_m2", "b_map", "b_form", "b_i", "b_div", "d", "b_p")},
        "errors": {"omega": float(abs(c["o_hat"] - c["o_star"])),
                   "ieps": float(abs(c["i_hat"] - c["i_star"])),
                   "div": float(abs(c["p_hat"] - c["o_hat"] / c["i_hat"])),
                   "wtilde2": float(abs(c["p_hat"] - c["p_star"]))},
    }


_LABELS = None


def M2_LABELS(k):
    global _LABELS
    if _LABELS is None:
        _LABELS = load_m2()["labels"]
    return _LABELS[k - 1]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    try:
        res = run()
    except BridgeError as e:
        print(f"FAIL: {e}")
        return 1
    s = summary(res)
    if a.json:
        print(json.dumps(s, indent=2))
    else:
        for k, v in s.items():
            print(f"{k}: {v}")
        print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

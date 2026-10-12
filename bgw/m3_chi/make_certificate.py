#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Emit and check GW/BGW/M3Chi.lean from the committed transition dump.

    python3 bgw/m3_chi/make_certificate.py --emit    # write the Lean module
    python3 bgw/m3_chi/make_certificate.py --check   # regenerate and compare

The module's two endpoint theorems are unconditional: every hypothesis of the
general lemmas in `GW/BGW/M3Transfer.lean` is discharged by kernel computation
over the pinned data.

Only the *operands* are generated literals. Everything the certificate claims
downstream of them -- the star products, the per-transition aggregates, the
denominator residuals, the sums -- is recomputed inside Lean and compared
against its witness, so a systematic mistake in this file makes Lean fail
rather than producing a certificate of the wrong thing.

Integer scaling throughout: a 1792-term `Int` fold does not reduce in the
kernel, while the `Nat` forms do.
"""

import argparse
import importlib.util
import math
import pathlib
import sys
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "GW" / "BGW" / "M3Chi.lean"
DUMP = ROOT / "bgw" / "m3_chi" / "data" / "m3_dump_q2.txt"
M2DUMP = ROOT / "bgw" / "m3_chi" / "data" / "m3_chi_q2.txt"
RUNID = "m3-20260919-q2-cut15"
IQ, N, NRK = 2, 8, 5

#: the two certified entries: one diagonal, one nontrivial off-diagonal.
TARGETS = ((1, 1), (1, 2))

#: Scale for the per-transition denominator error bound `eUp`. Chosen once,
#: large enough that rounding `eps` up loses nothing that matters; not tuned.
K_EPS = 200

#: float64 unit roundoff.
U = F(1, 2 ** 53)

#: Roundings charged per term of the production sum, and why.
#:
#:   w   = fl(sqrt(-edenHat))       1 rounding, but it enters SQUARED
#:   gr  = fl(g_i * w)              1
#:   gc  = fl(g_j * w)              1
#:   p   = fl(gr * gc)              1
#:
#: `w` is formed once and multiplied into BOTH weighted matrix elements, so
#: the product carries `(1+delta_w)^2`: the sqrt rounding counts twice, not
#: once. The R1 review raised exactly this. The previous M3 budget charged it
#: once and was therefore short by one unit.
#:
#: `eden`'s own rounding is NOT charged here. This budget bounds the distance
#: to the reconstruction that uses the code's own exported `eden`; the step
#: from there to the operand-implied denominator is the separately PROVED
#: transfer term, so charging it here as well would double count.
ROUNDINGS_PER_TERM = 5

#: one further rounding for the final multiply by `negfact`.
ROUNDINGS_FINAL = 1


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def dyadic_exp(fr):
    d = fr.denominator
    if d & (d - 1):
        raise ValueError(f"{fr} is not a dyadic rational")
    return d.bit_length() - 1


def scaled(fr, s):
    v = fr * (1 << s)
    if v.denominator != 1:
        raise ValueError(f"{fr} does not scale to an integer at 2^{s}")
    return v.numerator


def gamma(m):
    return (m * U) / (1 - m * U)


def build(dump=DUMP, chidump=M2DUMP):
    x3 = _load("m3x", "bgw/m3_chi/extract.py")
    x2 = _load("m2x", "bgw/m2_screening/extract.py")
    blk = x3.load_single(dump, RUNID, IQ, expected_n=N, expected_nrk=NRK)
    chi, _, _, _, _ = x2.matrices(
        x2.load_single(chidump, RUNID, IQ, expected_n=N, expected_q=(0.0, 0.0, 0.5)))

    keys = sorted(blk["gme"])
    s_gme = max(dyadic_exp(v) for row in blk["gme"].values() for v in row.values())
    s_eden = max(dyadic_exp(v) for v in blk["EDEN"].values())
    s_den = max(max(dyadic_exp(t[0]), dyadic_exp(t[1])) for t in blk["TRANS"].values())
    s_occ = max(max(dyadic_exp(t[2]), dyadic_exp(t[3])) for t in blk["TRANS"].values())
    fact = blk["scalars"]["FACT"]
    s_fact = dyadic_exp(fact)
    factZ = scaled(fact, s_fact)

    by_irk = {}
    for k in keys:
        by_irk.setdefault(k[0], []).append(k)

    kpts, rows_all, abs_terms = [], [], {t: F(0) for t in TARGETS}
    for irk in sorted(by_irk):
        stars = {}
        for (i, j) in TARGETS:
            stars[(i, j)] = []
            for it in range(1, blk["nst"][irk] + 1):
                ii, ph_i = blk["map"][(irk, it, i)]
                jj, ph_j = blk["map"][(irk, it, j)]
                stars[(i, j)].append((ii, int(ph_i), jj, int(ph_j)))
        trans = []
        for k in by_irk[irk]:
            ev, ec, ov, oc = blk["TRANS"][k]
            evZ, ecZ = scaled(ev, s_den), scaled(ec, s_den)
            ovZ, ocZ = scaled(ov, s_occ), scaled(oc, s_occ)
            dZ, oZ = evZ - ecZ, ovZ - ocZ
            ez = scaled(blk["EDEN"][k], s_eden)
            g = [scaled(blk["gme"][k][a], s_gme) for a in range(1, 9)]
            qw = {}
            for tgt in TARGETS:
                qw[tgt] = sum((pi * g[ii - 1]) * (pj * g[jj - 1])
                              for ii, pi, jj, pj in stars[tgt])
                # the absolute term sum is over every individual product,
                # not the per-transition aggregate: cancellation inside a
                # transition must not shrink the rounding allowance.
                abs_terms[tgt] += sum(
                    abs(F(ez) * (pi * g[ii - 1]) * (pj * g[jj - 1]))
                    for ii, pi, jj, pj in stars[tgt])
            resid = abs(ez * (dZ * 2 ** s_occ) - (oZ * 2 ** s_den) * (2 ** s_eden))
            den = (2 ** s_eden) * abs(dZ * 2 ** s_occ)
            eUp = -((-resid * 2 ** K_EPS) // den)      # ceiling division
            assert resid * 2 ** K_EPS <= eUp * den
            trans.append({"evZ": evZ, "ecZ": ecZ, "ovZ": ovZ, "ocZ": ocZ,
                          "ez": ez, "dZ": dZ, "oZ": oZ, "g": g,
                          "qw1": qw[TARGETS[0]], "qw2": qw[TARGETS[1]],
                          "resid": resid, "eUp": eUp})
            rows_all.append(trans[-1])
        kpts.append((stars[TARGETS[0]], stars[TARGETS[1]], trans))

    parts = []
    for idx, tgt in enumerate(TARGETS):
        qkey = "qw1" if idx == 0 else "qw2"
        pos = sum(max(r[qkey] * r["ez"], 0) for r in rows_all)
        neg = sum(max(-(r[qkey] * r["ez"]), 0) for r in rows_all)
        tnum = sum(abs(r[qkey]) * r["eUp"] for r in rows_all)
        ntot = sum(len(k[0 if idx == 0 else 1]) * len(k[2]) for k in kpts)
        m = ROUNDINGS_PER_TERM + (ntot - 1) + ROUNDINGS_FINAL
        # production rounding allowance, against the exported-eden reconstruction
        bound = abs(fact) * gamma(m) * abs_terms[tgt] / F(1 << (2 * s_gme + s_eden))
        transfer = abs(F(factZ)) * F(tnum, 1 << (s_fact + 2 * s_gme + K_EPS))
        recon = F(factZ, 1 << (s_fact + 2 * s_gme + s_eden)) * (pos - neg)
        parts.append({"i": tgt[0], "j": tgt[1], "idx": idx, "pos": pos,
                      "neg": neg, "tnum": tnum, "ntot": ntot, "m": m,
                      "bound": bound, "transfer": transfer,
                      "final": bound + transfer, "recon": recon,
                      "chi": chi[tgt[0] - 1][tgt[1] - 1]})
    return {"S": {"sGme": s_gme, "sEden": s_eden, "sDen": s_den, "sOcc": s_occ,
                  "kEps": K_EPS, "sFact": s_fact, "factZ": factZ},
            "kpts": kpts, "rows": rows_all, "parts": parts, "block": blk,
            "chi": chi}


def q(fr):
    return (f"({fr.numerator} : ℚ)" if fr.denominator == 1
            else f"(({fr.numerator} : ℚ) / {fr.denominator})")


HEADER = '''/-
BGW-M3-R1: entries (1,1) and (1,2) of one static-polarizability q block,
carried from the pinned physical operands to the production value.

GENERATED by `bgw/m3_chi/make_certificate.py --emit`; `--check` regenerates
and compares. The data literals are generated because there are thousands of
them. Everything claimed downstream of them is recomputed in Lean and checked
against its witness, so a systematic generator mistake makes this module fail
rather than certifying the wrong thing.

THE CHAIN, from the exported operands to the endpoint:

  kpts                  the pinned inventory: per k-point, the star map
                        (indt, pht) for basis indices 1 and 2, and every
                        transition's eval, econd, occ_v, occ_c, eden and its
                        eight UNWEIGHTED matrix elements
    | products_correct  qw1, qw2 are recomputed in Lean from the eight matrix
    v                   elements and the star map, and compared
  rows11 / rows12       built from `kpts` by `List.map`, not supplied
    | rows_ok           dZ = evZ - ecZ, oZ = ovZ - ocZ, the residual is the
    v                   one the operands imply, and eUp dominates it
  chiRecon              sum over transitions with the code's own eden
    | recon_eq          evaluated as one scaled integer sum
    v
  chiStar               THE SAME SUM with the operand-implied denominators
    | transfer_bound    `table_transfer`, discharged from `rows_ok`
    v
  entry11_endpoint      |chiHat - chiStar| <= finalBudget, unconditional
  entry12_endpoint

WHAT THE ENDPOINTS SAY. `chiStar` is the exact rational transition sum built
from the committed energies, occupations, unweighted matrix elements,
prefactor, phases and index map. The theorems bound the distance from it to
the actual exported production value.

WHAT THEY DO NOT SAY. `rowOK` proves a *bound* on the denominator error. It is
NOT a proof that `eden` is the correctly rounded quotient; correct IEEE
rounding is not formalized anywhere here. The separate empirical result --
that the exported `eden` matches `fl(occ_diff / fl(eval - econd))` on 280/280
transitions of this run -- is a Python check in `tests/test_bgw_m3.py`, for
this compiler and these operands only.

Also not established: the wavefunctions, the FFT, the plane-wave basis, the
occupations as physics, convergence, the frequency-dependent path, spinors,
the q -> 0 head and wing limits, the compiler, the BLAS, or BerkeleyGW as a
program. The production-rounding part of the budget is a standard
floating-point bound assuming correctly rounded IEEE-754 operations.
-/
import GW.BGW.M3Transfer

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace GW.BGW.M3

/-- The eight unweighted matrix elements of one transition, scaled. -/
abbrev G8 := Int × Int × Int × Int × Int × Int × Int × Int

/-- One star element for one target entry: `(indt_i, pht_i, indt_j, pht_j)`. -/
abbrev Star := Nat × Int × Nat × Int

/-- One transition, exactly as exported, plus the witnesses this module
checks against it. -/
structure TransRec where
  evZ : Int
  ecZ : Int
  ovZ : Int
  ocZ : Int
  ez : Int
  dZ : Int
  oZ : Int
  g : G8
  qw1 : Int
  qw2 : Int
  resid : Nat
  eUp : Nat

/-- Select a matrix element by its `indt` index. Out of range yields `0`, and
`starOK` separately requires every index to be in `1..8`. -/
def sel (g : G8) : Nat -> Int
  | 1 => g.1
  | 2 => g.2.1
  | 3 => g.2.2.1
  | 4 => g.2.2.2.1
  | 5 => g.2.2.2.2.1
  | 6 => g.2.2.2.2.2.1
  | 7 => g.2.2.2.2.2.2.1
  | 8 => g.2.2.2.2.2.2.2
  | _ => 0

/-- One star element's contribution, from the operands. -/
def starProd (g : G8) (s : Star) : Int :=
  (s.2.1 * sel g s.1) * (s.2.2.2 * sel g s.2.2.1)

/-- The star-summed product for one transition, computed from the operands. -/
def qOf (stars : List Star) (g : G8) : Int := (stars.map (starProd g)).sum

/-- Every index in range and every phase a sign. -/
def starOK (s : Star) : Bool :=
  (1 <= s.1) && (s.1 <= 8) && (1 <= s.2.2.1) && (s.2.2.1 <= 8) &&
  ((s.2.1 == 1) || (s.2.1 == -1)) && ((s.2.2.2 == 1) || (s.2.2.2 == -1))
'''


def emit(b):
    S = b["S"]
    out = [HEADER]
    out.append(f"""
/-- The scale exponents and prefactor of the pinned run. -/
def S : Scales :=
  {{ sGme := {S['sGme']}, sEden := {S['sEden']}, sDen := {S['sDen']},
    sOcc := {S['sOcc']}, kEps := {S['kEps']}, sFact := {S['sFact']},
    factZ := {S['factZ']} }}
""")

    def star_lit(sl):
        return "[" + ", ".join(f"({a}, {b_}, {c}, {d})" for a, b_, c, d in sl) + "]"

    def tr_lit(t):
        g = ", ".join(str(v) for v in t["g"])
        return ("{ evZ := %d, ecZ := %d, ovZ := %d, ocZ := %d, ez := %d, "
                "dZ := %d, oZ := %d, g := (%s), qw1 := %d, qw2 := %d, "
                "resid := %d, eUp := %d }" % (
                    t["evZ"], t["ecZ"], t["ovZ"], t["ocZ"], t["ez"], t["dZ"],
                    t["oZ"], g, t["qw1"], t["qw2"], t["resid"], t["eUp"]))

    blocks = ",\n  ".join(
        "(%s,\n   %s,\n   [%s])" % (star_lit(s1), star_lit(s2),
                                    ",\n    ".join(tr_lit(t) for t in tr))
        for s1, s2, tr in b["kpts"])
    out.append(f"""
/-- **The pinned inventory.** One entry per k-point: the star map for basis
index 1, the star map for basis index 2, and every transition of that
k-point. Nothing outside this table feeds the endpoint theorems. -/
def kpts : List (List Star × List Star × List TransRec) :=
  [{blocks}]

/-- Every transition, in the order the sums traverse them. -/
def allTrans : List TransRec := kpts.flatMap (fun kp => kp.2.2)

/-- Both star-summed products are the ones the matrix elements and the star
map imply, and every index and phase is well formed. -/
def qwOK : Bool :=
  kpts.all (fun kp =>
    kp.1.all starOK && kp.2.1.all starOK &&
    kp.2.2.all (fun t => (t.qw1 == qOf kp.1 t.g) && (t.qw2 == qOf kp.2.1 t.g)))

/-- **Operand to product.** Corrupting a generated `qw` witness, or the index
map, or a phase, fails here. -/
theorem products_correct : qwOK = true := by rfl

/-- A witness row carries the generator's checked product and difference
witnesses. These rows are used for the exported-`eden` reconstruction and
the denominator transfer. -/
def toWitnessRow (second : Bool) (t : TransRec) : Row :=
  {{ evZ := t.evZ, ecZ := t.ecZ, ovZ := t.ovZ, ocZ := t.ocZ, ez := t.ez,
    dZ := t.dZ, oZ := t.oZ, qw := if second then t.qw2 else t.qw1,
    resid := t.resid, eUp := t.eUp }}

def rows11 : List Row := allTrans.map (toWitnessRow false)
def rows12 : List Row := allTrans.map (toWitnessRow true)

/-- A raw-operand row recomputes the product and both differences directly
from the committed matrix elements, star map, energies and occupations.
No generated `qw`, `dZ`, or `oZ` witness enters these rows. -/
def toRawRow (stars : List Star) (t : TransRec) : Row :=
  {{ evZ := t.evZ, ecZ := t.ecZ, ovZ := t.ovZ, ocZ := t.ocZ, ez := t.ez,
    dZ := t.evZ - t.ecZ, oZ := t.ovZ - t.ocZ, qw := qOf stars t.g,
    resid := t.resid, eUp := t.eUp }}

def rawRows11 : List Row :=
  kpts.flatMap (fun kp => kp.2.2.map (toRawRow kp.1))
def rawRows12 : List Row :=
  kpts.flatMap (fun kp => kp.2.2.map (toRawRow kp.2.1))

/-- Concrete witness-to-operand correspondence. These equalities are kernel
computed for the pinned table; they are not hypotheses of the endpoints. -/
theorem rows11_eq_rawRows11 : rows11 = rawRows11 := by rfl
theorem rows12_eq_rawRows12 : rows12 = rawRows12 := by rfl

/-- **Operand to residual.** `dZ = evZ - ecZ`, `oZ = ovZ - ocZ`, the residual
is the one those operands imply, and `eUp` dominates it. Corrupting a residual
or bound witness fails here. -/
theorem rows_ok11 : rows11.all (rowOK S) = true := by rfl

theorem rows_ok12 : rows12.all (rowOK S) = true := by rfl

theorem transition_count : allTrans.length = {len(b['rows'])} := by rfl
""")

    for p in b["parts"]:
        t = f"{p['i']}{p['j']}"
        sec = "true" if p["idx"] == 1 else "false"
        out.append(f"""
/-! ### Entry ({p['i']},{p['j']}): {p['ntot']} (transition, star) contributions -/

def posSum{t} : ℕ := (rows{t}.map (fun r => (r.qw * r.ez).toNat)).sum
def negSum{t} : ℕ := (rows{t}.map (fun r => (-(r.qw * r.ez)).toNat)).sum
def transferNum{t} : ℕ := (rows{t}.map (fun r => r.qw.natAbs * r.eUp)).sum

theorem posSum{t}_eq : posSum{t} = {p['pos']} := by rfl
theorem negSum{t}_eq : negSum{t} = {p['neg']} := by rfl
theorem transferNum{t}_eq : transferNum{t} = {p['tnum']} := by rfl

/-- The reconstruction that uses the code's own exported denominators. -/
def chiRecon{t} : ℚ := (rows{t}.map (fun r => r.coefQ S * r.edenHatQ S)).sum

/-- **The operand-implied transition sum.** Same weights, but with each
denominator replaced by the exact `(occ_v - occ_c)/(eval - econd)` its own
exported operands give. -/
def chiStar{t} : ℚ := (rawRows{t}.map (fun r => r.coefQ S * r.dStarQ S)).sum

/-- The exported production value of entry ({p['i']},{p['j']}), exactly decoded. -/
def chiHat{t} : ℚ := {q(p['chi'])}

/-- Production rounding allowance: `|fact| * gamma_m * S_abs`, with
`m = {p['m']}` and `S_abs` the sum of absolute term magnitudes over all
{p['ntot']} products. `m` charges the sqrt rounding TWICE, because the single
rounded `sqrt(-eden)` multiplies both weighted matrix elements and therefore
enters each product squared. -/
def bound{t} : ℚ := {q(p['bound'])}

/-- Proved denominator-transfer allowance. -/
def transferBudget{t} : ℚ := {q(p['transfer'])}

def finalBudget{t} : ℚ := bound{t} + transferBudget{t}

theorem chiRecon{t}_eq : chiRecon{t} = {q(p['recon'])} := by
  rw [chiRecon{t}, recon_eval S rows{t}, int_sum_split,
      show (rows{t}.map (fun r => (r.qw * r.ez).toNat)).sum = posSum{t} from rfl,
      show (rows{t}.map (fun r => (-(r.qw * r.ez)).toNat)).sum = negSum{t} from rfl,
      posSum{t}_eq, negSum{t}_eq]
  norm_num [S]

theorem transferBudget{t}_eq :
    (rows{t}.map (fun r => |r.coefQ S| * r.epsQ S)).sum = transferBudget{t} := by
  rw [transfer_eval S rows{t},
      show (rows{t}.map (fun r => r.qw.natAbs * r.eUp)).sum = transferNum{t} from rfl,
      transferNum{t}_eq]
  norm_num [S, transferBudget{t}]

/-- Distance from the production value to the exported-denominator
reconstruction. -/
theorem entry{t}_within_budget : absQ (chiHat{t} - chiRecon{t}) ≤ bound{t} := by
  rw [chiRecon{t}_eq]
  norm_num [absQ, chiHat{t}, bound{t}]

/-- **The denominator transfer, discharged for this data.** -/
theorem transfer_bound{t} : absQ (chiRecon{t} - chiStar{t}) ≤ transferBudget{t} := by
  rw [← absQ_eq, ← transferBudget{t}_eq, chiStar{t}, ← rows{t}_eq_rawRows{t}]
  exact table_transfer S rows{t} rows_ok{t}

/-- **ENDPOINT ({p['i']},{p['j']}).** The exported production value lies within a
justified operand-derived budget of the complete transition sum rebuilt from
the committed energies, occupations, unweighted matrix elements, prefactor,
phases and index map. No hypotheses. -/
theorem entry{t}_endpoint : absQ (chiHat{t} - chiStar{t}) ≤ finalBudget{t} := by
  have h1 := entry{t}_within_budget
  have h2 := transfer_bound{t}
  rw [← absQ_eq] at *
  calc |chiHat{t} - chiStar{t}|
      = |(chiHat{t} - chiRecon{t}) + (chiRecon{t} - chiStar{t})| := by
        rw [sub_add_sub_cancel]
    _ ≤ |chiHat{t} - chiRecon{t}| + |chiRecon{t} - chiStar{t}| := abs_add _ _
    _ ≤ bound{t} + transferBudget{t} := add_le_add h1 h2
    _ = finalBudget{t} := rfl
""")
    out.append("\nend GW.BGW.M3\n")
    return "".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args(argv)
    text = emit(build())
    if a.emit:
        LEAN.write_text(text)
        print(f"wrote {LEAN} ({len(text)} bytes)")
        return 0
    if a.check:
        if not LEAN.exists():
            print(f"MISSING: {LEAN}", file=sys.stderr)
            return 1
        if LEAN.read_text() != text:
            print(f"MISMATCH: {LEAN.name} is not what this dump regenerates",
                  file=sys.stderr)
            return 1
        print(f"OK: {LEAN.name} matches regeneration from {DUMP.name}")
        return 0
    ap.error("choose --emit or --check")


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- BGW-M3: exact reconstruction of chi from its unweighted operands.

What the production code does, traced in the pinned source:

    mtxel.f90:918   eden  = occ_diff / (eval - econd)      (static, else 0)
    mtxel.f90:858   gme  *= sqrt(-1D0*eden)                the weighting
    mtxelmultiply.f90:64,95
                    negfact = -fact
                    chilocal = negfact * gmetempr . gmetempc^T
    mtxelmultiply.f90 chi_sum_prep
                    gmetempr(i,t) = gme(indt(i,it,irk),t) * pht(i,it,irk)
                    gmetempc(j,t) = conj( same with j )

so, writing w = sqrt(-eden) and noting w^2 = -eden EXACTLY as reals,

    chi(i,j) = -fact * sum_t (-eden_t) * G_t(i) * G_t(j)

with G_t(i) = gme_t(indt(i,it,irk)) * pht(i,it,irk). That right-hand side is
rational in the exported operands: the irrational w never appears. The
production value is the same expression evaluated in binary64, where w IS
formed and rounded. The gap between them is what `budget` bounds.

This file never reads the exported chi as an input to the reference.
"""

from fractions import Fraction as F

#: float64 unit roundoff.
U = F(1, 2 ** 53)

#: Roundings charged per term of the PRODUCTION sum, and why.
#:
#:   w  = fl(sqrt(-edenHat))     one rounding, but it enters SQUARED
#:   gr = fl(g_i * w)            one
#:   gc = fl(g_j * w)            one
#:   p  = fl(gr * gc)            one
#:
#: `w` is formed once and multiplied into BOTH weighted matrix elements, so
#: each product carries `(1 + delta_w)^2`: the sqrt rounding counts twice.
#: BGW-M3-R1 review raised exactly this; the original M3 budget charged it
#: once and was short by one unit.
#:
#: `eden`'s own rounding is NOT charged here. `production_bound` measures the
#: distance to the reconstruction that uses the code's own exported `eden`.
#: The step from there to the operand-implied denominator is `transfer_bound`,
#: which is PROVED rather than estimated, so charging it twice would double
#: count.
ROUNDINGS_PER_TERM = 5

#: one further rounding for the final multiply by `negfact`.
ROUNDINGS_FINAL = 1

#: Scale of the per-transition denominator error bound. Matches
#: `make_certificate.K_EPS`; chosen once, not tuned.
K_EPS = 200


def gamma(m):
    """The standard `m*u/(1-m*u)` constant for `m` dependent roundings."""
    return (m * U) / (1 - m * U)


def eden_exact(block, key):
    """The energy denominator as its four operands imply it, EXACTLY.

    mtxel.f90:918, static branch:

        if (eval - econd < TOL_Degeneracy .and. occ_diff > TOL_Zero) then
          eden = occ_diff / (eval - econd)
        else
          eden = 0d0

    `TOL_Degeneracy` and `TOL_Zero` are the code's tolerances; this run has no
    transition near either, which `tolerance_margin` reports. Where the
    branches could differ the reconstruction would be wrong, so the margin is
    evidence, not decoration.
    """
    eval_, econd, occ_v, occ_c = block["TRANS"][key]
    occ_diff = occ_v - occ_c
    if eval_ - econd < 0 and occ_diff > 0:
        return occ_diff / (eval_ - econd)
    return F(0)


def tolerance_margin(block):
    """How far this run's transitions sit from the two branch tolerances.

    A transition within a tolerance of a branch boundary would make the
    reconstruction's branch choice a guess. Returned so that closeness is
    reported rather than assumed away.
    """
    de, docc = [], []
    for key, (eval_, econd, occ_v, occ_c) in block["TRANS"].items():
        de.append(abs(eval_ - econd))
        docc.append(abs(occ_v - occ_c))
    return {"min_abs_energy_gap": min(de), "min_abs_occ_diff": min(docc)}


def star_count(block):
    """Total columns the GEMM summed: sum over irk of nst(irk) * transitions."""
    per_irk = {}
    for (irk, ispin, iv, ic) in block["EDEN"]:
        per_irk[irk] = per_irk.get(irk, 0) + 1
    return sum(block["nst"][irk] * cnt for irk, cnt in per_irk.items())


def terms(block, i, j):
    """Every exact term of chi(i,j)'s sum, before the -fact multiply.

    Returned as a list so the inventory is inspectable: a reconstruction that
    silently dropped transitions would show up here as a shorter list.
    """
    out = []
    for key, row in sorted(block["gme"].items()):
        irk = key[0]
        eden = eden_exact(block, key)
        for it in range(1, block["nst"][irk] + 1):
            ind_i, ph_i = block["map"][(irk, it, i)]
            ind_j, ph_j = block["map"][(irk, it, j)]
            out.append((-eden) * (row[ind_i] * ph_i) * (row[ind_j] * ph_j))
    return out


def exact_entry(block, i, j):
    """chi(i,j) reconstructed exactly from the unweighted operands."""
    fact = block["scalars"]["FACT"]
    return -fact * sum(terms(block, i, j), F(0))


def exact_matrix(block):
    n = block["n"]
    return [[exact_entry(block, i, j) for j in range(1, n + 1)]
            for i in range(1, n + 1)]


def hat_terms(block, i, j):
    """The terms as the production path formed them: the code's own `eden`.

    `terms` uses the operand-implied denominator, which is what `chi_star`
    reconstructs. These are what the PRODUCTION rounding bound is measured
    against, so the two must not be confused.
    """
    out = []
    for key, row in sorted(block["gme"].items()):
        irk = key[0]
        eden = block["EDEN"][key]
        for it in range(1, block["nst"][irk] + 1):
            ind_i, ph_i = block["map"][(irk, it, i)]
            ind_j, ph_j = block["map"][(irk, it, j)]
            out.append((-eden) * (row[ind_i] * ph_i) * (row[ind_j] * ph_j))
    return out


def production_bound(block, i, j):
    """Distance from the production value to the EXPORTED-eden reconstruction.

    Standard floating-point bound: `|fact| * gamma_m * S_abs`, with
    `m = ROUNDINGS_PER_TERM + (ntot - 1) + ROUNDINGS_FINAL` and `S_abs` the
    sum of absolute term magnitudes over every individual product -- not over
    the per-transition aggregates, because cancellation inside a transition
    must not shrink the allowance.

    A numerical-analysis bound assuming correctly rounded IEEE-754
    operations. Not a statement about gfortran, the BLAS, or the order the
    GEMM accumulates in.
    """
    tms = hat_terms(block, i, j)
    m = ROUNDINGS_PER_TERM + (len(tms) - 1) + ROUNDINGS_FINAL
    fact = block["scalars"]["FACT"]
    return abs(fact) * gamma(m) * sum((abs(t) for t in tms), F(0))


def transfer_bound(block, i, j):
    """Allowance for replacing each exported `eden` by its operands' quotient.

    `sum |a_t| * |edenHat_t - dStar_t|`, summed per transition. This is the
    quantity `GW/BGW/M3Chi.lean` PROVES a bound on for entries (1,1) and
    (1,2); here it is computed exactly for all 64.
    """
    fact = block["scalars"]["FACT"]
    total = F(0)
    for key, row in sorted(block["gme"].items()):
        irk = key[0]
        qw = F(0)
        for it in range(1, block["nst"][irk] + 1):
            ind_i, ph_i = block["map"][(irk, it, i)]
            ind_j, ph_j = block["map"][(irk, it, j)]
            qw += (row[ind_i] * ph_i) * (row[ind_j] * ph_j)
        total += abs(fact * qw) * abs(block["EDEN"][key] - eden_exact(block, key))
    return total


def budget(block, i, j):
    """The full operand-level budget: production rounding plus the transfer."""
    return production_bound(block, i, j) + transfer_bound(block, i, j)


def budget_matrix(block):
    n = block["n"]
    return [[budget(block, i, j) for j in range(1, n + 1)]
            for i in range(1, n + 1)]


def inventory(block):
    """Complete transition inventory, including the ones the code skipped.

    `get_eden` sets eden = 0 when the transition is forbidden (equal
    occupations, or a non-negative energy difference); those contribute
    nothing but must still be accounted for, or a reconstruction could match
    by dropping exactly the terms it got wrong.
    """
    kept, skipped = [], []
    for key in sorted(block["EDEN"]):
        (skipped if block["EDEN"][key] == 0 else kept).append(key)
    return {"kept": kept, "skipped": skipped,
            "transitions": len(kept) + len(skipped),
            "columns": star_count(block)}


def occupation_check(block):
    """The exported `eden` must be the CORRECTLY ROUNDED quotient of its own
    four operands.

    Two roundings, in the order the compiled code performs them: the
    subtraction `eval - econd`, then the division. Requiring a single rounding
    of the exactly-subtracted quotient fails on 69 of this run's 280
    transitions; the two-rounding model matches all 280. The reference itself
    uses `eden_exact` and never reads this field -- this is a correspondence
    check on the export, not an input.
    """
    bad = []
    for key in sorted(block["TRANS"]):
        eval_, econd, occ_v, occ_c = block["TRANS"][key]
        occ_diff = occ_v - occ_c
        if eval_ - econd < 0 and occ_diff > 0:
            want = F(float(occ_diff / F(float(eval_) - float(econd))))
        else:
            want = F(0)
        if block["EDEN"][key] != want:
            bad.append((key, float(block["EDEN"][key]), float(want)))
    return bad

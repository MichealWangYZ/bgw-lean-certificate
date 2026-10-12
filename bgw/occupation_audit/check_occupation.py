#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- T-003 checker: near-pole GPP records whose occupation is not one.

Repaired under T-003-R1 after review findings F1 and F2
(`.agent/handoffs/CODEX-T-003-REVIEW.md`). The pre-repair version gated only on
the `ssx_post` residual and left 12 of the 29 exported fields parsed but never
read, so corrupted records and a negative event tally still exited 0.

Input is the record file written by the T-003 instrumentation patch
(`t003_instrument.patch`) from a real BerkeleyGW 4.0 run.

## Three kinds of check, deliberately kept apart

1. **Exact algebra.** Over the rationals: the branch the complete predicate
   selects, and the two occupied expressions of `GW.GPP.BGW4` at the record's
   own `occ`, compared via the closed form of `GW.GPP.BGW4.branch_mismatch`,
   used unchanged. No tolerance applies; these are identities.

2. **Rounded derived intermediates.** Fields the Fortran *computed* from other
   recorded fields (`wtilde2`, `omega2`, `delw`, `delwr`, `wdiffr`, the three
   denominators, `ssx_pre`, `ssx_post`). These carry binary64 rounding from the
   source's own operation order, so they get measured residual thresholds, NOT
   exact-real equality. Thresholds and the observed maxima that justify them
   are in `RESIDUAL_LIMITS`; see `REPORT.md` section 7.

3. **Exactly-determined fields.** Fields that are literals, parameters, or
   integer-valued in the source (`sch` in branch 2, `limittwo`, `limitone`,
   `wtilde_im`, `occ`, the clamp decision). Exact equality is correct for these
   and no tolerance is used.

Fields with no internal relation available in a record are listed in
`UNMODELED_FIELDS` and are reported as unverified rather than claimed checked.

## Modes

Default is **full-fixture validation**: exactly `--expect-records` records, ids
forming `1..N`, no duplicates. `--subset` performs explicitly labelled subset
analysis, which can establish existence but is NOT validation of the saved
export; the output carries `full_fixture_validated: false`.
"""

from fractions import Fraction as F
import argparse
import json
import math
import pathlib
import sys

# --- constants traced to the pinned source -----------------------------------
# Common/nrtype.f90:161-162, 155
TOL_ZERO = F(1, 10**12)
TOL_SMALL = F(1, 10**6)
RYD = 13.60569253
# Sigma/inread.f90:130 then :501 -- sig%tol = TOL_Degeneracy * RYD, in eV
SIG_TOL = 1.0e-6 * RYD
# Sigma/inread.f90:151-152
SIG_GAMMA = 0.5
SIG_SEXCUT = F(4)
# Sigma/inread.f90:149 -- finite_difference_spacing is absent from the probe
# input, so sig%dw keeps its default. This is an assumption about the input,
# and it is checked below against the recorded (iw, wxt, e_lk, e_n1kq).
SIG_DW = 1.0
# mtxel_cor.f90:1698-1699. Both are exact in binary64 and are checked as such.
LIMITTWO = 0.25
LIMITONE = 250000.0

EXPECTED_RECORDS = 48

FIELDS = (
    "rec n1true iw igp ig branch "
    "occ vcoul ieps wtilde_re wtilde_im wtilde2 wxt omega2 delw delwr wdiffr "
    "limittwo limitone ssx_pre ssx_post sch den_generic den_nearpole "
    "den_merged e_lk e_n1kq efermi occ_broadening"
).split()
N_INT = 6

#: Relative-residual limits for rounded derived intermediates, with the maximum
#: actually observed on the 48 archived records. Observed maxima are NOT proved
#: universal error bounds; the limits carry deliberate headroom so the checker
#: is not a hair trigger, while still rejecting corruption by many orders of
#: magnitude. `den_generic` is special: `wxt**2 - wtilde2` is a difference of
#: nearly equal quantities near the pole, so a plain relative residual reaches
#: 4.1e-13 by cancellation alone. It is therefore bounded relative to the
#: magnitude of its operands, `wxt**2 + wtilde2`, where the residual is 6.8e-17.
RESIDUAL_LIMITS = {
    "wtilde2":      dict(limit=1e-14, observed=9.361e-17, kind="relative"),
    "omega2":       dict(limit=1e-14, observed=1.774e-16, kind="relative"),
    "delw":         dict(limit=1e-14, observed=2.074e-16, kind="relative"),
    "delwr":        dict(limit=1e-14, observed=4.469e-16, kind="relative"),
    "wdiffr":       dict(limit=1e-14, observed=8.427e-17, kind="relative"),
    "den_nearpole": dict(limit=1e-14, observed=3.071e-16, kind="relative"),
    "den_merged":   dict(limit=1e-14, observed=1.598e-16, kind="relative"),
    "den_generic":  dict(limit=1e-14, observed=6.813e-17,
                         kind="scaled by wxt**2 + wtilde2 (cancellation)"),
    "ssx_pre":      dict(limit=1e-14, observed=2.743e-16, kind="relative"),
}
#: Absolute limit on `wxt` against `e_lk + sig%dw*(iw-2) - e_n1kq`.
WXT_LIMIT = dict(limit=1e-12, observed=4.441e-16, kind="absolute")
#: The pre-repair exit gate on `ssx_post` against its exact rational value.
#: Deliberately unchanged, as required by T-003-R1 item 1.
SSX_POST_LIMIT = dict(limit=1e-10, observed=4.2435598287864196e-19,
                      kind="absolute")

#: No relation internal to a record constrains these, so they are reported as
#: recorded and explicitly NOT claimed verified.
UNMODELED_FIELDS = {
    "vcoul": "Coulomb factor; no internal relation in the record",
    "ieps": "only constrained indirectly, through the omega2 residual",
    "e_lk": "only its difference with e_n1kq is constrained, through wxt",
    "n1true": "band index; only record-id integrity is checked",
    "igp": "reciprocal-lattice index; not cross-checkable here",
    "ig": "reciprocal-lattice index; not cross-checkable here",
    "occ_broadening": (
        "STORED DEFAULT, not evidence of smearing. Sigma/inread.f90:135 writes "
        "`sig%occ_broadening=0.1` with no kind suffix, so the default is the "
        "float32 image 0.10000000149011612. sig%do_smearing is a separate flag "
        "and is not exported; a nonzero value here does NOT mean smearing is on."
    ),
}


class RecordError(ValueError):
    """A record, tally, or fixture violates its contract."""


# --- parsing -----------------------------------------------------------------

def parse(text):
    """Parse the record file. Rejects wrong arity and nonfinite fields."""
    rows = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        if len(parts) != len(FIELDS):
            raise RecordError(
                f"line {lineno}: expected {len(FIELDS)} fields, got {len(parts)}"
                " (a short line usually means Fortran format reversion)"
            )
        r = {}
        for i, (name, tok) in enumerate(zip(FIELDS, parts)):
            if i < N_INT:
                r[name] = int(tok)
            else:
                v = float(tok)
                if not math.isfinite(v):
                    raise RecordError(f"line {lineno}: field {name} is {tok}, not finite")
                r[name] = v
        r["_line"] = lineno
        rows.append(r)
    if not rows:
        raise RecordError("no records found; refusing to report a vacuous pass")
    return rows


def check_record_integrity(rows, expect_records, subset):
    """Record-id and duplicate contract (finding F2)."""
    ids = [r["rec"] for r in rows]
    if any(i < 1 for i in ids):
        raise RecordError(f"record ids must be >= 1; got {sorted(ids)[:5]}")
    dupes = sorted({i for i in ids if ids.count(i) > 1})
    if dupes:
        raise RecordError(
            f"duplicate record ids {dupes}; a repeated record is not extra coverage"
        )
    signatures = [tuple(r[f] for f in FIELDS) for r in rows]
    if len(set(signatures)) != len(signatures):
        raise RecordError("duplicate record content; identical rows are not coverage")
    if subset:
        return dict(mode="subset", full_fixture_validated=False,
                    note="subset analysis can establish existence only; "
                         "this is NOT validation of the saved export")
    if len(rows) != expect_records:
        raise RecordError(
            f"full-fixture validation expects exactly {expect_records} records, "
            f"got {len(rows)}; pass --subset for explicitly labelled "
            f"subset analysis"
        )
    if sorted(ids) != list(range(1, expect_records + 1)):
        raise RecordError(
            f"record ids must be exactly 1..{expect_records}; got "
            f"{sorted(ids)[:5]}...{sorted(ids)[-3:]}"
        )
    return dict(mode="full-fixture", full_fixture_validated=True)


# --- the source's branch predicate -------------------------------------------

def classify(x, wt, limittwo, limitone):
    """The complete branch predicate of Sigma/mtxel_cor.f90:1828-1843.

    Evaluated over exact rationals from the recorded (rounded) inputs. The
    Fortran compared its OWN binary64 `wdiffr`/`delwr`; the two can in
    principle disagree for a record sitting on a threshold. `analyse` therefore
    also classifies using the recorded `wdiffr`/`delwr` and reports whether the
    two routes agree.
    """
    wdiff = x - wt
    wdiffr = wdiff * wdiff
    if wdiff == 0:
        return None, wdiffr, None
    delw = wt / wdiff
    delwr = delw * delw
    if wdiffr > limittwo and delwr < limitone:
        return 1, wdiffr, delwr
    if delwr > TOL_ZERO:
        return 2, wdiffr, delwr
    return 3, wdiffr, delwr


def _branch_from_recorded(r):
    """Branch implied by the Fortran's own recorded wdiffr/delwr."""
    if r["wdiffr"] > r["limittwo"] and r["delwr"] < r["limitone"]:
        return 1
    if F(r["delwr"]) > TOL_ZERO:
        return 2
    return 3


# --- per-record analysis -----------------------------------------------------

def _residual(name, recorded, exact, scale=None):
    """Relative (or scale-relative) residual plus its pass/fail verdict."""
    spec = RESIDUAL_LIMITS[name]
    denom = abs(float(scale if scale is not None else exact))
    if denom == 0:
        resid = abs(float(F(recorded) - exact))
    else:
        resid = abs(float(F(recorded) - exact)) / denom
    if resid > spec["limit"]:
        raise RecordError(
            f"field {name}: residual {resid:.3e} exceeds limit {spec['limit']:.0e} "
            f"(observed max on archived records: {spec['observed']:.3e})"
        )
    return resid


def analyse(r):
    occ = F(r["occ"])
    ieps = F(r["ieps"])
    wt = F(r["wtilde_re"])
    x = F(r["wxt"])
    line = r["_line"]

    # ---- exactly-determined fields ----
    if r["limittwo"] != LIMITTWO:
        raise RecordError(f"line {line}: limittwo {r['limittwo']!r} != {LIMITTWO!r} "
                          f"(sig%gamma**2, gamma default {SIG_GAMMA})")
    if r["limitone"] != LIMITONE:
        raise RecordError(f"line {line}: limitone {r['limitone']!r} != {LIMITONE!r}")
    if r["wtilde_im"] != 0.0:
        raise RecordError(f"line {line}: wtilde has nonzero imaginary part "
                          f"{r['wtilde_im']}; outside the mapped real-mode scope")
    if r["wtilde_re"] <= 0.0:
        raise RecordError(f"line {line}: wtilde_re {r['wtilde_re']} is not a "
                          f"positive real mode")
    if r["branch"] != 2:
        raise RecordError(f"line {line}: exported branch {r['branch']} != 2")
    # Branch 2 assigns the literal `sch = 0.0d0` (mtxel_cor.f90:1835): exact.
    if r["sch"] != 0.0:
        raise RecordError(f"line {line}: branch 2 requires sch == 0 exactly, "
                          f"got {r['sch']!r}")
    # Smearing cannot reach the GPP path (inread.f90:528-532), so occ comes from
    # mtxel_cor.f90:1399-1403 and is exactly 0.5 or 1.0.
    if r["occ"] not in (0.5, 1.0):
        raise RecordError(f"line {line}: occ {r['occ']!r} is neither 0.5 nor 1.0; "
                          f"smearing is excluded from the GPP path in this revision")
    if occ == 1:
        raise RecordError(f"line {line}: occ == 1; this file is for occ != 1")
    # occ == 0.5 requires abs(e_n1kq - efermi) < sig%tol (mtxel_cor.f90:1399).
    fermi_gap = abs(r["e_n1kq"] - r["efermi"])
    if not fermi_gap < SIG_TOL:
        raise RecordError(
            f"line {line}: occ == 0.5 claims Fermi-level half occupation, but "
            f"abs(e_n1kq - efermi) = {fermi_gap:.6e} is not below "
            f"sig%tol = {SIG_TOL:.6e} eV"
        )

    # ---- branch, exactly and as the source decided it ----
    branch, wdiffr_exact, delwr_exact = classify(x, wt, F(r["limittwo"]),
                                                 F(r["limitone"]))
    if branch != 2:
        raise RecordError(f"line {line}: recomputed branch {branch}, expected 2")
    branch_recorded = _branch_from_recorded(r)
    if branch_recorded != 2:
        raise RecordError(
            f"line {line}: the recorded wdiffr/delwr imply branch "
            f"{branch_recorded}, not 2"
        )

    # ---- rounded derived intermediates ----
    wt2 = wt**2
    omega2 = wt2 * ieps
    wdiff = x - wt
    delw = wt / wdiff
    den_generic = x**2 - wt2
    den_merged = 2 * wt * (x + wt)
    den_nearpole = 4 * wt2 * (delw + F(1, 2))
    ssx_exact = -omega2 * delw / den_nearpole

    for name, d in (("den_merged", den_merged), ("den_nearpole", den_nearpole)):
        if d == 0:
            raise RecordError(f"line {line}: recomputed {name} vanishes")
        if r[name] == 0.0:
            raise RecordError(f"line {line}: exported {name} is zero")

    resid = {
        "wtilde2": _residual("wtilde2", r["wtilde2"], wt2),
        "omega2": _residual("omega2", r["omega2"], omega2),
        "delw": _residual("delw", r["delw"], delw),
        "delwr": _residual("delwr", r["delwr"], delwr_exact),
        "wdiffr": _residual("wdiffr", r["wdiffr"], wdiffr_exact),
        "den_generic": _residual("den_generic", r["den_generic"], den_generic,
                                 scale=x**2 + wt2),
        "den_nearpole": _residual("den_nearpole", r["den_nearpole"], den_nearpole),
        "den_merged": _residual("den_merged", r["den_merged"], den_merged),
        "ssx_pre": _residual("ssx_pre", r["ssx_pre"], ssx_exact),
    }

    # wxt against the energies it is built from (mtxel_cor.f90:1743-1746).
    wxt_pred = F(r["e_lk"]) + F(r["iw"] - 2) * F(SIG_DW) - F(r["e_n1kq"])
    wxt_resid = abs(float(x - wxt_pred))
    if wxt_resid > WXT_LIMIT["limit"]:
        raise RecordError(
            f"line {line}: wxt {r['wxt']!r} disagrees with "
            f"e_lk + {SIG_DW}*(iw-2) - e_n1kq by {wxt_resid:.3e}, "
            f"limit {WXT_LIMIT['limit']:.0e}"
        )

    # ---- the sexcut clamp decision (mtxel_cor.f90:1847-1848): exact ----
    clamp_should_fire = (abs(F(r["ssx_pre"])) > SIG_SEXCUT * abs(ieps)) and x < 0
    if clamp_should_fire:
        if r["ssx_post"] != 0.0:
            raise RecordError(f"line {line}: sexcut clamp must fire "
                              f"(|ssx_pre| > sexcut*|ieps| and wxt < 0) but "
                              f"ssx_post = {r['ssx_post']!r} is not zero")
    elif r["ssx_post"] != r["ssx_pre"]:
        raise RecordError(
            f"line {line}: sexcut clamp must NOT fire, so ssx_post must equal "
            f"ssx_pre; got {r['ssx_post']!r} vs {r['ssx_pre']!r}"
        )

    fp_residual = abs(F(r["ssx_post"]) - ssx_exact)
    if fp_residual > F(SSX_POST_LIMIT["limit"]):
        raise RecordError(f"line {line}: ssx_post residual {float(fp_residual):.3e} "
                          f"exceeds {SSX_POST_LIMIT['limit']:.0e}")

    # ---- exact algebra: the two BGW4 expressions at this record's occ ----
    ssx_generic = omega2 / den_generic if den_generic != 0 else None
    sch_generic = delw * ieps
    generic_occ = (-occ * ssx_generic + F(1, 2) * sch_generic
                   if ssx_generic is not None else None)
    nearpole_occ = -occ * ssx_exact
    mismatch_closed = (1 - occ) * (omega2 / den_merged
                                   + omega2 / ((x - wt) * (x + wt)))
    mismatch_direct = (generic_occ - nearpole_occ
                       if generic_occ is not None else None)
    if mismatch_direct != mismatch_closed:
        raise RecordError(f"line {line}: branch_mismatch closed form disagrees "
                          f"with the direct difference")

    local_code_value = -occ * F(r["ssx_post"]) + F(1, 2) * F(r["sch"])
    rel = (abs(mismatch_closed / local_code_value)
           if local_code_value != 0 else None)

    return dict(
        rec=r["rec"], n1true=r["n1true"], iw=r["iw"], igp=r["igp"], ig=r["ig"],
        occ=r["occ"], wtilde=r["wtilde_re"], wxt=r["wxt"],
        omega2=float(omega2), ieps=r["ieps"], vcoul=r["vcoul"],
        branch_recomputed=branch, branch_from_recorded_intermediates=branch_recorded,
        wdiffr=float(wdiffr_exact), delwr=float(delwr_exact),
        generic_test_failed_because=("wdiffr <= limittwo"
                                     if wdiffr_exact <= F(r["limittwo"])
                                     else "delwr >= limitone"),
        fermi_gap=fermi_gap,
        sexcut_clamp_fired=(r["ssx_pre"] != r["ssx_post"]),
        sexcut_clamp_should_fire=clamp_should_fire,
        intermediate_residuals=resid,
        wxt_residual=wxt_resid,
        fp_residual=float(fp_residual),
        local_code_value=float(local_code_value),
        mismatch_exact=float(mismatch_closed),
        mismatch_closed_equals_direct=True,
        mismatch_over_local_value=None if rel is None else float(rel),
        vcoul_weighted_mismatch=float(mismatch_closed * F(r["vcoul"])),
    )


# --- tallies -----------------------------------------------------------------

TALLY_ROWS = ("branch1", "branch2", "branch3", "sexcut")


def check_counts(text, label="tally"):
    """Parse and validate a branch x occupation tally file (finding F2)."""
    out = {}
    for line in text.splitlines():
        if line.lstrip().startswith("#") or not line.strip():
            continue
        parts = line.split()
        if len(parts) != 3:
            raise RecordError(f"{label}: malformed line {line!r}")
        key = parts[0]
        if key not in TALLY_ROWS:
            raise RecordError(f"{label}: unknown row {key!r}; "
                              f"expected one of {TALLY_ROWS}")
        if key in out:
            raise RecordError(f"{label}: duplicate row {key!r}")
        try:
            a, b = int(parts[1]), int(parts[2])
        except ValueError:
            raise RecordError(f"{label}: non-integer counts in {line!r}")
        if a < 0 or b < 0:
            raise RecordError(f"{label}: negative count in {line!r}; "
                              f"event counts must be nonnegative")
        out[key] = (a, b)
    missing = [k for k in TALLY_ROWS if k not in out]
    if missing:
        raise RecordError(f"{label}: missing rows {missing}")
    branch_total = sum(sum(out[k]) for k in ("branch1", "branch2", "branch3"))
    for col, name in ((0, "occ==1"), (1, "occ!=1")):
        if out["sexcut"][col] > sum(out[k][col] for k in
                                    ("branch1", "branch2", "branch3")):
            raise RecordError(f"{label}: sexcut count in the {name} column "
                              f"exceeds the total number of evaluations")
    if branch_total == 0:
        raise RecordError(f"{label}: no evaluations recorded")
    return out


def check_tally_pair(probe, control):
    """Control contract and cross-count invariants (finding F2)."""
    for key in TALLY_ROWS:
        if control[key][1] != 0:
            raise RecordError(
                f"control reports {control[key][1]} occ != 1 events in {key}; "
                f"the control is required to be occ == 1 throughout"
            )
    if probe["branch2"][1] == 0:
        raise RecordError("probe reports no occ != 1 near-pole events")
    # The manual Fermi level changes only the occ classification, not which
    # (ig,igp,n1,iw) evaluations happen: flag_occ still admits bands 1..4
    # because nvband = 4 and ncrit = 0 in both runs. So each row's column sum
    # must be invariant between control and probe. This also catches a tampered
    # count that happens to stay nonnegative.
    for key in TALLY_ROWS:
        if sum(probe[key]) != sum(control[key]):
            raise RecordError(
                f"row {key}: probe column sum {sum(probe[key])} != control "
                f"{sum(control[key])}; the two runs must cover the same "
                f"evaluations, so a differing sum means a tampered or "
                f"mismatched tally"
            )
    return dict(
        qualifying_events=probe["branch2"][1],
        evaluations_per_row_invariant=True,
        total_evaluations=sum(sum(control[k]) for k in
                              ("branch1", "branch2", "branch3")),
    )


# --- entry point -------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser()
    here = pathlib.Path(__file__).parent
    ap.add_argument("records", nargs="?",
                    default=here / "fixtures" / "t003_nearpole_occ.dat")
    ap.add_argument("--counts", default=here / "fixtures" / "fermi_branch_occ_counts.dat")
    ap.add_argument("--control-counts",
                    default=here / "fixtures" / "control_branch_occ_counts.dat")
    ap.add_argument("--expect-records", type=int, default=EXPECTED_RECORDS,
                    help="record count required by full-fixture validation")
    ap.add_argument("--subset", action="store_true",
                    help="explicitly labelled subset analysis; establishes "
                         "existence only, does NOT validate the saved export")
    args = ap.parse_args(argv)

    rows = parse(pathlib.Path(args.records).read_text())
    coverage = check_record_integrity(rows, args.expect_records, args.subset)
    results = [analyse(r) for r in rows]

    counts = check_counts(pathlib.Path(args.counts).read_text(), "probe tally")
    control = check_counts(pathlib.Path(args.control_counts).read_text(),
                           "control tally")
    tally = check_tally_pair(counts, control)

    worst_int = {name: max(x["intermediate_residuals"][name] for x in results)
                 for name in RESIDUAL_LIMITS}
    summary = dict(
        source="BerkeleyGW 4.0 Si-EPM GPP, fermi_level_absolute probe; "
               "see bgw/occupation_audit/REPORT.md",
        coverage=coverage,
        records=len(results),
        exported_records_vs_counted_events=dict(
            exported_records=len(results),
            counted_qualifying_events=tally["qualifying_events"],
            note="the records are the first N qualifying evaluations "
                 "encountered, not a random sample of the counted events",
        ),
        all_branch2=all(x["branch_recomputed"] == 2 for x in results),
        exact_and_recorded_branch_agree=all(
            x["branch_recomputed"] == x["branch_from_recorded_intermediates"]
            for x in results),
        all_sch_zero=True,
        any_sexcut_clamped=any(x["sexcut_clamp_fired"] for x in results),
        distinct_occ=sorted({x["occ"] for x in results}),
        max_fermi_gap=max(x["fermi_gap"] for x in results),
        max_fp_residual=max(x["fp_residual"] for x in results),
        max_wxt_residual=max(x["wxt_residual"] for x in results),
        max_intermediate_residuals=worst_int,
        residual_limits=RESIDUAL_LIMITS,
        ssx_post_limit=SSX_POST_LIMIT,
        wxt_limit=WXT_LIMIT,
        unmodeled_fields=UNMODELED_FIELDS,
        max_abs_mismatch_exact=max(abs(x["mismatch_exact"]) for x in results),
        max_mismatch_over_local_value=max(
            x["mismatch_over_local_value"] for x in results
            if x["mismatch_over_local_value"] is not None),
        probe_counts=counts,
        control_counts=control,
        tally_invariants=tally,
        rows=results,
    )
    json.dump(summary, sys.stdout, indent=2)
    print()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RecordError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)

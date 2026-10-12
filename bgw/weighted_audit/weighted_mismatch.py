#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- T-004: partially weighted branch-mismatch sum over all 3702 witness events.

Question answered: for the SAME manually shifted, charge-inconsistent Si-EPM
probe of T-003, how large is the exact-real branch mismatch after
multiplication by the recorded wavefunction matrix elements and Coulomb
factor, including cancellation?

## What is computed

For each exported near-pole `occ != 1` evaluation, over exact rationals from
that record's own binary64 fields:

    weight   K = aqsntemp(ig,n1) * MYCONJG(aqsmtemp(igp,n1)) * vcoul(igp)
    mismatch m = GW.GPP.BGW4.branch_mismatch, used unchanged, i.e.
                 (1-occ) * ( Omega2/(2*w*(x+w)) + Omega2/((x-w)*(x+w)) )
    local    L = -occ*ssx_post + sch/2      (what the source accumulates)

and reports, per accumulator group, `sum(K*m)` with signs, `sum(|K*m|)`,
`max|K*m|`, and `sum(K*L)` as the reference.

Real flavor (`flavor_real.mk`): `aqsntemp`/`aqsmtemp` are `real(DP)` and
`MYCONJG` is the identity, so no conjugation is applied. A record with a
nonzero imaginary pole component is rejected rather than approximated.

## Grouping

One `mtxel_cor` call is identified by `(icalc, band_in, il, iband, ispin, qk)`
and accumulates into `asxtemp(iw)`/`achtemp(iw)` for each `iw`, so the group
key adds `iw`. That key is the **per-call accumulator group**, and the
per-record quantities are summed only within one. Multiplicity over
`(n1true, ig, igp)` inside a group is retained.

Grouping this way is a **choice made for this diagnostic**, not a claim that
cross-group sums are meaningless. BerkeleyGW itself sums related q-point and
call contributions later, with their outer factors, on the way to a
self-energy. This module emits two cross-group aggregates precisely so both
views are visible; neither is a physical error estimate, and neither is
designated primary.

## WHAT THIS IS, AND WHAT IT IS NOT

`K*L` is a product of `vcoul(igp)`, which BerkeleyGW holds in **Rydberg**, with
the dimensionless ratios `ssx` and `sch`. So these sums, and `asxtemp`/
`achtemp` themselves, carry **intermediate Rydberg energy units**. They are
*not* dimensionless. Calling them dimensionless, as earlier revisions of this
module did, was wrong.

They are equally *not* a final self-energy, a physical energy error, an
observable, or an eV result, because the outer factors have not been applied --
and **the set of missing factors differs by output type**:

| Output | Still missing |
| --- | --- |
| both | `neq(irq)`; the sum over q-points; `ax`; `achcor` |
| diagonal `icalc=1` | `ryd` **and** `1/ndeg`, together in `fact = ryd/dble(ndeg(ii))` at `shiftenergy.f90:113`; the degenerate subspaces are built at `:69` by a loop over `sig%ndiag` only |
| offdiagonal `icalc=2` | `ryd` only, applied earlier with `neq` at `sigma_main.f90:1860-1861`; offdiagonal elements receive **no** `1/ndeg` |

So `1/ndeg` is **not** universally missing, and `ryd` enters at a *different
later location* for each output type. `MISSING_FACTORS` and `UNITS` below are
the machine-readable form of this table and are covered by the module-contract
tests.

## The comparator is not a counterfactual run

`branch_mismatch` compares two algebraic expressions at identical inputs. A
program actually taking the generic branch would additionally re-apply the
`sexcut` clamp to the generic `ssx`, which can differ from the near-pole
decision. The number of records where that would have differed is reported as
`generic_clamp_would_differ`; the comparator ignores it by construction.

This module is the PUBLIC ENTRY POINT and the CLI. Since T-006 the
implementation lives in three focused modules, and this file re-exports their
names so every existing import, test and command line keeps working
unchanged:

  * `contract.py`  -- what the numbers are and are not (the claim surface)
  * `records.py`   -- parsing, arity, coverage: file integrity only
  * `analysis.py`  -- exact-rational weighted sums, grouping, ratios

The split was an external reviewer's recommendation: a single 662-line module
mixed the scientific core with its documentation contract, so prose churn and
numeric work could not be reviewed or gated separately.
"""

import argparse
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]
                       / "occupation_audit"))

from fractions import Fraction as F  # noqa: E402
import check_occupation as co  # noqa: E402  (imported unmodified)

from contract import (  # noqa: E402
    EXPECTED_RECORDS, LOCAL_RECON_LIMIT, MISSING_FACTORS, UNITS,
    CAPTURED_NOT_VALIDATED, completeness_evidence)
from records import (  # noqa: E402
    INT_FIELDS, REAL_FIELDS, FIELDS, OCC_FIELDS, ACC_INT_FIELDS,
    ACC_REAL_FIELDS, ACC_FIELDS, WeightedError, parse, parse_accumulators,
    check_coverage, occ_view)
from analysis import analyse, ratio  # noqa: E402

#: Re-exported so `import weighted_mismatch as wm; wm.parse(...)` still works.
__all__ = [
    "EXPECTED_RECORDS", "LOCAL_RECON_LIMIT", "MISSING_FACTORS", "UNITS",
    "CAPTURED_NOT_VALIDATED", "completeness_evidence", "INT_FIELDS",
    "REAL_FIELDS", "FIELDS", "OCC_FIELDS", "ACC_INT_FIELDS", "ACC_REAL_FIELDS",
    "ACC_FIELDS", "WeightedError", "parse", "parse_accumulators",
    "check_coverage", "occ_view", "analyse", "ratio", "build_summary", "main",
]


def main(argv=None):
    ap = argparse.ArgumentParser()
    here = pathlib.Path(__file__).parent
    ap.add_argument("records", nargs="?",
                    default=here / "fixtures" / "t004_nearpole_weighted.dat")
    ap.add_argument("--accumulators",
                    default=here / "fixtures" / "t004_accumulators.dat")
    ap.add_argument("--counts",
                    default=here / "fixtures" / "fermi_branch_occ_counts.dat",
                    help="the probe's branch x occupation tally; the export "
                         "must equal its near-pole occ != 1 count")
    ap.add_argument("--control-counts",
                    default=here / "fixtures" / "control_branch_occ_counts.dat")
    ap.add_argument("--no-tally", action="store_true",
                    help="skip the tally tie; the coverage report then says "
                         "tied_to_tally: false")
    ap.add_argument("--expect-records", type=int, default=EXPECTED_RECORDS)
    ap.add_argument("--max-groups", type=int, default=0,
                    help="0 = emit every group")
    args = ap.parse_args(argv)
    summary = build_summary(args)
    json.dump(summary, sys.stdout, indent=2)
    print()
    return 0


def build_summary(args):
    """Do the whole analysis and return the summary dict.

    Separated from `main` so the analysis can be exercised without going
    through argv and stdout. `args` is any object carrying the CLI attributes
    (`records`, `accumulators`, `counts`, `control_counts`, `no_tally`,
    `expect_records`, `max_groups`); argparse's Namespace is one such object.
    """

    rows = parse(pathlib.Path(args.records).read_text())
    tally = control = tally_pair = None
    if not args.no_tally:
        # Reuse the T-003 checker's tally validation unmodified: it rejects
        # negative, duplicate, unknown and incomplete rows and enforces the
        # control contract and the per-row cross-run invariant.
        tally = co.check_counts(pathlib.Path(args.counts).read_text(),
                                "probe tally")
        control = co.check_counts(
            pathlib.Path(args.control_counts).read_text(), "control tally")
        tally_pair = co.check_tally_pair(tally, control)
    expect = tally["branch2"][1] if tally is not None else args.expect_records
    coverage = check_coverage(rows, expect, tally)
    accumulators = parse_accumulators(
        pathlib.Path(args.accumulators).read_text())
    groups, singular, clamp_diff, totals, biggest = analyse(rows)

    # A ratio against a near-zero accumulator is not evidence of a large
    # effect, so groups whose reference is far below the largest accumulator
    # in this dataset are flagged. Threshold: 1e-3 of the largest |asx+ach|.
    acc_scale = max(
        (abs(F(v["asxtemp"]) + F(v["achtemp"]))
         for v in accumulators.values()), default=F(0))
    small_ref_cut = acc_scale / 1000

    out_groups, acc_total, acc_missing, recon_worst = summarise_groups(
        groups, accumulators, small_ref_cut, acc_scale)
    # Two cross-group aggregates are reported. This one takes each per-call
    # accumulator group's magnitude first, so groups do not cancel against one
    # another WITHIN THIS DIAGNOSTIC; `cross_group_signed_over_accumulators`
    # keeps the signs and lets them cancel. The difference between the two
    # measures this dataset's internal cancellation. Neither is a physical
    # error estimate and neither is preferred: BerkeleyGW deliberately sums
    # related q-point and call contributions later, with outer factors.
    sum_abs_group_signed = sum(abs(F(g["signed"])) for g in groups.values())

    rel_total, note_total = ratio(totals["signed"], totals["local"])
    cancel_total, _ = ratio(totals["signed"], totals["absolute"])
    # --max-groups truncates the emitted detail only; every statistic below is
    # computed from the full set first (smaller finding: truncating first made
    # the global statistics depend on a display option).
    stats_groups = out_groups
    if args.max_groups:
        out_groups = out_groups[:args.max_groups]
    summary = dict(
        what=("partially weighted local branch-mismatch sums in intermediate "
              "Rydberg units. NEITHER aggregate below is a physical error "
              "estimate; see per_call_group_l1_note and cross_group_warning."),
        units=UNITS,
        source="BerkeleyGW 4.0 Si-EPM GPP, fermi_level_absolute probe "
               "(charge-inconsistent); see bgw/weighted_audit/REVIEW_PACKET.md",
        weight="aqsntemp(ig,n1) * MYCONJG(aqsmtemp(igp,n1)) * vcoul(igp); "
               "real flavor, MYCONJG is the identity",
        missing_factors=MISSING_FACTORS,
        weights_captured_not_validated=list(CAPTURED_NOT_VALIDATED),
        coverage=coverage,
        exported_records_vs_counted_events=dict(
            exported_records=len(rows),
            counted_qualifying_events=(
                tally["branch2"][1] if tally is not None else None),
            cardinality_matches_tally=(
                tally is not None and len(rows) == tally["branch2"][1]),
            relationship=(
                "Cardinality and id-sequentiality match the validated tally. "
                "Completeness -- that these records ARE the counted population "
                "rather than a same-sized different set -- additionally "
                "requires the shared-predicate and same-run-provenance links "
                "in completeness_evidence, which this program does not check."
                if tally is not None and len(rows) == tally["branch2"][1]
                else "NOT tied to a tally; --no-tally was used"),
        ),
        completeness_evidence=completeness_evidence(tally is not None),
        tally_invariants_probe_vs_control=tally_pair,
        events_summed=totals["n"],
        singular_records_excluded=singular,
        events_accounted=totals["n"] + len(singular),
        generic_clamp_would_differ=clamp_diff,
        comparator_note="branch_mismatch compares two expressions at identical "
                        "inputs; it is not a counterfactual program run, and it "
                        "ignores any sexcut difference in the generic branch",
        groups=len(groups),
        total_signed_weighted_mismatch=float(totals["signed"]),
        total_sum_abs_weighted_mismatch=float(totals["absolute"]),
        total_weighted_recorded_local=float(totals["local"]),
        accumulator_rows=len(accumulators),
        local_reconstruction_check=dict(
            groups_verified=len(recon_worst),
            max_relative_difference=max(recon_worst) if recon_worst else None,
            **LOCAL_RECON_LIMIT,
            meaning="the Fortran summed K*L itself, in its own arithmetic, "
                    "over exactly these records, and the Python subtotal "
                    "agrees. This validates the GROUPED SUBTOTAL in two "
                    "arithmetic implementations. It does NOT independently "
                    "validate any individual captured weight or local value, "
                    "nor bound their individual reconstruction errors: "
                    "per-term errors can cancel within a subtotal"),
        largest_accumulator_in_dataset=float(acc_scale),
        small_reference_threshold=float(small_ref_cut),
        groups_flagged_small_reference=sum(
            1 for x in stats_groups if x["accumulator_is_small_reference"]),
        max_group_ratio_any=max(
            (x["signed_over_accumulator"] for x in stats_groups
             if x["signed_over_accumulator"] is not None), default=None),
        max_group_ratio_excluding_small_reference=max(
            (x["signed_over_accumulator"] for x in stats_groups
             if x["signed_over_accumulator"] is not None
             and not x["accumulator_is_small_reference"]), default=None),
        groups_above_10pct_of_accumulator=sum(
            1 for x in stats_groups
            if x["signed_over_accumulator"] is not None
            and not x["accumulator_is_small_reference"]
            and x["signed_over_accumulator"] > 0.1),
        groups_without_accumulator=len(acc_missing),
        sum_abs_accumulator_over_affected_groups=float(acc_total),
        per_call_group_l1_over_accumulators=(
            float(sum_abs_group_signed / acc_total) if acc_total else None),
        per_call_group_l1_note=(
            "A CHOSEN DATASET L1 NORM over per-call accumulator groups, not a "
            "preferred physical effect size. "
            "Each per-call-accumulator-group signed mismatch is taken in "
            "magnitude before aggregating, so cancellation between groups is "
            "avoided WITHIN THIS DIAGNOSTIC. That is a property of the choice, "
            "not evidence that such cancellation is unphysical: BerkeleyGW "
            "deliberately sums related q-point and call contributions, with "
            "their outer factors, on the way to a self-energy. Neither this L1 "
            "norm nor cross_group_signed_over_accumulators is a physical error "
            "estimate. Quote it as a per-call L1 diagnostic or not at all."),
        sum_abs_group_signed=float(sum_abs_group_signed),
        cross_group_signed_over_accumulators=(
            float(abs(totals["signed"]) / acc_total) if acc_total else None),
        cross_group_warning=(
            "The signed counterpart: the signed sum over all groups divided by "
            "the accumulator total, so different calls, matrix elements, "
            "q-points and iw energies do cancel against one another. It is "
            "reported for comparison with the L1 norm. It is likewise NOT a "
            "physical error estimate, and the difference between the two "
            "numbers measures how much this dataset cancels internally, not "
            "which of them is physically correct."),
        subset_local_over_affected_accumulators=(
            float(abs(totals["local"]) / acc_total) if acc_total else None),
        reference_warning=(
            "total_signed_over_local uses the exported records' OWN local "
            "contribution as the reference, which is a small subset of the "
            "accumulator, so the ratio is not informative about size. The two "
            "aggregates that divide by the accumulators instead are "
            "per_call_group_l1_over_accumulators and "
            "cross_group_signed_over_accumulators. Neither is preferred and "
            "neither is a physical error estimate; read them together."),
        total_signed_over_local=rel_total,
        total_reference_note=note_total,
        total_cancellation_ratio_signed_over_abs=cancel_total,
        largest_abs_term=float(abs(biggest[0])) if biggest else None,
        largest_abs_term_record=biggest[1] if biggest else None,
        group_detail=out_groups,
    )
    return summary


def summarise_groups(groups, accumulators, small_ref_cut, acc_scale):
    """Build the per-group detail rows and the aggregates over them.

    Extracted from `build_summary` so the per-group bookkeeping -- accumulator
    matching, small-reference flagging, subtotal agreement and cancellation
    ratios -- can be read and tested on its own. Returns
    `(out_groups, acc_total, acc_missing, recon_worst)`.
    """
    out_groups = []
    acc_total = F(0)
    acc_missing = []
    recon_worst = []
    for key, g in sorted(groups.items(),
                         key=lambda kv: -abs(float(kv[1]["signed"]))):
        rel, note = ratio(g["signed"], g["local"])
        cancel, _ = ratio(g["signed"], g["absolute"])
        pair = accumulators.get(key)
        if pair is None:
            acc_missing.append(key)
            acc_val = None
            rel_acc, note_acc = None, "no accumulator row matched this group"
        else:
            # The accumulator row carries its own outer identity. Check it
            # against the identity the records claim, or a record could be
            # matched to an accumulator for a different band, spin, output
            # type or q-point and still pass.
            ridn = g["ident"]
            rec_ident = (ridn[0], ridn[1], ridn[2], ridn[4],
                         ridn[5], ridn[6], ridn[7])
            if pair["ident"] != rec_ident:
                raise WeightedError(
                    f"group {key}: accumulator identity {pair['ident']} does "
                    f"not match the identity its records claim {rec_ident} "
                    f"(icalc, band_in, il, ispin, qk); the records and the "
                    f"accumulator describe different outputs")
            acc_val = F(pair["asxtemp"]) + F(pair["achtemp"])
            acc_total += abs(acc_val)
            rel_acc, note_acc = ratio(g["signed"], acc_val)
            recon = F(pair["subtotal"])
            diff = abs(g["local"] - recon)
            recon_rel = float(diff / abs(recon)) if recon != 0 else float(diff)
            if recon_rel > LOCAL_RECON_LIMIT["limit"]:
                raise WeightedError(
                    f"group {key}: Python sum(K*L) = {float(g['local']):.17e} "
                    f"disagrees with the Fortran subtotal "
                    f"{float(recon):.17e} by relative {recon_rel:.3e}, limit "
                    f"{LOCAL_RECON_LIMIT['limit']:.0e}. This localises the "
                    f"disagreement to this group's SUBTOTAL; it does not by "
                    f"itself identify which weight or local value is wrong, "
                    f"and per-term errors can cancel within a subtotal")
            recon_worst.append(recon_rel)
            if abs(acc_val) < small_ref_cut:
                note_acc = (note_acc or "") + (
                    f"reference accumulator {float(acc_val):.3e} is below "
                    f"1e-3 of the largest in this dataset "
                    f"({float(acc_scale):.3e}); the ratio is a small-reference "
                    f"artefact, not evidence of a large effect")
        idn = g["ident"]
        out_groups.append(dict(
            call_id=key[0], iw=key[1],
            icalc=idn[0], band_in=idn[1], il=idn[2], iband=idn[3],
            ispin=idn[4], qk=[idn[5], idn[6], idn[7]],
            events=g["n"],
            accumulator_asx=None if pair is None else pair["asxtemp"],
            accumulator_ach=None if pair is None else pair["achtemp"],
            accumulator_total=None if acc_val is None else float(acc_val),
            signed_over_accumulator=rel_acc,
            accumulator_is_small_reference=(
                pair is not None
                and abs(F(pair["asxtemp"]) + F(pair["achtemp"])) < small_ref_cut),
            accumulator_note=note_acc,
            signed_weighted_mismatch=float(g["signed"]),
            sum_abs_weighted_mismatch=float(g["absolute"]),
            largest_abs_term=float(abs(g["largest"])),
            largest_abs_term_record=g["largest_rec"],
            weighted_recorded_local=float(g["local"]),
            signed_over_local=rel,
            reference_note=note,
            cancellation_ratio_signed_over_abs=cancel,
        ))
    return out_groups, acc_total, acc_missing, recon_worst


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (WeightedError, co.RecordError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)

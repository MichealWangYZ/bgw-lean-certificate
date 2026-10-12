#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Sensitivity of the reported maximum per-call-group ratio to the
`small_reference_threshold` cutoff.

`weighted_mismatch.py` reports one headline number,
`max_group_ratio_excluding_small_reference`, after discarding every per-call
accumulator group whose reference accumulator `|asxtemp + achtemp|` falls below
`1e-3` times the largest accumulator in the dataset. That `1e-3` is a judgement
call. This module sweeps it and reports how the headline moves.

## What this module computes

For a relative cutoff `c` in `(0, 1]`:

    keep group g  <=>  abs(acc(g)) >= c * max_h abs(acc(h))
    reported(c)   =  max over kept g of  abs(signed_mismatch(g)) / abs(acc(g))

`reported` is a step function of `c`: it can only change when `c` crosses
`abs(acc(g)) / max_h abs(acc(h))` for some group `g`. `breakpoints()`
enumerates those steps exactly, so the curve is characterised completely rather
than sampled. `sweep`/`evaluate` additionally evaluate a grid, which is what a
reader normally wants to read as a table.

All arithmetic uses `fractions.Fraction` over the records' own binary64 fields,
matching `weighted_mismatch.analyse`, which this module imports unmodified and
never edits.

## WHAT THIS IS, AND WHAT IT IS NOT

This is a **robustness diagnostic for a reporting choice**, not a physical
measurement. It answers exactly one question: would a different arbitrary
exclusion cutoff have produced a different headline? It says nothing about
whether the ratio is a meaningful quantity in the first place. Every caveat
attached to that ratio in `bgw/weighted_audit/REVIEW_PACKET.md` section 4 --
intermediate Rydberg units, stripped outer factors that differ by output type,
a charge-inconsistent probe configuration, a grouping chosen for this
diagnostic -- applies unchanged to every number produced here.

In particular: a wide plateau shows the headline is **not an artefact of the
one cutoff that was chosen**. It does NOT show the headline is physically
meaningful, that `(call_id, iw)` is the right grouping, or that the effect is
large in any final self-energy. Those are separate claims with separate, and in
this project weaker, evidence.

The small-cutoff end of the curve is dominated by exactly the small-reference
groups the exclusion exists to suppress. A large value there is the artefact
the review packet already describes, not a finding.
"""

from fractions import Fraction as F
import argparse
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import weighted_mismatch as wm  # noqa: E402  (imported unmodified, never edited)

#: The cutoff `weighted_mismatch.py` actually applies, as a fraction of the
#: largest abs(asxtemp + achtemp) in the dataset. Held here so the sweep can
#: locate the shipped choice inside its own curve instead of restating it in
#: prose. It is read from that module's behaviour, not imported: the module
#: forms `acc_scale / 1000` inline.
SHIPPED_RELATIVE_CUTOFF = F(1, 1000)


def _pow10(exponent):
    """`10**exponent` as a Fraction.

    Integer exponents are exact. Fractional (quarter-decade) grid points are
    irrational and are carried as the exact Fraction of the nearest binary64,
    which is why they are only ever used as a *cutoff*, never as a measured
    quantity: rounding here can at most move a grid point across a breakpoint,
    and `breakpoints()` locates every breakpoint exactly and independently.
    """
    if exponent.denominator == 1:
        n = int(exponent)
        return F(10) ** n if n >= 0 else F(1, 10 ** (-n))
    return F(10.0 ** float(exponent))


def default_grid():
    """Quarter-decade steps from 1e-6 to 1e0 inclusive.

    `1e0` keeps only the single largest-accumulator group. That degenerate
    right-hand end is shown deliberately, so a reader sees where the curve
    stops rather than where the plot was cropped.
    """
    return [_pow10(F(e, 4)) for e in range(-24, 1)]


class SweepError(ValueError):
    """The inputs do not support a sweep."""


def group_table(groups, accumulators):
    """Per-group `(abs accumulator, ratio)` table, exact.

    Groups whose accumulator row is missing or exactly zero cannot carry a
    ratio. They are returned separately rather than silently dropped: the
    population being swept must never itself depend on the cutoff.
    """
    usable, unusable = [], []
    for key, g in groups.items():
        pair = accumulators.get(key)
        if pair is None:
            unusable.append(dict(call_id=key[0], iw=key[1],
                                 why="no accumulator row matched this group"))
            continue
        acc = abs(F(pair["asxtemp"]) + F(pair["achtemp"]))
        if acc == 0:
            unusable.append(dict(call_id=key[0], iw=key[1],
                                 why="reference accumulator is exactly zero"))
            continue
        idn = g["ident"]
        usable.append(dict(
            key=key, call_id=key[0], iw=key[1],
            icalc=idn[0], band_in=idn[1], il=idn[2], iband=idn[3],
            ispin=idn[4], events=g["n"],
            abs_accumulator=acc,
            ratio=abs(F(g["signed"])) / acc,
        ))
    if not usable:
        raise SweepError("no group carries a usable reference accumulator; "
                         "refusing a vacuous sweep")
    return usable, unusable


def evaluate(usable, scale, cutoff):
    """The reported maximum at one relative cutoff. Exact comparison."""
    keep = [x for x in usable if x["abs_accumulator"] >= cutoff * scale]
    if not keep:
        return dict(relative_cutoff=float(cutoff), groups_kept=0,
                    groups_excluded=len(usable), max_ratio=None,
                    argmax_call_id=None, argmax_iw=None,
                    argmax_accumulator=None, argmax_events=None,
                    argmax_icalc=None, argmax_band_in=None)
    best = max(keep, key=lambda x: x["ratio"])
    return dict(
        relative_cutoff=float(cutoff),
        groups_kept=len(keep),
        groups_excluded=len(usable) - len(keep),
        max_ratio=float(best["ratio"]),
        argmax_call_id=best["call_id"],
        argmax_iw=best["iw"],
        argmax_accumulator=float(best["abs_accumulator"]),
        argmax_events=best["events"],
        argmax_icalc=best["icalc"],
        argmax_band_in=best["band_in"],
    )


def sweep(usable, scale, grid):
    return [evaluate(usable, scale, c) for c in grid]


def breakpoints(usable, scale):
    """Exact step structure of `reported(c)`.

    One entry per distinct plateau, in increasing cutoff, each carrying the
    half-open interval `(lower, upper]` of relative cutoffs on which the
    reported maximum takes that value. Together these are the whole curve; any
    grid is a sampling of it.
    """
    order = sorted(usable, key=lambda x: x["abs_accumulator"])
    n = len(order)
    # suffix[i] = argmax over order[i:], i.e. after excluding the i groups with
    # the smallest reference accumulators
    suffix = [None] * n
    best = None
    for i in range(n - 1, -1, -1):
        if best is None or order[i]["ratio"] > best["ratio"]:
            best = order[i]
        suffix[i] = best
    out = []
    lower = F(0)
    for i in range(n):
        upper = order[i]["abs_accumulator"] / scale
        cur = suffix[i]
        if (out and out[-1]["argmax_call_id"] == cur["call_id"]
                and out[-1]["argmax_iw"] == cur["iw"]):
            out[-1]["relative_cutoff_upper"] = float(upper)
            out[-1]["groups_excluded_at_upper"] = i
            lower = upper
            continue
        out.append(dict(
            relative_cutoff_lower_exclusive=float(lower),
            relative_cutoff_upper=float(upper),
            groups_excluded_at_lower=i,
            groups_excluded_at_upper=i,
            max_ratio=float(cur["ratio"]),
            argmax_call_id=cur["call_id"],
            argmax_iw=cur["iw"],
            argmax_icalc=cur["icalc"],
            argmax_band_in=cur["band_in"],
            argmax_events=cur["events"],
            argmax_accumulator=float(cur["abs_accumulator"]),
        ))
        lower = upper
    return out


def plateau_containing(bps, cutoff):
    """The plateau whose half-open interval contains `cutoff`, or None."""
    c = float(cutoff)
    for b in bps:
        if b["relative_cutoff_lower_exclusive"] < c <= b["relative_cutoff_upper"]:
            return b
    return None


def run(records_path, accumulators_path, grid=None):
    rows = wm.parse(pathlib.Path(records_path).read_text())
    accumulators = wm.parse_accumulators(
        pathlib.Path(accumulators_path).read_text())
    groups, singular, _clamp, _totals, _biggest = wm.analyse(rows)
    scale = max((abs(F(v["asxtemp"]) + F(v["achtemp"]))
                 for v in accumulators.values()), default=F(0))
    if scale == 0:
        raise SweepError("largest accumulator is zero; a relative cutoff is "
                         "undefined")
    usable, unusable = group_table(groups, accumulators)
    grid = list(grid if grid is not None else default_grid())
    bps = breakpoints(usable, scale)
    return dict(
        what=("sensitivity of max_group_ratio_excluding_small_reference to "
              "the small_reference_threshold cutoff. A ROBUSTNESS DIAGNOSTIC "
              "FOR A REPORTING CHOICE, not a physical measurement: every "
              "caveat on the ratio itself -- intermediate Rydberg units, "
              "stripped outer factors, charge-inconsistent probe, chosen "
              "grouping -- applies unchanged to every number here."),
        records=len(rows),
        singular_records_excluded=singular,
        groups_total=len(groups),
        groups_usable=len(usable),
        groups_unusable=unusable,
        largest_accumulator_in_dataset=float(scale),
        shipped_relative_cutoff=float(SHIPPED_RELATIVE_CUTOFF),
        shipped_plateau=plateau_containing(bps, SHIPPED_RELATIVE_CUTOFF),
        curve=sweep(usable, scale, grid),
        breakpoints=bps,
        interpretation_limits=(
            "A plateau shows the headline is not an artefact of the one "
            "cutoff chosen. It does NOT show the headline is physically "
            "meaningful, that (call_id, iw) is the right grouping, or that "
            "the effect is large in any final self-energy. The small-cutoff "
            "end of the curve is dominated by exactly the small-reference "
            "groups the exclusion exists to suppress; a large value there is "
            "the artefact the review packet already describes."),
    )


def format_table(result):
    lines = ["| relative cutoff | groups kept | groups excluded | max ratio | "
             "argmax (call_id, iw) | argmax abs(accumulator) |",
             "| --- | --- | --- | --- | --- | --- |"]
    for r in result["curve"]:
        mr = "n/a" if r["max_ratio"] is None else f"{r['max_ratio']:.6f}"
        am = ("n/a" if r["argmax_call_id"] is None
              else f"({r['argmax_call_id']}, {r['argmax_iw']})")
        aa = ("n/a" if r["argmax_accumulator"] is None
              else f"{r['argmax_accumulator']:.6e}")
        lines.append(f"| {r['relative_cutoff']:.3e} | {r['groups_kept']} | "
                     f"{r['groups_excluded']} | {mr} | {am} | {aa} |")
    lines += ["",
              "Exact step structure. This is the whole curve; the grid above "
              "is a sampling of it.",
              "",
              "| cutoff interval (lower, upper] | groups excluded | max ratio "
              "| argmax (call_id, iw) | argmax abs(accumulator) |",
              "| --- | --- | --- | --- | --- |"]
    for b in result["breakpoints"]:
        lines.append(
            f"| ({b['relative_cutoff_lower_exclusive']:.6e}, "
            f"{b['relative_cutoff_upper']:.6e}] | "
            f"{b['groups_excluded_at_lower']}..{b['groups_excluded_at_upper']} "
            f"| {b['max_ratio']:.6f} | "
            f"({b['argmax_call_id']}, {b['argmax_iw']}) | "
            f"{b['argmax_accumulator']:.6e} |")
    return "\n".join(lines)


def main(argv=None):
    here = pathlib.Path(__file__).parent
    ap = argparse.ArgumentParser()
    ap.add_argument("records", nargs="?",
                    default=here / "fixtures" / "t004_nearpole_weighted.dat")
    ap.add_argument("--accumulators",
                    default=here / "fixtures" / "t004_accumulators.dat")
    ap.add_argument("--json", action="store_true",
                    help="emit the full JSON instead of the markdown tables")
    args = ap.parse_args(argv)
    result = run(args.records, args.accumulators)
    if args.json:
        json.dump(result, sys.stdout, indent=2)
        print()
        return 0
    print(format_table(result))
    print()
    print("largest accumulator in dataset: "
          f"{result['largest_accumulator_in_dataset']:.17e}")
    sp = result["shipped_plateau"]
    if sp is not None:
        print(f"shipped cutoff {result['shipped_relative_cutoff']:.0e} lies on "
              f"the plateau ({sp['relative_cutoff_lower_exclusive']:.6e}, "
              f"{sp['relative_cutoff_upper']:.6e}], max ratio "
              f"{sp['max_ratio']:.6f}")
    print()
    print(result["interpretation_limits"])
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (SweepError, wm.WeightedError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)

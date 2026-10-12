#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Parse and analyse the T-005 branch-boundary sweep table.

Pure analysis: this module never compiles or runs anything. `run_sweep.py`
produces the raw table, this module turns it into the machine-readable summary,
and `tests/test_branch_boundary.py` re-derives the same quantities from the
saved table.

Nothing here is a statement about BerkeleyGW production runs. The rows are
per-(ig,igp) local values of `-occ*ssx + 0.5*sch` with the common factor
`aqsntemp*MYCONJG(aqsmtemp)*vcoul(igp)` divided out.
"""

from __future__ import annotations

import math
import pathlib
import struct

#: Sign convention used everywhere below: the branch discrepancy is the
#: GENERIC candidate minus the NEAR-POLE candidate, evaluated at identical
#: inputs. This is the orientation of `GW.GPP.BGW4.branch_mismatch`,
#: `occupiedGenericOcc occ .. - occupiedNearPoleOcc occ ..`.
DELTA_IS = "generic_minus_near_pole"

#: Columns that stay integers.
INT_COLUMNS = {"bits", "bits_false", "bits_true", "steps", "c1", "c2", "branch",
               "cut_sel", "cut_gen", "cut_np", "policy", "cycled"}
#: Columns that stay strings.
STR_COLUMNS = {"case", "label", "point"}

#: Boundary cases where `wxt > 0` on every swept row, so the `ssxcutoff` clamp
#: of `mtxel_cor.f90:1848` can never fire.
UNCLAMPED_CASES = ("A+", "A-", "B+")
#: Boundary cases placed at `wxt < 0` where the clamp is observed to fire.
CLAMPED_CASES = ("C-",)


def bits(x: float) -> int:
    """Binary64 bit pattern as an unsigned integer."""
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def parse(path) -> dict:
    """Read the tagged table written by `branch_boundary.f90`."""
    return parse_text(pathlib.Path(path).read_text())


def parse_text(text: str) -> dict:
    """Parse the tagged table from a string."""
    meta: dict[str, object] = {}
    columns: dict[str, list[str]] = {}
    rows: dict[str, list[dict]] = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        if line.startswith("#"):
            fields = line[1:].split()
            if not fields:
                continue
            if fields[0] == "COLUMNS":
                columns[fields[1]] = fields[2:]
            elif len(fields) == 2:
                try:
                    meta[fields[0]] = float(fields[1])
                except ValueError:
                    meta[fields[0]] = fields[1]
            continue
        fields = line.split()
        tag, values = fields[0], fields[1:]
        names = columns[tag]
        if len(values) != len(names):
            raise ValueError(f"{tag}: expected {len(names)} columns, got {len(values)}")
        row = {}
        for name, value in zip(names, values):
            if name in STR_COLUMNS:
                row[name] = value
            elif name in INT_COLUMNS:
                row[name] = int(value)
            else:
                number = float(value)
                # F1 (checker-soundness audit): NaN and inf must never reach
                # the arithmetic. `abs(nan - x) > 0` is False, so a NaN slips
                # through the delta-consistency check, and `max(0.0, nan)` is
                # 0.0, so it then vanishes from the reported maximum -- an
                # invalid observation yields perfect-looking metrics. Reject
                # here rather than downstream. Any future row type that
                # legitimately needs a non-finite diagnostic must opt in with
                # an explicit status, not by arriving as a silent NaN.
                if not math.isfinite(number):
                    raise ValueError(
                        f"{tag} row: non-finite value {value!r} in column "
                        f"{name!r}; non-finite observations are rejected, not "
                        f"treated as numerical success")
                row[name] = number
        rows.setdefault(tag, []).append(row)
    if not rows:
        raise ValueError("no data rows")
    return {"meta": meta, "columns": columns, "rows": rows}


def closed_form(occ: float, ieps: float, wt: float, x: float) -> float:
    """`GW.GPP.BGW4.branch_mismatch` right-hand side, in binary64.

    `(1-occ) * (Omega2/(2*wt*(x+wt)) + Omega2/((x-wt)*(x+wt)))` with
    `Omega2 = wt^2 * ieps`. The theorem is about exact reals; evaluating it in
    binary64 is a comparison, not a proof.
    """
    omega2 = wt**2 * ieps
    return (1.0 - occ) * (
        omega2 / (2.0 * wt * (x + wt)) + omega2 / ((x - wt) * (x + wt))
    )


def sweep(parsed, case, occ):
    """Sweep rows of one case at one occupation, in file order."""
    return [r for r in parsed["rows"]["SWEEP"]
            if r["case"] == case and r["occ"] == occ]


def ulp_rows(parsed, case, occ):
    return [r for r in sweep(parsed, case, occ) if r["label"].startswith("ulp")]


def boundary_report(parsed) -> dict:
    """Which conjunct defines each located surface, and is it ULP-tight."""
    out = {}
    for row in parsed["rows"]["BOUNDARY"]:
        case = row["case"]
        near = {r["label"]: r for r in ulp_rows(parsed, case, 1.0)}
        false_side, true_side = near["ulpF-0"], near["ulpT+0"]
        deciding = []
        if false_side["c1"] != true_side["c1"]:
            deciding.append("wdiffr")
        if false_side["c2"] != true_side["c2"]:
            deciding.append("delwr")
        out[case] = {
            "ieps": row["ieps"],
            "wt": row["wt"],
            "wxt_false": row["w_false"],
            "wxt_true": row["w_true"],
            "adjacent_representable": abs(row["bits_true"] - row["bits_false"]) == 1,
            "bisection_steps": row["steps"],
            "d_false": false_side["d"],
            "d_true": true_side["d"],
            "branch_false": false_side["branch"],
            "branch_true": true_side["branch"],
            "deciding_conjunct": deciding,
            "wdiffr_false": false_side["wdiffr"],
            "delwr_false": false_side["delwr"],
        }
    return out


ULP_ORDER = ["ulpF-2", "ulpF-1", "ulpF-0", "ulpT+0", "ulpT+1", "ulpT+2"]


def _steps(seq, key):
    """(jump across the surface, largest adjacent step inside one branch)."""
    jump = seq[3][key] - seq[2][key]
    within = max(
        abs(seq[1][key] - seq[0][key]),
        abs(seq[2][key] - seq[1][key]),
        abs(seq[4][key] - seq[3][key]),
        abs(seq[5][key] - seq[4][key]),
    )
    return jump, within


def crossing_report(parsed, case, occ) -> dict:
    """Jump across the surface versus ordinary within-branch variation.

    `jump` is |value(first true-side point) - value(last false-side point)|,
    i.e. between two adjacent representable `wxt`. `within_branch` is the
    largest |difference| between adjacent representable points that stay inside
    one branch, taken over both sides. `scale` is the local |value|.

    The same quantities are reported for `value_pre`, the accumulated value
    built from the pre-`ssxcutoff` `ssx`. When the clamp fires on any of the
    six rows the post-clamp numbers are NOT the unclamped branch algebra, and
    `GW.GPP.BGW4.branch_mismatch` -- a statement about that algebra only --
    is not a prediction for them. `closed_form_applies` records exactly that,
    and `signed_jump_minus_predicted` is left None when it does not apply.
    """
    near = {r["label"]: r for r in ulp_rows(parsed, case, occ)}
    seq = [near[label] for label in ULP_ORDER]
    signed, within = _steps(seq, "value")
    jump = abs(signed)
    signed_pre, within_pre = _steps(seq, "value_pre")
    scale = max(abs(r["value"]) for r in seq)
    scale_pre = max(abs(r["value_pre"]) for r in seq)
    clamped = [r["label"] for r in seq if r["cut_sel"]]
    true_row = seq[3]
    predicted = closed_form(occ, true_row["ieps"], true_row["wt"], true_row["wxt"])
    applies = not clamped
    return {
        "occ": occ,
        "jump": jump,
        "signed_jump": signed,
        "within_branch_max": within,
        "value_scale": scale,
        # None, not infinity, when the denominator is exactly zero: inside a
        # fully clamped branch every adjacent step is 0, which is a fact about
        # the clamp rather than an unbounded ratio.
        "jump_over_scale": jump / scale if scale else None,
        "jump_over_within_branch": jump / within if within else None,
        "signed_jump_pre_clamp": signed_pre,
        "within_branch_max_pre_clamp": within_pre,
        "value_scale_pre_clamp": scale_pre,
        "clamp_active_labels": clamped,
        "clamp_active": bool(clamped),
        "closed_form_applies": applies,
        "predicted_mismatch": predicted,
        "signed_jump_minus_predicted": (signed - predicted) if applies else None,
        "signed_jump_pre_clamp_minus_predicted": signed_pre - predicted,
    }


def clamp_report(parsed) -> dict:
    """Where `mtxel_cor.f90:1848` actually fired, with pre/post values.

    The clamp needs `wxt < 0` AND `|ssx| > sig%sexcut*|I_eps|`. It is recorded
    from the source condition itself (`cut_*`), never inferred from a
    post-clamp zero, and it is reported separately for the selected branch and
    for each forced counterfactual candidate.
    """
    out = {}
    for row in parsed["rows"]["SWEEP"]:
        entry = out.setdefault(row["case"], {
            "rows_total": 0, "rows_clamped_selected": 0,
            "rows_clamped_generic": 0, "rows_clamped_near_pole": 0,
            "min_wxt": math.inf, "clamped_labels": [], "detail": [],
        })
        entry["rows_total"] += 1
        entry["min_wxt"] = min(entry["min_wxt"], row["wxt"])
        entry["rows_clamped_selected"] += row["cut_sel"]
        entry["rows_clamped_generic"] += row["cut_gen"]
        entry["rows_clamped_near_pole"] += row["cut_np"]
        if row["cut_sel"] and row["label"] not in entry["clamped_labels"]:
            entry["clamped_labels"].append(row["label"])
        if row["cut_sel"] and row["label"] in ULP_ORDER:
            entry["detail"].append({
                "label": row["label"], "occ": row["occ"], "wxt": row["wxt"],
                "branch": row["branch"], "ssxcutoff": row["ssxcutoff"],
                "ssx_pre": row["ssx_pre"], "ssx_post": row["ssx"],
                "gen_ssx_pre": row["gen_ssx_pre"], "gen_ssx_post": row["gen_ssx"],
                "np_ssx_pre": row["np_ssx_pre"], "np_ssx_post": row["np_ssx"],
                "sch": row["sch"],
                "value_pre": row["value_pre"], "value_post": row["value"],
                "delta_pre": row["gen_value_pre"] - row["np_value_pre"],
                "delta_post": row["gen_value"] - row["np_value"],
                "closed_form": closed_form(row["occ"], row["ieps"], row["wt"],
                                           row["wxt"]),
            })
    return out


def branch3_report(parsed) -> dict:
    """Which in-source states can reach the third branch.

    Two separate statements, which the original T-005 text conflated:

    * An ordinary surviving positive-real mode cannot reach branch 3. Line 774
      keeps only `|wtilde2| >= TOL_Small`; for `wtilde2 > 0` line 793 gives
      `wtilde = sqrt(wtilde2) >= sqrt(TOL_Small) = 1e-3`. Branch 3 needs
      `wdiffr <= limittwo` and `delwr <= TOL_Zero`, i.e. `|wdiff| <= gamma` and
      `|wtilde| <= sqrt(TOL_Zero)*|wdiff| <= 5e-7`. Those cannot both hold.
    * A zero mode is still reachable: line 774 filters on `abs(wtilde2)`, so a
      sufficiently negative `wtilde2` survives, and `invalid_gpp_mode = 0`
      assigns `wtilde = (0,0)` at line 782. That is a policy path, not an
      impossible state.
    """
    rows = parsed["rows"].get("BRANCH3", [])
    tol_small = parsed["meta"]["TOL_Small"]
    tol_zero = parsed["meta"]["TOL_Zero"]
    gamma = parsed["meta"]["sig_gamma"]
    reached = [r for r in rows if r["branch"] == 3]
    return {
        "rows": rows,
        "branch3_labels": [r["label"] for r in reached],
        "branch3_policies": sorted({r["policy"] for r in reached}),
        "branch3_requires_zero_mode": all(
            r["wtilde_re"] == 0.0 and r["wtilde_im"] == 0.0 for r in reached),
        "zero_mode_contribution": [r["value"] for r in reached],
        "invalid_mode_route": {
            "line_774_filters_on_abs": True,
            "wtilde2_in": [r["wtilde2_in"] for r in rows
                           if r["policy"] == 0 and r["wtilde2_in"] < 0
                           and not r["cycled"]],
            "policy_zero_gives_zero_mode": all(
                r["wtilde_re"] == 0.0 and r["wtilde_im"] == 0.0
                for r in rows
                if r["policy"] == 0 and r["wtilde2_in"] < 0 and not r["cycled"]),
            "other_policies_are_nonzero_modes": all(
                (r["wtilde_re"], r["wtilde_im"]) != (0.0, 0.0)
                for r in rows
                if r["policy"] != 0 and r["wtilde2_in"] < 0 and not r["cycled"]),
        },
        "positive_mode_bound": {
            "min_surviving_wtilde": math.sqrt(tol_small),
            "max_wtilde_for_branch3": math.sqrt(tol_zero) * gamma,
            "ratio": math.sqrt(tol_small) / (math.sqrt(tol_zero) * gamma),
        },
    }


def occupation_report(parsed) -> dict:
    """Linearity of the discrepancy in `1 - occ`, per fixed point."""
    occ_rows = parsed["rows"]["OCC"]
    chk_rows = parsed["rows"]["OCCCHK"]

    # F3 (checker-soundness audit): the report used to loop over OCCCHK, so a
    # deleted OCCCHK row silently dropped that point from the report while all
    # its OCC observations were still present, and a duplicated (point, occ)
    # row was silently overwritten by the occupation-keyed dict. Neither is a
    # coverage guarantee. Require the two tables to describe the same points,
    # exactly once each, with unique observations.
    occ_points = {r["point"] for r in occ_rows}
    chk_points = [c["point"] for c in chk_rows]
    if len(chk_points) != len(set(chk_points)):
        dupes = sorted({p for p in chk_points if chk_points.count(p) > 1})
        raise ValueError(f"duplicate OCCCHK rows for points {dupes}")
    if occ_points != set(chk_points):
        raise ValueError(
            f"OCC and OCCCHK describe different point sets: "
            f"OCC-only {sorted(occ_points - set(chk_points))}, "
            f"OCCCHK-only {sorted(set(chk_points) - occ_points)}")
    seen = {}
    for r in occ_rows:
        key = (r["point"], r["occ"])
        if key in seen:
            raise ValueError(f"duplicate OCC observation for {key}")
        seen[key] = True

    out = {}
    for chk in chk_rows:
        point = chk["point"]
        rows = [r for r in occ_rows if r["point"] == point]
        # F2b: the occupation sweep is only a linearity test if everything
        # except `occ` is held fixed. Enforce it rather than assume it.
        for field in ("ieps", "wt", "wxt"):
            values = {r[field] for r in rows}
            if len(values) != 1:
                raise ValueError(
                    f"{point}: {field} varies across the occupation sweep "
                    f"({sorted(values)}); the linearity comparison requires "
                    f"fixed non-occupation inputs")
        ratios = {}
        rel_closed = 0.0
        rel_supplied = 0.0
        delta_one = None
        for r in rows:
            delta = r["gen_value"] - r["np_value"]
            if abs(delta - r["delta"]) > 0:
                raise ValueError(f"{point}: delta column disagrees with gen-np")
            if r["occ"] == 1.0:
                delta_one = delta
            else:
                ratios[r["occ"]] = delta / (1.0 - r["occ"])
                # F2: the oracle must be INDEPENDENT. This used to compare
                # `delta` against the driver's own `closed_form` column, so
                # scaling gen_value, np_value, delta and closed_form together
                # left every metric at zero. Recompute the expectation from
                # the physical inputs instead, using the same expression the
                # Lean theorem states.
                expected = closed_form(r["occ"], r["ieps"], r["wt"], r["wxt"])
                if expected == 0.0:
                    raise ValueError(
                        f"{point}: recomputed expectation is zero at occ="
                        f"{r['occ']}; cannot form a relative error")
                rel_closed = max(rel_closed,
                                 abs(delta - expected) / abs(expected))
                # The driver's own column is still checked, but as an OUTPUT
                # under test rather than as the reference.
                rel_supplied = max(
                    rel_supplied,
                    abs(r["closed_form"] - expected) / abs(expected))
        ref = ratios[0.75]
        spread = max(abs(v - ref) / abs(ref) for v in ratios.values())
        # F1: derived metrics are validated before they are reported, so a
        # non-finite intermediate cannot be presented as a clean measurement.
        for label, value in (("max_relative_spread", spread),
                             ("max_relative_closed_form_error", rel_closed),
                             ("supplied_closed_form_error", rel_supplied)):
            if not math.isfinite(value):
                raise ValueError(f"{point}: {label} is non-finite")
        out[point] = {
            "ieps": rows[0]["ieps"],
            "wt": rows[0]["wt"],
            "wxt": rows[0]["wxt"],
            "ratios": {str(k): v for k, v in sorted(ratios.items())},
            "ratio_reference": ref,
            "max_relative_spread": spread,
            "supplied_closed_form_error": rel_supplied,
            "delta_at_occ_one": delta_one,
            "max_relative_closed_form_error": rel_closed,
            "fortran_ratio_reference": chk["ratio_ref"],
            "fortran_max_rel_spread": chk["max_rel_spread"],
        }
    return out


def invariance_report(parsed) -> dict:
    shifts = []
    for r in parsed["rows"].get("INVSHIFT", []):
        shifts.append({
            "shift": r["shift"],
            "wxt_exact": r["wxt_shift"] == r["wxt_base"],
            "value_exact": r["value_shift"] == r["value_base"],
            "wxt_shift": r["wxt_shift"],
            "value_shift": r["value_shift"],
        })
    scales = []
    for r in parsed["rows"].get("INVSCALE", []):
        scales.append({
            "lambda": r["lambda"],
            "rel_gen": r["rel_gen"],
            "rel_np": r["rel_np"],
            "rel_delta": r["rel_delta"],
        })
    exact = [s["shift"] for s in shifts if s["value_exact"]]
    inexact = [s["shift"] for s in shifts if not s["value_exact"]]
    return {
        "energy_zero_shift": {
            "rows": shifts,
            "exact_shifts": exact,
            "inexact_shifts": inexact,
            "largest_exact_shift": max(exact) if exact else None,
        },
        "ieps_scaling": {
            "rows": scales,
            "max_relative_deviation": max(
                max(s["rel_gen"], s["rel_np"], s["rel_delta"]) for s in scales
            ) if scales else None,
        },
    }


def summarize(parsed) -> dict:
    cases = [r["case"] for r in parsed["rows"]["BOUNDARY"]]
    crossings = {
        case: {"occ_1.0": crossing_report(parsed, case, 1.0),
               "occ_0.5": crossing_report(parsed, case, 0.5)}
        for case in cases
    }
    return {
        "delta_sign_convention": DELTA_IS,
        "parameters": parsed["meta"],
        "row_counts": {tag: len(rows) for tag, rows in sorted(parsed["rows"].items())},
        "boundaries": boundary_report(parsed),
        "crossings": crossings,
        "occupation_linearity": occupation_report(parsed),
        "invariances": invariance_report(parsed),
        "clamp": clamp_report(parsed),
        "branch3": branch3_report(parsed),
        "unclamped_cases": list(UNCLAMPED_CASES),
        "clamped_cases": list(CLAMPED_CASES),
    }


if __name__ == "__main__":
    import argparse
    import json

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("table")
    args = ap.parse_args()
    # allow_nan=False is the last line of defence: if a non-finite value ever
    # reaches emission despite the parser and metric guards, fail loudly rather
    # than print nonstandard JSON that downstream readers silently accept.
    print(json.dumps(summarize(parse(args.table)), indent=2, sort_keys=True,
                     allow_nan=False))

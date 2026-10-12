#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Regression checks for the two saved, occupied-loop BerkeleyGW exports.

Exact rational formulas use the saved binary64 inputs. This measures arithmetic
residuals, not a certified floating-point error bound or branch-selection proof.
Zero-mode placeholders are checked separately and are NOT S1 evaluations.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import sys

# Exact values of the binary64 defaults used by this build, not decimal reals.
TOL_ZERO = F(1e-12)
LIMITONE = F(1.0 / (1e-6 * 4.0))
LIMITTWO = F(0.5**2)
SEXCUT = F(4)
ABS_TOL = F(1, 10**10)  # Empirical regression threshold, not a physical bound.
OMEGA_REL_TOL = F(1, 10**12)
COLS = ("rec n1true iw igp ig occ vcoul ieps wtilde wxt omega2 ssx sch "
        "e_lk e_n1kq").split()
PROFILES = {
    "gpp_kernel_dump.dat": (64, {1: 34, 3: 30}, "after_sexcut"),
    "gpp_nearpole_dump.dat": (32, {2: 32}, "before_sexcut"),
}
EXPORT_FILES = set(PROFILES) | {
    "gpp_branch_counts.dat", "sigma_hp.log", "instrument.patch", "arch.mk",
    "epsilon.inp", "sig_GPP.inp", "WFN.in", "WFNq.in", "WFN_co.in",
}


def load(path):
    rows = []
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != len(COLS):
            raise ValueError(f"line {number}: expected {len(COLS)} columns")
        row = {c: (int(v) if i < 5 else float(v))
               for i, (c, v) in enumerate(zip(COLS, fields))}
        if not all(math.isfinite(row[c]) for c in COLS[5:]):
            raise ValueError(f"line {number}: nonfinite input or output")
        if row["rec"] != len(rows) + 1 or any(row[c] <= 0 for c in COLS[:5]):
            raise ValueError(f"line {number}: invalid or repeated record index")
        rows.append(row)
    if not rows:
        raise ValueError("empty export cannot establish agreement")
    return rows


def predict(r, capture="after_sexcut"):
    """Exact-real branch formulas; predicates are not IEEE emulation."""
    if capture not in {"before_sexcut", "after_sexcut"}:
        raise ValueError("unknown capture stage")
    ieps, wt, x = F(r["ieps"]), F(r["wtilde"]), F(r["wxt"])
    if wt < 0 or (wt == 0 and ieps != 0) or x in (wt, -wt):
        raise ValueError("unsupported pole/domain in the saved-export contract")
    omega2 = wt**2 * ieps
    wdiff = x - wt
    delw = wt / wdiff
    if wdiff**2 > LIMITTWO and delw**2 < LIMITONE:
        branch, sch, ssx = 1, delw * ieps, omega2 / (x**2 - wt**2)
    elif delw**2 > TOL_ZERO:
        branch, sch = 2, F(0)
        ssx = -omega2 * delw / (4 * wt**2 * (delw + F(1, 2)))
    else:
        branch, sch, ssx = 3, F(0), F(0)
    clamped = abs(ssx) > SEXCUT * abs(ieps) and x < 0
    if capture == "after_sexcut" and clamped:
        ssx = F(0)
    return branch, ssx, sch, omega2, clamped


def verify_rows(rows, profile):
    count, expected_branches, capture = PROFILES[profile]
    if len(rows) != count:
        raise ValueError(f"{profile}: expected {count} records, got {len(rows)}")
    out, branches = [], {}
    worst_ssx = worst_sch = worst_s1 = worst_omega = F(0)
    comparisons = nontrivial = placeholders = 0
    for r in rows:
        if r["occ"] != 1:
            raise ValueError("saved-export comparison requires full occupation")
        branch, ssx, sch, A, clamped = predict(r, capture)
        branches[branch] = branches.get(branch, 0) + 1
        # The saved sets have no clamp events. A later dataset needs its own scope.
        if clamped:
            raise ValueError("clamped record is outside this S1 comparison")
        dssx, dsch = abs(F(r["ssx"]) - ssx), abs(F(r["sch"]) - sch)
        domega = abs(F(r["omega2"]) - A) / max(F(1), abs(A))
        worst_ssx, worst_sch = max(worst_ssx, dssx), max(worst_sch, dsch)
        worst_omega = max(worst_omega, domega)
        code_value = -F(r["ssx"]) + F(1, 2) * F(r["sch"])
        wt, x = F(r["wtilde"]), F(r["wxt"])
        s1_value = d_s1 = None
        if wt == 0:
            if branch not in (1, 3) or any(r[c] != 0 for c in ("ieps", "omega2", "ssx", "sch")):
                raise ValueError("invalid zero-mode placeholder")
            placeholders += 1
        elif branch in (1, 2):
            s1_value = A / (2 * wt * (x + wt))
            if branch == 1:
                raw = -A / (x**2 - wt**2) + A / (2 * wt * (x - wt))
                if raw != s1_value:
                    raise ValueError("exact raw/merged identity failed")
            d_s1 = abs(code_value - s1_value)
            worst_s1 = max(worst_s1, d_s1)
            comparisons += 1
        nontrivial += A != 0
        out.append(dict(rec=r["rec"], branch_predicted=branch,
                        omega2_relative_residual=float(domega),
                        ssx_error=float(dssx), sch_error=float(dsch),
                        s1_error=None if d_s1 is None else float(d_s1)))
    if branches != expected_branches or comparisons == 0 or nontrivial != comparisons:
        raise ValueError("missing nontrivial S1/branch coverage in saved export")
    if max(worst_ssx, worst_sch, worst_s1) > ABS_TOL or worst_omega > OMEGA_REL_TOL:
        raise ValueError("exported arithmetic disagrees with the regression oracle")
    return dict(records=len(rows), capture_stage=capture, branches_predicted=branches,
                records_with_nonzero_omega2=nontrivial, s1_comparisons=comparisons,
                zero_placeholders=placeholders,
                max_abs_error_ssx=float(worst_ssx), max_abs_error_sch=float(worst_sch),
                max_abs_error_vs_S1_closed_form=float(worst_s1),
                max_relative_residual_omega2=float(worst_omega), rows=out)


def check_manifest(directory):
    directory = Path(directory)
    seen = set()
    for line in (directory / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split()
        if name not in EXPORT_FILES or name in seen:
            raise ValueError("unexpected or duplicate export manifest entry")
        if hashlib.sha256((directory / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"checksum mismatch: {name}")
        seen.add(name)
    actual = {p.name for p in directory.iterdir()}
    if seen != EXPORT_FILES or actual != EXPORT_FILES | {"SHA256SUMS"}:
        raise ValueError("missing or extra export evidence")
    return len(seen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", type=Path)
    parser.add_argument("--all", action="store_true", help="check saved checksums and both sets")
    args = parser.parse_args()
    directory = Path(__file__).parent / "export"
    try:
        if args.all:
            if args.path:
                parser.error("--all does not take a path")
            result = {"checksummed_files": check_manifest(directory), "exports": {
                name: verify_rows(load(directory / name), name) for name in PROFILES}}
        else:
            path = args.path or directory / "gpp_kernel_dump.dat"
            if path.name not in PROFILES:
                raise ValueError("filename must identify one of the two saved-export profiles")
            result = verify_rows(load(path), path.name)
        print(json.dumps(result, indent=2))
        return 0
    except (ValueError, OSError, ZeroDivisionError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

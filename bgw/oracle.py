#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Exact-rational check of the BerkeleyGW 4.0 GPP kernel transcript.

Reads the output of `kernel_transcript.f90` and, for each row, recomputes the
merged occupied value `Omega2 / (2*wtilde*(wxt + wtilde))` exactly over the
rationals, using `Fraction.from_float` on the SAME binary64 `wxt` the Fortran
program used.  As in Specification.md S4, this separates input rounding from
evaluation error: the exact value is the exact value *of the float input*.

This is a numerical experiment about one compiled transcript, not a proved
floating-point error bound, and not a run of BerkeleyGW.
"""

from fractions import Fraction
import json
import math
import pathlib
import sys

from verify_export import predict

I_EPS = Fraction(1)
WTILDE = Fraction(1)
OMEGA2 = WTILDE**2 * I_EPS


def merged(x: Fraction) -> Fraction:
    """S1 merged expression; branch equivalence requires nonzero denominators."""
    return OMEGA2 / (2 * WTILDE * (x + WTILDE))


def raw_split(x: Fraction) -> Fraction:
    """S1 `rawOccupied` = BerkeleyGW generic branch, exact. Undefined at x=+-w."""
    if x**2 - WTILDE**2 == 0 or x - WTILDE == 0:
        raise ZeroDivisionError("raw split is undefined at x = +-wtilde")
    return -OMEGA2 / (x**2 - WTILDE**2) + OMEGA2 / (2 * WTILDE * (x - WTILDE))


def main(path: str) -> int:
    rows = []
    for line in pathlib.Path(path).read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        f = line.split()
        if len(f) != 8 or not all(math.isfinite(float(v)) for v in f):
            raise ValueError("expected eight finite transcript fields")
        rows.append(
            dict(
                offset=float(f[0]),
                wxt=float(f[1]),
                branch=int(f[2]),
                sch=float(f[3]),
                ssx=float(f[4]),
                occupied=float(f[5]),
                empty=float(f[6]),
                occupied_times_ryd=float(f[7]),
            )
        )

    if len(rows) != 17 or len({r["wxt"] for r in rows}) != 17:
        raise ValueError("expected 17 distinct scan points")
    if any(r["offset"] <= 0 or r["wxt"] != 1.0 + r["offset"] for r in rows):
        raise ValueError("invalid transcript scan inputs")
    if [r["branch"] for r in rows] != [1] + [2] * 16:
        raise ValueError("expected one generic and sixteen near-pole points")
    results, worst = [], Fraction(0)
    for r in rows:
        branch, ssx, sch, _, clamped = predict(
            dict(ieps=1.0, wtilde=1.0, wxt=r["wxt"]))
        if branch != r["branch"] or clamped:
            raise ValueError("unexpected branch or clamp in scan")
        for got, expected in ((r["ssx"], ssx), (r["sch"], sch),
                              (r["empty"], sch / 2)):
            if abs(Fraction(got) - expected) > Fraction(1, 10**14):
                raise ValueError("transcript component mismatch")
        if r["occupied"] != -r["ssx"] + 0.5 * r["sch"]:
            raise ValueError("occupied accumulation mismatch")
        if r["occupied_times_ryd"] != r["occupied"] * 13.60569253:
            raise ValueError("RYD diagnostic mismatch")
        x = Fraction(r["wxt"])            # exact value of the binary64 input
        exact = merged(x)
        got = Fraction(r["occupied"])     # exact value of the binary64 output
        err = abs(got - exact)
        worst = max(worst, err)
        # The generic branch must also agree with the raw split, exactly.
        raw_ok = None
        if r["branch"] == 1:
            raw_ok = raw_split(x) == exact
        results.append(
            dict(
                offset=r["offset"],
                branch=r["branch"],
                exact_merged=str(exact),
                fortran=repr(r["occupied"]),
                abs_error=float(err),
                ulps=float(err / Fraction(math.ulp(r["occupied"]))),
                raw_equals_merged_exactly=raw_ok,
            )
        )

    limit = Fraction(1, 4)
    near = [r for r in rows if r["branch"] == 2]
    out = dict(
        source="BerkeleyGW-4.0 Sigma/mtxel_cor.f90 sigma_gpp_cpu (transcribed)",
        i_eps="1", wtilde="1", omega2=str(OMEGA2),
        gpp_broadening="0.5", gpp_sexcutoff="4.0",
        branch_counts={b: sum(1 for r in rows if r["branch"] == b) for b in (1, 2, 3)},
        extension_value=str(OMEGA2 / (4 * WTILDE**2)),
        limit_check=dict(
            smallest_offset=min(r["offset"] for r in near),
            occupied_there=repr(min(near, key=lambda r: r["offset"])["occupied"]),
            distance_to_extension_value=float(
                abs(Fraction(min(near, key=lambda r: r["offset"])["occupied"]) - limit)
            ),
        ),
        max_abs_error_vs_exact_merged=float(worst),
        rows=results,
    )
    json.dump(out, sys.stdout, indent=2)
    print()
    bad = [r for r in results if r["raw_equals_merged_exactly"] is False]
    if bad:
        print("MISMATCH: generic branch disagrees with merged form", file=sys.stderr)
        return 1
    if worst > Fraction(1, 10**14):
        print(f"MISMATCH: max error {float(worst)} too large", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1] if len(sys.argv) > 1 else "kt.out"))
    except (ValueError, OSError, ZeroDivisionError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)

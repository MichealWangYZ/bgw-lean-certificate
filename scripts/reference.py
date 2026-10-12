#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): Specification.md v0.1 demo lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and GW.Bridge; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Independent exact oracle and binary64 experiment, not a formal proof."""

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Term:
    coefficient: Q
    omega: Q
    epsilon: Q
    occupied: bool


def term_value(term, energy):
    if term.omega <= 0:
        raise ValueError("pole energy must be positive")
    gap = energy - term.epsilon
    denominator = 2 * term.omega * (gap + term.omega if term.occupied else gap - term.omega)
    if denominator == 0:
        raise ValueError("surviving denominator is zero")
    return term.coefficient / denominator


def sigma(terms, energy, sigma_x):
    return sigma_x + sum((term_value(t, energy) for t in terms), Q(0))


def raw_value(coefficient, gap, omega):
    if omega <= 0 or gap == omega or gap == -omega:
        raise ValueError("raw split expression is undefined")
    return -coefficient / (gap * gap - omega * omega) + coefficient / (2 * omega * (gap - omega))


def load_fixture():
    data = json.loads((ROOT / "fixtures/synthetic-three-term.json").read_text())
    terms = [Term(Q(t["coefficient"]), Q(t["omega"]), Q(t["epsilon"]), t["occupied"]) for t in data["terms"]]
    return data, terms, Q(data["energy"]), Q(data["sigma_x"])


def rejects(term, energy):
    try:
        term_value(term, energy)
    except ValueError:
        return True
    return False


def expected_output():
    data, terms, energy, static = load_fixture()
    probe = Term(Q(4), Q(1), Q(0), True)
    return {
        "fixture": data["id"],
        "terms": [str(term_value(t, energy)) for t in terms],
        "sigma": str(sigma(terms, energy, static)),
        "occupied_at_pole": str(term_value(probe, Q(1))),
        "reject_zero_omega": rejects(replace(probe, omega=Q(0)), Q(1)),
        "reject_negative_omega": rejects(replace(probe, omega=Q(-1)), Q(1)),
        "reject_occupied_pole": rejects(probe, Q(-1)),
        "reject_empty_pole": rejects(replace(probe, occupied=False), Q(1)),
        "empty_sum": str(sigma([], energy, static)),
    }


def numerical_experiment():
    rows = []
    for offset in [1e-2, 1e-6, 1e-8, 1e-10, 1e-12, 1e-14, math.ulp(1.0), 0.0]:
        x = 1.0 + offset
        exact = Q(4) / (2 * (Q.from_float(x) + 1))
        merged = 4.0 / (2.0 * (x + 1.0))
        split = None if x == 1.0 else -4.0 / (x*x - 1.0) + 4.0 / (2.0 * (x - 1.0))
        rows.append({
            "x_hex": x.hex(), "actual_offset": x - 1.0,
            "exact_for_binary64_input": str(exact), "raw": split, "merged": merged,
            "raw_abs_error": None if split is None else float(abs(Q.from_float(split) - exact)),
            "merged_abs_error": float(abs(Q.from_float(merged) - exact)),
        })
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-json", type=Path, help="compare actual Lean JSON against this oracle")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    expected = expected_output()
    data, _, _, _ = load_fixture()
    if expected["terms"] != data["expected_terms"] or expected["sigma"] != data["expected_sigma"]:
        raise AssertionError("fixture labels disagree with independently calculated values")
    if args.lean_json:
        actual = json.loads(args.lean_json.read_text())
        if actual != expected:
            raise AssertionError(f"Lean/oracle mismatch\nexpected={expected}\nactual={actual}")
        print("Lean output agrees with the independent exact oracle.")
    print(f"Synthetic fixture: terms={expected['terms']}; Sigma={expected['sigma']} eV")
    print("Binary64 experiment: A=4, w=1, x approaches 1 from above")
    print("offset          split abs error   merged abs error")
    rows = numerical_experiment()
    for row in rows:
        split = "undefined" if row["raw_abs_error"] is None else f"{row['raw_abs_error']:.6e}"
        print(f"{row['actual_offset']:<15.6e} {split:<17} {row['merged_abs_error']:.6e}")
    print("At x=w the occupied extension is 1; the raw split is undefined.")
    print("This is an experiment, not a floating-point stability proof.")
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        report = {"fixture": expected, "experiment": rows, "claim": "numerical observation only"}
        (args.output_dir / "numerical-demo.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())


#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Regenerate the LL-C1 comparison/mutation report from actual computation.

Deterministic. Reads the Lean evaluator's emitted values, recomputes every
number with the independent Python reference, recomputes every mutant, and
writes the observed outcomes. Nothing here is a hand-authored success claim:
every `exact_match` and `detected` field is the result of a comparison made
while this script runs.

    python3 ll/make_comparison.py \
        --lean artifacts/ll-c1/lean_values.json \
        --out  artifacts/ll-c1/comparison.json

`artifacts/ll-c1/lean_values.json` is produced by the Lean binary:

    lake build ll_c1_eval && ./.lake/build/bin/ll_c1_eval > artifacts/ll-c1/lean_values.json
"""

import argparse
import importlib.util
import json
import pathlib
from fractions import Fraction as F
from itertools import product

ROOT = pathlib.Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location(
    "ll_ring_reference", ROOT / "ll" / "ring_reference.py")
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

_espec = importlib.util.spec_from_file_location(
    "ll_evidence", ROOT / "ll" / "evidence.py")
evidence = importlib.util.module_from_spec(_espec)
_espec.loader.exec_module(evidence)

WITNESS = "N2-pd-unequal-ext"


def contract(fx, k, edges, sign_offset=0, divide=True):
    G, v, i, j = fx["G"], fx["v"], fx["i"], fx["j"]
    n = len(G)
    props, ints = edges
    internal = [s for m in range(k) for s in (('a', m), ('b', m))]
    total = F(0)
    for assignment in product(range(n), repeat=len(internal)):
        idx = dict(zip(internal, assignment))
        idx[('e', 0)], idx[('e', 1)] = i, j
        term = F(1)
        for (u, w) in props:
            term *= G[idx[u]][idx[w]]
        for (u, w) in ints:
            term *= v[idx[u]][idx[w]]
        total += term
    divisor = ref.symmetry_factor(k) if divide else 1
    return ((-1) ** (len(ints) + sign_offset)) * total / divisor


def wrong_site_edges(k):
    """Chain attached to the wrong bubble site: a genuine topology error."""
    extI, extJ = ('e', 0), ('e', 1)
    props = [(extI, extJ)]
    for m in range(k):
        props += [(('a', m), ('b', m))] * 2
    ints = ([(extI, ('a', 0))]
            + [(('a', m), ('a', m + 1)) for m in range(k - 1)]
            + [(('a', k - 1), extJ)])
    return props, ints


def build(lean_path):
    lean = json.loads(pathlib.Path(lean_path).read_text())
    # LL-C2A 2.1: the generator validates through the same module the tests
    # use, and checks the symmetry metadata against an independent constant
    # instead of copying the candidate's own claim.
    symmetry = evidence.validate_symmetry_factors(lean)
    rows = evidence.validate_rows(lean, ref.FIXTURES)
    out = {
        "source": lean["source"],
        "generated_by": "ll/make_comparison.py",
        "symmetry_factors_checked_against_paper": symmetry,
        "comparisons": [],
        "mutations": [],
    }
    for name, fx in ref.FIXTURES.items():
        for k in (0, 1, 2):
            expected = ref.both_agree(fx["G"], fx["v"], fx["i"], fx["j"], k)
            got = F(rows[name][f"ring{k}"])
            out["comparisons"].append(
                {"fixture": name, "k": k, "lean": str(got),
                 "python": str(expected), "exact_match": got == expected})

    fx = ref.FIXTURES[WITNESS]
    for k in (0, 1, 2):
        good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
        bad = contract(fx, k, ref.ring_edges(k), sign_offset=1)
        out["mutations"].append(
            {"witness": WITNESS, "k": k, "mutant": "sign_rule_off_by_one",
             "correct": str(good), "mutated": str(bad), "detected": good != bad})
    for k in (1, 2):
        good = ref.ring_contribution_contraction(fx["G"], fx["v"], fx["i"], fx["j"], k)
        for label, bad in (
                ("symmetry_factor_omitted",
                 contract(fx, k, ref.ring_edges(k), divide=False)),
                ("chain_attached_to_wrong_bubble_site",
                 contract(fx, k, wrong_site_edges(k)))):
            out["mutations"].append(
                {"witness": WITNESS, "k": k, "mutant": label,
                 "correct": str(good), "mutated": str(bad), "detected": good != bad})

    out["all_comparisons_exact"] = all(c["exact_match"] for c in out["comparisons"])
    out["all_mutants_detected"] = all(m["detected"] for m in out["mutations"])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default=str(ROOT / "artifacts/ll-c1/lean_values.json"))
    ap.add_argument("--out", default=str(ROOT / "artifacts/ll-c1/comparison.json"))
    args = ap.parse_args()
    try:
        out = build(args.lean)
    except evidence.EvidenceError as exc:
        print(f"FAIL: invalid evidence table: {exc}", file=__import__("sys").stderr)
        return 2
    dest = pathlib.Path(args.out)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(out, indent=2) + "\n")
    print(f"comparisons {len(out['comparisons'])} all_exact={out['all_comparisons_exact']}")
    print(f"mutations   {len(out['mutations'])} all_detected={out['all_mutants_detected']}")
    return 0 if out["all_comparisons_exact"] and out["all_mutants_detected"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

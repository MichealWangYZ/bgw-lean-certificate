#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Regenerate the Lean certificate literals and check them against the snapshot.

    python3 bgw/m1_screening/regenerate_certificate.py --check

Deterministic: reads only the committed dump slice, recomputes the exact
reference by rational elimination, and compares the three matrices against the
literals in `GW/BGW/M1Screening.lean`. Exits non-zero on any mismatch.

This is a regeneration check, not a rewriter: it never edits the Lean file, so
a drifted snapshot fails instead of being silently replaced.
"""

import argparse
import importlib.util
import pathlib
import re
import sys
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[2]


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def lean_matrix(text, name, n):
    m = re.search(rf"def {name} : Matrix \(Fin {n}\) \(Fin {n}\) ℚ :=\s*!!\[(.*?)\]\n",
                  text, re.S)
    if m is None:
        raise SystemExit(f"no literal for {name}")
    rows = m.group(1).split(";")
    out = []
    for row in rows:
        ent = re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", row)
        out.append([F(int(a), int(b)) for a, b in ent])
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="compare against the committed Lean module (default)")
    ap.parse_args(argv)

    extract = _load("m1x", "bgw/m1_screening/extract.py")
    ref = _load("m1r", "bgw/m1_screening/reference.py")
    dump = ROOT / "bgw/m1_screening/data/m1_eps_dump_q2.txt"
    lean = ROOT / "GW/BGW/M1Screening.lean"

    block = extract.load_single(dump, 2, expected_n=8, expected_q=(0.0, 0.0, 0.5))
    E, X, v = extract.matrices(block)
    n = len(E)
    R = ref.exact_inverse(E)
    V = [[v[a] if a == b else F(0) for b in range(n)] for a in range(n)]

    text = lean.read_text()
    bad = []
    for name, want in (("E", E), ("V", V), ("Rref", R)):
        if lean_matrix(text, name, n) != want:
            bad.append(name)
    if bad:
        print(f"MISMATCH: regenerated {bad} differ from {lean.name}", file=sys.stderr)
        return 1
    print(f"OK: E, V and Rref in {lean.name} match regeneration from "
          f"{dump.name} (n={n})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

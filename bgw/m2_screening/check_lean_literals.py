#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Check that GW/BGW/M2Screening.lean's literals are exactly this export."""
import importlib.util, pathlib, re, sys
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[2]


def _load(n, rel):
    s = importlib.util.spec_from_file_location(n, ROOT / rel)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


x = _load("m2x", "bgw/m2_screening/extract.py")
ref = _load("m2r", "bgw/m2_screening/reference.py")
text = (ROOT / "GW/BGW/M2Screening.lean").read_text()
b = x.load_single(ROOT / "bgw/m2_screening/data/m2_dump_q2.txt",
                  "m2-20260917-q2-cut15", 2, expected_n=8, expected_q=(0.0, 0.0, 0.5))
chi, v, Ehat, Xhat, _ = x.matrices(b)
Es = ref.e_star(chi, v)
Rs = ref.exact_inverse(Es)


def mat(name):
    m = re.search(rf"def {name} : Matrix \(Fin 8\) \(Fin 8\) ℚ :=\s*!!\[(.*?)\]\n",
                  text, re.S)
    return [[F(int(a), int(c)) for a, c in
             re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", row)]
            for row in m.group(1).split(";")]


def vec(name):
    m = re.search(rf"def {name} : Fin 8 → ℚ :=\s*!\[(.*?)\]\n", text, re.S)
    return [F(int(a), int(c)) for a, c in
            re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℚ\s*\)", m.group(1))]


bad = [n for n, want in (("chi", chi), ("Xhat", Xhat), ("Estar", Es), ("Rstar", Rs))
       if mat(n) != want]
if vec("vc") != v:
    bad.append("vc")
if bad:
    print(f"  Lean literals MISMATCH: {bad}", file=sys.stderr)
    sys.exit(1)
print("  Lean literals match this export (chi, vc, Xhat, Estar, Rstar)")

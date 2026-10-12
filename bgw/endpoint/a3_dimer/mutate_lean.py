#!/usr/bin/env python3
"""Discriminating mutations of the A3(b) Hubbard-dimer Lean files.

    python3 bgw/endpoint/a3_dimer/mutate_lean.py [--log FILE] [--only TAG ...]

Each mutant is a physically plausible slip (wrong sign in W, factor 2 in a pole
or residue, missing spin factor, missing exchange, linearised QP, wrong power
or wrong leading coefficient in the bound, wrong ground state, no
Jordan-Wigner string). A mutant PASSES the test ("OK") iff Lean rejects it and
every theorem listed as expected is among the declarations reporting errors.
The observed failing set is logged in full. The control (unmutated file) must
compile with no errors. Needs `lake` on PATH (source scripts/env.sh) and the
built oleans of GW.Endpoint.HubbardDimerFock / HubbardDimerExact.
"""
import argparse
import hashlib
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
FILES = {
    "fock": ROOT / "GW/Endpoint/HubbardDimerFock.lean",
    "exact": ROOT / "GW/Endpoint/HubbardDimerExact.lean",
    "gw": ROOT / "GW/Endpoint/HubbardDimer.lean",
}


def sub1(text, old, new):
    if text.count(old) != 1:
        raise SystemExit(f"mutation anchor not unique ({text.count(old)}x): {old!r}")
    return text.replace(old, new)


def cases():
    g = FILES["gw"].read_text()
    e = FILES["exact"].read_text()
    f = FILES["fock"].read_text()
    return [
        ("control-gw", "gw", g, set()),
        ("control-exact", "exact", e, set()),
        # --- GW side
        ("W-sign", "gw",
         sub1(g, "Matrix.of fun i j => sgn i * sgn j * (2 * t * U ^ 2 / (ω ^ 2 - hRPA t U ^ 2))",
              "Matrix.of fun i j => -(sgn i * sgn j * (2 * t * U ^ 2 / (ω ^ 2 - hRPA t U ^ 2)))"),
         {"rpa_solves", "Wc_single_pole"}),
        ("pole-factor-2", "gw",
         sub1(g, "Real.sqrt (4 * t ^ 2 + 4 * t * U)", "Real.sqrt (4 * t ^ 2 + 8 * t * U)"),
         {"hRPA_sq"}),
        ("residue-factor-2", "gw",
         sub1(g, "Matrix.of fun i j => sgn i * sgn j * (t * U ^ 2 / hRPA t U)",
              "Matrix.of fun i j => sgn i * sgn j * (2 * t * U ^ 2 / hRPA t U)"),
         {"Wc_single_pole", "sigmaC_orbital"}),
        ("sigma-pole-factor-2", "gw",
         sub1(g, "t * U ^ 2 / hRPA t U / (E - epsA t U - hRPA t U)",
              "t * U ^ 2 / hRPA t U / (E - epsA t U - 2 * hRPA t U)"),
         {"sigmaC_orbital", "qp_removal"}),
        ("no-spin-factor", "gw",
         sub1(g, "Matrix.of fun i j => 2 * (phiB i * phiA i) * (phiA j * phiB j) *",
              "Matrix.of fun i j => (phiB i * phiA i) * (phiA j * phiB j) *"),
         {"chi0_eq"}),
        ("no-exchange", "gw",
         sub1(g, "h0 t + U • Matrix.diagonal (fun i => 2 * rhoSpin i i) - U • Matrix.diagonal (fun i => rhoSpin i i)",
              "h0 t + U • Matrix.diagonal (fun i => 2 * rhoSpin i i)"),
         {"fock_eq"}),
        ("linearised-QP", "gw",
         sub1(g, "noncomputable def Erem (t U : ℝ) : ℝ := epsB t U + ((2 * t + hRPA t U) - Dgw t U) / 2",
              "noncomputable def Erem (t U : ℝ) : ℝ := epsB t U + sigBB t U (epsB t U)"),
         {"qp_removal"}),
        ("bound-power-3", "gw",
         sub1(g, "    |gapGW t U - gapExact t U| ≤ (1 / 8) * U ^ 2 / t := by",
              "    |gapGW t U - gapExact t U| ≤ (1 / 8) * U ^ 3 / t ^ 2 := by"),
         {"gw_error_abs"}),
        ("bound-coeff-1/16", "gw",
         sub1(g, "      gapGW t U - gapExact t U ≤ U ^ 2 / (8 * t) - U ^ 3 / (16 * t ^ 2) := by",
              "      gapGW t U - gapExact t U ≤ U ^ 2 / (16 * t) - U ^ 3 / (16 * t ^ 2) := by"),
         {"gw_error_bounds"}),
        ("leading-coeff-HF-sign", "gw",
         sub1(g, "    Tendsto (fun U => (gapHF t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (-(1 / (8 * t)))) := by",
              "    Tendsto (fun U => (gapHF t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by"),
         {"hf_error_leading"}),
        # --- exact side
        ("E0-2-wrong-root", "exact",
         sub1(e, "theorem ground_two {t U : ℝ} (ht : 0 < t) : IsSectorGround t U 2 ((U - rEx t U) / 2) := by",
              "theorem ground_two {t U : ℝ} (ht : 0 < t) : IsSectorGround t U 2 ((U + rEx t U) / 2) := by"),
         {"ground_two"}),
        ("E0-3-excited-state", "exact",
         sub1(sub1(e, "theorem ground_three {t U : ℝ} (ht : 0 ≤ t) : IsSectorGround t U 3 (U - t) := by",
                   "theorem ground_three {t U : ℝ} (ht : 0 ≤ t) : IsSectorGround t U 3 (U + t) := by"),
              "  refine ⟨⟨![0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0], ?_, ?_, ?_⟩, ?_⟩",
              "  refine ⟨⟨![0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0], ?_, ?_, ?_⟩, ?_⟩"),
         {"ground_three"}),
        # --- Fock side
        ("hopping-sign", "fock",
         sub1(f, "  (-t) • hopZ.map (Int.cast : ℤ → ℝ) + U • dblZ.map (Int.cast : ℤ → ℝ)",
              "  t • hopZ.map (Int.cast : ℤ → ℝ) + U • dblZ.map (Int.cast : ℤ → ℝ)"),
         {"H_mulVec"}),
        ("no-jordan-wigner", "fock",
         sub1(f, "def jw (s : Fin 16) (m : Fin 4) : ℤ := (-1) ^ below s m",
              "def jw (s : Fin 16) (m : Fin 4) : ℤ := 1"),
         {"car_anti", "hopZ_eq"}),
    ]


def run_module(text, tag):
    path = ROOT / "GW" / "Endpoint" / f"HubbardDimerMutant_{re.sub(r'[^A-Za-z0-9]', '_', tag)}.lean"
    path.write_text(text)
    try:
        exe = shutil.which("lake")
        if exe is None:
            raise SystemExit("lake not on PATH: source scripts/env.sh first")
        rc = subprocess.run([exe, "env", "lean", str(path.relative_to(ROOT))], cwd=ROOT,
                            capture_output=True, text=True)
        return rc.returncode, rc.stdout + rc.stderr
    finally:
        path.unlink(missing_ok=True)


def failing_decls(output, text):
    starts = []
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r"(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([\w.]+)", line)
        if m:
            starts.append((i, m.group(2)))
    names = set()
    for m in re.finditer(r":(\d+):\d+: error", output):
        ln = int(m.group(1))
        owner = None
        for start, name in starts:
            if start <= ln:
                owner = name
        names.add(owner or "<header>")
    return names


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--log")
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args(argv)
    lines = ["A3(b) Hubbard dimer: discriminating Lean mutations"]
    for k, p in FILES.items():
        lines.append(f"{p.relative_to(ROOT)} sha256: {hashlib.sha256(p.read_bytes()).hexdigest()}")
    lines.append("")
    ok = True
    for tag, which, body, expected in cases():
        if a.only and tag not in a.only:
            continue
        rc, out = run_module(body, tag)
        got = failing_decls(out, body) if rc != 0 else set()
        if expected:
            verdict = "OK" if rc != 0 and expected <= got else "FAIL"
        else:
            verdict = "OK" if rc == 0 and "error" not in out else "FAIL"
        ok &= verdict == "OK"
        lines.append(f"{tag:22s} file={which:5s} rc={rc} failing={sorted(got)} "
                     f"expected>={sorted(expected)} {verdict}")
        print(lines[-1], flush=True)
    lines.append("ALL OK" if ok else "SOME MUTATION DID NOT DISCRIMINATE")
    print(lines[-1])
    if a.log:
        pathlib.Path(a.log).write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

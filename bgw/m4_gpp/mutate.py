#!/usr/bin/env python3
"""Discriminating mutations of the M4 certificate, run through Lean.

    python3 bgw/m4_gpp/mutate.py              # report
    python3 bgw/m4_gpp/mutate.py --log FILE   # also write the evidence log

Each mutant edits the generated module in ONE place and must fail at EXACTLY
the named obligations, no more and no fewer; the unmodified control must
elaborate. A parse error or a failure elsewhere does not count.

  wrong-source  The map points at M2 entry (1,3) instead of (1,2), and the M2
                side is kept self-consistent (restated Xhat and Rstar literals
                of (1,3)). Production I, Omega2, wtilde2 are untouched and
                still satisfy their own division. Must fail: `map_bound`.
  no-wing       The wing normalization is dropped (kappa := 1), the error an
                identity-label comparison makes. Must fail: `map_bound`.
  phase         One gmap phase is flipped (+1 -> -1), a nontrivial phase
                error the all-+1 target would otherwise never exercise.
                Must fail: `formation_bound` (the consumed operand was formed
                with the true phase) and `PStar_pos` (the reference changes
                sign).
  primitive     One primitive operand of Omega2, rho(G-G'), is moved by one
                part in 1e9; the production witness is untouched.
                Must fail: `omega_bound`.
  division      Production wtilde2 is moved by 2^-40 relative while Omega2
                and I stay put: a local arithmetic violation.
                Must fail: `div_bound`.

Mutant modules are written beside the real one, elaborated, and deleted.
"""
import argparse
import hashlib
import pathlib
import re
import shutil
import subprocess
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "GW" / "BGW" / "M4GPP.lean"
sys.path.insert(0, str(HERE))
import bridge  # noqa: E402
import make_lean  # noqa: E402


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sub1(text, old, new):
    if text.count(old) != 1:
        raise SystemExit(f"mutation anchor not unique: {old[:80]!r}")
    return text.replace(old, new)


def def_line(text, name):
    m = re.search(rf"^def {name} : ℚ := .*$", text, re.M)
    if not m:
        raise SystemExit(f"no definition {name}")
    return m.group(0)


def mutants(text, res):
    m2 = bridge.load_m2()
    x13 = bridge.q64(m2["xbits"][(1, 3)])
    r13 = m2["rstar"][0][2]
    c = res["cert"]
    out = {}

    t = sub1(text, "def srcCol : Fin 8 := 1", "def srcCol : Fin 8 := 2")
    t = sub1(t, def_line(t, "xhatLit"), f"def xhatLit : ℚ := {make_lean.q(x13)}")
    t = sub1(t, f"M2.Rstar srcRow srcCol = {make_lean.q(c['rstar'])}",
             f"M2.Rstar srcRow srcCol = {make_lean.q(r13)}")
    out["wrong-source"] = (t, {"map_bound"})

    out["no-wing"] = (sub1(text, "def kappa : ℚ := wFact * wOneOverQ / (wVcoul1 * wQlen)",
                           "def kappa : ℚ := 1"), {"map_bound"})

    out["phase"] = (sub1(text, def_line(text, "phA"), "def phA : ℚ := (-1 / 1 : ℚ)"),
                    {"formation_bound", "PStar_pos"})

    rho = c["prims"]["rho"]
    out["primitive"] = (sub1(text, def_line(text, "rhoGG"),
                             f"def rhoGG : ℚ := {make_lean.q(rho * (1 + F(1, 10 ** 9)))}"),
                        {"omega_bound"})

    out["division"] = (sub1(text, def_line(text, "Phat"),
                            f"def Phat : ℚ := {make_lean.q(c['p_hat'] * (1 + F(1, 2 ** 40)))}"),
                       {"div_bound"})
    return out


def _lake():
    exe = shutil.which("lake")
    if exe is None:
        raise SystemExit("lake not on PATH: source scripts/env.sh first")
    return exe


def run_module(text, tag):
    path = ROOT / "GW" / "BGW" / f"M4Mutant_{tag.replace('-', '_')}.lean"
    path.write_text(text)
    try:
        rc = subprocess.run([_lake(), "env", "lean", str(path.relative_to(ROOT))],
                            cwd=ROOT, capture_output=True, text=True)
        return rc.returncode, rc.stdout + rc.stderr
    finally:
        path.unlink(missing_ok=True)


def failing_decls(output, text):
    """Declarations containing reported errors (theorems AND definitions)."""
    starts = []
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r"(theorem|lemma|def|abbrev)\s+(\w+)", line)
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
    a = ap.parse_args(argv)
    res = bridge.run()
    text = make_lean.render(res)
    if LEAN.read_text() != text:
        raise SystemExit("M4GPP.lean is not the generated module; run make_lean.py --check")
    lines = ["BGW-M4-R1 discriminating certificate mutations", "",
             f"M4GPP.lean sha256: {sha256(LEAN)}",
             f"mutate.py sha256: {sha256(pathlib.Path(__file__))}",
             f"m4r1_dump.dat.gz sha256: {sha256(bridge.DUMP)}", "",
             "Each mutant must fail at exactly the expected declarations; the control must elaborate.", ""]
    ok = True
    cases = [("control", text, set())] + [(k, v[0], v[1]) for k, v in mutants(text, res).items()]
    for tag, body, expected in cases:
        rc, out = run_module(body, tag)
        got = failing_decls(out, body) if rc != 0 else set()
        verdict = "OK" if (got == expected and (rc == 0) == (not expected)) else "FAIL"
        ok &= verdict == "OK"
        lines += [f"--- {tag} ---",
                  f"lean exit code         : {rc}",
                  f"expected failing decls : {sorted(expected)}",
                  f"actual failing decls   : {sorted(got)}",
                  f"verdict                : {verdict}", ""]
        print(f"{tag:14s} rc={rc} got={sorted(got)} expected={sorted(expected)} {verdict}")
    lines.append("ALL OK" if ok else "SOME MUTATION DID NOT DISCRIMINATE")
    if a.log:
        pathlib.Path(a.log).write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

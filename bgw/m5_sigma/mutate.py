#!/usr/bin/env python3
"""Discriminating mutations of the M5 certificate, run through Lean.

    python3 bgw/m5_sigma/mutate.py [--log FILE]

Each mutant changes ONE thing in the generated module and must fail at
exactly the listed declarations; the unmodified control must elaborate.

  wrong-root   The reference pole is the negative root, -sqrt(PStar). The
               algebraic identity with the occupied term still holds (it only
               uses w^2 = P). Must fail: `sqrt_bound`, the one place the branch
               is pinned numerically.
  pole         The production pole is moved by 2^-40 relative. Must fail:
               `sqrt_checks` (no longer the rounded root of the certified
               wtilde2), and `sch_local`/`ssx_local` (the kernel's arithmetic
               no longer reproduces from it).
  energy       e_n1kq is moved by 2^-30. Must fail: `x_bound`.
  local        Production `sch` is moved by 2^-40 relative. Must fail: `sch_local`.
  clamped      Production `ssx` is zeroed, as the sexcut clamp would. Must
               fail: `ssx_local` and `unclamped`.
"""
import argparse
import hashlib
import importlib.util
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN = ROOT / "GW" / "BGW" / "M5Sigma.lean"
sys.path.insert(0, str(HERE))
import sigma_mode  # noqa: E402
import make_lean_m5 as make_lean  # noqa: E402

_s = importlib.util.spec_from_file_location("m4mut", ROOT / "bgw" / "m4_gpp" / "mutate.py")
m4mut = importlib.util.module_from_spec(_s)
_s.loader.exec_module(m4mut)
sub1, def_line = m4mut.sub1, m4mut.def_line
q = make_lean.q


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def mutants(text, res):
    c, r = res["cert"], res["sel"]
    out = {}
    out["wrong-root"] = (sub1(text, "noncomputable def wStar : ℝ := Real.sqrt (M4.PStar : ℝ)",
                              "noncomputable def wStar : ℝ := -Real.sqrt (M4.PStar : ℝ)"),
                         {"sqrt_bound"})
    out["pole"] = (sub1(text, def_line(text, "wHat"),
                        f"def wHat : ℚ := {q(c['w_hat'] * (1 + F(1, 2 ** 40)))}"),
                   {"sqrt_checks", "sch_local", "ssx_local"})
    e = sigma_mode.q64(r["e_n1kq"])
    out["energy"] = (sub1(text, def_line(text, "eN1kq"),
                          f"def eN1kq : ℚ := {q(e + F(1, 2 ** 30))}"), {"x_bound"})
    out["local"] = (sub1(text, def_line(text, "schHat"),
                         f"def schHat : ℚ := {q(c['sch_hat'] * (1 + F(1, 2 ** 40)))}"),
                    {"sch_local"})
    out["clamped"] = (sub1(text, def_line(text, "ssxHat"), "def ssxHat : ℚ := (0 / 1 : ℚ)"),
                      {"ssx_local", "unclamped"})
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--log")
    a = ap.parse_args(argv)
    res = sigma_mode.run()
    text = make_lean.render(res)
    if LEAN.read_text() != text:
        raise SystemExit("M5Sigma.lean is not the generated module; run make_lean_m5.py --check")
    lines = ["BGW-M5 discriminating certificate mutations", "",
             f"M5Sigma.lean sha256: {sha256(LEAN)}",
             f"mutate.py sha256: {sha256(pathlib.Path(__file__))}",
             f"m5_dump.dat.gz sha256: {sha256(sigma_mode.DUMP)}", "",
             "Each mutant must fail at exactly the expected declarations; the control must elaborate.", ""]
    ok = True
    cases = [("control", text, set())] + [(k, v[0], v[1]) for k, v in mutants(text, res).items()]
    for tag, body, expected in cases:
        rc, out = m4mut.run_module(body.replace("namespace GW.BGW.M5", "namespace GW.BGW.M5"), "m5_" + tag)
        got = m4mut.failing_decls(out, body) if rc != 0 else set()
        verdict = "OK" if (got == expected and (rc == 0) == (not expected)) else "FAIL"
        ok &= verdict == "OK"
        lines += [f"--- {tag} ---", f"lean exit code         : {rc}",
                  f"expected failing decls : {sorted(expected)}",
                  f"actual failing decls   : {sorted(got)}",
                  f"verdict                : {verdict}", ""]
        print(f"{tag:12s} rc={rc} got={sorted(got)} expected={sorted(expected)} {verdict}")
    lines.append("ALL OK" if ok else "SOME MUTATION DID NOT DISCRIMINATE")
    if a.log:
        pathlib.Path(a.log).write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

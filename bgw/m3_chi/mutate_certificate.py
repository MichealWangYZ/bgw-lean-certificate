#!/usr/bin/env python3
"""Discriminating mutations of the M3 certificate, run through Lean.

    python3 bgw/m3_chi/mutate_certificate.py            # both, reports pass/fail
    python3 bgw/m3_chi/mutate_certificate.py --log FILE # also write evidence

Each mutation alters ONE generated witness while leaving the raw exported
operands untouched, and requires Lean to fail at a NAMED proof obligation. A
parser error, a build error, or a failure somewhere else does not count: the
script checks which declaration the error is attributed to.

1. product witness   `qw1` of one transition is perturbed. The dependent
   aggregates (`posSum11`, `negSum11`, `transferNum11`) are recomputed so the
   module cannot fail merely because an old total no longer matches. The only
   thing left inconsistent is the relation between `qw1` and the matrix
   elements plus the star map, so `products_correct` must fail.

2. residual witness  `resid` of one transition is decremented by one, with
   `evZ`, `ecZ`, `ovZ`, `ocZ`, `ez` and `eUp` untouched. The harness
   verifies that this breaks only the residual-identity clause while preserving
   the denominator-error allowance, so `rows_ok11` fails for the intended
   correspondence reason.

The mutated modules are written beside the real one, elaborated, and deleted.
They are imported by nothing and appear in neither the build nor the audit.
"""

import argparse
import hashlib
import pathlib
import re
from fractions import Fraction as F
import shutil
import subprocess
import sys
import tempfile

SELF = pathlib.Path(__file__).resolve()
ROOT = SELF.parents[2]
LEAN = ROOT / "GW" / "BGW" / "M3Chi.lean"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _lake():
    exe = shutil.which("lake")
    if exe is None:
        raise SystemExit(
            "lake not on PATH: cannot run the mutations. Run scripts/bootstrap.sh "
            "or set PATH to the pinned toolchain first.")
    return exe


def run_module(text, tag):
    """Elaborate `text` as a throwaway module; return (exit code, output)."""
    path = ROOT / "GW" / "BGW" / f"M3Mutant_{tag}.lean"
    path.write_text(text)
    try:
        rc = subprocess.run([_lake(), "env", "lean", str(path.relative_to(ROOT))],
                            cwd=ROOT, capture_output=True, text=True)
        return rc.returncode, rc.stdout + rc.stderr
    finally:
        path.unlink(missing_ok=True)


def attributed_to(output, text):
    """Declarations containing reported errors, in diagnostic order.

    Track definitions as well as theorems. The old classifier considered only
    theorem starts, so an error in a later `def` could be misattributed to the
    preceding theorem and falsely count as a discriminating mutation.
    """
    starts = []
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(
            r"\s*(theorem|lemma|def|abbrev|structure|inductive)\s+(\w+)", line)
        if m:
            starts.append((i, m.group(1), m.group(2)))

    hit, seen = [], set()
    for m in re.finditer(r"^[^:]+:(\d+):\d+: error", output, re.M):
        ln = int(m.group(1))
        owner = None
        for start, kind, name in starts:
            if start <= ln and (owner is None or start > owner[0]):
                owner = (start, kind, name)
        label = (f"{owner[1]} {owner[2]}" if owner
                 else "<outside any tracked declaration>")
        if label not in seen:
            seen.add(label)
            hit.append(label)
    return hit


def mutate_product(text):
    """Perturb one `qw1` and repair every aggregate that depends on it."""
    m = re.search(r"qw1 := (-?\d+), qw2 := (-?\d+)", text)
    if m is None:
        raise SystemExit("no qw1 witness found")
    old = int(m.group(1))
    new = old + 1
    out = text[:m.start()] + f"qw1 := {new}, qw2 := {m.group(2)}" + text[m.end():]
    # the transition's ez, needed to repair posSum/negSum
    rec_start = text.rfind("{ evZ :=", 0, m.start())
    ez = int(re.search(r"ez := (-?\d+)", text[rec_start:m.start()]).group(1))
    eUp = int(re.search(r"eUp := (\d+)", text[m.start():m.start() + 400]).group(1))

    def bump(name, delta):
        nonlocal out
        mm = re.search(rf"theorem {name}_eq : {name} = (\d+) := by rfl", out)
        val = int(mm.group(1)) + delta
        out = out[:mm.start()] + f"theorem {name}_eq : {name} = {val} := by rfl" + out[mm.end():]

    before, after = old * ez, new * ez
    bump("posSum11", max(after, 0) - max(before, 0))
    bump("negSum11", max(-after, 0) - max(-before, 0))
    bump("transferNum11", (abs(new) - abs(old)) * eUp)

    # the two rational literals DERIVED from those totals must be repaired as
    # well, or the module fails at them too and the mutation stops isolating
    # the operand-to-product correspondence.
    sc = {k: int(re.search(rf"{k} := (-?\d+)", out).group(1))
          for k in ("sGme", "sEden", "kEps", "sFact", "factZ")}
    pos = int(re.search(r"theorem posSum11_eq : posSum11 = (\d+)", out).group(1))
    neg = int(re.search(r"theorem negSum11_eq : negSum11 = (\d+)", out).group(1))
    tnum = int(re.search(r"theorem transferNum11_eq : transferNum11 = (\d+)", out).group(1))
    recon = F(sc["factZ"], 1 << (sc["sFact"] + 2 * sc["sGme"] + sc["sEden"])) * (pos - neg)
    transfer = abs(F(sc["factZ"])) * F(tnum, 1 << (sc["sFact"] + 2 * sc["sGme"] + sc["kEps"]))

    def qlit(fr):
        return (f"({fr.numerator} : ℚ)" if fr.denominator == 1
                else f"(({fr.numerator} : ℚ) / {fr.denominator})")

    out = re.sub(r"(theorem chiRecon11_eq : chiRecon11 = ).*?( := by)",
                 lambda mm: mm.group(1) + qlit(recon) + mm.group(2), out, count=1)
    out = re.sub(r"(def transferBudget11 : ℚ := ).*",
                 lambda mm: mm.group(1) + qlit(transfer), out, count=1)
    return out, "theorem products_correct"


def first_residual_witness_checks(text):
    """Re-evaluate the non-product clauses of `rowOK` for the first row.

    This is intentionally independent of Lean: it keeps the residual mutation
    discriminating by checking that only the residual-identity clause is
    broken, while the energy/occupation differences, nonzero denominator and
    certified error allowance still hold.
    """
    scales = {}
    for name in ("sEden", "sDen", "sOcc", "kEps"):
        m = re.search(rf"{name} := (\d+)", text)
        if m is None:
            raise SystemExit(f"missing scale {name}")
        scales[name] = int(m.group(1))

    row = re.search(
        r"\{ evZ := (-?\d+), ecZ := (-?\d+), ovZ := (-?\d+), "
        r"ocZ := (-?\d+), ez := (-?\d+), dZ := (-?\d+), oZ := (-?\d+), "
        r"g := .*?, qw1 := -?\d+, qw2 := -?\d+, resid := (\d+), eUp := (\d+) \}",
        text)
    if row is None:
        raise SystemExit("cannot parse first transition row")

    evZ, ecZ, ovZ, ocZ, ez, dZ, oZ, resid, eUp = map(int, row.groups())
    expected_resid = abs(
        ez * (dZ * 2 ** scales["sOcc"])
        - (oZ * 2 ** scales["sDen"]) * (2 ** scales["sEden"]))
    allowance_rhs = (
        eUp
        * (2 ** scales["sEden"])
        * abs(dZ * 2 ** scales["sOcc"])
    )
    return {
        "energy_difference": dZ == evZ - ecZ,
        "occupation_difference": oZ == ovZ - ocZ,
        "nonzero_denominator": dZ != 0,
        "residual_identity": resid == expected_resid,
        "allowance": resid * 2 ** scales["kEps"] <= allowance_rhs,
    }


def mutate_residual(text):
    """Break only the residual identity, preserving the error allowance."""
    m = re.search(r"resid := (\d+)", text)
    if m is None:
        raise SystemExit("no resid witness found")
    old = int(m.group(1))
    if old <= 0:
        raise SystemExit("first residual is not positive; cannot decrement safely")
    new = old - 1
    out = text[:m.start()] + f"resid := {new}" + text[m.end():]

    checks = first_residual_witness_checks(out)
    expected = {
        "energy_difference": True,
        "occupation_difference": True,
        "nonzero_denominator": True,
        "residual_identity": False,
        "allowance": True,
    }
    if checks != expected:
        raise SystemExit(
            "residual mutation is not isolated to the residual identity: "
            f"{checks}")
    return out, "theorem rows_ok11"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", help="write the evidence log here")
    a = ap.parse_args(argv)

    base = LEAN.read_text()
    report, ok = [], True

    # The same harness must accept the pristine module. A mutation failure is
    # meaningless if the throwaway compilation path is broken on the control.
    code, output = run_module(base, "control")
    blamed = attributed_to(output, base)
    good = code == 0
    ok &= good
    report.append(
        "--- unmodified control ---\n"
        f"lean exit code              : {code}\n"
        f"first failing declaration   : {blamed[0] if blamed else '(none)'}\n"
        f"failure declarations        : {blamed or '(none)'}\n"
        f"verdict                     : {'OK' if good else 'CONTROL FAILED'}\n")
    print(report[-1], end="")

    for tag, fn in (("product", mutate_product), ("residual", mutate_residual)):
        text, expect = fn(base)
        # The namespace is NOT renamed: `Scales`, `Row` and `rowOK` live in
        # `GW.BGW.M3` in the transfer module, and renaming made every
        # declaration unresolvable -- a build failure, which proves nothing.
        # The mutant file is standalone and imported by nothing.
        code, output = run_module(text, tag)
        blamed = attributed_to(output, text)
        primary = blamed[0] if blamed else None
        good = code != 0 and primary == expect
        ok &= good
        report.append(
            f"--- {tag} witness mutation ---\n"
            f"expected first declaration  : {expect}\n"
            f"lean exit code              : {code}\n"
            f"first failing declaration   : {primary or '(none)'}\n"
            f"failure declarations        : {blamed or '(none)'}\n"
            f"verdict                     : {'OK' if good else 'NOT DISCRIMINATING'}\n")
        print(report[-1], end="")

    if a.log:
        pathlib.Path(a.log).write_text(
            "BGW-M3-R1 discriminating certificate mutations\n\n"
            "Source fingerprints bind this evidence to the exact certificate "
            "and mutation harness.\n"
            f"M3Chi.lean sha256: {sha256(LEAN)}\n"
            f"mutate_certificate.py sha256: {sha256(SELF)}\n\n"
            "The control must elaborate, and each mutation must have its named "
            "correspondence obligation as the FIRST failing declaration.\n\n"
            + "\n".join(report))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

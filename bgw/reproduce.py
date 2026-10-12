#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Regenerate Si-EPM inputs and exports using two already-built source trees.

No installation or source modification. Output must be a new directory.
This tests reused binaries; it does not certify their compiler provenance.

Byte identity with the saved evidence depends on the BLAS threading of the
mean-field step: single-threaded OpenBLAS changes the wavefunctions and some
off-diagonal outputs in this test. A changed basis inside degenerate subspaces
is a plausible explanation, not a proved physical equivalence. The archived
run used the host default,
so `--blas-threads` defaults to inheriting the ambient environment.
"""

import argparse
import ast
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess

from verify_export import check_manifest, load, PROFILES, verify_rows

ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd"
EXPECTED_ASSERTIONS = 24


def parse_assertions(test_text):
    """Parse the upstream GPP sigma block of `testsuite/Si-EPM/Si.test`.

    Each assertion keeps the `Precision` in force where it appears, as the
    upstream Perl harness does. `GREP` takes the first matching line, matching
    `run_regression_test.pl`'s documented `grep ... | awk (NR==off+1)` pipe.
    """
    if "Input  : sig_GPP.inp sigma.inp" not in test_text:
        raise ValueError("no GPP sigma block in the upstream test file")
    block = test_text.split("Input  : sig_GPP.inp sigma.inp", 1)[1]
    block = block.split("Copy : Si.nnkp", 1)[0]
    assertions, tolerance = [], None
    for line in block.splitlines():
        if line.startswith("Precision :"):
            tolerance = float(line.split(":", 1)[1])
        if not line.startswith("match ;"):
            continue
        parts = [part.strip() for part in line.split(";")]
        if len(parts) != 4:
            raise ValueError("unsupported upstream match syntax")
        _, name, expression, expected = parts
        if not expression.startswith("GREP(sigma_hp.log,") or not expression.endswith(")"):
            raise ValueError("unsupported upstream benchmark syntax")
        arguments = ast.literal_eval(
            "(" + expression.removeprefix("GREP(sigma_hp.log,")[:-1] + ")")
        if len(arguments) != 3:
            raise ValueError("unsupported upstream GREP arity")
        needle, column, offset = arguments
        if tolerance is None:
            raise ValueError("upstream assertion with no Precision in force")
        assertions.append(dict(name=name, needle=needle, column=int(column),
                               offset=int(offset), expected=float(expected),
                               tolerance=tolerance))
    return assertions


def evaluate_assertions(assertions, log_text):
    """Check parsed upstream assertions against one `sigma_hp.log`."""
    lines, results = log_text.splitlines(), []
    for assertion in assertions:
        index = next((i for i, line in enumerate(lines)
                      if assertion["needle"] in line), None)
        if index is None:
            raise ValueError(f"upstream benchmark needle not found: {assertion['name']}")
        fields = lines[index + assertion["offset"]].split() if \
            index + assertion["offset"] < len(lines) else []
        if len(fields) < assertion["column"]:
            raise ValueError(f"upstream benchmark column missing: {assertion['name']}")
        actual = float(fields[assertion["column"] - 1])
        if not all(math.isfinite(v) for v in
                   (actual, assertion["expected"], assertion["tolerance"])):
            raise ValueError("nonfinite benchmark value or tolerance")
        residual = abs(actual - assertion["expected"])
        if residual > assertion["tolerance"]:
            raise ValueError(
                f"upstream benchmark failed: {assertion['name']}: "
                f"{actual} vs {assertion['expected']} > {assertion['tolerance']}")
        results.append(dict(name=assertion["name"], expected=assertion["expected"],
                            actual=actual, tolerance=assertion["tolerance"],
                            absolute_error=residual))
    return results


def check_benchmarks(source, log):
    assertions = parse_assertions((source / "testsuite/Si-EPM/Si.test").read_text())
    if len(assertions) != EXPECTED_ASSERTIONS:
        raise ValueError(f"expected {EXPECTED_ASSERTIONS} upstream GPP assertions, "
                         f"got {len(assertions)}")
    return evaluate_assertions(assertions, log.read_text())


def column_deviations(saved_rows, fresh_rows):
    """Per-column worst deviation between two export dumps of equal length."""
    if len(saved_rows) != len(fresh_rows):
        return {"record_counts": [len(saved_rows), len(fresh_rows)]}
    worst = {}
    for saved, fresh in zip(saved_rows, fresh_rows):
        for column, value in saved.items():
            delta = abs(value - fresh[column])
            if delta:
                relative = delta / abs(value) if value else float("inf")
                previous = worst.get(column, (0.0, 0.0))
                worst[column] = (max(previous[0], delta), max(previous[1], relative))
    return {column: {"max_abs": absolute, "max_rel": relative}
            for column, (absolute, relative) in worst.items()}


def diagnose(label, fresh, saved):
    """Byte-compare two outputs and, if they differ, describe how."""
    record = {"file": label, "identical": fresh.read_bytes() == saved.read_bytes()}
    if record["identical"]:
        return record
    before, after = saved.read_text().splitlines(), fresh.read_text().splitlines()
    differing = [i + 1 for i, (x, y) in enumerate(zip(before, after)) if x != y]
    record.update(saved_line_count=len(before), fresh_line_count=len(after),
                  differing_line_count=len(differing),
                  differing_line_numbers=differing[:20])
    if differing:
        line = differing[0]
        record["first_difference"] = {"line": line, "saved": before[line - 1],
                                      "fresh": after[line - 1]}
    if fresh.name in PROFILES:
        record["numeric_deviation"] = column_deviations(load(saved), load(fresh))
    return record


def run_tree(label, tree, run, env, source):
    run.mkdir()
    for name in ("WFN.in", "WFNq.in", "WFN_co.in", "epsilon.inp", "sig_GPP.inp"):
        shutil.copy2(ROOT / "bgw/export" / name, run / name)

    def execute(binary, log, input_name=None):
        print(f"{label}: {binary.name}", flush=True)
        with (run / log).open("w") as out:
            stdin = (run / input_name).open() if input_name else None
            try:
                subprocess.run([str(binary)], cwd=run, env=env, stdin=stdin,
                               stdout=out, stderr=subprocess.STDOUT,
                               check=True, timeout=600)
            finally:
                if stdin:
                    stdin.close()

    for name in ("WFN", "WFNq", "WFN_co"):
        execute(tree / "MeanField/EPM/epm2bgw.x", name + ".out", name + ".in")
    if not (run / "WFN_inner").is_file():
        raise ValueError("WFN_co.in did not produce the required WFN_inner")
    execute(tree / "Epsilon/epsilon.real.x", "epsilon.out")
    shutil.copy2(run / "sig_GPP.inp", run / "sigma.inp")
    execute(tree / "Sigma/sigma.real.x", "sigma.out")
    return {"tree": str(tree),
            "benchmarks": check_benchmarks(source, run / "sigma_hp.log")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pristine", type=Path, required=True)
    parser.add_argument("--instrumented", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--blas-threads", type=int, default=None,
                        help="pin OpenBLAS/OpenMP threads; default inherits the "
                             "environment, as the archived run did")
    args = parser.parse_args()
    output = args.output.resolve()
    pristine, instrumented = args.pristine.resolve(), args.instrumented.resolve()
    check_manifest(ROOT / "bgw/export")
    source = pristine / "Sigma/mtxel_cor.f90"
    if hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_SHA:
        raise ValueError("pristine source checksum mismatch")
    output.mkdir(parents=True, exist_ok=False)
    patched = output / "mtxel_cor.instrumented.f90"
    subprocess.run(["patch", "--batch", "--silent", "--output", str(patched),
                    str(source), str(ROOT / "bgw/export/instrument.patch")], check=True)
    if patched.read_bytes() != (instrumented / "Sigma/mtxel_cor.f90").read_bytes():
        raise ValueError("instrumented source does not match the saved patch")

    env = dict(os.environ)
    if args.blas_threads is not None:
        env.update(OPENBLAS_NUM_THREADS=str(args.blas_threads),
                   OMP_NUM_THREADS=str(args.blas_threads))
    report = {"scope": "fresh runs using existing binaries; no clean rebuild",
              "pristine_source_sha256": SOURCE_SHA, "status": "running",
              "blas_threads": args.blas_threads,
              "thread_environment": {name: env.get(name) for name in
                                     ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS")},
              "runs": {}}
    summary = output / "report.json"

    def save():
        summary.write_text(json.dumps(report, indent=2) + "\n")

    save()
    try:
        for label, tree in (("pristine", pristine), ("instrumented", instrumented)):
            report["runs"][label] = run_tree(label, tree, output / label, env, pristine)
            save()
        filenames = ["sigma_hp.log", "gpp_branch_counts.dat", *PROFILES]
        report["saved_evidence_comparison"] = [
            diagnose(name, output / "instrumented" / name, ROOT / "bgw/export" / name)
            for name in filenames]
        report["instrumentation_comparison"] = diagnose(
            "sigma_hp.log (pristine vs instrumented)",
            output / "instrumented/sigma_hp.log", output / "pristine/sigma_hp.log")
        report["exports"] = {
            name: verify_rows(load(output / "instrumented" / name), name)
            for name in PROFILES}
        save()
        differing = [record["file"] for record in report["saved_evidence_comparison"]
                     if not record["identical"]]
        if differing:
            raise ValueError("fresh run differs from saved evidence: "
                             + ", ".join(differing))
        if not report["instrumentation_comparison"]["identical"]:
            raise ValueError("instrumentation changed sigma_hp.log")
        report["byte_identical_saved_outputs"] = filenames
        report["status"] = "passed"
        print(f"PASS: fresh runs, {EXPECTED_ASSERTIONS} upstream assertions each, "
              f"identical exports; {summary}")
    except Exception as error:
        report.update(status="failed", error=f"{type(error).__name__}: {error}")
        raise
    finally:
        save()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent supervisor gate: compile, audit, execute, compare, retain evidence."""

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gates  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts"


def source_hashes():
    paths = [ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json", ROOT / "Specification.md"]
    for directory, pattern in [(ROOT, "*.lean"), (ROOT / "GW", "**/*.lean"), (ROOT / "scripts", "*"), (ROOT / "tests", "*.py"), (ROOT / "ll", "*.py"), (ROOT / "fixtures", "*.json")]:
        paths.extend(p for p in directory.glob(pattern) if p.is_file())
    paths.extend(p for directory in (ROOT / "bgw", ROOT / "docs")
                 for p in directory.rglob("*")
                 if p.is_file() and "__pycache__" not in p.parts)
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}


def git_state():
    """HEAD and whether the tree differs from it, so a result names its source."""
    def git(*a):
        r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
        return r.stdout.strip() if r.returncode == 0 else None
    status = git("status", "--porcelain", "--untracked-files=no")
    return {"head": git("rev-parse", "HEAD"),
            "tracked_changes": None if status is None else bool(status)}


def skipped_tests(logs):
    """`unittest -v` lines reporting a skip: (test id, reason)."""
    out = []
    for log in logs:
        if not log.exists():
            continue
        for line in log.read_text().splitlines():
            if " ... skipped " in line:
                test, reason = line.split(" ... skipped ", 1)
                out.append({"test": test.strip(), "reason": reason.strip().strip("'")})
    return out


def changed_files(base):
    """Paths changed relative to `base` (tracked diff plus untracked files). With no
    `base` and a clean tree, the last commit is the change (HEAD~1..HEAD)."""
    def git(*a):
        return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True,
                              check=True).stdout.split()
    ref = base or "HEAD"
    files = set(git("diff", "--name-only", ref)) | set(
        git("ls-files", "--others", "--exclude-standard"))
    if not files and base is None:
        ref = "HEAD~1"
        files = set(git("diff", "--name-only", ref))
    return ref, sorted(files)


def fast(args):
    """The fast gate for routine changes (WRAPUP item 5). It is NOT a substitute for
    the full gate before a merge. Steps: the registry check, `lake build GW` (the default
    library, no GWKernelData), the memoized audit of the default library, the workflow
    tests, and the scientific tests that cover the change (scripts/gates.py FAST), run in
    parallel processes."""
    import time
    from concurrent.futures import ThreadPoolExecutor
    t0 = time.monotonic()
    out = OUT / "fast"
    out.mkdir(parents=True, exist_ok=True)
    ref, changed = changed_files(args.base)
    tests, unsure, archived = gates.select_fast(changed)
    if args.all_tests:
        tests = sorted(gates.FAST)
    record = {"started_at": datetime.now(timezone.utc).isoformat(), "status": "running",
              "gate": "fast", "git": git_state(), "base": ref, "changed": changed,
              "unsure": unsure, "archived_changed": archived, "tests": tests, "steps": []}
    summary = OUT / "verification-fast.json"

    def save():
        summary.write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command, filename, timeout=1800):
        print(label, flush=True)
        s = time.monotonic()
        with (out / filename).open("w") as log:
            done = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                  timeout=timeout)
        record["steps"].append({"label": label, "command": command, "exit_code": done.returncode,
                                "log": f"fast/{filename}", "seconds": round(time.monotonic() - s, 1)})
        save()
        if done.returncode:
            print((out / filename).read_text()[-6000:])
            raise RuntimeError(f"{label} failed with exit {done.returncode}")

    save()
    try:
        run("Registry check", [sys.executable, "scripts/registry.py", "--check"], "registry.log")
        run("Build the default library (no GWKernelData)", ["lake", "build", "GW"], "build.log")
        run("Memoized axiom audit, default library", ["lake", "env", "lean",
            "scripts/CheckAxiomsFast.lean"], "axioms.log", timeout=3600)
        import registry
        expected = {"GW", "Main", *registry.default_lib(registry.project_modules())}
        audited = {l.removeprefix("AUDIT_MODULE ").strip()
                   for l in (out / "axioms.log").read_text().splitlines()
                   if l.startswith("AUDIT_MODULE ")}
        if expected - audited:
            raise RuntimeError(f"Unaudited default-library modules: {sorted(expected - audited)}")
        if unsure:
            print(f"selection UNSURE for {unsure}: running every FAST test module")
        for f in archived:
            print(f"ARCHIVED path changed (full gate only): {f}")
        mods = list(gates.WORKFLOW) + tests
        print(f"Python tests ({len(mods)} modules, parallel): {' '.join(mods)}", flush=True)

        def one(m):
            s = time.monotonic()
            with (out / f"{m}.log").open("w") as log:
                rc = subprocess.run([sys.executable, "-m", "unittest", "-v", m], cwd=ROOT,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=3600).returncode
            return m, rc, round(time.monotonic() - s, 1)

        with ThreadPoolExecutor(max_workers=max(1, min(len(mods), args.jobs))) as pool:
            results = list(pool.map(one, mods))
        record["test_results"] = [{"module": m, "exit_code": rc, "seconds": sec}
                                  for m, rc, sec in results]
        failed = [m for m, rc, _ in results if rc]
        if failed:
            for m in failed:
                print((out / f"{m}.log").read_text()[-4000:])
            raise RuntimeError(f"tests failed: {failed}")
        record["not_verified"] = skipped_tests([out / f"{m}.log" for m in mods])
        record["status"] = "passed"
        print(f"PASS (fast): registry, default-library build, memoized audit, "
              f"{len(mods)} test modules; NOT the full gate (run before any merge).")
        for item in record["not_verified"]:
            print(f"NOT VERIFIED (skipped): {item['test']} -- {item['reason']}")
    except (OSError, RuntimeError, subprocess.TimeoutExpired, subprocess.CalledProcessError) as error:
        record.update(status="failed", error=str(error))
        print(f"FAIL: {error}", file=sys.stderr)
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        record["wall_seconds"] = round(time.monotonic() - t0, 1)
        save()
        print(f"fast gate wall time: {record['wall_seconds']} s")
    return 0 if record["status"] == "passed" else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--gate", choices=("all", "scientific", "workflow", "fast"), default="all",
        help="which test gate to run; for all/scientific/workflow the Lean build, axiom "
             "audit, oracle and export checks always run. `fast` is the routine-change "
             "gate (default library only, tests selected by the change). See "
             "scripts/gates.py for the split.")
    parser.add_argument("--base", default=None,
                        help="fast gate: git ref the change is measured against "
                             "(default: uncommitted changes, else the last commit)")
    parser.add_argument("--all-tests", action="store_true",
                        help="fast gate: run every FAST test module regardless of the change")
    parser.add_argument("--jobs", type=int, default=8,
                        help="fast gate: parallel test processes")
    args = parser.parse_args(argv)
    if args.gate == "fast":
        return fast(args)

    OUT.mkdir(exist_ok=True)
    record = {"started_at": datetime.now(timezone.utc).isoformat(), "status": "running",
              "gate": args.gate, "git": git_state(), "steps": []}
    summary = OUT / "verification.json"

    def save():
        summary.write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command, filename, timeout=600):
        print(label, flush=True)
        with (OUT / filename).open("w") as log:
            completed = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        record["steps"].append({"label": label, "command": command, "exit_code": completed.returncode, "log": filename})
        save()
        if completed.returncode:
            print((OUT / filename).read_text()[-10000:])
            raise RuntimeError(f"{label} failed with exit {completed.returncode}")

    save()
    try:
        record["source_sha256"] = source_hashes()
        run("Registry check (generated registries match the tree)",
            [sys.executable, "scripts/registry.py", "--check"], "registry.log")
        run("Build pinned Lean project", ["lake", "build"], "build.log")
        # G2: the kernel-checked certificate data (stages 1-3: ~2 h wall from
        # scratch, cached afterwards); audited by scripts/CheckAxioms.lean below.
        run("Build kernel-checked certificate data", ["lake", "build", "GWKernelData"],
            "build-kernel-data.log", timeout=6 * 3600)
        run("Print named theorem dependencies", ["lake", "env", "lean", "GW/Audit.lean"], "named-axioms.log",
            timeout=2 * 3600)
        run("Audit all project theorem dependencies", ["lake", "env", "lean", "scripts/CheckAxioms.lean"], "axioms.log",
            timeout=2 * 3600)          # memoized (WRAPUP): ~2.5 min warm, was ~46 min
        expected_modules = {"GW", "Main"} | {
            ".".join(p.relative_to(ROOT).with_suffix("").parts)
            for p in (ROOT / "GW").rglob("*.lean") if p != ROOT / "GW" / "Audit.lean"
        }
        imported_modules = {
            line.removeprefix("AUDIT_MODULE ").strip()
            for line in (OUT / "axioms.log").read_text().splitlines()
            if line.startswith("AUDIT_MODULE ")
        }
        if expected_modules - imported_modules:
            raise RuntimeError(f"Unaudited project modules: {sorted(expected_modules - imported_modules)}")
        run("Run Lean demo", [".lake/build/bin/gpp_demo", "--json"], "lean-demo.json")
        run("Exercise actual Lean evaluator edge cases", ["lake", "env", "lean", "--run", "scripts/RuntimeChecks.lean"], "lean-runtime-tests.log")
        run("Compare against exact oracle", [sys.executable, "scripts/reference.py", "--lean-json", "artifacts/lean-demo.json", "--output-dir", "artifacts"], "numerical-demo.log")
        run("Check BerkeleyGW saved evidence and both exports", [sys.executable, "bgw/verify_export.py", "--all"], "bgw-exports.json")
        # The two gates run as SEPARATE steps so the log says which kind of
        # thing broke: a measured quantity, or the project's own prose.
        # scripts/gates.py states the criterion; tests/test_gate_partition.py
        # guarantees no module escapes both lists.
        # LL-C1: regenerate the Lean diagram values so the Python comparison
        # in tests/test_ll_c1.py cannot run against a stale artifact.
        (OUT / "ll-c1").mkdir(exist_ok=True)
        run("Evaluate LL-C1 ring diagrams in Lean", [".lake/build/bin/ll_c1_eval"],
            "ll-c1/lean_values.json")
        # Validate those values and regenerate the comparison report in the
        # same pass, so the checked report cannot silently lag the checked
        # values. The generator exits non-zero on an invalid table.
        run("Validate and regenerate the LL-C1 comparison report",
            [sys.executable, "ll/make_comparison.py"], "ll-c1/make_comparison.log")
        # LL-C2A: the structural ring family at orders 0..4.
        (OUT / "ll-c2a").mkdir(exist_ok=True)
        run("Evaluate the structural ring family in Lean",
            [".lake/build/bin/ll_c2a_eval"], "ll-c2a/structural_values.json")
        # LL-C2B: the screened-interaction and ring series coefficients at
        # degrees 0..4. Regenerated here so tests/test_ll_c2b.py cannot run
        # against a stale table.
        (OUT / "ll-c2b").mkdir(exist_ok=True)
        run("Evaluate the formal screening coefficients in Lean",
            [".lake/build/bin/ll_c2b_eval"], "ll-c2b/screening_values.json")
        # LL-C3: the normalized first-order Wick computation and its
        # Hartree/Fock split. Regenerated so tests/test_ll_c3.py cannot run
        # against a stale table.
        (OUT / "ll-c3").mkdir(exist_ok=True)
        run("Evaluate the first-order Wick correction in Lean",
            [".lake/build/bin/ll_c3_eval"], "ll-c3/wick_values.json")
        # LL-C4: the finite static electronic RPA model. Regenerated so
        # tests/test_ll_c4.py cannot run against a stale table.
        (OUT / "ll-c4").mkdir(exist_ok=True)
        run("Evaluate the electronic RPA screening in Lean",
            [".lake/build/bin/ll_c4_eval"], "ll-c4/electronic_values.json")

        if args.gate in ("all", "scientific"):
            run("Scientific gate: numbers, algebra, source correspondence",
                [sys.executable, "-m", "unittest", "-v", *gates.SCIENTIFIC],
                "tests-scientific.log", timeout=3600)   # ~9-10 min when idle
        if args.gate in ("all", "workflow"):
            run("Workflow gate: evidence bookkeeping",
                [sys.executable, "-m", "unittest", "-v", *gates.WORKFLOW],
                "tests-workflow.log")
        invalid = subprocess.run([".lake/build/bin/gpp_demo", "--invalid"], cwd=ROOT, capture_output=True, text=True, timeout=30)
        if invalid.returncode == 0:
            raise RuntimeError("demo accepted an unknown flag")
        record["unknown_flag_rejected"] = True
        if record["source_sha256"] != source_hashes():
            raise RuntimeError("source changed during verification; rerun after the writer stops")
        record["status"] = "passed"
        record["not_verified"] = skipped_tests(
            [OUT / name for name in ("tests-scientific.log", "tests-workflow.log")])
        print(f"PASS ({args.gate}): Lean build, exhaustive axiom check, exact "
              f"oracle, BerkeleyGW exports, domain and mutation checks.")
        # A skipped test verified nothing. Say so where the verdict is read.
        for item in record["not_verified"]:
            print(f"NOT VERIFIED (skipped): {item['test']} -- {item['reason']}")
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        record.update(status="failed", error=str(error))
        print(f"FAIL: {error}", file=sys.stderr)
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()
    return 0 if record["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())

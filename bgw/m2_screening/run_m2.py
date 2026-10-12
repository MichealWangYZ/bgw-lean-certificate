#!/usr/bin/env python3
"""Rerunnable driver for the BGW-M2 screening comparison.

Two modes.

    python3 bgw/m2_screening/run_m2.py
        Verify from the committed snapshot: pin its digest, extract exactly,
        form E_star, check the frozen formation budget, certify the inverses,
        check the inverse-shift identity and the composed total budget, and
        confirm the Lean literals are this same data. No BerkeleyGW needed.

    python3 bgw/m2_screening/run_m2.py --full --source TREE --inputs DIR
        Additionally reproduce the production event: copy TREE to a fresh
        temporary directory, apply the instrumentation patch, build the real
        flavor from clean, run a pristine and an instrumented build on the same
        inputs, compare their whole `epsmat` outputs, and require the extracted
        q-block to reproduce the committed snapshot byte for byte.

    `--proof` additionally elaborates `GW/BGW/M2Screening.lean` with Lean.
    WITHOUT it, this driver performs NO kernel check: `check_lean_literals.py`
    compares literals only. A successful run of this driver is therefore not a
    fresh proof check, and the acceptance command is
    `run_m2.py --full --proof ...` together with `scripts/verify.py --gate all`.

The repository root is resolved from this file, so the driver runs from any
working directory. `--full` works only in a fresh `mkdtemp` and never deletes
an existing run directory.

On TREE and DIR the contract is DETECTION, not prevention. This driver issues
no write of its own inside either, and it materializes escaping symlinks in
its copies so that its own builds cannot reach back; but the run directories
link at the supplied wavefunctions, so a native program that wrote through
those links WOULD reach them. What `verify_preserved` establishes is that
nothing under TREE or DIR changed on this run -- by content, dereferencing
supplied symlinks, and counting additions as changes. It does not make a write
impossible.
"""

import argparse
import hashlib
import importlib.util
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[2]

RUNID = "m2-20260917-q2-cut15"
IQ, N, Q = 2, 8, (0.0, 0.0, 0.5)
DUMP = ROOT / "bgw/m2_screening/data/m2_dump_q2.txt"
DUMP_SHA256 = "37ee0a30072845f8b36274a2fad518bf8e42f09edcdcaefe5b8aaf9540b0f6ba"
PATCH = ROOT / "bgw/m2_screening/epsinv_m2_dump.patch"
PRISTINE_EPSINV_SHA256 = \
    "cb7c9fb326df1b437c0a043305789e60f793148233ed516420669d8e946998e1"
WFN_SHA256 = "f85a1534fe70a5a1b966fdbc1c6f0fc1d8acab2f08215b39ef0f04ff9bfce37d"
WFNQ_SHA256 = "1138228a81c562bbfd88693072446443a259f4676f095d9afe15bb86f3e6c8ca"
EPSILON_INP = """epsilon_cutoff 1.5

number_bands 18

begin qpoints
  0.000000000  0.000000000  0.001000000   1.0 1
  0.000000000  0.000000000  0.500000000   1.0 0
  0.000000000  0.500000000  0.500000000   1.0 0
end
"""


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


#: The dump must belong entirely to this run, and the retained block must occur
#: exactly once. A real run emits q = 1, 2, 3; an isolated reproduction of the
#: target block alone is also legitimate, so the count of OTHER blocks is not
#: fixed -- what is rejected is a foreign run id or a repeated target.
EXPECTED_RUNID = RUNID


def tree_digests(root, *, follow=True):
    """Digest map of the regular files under `root`, for a safety check.

    BGW-M2-R3. `follow=True` DEREFERENCES symlinks, so an entry that is itself
    a link to a file outside `root` still contributes its CONTENT here. The R2
    version skipped every symlink, which left a real hole: with

        inputs/WFN      -> ../data/WFN          (supplied by the caller)
        run-pristine/WFN -> inputs/WFN          (created by this driver)

    `data/WFN` was in neither baseline, so a write through the run directory
    reached it and the driver still returned 0. Review reproduced that.

    A dangling link contributes nothing: `is_file()` is False for it.
    """
    root = pathlib.Path(root)
    out = {}
    for f in sorted(root.rglob("*")):
        if f.is_symlink() and not follow:
            continue
        if f.is_file():          # follows links; False for dangling or non-file
            out[str(f.relative_to(root))] = sha(f)
    return out


def _differences(before, after):
    """Modified, removed AND added keys between two digest maps.

    BGW-M2-R3. The R2 input comparison iterated over `before` only, so a new
    file appearing in the supplied inputs directory was reported as "unchanged".
    The source comparison already covered additions; this makes one rule for
    both.
    """
    out = sorted(k for k in before if after.get(k) != before[k])
    out += sorted(f"<new> {k}" for k in after if k not in before)
    return out


def verify_preserved(source, before_source, inputs, before_inputs):
    """Re-check that BOTH the supplied source tree and the supplied inputs are
    byte-identical to what was handed in.

    BGW-M2-R2. The R1 version checked the source tree only, and only on the
    success path. The run directories link `WFN`/`WFNq` straight at the
    owner's originals, so a native program that wrote through those links
    would reach them, and the driver still returned 0. Review reproduced that
    with a disposable mock.

    This is DETECTION, not prevention. It establishes that nothing was
    modified on this run; it does not make modification impossible. Preventing
    it would mean copying multi-gigabyte wavefunctions or relying on
    filesystem permissions the driver does not own.
    """
    changed = _differences(before_source, tree_digests(source))
    if changed:
        raise SystemExit(f"SUPPLIED SOURCE WAS MODIFIED: {changed[:5]}")
    bad = _differences(before_inputs, tree_digests(inputs))
    if bad:
        raise SystemExit(f"SUPPLIED INPUTS WERE MODIFIED: {bad[:5]}")
    print(f"  supplied source ({len(before_source)} files) and inputs "
          f"({len(before_inputs)} files) unchanged")


def safe_copy_tree(source, dest):
    """Copy a source tree so that NOTHING later written can escape it.

    BGW-M2-R1. The previous version used `copytree(..., symlinks=True)` and
    then `shutil.copy` onto `flavor.mk`. A preserved absolute symlink pointing
    back into the supplied tree made that second copy FOLLOW the link and
    overwrite the owner's file -- contradicting this driver's non-destructive
    guarantee. Found by review; reproduced with disposable files.

    Every symlink whose resolved target lies outside `dest` is materialized as
    a plain copy of its contents (or dropped if dangling), so no write inside
    `dest` can reach `source`. Moving the same unsafe write to another
    temporary directory would not have fixed it.
    """
    source, dest = pathlib.Path(source), pathlib.Path(dest)
    shutil.copytree(source, dest, symlinks=True)
    dest_real = dest.resolve()
    materialized, dropped = 0, 0
    for f in sorted(dest.rglob("*")):
        if not f.is_symlink():
            continue
        target = pathlib.Path(os.path.realpath(f))
        if dest_real in target.parents or target == dest_real:
            continue                      # stays inside the copy: harmless
        f.unlink()
        if target.is_file():
            shutil.copyfile(target, f)    # copyfile: never follows a link
            materialized += 1
        elif target.is_dir():
            shutil.copytree(target, f, symlinks=False)
            materialized += 1
        else:
            dropped += 1                  # dangling
    if materialized or dropped:
        print(f"  neutralized {materialized} escaping symlink(s), "
              f"dropped {dropped} dangling")
    return dest


def write_no_follow(dest, data):
    """Write bytes without ever following an existing symlink at `dest`."""
    dest = pathlib.Path(dest)
    if dest.is_symlink() or dest.exists():
        dest.unlink()
    dest.write_bytes(data)


def need(path, expected, what):
    got = sha(path)
    if got != expected:
        raise SystemExit(f"{what}: sha256 {got} != expected {expected}")
    print(f"  hash OK  {what}")


def verify_snapshot():
    x = _load("m2x", "bgw/m2_screening/extract.py")
    ref = _load("m2r", "bgw/m2_screening/reference.py")
    print("== snapshot verification ==")
    need(DUMP, DUMP_SHA256, DUMP.name)

    b = x.load_single(DUMP, RUNID, IQ, expected_n=N, expected_q=Q)
    chi, v, Ehat, Xhat, basis = x.matrices(b)
    print(f"  extracted run {b['runid']} q={b['q']} nmtx={b['n']}")

    Es = ref.e_star(chi, v)
    D = ref.delta(Ehat, Es)
    B = ref.formation_budget(chi, v)
    nz = sum(1 for i in range(N) for j in range(N) if D[i][j] != 0)
    bad = [(i, j) for i in range(N) for j in range(N) if abs(D[i][j]) > B[i][j]]
    print(f"  Delta nonzero in {nz}/{N * N} entries, max |Delta| = "
          f"{float(ref.max_abs(D)):.6e}")
    if bad:
        raise SystemExit(f"formation budget violated at {bad[:4]}")
    print(f"  formation budget holds; b_form = {float(ref.b_form(B)):.6e}")

    Rs, Rh = ref.exact_inverse(Es), ref.exact_inverse(Ehat)
    lhs = ref.matsub(Rh, Rs)
    rhs = [[-e for e in row] for row in ref.matmul(ref.matmul(Rh, D), Rs)]
    if lhs != rhs:
        raise SystemExit("inverse-shift identity failed")
    print("  inverse shift  R_hat - R_star = -R_hat Delta R_star  holds exactly")

    binv = ref.b_inv(Ehat, Rh, N)
    bshift = ref.b_shift(Rh, ref.b_form(B), Rs)
    btot = ref.b_total(binv, bshift)
    worst = max(sum((abs(Xhat[i][j] - Rs[i][j]) for j in range(N)), F(0))
                for i in range(N))
    print(f"  b_inv={float(binv):.6e}  b_shift={float(bshift):.6e}  "
          f"b_total={float(btot):.6e}")
    print(f"  ||X_hat - R_star||_inf = {float(worst):.6e}")
    if worst > btot:
        raise SystemExit("total budget exceeded")
    print("  total budget met")

    rc = subprocess.run(
        [sys.executable, str(ROOT / "bgw/m2_screening/check_lean_literals.py")],
        cwd=ROOT)
    if rc.returncode:
        raise SystemExit("Lean literals do not match this data")
    return 0


def _build_and_run(source, inputs, work, env):
    """Build pristine and instrumented trees and run both. Extracted in
    BGW-M2-R2 so that `reproduce` can re-verify input preservation on every
    exit path, including a failed native command."""
    outs = {}
    for tag, patched in (("pristine", False), ("instr", True)):
        tree = safe_copy_tree(source, work / f"tree-{tag}")
        if patched:
            subprocess.run(["patch", "-p1", "-i", str(PATCH)], cwd=tree, check=True)
        write_no_follow(tree / "flavor.mk", (tree / "flavor_real.mk").read_bytes())
        subprocess.run(["make", "clean"], cwd=tree, check=True,
                       stdout=subprocess.DEVNULL)
        subprocess.run(["make", "-j8", "epsilon"], cwd=tree, check=True,
                       stdout=subprocess.DEVNULL)
        run = work / f"run-{tag}"
        run.mkdir()
        for f in ("WFN", "WFNq"):
            os.symlink(inputs / f, run / f)
        write_no_follow(run / "epsilon.inp", EPSILON_INP.encode())
        with open(run / "epsilon.out", "w") as log:
            subprocess.run([tree / "Epsilon/epsilon.real.x"], cwd=run, env=env,
                           stdout=log, check=True)
        outs[tag] = run
        print(f"  {tag} run complete")

    return outs


def reproduce(source, inputs, check_proof=False):
    print("== full production reproduction ==")
    source, inputs = pathlib.Path(source).resolve(), pathlib.Path(inputs).resolve()
    need(source / "Epsilon/epsinv.f90", PRISTINE_EPSINV_SHA256, "pristine epsinv.f90")
    need(inputs / "WFN", WFN_SHA256, "WFN")
    need(inputs / "WFNq", WFNQ_SHA256, "WFNq")

    before = tree_digests(source)
    # every regular file in the supplied inputs directory, not just the two
    # pinned wavefunctions: the run directories link into this directory.
    before_inputs = tree_digests(inputs)
    # and an input path that EXISTS but cannot be digested -- a dangling link,
    # a directory, a device -- is refused rather than silently dropping out of
    # the preservation baseline, which is the layout review exploited.
    # `lexists`, not `exists`: a dangling symlink must reach this check.
    missing = [f for f in ("WFN", "WFNq")
               if os.path.lexists(inputs / f) and f not in before_inputs]
    if missing:
        raise SystemExit(
            f"{missing} did not resolve to readable regular files under "
            f"{inputs}; this driver cannot vouch for inputs it cannot digest")
    print(f"  snapshotted {len(before)} supplied source files and "
          f"{len(before_inputs)} input files for a safety check")

    work = pathlib.Path(tempfile.mkdtemp(prefix="bgw-m2-"))
    print(f"  fresh working directory {work}")
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1",
               MKL_NUM_THREADS="1", M2_RUNID=RUNID)
    outs = {}
    try:
        outs = _build_and_run(source, inputs, work, env)
    except BaseException:
        # a native command that failed may still have written; check anyway
        verify_preserved(source, before, inputs, before_inputs)
        raise
    verify_preserved(source, before, inputs, before_inputs)

    a, b = outs["pristine"] / "epsmat", outs["instr"] / "epsmat"
    if sha(a) != sha(b):
        raise SystemExit(f"PRISTINE/INSTRUMENTED MISMATCH: {sha(a)} vs {sha(b)}")
    print(f"  epsmat identical in both builds ({sha(a)[:16]}...)")

    # BGW-M2-R1: validate the COMPLETE dump and its run/q inventory BEFORE
    # selecting the retained block. The previous version sliced the first
    # matching QSTART..QEND and hashed it, so an appended duplicate of the
    # target block was discarded before any validation could see it.
    x = _load("m2x", "bgw/m2_screening/extract.py")
    dump = outs["instr"] / "m2_dump.dat"
    blocks = x.parse(dump)            # strict: a repeated run/q raises here
    foreign = sorted({r for r, _ in blocks} - {EXPECTED_RUNID})
    if foreign:
        raise SystemExit(f"dump contains foreign run ids {foreign}")
    if (EXPECTED_RUNID, IQ) not in blocks:
        raise SystemExit(f"dump has no block for run {EXPECTED_RUNID!r} q {IQ}")
    print(f"  complete dump validated: {len(blocks)} block(s), run id as expected")

    lines = dump.read_text().splitlines()
    starts = [i for i, l in enumerate(lines)
              if l.startswith(f"QSTART {RUNID} {IQ} ")]
    ends = [i for i, l in enumerate(lines) if l.startswith(f"QEND {RUNID} {IQ}")]
    if len(starts) != 1 or len(ends) != 1:
        raise SystemExit(
            f"target block appears {len(starts)} times; refusing to select one")
    slice_text = "\n".join(lines[starts[0]:ends[0] + 1]) + "\n"
    got = hashlib.sha256(slice_text.encode()).hexdigest()
    if got != DUMP_SHA256:
        raise SystemExit(f"reproduced slice {got} != committed {DUMP_SHA256}")
    print("  reproduced q-block matches the committed snapshot byte for byte")
    print(f"  artifacts left in {work} (not deleted)")
    if check_proof:
        check_lean_proof()
    return 0


def check_lean_proof():
    """Actually elaborate the certificate. Literal checking is not proof."""
    print("== kernel check ==")
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit(
            "lake not on PATH: cannot check the proof. Run "
            "`scripts/bootstrap.sh` first, or `scripts/verify.py --gate all`.")
    rc = subprocess.run([lake, "env", "lean", "GW/BGW/M2Screening.lean"], cwd=ROOT)
    if rc.returncode:
        raise SystemExit("GW/BGW/M2Screening.lean did not elaborate")
    print("  GW/BGW/M2Screening.lean elaborated (exit 0)")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--full", action="store_true",
                    help="also rebuild and rerun BerkeleyGW")
    ap.add_argument("--source", help="pristine BerkeleyGW 4.0 tree (with --full)")
    ap.add_argument("--inputs", help="directory holding WFN and WFNq (with --full)")
    ap.add_argument("--proof", action="store_true",
                    help="also elaborate GW/BGW/M2Screening.lean in Lean")
    a = ap.parse_args(argv)
    rc = verify_snapshot()
    if a.full:
        if not (a.source and a.inputs):
            raise SystemExit("--full needs --source and --inputs")
        rc |= reproduce(a.source, a.inputs, check_proof=a.proof)
    elif a.proof:
        check_lean_proof()
    print("OK")
    return rc


if __name__ == "__main__":
    sys.exit(main())

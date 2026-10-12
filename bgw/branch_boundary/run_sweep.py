#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Compile and run the T-005 branch-boundary driver, then save its evidence.

Build products go under /tmp; only the raw table and the summary are written
into the repository, under `artifacts/t005/`. The compiler is the one already
named by `bgw/export/arch.mk` -- nothing is installed and no BerkeleyGW tree is
touched or rebuilt.

    python3 bgw/branch_boundary/run_sweep.py
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARCH_MK = ROOT / "bgw" / "export" / "arch.mk"
ARCHIVED_PREFIX = "/tmp/mm/root/envs/bgw"
DRIVER = HERE / "branch_boundary.f90"
OUT_DIR = ROOT / "artifacts" / "t005"
RAW = OUT_DIR / "raw_sweep.txt"
SUMMARY = OUT_DIR / "summary.json"

#: Accepted digest and length of the transcribed BerkeleyGW file, read from the
#: accepted T-002 correspondence module rather than from any run artifact:
#: `artifacts/` is gitignored, so only these files are guaranteed to be in a
#: fresh checkout. The pristine checkout itself lives outside source control.
ACCEPTED_SOURCES = (ROOT / "GW" / "GPP" / "BerkeleyGWMap.lean",
                    ROOT / "bgw" / "kernel_transcript.f90")
PRISTINE = pathlib.Path("/tmp/bgw/BerkeleyGW-4.0-reviewed-pristine/Sigma/mtxel_cor.f90")

sys.path.insert(0, str(HERE))
import analyze  # noqa: E402


def sha256(path) -> str:
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


#: How each accepted source spells the `Sigma/mtxel_cor.f90` digest.
DIGEST_PATTERNS = {
    "GW/GPP/BerkeleyGWMap.lean":
        r"Sigma/mtxel_cor\.f90`, SHA-256\s*`([0-9a-f]{64})`, (\d+) lines",
    "bgw/kernel_transcript.f90":
        r"mtxel_cor\.f90 sha256 ([0-9a-f]{64})",
}


def accepted_digest() -> tuple[str, int]:
    """The `mtxel_cor.f90` digest and length already vouched for by accepted
    T-002 material. The sources must agree with each other."""
    digests = set()
    lines = None
    for path in ACCEPTED_SOURCES:
        key = str(path.relative_to(ROOT))
        match = re.search(DIGEST_PATTERNS[key], path.read_text())
        if not match:
            raise RuntimeError(f"{key}: no mtxel_cor.f90 digest recorded")
        digests.add(match.group(1))
        if match.lastindex and match.lastindex > 1:
            lines = int(match.group(2))
    if len(digests) != 1:
        raise RuntimeError(f"accepted sources disagree on the digest: {sorted(digests)}")
    return digests.pop(), lines


def arch_settings(path=ARCH_MK, relocate=True) -> dict:
    """The `F90free` and `FOPTS` lines of the pinned arch.mk."""
    text = pathlib.Path(path).read_text()
    out = {}
    for key in ("F90free", "FOPTS"):
        match = re.search(rf"^{key}\s*=\s*(.*)$", text, re.M)
        if not match:
            raise RuntimeError(f"{path}: no {key} line")
        out[key] = match.group(1).strip()
    # The archived arch.mk names the historical /tmp/mm prefix, which is gone.
    # BGW_TOOLCHAIN relocates it (e.g. the prefix bgw/toolchain/setup.sh makes);
    # only the path changes, never the flags.
    prefix = os.environ.get("BGW_TOOLCHAIN") if relocate else None
    if prefix:
        out = {k: v.replace(ARCHIVED_PREFIX, prefix.rstrip("/")) for k, v in out.items()}
    return out


def compile_command(exe, arch=None) -> list[str]:
    arch = arch or arch_settings()
    return shlex.split(arch["F90free"]) + shlex.split(arch["FOPTS"]) + [
        "-o", str(exe), str(DRIVER)]


def build_and_run(build_dir) -> tuple[str, dict]:
    """Compile the driver into `build_dir` and return (stdout, provenance)."""
    build_dir = pathlib.Path(build_dir)
    build_dir.mkdir(parents=True, exist_ok=True)
    arch = arch_settings()
    exe = build_dir / "branch_boundary"
    command = compile_command(exe, arch)
    compiler = command[0]
    version = subprocess.run([compiler, "--version"], capture_output=True,
                             text=True, check=True).stdout.splitlines()[0]
    subprocess.run(command, check=True, cwd=build_dir)
    completed = subprocess.run([str(exe)], check=True, capture_output=True,
                               text=True, cwd=build_dir)
    digest, source_lines = accepted_digest()
    if digest not in DRIVER.read_text():
        raise RuntimeError("the driver header does not cite the accepted digest")
    provenance = {
        "compiler": compiler,
        "compiler_version": version,
        "compile_command": " ".join(shlex.quote(part) for part in command),
        "arch_mk": str(ARCH_MK.relative_to(ROOT)),
        "arch_mk_sha256": sha256(ARCH_MK),
        "toolchain_prefix": os.environ.get("BGW_TOOLCHAIN", ARCHIVED_PREFIX),
        "driver": str(DRIVER.relative_to(ROOT)),
        "driver_sha256": sha256(DRIVER),
        "analyzer_sha256": sha256(HERE / "analyze.py"),
        "mtxel_cor_sha256_accepted": digest,
        "mtxel_cor_lines": source_lines,
        "accepted_digest_sources": [str(p.relative_to(ROOT)) for p in ACCEPTED_SOURCES],
        "pristine_path": str(PRISTINE),
        "pristine_present": PRISTINE.is_file(),
        "pristine_sha256": sha256(PRISTINE) if PRISTINE.is_file() else None,
        "transcribed_lines": {
            "gpp_setup": "Sigma/mtxel_cor.f90:772-795",
            "limits": "Sigma/mtxel_cor.f90:1698-1699",
            "wx_clamp": "Sigma/mtxel_cor.f90:1746",
            "inner_loop": "Sigma/mtxel_cor.f90:1810-1848",
            "accumulation": "Sigma/mtxel_cor.f90:1854-1855,1906-1916",
            "defaults": "Sigma/inread.f90:151-152",
            "tolerances": "Common/nrtype.f90:155,161-162",
        },
    }
    if provenance["pristine_present"] and (
            provenance["pristine_sha256"] != provenance["mtxel_cor_sha256_accepted"]):
        raise RuntimeError(
            "pristine mtxel_cor.f90 digest differs from the accepted digest; "
            "stop and report rather than re-deriving the transcription")
    return completed.stdout, provenance


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build-dir", default="/tmp/t005-build",
                    help="build directory, kept outside source control")
    ap.add_argument("--check", action="store_true",
                    help="do not write; fail if the saved table would change")
    args = ap.parse_args()

    table, provenance = build_and_run(args.build_dir)
    summary = analyze.summarize(analyze.parse_text(table))
    summary["provenance"] = provenance
    summary["claim_boundary"] = (
        "Standalone real-flavor driver re-executing the transcribed statements "
        "of sigma_gpp_cpu. Not a BerkeleyGW run, not a material calculation, "
        "and not evidence of an error in any production self-energy.")
    blob = json.dumps(summary, indent=2, sort_keys=True) + "\n"

    if args.check:
        ok = RAW.read_text() == table and SUMMARY.read_text() == blob
        print("MATCH" if ok else "DIFFERS")
        return 0 if ok else 1

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    RAW.write_text(table)
    SUMMARY.write_text(blob)
    print(f"wrote {RAW.relative_to(ROOT)} and {SUMMARY.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

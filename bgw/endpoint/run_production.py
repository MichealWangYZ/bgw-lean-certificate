#!/usr/bin/env python3
"""Run the pinned Si-EPM GPP calculation (E0) with the pristine binaries.

    python3 bgw/endpoint/run_production.py OUTDIR [--tree TREE] [--blas-threads N]
        [--set FILE:KEY=VALUE ...]

Inputs are the shipped testsuite files, checked against the committed copies
in `bgw/export/` by sha256. `--set` overrides one keyword line in one input
file (used by the convergence sweeps; E0 itself uses none). The run directory
gets `run.json` with every input and binary hash, the thread environment and
the overrides, so a result can always be traced to what produced it.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
# BGW_TREE overrides the default location (e.g. node-local scratch on a cluster)
DEFAULT_TREE = pathlib.Path(os.environ.get("BGW_TREE", pathlib.Path.home() / "bgw-src/pristine/BerkeleyGW-4.0"))
INPUTS = {
    "WFN.in": "72e47aa2ceebf79972603cf16fc35e5162ae07bb7c15370d3760433f0e3d0e29",
    "WFNq.in": "dfc1641e9214b3f8d8d302cddcf8b775a570a8d5a6e8f64c985d46f558d140b7",
    "WFN_co.in": "f83257277a3152645f9556f4b18c11d4c08026521e259fe0a042db4988085237",
    "epsilon.inp": "b5b1a11a623c8efb2830df607833e2a7aab0377a96be9c34c988de163b0aa3b1",
    "sig_GPP.inp": "0407b52140212a2d46ab41052526a6b6fbfc1f5f61119f3fb0492a84dff46fd5",
}
BINARIES = ["MeanField/EPM/epm2bgw.x", "Epsilon/epsilon.real.x", "Sigma/sigma.real.x"]


def sha256(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def apply_override(text, key, value):
    """Replace the single line starting with `key`, or append it if absent.
    A block override (value containing newlines) replaces the `begin key` ...
    `end` block."""
    if "\n" in value:
        pat = re.compile(rf"^begin {re.escape(key)}\n.*?^end\n", re.M | re.S)
        if len(pat.findall(text)) != 1:
            raise ValueError(f"block {key!r} not found exactly once")
        return pat.sub(lambda _: f"begin {key}\n{value.rstrip()}\nend\n", text)
    pat = re.compile(rf"^{re.escape(key)}\b.*$", re.M)
    hits = pat.findall(text)
    if len(hits) > 1:
        raise ValueError(f"key {key!r} appears {len(hits)} times")
    if hits:
        return pat.sub(f"{key} {value}", text)
    return text.rstrip("\n") + f"\n{key} {value}\n"


def run(out, tree=DEFAULT_TREE, blas_threads=None, overrides=(), input_texts=None):
    out = pathlib.Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    tree = pathlib.Path(tree).resolve()
    texts = {}
    for name, digest in INPUTS.items():
        src = ROOT / "bgw/export" / name
        if sha256(src) != digest:
            raise ValueError(f"committed input {name} does not match its pinned hash")
        texts[name] = src.read_text()
    if input_texts:                      # whole-file replacements (sweeps)
        texts.update(input_texts)
    for spec in overrides:
        fname, kv = spec.split(":", 1)
        key, value = kv.split("=", 1)
        texts[fname] = apply_override(texts[fname], key, value)
    for name, text in texts.items():
        (out / name).write_text(text)
    env = dict(os.environ)
    if blas_threads is not None:
        env.update(OPENBLAS_NUM_THREADS=str(blas_threads), OMP_NUM_THREADS=str(blas_threads))
    record = {"tree": str(tree),
              "binaries": {b: sha256(tree / b) for b in BINARIES},
              "inputs": {n: hashlib.sha256(t.encode()).hexdigest() for n, t in texts.items()},
              "pinned_inputs_unchanged": not overrides and not input_texts,
              "overrides": list(overrides),
              "threads": {k: env.get(k) for k in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS")},
              "steps": []}

    def execute(binary, log, stdin_name=None):
        with (out / log).open("w") as fh:
            stdin = (out / stdin_name).open() if stdin_name else None
            try:
                r = subprocess.run([str(tree / binary)], cwd=out, env=env, stdin=stdin,
                                   stdout=fh, stderr=subprocess.STDOUT, timeout=7200)
            finally:
                if stdin:
                    stdin.close()
        record["steps"].append({"binary": binary, "log": log, "rc": r.returncode})
        if r.returncode != 0:
            raise RuntimeError(f"{binary} exited {r.returncode}; see {out / log}")

    try:
        for name in ("WFN", "WFNq", "WFN_co"):
            execute(BINARIES[0], name + ".out", name + ".in")
        execute(BINARIES[1], "epsilon.out")
        shutil.copy2(out / "sig_GPP.inp", out / "sigma.inp")
        execute(BINARIES[2], "sigma.out")
        record["outputs"] = {n: sha256(out / n) for n in
                             ("WFN", "WFNq", "WFN_inner", "RHO", "eps0mat", "epsmat",
                              "sigma_hp.log") if (out / n).exists()}
        record["status"] = "done"
    except Exception as e:  # recorded, then re-raised
        record["status"] = f"failed: {e}"
        raise
    finally:
        (out / "run.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("out")
    ap.add_argument("--tree", default=str(DEFAULT_TREE))
    ap.add_argument("--blas-threads", type=int)
    ap.add_argument("--set", action="append", default=[], dest="overrides")
    a = ap.parse_args(argv)
    rec = run(a.out, a.tree, a.blas_threads, a.overrides)
    print(json.dumps(rec["outputs"], indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())

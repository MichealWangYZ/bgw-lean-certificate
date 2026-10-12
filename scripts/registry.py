#!/usr/bin/env python3
"""Generate the project's shared registries from the source tree (WRAPUP item 4).

Before this script, each new module or test meant four or five hand edits in shared
files. Parallel workers each made them, and the edits collided. Now one command writes
all of them, and `--check` fails on drift:

    python3 scripts/registry.py           # (re)generate in place
    python3 scripts/registry.py --check   # exit 1 and list every drifted registry

Registries and the rule each one follows:

1. `GW.lean` import block: every module of the DEFAULT library, sorted. A module
   `GW/**/X.lean` is in the default library unless it is `GW/Audit.lean`, or lies under
   `GW/Endpoint/Kernel/Data/`, or imports such a module (directly or transitively).
   Those modules belong to the non-default target `GWKernelData`, which can take hours
   to build. The docstring above the imports is kept verbatim.
2. `scripts/CheckAxioms.lean` import block: `GW`, `Main`, then every `GWKernelData`
   root in `lakefile.toml` order. The audit body below the imports is hand-written and
   kept verbatim. `scripts/CheckAxiomsFast.lean` is generated whole: imports `GW` and
   `Main` only (no kernel data), then the same body. The fast gate runs it.
3. `scripts/gates.py` partition: every `tests/test_*.py`, sorted. A module is in WORKFLOW
   iff the first line of its module docstring starts with `WORKFLOW GATE`. Otherwise it
   is SCIENTIFIC. The default is the gate that must never be weakened.
4. `bgw/weighted_audit/PROVENANCE-R6.txt` digests: re-hash every path the manifest
   already lists, as `scripts/make_manifest.py` does. Entries are never added or
   removed; deciding what is vouched for stays a human act. This step runs last,
   because the manifest vouches for `GW.lean` and `scripts/gates.py`.

NOT generated: `GW/Audit.lean`. It is the curated NAMED list of Specification.md S5:
1316 headline theorems in prose-annotated sections, a deliberate subset of the declared
theorems. The exhaustive check is CheckAxioms. Generating the named list from all
declared theorems would change what it means. `--check` only verifies its structure:
it imports `GW` and nothing else, it names no theorem twice, and it contains every S5
required name.
"""

import argparse
import ast
import hashlib
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA_PREFIX = "GW.Endpoint.Kernel.Data."
MANIFEST = ROOT / "bgw" / "weighted_audit" / "PROVENANCE-R6.txt"
S5_REQUIRED = (
    "GW.GPP.rawOccupied_eq_occupiedTerm", "GW.GPP.occupiedTerm_at_pole",
    "GW.GPP.continuousAt_occupiedTerm", "GW.GPP.tendsto_rawOccupied_nhdsWithin_ne",
    "GW.GPP.Term.valueUnchecked_cast", "GW.GPP.Data.sigmaUnchecked_cast",
    "GW.GPP.Data.sigmaChecked_ok_eq_real", "GW.GPP.Data.sigmaChecked_ok_valid",
)
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def project_modules():
    """name -> list of imported project modules, for every GW/**/*.lean."""
    out = {}
    for p in sorted((ROOT / "GW").rglob("*.lean")):
        out[module_name(p)] = [m for m in IMPORT.findall(p.read_text())
                               if m == "GW" or m.startswith("GW.")]
    return out


def default_lib(mods):
    """Default-library modules: rule 1 of the module docstring."""
    kernel = {m for m in mods if m.startswith(DATA_PREFIX)}
    changed = True
    while changed:
        changed = False
        for m, deps in mods.items():
            if m not in kernel and any(d in kernel for d in deps):
                kernel.add(m)
                changed = True
    return sorted(m for m in mods if m not in kernel and m not in ("GW.Audit", "GW"))


def split_imports(text):
    """(head, imports, tail): the text before the first import line, the import
    lines, and the rest. Imports must be contiguous (blank/comment lines allowed)."""
    lines = text.split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith("import ")]
    if not idx:
        raise SystemExit("no import block")
    first, last = idx[0], idx[-1]
    return "\n".join(lines[:first]), lines[first:last + 1], "\n".join(lines[last + 1:])


def gen_gw_lean(mods):
    head, _, tail = split_imports((ROOT / "GW.lean").read_text())
    body = "\n".join(f"import {m}" for m in default_lib(mods))
    return f"{head}\n{body}\n{tail.lstrip(chr(10))}" if tail.strip() else f"{head}\n{body}\n"


def kernel_roots():
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
    for lib in lake["lean_lib"]:
        if lib["name"] == "GWKernelData":
            return lib["roots"]
    raise SystemExit("lakefile.toml has no GWKernelData lib")


AUDIT_HEAD = """-- GENERATED import block: `python3 scripts/registry.py` writes it (GW, Main, then every
-- GWKernelData root of lakefile.toml, in that order); `--check` fails on drift. The audit
-- body below the imports is hand-written and kept verbatim."""


def audit_body():
    """(library imports, body) of CheckAxioms.lean: the non-project imports of its
    import block (e.g. `Lean.Util.CollectAxioms`), and everything after the block."""
    _, block, tail = split_imports((ROOT / "scripts" / "CheckAxioms.lean").read_text())
    libs = [l for l in block if l.startswith("import ")
            and not (l.split()[1] in ("GW", "Main") or l.split()[1].startswith("GW."))]
    return "\n".join(libs), tail


def gen_check_axioms(roots, body):
    libs, tail = body
    imports = "\n".join(f"import {m}" for m in ["GW", "Main", *roots])
    return f"{AUDIT_HEAD}\n{imports}\n{libs}\n{tail}"


FAST_HEAD = """-- GENERATED by `python3 scripts/registry.py` from scripts/CheckAxioms.lean: the same
-- memoized audit over the default library only (GW, Main; no GWKernelData), for the fast
-- gate (`scripts/verify.sh --gate fast`). Do not edit; edit CheckAxioms.lean and regenerate."""


def gen_check_axioms_fast(body):
    libs, tail = body
    return f"{FAST_HEAD}\nimport GW\nimport Main\n{libs}\n{tail}"


def test_gate(path):
    doc = ast.get_docstring(ast.parse(path.read_text())) or ""
    first = doc.splitlines()[0] if doc else ""
    return "workflow" if first.startswith("WORKFLOW GATE") else "scientific"


def gen_gates():
    text = (ROOT / "scripts" / "gates.py").read_text()
    sci, wf = [], []
    for p in sorted((ROOT / "tests").glob("test_*.py")):
        (wf if test_gate(p) == "workflow" else sci).append(f"tests.{p.stem}")

    def block(name, items):
        return f"{name} = (\n" + "".join(f'    "{m}",\n' for m in items) + ")"

    for name, items in (("SCIENTIFIC", sci), ("WORKFLOW", wf)):
        pat = re.compile(rf"^{name} = \(\n(?:    \"[^\"]+\",\n)*\)", re.M)
        if not pat.search(text):
            raise SystemExit(f"scripts/gates.py: no `{name} = (...)` block")
        text = pat.sub(lambda _m, b=block(name, items): b, text, count=1)
    return text


DIGEST = re.compile(r"^([0-9a-f]{64})  (.+)$", re.M)


def gen_manifest(overrides):
    """Manifest text with every listed digest recomputed. `overrides` maps a
    repo-relative path to the bytes it WILL have (so --check can account for the
    registries regenerated above without writing them)."""
    text = MANIFEST.read_text()

    def fix(m):
        rel = m.group(2)
        data = overrides.get(rel)
        if data is None:
            target = ROOT / rel
            if not target.exists():
                raise SystemExit(f"{MANIFEST.name}: listed path missing: {rel}")
            data = target.read_bytes()
        return f"{hashlib.sha256(data).hexdigest()}  {rel}"

    return DIGEST.sub(fix, text)


def check_audit_lean():
    text = (ROOT / "GW" / "Audit.lean").read_text()
    problems = []
    imports = IMPORT.findall(text)
    if imports != ["GW"]:
        problems.append(f"GW/Audit.lean must import exactly GW, has {imports}")
    names = re.findall(r"^#print axioms (\S+)", text, re.M)
    dup = sorted({n for n in names if names.count(n) > 1})
    if dup:
        problems.append(f"GW/Audit.lean names theorems twice: {dup[:10]}")
    missing = [n for n in S5_REQUIRED if n not in names]
    if missing:
        problems.append(f"GW/Audit.lean lacks S5 required names: {missing}")
    return problems


def check_fast_partition(gates_text):
    """Every SCIENTIFIC module is in exactly one of gates.FAST / gates.ARCHIVED_TESTS."""
    ns = {}
    exec(compile(gates_text, "scripts/gates.py", "exec"), ns)
    sci, fast, arch = set(ns["SCIENTIFIC"]), set(ns["FAST"]), set(ns["ARCHIVED_TESTS"])
    problems = []
    if sci - fast - arch:
        problems.append(f"scripts/gates.py: SCIENTIFIC modules in neither FAST nor "
                        f"ARCHIVED_TESTS: {sorted(sci - fast - arch)}")
    if fast & arch:
        problems.append(f"scripts/gates.py: in both FAST and ARCHIVED_TESTS: {sorted(fast & arch)}")
    if (fast | arch) - sci:
        problems.append(f"scripts/gates.py: FAST/ARCHIVED_TESTS name non-SCIENTIFIC modules: "
                        f"{sorted((fast | arch) - sci)}")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true",
                    help="write nothing; exit 1 if any registry differs from its generated form")
    a = ap.parse_args(argv)

    mods = project_modules()
    body = audit_body()
    targets = {
        "GW.lean": gen_gw_lean(mods),
        "scripts/CheckAxioms.lean": gen_check_axioms(kernel_roots(), body),
        "scripts/CheckAxiomsFast.lean": gen_check_axioms_fast(body),
        "scripts/gates.py": gen_gates(),
    }
    overrides = {rel: t.encode() for rel, t in targets.items()}
    targets[str(MANIFEST.relative_to(ROOT))] = gen_manifest(overrides)

    drift = []
    for rel, new in targets.items():
        path = ROOT / rel
        old = path.read_text() if path.exists() else None
        if old != new:
            drift.append(rel)
            if not a.check:
                path.write_text(new)
    problems = check_audit_lean() + check_fast_partition(targets["scripts/gates.py"])
    for p in problems:
        print(f"REGISTRY: {p}", file=sys.stderr)
    if a.check:
        for rel in drift:
            print(f"REGISTRY DRIFT: {rel} differs from its generated form; "
                  f"run `python3 scripts/registry.py`", file=sys.stderr)
        ok = not drift and not problems
        print("registry check: " + ("OK" if ok else "FAILED"))
        return 0 if ok else 1
    for rel in drift:
        print(f"regenerated {rel}")
    print(f"{len(drift)} regenerated, {len(targets) - len(drift)} unchanged")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())

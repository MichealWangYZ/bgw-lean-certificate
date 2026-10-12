#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- BGW-M3: strictly parse the transition-sum dump into per-q blocks.

The M3 dump records, for one static-polarizability q block, the operands the
code consumed BEFORE it folded the energy denominator into the matrix
elements. `Epsilon/mtxel.f90` says so itself:

    ! In the static case, we lump sqrt(eden) into the matrix elements gme.

so an export taken after that multiply is an already-weighted product, not a
physical operand. `GMERAW` is taken immediately before it.

Every value carries a 17-digit decimal AND its raw IEEE-754 bits; the bits are
the truth and the decimal is checked against them. The bracket discipline is
M2's, for the same reason: a record outside a bracket, a nested or repeated
bracket, or an unterminated block is an error, so nothing can be sliced out of
an unvalidated file.

Primitives are imported from M1's repaired boundary rather than rewritten.
"""

import importlib.util
import pathlib

_ROOT = pathlib.Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location(
    "m1_extract", _ROOT / "bgw" / "m1_screening" / "extract.py")
_m1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_m1)

ExtractionError = _m1.ExtractionError
bits_to_exact = _m1.bits_to_exact
sha256 = _m1.sha256
require_sha256 = _m1.require_sha256

#: exactly once per block
_SCALAR = ("FACT", "CELVOL", "GEOM", "GRID", "PATCHED")
#: keyed by (irk, ispin, iv, ic)
_PER_TRANSITION = ("EDEN", "KFACT", "SLOT", "TRANS")


def _value(fields, decimal_at, bits_at, lineno, what):
    """Exact value from the raw bits, cross-checked against the decimal."""
    exact, as_float = bits_to_exact(int(fields[bits_at]))
    shown = float(fields[decimal_at])
    if as_float != shown:
        raise ExtractionError(
            f"line {lineno}: {what} decimal {shown!r} does not match its bit "
            f"pattern {float(exact)!r}")
    return exact


def _finish(block, lineno):
    n, nrk = block["n"], block["nrk"]
    if n < 1 or nrk < 1:
        raise ExtractionError(f"line {lineno}: q {block['iq']} has nmtx={n} nrk={nrk}")
    for name in _SCALAR:
        if name not in block["scalars"]:
            raise ExtractionError(f"line {lineno}: q {block['iq']} has no {name}")

    # the star inventory: every irk must carry a contiguous 1..nst(irk), and
    # every (irk, it) a complete 1..n map.
    nst = {}
    for (irk, it, ia) in block["map"]:
        nst[irk] = max(nst.get(irk, 0), it)
    if sorted(nst) != list(range(1, nrk + 1)):
        raise ExtractionError(
            f"line {lineno}: MAP covers irk {sorted(nst)}, want 1..{nrk}")
    for irk, top in nst.items():
        for it in range(1, top + 1):
            missing = [ia for ia in range(1, n + 1)
                       if (irk, it, ia) not in block["map"]]
            if missing:
                raise ExtractionError(
                    f"line {lineno}: MAP irk {irk} it {it} missing "
                    f"{missing[:4]} of 1..{n}")
    block["nst"] = nst

    # the transition inventory: identical key sets, and a complete GMERAW row.
    keys = set(block["EDEN"])
    for name in _PER_TRANSITION:
        if set(block[name]) != keys:
            extra = sorted(set(block[name]) ^ keys)[:4]
            raise ExtractionError(
                f"line {lineno}: {name} and EDEN disagree on transitions "
                f"{extra}")
    if set(block["gme"]) != keys:
        extra = sorted(set(block["gme"]) ^ keys)[:4]
        raise ExtractionError(f"line {lineno}: GMERAW covers other transitions {extra}")
    for key, row in block["gme"].items():
        missing = [ia for ia in range(1, n + 1) if ia not in row]
        if missing:
            raise ExtractionError(
                f"line {lineno}: GMERAW {key} missing components {missing[:4]}")
    if not keys:
        raise ExtractionError(f"line {lineno}: q {block['iq']} has no transitions")
    block["closed"] = True
    return block


def parse(path):
    """Strictly parse an M3 dump into per-q blocks keyed by (run id, iq)."""
    blocks, cur, key = {}, None, None
    for lineno, raw in enumerate(pathlib.Path(path).read_text().splitlines(), 1):
        f = raw.split()
        if not f:
            continue
        tag = f[0]
        if tag == "TSTART":
            if cur is not None:
                raise ExtractionError(
                    f"line {lineno}: TSTART while q {cur['iq']} is still open")
            key = (f[1], int(f[2]))
            if key in blocks:
                raise ExtractionError(
                    f"line {lineno}: run {f[1]!r} q {f[2]} appears twice")
            cur = {"runid": f[1], "iq": int(f[2]), "scalars": {}, "map": {},
                   "gme": {}, "closed": False}
            for name in _PER_TRANSITION:
                cur[name] = {}
            continue
        if tag == "TEND":
            if cur is None:
                raise ExtractionError(f"line {lineno}: TEND with no open block")
            if (f[1], int(f[2])) != key:
                raise ExtractionError(
                    f"line {lineno}: TEND {f[1]!r} q {f[2]} closes "
                    f"{key[0]!r} q {key[1]}")
            blocks[key] = _finish(cur, lineno)
            cur, key = None, None
            continue
        if cur is None:
            raise ExtractionError(f"line {lineno}: {tag} outside any q block")

        if tag == "FACT" or tag == "CELVOL":
            cur["scalars"][tag] = _value(f, 1, 2, lineno, tag)
        elif tag == "GEOM":
            cur["n"], cur["nrk"] = int(f[1]), int(f[2])
            cur["nspin"], cur["nspinor"] = int(f[3]), int(f[4])
            cur["scalars"][tag] = tuple(int(x) for x in f[1:5])
        elif tag == "GRID":
            cur["scalars"][tag] = tuple(int(x) for x in f[1:5])
        elif tag == "PATCHED":
            cur["scalars"][tag] = f[1] == "T"
        elif tag == "MAP":
            irk, it, ia, ind = (int(x) for x in f[1:5])
            k = (irk, it, ia)
            if k in cur["map"]:
                raise ExtractionError(f"line {lineno}: MAP {k} appears twice")
            cur["map"][k] = (ind, _value(f, 5, 6, lineno, "MAP phase"))
        elif tag in ("EDEN", "KFACT"):
            k = tuple(int(x) for x in f[1:5])
            if k in cur[tag]:
                raise ExtractionError(f"line {lineno}: {tag} {k} appears twice")
            cur[tag][k] = _value(f, 5, 6, lineno, tag)
        elif tag == "SLOT":
            k = tuple(int(x) for x in f[1:5])
            if k in cur["SLOT"]:
                raise ExtractionError(f"line {lineno}: SLOT {k} appears twice")
            cur["SLOT"][k] = (int(f[5]), int(f[6]))
        elif tag == "TRANS":
            k = tuple(int(x) for x in f[1:5])
            if k in cur["TRANS"]:
                raise ExtractionError(f"line {lineno}: TRANS {k} appears twice")
            cur["TRANS"][k] = tuple(
                _value(f, 5 + m, 9 + m, lineno, f"TRANS field {m}")
                for m in range(4))
        elif tag == "GMERAW":
            irk, ispin, iv, ic, ia = (int(x) for x in f[1:6])
            k = (irk, ispin, iv, ic)
            row = cur["gme"].setdefault(k, {})
            if ia in row:
                raise ExtractionError(f"line {lineno}: GMERAW {k} component {ia} twice")
            row[ia] = _value(f, 6, 7, lineno, "GMERAW")
        else:
            raise ExtractionError(f"line {lineno}: unknown record {tag!r}")
    if cur is not None:
        raise ExtractionError(f"q {cur['iq']} is never closed")
    if not blocks:
        raise ExtractionError("no q blocks found")
    return blocks


def load_single(path, runid, iq, expected_n=None, expected_nrk=None):
    """The one block for `runid` and `iq`, with its shape checked by the caller."""
    blocks = parse(path)
    if (runid, iq) not in blocks:
        raise ExtractionError(
            f"no block for run {runid!r} q {iq}; file has "
            f"{sorted(blocks)[:4]}")
    b = blocks[(runid, iq)]
    if expected_n is not None and b["n"] != expected_n:
        raise ExtractionError(f"q {iq} has nmtx {b['n']}, expected {expected_n}")
    if expected_nrk is not None and b["nrk"] != expected_nrk:
        raise ExtractionError(f"q {iq} has nrk {b['nrk']}, expected {expected_nrk}")
    return b

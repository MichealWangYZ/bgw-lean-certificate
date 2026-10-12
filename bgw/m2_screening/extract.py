#!/usr/bin/env python3
"""Exact extraction of the BGW-M2 operand export.

Reuses the parser boundary repaired in BGW-M1-R1 rather than starting another
ad hoc name-keyed dictionary: the low-level primitives (`bits_to_exact`,
`ExtractionError`, `sha256`, `require_sha256`) are imported from
`bgw/m1_screening/extract.py`, and the same rejection rules apply -- repeated
q, nested `QSTART`, mismatched `QEND`, data outside a block, in-block
duplicates, out-of-range or missing labels, inconsistent dimension.

M2 adds a **run identity** on every block delimiter. Records from two different
runs can therefore never be joined silently, which matters because the Fortran
instrumentation opens its dump in append mode.

Record set, all at the same q and in the same ordered basis:

    CHI    i j   pol%chi(i,j,1)   -- the operand the formation loop consumes
    VCOUL  i     vcoul(i)         -- the row Coulomb factor
    GVEC   i gx gy gz ekin        -- the ordered retained basis
    EPSPRE i j   eps(i,j)         -- stored pre-inversion E_hat
    EPSINV i j   eps(i,j)         -- production inverse X_hat

`chi` is read, never written, in `Epsilon/epsinv.f90`, so the exported values
are exactly those used to build `eps`. Nothing here is reconstructed by
inverting or rearranging the answer under test.
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

#: matrix-valued records, and the per-index records
_PAIR = ("CHI", "EPSPRE", "EPSINV")
_SINGLE = ("VCOUL",)


def _finish(block, lineno):
    n = block["n"]
    if n < 1:
        raise ExtractionError(f"line {lineno}: q {block['iq']} has nmtx={n}")
    if len(block["vcoul"]) != n:
        raise ExtractionError(
            f"line {lineno}: q {block['iq']} vcoul has {len(block['vcoul'])} "
            f"entries, want {n}")
    if len(block["gvec"]) != n:
        raise ExtractionError(
            f"line {lineno}: q {block['iq']} gvec has {len(block['gvec'])} "
            f"entries, want {n}")
    for name in _PAIR:
        got = block[name]
        if len(got) != n * n:
            raise ExtractionError(
                f"line {lineno}: q {block['iq']} {name} has {len(got)} entries, "
                f"want {n * n}")
        missing = [(i, j) for i in range(1, n + 1) for j in range(1, n + 1)
                   if (i, j) not in got]
        if missing:
            raise ExtractionError(
                f"line {lineno}: q {block['iq']} {name} missing {missing[:4]}")
    block["closed"] = True
    return block


def parse(path):
    """Strictly parse an M2 dump into per-q blocks keyed by run id."""
    path = pathlib.Path(path)
    blocks, cur = {}, None
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        t = line.split()
        if not t:
            continue
        if t[0] == "QSTART":
            if cur is not None:
                raise ExtractionError(
                    f"line {lineno}: QSTART while q {cur['iq']} of run "
                    f"{cur['runid']!r} is still open")
            if len(t) != 7:
                raise ExtractionError(f"line {lineno}: malformed QSTART {line!r}")
            runid, iq = t[1], int(t[2])
            if (runid, iq) in blocks:
                raise ExtractionError(
                    f"line {lineno}: run {runid!r} q {iq} appears twice; the "
                    f"dump is appended to, so select one run explicitly")
            cur = {"runid": runid, "iq": iq,
                   "q": tuple(float(x) for x in t[3:6]), "n": int(t[6]),
                   "vcoul": {}, "gvec": {}, "CHI": {}, "EPSPRE": {},
                   "EPSINV": {}, "closed": False}
        elif t[0] == "QEND":
            if cur is None:
                raise ExtractionError(f"line {lineno}: QEND outside a block")
            if (t[1], int(t[2])) != (cur["runid"], cur["iq"]):
                raise ExtractionError(
                    f"line {lineno}: QEND {t[1]!r}/{t[2]} closes "
                    f"{cur['runid']!r}/{cur['iq']}")
            blocks[(cur["runid"], cur["iq"])] = _finish(cur, lineno)
            cur = None
        elif t[0] in _PAIR or t[0] in _SINGLE or t[0] == "GVEC":
            if cur is None:
                raise ExtractionError(f"line {lineno}: {t[0]} outside a q block")
            n = cur["n"]
            if t[0] == "GVEC":
                key = int(t[1])
                if not 1 <= key <= n:
                    raise ExtractionError(
                        f"line {lineno}: GVEC index {key} outside 1..{n}")
                if key in cur["gvec"]:
                    raise ExtractionError(
                        f"line {lineno}: duplicate GVEC {key} inside q {cur['iq']}")
                cur["gvec"][key] = ((int(t[2]), int(t[3]), int(t[4])), float(t[5]))
                continue
            if t[0] in _SINGLE:
                key, dec, bits, store = int(t[1]), t[2], t[3], cur["vcoul"]
                if not 1 <= key <= n:
                    raise ExtractionError(
                        f"line {lineno}: {t[0]} index {key} outside 1..{n}")
            else:
                key, dec, bits, store = (int(t[1]), int(t[2])), t[3], t[4], cur[t[0]]
                if not (1 <= key[0] <= n and 1 <= key[1] <= n):
                    raise ExtractionError(
                        f"line {lineno}: {t[0]} index {key} outside 1..{n}")
            exact, asfloat = bits_to_exact(bits)
            if asfloat != float(dec):
                raise ExtractionError(
                    f"line {lineno}: decimal {dec} != bits {bits} ({asfloat!r})")
            if asfloat != asfloat or asfloat in (float("inf"), float("-inf")):
                raise ExtractionError(f"line {lineno}: non-finite value {asfloat!r}")
            if key in store:
                raise ExtractionError(
                    f"line {lineno}: duplicate {t[0]} key {key} inside q {cur['iq']}")
            store[key] = exact
        else:
            raise ExtractionError(f"line {lineno}: unknown record {t[0]!r}")
    if cur is not None:
        raise ExtractionError(f"block {cur['runid']!r}/{cur['iq']} not terminated")
    if not blocks:
        raise ExtractionError("dump contains no complete block")
    return blocks


def load_single(path, runid, iq, expected_n=None, expected_q=None):
    """Require EXACTLY one block, with the specified run id and q.

    The expected inventory is the caller's, from the specification.
    """
    blocks = parse(path)
    if set(blocks) != {(runid, iq)}:
        raise ExtractionError(
            f"expected exactly {{({runid!r}, {iq})}}, found {sorted(blocks)}")
    b = blocks[(runid, iq)]
    if expected_n is not None and b["n"] != expected_n:
        raise ExtractionError(f"nmtx {b['n']} != {expected_n}")
    if expected_q is not None and b["q"] != tuple(expected_q):
        raise ExtractionError(f"q {b['q']} != {tuple(expected_q)}")
    return b


def matrices(block):
    """Exact `chi`, `vcoul`, `E_hat`, `X_hat` and the ordered basis."""
    if not block.get("closed"):
        raise ExtractionError("block never closed validly")
    n = block["n"]
    grab = lambda name: [[block[name][(i + 1, j + 1)] for j in range(n)]
                         for i in range(n)]
    return (grab("CHI"), [block["vcoul"][i + 1] for i in range(n)],
            grab("EPSPRE"), grab("EPSINV"),
            [block["gvec"][i + 1] for i in range(n)])

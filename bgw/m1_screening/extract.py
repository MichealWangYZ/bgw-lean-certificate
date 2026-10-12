#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Exact extraction of one BerkeleyGW 4.0 static screening stage.

Reads the instrumentation dump written by a patched `Epsilon/epsinv.f90`
(`bgw/m1_screening/epsinv_dump.patch`) and returns EXACT rational matrices.

Every value is dumped twice by the instrumentation: as a 17-significant-digit
decimal and as the raw IEEE-754 bit pattern of the same `real(DP)`. This module
requires them to agree for every entry, which is the round-trip check: it rules
out a formatting or parsing error silently changing a number.

A float64 is a dyadic rational, so the exact rational value is recovered with no
approximation. Note the interpretation carefully: this is the exact rational
value OF THE STORED DOUBLE. It is not the unrounded physical dielectric matrix,
and forming E exactly from rounded chi0 and vcoul is a different problem.

Convention, read from the pinned source `Epsilon/epsinv.f90` (BerkeleyGW 4.0):

    eps(i,j) = delta_ij - vcoul(i) * chi(i,j)

so E = I - V*chi with V DIAGONAL acting on the row index, unsymmetrized.
`epsmat` stores the INVERSE (source comment: "2. Inverts epsilon. 3. Writes the
result"). The inversion is in-place: `call X(invert_serial)(pol%nmtx, eps)`.
"""

from fractions import Fraction as F
import hashlib
import pathlib
import struct


class ExtractionError(ValueError):
    """The dump is not a usable exact export."""


def bits_to_exact(bits):
    """Exact rational value of the float64 with this IEEE-754 bit pattern."""
    x = struct.unpack("<d", struct.pack("<q", int(bits)))[0]
    return F(x), x


def _finish(block, lineno):
    """Validate a block the moment it closes. A block that never closes, or
    closes malformed, must not contribute data."""
    n = block["n"]
    if n < 1:
        raise ExtractionError(f"line {lineno}: q {block['iq']} has nmtx={n}")
    if len(block["vcoul"]) != n:
        raise ExtractionError(
            f"line {lineno}: q {block['iq']} has {len(block['vcoul'])} vcoul "
            f"entries, want {n}")
    for name in ("pre", "inv"):
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
    """Parse the dump into per-q blocks, strictly.

    Rejected, because the Fortran instrumentation opens its output in APPEND
    mode and a rerun therefore accumulates blocks in one file:

    * a repeated q id -- silently keeping the last one would let a corrupted
      run be masked by a later good run of the same q;
    * a `QSTART` before the current block's `QEND` -- an interrupted run
      followed by a good one must not merge into a valid-looking block;
    * a `QEND` that does not match the open block, or data outside a block;
    * a block that closes with a missing, duplicated or out-of-range label,
      or an inconsistent dimension.

    Every value must also pass the decimal/bits round trip.
    """
    path = pathlib.Path(path)
    blocks, cur = {}, None
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        t = line.split()
        if not t:
            continue
        if t[0] == "QSTART":
            if cur is not None:
                raise ExtractionError(
                    f"line {lineno}: QSTART {t[1]} while q {cur['iq']} is still "
                    f"open; an unterminated block may not be followed by another")
            iq = int(t[1])
            if iq in blocks:
                raise ExtractionError(
                    f"line {lineno}: q {iq} appears twice; the dump is appended "
                    f"to, so this is two runs in one file -- select one run "
                    f"explicitly instead of taking the last block")
            if len(t) != 6:
                raise ExtractionError(f"line {lineno}: malformed QSTART {line!r}")
            cur = {"iq": iq, "q": tuple(float(x) for x in t[2:5]),
                   "n": int(t[5]), "vcoul": {}, "pre": {}, "inv": {},
                   "closed": False}
        elif t[0] == "QEND":
            if cur is None:
                raise ExtractionError(f"line {lineno}: QEND outside a block")
            if cur["iq"] != int(t[1]):
                raise ExtractionError(
                    f"line {lineno}: QEND {t[1]} closes q {cur['iq']}")
            blocks[cur["iq"]] = _finish(cur, lineno)
            cur = None
        elif t[0] in ("VCOUL", "EPSPRE", "EPSINV"):
            if cur is None:
                raise ExtractionError(f"line {lineno}: {t[0]} outside a q block")
            n = cur["n"]
            if t[0] == "VCOUL":
                key, dec, bits = int(t[1]), t[2], t[3]
                store = cur["vcoul"]
                if not 1 <= key <= n:
                    raise ExtractionError(
                        f"line {lineno}: VCOUL index {key} outside 1..{n}")
            else:
                key, dec, bits = (int(t[1]), int(t[2])), t[3], t[4]
                store = cur["pre" if t[0] == "EPSPRE" else "inv"]
                if not (1 <= key[0] <= n and 1 <= key[1] <= n):
                    raise ExtractionError(
                        f"line {lineno}: {t[0]} index {key} outside 1..{n}")
            exact, asfloat = bits_to_exact(bits)
            if asfloat != float(dec):
                raise ExtractionError(
                    f"line {lineno}: decimal {dec} != bits {bits} "
                    f"({asfloat!r}); extraction is not exact")
            if key in store:
                raise ExtractionError(
                    f"line {lineno}: duplicate {t[0]} key {key} inside q "
                    f"{cur['iq']}")
            store[key] = exact
        else:
            raise ExtractionError(f"line {lineno}: unknown record {t[0]!r}")
    if cur is not None:
        raise ExtractionError(f"q block {cur['iq']} not terminated")
    if not blocks:
        raise ExtractionError("dump contains no complete q block")
    return blocks


def load_single(path, expected_iq, expected_n=None, expected_q=None):
    """Load a dump that must contain EXACTLY the one specified q block.

    The expected inventory is the caller's, from the specification -- not
    whatever the file happens to hold. An extra q block is a different run or a
    different selection and is rejected rather than ignored.
    """
    blocks = parse(path)
    if set(blocks) != {expected_iq}:
        raise ExtractionError(
            f"expected exactly q {{{expected_iq}}}, found {sorted(blocks)}")
    block = blocks[expected_iq]
    if expected_n is not None and block["n"] != expected_n:
        raise ExtractionError(f"q {expected_iq}: nmtx {block['n']} != {expected_n}")
    if expected_q is not None and block["q"] != tuple(expected_q):
        raise ExtractionError(f"q {expected_iq}: q {block['q']} != {tuple(expected_q)}")
    return block


def matrices(block):
    """Exact `E` (pre-inversion) and `X` (production inverse) plus `vcoul`.

    Completeness was enforced when the block closed (`_finish`); this only
    lays the validated entries out in order.
    """
    n = block["n"]
    if not block.get("closed"):
        raise ExtractionError(f"q {block['iq']}: block never closed validly")
    E = [[block["pre"][(i + 1, j + 1)] for j in range(n)] for i in range(n)]
    X = [[block["inv"][(i + 1, j + 1)] for j in range(n)] for i in range(n)]
    v = [block["vcoul"][i + 1] for i in range(n)]
    return E, X, v


def sha256(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def require_sha256(path, expected):
    """Pin a retained snapshot to its recorded digest.

    The expectation is a constant supplied by the caller; it is never read from
    the data under test, so a replaced snapshot fails instead of redefining
    what is correct.
    """
    got = sha256(path)
    if got != expected:
        raise ExtractionError(
            f"{pathlib.Path(path).name}: sha256 {got} != recorded {expected}")
    return got

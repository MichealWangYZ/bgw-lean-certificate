#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Machine-checked identity of the M3 chi block and the block M2 consumed.

    python3 bgw/m3_chi/link_m2.py

BGW-M3-R1 item 6. Previously this was prose in the A/B log: "byte-identical
up to the run-id string". Prose is not evidence. This compares the two
committed slices directly, normalising ONLY the documented run-id token, and
then compares the decoded matrices entry by entry as well, so a change that
happened to preserve the text length or ordering would still be caught.
"""

import importlib.util
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
M3_CHI = ROOT / "bgw" / "m3_chi" / "data" / "m3_chi_q2.txt"
M2_CHI = ROOT / "bgw" / "m2_screening" / "data" / "m2_dump_q2.txt"
M3_RUNID = "m3-20260919-q2-cut15"
M2_RUNID = "m2-20260917-q2-cut15"
IQ, N, Q = 2, 8, (0.0, 0.0, 0.5)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class LinkError(ValueError):
    """The two chi blocks are not the same data."""


def normalised(path, runid):
    """The slice with its run id replaced by a placeholder, nothing else."""
    text = path.read_text()
    if runid not in text:
        raise LinkError(f"{path.name} does not carry run id {runid!r}")
    return text.replace(runid, "<RUNID>")


def check():
    """Raise `LinkError` unless the two blocks are the same data."""
    a, b = normalised(M3_CHI, M3_RUNID), normalised(M2_CHI, M2_RUNID)
    if a != b:
        la, lb = a.splitlines(), b.splitlines()
        if len(la) != len(lb):
            raise LinkError(f"line counts differ: {len(la)} vs {len(lb)}")
        diff = [(i + 1, x, y) for i, (x, y) in enumerate(zip(la, lb)) if x != y]
        raise LinkError(
            f"{len(diff)} line(s) differ beyond the run id, first at "
            f"{diff[0][0]}: {diff[0][1]!r} vs {diff[0][2]!r}")

    # and independently, through the parser rather than the text
    x2 = _load("m2x", "bgw/m2_screening/extract.py")
    m3 = x2.matrices(x2.load_single(M3_CHI, M3_RUNID, IQ, expected_n=N, expected_q=Q))
    m2 = x2.matrices(x2.load_single(M2_CHI, M2_RUNID, IQ, expected_n=N, expected_q=Q))
    names = ("chi", "vcoul", "Ehat", "Xhat", "basis")
    for name, u, v in zip(names, m3, m2):
        if u != v:
            raise LinkError(f"decoded {name} differs between the two blocks")
    return {"lines": len(a.splitlines()), "matrices": list(names)}


def main():
    try:
        info = check()
    except LinkError as exc:
        print(f"LINK BROKEN: {exc}", file=sys.stderr)
        return 1
    print(f"OK: the M3 chi block and the block BGW-M2 consumed are the same "
          f"data ({info['lines']} lines; {', '.join(info['matrices'])} all "
          f"equal), differing only in the run-id token")
    return 0


if __name__ == "__main__":
    sys.exit(main())

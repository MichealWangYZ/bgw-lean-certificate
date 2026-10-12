#!/usr/bin/env python3
"""Discriminating mutations of GW/Endpoint/NearPole.lean (E1.4).

    python3 bgw/endpoint/mutate_lean.py [--log FILE]

The certified evaluator encloses -I w / (2 (x + w)) in place of the source's
near-pole formula. Each mutant misstates that closed form in a way a
transcription slip could; `ssxNear_eq` must fail for every one of them.
"""
import argparse
import hashlib
import importlib.util
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "GW/Endpoint/NearPole.lean"
_s = importlib.util.spec_from_file_location("m4mut", ROOT / "bgw/m4_gpp/mutate.py")
m4mut = importlib.util.module_from_spec(_s)
_s.loader.exec_module(m4mut)

CLOSED = "  -I * w / (2 * (x + w))"


def cases():
    t = SRC.read_text()
    return [("control", t, set()),
            ("pole-sign", m4mut.sub1(t, CLOSED, "  -I * w / (2 * (x - w))"), {"ssxNear_eq"}),
            ("factor-4", m4mut.sub1(t, CLOSED, "  -I * w / (4 * (x + w))"), {"ssxNear_eq"}),
            ("overall-sign", m4mut.sub1(t, CLOSED, "  I * w / (2 * (x + w))"), {"ssxNear_eq"})]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--log")
    a = ap.parse_args(argv)
    lines = ["NearPole.lean discriminating mutations",
             f"NearPole.lean sha256: {hashlib.sha256(SRC.read_bytes()).hexdigest()}", ""]
    ok = True
    for tag, body, expected in cases():
        rc, out = m4mut.run_module(body, "e1_nearpole_" + tag.replace("-", "_"))
        got = m4mut.failing_decls(out, body) if rc != 0 else set()
        verdict = "OK" if got == expected and (rc == 0) == (not expected) else "FAIL"
        ok &= verdict == "OK"
        lines.append(f"{tag:14s} rc={rc} failing={sorted(got)} expected={sorted(expected)} {verdict}")
    lines.append("ALL OK" if ok else "SOME MUTATION DID NOT DISCRIMINATE")
    print("\n".join(lines))
    if a.log:
        pathlib.Path(a.log).write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

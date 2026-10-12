#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- Reading and validating the exported records: parsing, arity, coverage.

File integrity only. Nothing here forms a weighted sum or interprets a number
physically; that is `analysis.py`. Keeping the two apart is deliberate -- the
T-003 checker went wrong by conflating file integrity with algebraic
consistency, and the test classes have been separated along this line since.
"""

from fractions import Fraction as F
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]
                       / "occupation_audit"))
import check_occupation as co  # noqa: E402  (imported unmodified)

from contract import EXPECTED_RECORDS  # noqa: E402,F401

INT_FIELDS = ("rec call_id n1true n1 iw igp ig branch band_in il iband ispin "
              "icalc".split())
REAL_FIELDS = (
    "occ vcoul ieps wtilde_re wtilde_im wtilde2 wxt omega2 delw delwr wdiffr "
    "limittwo limitone ssx_pre ssx_post sch den_generic den_nearpole "
    "den_merged e_lk e_n1kq efermi occ_broadening aqsn aqsm qk1 qk2 qk3"
).split()
FIELDS = INT_FIELDS + REAL_FIELDS
#: the 29 fields the T-003 checker validates, in its own order
OCC_FIELDS = co.FIELDS
#: The per-call GPP accumulator dump, written at Sigma/mtxel_cor.f90:1530-1532
#: where `asxt(iw) = asxt(iw) + asxtemp(iw)`. At that point `asxtemp(iw)` and
#: `achtemp(iw)` hold the totals over ALL n1, ig and igp for this mtxel_cor
#: call, so `asxtemp(iw) + achtemp(iw)` is exactly the full accumulator that
#: the per-record local quantity `K*L` sums into. This is the correct
#: reference; the subset sum over the 3702 near-pole occ != 1 records is NOT.
ACC_INT_FIELDS = "call_id band_in il ispin icalc iw nend".split()
ACC_REAL_FIELDS = "asxtemp achtemp qk1 qk2 qk3 subtotal_in_code".split()
ACC_FIELDS = ACC_INT_FIELDS + ACC_REAL_FIELDS
class WeightedError(ValueError):
    """A record file violates its parsing, coverage or consistency contract."""
def parse(text):
    rows = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        if len(parts) != len(FIELDS):
            raise WeightedError(
                f"line {lineno}: expected {len(FIELDS)} fields, got "
                f"{len(parts)} (a short line usually means Fortran format "
                f"reversion)")
        r = {}
        for i, (name, tok) in enumerate(zip(FIELDS, parts)):
            if i < len(INT_FIELDS):
                r[name] = int(tok)
            else:
                v = float(tok)
                if not math.isfinite(v):
                    raise WeightedError(
                        f"line {lineno}: field {name} is {tok}, not finite")
                r[name] = v
        r["_line"] = lineno
        rows.append(r)
    if not rows:
        raise WeightedError("no records found; refusing a vacuous pass")
    return rows
def parse_accumulators(text):
    """Parse the per-call accumulator dump, keyed like the record groups."""
    acc = {}
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        if len(parts) != len(ACC_FIELDS):
            raise WeightedError(
                f"accumulator line {lineno}: expected {len(ACC_FIELDS)} "
                f"fields, got {len(parts)}")
        vals = {}
        for i, (name, tok) in enumerate(zip(ACC_FIELDS, parts)):
            if i < len(ACC_INT_FIELDS):
                vals[name] = int(tok)
            else:
                v = float(tok)
                if not math.isfinite(v):
                    raise WeightedError(
                        f"accumulator line {lineno}: {name} is {tok}")
                vals[name] = v
        key = (vals["call_id"], vals["iw"])
        if key in acc:
            raise WeightedError(f"accumulator line {lineno}: duplicate key {key}")
        acc[key] = dict(
            asxtemp=vals["asxtemp"], achtemp=vals["achtemp"],
            subtotal=vals["subtotal_in_code"],
            ident=(vals["icalc"], vals["band_in"], vals["il"], vals["ispin"],
                   vals["qk1"], vals["qk2"], vals["qk3"]))
    if not acc:
        raise WeightedError("no accumulator rows found")
    return acc
def check_coverage(rows, expect, tally=None):
    """Coverage contract, tied to the run's own tally where one is supplied."""
    ids = [r["rec"] for r in rows]
    if len(set(ids)) != len(ids):
        dupes = sorted({i for i in ids if ids.count(i) > 1})[:5]
        raise WeightedError(f"duplicate record ids {dupes}")
    if len(rows) != expect:
        source = ("all qualifying events, per the run's tally" if tally
                  else "the requested --expect-records count; no tally was "
                       "read, so this is a synthetic contract")
        raise WeightedError(
            f"coverage contract: expected exactly {expect} records "
            f"({source}), got {len(rows)}")
    if sorted(ids) != list(range(1, expect + 1)):
        raise WeightedError(f"record ids must be exactly 1..{expect}")
    out = dict(records=len(rows), ids_complete=True,
               tied_to_tally=False, counted_qualifying_events=None)
    if tally is not None:
        counted = tally["branch2"][1]
        if len(rows) != counted:
            raise WeightedError(
                f"coverage contract: the run's tally records {counted} "
                f"near-pole occ != 1 evaluations but {len(rows)} records were "
                f"exported; the export must BE those events, not a subset or "
                f"a superset")
        out["tied_to_tally"] = True
        out["counted_qualifying_events"] = counted
    return out
def occ_view(r):
    """The 29-field view the T-003 checker validates, reused unmodified."""
    v = {k: r[k] for k in OCC_FIELDS}
    v["_line"] = r["_line"]
    return v

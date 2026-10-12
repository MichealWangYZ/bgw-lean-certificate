#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- The numeric core: exact-rational weighted sums, grouping, ratios.

Every quantity here is computed with `fractions.Fraction` from each record's
own binary64 fields, so the arithmetic introduces no error of its own. What
the resulting numbers do and do not mean is stated in `contract.py`, not here.
"""

from fractions import Fraction as F
import math  # noqa: F401

from records import WeightedError, occ_view  # noqa: F401
from contract import LOCAL_RECON_LIMIT  # noqa: F401

import check_occupation as co  # noqa: F401

def analyse(rows):
    groups = {}
    singular = []
    clamp_would_differ = 0
    totals = dict(n=0, signed=F(0), absolute=F(0), local=F(0))
    biggest = None

    for r in rows:
        if r["wtilde_im"] != 0.0:
            raise WeightedError(
                f"line {r['_line']}: nonzero imaginary pole component "
                f"{r['wtilde_im']}; outside the mapped real-mode scope and "
                f"not approximated")
        # reuse the established per-record algebraic validation
        checked = co.analyse(occ_view(r))

        occ = F(r["occ"])
        ieps = F(r["ieps"])
        wt = F(r["wtilde_re"])
        x = F(r["wxt"])
        omega2 = wt ** 2 * ieps
        den_merged = 2 * wt * (x + wt)
        den_gen = (x - wt) * (x + wt)
        if den_merged == 0 or den_gen == 0:
            singular.append(r["rec"])          # accounted for, never skipped
            continue

        # branch_mismatch, unchanged
        m = (1 - occ) * (omega2 / den_merged + omega2 / den_gen)
        # real flavor: MYCONJG is the identity
        K = F(r["aqsn"]) * F(r["aqsm"]) * F(r["vcoul"])
        L = -occ * F(r["ssx_post"]) + F(r["sch"]) / 2

        # would a program actually in the generic branch have clamped?
        ssx_generic = omega2 / den_gen
        if (abs(ssx_generic) > co.SIG_SEXCUT * abs(ieps)) and x < 0:
            clamp_would_differ += 1

        key = (r["call_id"], r["iw"])
        ident = (r["icalc"], r["band_in"], r["il"], r["iband"], r["ispin"],
                 r["qk1"], r["qk2"], r["qk3"])
        g = groups.setdefault(key, dict(n=0, signed=F(0), absolute=F(0),
                                        local=F(0), largest=F(0),
                                        largest_rec=None, ident=ident))
        if g["ident"] != ident:
            raise WeightedError(
                f"line {r['_line']}: call {r['call_id']} carries two different "
                f"outer identities {g['ident']} and {ident}")
        w = K * m
        g["n"] += 1
        g["signed"] += w
        g["absolute"] += abs(w)
        g["local"] += K * L
        if abs(w) > abs(g["largest"]):
            g["largest"], g["largest_rec"] = w, r["rec"]
        totals["n"] += 1
        totals["signed"] += w
        totals["absolute"] += abs(w)
        totals["local"] += K * L
        if biggest is None or abs(w) > abs(biggest[0]):
            biggest = (w, r["rec"])
        assert checked["mismatch_closed_equals_direct"]

    accounted = totals["n"] + len(singular)
    if accounted != len(rows):
        raise WeightedError(
            f"accounting error: {accounted} of {len(rows)} records accounted "
            f"for; records must never be silently skipped")
    return groups, singular, clamp_would_differ, totals, biggest
def ratio(num, den, floor=1e-300):
    """Signed-sum ratio, with an explicit flag when the reference is tiny."""
    d = abs(float(den))
    if d < floor:
        return None, "reference sum is zero or below representable scale"
    return float(abs(num) / abs(den)), None

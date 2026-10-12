#!/usr/bin/env python3
"""ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md. -- The weighted audit's CLAIM SURFACE: what the numbers are, and are not.

Split out of `weighted_mismatch.py` on an external reviewer's recommendation
that this project separate its scientific core from its documentation
contract. Everything here is a statement ABOUT the measurement rather than
part of computing it, and almost every constant exists because a specific
written claim was found to be false and had to be pinned down so it could not
drift again.

Its tests live in the WORKFLOW gate (`tests/test_weighted_contracts.py`),
because rewording any of it can fail them without any number changing. The one
exception is the STRUCTURE of `MISSING_FACTORS` -- which factor is missing for
which output type is physics, not prose, and is asserted in the scientific
gate.
"""

#: The coverage contract reads the qualifying-event count from the run's own
#: tally instead of hard-coding it, so the record COUNT and the tally COUNT
#: cannot silently drift apart. That is a cardinality guarantee only.
#: `EXPECTED_RECORDS` is only the fallback when no tally is supplied.
#:
#: What this check alone proves, precisely: **cardinality and record-id
#: sequentiality against a validated tally**. It does NOT by itself prove that
#: the exported records are the counted events. That conclusion rests on two
#: further links, which live outside this checker:
#:
#:   1. the tally increment and the record emission are TWO SITES in the same
#:      inner loop of `sigma_gpp_cpu`, both gated on the same derived predicate
#:      (`t4_b == 2 .and. t4_o == 2`). They are not one statement; the argument
#:      is that the same predicate selects both, not that one act does both;
#:   2. same-run provenance: the saved tally file and the saved record file were
#:      written by the SAME INSTRUMENTED EXECUTION of the SAME BINARY, recorded
#:      in `bgw/weighted_audit/PROVENANCE*.txt`. Two executions of the same
#:      binary would not support this step.
#:
#: Cardinality plus sequential ids plus those two links give completeness. The
#: checker supplies the first part only; `completeness_evidence()` below builds
#: the emitted field, so the JSON cannot be read as claiming more than is
#: checked -- and under `--no-tally` it makes no positive tally claim at all.
EXPECTED_RECORDS = 3702
#: Relative bound on |Python sum(K*L) - Fortran subtotal| per group. The two
#: sum the same terms in different orders, so they differ only by float
#: summation order. Observed maximum on the saved evidence: 8.694e-15.
#: This is a check on the SUBTOTAL, not on any individual term: errors in
#: individual weights or local values can cancel inside a subtotal.
LOCAL_RECON_LIMIT = dict(limit=1e-11, observed=8.694e-15, kind="relative")
#: `subtotal_in_code` is the Fortran's OWN running sum of
#: `aqsntemp*aqsmtemp*vcoul * (-occ*ssx + 0.5*sch)` over exactly the records
#: exported here, accumulated inside `sigma_gpp_cpu` in the code's own
#: arithmetic and zeroed per `mtxel_cor` call. It exists so the Python
#: GROUPED SUBTOTAL can be compared against the source rather than trusted:
#: `LOCAL_RECON_LIMIT` bounds the relative difference of the two subtotals.
#: This does NOT validate any individual weight or local value, and does not
#: bound their individual errors -- per-term errors can cancel inside a
#: subtotal. Only quantities the code already computes are summed; the
#: alternative branch expression is never evaluated in Fortran.
#:
#: `(in, il, ispin, icalc, iw, qk)` is NOT a unique accumulator key: the
#: offdiagonal band index `m` is implicit in the `aqsm` array rather than
#: passed, and even diagonal calls repeat that tuple. The instrumentation
#: therefore emits an explicit per-call counter, incremented once per
#: `mtxel_cor` entry where `iband = sig%diag(il)` is set, and `(call_id, iw)`
#: is verified unique. The outer identity is carried alongside for reporting
#: and cross-checked for consistency within a call.

#: The outer factors differ by output type, so they are listed per type rather
#: than as one universal list. Diagonal and offdiagonal elements take different
#: paths out of mtxel_cor.
MISSING_FACTORS = {
    "both output types": {
        "neq(irq)": "q-star degeneracy; diagonal at Sigma/sigma_main.f90:1586-1587, "
                    "offdiagonal at :1860-1861. Not available inside mtxel_cor.",
        "sum over q-points": "performed in sigma_main, outside this kernel",
        "ax (bare exchange)": "separate term, not part of sigma_gpp_cpu",
        "achcor (static remainder)": "separate term, not part of sigma_gpp_cpu",
    },
    "diagonal (icalc=1) only": {
        "ryd": "applied in Sigma/shiftenergy.f90:113 as part of "
               "fact = ryd/dble(ndeg(ii))",
        "1/ndeg": "degeneracy average, Sigma/shiftenergy.f90:113. The "
                  "degenerate subspaces are built at :69 by a loop over "
                  "`sig%ndiag` only, so this factor applies to DIAGONAL "
                  "elements and not to offdiagonal ones.",
    },
    "offdiagonal (icalc=2) only": {
        "ryd": "applied earlier, at Sigma/sigma_main.f90:1860-1861, together "
               "with neq; offdiagonal elements receive no 1/ndeg average",
    },
}
#: `ssx` and `sch` are dimensionless (`Omega2/(x^2-w^2)` and `delw*ieps` are
#: ratios of eV quantities), but the weight carries `vcoul(igp)`, which
#: BerkeleyGW holds in Rydberg. So `K*L`, and therefore `asxtemp`/`achtemp`,
#: are intermediate **Rydberg** values, not dimensionless. The conversion to
#: eV happens later, per output type, as listed above.
UNITS = ("intermediate Rydberg (vcoul carries the Ry scale; ssx and sch are "
         "dimensionless). NOT eV: the ryd conversion is applied later, and "
         "differently for diagonal and offdiagonal elements.")
#: weights are captured inputs: no relation internal to a record constrains
#: aqsn, aqsm or vcoul, so they are NOT independently validated here.
CAPTURED_NOT_VALIDATED = ("aqsn", "aqsm", "vcoul", "qk1", "qk2", "qk3")
def completeness_evidence(tally_used):
    """The evidence chain behind the whole-population claim.

    Under `--no-tally` there is no tally to compare against, so **no positive
    completeness claim is emitted at all**. An earlier revision emitted the
    tally-based text unconditionally, which was false in that mode.
    """
    if not tally_used:
        return {
            "checked here": None,
            "reason": "--no-tally was used: no tally was read, so no "
                      "cardinality comparison was performed and no "
                      "completeness claim of any kind is made here",
        }
    return {
        "checked here": "cardinality equals the validated tally's near-pole "
                        "occ != 1 count, and record ids are exactly 1..N with "
                        "no duplicates",
        "not checked here (1) shared predicate":
            "counting and emission happen at two sites in the same inner loop "
            "of sigma_gpp_cpu, both gated on the same derived predicate "
            "`t4_b == 2 .and. t4_o == 2`, so a counted event and an emitted "
            "record are the same event. Verifiable by reading "
            "bgw/weighted_audit/t004_instrument.patch.",
        "not checked here (2) same-run provenance":
            "the saved tally file and the saved record file were written by "
            "the same instrumented execution of the same binary. Verifiable "
            "from bgw/weighted_audit/PROVENANCE*.txt.",
        "conclusion": "cardinality alone does not establish completeness; it "
                      "does so only together with (1) and (2), which are "
                      "documentary rather than checked by this program",
    }

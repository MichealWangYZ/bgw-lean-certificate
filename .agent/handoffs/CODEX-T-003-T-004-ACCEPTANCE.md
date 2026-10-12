# Acceptance record: T-003 (with R1-R4) and T-004 (with R1-R5)

## STATUS: ACCEPTED WITH SCOPE AND KNOWN RESIDUALS

Validated by: Codex, at the user's direction
Date: 2026-09-12

The user explicitly ended the residual wording-review loop and authorized this
acceptance and a private GitHub push. This accepts the working demo and the
bounded evidence described below. It does not silently convert the known
residuals into accepted scientific claims.

## 1. Accepted scope

| Milestone | Deliverable | Repairs folded in |
| --- | --- | --- |
| T-003 | occupation-reachability audit of the GPP near-pole branch | R1-R4 |
| T-004 | weighted branch-mismatch measurement over all qualifying events | R1-R5 |

T-001 and T-002 were accepted previously and are unchanged. T-004-R6 was
authorized after review of R5 but was waived before implementation by the
user's sign-off; its task file is retained as the record of the known residuals.

## 2. Accepted result

| Quantity | Value | Accepted interpretation |
| --- | --- | --- |
| pre-outer-factor L1 diagnostic | **1.056%** | chosen dataset L1 norm over per-call accumulator groups; not a physical error estimate and not preferred over the signed cross-group ratio |
| maximum per-call accumulator-group sensitivity | **49.6%** | call 107, `iw=2`, diagonal, band 8, 134 events, accumulator `-0.02903`, after the stated small-reference exclusion |
| qualifying events | **3702** | cardinality and sequential IDs match the validated tally; the whole-population reading additionally relies on the same-derived-predicate and same-instrumented-execution evidence |
| units | intermediate **Rydberg** | `vcoul` supplies the Ry scale; outer factors differ by output type, and these are not final self-energy or eV results |
| witness | charge-inconsistent **stress witness** | `RHO` 8.00000 versus occupations 7.00000; not a material prediction |

Explicitly not accepted: a claim that BerkeleyGW is correct or incorrect, a
physical energy or observable error, a material-accuracy conclusion, or a
claim about the accuracy of the GW approximation.

## 3. Verification accepted

The pre-signature R5 gate was rerun independently by Codex and passed:

- **183 Python tests**;
- **60 named / 126 exhaustive theorem dependency audits**;
- 17 Lean runtime cases;
- only `propext`, `Classical.choice`, and `Quot.sound` in the allowed axiom set;
- no Lean, `Specification.md`, raw-fixture, instrumentation, or BerkeleyGW
  export changes in the T-003/T-004 repair series.

Codex reruns the same full gate after this owner record and `.agent/STATE.md`
are signed. The resulting commit is the accepted integration point.

## 4. Known residuals accepted as limitations

1. `REVIEW_PACKET.md` claim C3 should be read only at full occupation
   (`occ = 1`); its current sentence omits that qualifier.
2. A live `weighted_mismatch.py` comment and subtotal failure message still
   overdiagnose grouped-subtotal disagreement as individual weight/local-value
   reconstruction failure. The accepted numerical check establishes only
   grouped `sum(K*L)` agreement.
3. The general JSON field-reference regression does not detect a deleted field
   name surrounded by backticks.
4. The acceptance-status regression can recognize the fenced blank template as
   a fallback status if the real status heading is removed.
5. The review packet's worker index names nonexistent `T-003-R3.md` and
   `T-003-R4.md` handoffs. The actual handoff list is recorded below.
6. The witness remains manually shifted and charge-inconsistent; a physically
   self-consistent metallic or band-touching witness is not provided.

These are documentation, diagnostic-scope, and defensive-test limitations.
They do not change the measured values or the kernel-checked Lean theorems.

## 5. Correction history

The review packet records 33 corrected claims. Attribution is mixed: two were
self-reported, one was split, and thirty were found by independent supervisor
review. This count is not evidence of quality; reviewers should evaluate the
claim/evidence table directly.

## 6. Release decision

- **Private repository and private external review:** authorized.
- **Public publication:** not authorized. The repository's original work has
  no selected license. `THIRD_PARTY_NOTICES.md` separately records the terms
  applying to BerkeleyGW-derived material.

## 7. Evidence index

- Occupation audit: `bgw/occupation_audit/REPORT.md`,
  `check_occupation.py`, `PROVENANCE.txt`, `PROVENANCE-R1.txt` through
  `PROVENANCE-R4.txt`, and `fixtures/`.
- Weighted audit: `bgw/weighted_audit/REVIEW_PACKET.md`,
  `weighted_mismatch.py`, `PROVENANCE.txt`, `PROVENANCE-R1.txt` through
  `PROVENANCE-R5.txt`, and `fixtures/`.
- Worker handoffs that exist: `T-003.md`, `T-003-R1.md`, `T-003-R2.md`,
  `T-004.md`, `T-004-R1.md`, `T-004-R2.md`, `T-004-R3.md`, `T-004-R4.md`,
  and `T-004-R5.md`.
- Supervisor records: `CODEX-T-003-REVIEW.md`,
  `CODEX-T-003-R1-REVIEW.md`, and this acceptance record.
- Saved outputs: `artifacts/t003*/`, `artifacts/t004/`, and
  `artifacts/verification.json`.

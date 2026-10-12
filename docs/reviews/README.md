# External reviews

## REVIEW-28: adversarial core-claim review of PR 28

| | |
| --- | --- |
| Reviewer | Codex, the acceptance owner under `AGENTS.md`. The brief `.agent/tasks/REVIEW-28.md` names it; the review text does not name its author. The brief was written by the Claude supervisor of PRs #27/#28, which is the party under review. |
| Revision | `main` at `d783e188211bcaa477171b98cc96853badf334e6` (merge of PR #28) |
| Date | 2026-10-02 |
| Files | [`REVIEW-28-adversarial.md`](REVIEW-28-adversarial.md) (the review), [`counterexamples.py`](counterexamples.py) and its output [`counterexamples.json`](counterexamples.json), brief [`../../.agent/tasks/REVIEW-28.md`](../../.agent/tasks/REVIEW-28.md). All four are committed unchanged from what the reviewer delivered. |

Line numbers cited in the review refer to that revision. Later edits shift the cited
ranges: comment edits in `GW/Bridge/Compare.lean`, `EpsCompare.lean`, `EpsQ0Sigma.lean`,
`Bloch.lean` and `GPPModel.lean` (R28 integration; `GW/Bridge/Cor.lean` kept its line
count), further comment edits in the bridge files (R28-R2), and added lines in
`docs/BRIDGE.md`. `git show d783e18:<file>` gives the cited text.

**What was and was not replayed.** The review was a read-only source review through the
GitHub connector. It covered:
* the brief and the PR metadata;
* `docs/ENDPOINT.md` and `docs/BRIDGE.md`;
* the bridge definitions, theorem statements and proofs;
* the endpoint specification and the interval evaluator;
* `S3.o1_enclosure`;
* the axiom-audit implementation.

It was not an exhaustive audit of imported theorems, and it did **not** replay any of
the following:
* `lake build`;
* `GWKernelData`;
* the test suite;
* a BerkeleyGW executable;
* a pristine-Fortran-to-spec comparison.

The recorded full-gate PASS therefore remains author-supplied evidence. The reviewer
did run `counterexamples.py`. It checks rational witnesses reconstructed from the
reviewed definitions; it is not a Lean witness and not a rerun of the pipeline. R28-WORDS
re-ran it on 2026-10-02 (Python 3, standard library): it exits 0, and its output equals
the committed `counterexamples.json`.

**Decision.** Publish as a scoped formalization and numerical-certification artifact
after correcting the scientific descriptions. Do not claim "we formally verified the
core physics of BerkeleyGW". Claim 1 (the certified enclosure of the specified finite
calculation, and the 5.21 µeV production comparison) is supported within its declared
trust boundaries. The review re-derived the bound as at most 5.2077 µeV in exact
arithmetic. Claim 2 (spec = G0W0/HL-GPP of a general finite fermion system) is not
established as an end-to-end statement; what it does give are conditional identities.

| Finding | Severity | Summary | R28 task |
| --- | --- | --- | --- |
| F1 | BLOCKER for the broad claim | The composed bridge takes the screening blocks `bs` and the self-energy state `gl`, `st` independently; `EpsBlock.OK` has no common-system field. Its premises (`hC`, wings, `hX`, `ModeOK`) are not fulfilled on the run. | R28-F1 (Lean), `GW/Bridge/Common.lean`, `docs/reviews/R28-F1.md` (integrated; finding: Epsilon/Sigma k-grids disjoint, so no common system exists on the run; `Compat`'s grid-membership fields added in R28-R2); wording: R28-WORDS |
| F2 | MAJOR | `fsum_moment` is an identity once the oscillator strength is supplied; the HL prescription `OmT` is not independently identified with the system's response moment. Say "formal properties and consequences of the specified HL ansatz, conditional on its oscillator-strength prescription". | wording only: R28-WORDS (no Lean task) |
| F3 | MAJOR | `CompleteK κ` with the Gershgorin `κ` makes `κI - RᵀR` full rank, so no `N - m` physical omitted eigenvectors satisfy it (2-D witness, `ε = 2^-40`). It is an abstract completion, not a tolerance certificate. | R28-F3 (Lean), `GW/Bridge/CorPerturb*.lean`, `docs/reviews/R28-F3.md` (integrated; Löwdin + exact completion; the distance `d` in `RowDist` between the EPM eigenvectors and the stored rows is not evaluated); wording: R28-WORDS |
| F4 | MAJOR | `SigAall` is not "all bands, static remainder 0". The remainder is `(κ-1)I/4` per normalized channel, and even at `κ = 1` a non-shift-closed sphere leaves `-1/8` (witness). | R28-F4 (Lean), `GW/Bridge/CorResidual.lean`, `docs/reviews/R28-F4.md` (integrated; the static remainder `CORall` named and split exactly); its replacement wording is applied by R28-WORDS |

The review explicitly does not treat as new findings the disclosed band-count sign change,
the non-cubic RHO, the occupied `x = w̃` discrepancy or the GPP discontinuity.

The owner lifted the feature freeze on 2026-10-02 only for these corrections (recorded in
`.agent/tasks/R28-WORDS.md` and `.agent/STATE.md`). None of the R28 work is accepted
until the supervisor integrates it and reruns the gates.

## R28-R2: post-fix review of the R28 corrections

The R28 corrections (`r28/integration` at `b580e80`) were reviewed again by the same
standard, and the open items corrected on `r28-r2/work`: [`R28-R2.md`](R28-R2.md) (task
[`../../.agent/tasks/R28-R2.md`](../../.agent/tasks/R28-R2.md)). That review was done by
the Claude supervisor, not by an independent reviewer; it is not an acceptance.

## R28-R3: gate of PR #30 and repo-wide completion of its fixes

PR #30 (Codex's fixes for the four MINOR findings of its independent re-review of PR #29)
was gated here: fast and full PASS at f9cf59a. A sweep showed that the same two defect
classes, non-outward interval arithmetic and prose claiming more than the Lean statement,
also occurred elsewhere. They were fixed on `r28-r3/work` and verified in a second round:
[`R28-R3.md`](R28-R3.md) (task [`../../.agent/tasks/R28-R3.md`](../../.agent/tasks/R28-R3.md)).
This was done by the Claude supervisor, not by an independent reviewer; it is not an
acceptance.

## R28-R3 independent review — 2026-10-09

[`R28-R3-INDEPENDENT.md`](R28-R3-INDEPENDENT.md) records the review of main at
`94393de` (the same tree as `47a46c9`), the four remaining MINOR findings, and the
explicit acceptance decision: sign off after one bounded closing patch and its
validation, without requiring new physics work or another open-ended audit cycle.
It does not approve the unrepaired revision. The review was separate from the
Claude authoring/supervisor session; it was not a human review or a fresh full-gate
replay.

The finite repair brief is
[`.agent/tasks/R28-R3-CLOSEOUT.md`](../../.agent/tasks/R28-R3-CLOSEOUT.md), and the
execution limits are in the
[handoff](../../.agent/handoffs/R28-R3-INDEPENDENT.md).
The arithmetic reproducer, captured output and environment record are in
[`audits/r28_r3_review/`](../../audits/r28_r3_review/). This packet changes only
review documentation and reproducer evidence, not the implementation.

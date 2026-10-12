# R28-R3 independent review and bounded acceptance decision

Date: 2026-10-09. Reviewer: ChatGPT, separate from the Claude authoring/supervisor
session. This is AI-assisted technical review, not a human-maintainer signature or
an independently replayed Lean/BerkeleyGW gate.

## Decision

**Accept after one bounded closeout patch. The reviewed revision is not yet signed
off.** The review found four MINOR items and established no new BLOCKER or MAJOR
defect. Once these four items are repaired, the closing diff is checked, and the
required validation evidence covers that revision, the reviewer recommends
acceptance of R28-R3 and release under the existing bounded claims. Do not turn
closeout into another open-ended whole-repository review cycle.

The intended approved claim is kernel-checked evaluation of a specified finite
calculation on fixed literals exported from one pinned BerkeleyGW run, together
with conditional theory-to-specification identities. It is not formal verification
of the Fortran executable, binary decoding/export, source-to-spec correspondence,
or BerkeleyGW's core physics.

The larger limitations of the physics bridge are not minor. They limit what can
be claimed, but their disclosed existence does not block publication of the
narrower result. Generalising MF.TR, deriving the oscillator-strength prescription,
proving RowDist for the physical eigenvectors, and formalising decoding are NOT
additional closeout requirements.

## Pinned target and evidence

- Reviewed main: `94393dec0b74bd4927263dbe9513d2aa63ea3737`.
- R28-R3 delta: `f9cf59a4ca0678a7186d972121401a1127341632` to
  `47a46c994d0c11424754d14a48303cb4eff9c276` (PR #31).
- Main and that head have the same tracked tree:
  `7cddc5dbd2f54f93176ced7218f29709721ba20f`.
- [PR #31's final gate comment](https://github.com/MichealWangYZ/physics_lean_bgw/pull/31#issuecomment-6074498928)
  reports a full PASS at `47a46c9`: 34,553 theorems, standard axioms only;
  694 scientific and 15 workflow tests, two environment skips; 1,376
  certificate-data modules rebuilt. It explicitly says it is not independent
  review. These remain submitted execution evidence, not reviewer-run results.
- The reviewer inspected the diff and relevant source, theorem statements and
  documentation. This was not an exhaustive re-proof of imported dependencies.
- The committed arithmetic reproducer was rerun on 2026-10-09: 10,016 intervals
  passed both meV conversion directions; 5,016 rational cases passed directed
  conversion and nearest-neighbor checks. The radius counterexample reproduced.
  See `audits/r28_r3_review/rounding_spotchecks.py`, its log, and `evidence.json`.
- The script checks copied expressions with Fraction as oracle. It is NOT a
  checkout or execution of the full repository modules. Lean and Lake were not
  installed; neither the fast/full gate nor BerkeleyGW was rerun here. A direct
  clone attempt failed on DNS. No fresh agent or external reviewer was launched.

## Four remaining findings

### R3-I1 — MINOR: padded scalar radius conversion is not generally outward

Locations: `bgw/bridge_cor/cor.py`, `run_all()` per-band `radius_*_eV` and
`all_bands()` `radius_eV` reporting. Both use a scalar product of the radius,
`RYD_F`, and `(1 + 1e-12)`.

Let s be the smallest positive binary64 subnormal and the input radius be 2s.
The exact conversion with the specification's decimal constant is
`2s * 13.60569253 = 27.21138506s`. The padded scalar expression returns 27s,
which is inward. Relative padding cannot guarantee a representable step for
subnormal values.

This is a real numerical correctness bug, not a cosmetic observation. It is
MINOR for this package because the affected fields are auxiliary reporting:
`assemble()` consumes the underlying radii as intervals and converts with
interval-valued `RYD`, rather than consuming these reporting fields. No failure
of the pinned headline enclosure is established; the counterexample is not
claimed to occur in the pinned run. An inward rounding on the certified endpoint's
proof path would have a different severity, regardless of its tiny magnitude.

Repair both sites with the existing interval operation, for example
`float((I.exact(radius) * RYD).hi)`. Add a regression exercising the actual
implementation, including the 2s case and ordinary values, against an exact
rational oracle. No new interval library, tolerance tuning, or certificate change
is needed. Check any affected reporting consumers and preserve the provenance of
committed output data; do not claim a production regeneration that was not run.

### R3-I2 — MINOR: first B2 table row drops the static-match hypotheses

Location: `docs/BRIDGE.md`, first B2 chain row listing `gppC_static`,
`gppC_tail`, and `fsum_moment`.

The static-value assertion is unqualified although `gppC_static` takes nonzero
hypotheses for I and Omega squared. At I = 1, Omega squared = 0, Lean's totalized
`gppC 1 0 0` is 0, not -1. The source theorem and its header already state the
conditions. The table should separately qualify static match, tail asymptotics,
and `fsum_moment` (w nonzero; an algebraic identity, not a formalized spectral
integral). This fixes a false unrestricted prose statement without changing a
Lean theorem or its proof.

### R3-I3 — MINOR: departure-table row 6 conflates the two wing scalings

Location: `docs/BRIDGE.md`, departure-table row 6.

The blanket description `wings O(q)` is wrong in the row-scaled convention.
The unscaled row wing is O(1/|q|), while the column wing is O(|q|). The finite
scaled limits concern t times the row wing and the column wing divided by t.
`GW/Bridge/EpsQ0.lean` already gives the distinction. Correct the table, retaining
the caveat that a row wing need not diverge if its leading coefficient vanishes.
This is a substantive description error, not a new defect in the underlying
limit theorem.

### R3-I4 — MINOR: status and gate summaries are stale

The README and R28-R3 gate section still stop at `214b656` and 14 workflow tests,
while the final PR comment reports full coverage at `47a46c9` and 15 workflow
tests. ENDPOINT's E1.4 cell still says the spec files were deliberately not
edited, although the final headers and the October 7 authorization update show
that they were. Historical records must be distinguished from current status;
explicitly supersede obsolete assertions without erasing their history.

This is a documentation/evidence-summary inconsistency, not evidence that the
later reported gate failed. A gate for old code passed off as validation of
untested newer code would be materially more serious. Link the existing final
record and label it author/supervisor-reported, not independently reproduced.
A future closing patch needs its own applicable validation record.

## Changes that held up on source inspection

`hyps_unsat_of_selfpaired` derives False by choosing a block outside finite Z,
using hT and hfix there, and applying `MF.tr_fixed` to contradict the given
nonzero sphere vector. It does not need hnp or EP.WF. Its X/L interpretation
remains an explicit trusted plan-semantics step, not a theorem about coordinates.
It records an obstruction in the present MF.TR model; it does not repair the
common-system bridge or prove that the numerical endpoint is invalid.

The headline fixed-data numerical certificate does not derive its conclusion by
assuming that this problematic common-system bridge applies to the run. The two
claims must remain separate.

The inspected meV conversion, rational directed-rounding and q0 bound changes
held up; q0's 48-operation endpoint mean is explicitly labelled float-only and
not spec B. The GWOffPoles qualification and the corrected SigmaSpec/EpsSpec
headers preserve the relevant hypotheses and trust boundaries. The remaining
findings do not call for undoing those corrections.

## Closeout and sign-off

The executable changes in the closing patch, their consumers and the relevant
regressions must be checked. Keep normal repository gates; submitted execution
evidence is acceptable when accurately attributed. A fresh independent replay
of the entire Lean/BerkeleyGW toolchain is not an extra acceptance prerequisite.
After the four findings close and that evidence is verified, record approval:

> Approved within the documented scope. The identified R28-R3 findings are
> resolved. The reviewed source and submitted validation evidence support release
> of the fixed-data numerical certificates and conditional theory-to-specification
> results. This review does not constitute an independent replay of the complete
> Lean/BerkeleyGW toolchain or establish whole-program or end-to-end physical
> correctness.

That paragraph is the intended post-closeout sign-off, NOT approval of the current
unrepaired revision. Implementation brief: `.agent/tasks/R28-R3-CLOSEOUT.md`.
This commit records review evidence and the finite acceptance decision only;
no implementation repair, merge, visibility change or public release is made.

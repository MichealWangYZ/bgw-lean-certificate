# LL-C1-R1 — repair the reviewed checkpoint, then stop

Status: ready for owner activation, NOT already running or accepted.
Reviewed scientific base: `cf498531d1e0776daa69a22c891a853b2275cfff`.
Read: `AGENTS.md`, the existing LL-C1 task/handoff, and
[`docs/LL-C1-REVIEW.md`](../../docs/LL-C1-REVIEW.md).

## Purpose and authority

Repair the review's demonstrated delivery/checker defects, narrow the unsupported
model-correspondence claim, and reuse an existing mathlib definition. Preserve
all three ring theorem targets. Do not start C2 or solve general diagram theory.
The checkpoint hypothesis survived; the submitted package is not yet accepted.
This is an AI-authored internal assignment, not upstream feedback or human sign-off.

Work in an isolated local branch/worktree based on `review/ll-c1-r1-20260914`.
Check actual refs and working-tree state first; do not overwrite concurrent work.
Merging the planning/review PR or reading this file does not activate the task.
The owner's instruction to execute LL-C1-R1 is the activation event.

One **3-hour cumulative active-wall-time allowance**, including builds/tool waits
and resumed sessions. This is the controlling R1 budget, replacing the earlier
chat's two-hour suggestion; it is a spending cap, not an estimate of difficulty.
Reserve at most 15 additional minutes for saving evidence and writing the handoff
only, not more implementation. No session reset or automatic extension.

## Required repairs

### A. Portable checkout

Remove `.tools` from the tracked tree: it is an absolute symlink to the original
worker's installation. Preserve the real target and all user caches. Make the
ignore rule exclude `.tools` as either directory or symlink. Do not recursively
remove a symlink target, reset the user's worktree, or install tools elsewhere in
the user's system. No new installer or toolchain upgrade.

Confirm using `git ls-files` / the committed tree that no machine-local link is
being shipped. Exercise the documented bootstrap and full gate from a fresh,
independent checkout. An explicitly documented cache is acceptable; an inherited
absolute symlink, untracked project source or prebuilt project binary is not.
Record exactly which dependency caches were reused. If the environment prevents
this reproduction, return BLOCKED rather than reusing the old worktree's pass.

### B. Honest, reproducible evidence

The old handoff falsely said both `artifacts/ll-c1/lean_values.json` and
`artifacts/ll-c1/comparison.json` were committed. Correct that claim explicitly.
Keep original historical results distinguishable from the new run.

Use the real Lean executable to generate the candidate values. Provide a
reproducible comparison/mutation report generated from actual commands, not a
handwritten success JSON. Either deliberately commit the small output snapshots,
or document that they are generated and supply one deterministic command that
recreates them, returning the actual outputs with the handoff. A generated file
need not be committed, but its status must not be misreported. Do not add all
ignored artifacts, broaden unrelated BGW manifests, or build a new provenance
system. Verify the named paths in the final commit or returned packet.

### C. Small checker fixes and regressions

The review reproducer demonstrates old checker false passes on synthetic rows.
It is archival evidence pinned to cf498531, NOT a new production gate. Migrate
only the useful regressions into the existing scientific tests.

- Reject duplicate output names before dictionary construction; enforce the exact
  fixture inventory and row count, not just a deduplicated key set.
- Validate each row's integer `N`, `i`, `j` against its named fixture and bounds
  (`0 <= i,j < N`). Do not let booleans or floats masquerade as integer metadata.
- Retain exact rational value comparisons; show that the fixed checker rejects
  the wrong duplicate and invalid-index probes as well as an ordinary wrong value.
- Include `ll/ring_reference.py` in the existing `source_hashes()` coverage.
  Use the existing mechanism, not another hash registry.

These findings are about the parser/evidence boundary. Do not claim they prove
old Lean outputs were wrong or that a corrupt generated table survives every
step of the full fresh-generation gate.

### D. Mathematical scope, not a redesign

Keep `samePair`, the three ring data definitions, and the proved ring identities
unless a concrete bug requires a reviewed change. Explain that the compressed
site/edge representation has a demonstrated interpretation for these loopless
rings, not a proved general equivalence to all Lin–Lindsey half-edge diagrams.
Retain a small self-loop counterexample as scope evidence: its flag swap is lost
by the compressed representation (true half-edge count 2, coarse count 1).

The structure currently does not enforce well-formed quartic incidence either.
Do not assert that arbitrary `FeynDiagram` inputs are physically valid. Polynomial
identities for arbitrary matrices remain valid statements; interpreting reversal
of unordered stored endpoints as value-preserving uses symmetric G and v. Keep
those claims separate. No new general well-formedness hierarchy or universal
half-edge library is required to close R1.

Do not label the source-to-paper correspondence kernel-verified based on a
Python cross-check. A future general-ring task can prove the needed lift explicitly.

### E. Concrete reuse and community respect

Replace the independently reimplemented `consEquiv` with pinned mathlib v4.19.0's
`Fin.consEquiv`, or a thin justified local specialization of it. Preserve callers
when practical; no unrelated style sweep. Confirm the replacement compiles.

Spend at most 20 minutes, within the total budget, checking the cited Physlib
entry point/policy and recording why it is not a demonstrated drop-in dependency
here. A few lines in the handoff with exact refs suffice. Do not duplicate the
review as another landscape report. No migration, dependency upgrade, speculative
adapter or upstream contact is authorized.

## Verification and completion

Run the existing full `bash scripts/verify.sh`, with new modules/tests actually
included, from the independent checkout after the changes settle. Record commit,
versions, commands, exit codes, audit-module coverage and logs. Do not change
old theorem targets, discard failing scientific tests, add unproved assumptions,
use `sorry`/`admit`/`native_decide`, or certify a changed source using old outputs.
If existing manifests need ordinary digest refresh for changed covered files,
use the existing method and record it; do not enlarge their claim scope.

No theorem-count target, prose-enforcement tests, new scheduler, nested agents,
GPP investigation, license edits, public-visibility change, merge to main or
remote push is authorized. A local commit is allowed. Obtain separate permission
before any remote write; this task does not inherit the review author's PR-write
permission.

## Mandatory exits — earliest applicable wins

`CHECKPOINT_READY`: all A–E targets and the final independent-checkout gate pass,
with deliverable evidence. Stop for independent review; do not self-accept.

`ROUTE_REFUTED`: an exact admissible counterexample overturns a previously claimed
in-scope ring result. Name the exact assertion. The already-known out-of-family
loop limitation is not a new refutation of C1, and a tactic error is not one.

`BLOCKED`: a required repair needs a semantic change, missing access, unauthorized
scope, toolchain upgrade or an unproved mathematical assumption; or a central
obligation has **45 active minutes without new evidence**, or **two materially
different unsuccessful approaches**, whichever occurs first. Record the smallest
reproducer and decision required. Do not spend the budget looping on install
failures. Ordinary local debugging before these limits is allowed.

`BUDGET_STOP`: the 3-hour allowance expires, even if nearly finished. Save useful
partial work and open obligations. Forced session interruption uses this status
with that reason; no automatic restart. It does not establish impossibility.

## Return once

Write `.agent/handoffs/LL-C1-R1.md` with terminal status, base/result commit or patch,
actual elapsed work, A–E pass/open/fail pointers, exact command results, generated
versus committed artifact paths, remaining assumptions, and one recommendation
(accept for review / bounded repair / pivot / park). No new report hierarchy.

At a successful return, we review whether R1 closes the findings; we do not
relabel it as completion of arbitrary-order rings, all diagram theory, electronic
GW, or BerkeleyGW. A subsequent C2-prelude requires a new explicit task and budget.

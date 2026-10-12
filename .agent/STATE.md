# Project State

## Current decision — 2026-10-12: accepted within scope; scientific work frozen

The owner requested: “@GitHub seal off my lean verification of BGW please”.
The bounded R28-R3 closeout review is **ACCEPTED**. All four findings of
`docs/reviews/R28-R3-INDEPENDENT.md` are closed; no additional broad review or
physics-bridge research is required to accept this package.

The authoritative closeout is
[BGW-SEAL-2026-10-12](handoffs/BGW-SEAL-2026-10-12.md). It records the exact
revisions, four-item closure, submitted gates, reviewer-run arithmetic check,
remaining trust boundaries and generated-guide caveat. Private integration and
its actual merge outcome are tracked in
[PR #32](https://github.com/MichealWangYZ/physics_lean_bgw/pull/32).
This current decision supersedes earlier dated “ready for review”, “not accepted”
and “owed review/merge” entries for R28-R3 and its four-item closeout. It does not
retroactively accept unrelated parked work.

### What is accepted

Kernel-checked numerical evaluation of a specified finite calculation on fixed
literals exported from one pinned BerkeleyGW Si-EPM run, together with
conditional theory-to-specification identities under their actual hypotheses.
The project does **not** claim to have formally verified BerkeleyGW's core
physics, its Fortran executable, binary decoding/export or the complete
source-to-spec correspondence. The common-system bridge is not instantiated on
this benchmark. Physical and finite-basis limitations remain disclosed.

### Evidence ownership

- Reviewed implementation: `e8ef424e3009861b318f34ff46e0b44de1f78d5f`.
  The author reports fast/full gates PASS there: 34,553 audited theorems with
  standard axioms only, 699 scientific and 15 workflow tests, two environment
  skips. See `handoffs/R28-R3-CLOSEOUT.md`.
- Reviewed submitted head: `471e86adb9efb77712b35d3634281704ca4deed5`.
  Its only changes after the full-gated fix are state/handoff documentation;
  the author reports a fast gate for that commit.
- Reviewer-run check: 22,113 isolated copied-method arithmetic cases against
  exact Fractions, zero failures for the repaired radius conversion. This was
  not an import/run of the whole repository or a Lean/BerkeleyGW replay.
- The final seal changes documentation only. No repository fast/full gate was
  replayed for the seal documents; no new full-gate PASS is claimed. Acceptance
  uses the existing review's explicit allowance for accurately attributed
  submitted execution evidence and unchanged scientific/executable content.

`docs/review/index.html` is a pre-gate source-navigation snapshot generated
without its local `artifacts/axioms.log`. Its “0 audited”/“not found” badges are
not a failed audit and not the current gate status. The later author-run gate is
recorded in the handoff; the seal explains this without manufacturing a log.

### Stop condition and boundaries

There is **no active scientific assignment** after this closeout. Preserve the
feature freeze. Do not automatically launch another reviewer or worker, restart
a broad audit, generate a certificate, run new science or treat the backlog as
an instruction. No scheduler is installed by this closeout.

Disclosed future work remains parked: generalizing `MF.TR`, propagating
`wxS_close`, a physical-eigenvector `RowDist`/Davis–Kahan bound, compatible epsilon
and Sigma grids, deriving the HL oscillator-strength prescription, and stronger
decoder/export/source correspondence. These are not unresolved R28-R3 findings.
Existing parked branches and PRs are preserved. Reopening any work requires a
new owner instruction.

Visibility, licensing and public-release authorization are unchanged. This is a
private closeout, not publication, a human-maintainer signature or upstream
approval. Do not contact upstream communities under this request.

## Historical record — preserved, not rewritten as current status

The complete pre-seal append-only state log is preserved at the immutable
reviewed revision:

[STATE.md at 471e86adb9efb77712b35d3634281704ca4deed5](https://github.com/MichealWangYZ/physics_lean_bgw/blob/471e86adb9efb77712b35d3634281704ca4deed5/.agent/STATE.md)

Its blob is `ddf4e14b382bebb08a086c21841c3274601e4d74`. This current-state
consolidation does not erase that history or change its dated observations.
The individual task, review and handoff files remain in place. In particular,
`docs/reviews/R28-R3-INDEPENDENT.md` records the finite acceptance policy and
`handoffs/R28-R3-CLOSEOUT.md` preserves the worker's submitted evidence.

Reading order remains: this STATE, `docs/CODEMAP.md`, `docs/ENDPOINT.md` /
`docs/BRIDGE.md`, and the relevant dated task/review. For this completed work,
read the seal rather than automatically resuming a historical task.

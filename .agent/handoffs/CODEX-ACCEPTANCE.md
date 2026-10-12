# Codex Acceptance: T-001

Date: September 10, 2026 (America/Chicago; run logs use September 11 UTC).
Status: **accepted for Specification.md v0.1's restricted mathematical demo**.
No physical-model signoff or BerkeleyGW implementation verification is implied.

## Actual Handoff Cycle

Codex wrote the contract, installed pinned dependencies, and assigned the Lean
files to one Claude process. Claude implemented and compiled them, then wrote
`T-001.md`. Codex inspected the actual definitions and proofs, independently
exercised the public evaluator, integrated one JSON-serialization change, and
ran the full acceptance gate after Claude exited.

- Worker run: `.agent/runs/20260911T030321Z-1dd42a2a`.
- Worker exit: 0, status `needs_review`; lock subsequently verified idle.
- Optional Claude session ID: `a57054f7-91b9-4347-b6f0-38ed5f89ccca`.
- The durable resume path is files, not that session ID.
- Git was initialized, but no commit, push, or publication was made. The source
  checksum map in `artifacts/verification.json` identifies the verified files.

## Independent Verification

Command: `bash scripts/verify.sh`, exit 0.

| Check | Result | Evidence |
| --- | --- | --- |
| Pinned Lean project build | Passed | `artifacts/build.log` |
| Named theorem audit | 47 named theorems, allowed dependencies only | `artifacts/named-axioms.log` |
| Environment-based exhaustive audit | 106 theorems, including private/generated declarations | `artifacts/axioms.log` |
| Coverage of project modules | All mathematical modules and Main imported by the audit | `artifacts/axioms.log` |
| Independent Lean runtime cases | 17 passed | `artifacts/lean-runtime-tests.log` |
| Exact Python oracle vs Lean JSON | All fields agree | `artifacts/numerical-demo.log` |
| Python tests | 7 passed, including subcases and four mutants | `artifacts/tests.log` |
| Unknown CLI option | Rejected with nonzero exit | `artifacts/verification.json` |
| Source stability during checks | SHA-256 map unchanged during the gate | `artifacts/verification.json` |

The allowable proof assumptions are `propext`, `Classical.choice`, and
`Quot.sound`. No theorem depends on `sorryAx`, a native-computation trust axiom,
or an additional project axiom. Source review found no admitted proof or
user-authored unsafe shortcut.

The initial exhaustive audit also encountered nine **unsafe compiler runtime
placeholders** associated with generated code. They are reported separately,
while all theorem dependencies retain the strict allowlist. A separate negative
smoke test attempted to use an unsafe definition to prove `False`; this Lean
toolchain rejected it with `(kernel) invalid declaration, it uses unsafe
declaration`. This distinction does not certify the runtime or compiler.

## Review Corrections and Integration

The worker report is retained as submitted; these corrections take precedence:

1. `scripts/verify.sh` exists. The worker's claim that it was absent was stale.
   Codex ran it successfully after integration.
2. The oracle compares parsed JSON objects, so object key order is irrelevant.
   Codex replaced handwritten JSON concatenation with `Lean.Json.mkObj` and
   `.compress`; the resulting changed key order passes the comparison.
3. The extension-value identity is an algebraic identity proved using `ring`,
   not just definitional reduction. In Lean's totalized field it also holds at
   `w=0`, but physical continuity and evaluation still require the documented
   nonzero/positive domain. The theorem statement has not been weakened.
4. The worker's speculative next mathematical exercises are not active tasks.
   The next useful external connection is a versioned BerkeleyGW sample.

## Demonstrated Behavior

The synthetic fixture returns terms `2/3, -1, -1` and total `-11/6 eV`, including
the static `-1/2 eV`. The occupied pole probe at `A=4, x=w=1` returns the
continuous-extension value `1`; the raw split is undefined at that exact point.
Zero/negative pole energy and surviving branch poles are rejected, including
zero-coefficient cases.

The binary64 experiment, evaluated against exact rationals for the SAME float
input, shows a split value of zero near an offset of `1e-8`, despite an exact
value near one. The merged error at that point is about `2.5e-17 eV`. This is a
measured numerical example, not a proved floating-point error bound.

Figure: `artifacts/pole-cancellation.png` and `.pdf`. The PNG was visually
inspected. Source data: `artifacts/numerical-demo.json`. Regenerate with
`python3 scripts/reference.py --output-dir artifacts` then
`python3 scripts/plot_demo.py` (matplotlib required only for plotting).

## Remaining Boundary

The scalar rewrite and checked finite evaluator are proved for the documented
model. Unit conventions, occupancy interpretation, coefficient extraction,
BerkeleyGW code correspondence, physical accuracy, roundoff bounds, interval
certificates, and quasiparticle roots are outside this acceptance.

Read `docs/SOURCE_MAP.md` before broadening the claim. A next task should record
an immutable BerkeleyGW revision, one relevant code path, and a small genuine
export with its units, weights, precision, occupancy, cutoffs, and checksum.
No such source checkout or export was supplied; no substitute was invented.

## Wakeup State

No periodic automation is installed, no worker remains running, and no next task
is active. `.agent/WAKEUP.md` is shared restart guidance and a proposed supervisor
schedule prompt. Its presence is not evidence of a timer. A future supported
automation interface must create and read back an actual schedule before state
can claim that periodic wakeups are enabled.

For manual resumption, read `AGENTS.md`, `Specification.md`, `.agent/STATE.md`,
this acceptance, and `.agent/WAKEUP.md`; then inspect current source and rerun
the gate if code has changed. Do not redispatch accepted T-001 automatically.


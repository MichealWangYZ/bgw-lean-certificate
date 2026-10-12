# LL-C1 — test the finite diagram-to-algebra bridge, then STOP

Status: executable brief awaiting the owner's explicit start instruction.
Planning base: `7b5eea13143ce5b1aebd805d375529cb352550d2`.
Parent: [revisable roadmap](../../docs/LIN_LINDSEY_ROADMAP.md).
Implementer: Claude. Acceptance: owner / independent reviewer, not the implementer.

## 1. Mission and limits

Determine whether a small, genuine graph representation can yield the first three
ring contributions of Lin–Lindsey Part I, including their symmetry factors, with
kernel-checked connections to finite matrix expressions and a runnable exact
reference. This tests a route; it is not a commission to finish Part I, derive
electronic GW, or build a general field-theory library.

Read `AGENTS.md`, `Specification.md`, `.agent/STATE.md` and `.agent/WAKEUP.md` first.
Their proof-integrity and user-work protections remain in force. This task governs
only the new LL-C1 scope; it does not accept or reopen earlier milestones. Work in
an isolated local branch/worktree based on the planning PR. Do not overwrite a
user's dirty worktree, reset existing work, merge to main, push, publish, install
timers, or spawn nested agents. A safe new local worktree is allowed. A local commit
is allowed; remote writes need a separate owner instruction.

Budget on activation: **6 hours of cumulative active wall time**, including tool
waits/builds, across all resumes. This is a spending limit, not an estimated proof
time. Record start/resume/stop timestamps in the eventual handoff, not a new runtime
framework. Pauses while no process is working do not count; a new session does not
reset the allowance. Reserve up to 15 additional minutes solely to preserve evidence
and write the handoff after a stop. Never continue research in that reserve.

Preflight cap: 45 minutes to establish the baseline/toolchain and access the source.
Reuse scouting cap: 30 minutes within the total budget. Use the pinned Lean 4.19.0 /
mathlib v4.19.0; inspect compatible existing facilities rather than upgrading or
importing a large library speculatively. A missing candidate library is not itself
a blocker when a small local definition suffices.

## 2. Source and fixed semantic target

Read [Part I v1](https://arxiv.org/abs/1809.02900v1), especially PDF §2.1, §3.2 and
§4.7.1, printed pp. 42–43 / PDF pages 41–42 (zero based), including Fig. 4.11.
Inspect the figure; do not infer the graph from the matrix answer. Use the PDF's
numbering. No source text or image needs to be copied into this repository.

Use the paper's real, symmetric finite matrices `G` and `v`. The ring index is
`k=0,1,2`, meaning **0,1,2 bubbles and 1,2,3 interaction vertices**, respectively.
The zeroth ring is the Fock diagram, not the Hartree diagram. External half-edge
labels remain fixed by graph symmetries, even when numerical indices happen to
coincide. Internal labels, half-edge pairing, interaction structure and parallel
propagators must have explicit meanings.

With `B = G ⊙ G` and `⊙` the entrywise product, the contributions to be obtained are

```
k=0: - G ⊙ v
k=1: + (1/2) • (G ⊙ (v * B * v))
k=2: - (1/4) • (G ⊙ (v * B * v * B * v))
```

`*` denotes matrix multiplication; `•` is scalar multiplication. These are targets
to derive from graph data, NOT permitted definitions of graph evaluation. The
expected symmetry counts are 1, 2, 4. Keep the amplitude, symmetry count, reciprocal
weight and final contribution separate. If inspection reveals an inconsistent target
or convention, provide evidence and stop for review rather than quietly rewriting it.

For each of these three graphs the symbolic identity must hold for arbitrary finite
matrix dimension (at least every N≥1), not just N=1,2,3. Symmetry assumptions must be
explicit. Positivity/invertibility are not needed for these polynomial contractions;
do not invent a denominator or an analytic convergence obligation here. Give a
real-valued interpretation of the exact rational evaluator via a checked finite-sum /
product cast lemma, or an equivalent common algebraic definition with proved specializations.
No infinite-dimensional limit is part of this target.

## 3. Deliver the smallest real implementation

Choose the representation; do not treat the following as a required class hierarchy.
A finite half-edge/incidence model restricted to these graphs is enough. It may use
existing mathlib combinatorics, or a small local structure if that is simpler.

The needed content is:

- Concrete graph data for the three rings, including external labels and parallel
  lines. Derive contraction by summing internal index assignments and multiplying
  the local interaction/propagator factors read from those data.
- A faithful finite notion of symmetry preserving the relevant graph structure and
  fixing the external labels. Prove the automorphism counts 1,2,4. Enumerating a
  proved-complete set or proving a bijection to permitted swaps is acceptable.
  Defining `Aut(ring k)` as `Fin (2^k)` without a graph-preservation/completeness
  proof is not. Do not brute-force all permutations blindly when a structural
  argument or smaller complete candidate set is available.
- Kernel-checked graph-contribution identities for k=0,1,2 and arbitrary finite N,
  including a connection to exact executable evaluation. The two sides must be
  independently defined: a graph contraction and a matrix polynomial.
- Exact end-to-end comparisons of the Lean graph evaluator with a separately
  implemented Python rational matrix reference on fixed N=1,2,3 examples. Use
  standard-library `fractions.Fraction`; no floating tolerances. Include a symmetric
  non-diagonal case with `v*B != B*v`, and both equal and unequal external indices.
  At least one non-scalar G should be positive definite so the examples are not
  exclusively outside the Gibbs interpretation. A scalar fixture alone is inadequate.
- Adversarial checks that visibly detect at least: a wrong sign; a missing bubble
  symmetry factor; and a multiplication/index-contraction mistake. Show a fixed
  witness for each mutant. Also test that a permitted internal relabeling leaves
  the result unchanged. Do not require a symmetric output to change under reversal
  when the reversal is a true identity; choose a genuinely inequivalent mutation.

It is fine for the generic graph evaluator to be shared by the three graph instances.
It is not fine for the Python oracle to call the Lean candidate or read a candidate-
supplied expected-answer column. Do not manufacture agreement by adjusting weights,
targets, domains, or fixtures after seeing a failure; fix an implementation error or
report a target discrepancy explicitly.

Suggested placement: `GW/LL/` under a namespace explicitly documented as the
Lin–Lindsey Gibbs model, not electronic GW. This location allows a small additive
import through `GW.lean` to be seen by the existing GW-prefix axiom audit. Another
location is allowed only if its actual modules/declarations are included in the
existing exhaustive audit and verification command. Do not build a new audit system.
Use minimal additive wiring for any new executable or scientific test; preserve all
old tests and target statements. Inspect the existing gate before editing it.

## 4. Evidence and verification

Before implementation, record `git status`, the actual base commit and tool versions;
run `bash scripts/verify.sh` and save its exit code/log. If a baseline failure exists,
distinguish it from new failures. Do not spend this task repairing unrelated provenance
or prose gates. When a known pre-existing failure does not prevent the new work, the
scoped work may proceed, but CHECKPOINT_READY still requires a green final baseline;
otherwise return BLOCKED with the scoped results ready and the exact baseline issue.
If source access or the essential Lean toolchain remains unavailable at the preflight
cap, stop BLOCKED with commands/errors, not an assumed mathematical obstacle.

For the final run, use the existing full gate and the minimal explicit command(s)
that build/audit/test LL-C1. The existing gate must actually reach the new modules
and tests, not merely build the untouched GPP demo. Confirm the new module names
appear in the exhaustive audit. No `sorry`, `admit`, custom axioms, `native_decide`,
unsafe proof shortcuts, empty-domain success, or assumed target equalities. Ordinary
kernel-checked finite computation is allowed. Tactic experiments with unresolved
goals should be kept outside the accepted imported proof chain and reported as open,
not made green by weakening statements.

Capture actual commands, exit codes, theorem names/statements and stdout/stderr paths.
Keep the code and a compact machine-readable exact comparison/mutation result. Reuse
existing log/artifact conventions. Do not add tests whose only purpose is to police
this task's wording, expected prose, handoff length, or future plans.

## 5. Stop immediately at the first applicable condition

**CHECKPOINT_READY:** Every target in §§2–4 is present and passes. Write the handoff
and stop. Do not attempt k=3, general ring induction, formal series, skeleton theory,
self-consistency, or BerkeleyGW work even if these look like natural next steps.

**ROUTE_REFUTED:** A required mathematical assertion of the fixed target is contradicted
by an exact admissible example or a checked argument. Identify the assertion and the
scope refuted. A bug in your implementation is ordinary debugging, not a reason to
call the mathematical route false. Likewise, a Lean error or lack of a tactic is
not a counterexample, and refuting one representation does not refute the research goal.

**BLOCKED:** Stop when the next necessary step needs a semantic change, new physical
assumptions, missing access, a toolchain upgrade, unproved bridge, or scope beyond
C1. Also stop on an unresolved central obstruction after **90 active minutes without
new evidence**, or after **two materially different approaches fail to advance that
same obligation**, whichever occurs first. New helper names or tactic variations do
not count as different approaches or new evidence. Preserve the smallest reproducible
Lean goal / graph example / error and explain the two attempts. A cheap local bugfix
within the unchanged target is allowed before either limit is reached.

**BUDGET_STOP:** Stop when the cumulative 6-hour allowance ends, even if nearly done.
Also use this status with reason `session_interruption` if a forced session/context
limit prevents a proper run to another exit; preserve resumable evidence, but do not
arrange an automatic restart. A reviewer may explicitly grant a bounded continuation.

Specific infinity trigger: if the chosen route needs an infinite-dimensional measure,
cutoff-removal theorem, interchange of limits, or analytic summation of the perturbative
series to complete C1, stop BLOCKED and identify why the finite reformulation failed.
Do not insert such a result as an axiom or pretend a theorem for every finite N already
proves the N→∞ limit. You may explain a possible future analytic task, not implement it.

## 6. One return packet, and no self-acceptance

Write `.agent/handoffs/LL-C1.md` with the following compact content (use judgment on
length; code and logs carry the evidence):

```
Status: CHECKPOINT_READY | ROUTE_REFUTED | BLOCKED | BUDGET_STOP
Base / result commit or patch, tool versions, cumulative active time:
Exact claim proved; assumptions; unproved boundaries:
Acceptance items: pass / open / fail, with theorem or command pointers:
Independent comparisons and which mutants were detected:
Decisive obstruction and distinct attempts, if any:
What this teaches us about the roadmap:
One recommended decision: continue / bounded repair / pivot / park;
  with the smallest proposed next task and an allowance, not an automatic order.
```

Preserve partial useful proofs on failure. Keep an unchanged green base available;
do not present a broken development branch as accepted. Report any untracked artifact
paths needed for reproduction and provide the patch/commit and logs to the owner.
Finish by telling the owner the terminal status and that you stopped. Do not repeatedly
ask 'is this enough?', invent extra completion work, accept your own milestone, or
continue until the owner/independent reviewer authorizes a new bounded assignment.

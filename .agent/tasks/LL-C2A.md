# LL-C2A — arbitrary finite ring structure, then STOP

Status: executable brief awaiting the owner's explicit start instruction.
Base for this task: PR #4 result `111e97ce793118e35093cd5d1890171741c3f0db`.
Parent roadmap: `docs/LIN_LINDSEY_ROADMAP.md`.
Review entering this task: `docs/LL-C1-R1-REVIEW.md`.
Implementer: Claude. Acceptance: owner / independent reviewer, not implementer.

## 1. Mission

Test whether the C1 representation scales from three examples to the **entire finite
ring family**, without enumeration by order and without yet invoking formal power
series, skeleton theory, electronic GW, or BerkeleyGW.

The scientific checkpoint is successful only if the arbitrary-k graph is defined
structurally and Lean proves both:

1. its contraction is the expected matrix chain for every finite matrix dimension;
2. its symmetry factor is `2^k` because the only surviving automorphisms are the
   independent swaps of the two propagators in each bubble.

Also close the ring-specific correspondence gap exposed by C1 review: prove enough
about an explicit **ring-only half-edge model** to justify that the compressed
`Aut (ring k)` has the same automorphisms on this family. Do not build a universal
Feynman-diagram framework.

This is C2A only. Even after complete success, STOP. C2B (formal resummation) needs
its own authorization after review.

## 2. Mandatory opening cleanup — bounded, not a new milestone

Spend at most **45 active minutes** on these two carry-forward items before the new
mathematics. If either requires a semantic redesign, stop `BLOCKED` rather than
turning C2A into another infrastructure project.

### 2.1 One validator for tests and report generation

The repaired test path validates duplicate names, fixture inventory, `N/i/j`, and
exact values. `ll/make_comparison.py` still bypasses that validator and can falsely
succeed on a duplicate row, impossible metadata, or forged symmetry metadata.

Repair this with the smallest shared scientific validator:

- tests and report generation must call the same row/inventory validator;
- independently require symmetry metadata exactly `{ring0:1, ring1:2, ring2:4}`
  for the C1 artifact rather than copying candidate metadata into a field named
  `*_from_paper`;
- add CLI-level regressions for duplicate rows, invalid `N/i/j`, forged symmetry
  metadata, and one ordinary wrong numerical value;
- regenerate `comparison.json` as part of the existing verification path so the
  checked report cannot silently lag the checked values.

Do not import the test module into production, and do not add a schema framework,
new provenance system, or report hierarchy. One tiny shared module under `ll/` is
fine if needed.

### 2.2 Make the limitation witness and docstrings precise

The current `loopExample` is useful as an abstract incidence toy, but it is not by
itself a well-formed quartic Lin–Lindsey diagram. Either relabel it explicitly as an
abstract compressed-incidence counterexample, or replace it with the valid small
witness already identified by review:

- sites `I,J,a,b`;
- interactions `(I,J)` and `(a,b)`;
- propagators `(I,a)`, `(a,J)`, `(b,b)`;
- external flags fixed at `I,J`.

In a half-edge reading, swapping the two incidences of the `(b,b)` propagator is
invisible to site/edge identifiers. Keep the claim boundary explicit: Lean may prove
the compressed cardinality; any half-edge cardinality not formalized in Lean must be
labelled as external reasoning, not kernel-checked.

Also qualify the remaining `Aut` docstring so it does not identify the compressed
cardinality with Lin–Lindsey Definition 3.8 for arbitrary `FeynDiagram`; remove the
`example : True := trivial` comment-holder.

## 3. Fixed mathematical target

Primary source: Lin–Lindsey Part I, arXiv:1809.02900v1, PDF §3.2 and §4.7.1,
printed pp. 42–43 / Fig. 4.11. Use the PDF numbering and inspect the figure.
This is the paper's classical real Gibbs model, not electronic GW.

Define a structural family, say `ring (k : ℕ) : FeynDiagram`, whose `k=0,1,2`
specializations agree with the existing `ring0/1/2` **as graph data**, not merely
as numerical values. You may keep compatibility theorems instead of definitional
reduction when that is cleaner.

For each `k`:

- there are `k` bubbles, each containing two parallel propagators;
- there are `k+1` interaction edges forming the chain between fixed external sites;
- the external propagator remains fixed;
- the graph has no self-loop.

Choose the indexing representation that gives the cleanest proofs. Do not preserve
an awkward old encoding merely for textual similarity.

### 3.1 General contraction theorem

With `B = G ⊙ G`, prove for every finite dimension `N` a graph-data contraction
identity equivalent to

```text
contraction (ring k) G v i j
  = G i j * (v * (B * v)^k) i j
```

or an explicitly recursive matrix-chain definition proved equal to this expression.
The theorem should live over the weakest practical commutative algebraic assumptions;
do not add positivity, invertibility, symmetry, or convergence hypotheses that the
finite polynomial identity does not need.

The contribution theorem should then incorporate the uniform sign and the proved
symmetry factor, recovering the paper's finite-order ring contribution. Do not use
`2^k` as an input to define the automorphism group or graph value.

### 3.2 Structural automorphism theorem — no order-by-order enumeration

Prove the family-level statement that the fixed external labels and interaction
chain make the site relabeling and interaction-edge permutation rigid, and that the
only remaining freedom is independently exchanging the two parallel propagators in
each bubble.

Target an equivalence of the form

```text
Aut (ring k) ≃ (Fin k → Bool)
```

or a clearly equivalent finite type, and derive

```text
Fintype.card (Aut (ring k)) = 2^k.
```

A proof may use local finite decisions for base cases or helper facts, but **the
arbitrary-k theorem may not enumerate all automorphisms for each k**. The point of
this checkpoint is the structural argument that replaces the explosion observed at
ring2.

### 3.3 Ring-specific half-edge fidelity

Do not claim that the compressed representation is generally faithful. Define only
the minimum ring-specific half-edge data needed to state the correspondence. A good
result is either

```text
RingHalfEdgeAut k ≃ Aut (ring k)
```

or both sides independently equivalent to `(Fin k → Bool)` with a proved commuting
interpretation of the bubble swaps.

This model must retain the two incidences of each propagator explicitly enough that
its meaning does not simply restate the compressed `Aut`. It need not support
arbitrary graphs, tadpoles, Wick contractions, or skeleton decomposition.

The accepted result should therefore let us say:

> for the arbitrary finite ring family, the compressed automorphism computation is
> proved faithful to the ring's explicit half-edge symmetries;

not:

> this repository now formalizes Lin–Lindsey diagram automorphisms in general.

## 4. Executable / adversarial evidence

Keep executable evidence small because the general claims are Lean theorems.
Extend the exact rational reference to at least `k=3` on a nonscalar `N=2` fixture
and one additional small order convenient for runtime. Exact arithmetic only.

The check must distinguish at least:

- a missing bubble factor of two;
- a wrong interaction-chain attachment;
- a graph family that accidentally duplicates/drops one bubble;
- a purported extra automorphism that moves an external label or swaps whole
  bubbles contrary to interaction-path rigidity.

Do not turn finite examples into the proof of the arbitrary-k theorem. They are
regressions and semantic witnesses only.

Preserve the C1 exact fixtures and all repaired evidence checks.

## 5. Community / dependency boundary

Before introducing a generic helper, search the **pinned** mathlib source. Reuse
stable APIs where they fit. The existing Physlib Feynman-diagram area is work in
progress and on a different toolchain; do not upgrade, vendor, add it as a dependency,
or build an adapter merely for nominal alignment.

If C2A genuinely requires a new broadly reusable graph abstraction, STOP `BLOCKED`
and explain the missing interface. Do not create a parallel universal library under
this task.

No agent-initiated upstream issue, PR, reviewer message, or public outreach. This
work remains downstream. Human ownership is required for any eventual upstream
proposal.

## 6. Verification / proof integrity

Use the pinned Lean 4.19.0 / mathlib version. No `sorry`, `admit`, custom axioms,
`native_decide`, unsafe proof shortcuts, or target weakening.

Every new imported theorem must be covered by the existing exhaustive axiom audit;
only the repository's existing foundational allowlist is permitted. Run the complete
existing verification gate before returning `CHECKPOINT_READY`, and show that the
new arbitrary-k modules appear in its module audit.

The verification gate should regenerate the C1 comparison report after validating
its inputs. Keep scientific and workflow gates distinct under the existing scheme.
Do not add tests whose only purpose is to enforce prose or future plans.

Record actual commands, exit codes, theorem names/statements, and relevant logs.
A green gate is evidence about the checked development, not proof of the paper or
physical accuracy outside the stated model.

## 7. Budget and stop contract

Authorized allowance on activation: **6 cumulative active hours**, including
builds/tool waits. This is a spending limit, not a prediction. Reserve at most
15 additional minutes after a terminal condition only to preserve evidence and
write the handoff.

Preflight/baseline cap: 30 active minutes. Opening cleanup cap: 45 active minutes.

For one central mathematical obstruction, stop `BLOCKED` after either:

- **90 active minutes with no new evidence**, or
- **two materially different approaches** fail to advance the same obligation,

whichever happens first. Tactic variations or renamed helpers are not different
approaches.

The earliest applicable terminal status wins:

### `CHECKPOINT_READY`

All opening cleanup and §§3–6 pass. In particular:

- structural `ring k` exists and specializes correctly at k=0,1,2;
- general contraction theorem proved;
- `Aut (ring k)` structurally classified and card proved `2^k` without per-k
  exhaustive enumeration;
- ring-specific explicit half-edge symmetry is proved equivalent in the required
  sense;
- exact k≥3 executable regressions and mutants pass;
- full existing verification gate passes.

Write `.agent/handoffs/LL-C2A.md` and STOP. Do not start resummation.

### `ROUTE_REFUTED`

An exact admissible counterexample or checked contradiction shows a required
arbitrary-ring claim above is false under its stated construction/assumptions.
Identify the smallest broken assertion. A tactic failure, performance problem, or
failure of one representation is not route refutation.

### `BLOCKED`

The target cannot proceed without a semantic change, dependency/toolchain decision,
general diagram framework, unproved analytic/infinite-dimensional result, or other
unauthorized scope; or the no-progress rule above triggers. Preserve the smallest
reproducible Lean obligation/counterexample and the distinct attempts.

Specific infinity trigger: C2A is finite-dimensional and finite-order for each k.
If completing it requires convergence of the perturbative series, cutoff removal,
an infinite-dimensional measure, or interchange of limits, STOP `BLOCKED`; do not
smuggle that result in as an assumption.

### `BUDGET_STOP`

The six-hour allowance expires before another terminal condition. Preserve useful
partial theorems and exact open obligations. Do not infer impossibility.

## 8. Return packet

Write `.agent/handoffs/LL-C2A.md` containing, compactly:

```text
Status: CHECKPOINT_READY | ROUTE_REFUTED | BLOCKED | BUDGET_STOP
Base/result commit or patch; versions; cumulative active time
Opening cleanup: exact changes and regression evidence
Exact arbitrary-k theorem statements and assumptions
How site/path rigidity was proved; how bubble swaps were classified
Half-edge model and exact correspondence proved (and what remains outside scope)
Executable k>=3 comparisons/mutants
Full gate/audit commands and outcomes
Failed approaches or obstruction evidence, if any
What this teaches us about C2B/general theory
One recommended next decision: C2B / bounded repair / pivot / park
```

Preserve partial useful work on failure. Do not self-accept, merge `main`, push unless
separately authorized, install a scheduler, or automatically begin C2B.

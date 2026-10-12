# LL-C1 review — keep the route, repair the package, remain community-aligned — ARCHIVED (2026-10-01): LL review record; LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Reviewed scientific submission: `cf498531d1e0776daa69a22c891a853b2275cfff`.
Disposition: **bounded repair before acceptance; no C2 yet**.
This is a ChatGPT-authored private review and planning record, not a human
maintainer endorsement, upstream submission, or completed implementation repair.

Read the executable assignment in [LL-C1-R1](../.agent/tasks/LL-C1-R1.md).
The controlling repair allowance is **3 cumulative active hours**, with earlier
scope/blocker exits and a 45-minute no-new-evidence limit on one central obstacle.
This resolves the differing allowances in the earlier chat versions. The task
activates only when the owner directs Claude to execute it.

## 1. What the review establishes, and what it does not

The scientific question was whether genuine finite graph data could yield the
first three Lin–Lindsey ring contractions and multiplicities rather than have
the target formula inserted into the definition. That hypothesis survived this
review. The package nevertheless needs portability, evidence-checker and scope
corrections. A green build is neither a semantic audit nor proof that advertised
files reached the remote repository.

I inspected the submitted definitions, theorem statements/proofs, executable,
Python reference/tests, gate wiring, handoff and Git tree. The original review
also compared the diagram conventions with the paper. During preparation of this
PR I reran the consolidated Python probes against the four preserved source
files, first verifying their exact Git blob hashes. The measured results are
committed in [evidence.json](../audits/ll_c1_review/evidence.json), and the runnable
source is [review_checks.py](../audits/ll_c1_review/review_checks.py).

**No full Lean build, `verify.sh`, BerkeleyGW execution or kernel audit was rerun
in this review.** The worker's 240 tests / 248 exhaustive audits remain its
reported run, not mine. The 18 reference values in the review evidence were
recomputed in Python; they are not output from an executed Lean binary. A second
AI review also does not satisfy community requirements for human understanding.

The controls and probes produced:

| Probe | Measured result |
|---|---|
| Explicit half-edge vs compressed automorphisms, rings 0/1/2 | 1/1, 2/2, 4/4; projection is one-to-one |
| Two valid out-of-family self-loop examples | half-edge count 2, compressed count 1; projection has a two-element fiber |
| Correct synthetic output table | 13 tests pass |
| Ordinary wrong numerical value | one failure, correctly detected |
| Wrong duplicate before the correct row with the same name | all 13 tests pass incorrectly |
| N=1 row with i=j=999 but correct numerical values | all 13 tests pass incorrectly |
| No output file | a setup error; not a numerical pass |
| Actual bootstrap scripts with the submitted dangling absolute symlink | exit 1 before network access or Lean |

## 2. The load-bearing mathematics: credible rings, overbroad generic claims

The implementation usefully separates graph data, internal-index contraction,
a uniform interaction sign, automorphism cardinality, weighted contribution and
independently written matrix targets. The contraction theorems therefore are not
merely `rfl` over a definition that already contains the answer. The finite
reduction in `autEquivProps` is legitimate in form: its rigidity hypotheses are
discharged by the ring-specific proofs, not assumed as custom axioms.

### Why `samePair` does not double-count these rings

The definition permits either stored endpoint order:

```lean
(σ e.1 = f.1 ∧ σ e.2 = f.2) ∨
(σ e.1 = f.2 ∧ σ e.2 = f.1)
```

`Aut` counts triples of site/propagator/interaction permutations satisfying this
proposition; a choice of disjunct is not an additional counted Boolean. For an
edge joining distinct sites, the site map and edge map determine its two
half-edge images. The disjunction handles storage order, not an independent
edge-reversal degree of freedom.

The independent model retains four distinct half-edges per interaction, a
partition into two sides, propagator pairings and individually fixed external
flags. It enumerates vertex permutations and the eight permitted local
pair-preserving actions. It does NOT take `2^k` as input. For all three submitted
rings, its automorphisms project bijectively onto a separately implemented
transcription of `IsAut`, yielding 1, 2, 4. This addresses the circular-normalization
concern more directly than comparing two values that both assume the same divisor.

It remains a finite executable cross-check and source-level interpretation, not
a Lean proof of equivalence between two formal diagram models. The source-to-paper
connection must not be advertised as kernel-verified on this evidence alone.

### What the compressed representation loses

When a propagator is a self-loop, its two distinct half-edge incidences may
exchange while both the site map and whole-edge map remain the identity. A type
containing only those maps cannot distinguish that action.

One small concrete example, with fixed external labels at distinct sites I,J:

```text
interaction edges: (I,J), (a,b)
propagators:       (I,a), (a,J), (b,b)
```

A second example used in the earlier review:

```text
interaction edges: (I,a), (b,J), (c,d)
propagators:       (I,J), (a,b), (a,c), (c,b), (d,d)
```

Both have the appropriate quartic half-edge incidence when the external flags
are included, and remain connected after deletion of any one propagator. The
probe checks these properties. For both, half-edge automorphisms have cardinality
2 while the compressed type has cardinality 1. The missing element is the loop's
flag exchange. These are two witnesses to the same limitation, not conflicting
versions of one graph.

Thus the unqualified claim that `Aut D` is Definition 3.8's automorphism type for
every admitted `FeynDiagram D` is unsupported and in general false. The raw type
also does not enforce the physical quartic-incidence conditions.

**This does not refute `symmetry_ring0/1/2`.** Correct the broad docstrings and
restrict the claimed physical correspondence to the demonstrated ring use. Keep
a concrete loop boundary example. Do not require a universal half-edge library
or a general well-formedness hierarchy merely to close C1.

A related distinction: the submitted polynomial identities may genuinely hold
for arbitrary matrices. Interpreting unordered endpoint reversal as preserving
a physical amplitude uses the paper's symmetric G and v. Do not turn the former
algebraic generality into an unsupported relabeling-invariance claim.

## 3. Portable delivery is currently broken

Git tracks `.tools` as mode `120000`, blob
`6ddf4d1e032cebdea01246d8160cb827a38de7fc`, pointing to
`<repo>/.tools`. The bootstrap script runs `mkdir -p .tools`.
With that target absent on another host, the script fails immediately. I reproduced
this with the actual byte-verified bootstrap/env scripts in a temporary checkout.

A clean tree and successful local build can coexist with this defect. It does not
imply the worker fabricated its run; it means local success was generalized too far.

Remove the tracked link without deleting its real target; ignore `.tools` as either
a directory or a link. Reproduce from an independent checkout with dependencies
and any cache reuse explicitly identified. Do not invent a second installer or
upgrade the pinned toolchain. If access prevents the fresh run, report BLOCKED.

## 4. Evidence delivery and checker integrity need small repairs

### Claimed committed outputs are missing

The handoff says `artifacts/ll-c1/lean_values.json` and `comparison.json` were
committed. Neither is in cf498531's artifact tree. That subtree is
`c58f37baeb43fcd81c42440d81d04a3de39de3fa` and contains the older T-003–T-005 data.

The gate does regenerate Lean values before comparison, which is useful and
should be preserved. It does not generate the promised comparison JSON. Correct
the description, provide a reproducible comparison-report command, and return
actual outputs. Intentionally committed small snapshots or accurately documented
generated outputs are both acceptable. Do not handwrite missing success evidence
or build another provenance hierarchy.

### Two false passes, with controls

The helper makes a dictionary directly from output rows. An earlier wrong row
with the same name is silently overwritten by a later correct row. The probe
inserts `ring1 = 999999` in such a duplicate; all 13 current tests pass.

Metadata checks test global sets/properties instead of matching each named row
to its fixture. Setting the N=1 output row's i and j to 999 still passes because
the numerical comparison uses the reference fixture's own indices.

An ordinary wrong numerical value DOES fail. These findings concern the table
checker, not a claim that all checks are useless, that real Lean values were
wrong, or that arbitrary corruption survives the whole freshly generating gate.

Reject duplicates before conversion, enforce the exact inventory/count, and
validate each row's integer N/i/j and bounds against its named fixture. Add only
the demonstrated regressions to the existing scientific suite. Include
`ll/ring_reference.py` in the existing source-stability hash coverage; it is
currently omitted. No schema generator or parallel verification framework.

## 5. Community alignment is a design constraint, not a disclosure slogan

The goal is a narrow, useful downstream research asset that could eventually
contribute selected results to existing libraries. It is not to generate a
competing general library and ask maintainers to reconcile it later. Expert
attention, review time and future maintenance must be treated as real costs.

### Reuse an actual existing definition

The local `consEquiv` is deliberately recreated instead of searching mathlib.
But pinned mathlib v4.19.0 already supplies `Fin.consEquiv` in the imported tuple
API. Replace the duplicate, or use a thin specialization if callers need one.
This is a targeted correction, not a mandate for a broad style refactor.

Future tasks should search the pinned source before inventing general helpers.
Novel local objects are justified by missing semantics, not by ease of code
generation. Prefer explicit connections to established interfaces; do not merely
imitate their names with subtly different meanings.

### Downstream work is not inherently divergence

At the inspected Physlib commit, the apparent Feynman-diagram entry point is a
work-in-progress design note and asks contributors to contact its author before
working there. It does not provide the automorphism implementation we need. Its
Lean version is also newer than this project's. Study that direction, but do not
vendor, upgrade or implement a speculative adapter simply to claim alignment.
A focused standalone project depending on mathlib is a legitimate development
choice, not evidence of disrespect. External response times need not block our
private experiments.

### Human ownership before any upstream contribution

The current mathlib policy requires understanding and disclosure of AI-assisted
contributions, and prohibits LLM-written GitHub/Zulip comments. Physlib requires
human responsibility for the content, personal checking of bibliographic
references, human reviewer communication, and independent checking of implemented
feedback before re-review. Links are below; policies should be rechecked at the
time of any proposed submission. This private agent-authored PR is not a template
for prohibited upstream communication and does not satisfy those human duties.

No autonomous upstream issues, PRs, bulk batches, review requests, replies or
outreach. No model-generated messages for posting where the destination bans
that use. A named human owner must personally understand the definitions/proofs,
check the literature, discuss fit in their own words, and own future maintenance.
AI-to-AI review cannot substitute for that work. Respect maintainers' preferred
abstractions and scope. If they decline or lack capacity, stay downstream; do not
keep resubmitting or split the same demand into many small PRs. No upstream-PR,
line-count or theorem-count targets.

Credit the paper and reused library work, preserve source/license notices, and
do not present our agent workflow as a novel mathematical result or imply
community endorsement. Disclosure alone cannot make unwanted work valuable.

## 6. Decision now, and candidate decision later

Authorize only LL-C1-R1: portable checkout, honest outputs, bounded checker repairs,
accurate model scope and concrete reuse. Preserve the finite-ring mathematics.
Do not start arbitrary-order rings, formal-series resummation, skeleton theory,
electronic GW, BerkeleyGW work, dependency migrations or a universal diagram API.
Do not change licensing, visibility, existing acceptance records or main.

After R1, review the actual artifacts once and choose acceptance for this scope,
one further bounded repair, a pivot or a pause. Do not keep adding unrelated
acceptance work merely because more improvements are possible.

The next scientific candidate remains a structural theorem for all finite ring
orders: fixed external labels make the interaction chain rigid, leaving independent
bubble exchanges, with a proved correspondence to explicit half-edges and a
finite contraction identity. Enumeration is a useful C1 check, not the all-order
proof strategy. Even that task requires a new owner-approved brief; no automatic
C2, analytic infinite-dimensional limit or claimed completion of electronic GW.
The self-loop finding is a reason to choose that brief carefully, not to give up
on the research goal or immediately rewrite everything.

## Reproduction and evidence provenance

On this review-only branch, production files still have the original hashes:

```bash
python3 audits/ll_c1_review/review_checks.py --repo . --output /tmp/ll-c1-review
```

This regenerates `evidence.json` plus detailed logs. Committed JSON contains the
measured outcomes (whitespace compacted only), Python version, four source hashes
and reproducer hash. The PR-preparation run used exact archived source bytes
from the prior connector reads, not a complete cloned/buildable repository.

The script intentionally confirms old false passes and rejects changed source
hashes. It is archival review evidence, NOT an additional production gate. After
repair, use the migrated regressions to test the new behavior. A host where the
original absolute tool target exists skips the dangling-link experiment rather
than touching that installation; use a separate host for that demonstration.

## Primary sources and exact inspected references

- [Lin–Lindsey Part I v1](https://arxiv.org/abs/1809.02900v1): diagram definitions
  in §3.2, Definition 3.8 / Remark 3.9, truncated/external-label conventions,
  and §4.7.1 / Fig. 4.11 for ring amplitudes and symmetry factors.
- [Submitted Diagram.lean](https://github.com/MichealWangYZ/physics_lean_bgw/blob/cf498531d1e0776daa69a22c891a853b2275cfff/GW/LL/Diagram.lean)
  and [submitted checker](https://github.com/MichealWangYZ/physics_lean_bgw/blob/cf498531d1e0776daa69a22c891a853b2275cfff/tests/test_ll_c1.py).
- [Pinned mathlib v4.19.0 tuple API](https://github.com/leanprover-community/mathlib4/blob/v4.19.0/Mathlib/Data/Fin/Tuple/Basic.lean#L180-L189): `Fin.consEquiv`.
- [Inspected Physlib diagram entry point](https://github.com/leanprover-community/physlib/blob/7c26cf8b47abd92eeb43bd8a2dd1849b8e8bf835/Physlib/QFT/PerturbationTheory/FeynmanDiagrams/Basic.lean)
  and [toolchain](https://github.com/leanprover-community/physlib/blob/7c26cf8b47abd92eeb43bd8a2dd1849b8e8bf835/lean-toolchain).
- [Mathlib contribution / AI-use policy](https://leanprover-community.github.io/contribute/index.html)
  and [Physlib AI policy](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md),
  rechecked during PR preparation. Follow each destination's current policy,
  including its linked instructions, before future community interaction.

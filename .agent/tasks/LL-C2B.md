# LL-C2B — formal ring screening, then STOP

Base: PR #6 at `ce92b809897bbe3fa4268870eaef72e7741755b1`.
Read `AGENTS.md`, `.agent/WAKEUP.md`, `Specification.md`,
`docs/LL-C2A-REVIEW.md`, and `docs/LIN_LINDSEY_ROADMAP.md` first.
Disposition entering this task: C2A is sufficient for internal progression, with
explicit review limits and bounded carry-forward. This is not human sign-off.
Owner activation authorizes **C2B only**. Reading/merging a file does not run it.

## 1. One scientific question

Can the already-proved ring coefficients be identified with a screened interaction
in the existing formal-power-series library, with correct matrix order, sign,
symmetry weight, and degree convention?

Primary source: Lin–Lindsey Part I, arXiv:1809.02900v1, PDF section 4.7.1,
printed pp. 42–43 / Fig. 4.11. Read the formulas and figure. This is the classical
real Gibbs model's **ring contribution at fixed G**, not electronic GW, a proof
of Dyson self-consistency, the Hartree term's diagram derivation, or BerkeleyGW.

C2A supplies the graph family, arbitrary-order contraction, symmetry factor and
ring-specific half-edge correspondence. Reuse them. Do not re-prove graph theory.
No general diagram framework or new inverse/series library belongs in this task.

## 2. Opening cleanup: at most 45 active minutes

The C1 reader is fixed but `tests/test_ll_c2a.py` repeats the same bug: it builds a
name-keyed dictionary without rejecting duplicates, trusts candidate `orders`,
and ignores per-row N/i/j. The review's synthetic probes demonstrate false passes.

Extend/reuse the small existing `ll/evidence.py` validator. Tests and reports for
C1, C2A and the new coefficient evidence must use it. Supply expected fixture names,
orders and value keys from the test/spec, not from the candidate output. Preserve
C1's interface through a small wrapper if useful; no schema framework.

Reject duplicate rows/orders, missing/extra fixtures/orders, invalid or mismatched
N/i/j (including non-integer/bool metadata), and missing expected value columns.
Expected C2A orders are exactly 0..4. Preserve a normal incorrect-value control.
Add regressions for an incorrect duplicate preceding the correct row, impossible
indices, false dimension, and `orders=[0,3]` hiding an incorrect k4 column. Ensure
C2B's own reader cannot choose its comparison coverage from candidate output.
The historical reproducer is `audits/ll_c2a_review/checker_probe.py`; it refuses
changed historical sources, so migrate relevant assertions into current tests.

Keep scope statements precise: C2A proves fidelity for its ring family, not every
loopless graph. Use characteristic zero for physical symmetry weights; do not
interpret totalized division in characteristic two as a physical result. These
are claim corrections, not permission to weaken or rewrite existing theorems.

If cleanup needs a redesign or exceeds the cap, stop BLOCKED with a minimal
reproducer. Otherwise move on to the new mathematics rather than polishing reports.

## 3. Reuse checkpoint: there is already a noncommutative inverse API

Pinned mathlib v4.19.0, `Mathlib/RingTheory/PowerSeries/Inverse.lean`, has under
`[Ring R]`: `invOfUnit`, `mul_invOfUnit`, `invOfUnit_mul`, `coeff_invOfUnit` and
`isUnit_iff_constantCoeff`. The latter two-sided identities require a proof that
the series constant coefficient equals the chosen unit. For constant I, choose 1.

The PR's conclusion that matrix coefficients block the off-the-shelf route was
too strong: the field-only `PowerSeries.inv` is not the only interface. Inspect
and compile a small use of the pinned API before designing a replacement.

An explicit coefficient construction plus an equality proof to `invOfUnit` is
acceptable. A disconnected homemade inverse with no library connection is not.
Do not upgrade dependencies, assume matrices commute, diagonalize v and B together,
or require invertible v merely to simplify the proof. Search pinned APIs before
adding generic helper lemmas. Spend at most 30 active minutes on reuse scouting,
inside the overall allowance; do not turn it into an upstream survey.

## 4. Fixed definitions and target (names are illustrative)

Use a characteristic-zero field K (covering Q and R), arbitrary finite dimension N,
R = Matrix (Fin N) (Fin N) K, and formal variable z central in PowerSeries R.
G and v are fixed matrices. Set B = G entrywise-multiplied by G and
A_L = (1/2) • (v * B), A_R = (1/2) • (B * v). Matrix products need not commute.
Let C denote constant-series embedding and X denote the formal variable.

Define P_L = 1 + X * C(A_L), P_R = 1 + X * C(A_R).
Prove their constant coefficients are I. Use the library to define inverses
S_L and S_R, and the screened bubble-counting series

    W = S_L * C(v).

Independently define the graph series T by its kth coefficient:

    coeff k T i j = FeynDiagram.contribution (ring k) G v i j.

This is allowed because the contribution already comes from C2A graph data and
proved multiplicity. Do not define W from T or define T to be the target answer.

### 4.1 Inverses, matrix ordering, coefficients

Prove both inverse identities for S_L/P_L and S_R/P_R, using the constant-unit
hypotheses explicitly. Then prove

    P_L * W = C(v),
    W * P_R = C(v),
    W = C(v) * S_R.

Notice the RIGHT polynomial is P_R, not P_L. No commutativity assumption may hide
the distinction. These follow from P_L*C(v) = C(v)*P_R and the two inverses.

Derive for every k the equivalent recurrence/closed form

    W_0 = v,
    W_(k+1) = -A_L * W_k = -W_k * A_R,
    W_k = (-(1/2))^k • (v * (B * v)^k).

An alternative but proved-equal ordering such as ((-(1/2)) • (v*B))^k * v is fine.
The inverse and coefficient definitions must be connected by a checked theorem,
not merely compared at a few orders. Use standard coefficient extensionality.

### 4.2 Connect the series back to the graph theorem

Define the coefficientwise entrywise multiplication H_G by
(coeff k (H_G U)) i j = G i j * (coeff k U) i j.
Prove

    T = - H_G W

using C2A's `contribution_ring`, not a new unconnected formula with the same name.
H_G is an additive/linear operation, NOT a matrix-ring homomorphism in general.
Do not use a ring-hom API to transport it through matrix multiplication.

### 4.3 Degree convention is part of the contract

The series above counts bubbles: T has the Fock contribution at degree zero.
A ring k has k+1 interaction vertices. For coupling counting at fixed G define
T_coupling = X*T and W_coupling = X*W. Prove their constant coefficients vanish,
coeff (k+1) T_coupling = contribution (ring k), and coeff 1 W_coupling = v.
Explain explicitly that this is not the expansion of a self-consistent G(z).
A graph-derived Hartree contribution is outside scope; leave it separate rather
than claiming T alone is the complete GW self-energy ansatz.

### 4.4 Formal is not analytic

All equalities are in PowerSeries R. Do not evaluate an unrestricted series at
z=1, assert numerical convergence, or infer a cutoff-free/infinite-dimensional
physical result. A formal unit with constant I can specialize to a singular
finite matrix (for example I-zI at z=1). This is a boundary example, not a request
for a new analytic theorem. The full quartic perturbation series and the selected
geometric ring series are different series; divergence of one does not establish
divergence of the other.

## 5. Executable evidence: small, exact, and connected

Give a small Q-valued coefficient evaluator through at least degrees 0..4,
including a nonscalar N=2 fixture where v*B != B*v. Keep C1/C2A fixtures intact.
If the inverse is noncomputable, compute the finite coefficient recurrence and
prove that evaluator equals coeff k W/T; do not build an analytic matrix inverse.

Compare three specified views where applicable: existing graph contribution,
coefficients certified equal to W/T, and an independently written Python finite
recurrence/polynomial-product reference. Existing constants and graph fixtures may
be reused; an oracle must not read candidate expected-answer columns.

At finite truncation verify P_L*W and W*P_R coefficientwise through the tested
orders, allowing the first omitted coefficient to be nonzero. Mutants must detect
wrong sign, a missing factor 1/2, genuinely incorrect matrix ordering, and the
bubble-degree/coupling-degree off-by-one error, at fixed nonzero witnesses.
Wrong value and malformed coverage/inventory must fail separately.

A truncation regression is not the arbitrary-order proof. A compiler-produced
value is not automatically linked to a theorem because a comment says it is:
name the checked correspondence between the executable definition and coefficients.

## 6. Integration and reviewable result

Use existing `GW.LL` modules, gate and exhaustive axiom audit. Add the minimum
imports/executable/test wiring. Every new theorem module must appear in the audit;
no sorry/admit/custom axioms/native_decide/unsafe proof shortcuts. Preserve old
targets and pinned Lean/mathlib. Only the existing foundational allowlist is allowed.

Run the full gate before CHECKPOINT_READY. Record actual commands, exit codes,
module/theorem names, active-time accounting and source commit. State exactly
which evidence is committed versus generated; retain a reproducible small result
and logs. Before returning, inspect the actual Git tree, not just clean status.
No machine-specific symlink, inherited project binary, or invisible untracked source
may be required. Dependency caches may be reused if disclosed.

Do not expand GPP scope, license/visibility work, old acceptance records, general
graph support, or maintainers' workload. No agent-initiated upstream contact,
bulk patches, community PRs or reviewer replies. Human technical ownership and
current target-community policies remain requirements for any eventual outreach.

## 7. Budget, exits, and next decision

Allowance: 6 cumulative active hours, including builds/tool waits, across resumes.
Preflight cap 30 minutes; carry-forward cleanup cap 45 minutes. These are spending
limits, not predicted completion times. Reserve up to 15 further minutes only to
save evidence and write the handoff after a terminal condition.

Stop on the FIRST applicable outcome:

- CHECKPOINT_READY: cleanup, definitions, all arbitrary-order equalities and degree
  relations, library connection, executable checks and full gate pass. STOP before C3/C4.
- ROUTE_REFUTED: exact admissible counterexample or checked contradiction to a
  required mathematical assertion. A local code/tactic failure is not a refutation.
- BLOCKED: next necessary work requires changed semantics, a dependency decision,
  generalized diagram/inverse framework, an unproved analytic limit, or other
  unauthorized scope. Also stop after 90 active minutes without new evidence on
  one central obstruction, or two materially distinct unsuccessful approaches to
  that obligation. Tactic variations/renamed helpers are not separate approaches.
- BUDGET_STOP: six hours expire or an unavoidable session interruption prevents
  completing the run. Preserve partial useful proofs; no automatic restart.

Write `.agent/handoffs/LL-C2B.md`: status; base/result and time; exact claims and
assumptions; cleanup regressions; inverse API used; coefficient and degree bridges;
executed checks; open obligations/failed attempts; one recommended next decision.
Completion is not self-acceptance. Do not merge, push without separate permission,
change visibility, install timers, or continue automatically after any exit.

After review we choose general skeleton work, a narrow electronic bridge, one
bounded repair, a pivot, or parking. None of those is pre-authorized now.

# LL-C3 — finite Wick pairings to Hartree/Fock, then STOP

Base: C2B result `52a2472` on `ll-c2b/formal-screening`.
Read `AGENTS.md`, `.agent/WAKEUP.md`, `docs/LIN_LINDSEY_ROADMAP.md`,
`docs/LL-C2B-REVIEW.md` and `.agent/handoffs/LL-C2B.md` first.

## 0. Provenance of this build book — read this first

**This brief was written by the implementer, not dispatched by a supervisor.**
Every previous checkpoint (C1, C2A, C2B) had a build book written by the
reviewer before the work started, which is a real check: the person who sets
the acceptance bar was not the person trying to clear it. That check is absent
here. The owner authorized "C3" directly after the C2B review, and no
`.agent/tasks/LL-C3.md` existed.

Two consequences, and they are not rhetorical:

1. The targets in section 3 are taken verbatim from `docs/LL-C2B-REVIEW.md`
   section 6 ("connect finite Wick pairings and normalized first-order moments
   to Hartree/Fock, including cancellation of disconnected terms and the 1/8
   interaction normalization"). They are not chosen for convenience. Nothing in
   section 3 may be weakened by the implementer during execution; if a target
   proves unreachable the exit is `BLOCKED`, not a smaller target.
2. A reviewer should treat a self-authored brief as weaker evidence of scope
   discipline than a dispatched one, and should check section 3 against the
   review text rather than against the delivered result.

The roadmap's C3 row is broader than this ("general bare→bold / skeleton
theory ... eventually Theorem 4.12"). This task is the **first bounded subtask**
of that row, the one the C2B review actually recommended. It is not the whole
C3 row and must not be reported as such.

## 1. One scientific question

Does the ring series that C1/C2A/C2B built sit inside a correctly normalized
perturbation expansion of the model — specifically, is the ring family's
lowest-order term recoverable from finite Wick pairings of the Gibbs model,
with disconnected contributions cancelling against the partition function and
with the interaction's own normalization carried correctly?

This is an **upstream** semantic link. C1–C2B all start from graph data that
was asserted to be the right graph data. Nothing so far derives that data from
the model's moments. This task tests one order of that derivation.

Primary source: Lin–Lindsey Part I, arXiv:1809.02900v1, the classical real
Gibbs model of PDF sections 3–4. Not electronic GW, not BerkeleyGW.

## 2. The declared input, stated before any result

Pinned mathlib v4.19.0 has **no** Isserlis/Wick theorem and **no** multivariate
Gaussian with a covariance matrix (`Mathlib/Probability/Distributions/Gaussian.lean`
is one-dimensional real). Verified by source inspection before designing.

Therefore this task **defines** the moment functional as a sum over pairings and
**does not prove** that it equals a Gaussian integral. That equivalence —
Wick's / Isserlis' theorem — is an explicitly declared input, not a result.

This must be stated in the module docstring, in the handoff, and in any summary.
A reader must not be able to come away believing this repository has formalized
Gaussian perturbation theory. Proving Wick's theorem from a measure-theoretic
Gaussian is out of scope: it needs an analytic development that does not exist
in the pinned dependency, and inventing one here is precisely the "parallel
general framework" the reviews prohibit.

Similarly, the interaction normalization `U = (1/8) Σ_{i,j} v_ij x_i² x_j²` is
taken from the C2B review's description of the paper. **The implementer has not
personally verified this against the PDF and must not claim to have.** Make the
convention an explicit named definition so a human can check it against printed
p. 42 in one step, and record the unverified status in the handoff.

## 3. Fixed targets — not weakenable

Let `G` be a symmetric covariance matrix over a characteristic-zero field,
`v` the interaction matrix, `N` finite, all indices `Fin N`.

### 3.1 Pairings

Define the pairing-sum moment of a finite list of indices, and a computable
recursive form, and **prove them equal**. The pairing side must be a genuine
enumeration of perfect matchings (equivalently fixed-point-free involutions),
not a restatement of the recursion. Establish `moment [a, b] = G a b`.

### 3.2 Normalized first order and disconnected cancellation

Define the first-order correction with the partition-function normalization
included, i.e. the bracket `⟨x_a x_b U⟩ - ⟨x_a x_b⟩⟨U⟩`, and prove that the
matchings in which `a` pairs directly with `b` cancel **exactly**. The
cancellation must be proved, not observed on examples.

### 3.3 Hartree and Fock

Prove the surviving connected part equals, in closed matrix form and for
symmetric `v`,

```text
δ⟨x_a x_b⟩ = -( (1/2) (G · diag(v d) · G)_ab  +  (G · (v ⊙ G) · G)_ab ),  d_k = G k k
```

with the two summands separately identified as the Hartree and Fock terms. Do
not assume `v` symmetric where it is not needed; state where it is used.

### 3.4 The link back to the ring family

Prove that the Fock term is exactly C2A's order-zero ring contribution dressed
by external propagators:

```text
FockTerm G v = G * T₀ * G,   T₀ = contribution (ring 0) G v  (= -(v ⊙ G))
```

using the existing `GW.LL` theorem, not a re-derived formula of the same shape.
Also state explicitly that the Hartree term is **absent** from the ring family —
this is the concrete content of C2B's "a graph-derived Hartree contribution is
outside scope".

## 4. Executable evidence

Exact rationals only. An independent Python reference that brute-force
enumerates perfect matchings and computes the normalized correction directly
from the definition, never reading the Lean output. Nonscalar `N ≥ 2`.

> **Correction (C3/C4 review).** This section originally also required "a
> fixture with `v ⊙ G` nonsymmetric". That is **impossible** under section 3's
> own hypotheses: if `G` and `v` are both symmetric then `v ⊙ G` is symmetric
> entrywise. The requirement is withdrawn as ill-posed rather than reported as
> satisfied. The useful non-degeneracy condition, which the fixtures do meet,
> is a non-uniform loop vector `(v d)_i`, so the Hartree term distinguishes
> sites.

Route the table through `ll/evidence.py`
with specification-owned fixtures, orders and value keys — do not write a new
reader. Mutants that must be detected: dropped normalization (disconnected term
left in), `1/8` replaced by `1/4` or `1/2`, Hartree/Fock swapped, a wrong
matching count, and an ordinary wrong value.

## 5. Out of scope — stop rather than do these

Measure theory, Gaussian integrals, convergence, higher orders, general bare-to-
bold or skeleton theory, Theorem 4.12, self-consistency, electronic GW,
BerkeleyGW, any new general diagram framework, dependency or toolchain change,
license/visibility change, upstream contact, `main` merge.

## 6. Verification

Pinned Lean 4.19.0 / mathlib. No `sorry`, `admit`, custom axiom, `native_decide`
or unsafe shortcut. Every new module in the exhaustive audit. Full existing gate
before `CHECKPOINT_READY`. Record actual commands and exit codes. Preserve all
C1/C2A/C2B targets and fixtures unchanged.

## 7. Budget and stop contract

Allowance **6 cumulative active hours**, matching prior checkpoints; preflight
cap 30 min. Reserve at most 15 further minutes after a terminal condition to
save evidence and write the handoff.

Earliest applicable status wins:

- `CHECKPOINT_READY` — all of section 3 proved, section 4 passes, full gate green.
- `ROUTE_REFUTED` — an exact counterexample contradicts a section 3 claim.
- `BLOCKED` — a target needs measure theory, a new framework, a dependency
  decision, or other section 5 scope; or 90 active minutes pass with no new
  evidence on one obstruction; or two materially different approaches to the
  same obligation fail.
- `BUDGET_STOP` — the allowance expires.

Write `.agent/handoffs/LL-C3.md` and STOP. Do not start the rest of the C3 row
or C4. Do not self-accept, merge, or push without separate authorization.

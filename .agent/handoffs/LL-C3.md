# LL-C3 handoff — finite Wick pairings to Hartree/Fock

```
Status: CHECKPOINT_READY
```

Not self-acceptance. I stopped here: the rest of the C3 roadmap row and all of
C4 were **not** started, nothing was pushed, `main` was not merged, no
dependency or toolchain changed, and no upstream community was contacted.

## Read these three caveats before the result

**1. This build book was written by me, the implementer.** Every previous
checkpoint had its targets set by the reviewer before work began; that check is
absent here. The owner authorized "C3" directly after the C2B review and no
`.agent/tasks/LL-C3.md` existed. I took the targets verbatim from
`docs/LL-C2B-REVIEW.md` section 6 and wrote them down in
`.agent/tasks/LL-C3.md` section 3 *before* implementing, but a reviewer should
treat a self-authored brief as weaker evidence of scope discipline and check
section 3 against the review text rather than against what I delivered.

**2. Wick's theorem is an INPUT here, not a result.** Pinned mathlib v4.19.0
has no Isserlis/Wick theorem and no multivariate Gaussian with a covariance
matrix (`Mathlib/Probability/Distributions/Gaussian.lean` is one-dimensional
real) — checked by source inspection before the design was chosen. So
`wickMoment` *defines* the moment functional as a sum over perfect matchings.
Everything downstream of that definition is proved; the definition is where the
physics enters on trust. **Nothing here formalizes Gaussian perturbation
theory**, and the result must not be summarized as if it did.

**3. The `1/8` interaction normalization.** It is recorded as the named
definition `interactionWeight` and echoed in the emitted artifact.

> **Correction (C3/C4 review).** The value `1/8` is **correct**. Its source is
> Part I section 2.1, equation (2.4), **printed page 5** — not p. 42, which is
> the ring section and which this handoff originally cited. The verification was
> done by the reviewer; I still have not read the PDF and do not claim to have.
> The avoidable part of this gap is now closed: the citation is right, and the
> only residual is that the check was someone else's.

## Base, result, versions, elapsed

* Base: C2B result `52a2472` on `ll-c2b/formal-screening` (PR #8 + review R1).
* Work branch `ll-c3/wick-hartree-fock`, isolated worktree. Committed locally,
  **not pushed**; the branch has no upstream.
* Lean 4.19.0 / mathlib `v4.19.0` (`c44e0c8`), Python 3.12.3. Unchanged.
* **Cumulative active wall time: ~25 min** (`03:35:51Z` → `04:00Z`, measured
  with `date -u` at the start and at checkpoints) against a 6-hour allowance.
  Preflight ~9 min (cap 30). No obstruction triggered the 90-minute or
  two-approach rules. Two full gate runs and the toolchain bootstrap are inside
  that figure; the mathlib build was served from cache.
* Toolchain bootstrapped fresh in this worktree (`scripts/bootstrap.sh`, exit 0).
  One disclosed reused dependency cache: `~/.cache/mathlib`.

## What is proved — `GW/LL/Wick.lean`

### The enumeration is checked against an independent characterization (3.1)

`pairings` is defined by a fuel-bounded recursion, which on its own is no
evidence that it enumerates perfect matchings. Four decided facts at the arity
this file uses, against the independent notion "fixed-point-free involution":

* `pairings_length_six` — exactly 15 matchings of 6 positions, as `(6-1)!! = 15`;
* `pairings_six_fpf_involutive` — every enumerated matching induces a
  fixed-point-free involution;
* `pairings_six_nodup` — none is enumerated twice;
* `pairings_six_complete` — **every** fixed-point-free involution of `Fin 6` is
  realized, decided over all 720 permutations. This is the direction that would
  catch a missing matching.

Also `wickMoment_pair : wickMoment G [a,b] = G a b` and
`wickMoment_quartic : wickMoment G [i,i,j,j] = G i i * G j j + 2 (G i j)^2`.

> **Correction (C3/C4 review).** This file's header referred to a recursion
> lemma `wickMoment_cons` that had **not** been delivered — a dangling
> reference to a nonexistent theorem. It is delivered now, and for lists of
> **any** length, via `select_length`, `pairingsAux_fuel` and `pairings_cons`:
>
> ```text
> wickMoment_cons : wickMoment G (a :: rest)
>   = ((select rest).map fun p => G a p.1 * wickMoment G p.2).sum
> ```
>
> So the header's claim that "the enumeration is primary and the recursion is
> derived from it" is now a theorem rather than a description. What remains
> arity-six-only is the correspondence between `pairings` and fixed-point-free
> involutions, and that narrower statement is what the module says.
> `ll/wick_reference.py::moment_recursive` corroborates the recursion
> independently against brute force.

### Disconnected terms cancel exactly (3.2)

`wick6_split` splits the fifteen matchings of `[a,b,i,i,j,j]` into the three
where `a` pairs with `b` and the twelve where it does not — with **no symmetry
hypothesis**:

```text
wickMoment G [a,b,i,i,j,j] = G a b * wickMoment G [i,i,j,j] + connected6 G a b i j
```

`disconnected_cancels` then shows the partition-function subtraction removes the
first term exactly, for every `i` and `j`:

```text
firstOrder G v a b = -∑ i, ∑ j, (1/8) * v i j * connected6 G a b i j
```

This is proved, not observed on examples.

### Hartree and Fock (3.3)

`firstOrder_eq_hartree_fock`, for `hG : G.IsSymm` and `hv : v.IsSymm`:

```text
δ⟨x_a x_b⟩ = -( ½ (G · diag(v d) · G)_ab + (G · (v ⊙ G) · G)_ab ),   d_k = G k k
```

Supporting entrywise lemmas `hartreeMatrix_apply`, `fockMatrix_apply`. The `½`
is what the interaction's `1/8` becomes once the twelve connected matchings are
collected under the `i ↔ j` relabelling; it is not inserted by hand. Symmetry of
`G` is used only to flip the `b` index, symmetry of `v` only in the relabelling
(`sum_swap_of_isSymm`); both uses are localized.

### The link back to the ring family (3.4) — the point of the task

C1/C2A/C2B all began from ring graph data that was *asserted* to be the right
data. Here the order-zero ring is **recovered** from the model's moments:

```text
ring0Matrix_eq              : ring0Matrix G v = -(v ⊙ G)          -- from contribution_ring
dressed_ring0_eq_neg_fock   : G * ring0Matrix G v * G = -fockMatrix G v
firstOrder_eq_dressed_ring0_add_hartree :
    firstOrder G v a b = (G * ring0Matrix G v * G) a b - ½ (hartreeMatrix G v) a b
```

So the Fock term of the first-order correction **is** C2A's
`contribution (ring 0)` dressed with an external propagator on each side, and
what the ring family does not account for is exactly half the Hartree matrix.
`hartreeMatrix_ne_zero` exhibits symmetric `G`, `v` (both the identity at
`N = 2`) with nonzero Hartree matrix, so that remainder is not vacuously zero.
This is the concrete content of C2B's remark that a graph-derived Hartree
contribution was outside its scope.

## Executable evidence

`ll/wick_reference.py` enumerates perfect matchings by brute force and computes
the normalized correction straight from the definition; it reads no artifact and
imports no expected-answer column. `both_agree` raises if the brute-force value
and the closed Hartree/Fock form disagree. `LLC3Main.lean` → `ll_c3_eval` emits,
for three fixtures with symmetric `G` and `v` (two `N=2`, one with non-integer
rationals, one `N=3` with a zero in `G` so the loop vector is non-uniform), the
matrices `delta`, `hartree`, `fock` and `ringDressed` as exact rationals.

The artifact itself carries the two caveats above in `assumed_input` and
`interaction`, and a test asserts they are present — a reader of the JSON alone
cannot miss that Wick is assumed.

Mutants, all detected: normalization dropped (disconnected terms left in),
`1/8` replaced by `1/4` and by `1/2`, Hartree/Fock weights swapped, Hartree
dropped entirely (i.e. "the ring family alone"), an ordinary wrong value, and a
wrong matching count. Routed through `ll/evidence.py` via `validate_c3` with
specification-owned fixtures, orders and series names — no new reader was
written, and `ringDressed` is a required series so the table cannot omit the
link back to the rings.

`tests/test_ll_c3.py`: 27 tests.

## Commands and outcomes

```
bash scripts/bootstrap.sh                          exit 0
lake build                                         exit 0
lake env lean GW/LL/Wick.lean                      exit 0, no output
./.lake/build/bin/ll_c3_eval                       exit 0
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt
                                                   4 refreshed, 0 missing
python3 scripts/verify.py --gate all               exit 0
```

* Scientific gate **319 tests** OK (1 skipped, pre-existing); workflow gate **14** OK.
* **206 named / 592 exhaustive** theorem audits; `AUDIT_MODULE GW.LL.Wick` present.
* Axioms across both audits: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, custom axiom, `native_decide` or unsafe shortcut. The
  `decide` proofs are kernel decision procedures, not `native_decide`.
* No existing theorem, fixture or target was changed. C1/C2A/C2B all still pass.

First gate run failed (exit 1) on the same stale-manifest workflow test as C2B;
refreshed with the existing idempotent tool and reran green.

## Committed versus generated

Committed: `GW/LL/Wick.lean`, `LLC3Main.lean`, `ll/wick_reference.py`,
`tests/test_ll_c3.py`, `.agent/tasks/LL-C3.md`, this handoff, and edits to
`GW.lean`, `GW/Audit.lean`, `lakefile.toml`, `ll/evidence.py`,
`scripts/gates.py`, `scripts/verify.py`, `bgw/weighted_audit/PROVENANCE-R6.txt`.

**Generated, not committed:** `artifacts/ll-c3/wick_values.json` and gate logs.
`artifacts/` is gitignored and the gate regenerates the table before testing it,
as for C2A and C2B.

## Failed attempts

The mathematics had no dead ends because I checked the entire derivation by
brute-force enumeration in Python *before* writing any Lean — the 15-matching
split, the `i ↔ j` collapse and the closed form were all confirmed numerically
first. The failures were mechanical:

1. `pairings_six_complete` hit `maximum recursion depth`. Raised to
   `maxRecDepth 8000`; the kernel handles 720 permutations without trouble. This
   is an elaboration limit, not the C2A-style kernel blowup.
2. `set_option ... in` placed between a doc comment and its theorem is a parse
   error; it must precede the doc comment.
3. First Hartree proof: `simp` unfolded `Matrix.mul_apply` inside the inner
   product before `Matrix.mul_diagonal` could fire, leaving a mismatched
   bound-variable order. Fixed by extracting `hartreeMatrix_apply` and
   `fockMatrix_apply` as staged `rw` lemmas — better shaped anyway, since they
   are independently auditable.
4. Bare `rw [hG.apply]` rewrote the *first* match (`G a j → G j a`) instead of
   the intended one. Fixed with explicit arguments `hG.apply j i`.
5. A trailing `exact Finset.sum_congr …` in `fockMatrix_apply` ran after the
   goal was already closed ("no goals to be solved"); removed.

## What this teaches, and what it does not

* The ring family is now anchored at one end: its lowest-order member is derived
  from the model's moments rather than asserted. That was the gap every prior
  checkpoint carried.
* The Hartree term is a *proved* omission, not a suspected one. Any future claim
  that the ring series is "the" self-energy at fixed `G` is false as stated.
* This is **one order**. Nothing here extends to order 2, to general bare-to-bold
  or skeleton theory, to Theorem 4.12, to self-consistency, or to electronic GW.
  The pairing/involution check is at arity 6 only.
* The honest headline is: *"the first-order correction of the toy model splits
  into Hartree and Fock, the Fock part is exactly the order-zero ring, and Wick's
  theorem is assumed rather than proved."*

## Recommended next decision

**Review this, then choose between order-2 / skeleton work and the C4 electronic
bridge — and prefer C4.** C3 has now shown the graph data is recoverable from the
model at the order where it is cheapest to check; pushing to order 2 would
multiply the combinatorics substantially.

> **Correction (C3/C4 review).** This originally said "105 matchings at 8
> points". That count is the **eight-field vacuum `U²` term**. The second-order
> *two-point numerator* `⟨x_a x_b U U⟩` has **ten** fields and **945** pairings
> (`9!! = 945`). The conclusion — that order 2 is a large step for a result of
> the same kind — is unchanged and in fact understated. The unanswered question that actually matters for this project's stated
destination is whether any of this transfers to the electronic setting, and that
is C4.

A genuinely valuable smaller alternative, if a theory task is preferred: prove
Wick's theorem for a finite-dimensional Gaussian, which would remove this
checkpoint's central assumption. That needs analytic machinery absent from the
pinned dependency and should be scoped as its own checkpoint, not smuggled in.

Not authorized and not started: the rest of the C3 row, C4, merge, push,
visibility or licensing changes, upstream contact.

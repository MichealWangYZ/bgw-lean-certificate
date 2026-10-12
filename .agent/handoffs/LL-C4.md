# LL-C4 handoff — finite static electronic RPA screening

```
Status: CHECKPOINT_READY
```

Not self-acceptance. C5 and everything else were not started; `main` was not
merged; no dependency or toolchain changed; no upstream community was contacted.

## Post-review addendum (C3/C4 review, PR #12)

Disposition: **retain as the C4.1 static-response prototype**, with corrections
to the main non-transferability inference and to one nondiagnostic test. The
original C4 milestone (matched-input production comparison) **remains open**.

I reproduced all findings independently before changing anything. The headline
correction is serious and is marked in place below; the others are recorded at
the points they affect. Corrections applied:

1. **The non-transferability claim was too strong** — see the replacement below.
   The review's counterexample is now a checked theorem, not a concession.
2. **The early-truncation mutant test was nondiagnostic** — it compared the
   early partial sum against the exact `W`, and the *correct* partial sum also
   differs from exact `W`, so it passed for the wrong reason. Now compared
   against the required-order partial sum, plus a residual comparison, plus a
   test that pins the defect so it cannot silently return.
3. **The Neumann series is not a convergent solver on fixture 1** — recorded as
   a test. `det(v·chi0) = 20`, so the product of eigenvalues exceeds 1 in
   modulus and the spectral radius does too, *while the exact static solution
   still exists*. An exact argument with no square roots. This is the sharpest
   available illustration that "formal" here does not mean "summable".
4. Two boundaries the review named and I had not stated plainly: there is **no
   Lean static solution compared against the Python exact solve** (Lean handles
   formal coefficients and the finite telescoping identity only), and the GPP
   theorem is a **scalar static-matching identity** that fixes pole strength
   from an input value — it does not determine the pole location from the
   physical model, map onto `GW.GPP.Data`, or prove the frequency convolution.

## Four caveats that qualify everything below

**1. This is the second consecutive unreviewed checkpoint.** C3 was not reviewed
before C4 began — the owner authorized C4 directly and chose to skip the review
round to conserve reviewer budget. This project's own history records that
consecutive unreviewed passes are where errors enter. I compensated in the two
ways the build book required (an independent oracle by a different algorithm;
every non-claim written down as a theorem or an explicit sentence), but that is
compensation, not a substitute.

**2. The build book is self-authored**, like C3's. Targets were taken from the
roadmap's C4 row and `docs/LL-C2B-REVIEW.md` §6 and committed before
implementing, but the person setting the bar was the person clearing it.

**3. The C4 row's "matched-input comparison" is NOT done.** The repository holds
no dielectric or screened-interaction fixture from a BerkeleyGW run — `fixtures/`
contains only synthetic GPP self-energy data. I verified this before designing.
So the comparison against a production path remains **open**, and this checkpoint
must not be described as having compared anything to BerkeleyGW.

**4. The electronic quantities are specified, not derived.** Transition energies,
spectral weights (which carry spin/degeneracy), the static form of `chi0` and
`eps = 1 - v chi0` are **inputs**. They are not derived from a many-body
Hamiltonian and are not claimed to be BerkeleyGW's conventions.

## Base, result, versions, elapsed

* Base: C3 result `2abd10d` on `ll-c3/wick-hartree-fock` (PR #10).
* Work branch `ll-c4/electronic-screening`, cut from the C3 branch in the same
  worktree (C3 was already pushed, so the build cache is reused).
* Lean 4.19.0 / mathlib `v4.19.0` (`c44e0c8`), Python 3.12.3. Unchanged.
* **Cumulative active wall time: ~12 min** (`04:04:53Z` → `04:17Z`) against a
  6-hour allowance. No obstruction triggered the 90-minute or two-approach rules.

## The question, and the answer

Does any of C1–C3 transfer to the electronic setting? The answer separates into
two halves and **both are proved**.

### The algebra transfers — by definitional reuse, not resemblance

`geoP A = 1 + X·C A`, `geoS A = invOfUnit (geoP A) 1`, `geoW A u = geoS A * C u`
is C2B's algebra with the kernel abstracted out. Two-sided inverse identities
and the coefficient bridge `coeff k (geoW A u) = (-1)^k • (A^k * u)` are proved
once, for arbitrary `A`, over the noncommutative matrix coefficient ring.

Then both settings are instances — and the classical one is **`rfl`**:

```text
classical_W_eq_geoW : GW.LL.W G v = geoW (AL G v) v          -- by rfl
coeff_electronicW   : coeff k (electronicW v ts) = (v * chi0 ts)^k * v
```

So the textbook Neumann series `W = Σ (vχ⁰)^k v` comes out of the *same* library
inverse C2B used, with kernel `-(v chi0)` instead of `½vB`. "The algebra
transfers" is now a statement about definitions, not an impression.

### A direct identification `B = chi0` is wrong — but that is all the signs show

**CORRECTED (C3/C4 review).** This section originally read "the content does not
transfer — by a structural obstruction", concluding from opposite diagonal signs
that C2A/C2B could not be electronic results. **That inference was too strong.**

The lemmas themselves are true and retained:

* `bubble_diag_nonneg : 0 ≤ bubble G i i` — the classical bubble is an entrywise
  square;
* `chi0_diag_nonpos` — a `chi0` from `occ < emp` transitions with nonnegative
  weight has nonpositive diagonal;
* `bubble_chi0_diag_witness` — a case separating them strictly.

What they establish is only that **`B` and `chi0` cannot be directly
identified**. They do *not* establish non-transferability, because the sign is
already carried by the kernels' prefactors:

```text
classical :  1 + z * (v * bubble G) / 2
electronic:  1 - z * (v * chi0)
```

Setting `chi0 = -(1/2) bubble G` makes the kernels **identical**. The reviewer
showed this is realizable inside this file's own model, and it is now proved
here rather than merely conceded:

```text
chi0_eq_neg_half_bubble_witness : admissible transitions with
    chi0 = -(1/2) • bubble G   and   v * bubble G ≠ bubble G * v
electronic_kernel_eq_AL         : -(v * chi0 ts) = AL G v
geoP_electronic_eq_PL           : geoP (-(v * chi0 ts)) = PL G v
electronicW_eq_classical_W      : electronicW v ts = GW.LL.W G v
```

with `G = diag(2,3)`, `v = !![2,1;1,3]` and two admissible channels. The
non-commutativity clause rules out a degenerate accident.

**The surviving claim**, which is what I should have written: the correctly
signed, weighted and convention-matched physical correspondence **has not been
derived here**; and a naive `B = chi0` is wrong. The sign difference must not be
used to dismiss the classical route.

### Sign conventions are internally coherent

`chi0_isSymm`, and `chi0_quadForm_nonpos`: the specified `chi0` is negative
semidefinite whenever every transition runs occupied → strictly higher empty with
nonnegative weight. Proved by list induction, with each transition contributing
`weight/(occ-emp) · (Σ x·m)²`.

### Truncation is finite algebra, not convergence

`dielectric_mul_partialScreened : eps * partialScreened v ts k = v - (v·chi0)^(k+1)·v`

for every `k`, at the matrix level, with no inverse and no limit. This is the
lesson the C2B review taught, applied up front: the residual left by truncating
is an exact finite quantity, not a convergence question. A test checks it is
genuinely nonzero so the identity is not vacuous.

### The GPP bridge — dielectric level only

`gpp_static_limit : gppInvEps (gppOmega2FromStatic invEps0 wtilde) wtilde 0 = invEps0`
under `wtilde ≠ 0`. The single-pole model reproduces the static value under the
standard parameter identification, with the nonvanishing-pole domain condition
that `GW.GPP.PoleDomain` already carries.

**Connecting this to `GW.GPP.Data.sigmaChecked` requires the frequency integral
`Sigma = i G W`, which this repository does not perform anywhere.** Stated in the
module, in the artifact's `scope` field, and asserted by a test.

## Executable evidence

`ll/electronic_reference.py` solves `eps W = v` by **exact Gaussian elimination**
with rational pivoting — a genuinely different algorithm from the Neumann series
Lean manipulates, not a restatement of it. It reads no artifact and imports no
expected-answer column. Three fixtures (two `N=2`, one all-rational, one `N=3`
with three channels).

Verified: `chi0` and `eps` match; Neumann coefficients `k=0..3` match; partial
sums match; the exact solve satisfies `eps W = v`; and the truncation residual
computed from the *emitted* partial sums equals `(vχ⁰)^(k+1)v` at every `k`.

Mutants detected: flipped transition denominator (`emp - occ`), dropped spectral
weight, `eps = 1 + v chi0`, early truncation (now compared against the
required-order partial sum — see the addendum), ordinary wrong value. Routed
through `ll/evidence.py::validate_c4`, which makes **two** calls to the existing
`validate_matrix_table` — one for the static series at `static_orders = [0]`, one
for the expansion at `orders = [0..3]`. No new reader was written.

`tests/test_ll_c4.py`: 31 tests.

## Commands and outcomes

```
lake build ll_c4_eval                              exit 0
lake env lean GW/LL/Electronic.lean                exit 0, no output
./.lake/build/bin/ll_c4_eval                       exit 0
python3 scripts/make_manifest.py bgw/weighted_audit/PROVENANCE-R6.txt
                                                   4 refreshed, 0 missing
python3 scripts/verify.py --gate all               exit 0
```

* Scientific gate **350 tests** OK (1 skipped, pre-existing); workflow **14** OK.
* **225 named / 631 exhaustive** audits; `AUDIT_MODULE GW.LL.Electronic` present.
* Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, custom axiom, `native_decide` or unsafe shortcut.
* No existing theorem, fixture or target changed; C1/C2A/C2B/C3 all still pass.

## Committed versus generated

Committed: `GW/LL/Electronic.lean`, `LLC4Main.lean`, `ll/electronic_reference.py`,
`tests/test_ll_c4.py`, `.agent/tasks/LL-C4.md`, this handoff, and edits to
`GW.lean`, `GW/Audit.lean`, `lakefile.toml`, `ll/evidence.py`, `scripts/gates.py`,
`scripts/verify.py`, `bgw/weighted_audit/PROVENANCE-R6.txt`.

**Generated, not committed:** `artifacts/ll-c4/electronic_values.json` and gate
logs; `artifacts/` is gitignored and the gate regenerates the table.

## Failed attempts

As in C3, the mathematics had no dead ends because the whole model was checked
against the Python oracle before any Lean was written. Mechanical failures:

1. `Finset.sum_mul_sum` left a stuck typeclass metavariable; replaced by an
   explicit `Finset.sum_mul` / `Finset.mul_sum` expansion.
2. A stray `end` closed `namespace GW.LL` early, cascading ~15 spurious errors.
3. **`LinearOrderedField` is deprecated in the pinned mathlib** (since
   2025-04-10) in favour of `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.
   Worth recording: the deprecation surfaced as "type is not a class instance",
   which reads like a missing import rather than a rename.
4. `div_nonpos.mpr` does not exist; the pinned names are
   `div_nonpos_of_nonneg_of_nonpos` and `div_nonpos_iff`.
5. `List.mem_cons_self` takes no explicit arguments in this version.
6. Power bookkeeping: `pow_succ` vs `pow_succ'` peel from opposite ends, and
   `(-M)^k = (-1)^k • M^k` needed its own induction (`neg_pow_smul`).

## What this teaches, and what it does not

* The reusable asset from C1–C3 is the **formal geometric-inverse machinery**,
  and it is genuinely reusable — one definition now serves both settings.
* Everything physical had to be respecified. That is the honest measure of how
  far the classical work carries: the scaffolding, not the physics.
* This is still a **specified model**, not a derivation and not a comparison. The
  next real increment for the stated destination is either (a) obtaining a
  dielectric or `W` fixture from an actual BerkeleyGW run so the roadmap's
  matched-input comparison can be attempted, or (b) the frequency integral
  `Sigma = i G W` connecting this to the existing GPP self-energy track.

## Recommended next decision

**The review's recommendation and mine now agree: one matched-input production
static-screening comparison.** It proposes a 4-hour allowance with a 45-minute
data/access preflight, a complete small retained basis at fixed nonzero `q`,
production `chi0` and bare Coulomb as *inputs* (claiming screening-stage
verification, not derivation of `chi0`), reconciliation of matrix ordering,
units, spin/occupation/k-point weights, complex conjugation, Coulomb treatment
and symmetrization, a predeclared numerical-error criterion, and a deliberately
perturbed convention the comparison must catch. A precise `BLOCKED` is the
correct outcome if the data cannot be obtained — **not** synthetic data reported
as a production success.

One correction to my own earlier framing: I said this was "blocked on data". The
review is right that absence of a fixture in Git is a *starting condition*, not
proof that acquisition is impossible; existing authorized installations, runs and
official examples should be inspected first.

That task is **not authorized** by this review or by anything in this handoff.

## A note I think is worth keeping

The review's sharpest observation is not about any theorem. It is that across
C2B, C3 and C4 the unresolved model/implementation connections keep becoming
*declared inputs or exclusions*, while the local algebra keeps becoming complete
— so the green labels stay green while the interface that matters stays open.
Disclosure is necessary but does not close a connection. Concretely: C4 imports
C2B's `Screening`, not C3's `Wick`; a stacked Git history is not a cumulative
physical derivation. The right corrective is the one the review proposes —
make an unresolved interface the *acceptance criterion* of the next task rather
than a caveat in its handoff.

Not authorized and not started: C5, merge, push beyond this branch, visibility or
licensing changes, upstream contact.

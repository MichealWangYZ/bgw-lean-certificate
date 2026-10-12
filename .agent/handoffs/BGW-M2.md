# BGW-M2 handoff — independently exported chi to certified screening

```
Status: CHECKPOINT_READY
```

> **BGW-M2-R1 addendum.** PR #17 was **not accepted**; the acceptance review
> found four concrete defects in the checks and driver, plus an invalid
> provenance argument. All were reproduced and repaired — see
> `.agent/handoffs/BGW-M2-R1.md`. Corrections are marked in place below. The
> underlying numerical result was unaffected and every reviewer figure was
> reproduced exactly.

Not self-acceptance. No `main` merge, no stack cleanup, no visibility or
licensing change, no upstream contact, no paid compute, no nested agents, no M3.
Commit/push and one private review PR are under the standing grant.

## Base, result, time ledger

* Base: PR #14 repair `353f980` plus the M2 plan branch (`badf70a`).
* Branch `bgw-m2/rounding-aware`, isolated worktree. Other worktrees untouched.
* **Active time ≈ 25 min** (`04:11:16Z` → `04:36Z`) of the **12-hour** allowance.
  Access preflight ≈ 5 min of its 60-minute cap. The allowance is a ceiling, not
  a target; the work finished early because M1's infrastructure carried over.
* Waypoints: **A** ≈ 04:16 (Lean baseline built, both trees copied, hashes
  pinned) · **B** ≈ 04:22, due by 3 h (chi/V/E/X exported, A/B byte-identical,
  conventions and budgets frozen) · **C** ≈ 04:28, due by 6 h (first new
  actual-input certificate compiled) · **D** ≈ 04:33 (full gate green).
  No no-progress trigger fired; no obligation needed a second approach.

## Pristine / instrumented comparison — full block, not diagonals

Two separate trees, separate clean real-flavor builds, separate fresh run
directories, identical input bytes, all thread counts pinned to 1.

```
cmp m2run-pristine/epsmat  m2run-instr/epsmat    -> identical
cmp m2run-pristine/eps0mat m2run-instr/eps0mat   -> identical
```

The **entire `epsmat` output file** is byte-identical, so all 64 entries of the
retained inverse agree by construction — no decoder needed and no partial
two-diagonal-entry substitute. Empirical instrumentation neutrality **for this
input and these settings only**; not a theorem about the patch in general.

## Acquisition, and why it is not circular

`pol%chi` is read and never written in `epsinv.f90`, so exporting it at the
point of use gives exactly the operand the formation consumed. Exported per
entry as a 17-digit decimal **and** raw IEEE-754 bits, with a **run identity**
on every block delimiter: `CHI`, `VCOUL`, `GVEC`, `EPSPRE`, `EPSINV`.

> **Corrected (R1).** This claimed that `chi ≠ V⁻¹(1 − E_hat)` rules out
> circularity. It does not. `round64(V⁻¹(1 − E_hat))` is answer-derived by
> construction, differs from the exact recovery, differs from the exported
> `chi` in 10 of 64 entries, and satisfies the decision rule. Independence
> rests on inspected source correspondence, fixed digests and byte-identical
> replay — not on any comparison of matrix values. Also, "reads and never
> writes" covers the **inspected routine**, not the whole program.

The parser reuses the boundary repaired in M1-R1 — importing its primitives, not
re-implementing them — and additionally rejects a mismatched run identity.

**M1 reuse justified:** the newly exported `E_hat`, `X_hat` and `vcoul` are
**identical** to M1's represented matrices (checked in
`tests/test_bgw_m2.py::ReuseOfM1IsJustified`), so `Ehat`/`Rhat` reuse `GW.BGW.E`
and `GW.BGW.Rref` with M1's certificates instead of re-deriving them.

## Traced floating-point path — measured, not assumed

* **64/64** stored entries equal `fl(delta − fl(v·chi))` — two roundings;
* only **63/64** equal a fused `fl(delta − v·chi)`.

So the compiled path is not a contracted FMA, and one entry actually
distinguishes the hypotheses. The frozen budget is conservative for **either**
path, so the certificate does not depend on this determination.

## Three matrices, kept apart

| Quantity | Value |
| --- | --- |
| `Delta = E_hat − E_star` nonzero entries | **64 / 64** |
| `max |Delta|` | `1.505033517723375e-16` |
| `gamma2 = 2u/(1−2u)` | `1/4503599627370495` |
| tightest `|Delta_ij| / B_ij` | `0.3945` |

`E_hat ≠ E_star` everywhere, exactly as the premise of the task requires.

> **Corrected (R1).** `max |Delta| = 1.505e-16` is entrywise; the row-sum
> `‖Delta‖∞ = 2.396e-16`. Headroom is 2.53× entrywise and 4.73× in the row-sum
> norm. "Tight" applies only to **formation** — the **total** budget is ≈1420×
> the observed total error and is dominated by the engineering `b_inv`.

## New Lean theorems

General, arbitrary ring and index type:

```text
inverse_shift  : Rhat*Ehat = 1 → Estar*Rstar = 1 →
                 Rhat - Rstar = -(Rhat * (Ehat - Estar) * Rstar)
screened_shift : same, post-multiplied by V
absQ_eq        : absQ x = |x|            (max form, so literals reduce)
```

Concrete, on the exact rational decodings of this run's operands:

```text
Estar_eq                : Estar = 1 - V * chi        -- the literal IS the exact formation
formation_bound         : ∀ i j, |Delta i j| ≤ B i j
Rstar_mul_Estar         : Rstar * Estar = 1
Estar_mul_Rstar         : Estar * Rstar = 1
Rstar_unique            : Estar * Y = 1 → Y = Rstar
Estar_mul_Wstar         : Estar * Wstar = V
inverse_shift_instance  : Rhat - Rstar = -(Rhat * Delta * Rstar)
screened_shift_instance : WhatRef - Wstar = -(Rhat * Delta * Rstar * V)
rowAbsSum_eq, nrmEhat_bounds, nrmRhat_bounds, nrmRstar_bounds, bForm_bounds
total_error_bound       : ∀ i, rowAbsSum (Xhat - Rstar) i ≤ bTotal
```

`total_error_bound` is the required finite endpoint: the **actual encoded
production inverse** bounded against the reference built from **independently
exported** operands, under a budget frozen from inputs. Row-sum (infinity) norm
throughout, stated explicitly rather than inherited from a generic instance.

> **Corrected (R1).** The **component** inequalities were missing, and proving
> only the total does not enforce the advertised contract: the review built a
> realizable binary64 candidate inside the total budget but outside `b_inv`.
> `inv_error_bound` and `shift_error_bound` were added, and `decides` now
> enforces all three components separately.

Compiles in 2 m 13 s; 18 M2 theorems in the named audit; axioms limited to
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, custom axiom,
`native_decide` or unsafe shortcut.

## The three error components

| Component | Budget | Measured |
| --- | --- | --- |
| formation | `b_form = 1.1342931227599965e-15` | `max|Delta| = 1.505e-16` |
| inversion (stored problem) | `b_inv = 2.5719777753175876e-13` | — |
| propagated shift | `b_shift = 6.429944438293971e-16` | `‖R_hat − R_star‖∞ = 5.895e-17` |
| **total** | **`b_total = 2.578407719755882e-13`** | **`‖X_hat − R_star‖∞ = 1.8151e-16`** |

Both residual normalizations kept explicit: `r/p = 7.008168410280357e-17` and
`r/(p+1) = 5.562036787802374e-17`. The second **reproduces the acceptance
record's number exactly**, confirming that reconciliation independently.

## Mutations and controls

Same frozen decision rule (`decides`) for control and every mutant; each mutant
compared against its own intended problem, with the reference recomputed:

wrong-side Coulomb (`I − chi·V`), wrong sign, wrong prefactor, one-sided basis
permutation, ordinary wrong formation entry, ordinary wrong inverse entry,
forged zero-formation-error — **all rejected**. Unmodified control **accepted**.
A **consistent** permutation of all matrices and the basis together remains
**valid**, as a positive control on the representation.

Parser regressions retained and extended: repeated run/q, nested start,
mismatched run identity, wrong run id, dropped entry, in-block duplicate, broken
decimal/bits round trip, out-of-range label, non-finite value.

**Corrupted certificate rejected:** +1 in the last digit of one `Rstar`
numerator turns the product goals into `⊢ False`, exit 1. That file is
namespaced `M2Corrupt`, lives outside the repository, and is in neither
`GW.lean`, `GW/Audit.lean` nor the audit log.

## Commands and outcomes

```
scripts/bootstrap.sh                                        exit 0
make clean && make -j8 epsilon   (pristine and instrumented) exit 0, exit 0
epsilon.real.x   (two fresh run dirs, threads pinned)        exit 0, exit 0
cmp epsmat / eps0mat across builds                           identical
lake env lean GW/BGW/M2Screening.lean                        exit 0, 2m13s
python3 bgw/m2_screening/run_m2.py                           OK
python3 -m pytest tests/test_bgw_m2.py                       38 passed
python3 scripts/verify.py --gate all                         exit 0
```

Gate: **435 scientific + 14 workflow** tests (was 397 + 14); **258 named / 696
exhaustive** audits; `AUDIT_MODULE GW.BGW.M2Screening` present. No existing
theorem, fixture, target, dependency or GPP scope changed; only the unavoidable
existing manifest refresh.

## Committed versus generated

Committed (~60 KB): `GW/BGW/M2Screening.lean`, `bgw/m2_screening/{extract,
reference,run_m2,check_lean_literals}.py`, `epsinv_m2_dump.patch`,
`PROVENANCE.md`, `data/m2_dump_q2.txt`, `tests/test_bgw_m2.py`, wiring.

Not committed: the two 159 MB BerkeleyGW trees, wavefunctions, full three-q
dumps, `epsmat` outputs, gate logs. Hashes and commands are in `PROVENANCE.md`;
the `/tmp` paths are recorded as locations, not as durable provenance.

## Remaining gaps

1. **The origin of `chi`** from wavefunctions is still outside the chain. M2
   moved the boundary one stage up, not to the start.
2. No exported production `W`. `Wstar` and `WhatRef` are **derived** from
   certified inverses and `V`; nothing here certifies a production `W`
   multiplication.
3. Instrumentation neutrality is empirical for this input and these settings.
4. `b_inv`'s constant 100 remains an engineering choice, not a proved bound.
5. One q, one cutoff, one material, unconverged by design.
6. The general C3 theory row and the end-to-end electronic-GW C4 row are
   untouched by this milestone.

## One recommended next decision

**Review this, then choose deliberately between the two open lanes rather than
adding a third matrix instance.** The physics-interface lane's next real step is
the origin of `chi` — exporting the transition matrix elements and occupation
factors and certifying one `chi` entry against them — which is a genuinely
harder problem than M1/M2 because it involves the wavefunction sum, not just
linear algebra. The theory lane (model moments / skeleton, or the GPP frequency
link) is untouched and was the original destination.

I would not recommend a third screening-instance certificate: M1 and M2 have
established the pattern, and repeating it at another q or basis size would add
confidence in the tooling without advancing either open question.

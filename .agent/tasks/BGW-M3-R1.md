# BGW-M3-R1 — close the operand-to-chi certificate, then STOP

Base: `35ebab4` on `bgw-m3/chi-transition-sum`.

This is a **closure milestone for M3**, not a new physics milestone. Do not broaden it to another screening instance, more chi entries, GPP, wavefunctions, FFT provenance, partial occupations, or q->0 behavior.

## Milestone

For the pinned M3 run at q index 2, Lean must prove **two unconditional operand-level endpoint theorems**, one diagonal and one nontrivial off-diagonal:

- entry (1,1)
- entry (1,2)

The reconstruction must be defined from the committed exported operands:

- unweighted matrix elements before `sqrt(-eden)`
- `eval`, `econd`, `occ_v`, `occ_c`
- `fact`
- `pht` phases and `indt` index map
- the complete pinned transition/star inventory

For each target entry define, at the mathematical level,

```
d*_t = (occ_v,t - occ_c,t) / (eval_t - econd_t)

chi*_ij = fact * sum_(transition,star)
            d*_t * gme_t(ind_i) * ph_i * gme_t(ind_j) * ph_j
```

and prove concrete theorems of the form

```
absQ (chiHat11 - chiStar11) <= finalBudget11
absQ (chiHat12 - chiStar12) <= finalBudget12
```

where the two endpoint theorems take **no unproved numerical hypotheses**.

A helper theorem may be general and conditional. The final two concrete theorems must discharge every hypothesis for the pinned data.

## What counts as closure

### 1. Kernel-check the operand-to-witness arithmetic

The current M3 generator computes signed products and denominator residual witnesses in Python before Lean sees them. R1 must add kernel-checked identities that connect those generated witnesses back to the encoded operands and index map.

A systematic bug in Python's product/residual construction must therefore be capable of making Lean fail.

This does NOT require formalizing the file parser or Fortran. The parsed/exported values may remain the input boundary. Arithmetic claimed by the certificate downstream of that boundary must be checked in Lean.

### 2. Prove the denominator transfer for this concrete dataset

Establish, for the pinned transitions, a denominator error bound derived from the encoded energies and occupations, and compose it through the finite sum.

A sufficient pattern is:

```
|edenHat_t - d*_t| <= eps_t
```

then

```
|sum a_t * edenHat_t - sum a_t * d*_t|
  <= sum |a_t| * eps_t
```

with `a_t` built from the checked prefactor, matrix elements, phases, and map.

The exact mixed-denominator sum may remain symbolic. Do not normalize everything into one giant rational unless useful.

The current `entry11_operand_budget` / `entry12_operand_budget` style is NOT enough if it still accepts the transfer inequality as a hypothesis.

### 3. Correct the denominator claim

Do not call the current residual inequality a proof of "correctly rounded" unless exact IEEE rounding is actually formalized.

Separate two claims cleanly:

- Lean: a proved denominator error bound sufficient for the transfer theorem.
- Python/empirical check: the exported denominator matches `fl(occ_diff / fl(eval - econd))` on 280/280 transitions for this pinned run/compiler.

### 4. Repair the rounding-budget justification

The production path forms a rounded `sqrt(-eden)` and that rounded quantity enters both weighted matrix elements. The error analysis must account for its repeated multiplicative use, or provide another valid derivation of the final bound.

The final budget must be fixed from the operation/error model and operand magnitudes, not tuned to the observed chi discrepancy.

It is acceptable if the numerical headroom changes substantially. Preserving the previous 444x figure is NOT a requirement.

### 5. Discriminating regressions

Keep the existing control and mutations. Add at least these two regressions:

1. **Product-witness mutation:** alter one generated product witness while keeping the raw operands fixed, and update any aggregate total necessary to prevent rejection only because of the old sum equality. Lean must fail at the new operand-to-product correspondence.
2. **Residual-witness mutation:** alter one denominator residual/error witness while keeping its raw energy/occupation operands fixed. Lean must fail at the operand-to-residual correspondence.

Record which proof obligation fails. A parser failure or unrelated build failure does not count.

Also retain rejection of:
- dropped/substituted transition
- wrong occupation difference
- swapped `eval` / `econd`
- phase error on one side
- perturbed matrix element
- wrong prefactor

and acceptance of the unmodified control.

### 6. Make M3 -> M2 linkage executable

Add a machine-checked comparison showing that the M3 chi q-block is the same q/basis/data block that M2 consumed, allowing only the documented run-id difference.

Do not leave this only as prose in the handoff/A-B log.

## Required final checks

At the final R1 commit, all must pass:

```bash
python3 -m pytest tests/test_bgw_m3.py
python3 bgw/m3_chi/make_certificate.py --check
lake build
python3 scripts/verify.py --gate all
```

The new endpoint theorems and their dependencies must be included in the exhaustive audit.

No `sorry`, `admit`, new `axiom`, or `native_decide`.

The handoff must print the **complete signatures** of the two final operand-level endpoint theorems, not only their axiom dependencies.

## Acceptance condition

R1 is complete only when the repository contains two concrete, unconditional, audited Lean theorems establishing that the actual exported production values for entries (1,1) and (1,2) lie within justified operand-derived error budgets of the complete transition sums reconstructed from the committed energies, occupations, unweighted matrix elements, prefactor, phases, and index map.

In short:

> **Pinned physical operands -> checked finite transition sum -> production chi, with the full numerical transfer discharged in Lean for (1,1) and (1,2).**

That is the milestone. Once those two endpoint theorems and the discriminating regressions pass, STOP.

## Non-goals

Do not require:
- the other 62 chi entries in Lean
- a second material or second q block
- skipped/partially occupied transition coverage
- wavefunction or FFT provenance
- q->0 head/wing limits
- frequency dependence
- spinors
- GPP
- compiler/BLAS formalization
- a whole-program BerkeleyGW correctness claim

These remain later or explicitly separate milestones.

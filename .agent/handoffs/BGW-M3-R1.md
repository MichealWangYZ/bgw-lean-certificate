# BGW-M3-R1 — operand-to-chi certificate closed

**Status: CHECKPOINT_READY. Not accepted by me.**

Base: `00284fc` on `bgw-m3/chi-transition-sum` (PR #22). Active time ~4 h.

The R1 milestone was to remove the conditional step: the M3 Lean certificate
reached the exported-`eden` reconstruction, while the operand-level statement
took the transfer as a hypothesis. It no longer does.

## The two endpoint theorems

Complete signatures, as required:

```lean
theorem GW.BGW.M3.entry11_endpoint :
    absQ (chiHat11 - chiStar11) ≤ finalBudget11

theorem GW.BGW.M3.entry12_endpoint :
    absQ (chiHat12 - chiStar12) ≤ finalBudget12
```

No hypotheses, no `reconExact`, no assumed transfer inequality, no assumed
operand-to-product or operand-to-residual identity. Both audited:

```
'GW.BGW.M3.entry11_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'GW.BGW.M3.entry12_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The proof chain from the encoded operands

`chiStar11` is not a literal. It is a definition over rows that recompute
every derived quantity from the raw operands:

```lean
def toRawRow (stars : List Star) (t : TransRec) : Row :=
  { ..., dZ := t.evZ - t.ecZ, oZ := t.ovZ - t.ocZ, qw := qOf stars t.g, ... }
def rawRows11 : List Row := kpts.flatMap (fun kp => kp.2.2.map (toRawRow kp.1))
def chiStar11 : ℚ := (rawRows11.map (fun r => r.coefQ S * r.dStarQ S)).sum
```

> **Corrected in the PR #23 follow-up.** My first version defined `chiStar`
> over the *witness* rows, whose `qw`, `dZ` and `oZ` were generated literals.
> `products_correct` and `rows_ok` checked those witnesses, but
> `entry11_endpoint`'s own proof did not depend on `products_correct`, so the
> endpoint statement was about a witness-defined quantity rather than about
> the raw operands. The independent audit caught this and it was a real gap.
> `chiStar` is now built from `rawRows`, and `rows11_eq_rawRows11` (by `rfl`)
> is what `transfer_bound11` rewrites through, so the endpoint reaches the
> committed matrix elements, energies and occupations.

`kpts` is the only data: per k-point, the star map `(indt, pht)` for basis
indices 1 and 2, and every transition's `eval`, `econd`, `occ_v`, `occ_c`,
`eden` and its eight **unweighted** matrix elements. Everything else is
derived in Lean and checked:

| Link | Obligation | Tactic |
| --- | --- | --- |
| matrix elements + star map → `qw1`, `qw2` | `products_correct : qwOK = true` | `rfl` |
| `evZ,ecZ → dZ`; `ovZ,ocZ → oZ`; residual; `eUp` dominates | `rows_ok11`, `rows_ok12` | `rfl` |
| rows come from that table | `rows11 = allTrans.map (toRow false)` | definitional |
| sum with the exported denominators | `chiRecon11_eq` | `recon_eval` + `int_sum_split` |
| production rounding | `entry11_within_budget` | `norm_num` |
| exported → operand-implied denominator | `transfer_bound11` | `table_transfer` from `rows_ok11` |
| endpoint | `entry11_endpoint` | triangle inequality |

The general lemmas live in the hand-written `GW/BGW/M3Transfer.lean`
(`list_transfer`, `abs_sub_div_le`, `row_bound`, `table_transfer`,
`recon_eval`, `transfer_eval`, and the sum plumbing). They are conditional, as
the brief allows; the two concrete theorems discharge every hypothesis by
kernel computation.

## Item by item

**1. Operand-to-witness arithmetic is kernel-checked.** Python no longer hands
Lean anything it does not recheck. `qOf` recomputes the star sum from the
eight matrix elements and the index map; `rowOK` recomputes `dZ`, `oZ` and the
residual from `evZ`, `ecZ`, `ovZ`, `ocZ`.

**2. The transfer is proved for this dataset.** `row_bound` turns the integer
residual witness into `|edenHat - dStar| ≤ eps`, and `table_transfer`
propagates it. `transferBudget11_eq` evaluates the resulting allowance to a
literal via `transfer_eval`.

**3. The denominator claim is corrected.** Lean proves a *bound*. It does not
prove correct rounding, and nothing here formalizes IEEE-754. The empirical
result — exported `eden` equals `fl(occ_diff / fl(eval - econd))` on 280/280,
against 211/280 for the single-rounding model — is a Python test, labelled as
being about this compiler and these operands.

**4. The budget is repaired.** The single rounded `w = fl(sqrt(-eden))`
multiplies **both** weighted matrix elements, so each product carries
`(1+delta_w)^2` and the sqrt rounding counts twice. `ROUNDINGS_PER_TERM` is
now 5 (was 4 with `eden` separately charged). `eden`'s own rounding left the
estimate entirely and became the proved transfer term. For the tightest entry
(5,5): production `5.753075e-15`, transfer `1.567625e-18`, usage
`2.250e-03` of allowance. All 64 entries still hold in Python.

**5. Discriminating regressions.** `bgw/m3_chi/mutate_certificate.py`:

```
unmodified control       : lean exit 0, no failing declaration
product witness mutation : first failing = theorem products_correct
residual witness mutation: first failing = theorem rows_ok11
```

The harness now attributes errors to `def`s as well as theorems (a later
definition could previously be blamed on the preceding theorem), requires the
intended declaration to be the FIRST failure rather than merely present, runs
the pristine module through the same throwaway path as a control, and binds
the log to SHA-256 fingerprints of `M3Chi.lean` and the harness itself.

> **Corrected in the PR #24 follow-up.** My residual mutation perturbed
> `resid` *upwards*, which broke two clauses of `rowOK` at once: the residual
> identity **and** the error allowance. `eUp` is the exact ceiling, tight to
> the last bit, so any increase in `resid` overflows it. `rows_ok11` failing
> therefore did not isolate the operand-to-residual correspondence — the
> allowance could have been the cause. The mutation is now `resid - 1`, which
> leaves the allowance satisfied, and the harness asserts clause by clause
> that only the residual identity is broken before it ever calls Lean.
> Measured on the first row: `resid + 1` gives
> `{residual_identity: False, allowance: False}`; `resid - 1` gives
> `{residual_identity: False, allowance: True}`, everything else `True`.

Beyond the committed harness I also checked, once, that the raw binding is
load-bearing: perturbing a single raw matrix element by `2^40` while leaving
every witness untouched fails `products_correct`, `rows11_eq_rawRows11` and
`rows12_eq_rawRows12`. Not added to the harness, to keep this follow-up's
scope as stated.

The product mutation repairs `posSum11`, `negSum11`, `transferNum11` and the
two rational literals derived from them, so the *only* thing left inconsistent
is the operand-to-product relation. The residual mutation fails both row
lists because the residual belongs to the transition, not to a target entry.
All earlier mutations and the unmodified control are retained.

**6. The M3→M2 linkage is executable.** `bgw/m3_chi/link_m2.py` normalises
only the run-id token, compares the slices, then compares the decoded `chi`,
`vcoul`, `Ehat`, `Xhat` and basis entry by entry. Two negative controls.

## Commands

```
python3 -m pytest tests/test_bgw_m3.py            49 passed
python3 bgw/m3_chi/make_certificate.py --check    exit 0
python3 bgw/m3_chi/link_m2.py                     exit 0
python3 bgw/m3_chi/mutate_certificate.py          exit 0  (control + both)
lake build                                        exit 0
python3 scripts/verify.py --gate all              exit 0
```

Gate: **495 scientific + 14 workflow**, **293 named / 772 exhaustive** audits,
`AUDIT_MODULE` present for both `GW.BGW.M3Transfer` and `GW.BGW.M3Chi`. No
`sorry`, `admit`, new `axiom` or `native_decide` in either module; a test
asserts this for both files.

## Failed attempts worth recording

* A flat per-star witness table (1792 rows carrying their own matrix
  elements) elaborated in **14.5 min**. Grouping by k-point — the star map is
  a property of the k-point, not the transition — cut the literal count ~56x
  and the whole module now elaborates in ~25 s.
* `Int` folds do not reduce in the kernel at this size; the `Nat` split via
  `int_sum_split` is why the sums are carried as two natural sums.
* Renaming the mutant module's namespace made `Scales`/`Row` unresolvable, so
  every obligation "failed" — a build failure that proves nothing. Removed.
* The first product mutation also broke `chiRecon11_eq` and
  `transferBudget11_eq` because the generated proofs embedded the sum
  literals a second time. The generator now names each literal once.

## Limitations, unchanged

Two of 64 entries are certified in Lean; the other 62 are Python-checked.
This run has no skipped and no partially occupied transition, so that branch
of `get_eden` is untested — a stated limitation, not a proved absence. No
claim about wavefunctions, the FFT, convergence, the frequency-dependent
path, spinors, the q → 0 limits, the compiler, the BLAS, or BerkeleyGW as a
program.

## Recommended next decision

Review against `.agent/tasks/BGW-M3-R1.md`. I did not start anything further.

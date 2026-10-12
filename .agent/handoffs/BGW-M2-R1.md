# BGW-M2-R1 handoff — repair the M2 acceptance boundary

```
Status: CHECKPOINT_READY
```

Not self-acceptance. No `main` merge, no stack cleanup, no visibility or
licensing change, no upstream contact, no M3, no change to the snapshot, the
frozen budgets or the numerical result. Commit/push and the PR update are under
the standing grant.

## Base, result, time

* Base: M2 result `5ccf753` on `bgw-m2/rounding-aware`; review evidence in draft
  PR #19 at `7af6444` and the concurrent source-safety finding in PR #18.
* **Active time ≈ 35 min** (`04:04:37Z` → `04:40Z`).
* The reviewed implementation was **not** restarted. `data/m2_dump_q2.txt`,
  `GW.BGW.M2.Estar/Rstar/Xhat/chi/vc` literals and all budget constants are
  unchanged; `scripts/make_manifest.py` reports the snapshot digests unchanged.

## Verification of the verdict, before repairing

I ran the reviewer's `acceptance_regressions.py` unmodified against `5ccf753`:
**7 tests, 3 pass, 4 fail** — exactly as reported. Each failure was a real
defect in my acceptance checks, not a disagreement.

I also reproduced every independent figure in the verdict exactly:

| Quantity | Reviewer | Mine |
| --- | --- | --- |
| `‖Ê − E_star‖∞` | `2.39618e-16` | `2.396180681803995e-16` |
| `‖X̂ − R̂‖∞` | `1.28838e-16` | `1.2883849931305328e-16` |
| `‖R̂ − R_star‖∞` | `5.89524e-17` | `5.89524274501315e-17` |
| `‖X̂ − R_star‖∞` | `1.81511e-16` | `1.8151131880718541e-16` |

## A — the driver could modify the supplied source tree

**Confirmed.** `shutil.copytree(source, tree, symlinks=True)` preserved an
absolute `flavor.mk` symlink pointing back into the supplied tree; the following
`shutil.copy` onto `flavor.mk` then *followed* it and overwrote the owner's
file, before any native command ran. My non-destructive guarantee was false.

**Repair.** `safe_copy_tree` copies with symlinks preserved and then
**materializes** every symlink whose resolved target lies outside the copy
(dropping dangling ones), so no write inside the copy can reach the source.
Writes use `write_no_follow`, which unlinks before writing. `reproduce` now
snapshots the digest of **every** regular file in the supplied tree and
re-checks them after the builds, failing loudly on any change. Moving the same
unsafe write into another temporary directory would not have fixed this, so I
did not.

## B — the checker accepted output violating the inversion budget

**Confirmed.** `decides` enforced formation and the **total** only. The
reviewer's realizable binary64 candidate satisfies the total while
`‖X−R̂‖∞ = 2.5753467640e-13 > b_inv = 2.5719777753e-13`. The Lean module
likewise defined the component budgets but proved only the total.

**Repair.** `decides` now enforces `b_form`, `b_inv`, `b_shift` **and**
`b_total` separately. Two new concrete Lean theorems:

```text
inv_error_bound   : ∀ i, rowAbsSum (Xhat - Rhat) i ≤ bInv
shift_error_bound : ∀ i, rowAbsSum (Rhat - Rstar) i ≤ bShift
```

`total_error_bound` is retained. No norm library was added.

> **Corrected in BGW-M2-R2.** This paragraph originally said the total "is not
> implied by the components in general". That is backwards for these
> definitions: `b_total = b_inv + b_shift`, so the triangle inequality gives
> the total FROM the components. What fails is the converse — the total
> establishes neither component — which is the actual reason the two component
> theorems are proved separately. See `.agent/handoffs/BGW-M2-R2.md` §4.

## C — the forged-zero negative test was vacuous

**Confirmed, and it is the same vacuity class I repaired in M1-R1.** The body
asserted `not (decides(...) and Es == Ehat)` *after* asserting `Es != Ehat`, so
the conjunct was constantly false and the test passed regardless. The reviewer
replaced `decides` with an always-accepting function and the test still passed.

**Repair.** `reference.validate_formation_claim(chi, vcoul, E_hat, claimed)`
recomputes `Delta` from operands the claimant does not supply and rejects a
claim that disagrees. `decides` takes the claim positionally and routes it
through that boundary. The negative test now submits a forged zero `Delta`
against the **unmodified archived** `E_hat`, so disabling the rejection logic
makes it fail — which is precisely the reviewer's meta-check.

## D — full reproduction bypassed the strict parser

**Confirmed.** `reproduce` sliced the *first* matching `QSTART`–`QEND` and
hashed it. With the genuine target block appended twice, the first slice had the
expected digest and the duplicate was discarded before validation, so the driver
returned success.

**Repair.** The complete dump is parsed with the strict parser first — which
raises on a repeated run/q — then the run identity is checked, a missing or
repeated target block is refused, and only then is the block selected. The
inventory rule requires the file to belong entirely to the expected run and the
target to occur exactly once; it does **not** demand the other q blocks, so an
isolated legitimate single-block dump still passes. That distinction cost me one
iteration: my first version hard-coded a three-block inventory and broke the
reviewer's own control.

**Delivery gap also fixed.** Neither driver mode invoked Lean;
`check_lean_literals.py` compares literals only. `--proof` now elaborates
`GW/BGW/M2Screening.lean`, and the documented acceptance command is
`run_m2.py --full --proof …` **together with** `scripts/verify.py --gate all`.
A driver run without `--proof` is explicitly not a kernel check.

## The circularity argument was wrong

The export itself looks genuine — the patch reads the existing `pol%chi` before
the inverse call — but my justification was a non-sequitur:

> the exported `chi` differs from `V⁻¹(1 − Ê)`, therefore circularity is ruled out

`round64(V⁻¹(1 − Ê))` is answer-derived **by construction**, yet differs from
the exact recovery, differs from the exported `chi` in **10 of 64** entries, and
satisfies the decision rule. I reproduced that counterexample and kept it as a
test that records *why* the inference fails. Independence is a property of
acquisition and data flow; matrix non-equality cannot establish it. The
supporting evidence is inspected source correspondence, fixed digests and
byte-identical replay. I also narrowed "reads and never writes" to the
**inspected routine** — I did not establish it for the whole program.

## Smaller corrections

* Removed the documentation-word test; checking that a file contains the string
  "unconverged" validates nothing.
* The permutation positive control now permutes the **exported basis labels**
  with the matrices, checks the relabelled basis is a genuine permutation, and
  checks each Coulomb factor travels with its G vector. It previously
  transformed numerical arrays only.
* `max |Delta|` (entrywise, `1.505e-16`) and `‖Delta‖∞` (row sum, `2.396e-16`)
  are now reported as the distinct quantities they are.
* "Tight budget" is now scoped to **formation** — 2.53× entrywise, 4.73×
  row-sum. The **total** is ≈1420× the observed error and dominated by the
  engineering `b_inv`; the constant 100 was not and must not be tuned to this
  fixture.

## Results

```
reviewer acceptance_regressions.py (unmodified)   7 tests, OK  (was 3/4 fail)
python3 -m pytest tests/test_bgw_m2.py            43 passed    (was 38)
lake env lean GW/BGW/M2Screening.lean             exit 0, 2m15s
python3 scripts/verify.py --gate all              exit 0
```

Gate: **440 scientific + 14 workflow** tests; **260 named / 698 exhaustive**
audits; 20 M2 theorems in the named audit; axioms limited to `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, `admit`, custom axiom,
`native_decide` or unsafe shortcut. Snapshot, literals and budgets unchanged.

The four acceptance regressions are migrated into `tests/test_bgw_m2.py`
(`AcceptanceRegressions`) so the gate enforces them; the reviewer's script stays
on PR #19 as their evidence rather than being vendored here.

## What remains open

Unchanged by this repair: the origin of `chi` from wavefunctions, any exported
production `W`, the frequency convolution, self-consistency, physical accuracy
at this deliberately unconverged cutoff, and both original theory rows.
Instrumentation neutrality remains empirical for this input. `b_inv`'s constant
100 remains an engineering choice.

## One recommended next decision

**Accept or reject this repair; then take the reviewer's χ transition-sum
target.** I agree with their reasoning and with their argument against another
screening instance: `chi` is now the earliest opaque input in the chain. One
nontrivial off-diagonal `chi` entry, assembled from its complete finite
transition population, with the source mapping identifying which factors are
already absorbed into BerkeleyGW's effective matrix elements — exporting an
already-weighted product and calling it a derivation would hide the same gap.

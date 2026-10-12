# BGW-M2-R2 — completion pass on the M2 acceptance package

**Status: CHECKPOINT_READY. Not accepted by me.**

Base: `8e754bd553d8e62d16b1f7fd6296eaa7a2f45322` (PR #17 head after R1).
Active time: ~45 min, of which ~20 min was the native A/B rebuild and two Lean
elaborations.

The second acceptance recheck confirmed the R1 repairs but found that the
package-level claims were premature on three counts. All three reproduced
before being repaired. Snapshot, budgets, Lean literals and scientific scope
are unchanged.

## 1. The migrated inversion regression had stopped discriminating

R1 rebuilt the review's mutant as `R_hat[0][0] + 2 * b_inv`. Measured:

| | value | budget |
| --- | --- | --- |
| R1 mutant, inversion error | `5.1444028429942409e-13` | `b_inv = 2.5719777753175876e-13` |
| R1 mutant, total error | `5.1444277444141919e-13` | `b_total = 2.578407719755882e-13` |
| review mutant, inversion error | `2.5753467640116286e-13` | `b_inv = 2.5719777753175876e-13` |
| review mutant, total error | `2.5753716654315802e-13` | `b_total = 2.578407719755882e-13` |

The R1 mutant violates the total as well, so the total rule alone rejects it
and the test passes against a checker with no inversion guard at all. It
certified nothing about the repair it was migrated to protect. The review's
figure `5.144427744414192e-13` reproduces exactly.

Repaired in `tests/test_bgw_m2.py`:

* `_tight_inversion_mutant` restores `b_inv + b_shift / 2` with binary64
  rounding;
* `test_the_inversion_subbudget_is_enforced` asserts **both** halves — over
  `b_inv`, inside `b_total` — before asserting rejection;
* `test_deleting_only_the_inversion_guard_breaks_that_regression` runs the
  mutant through `_decides_without_inversion_guard`, a copy of `decides` with
  only the inversion comparison removed, and requires it to ACCEPT. If some
  other rule caught the mutant, that test fails and the regression is known
  not to be load-bearing.

## 2. Input preservation was incomplete

R1 hashed `WFN`/`WFNq` before the run and never again, and placed the source
comparison after the build loop so a raised native command skipped it. The run
directories `os.symlink` the wavefunctions straight at the supplied originals.

Reproduced with a disposable probe: a mocked native step writing through
`run-pristine/WFN` left the supplied input corrupted and the driver returned
`0`.

Repaired in `bgw/m2_screening/run_m2.py`:

* `verify_preserved(source, before_source, inputs, before_inputs)` compares
  digest maps of every regular file in the supplied source tree **and** the
  supplied inputs directory;
* the build/run loop moved into `_build_and_run`, so `reproduce` calls
  `verify_preserved` on the success path and in an `except BaseException`
  handler before re-raising;
* two regressions: `test_the_driver_detects_a_modified_supplied_input` and
  `test_preservation_is_checked_when_a_native_command_fails`.

This is **detection, not prevention**, and the code says so. Preventing a
write would mean copying multi-gigabyte wavefunctions or relying on filesystem
permissions the driver does not own. What is established is that nothing was
modified on a given run.

## 3. Head-pinned replay evidence

Both required paths were executed at this head and the logs committed under
`bgw/m2_screening/evidence/`.

`full-proof-replay.log` — `run_m2.py --full --proof` against
`/tmp/bgw/BerkeleyGW-4.0` and the pinned `WFN`/`WFNq`:

```
snapshotted 1980 supplied source files and 26 input files for a safety check
neutralized 102 escaping symlink(s), dropped 1 dangling   (x2)
supplied source (1980 files) and inputs (26 files) unchanged
epsmat identical in both builds (4512f63a4a9c28e8...)
complete dump validated: 3 block(s), run id as expected
reproduced q-block matches the committed snapshot byte for byte
GW/BGW/M2Screening.lean elaborated (exit 0)
```

`proof-corruption.log` — the case `--proof` exists for. The tactic of
`total_error_bound` was replaced by `norm_num [rowAbsSum]` with **every
literal unchanged**:

```
check_lean_literals.py        Lean literals match this export ... EXIT=0
run_m2.py --proof             GW/BGW/M2Screening.lean did not elaborate  EXIT=1
```

Literal checking passes and the completion path still fails closed. The file
was restored from backup immediately afterwards.

## 4. The backwards implication

An R1 comment (Lean module, and `BGW-M2-R1.md` §"B") said the total bound is
not implied by the components. That is backwards. `b_total = b_inv + b_shift`,
so the triangle inequality gives the total from the components. What fails is
the converse: the total establishes neither component, which is why
`inv_error_bound` and `shift_error_bound` are proved separately. The comment on
`total_error_bound` now says this; the theorem is kept as a direct finite
endpoint, not as an independent fact.

## 5. PR #17 description

The live description still asserted that differing from `V⁻¹(1 − E_hat)` rules
circularity out, while the provenance and handoff had retracted it. The body is
now corrected and marked, so the accounts no longer contradict each other.

## Commands and results

```
python3 -m pytest tests/test_bgw_m2.py            46 passed  (was 43)
python3 bgw/m2_screening/acceptance_regressions.py (review's, verbatim)  7 OK
python3 bgw/m2_screening/run_m2.py --full --proof  exit 0
python3 scripts/verify.py --gate all               exit 0
```

Gate: **443 scientific + 14 workflow**, **260 named / 698 exhaustive** audits.
`artifacts/verification.json` records each step's command and exit code.

## What is still not established

Unchanged from M2: IEEE-754, gfortran, LAPACK, BerkeleyGW as a program, the
HDF5/IO path, the origin of `chi` from wavefunctions, the frequency
convolution, self-consistency, and physical accuracy. Instrumentation
neutrality is empirical for this input only. The driver detects input
modification; it does not prevent it.

## Recommended next decision

Accept or reject the M2 package. If accepted, the next contract is the χ
transition-sum provenance for one nontrivial entry. The point worth writing
into that contract: BerkeleyGW's tutorial absorbs denominator weighting into
the effective `M` matrix, so exporting an already-weighted product and calling
it a derivation from physical operands would leave the same gap hidden.

No further milestone is authorized and none was started.

# BGW-M2 — from independently exported chi to a certified screening reference — ARCHIVED (2026-10-01): BGW-M1/M2 lineage, superseded by the kernel-checked eps^-1 certificates (GW.Endpoint.Kernel, Data.Q*Check/E*Check); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Supports `GW/BGW/M2Screening.lean` and `tests/test_bgw_m2.py`. Nothing here is a
proof; the kernel-checked claims are the Lean theorems.

## The production event

Same run family as M1, deliberately: one physical interface carried upstream,
not a second example.

| Item | Value |
| --- | --- |
| Code | BerkeleyGW 4.0, `Epsilon/epsinv.f90`, static, serial, real flavor |
| Pristine `epsinv.f90` SHA-256 | `cb7c9fb326df1b437c0a043305789e60f793148233ed516420669d8e946998e1` |
| M2 instrumentation patch SHA-256 | `22c40b2f0a6c7e353b40848c79e141d91296aa50dc9adf3fc8a9c290667d0540` |
| Pristine executable SHA-256 | `28da125275865808ae976477e55c236c0533d3dc5532d8a6f11f26fa69351af0` |
| Instrumented executable SHA-256 | `0eaa08a942b36e11176143c8c3cf161aa9985f1f04caf6fa2c3614a7c950b66f` |
| `WFN` / `WFNq` SHA-256 | `f85a1534…` / `1138228a…` (as M1) |
| `epsilon_cutoff` | **1.5 Ry — unconverged for material properties, by design** |
| q | index 2, `(0, 0, 1/2)`, regular non-zero |
| Basis | complete retained, `nmtx = 8` |
| Run id | `m2-20260917-q2-cut15` |
| Threads | `OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=1`, both builds |
| Committed slice | `data/m2_dump_q2.txt`, SHA-256 `37ee0a30072845f8b36274a2fad518bf8e42f09edcdcaefe5b8aaf9540b0f6ba` |

## Pristine / instrumented comparison

Two **separate source trees, separate clean real-flavor builds, separate fresh
run directories**, identical input bytes and thread settings. The instrumented
tree differs from the pristine one only by `epsinv_m2_dump.patch`.

```
cmp /tmp/bgw/m2run-pristine/epsmat /tmp/bgw/m2run-instr/epsmat   -> identical
cmp .../eps0mat                    .../eps0mat                   -> identical
sha256(epsmat) = 83358b72a3032fe29dff567fc7258f5e9a6d9a19032e68b0e7ee416ff3dcbbcb
```

The **whole `epsmat` output file** is byte-identical between the two builds, so
all 64 entries of the retained inverse agree by construction — no decoder and no
partial diagonal check was needed. This is empirical instrumentation neutrality
**for this input and these settings**, not a theorem about every execution.

## What is exported, and why it is not circular

At the point of use in the static branch, the source computes

```fortran
eps(irowm,icolm) = ZERO
if (i.eq.j) eps(irowm,icolm) = ONE
chitmp = pol%chi(irowm,icolm,1)
eps(irowm,icolm) = eps(irowm,icolm) - vc*chitmp      ! vc = vcoul(i)
```

The inspected routine **reads and does not write** `pol%chi`, so the exported
`CHI` records are the operands the formation consumed.

> **Corrected in BGW-M2-R1.** This section previously argued that because the
> exported `chi` differs from `V⁻¹(1 − E_hat)`, circularity was ruled out. That
> inference is **invalid**. The acceptance review constructed
> `round64(V⁻¹(1 − E_hat))`, which is answer-derived by construction yet
> differs from the exact rational recovery, differs from the exported `chi` in
> **10 of 64** entries, and satisfies the numerical decision rule. Independence
> is a property of acquisition and data flow; no comparison of matrix values
> can establish it. What supports it here is the inspected source
> correspondence, the fixed input/output digests, and byte-identical replay.
> `tests/test_bgw_m2.py::AcceptanceRegressions` keeps the counterexample so the
> bad argument cannot return. Note also that the "reads and does not write"
> statement covers the **inspected routine**; it is not a whole-program claim.

Exported per entry, each as a 17-digit decimal **and** raw IEEE-754 bits, with a
run identity on every block delimiter so records from two runs can never be
joined silently: `CHI`, `VCOUL`, `GVEC`, `EPSPRE` (stored `E_hat`), `EPSINV`
(production `X_hat`).

The newly exported `E_hat`, `X_hat` and `vcoul` are **identical** to M1's
represented matrices, which is what licenses reusing `GW.BGW.E`, `GW.BGW.Rref`
and M1's certificates for the stored problem.

## Traced floating-point path

Measured, not assumed:

* all **64/64** stored entries equal `fl(delta − fl(v·chi))` — two roundings;
* only **63/64** equal the fused `fl(delta − v·chi)`.

So the compiled path is *not* a contracted FMA, and one entry distinguishes the
two. The budget below is conservative for either path, so the certificate does
not depend on this determination.

## The three matrices

`E_star = 1 − V·chi` exactly (rational), `E_hat` stored, `Delta = E_hat − E_star`.

| Quantity | Value |
| --- | --- |
| `Delta` nonzero entries | **64 / 64** |
| `max |Delta|` (entrywise) | `1.505033517723375e-16` |
| `‖Delta‖∞` (row sum) | `2.396180681803995e-16` |
| `min |Delta|` | `3.179392763140503e-20` |
| `gamma2 = 2u/(1−2u)` | `1/4503599627370495` ≈ `2.2204460492503136e-16` |
| tightest `|Delta_ij| / B_ij` (entrywise) | `0.3945`, i.e. **2.53×** headroom |
| `b_form / ‖Delta‖∞` (row sum) | **4.73×** headroom |

`E_hat` and `E_star` are **not** equal and are never interchanged.

> **Corrected in BGW-M2-R1.** Two distinct quantities were previously conflated:
> the entrywise `max |Delta|` and the row-sum `‖Delta‖∞`. Both are reported
> above. Separately, "tight budget" applies **only to formation** — 2.53×
> entrywise, 4.73× in the row-sum norm. The **total** budget sits about
> **1420×** above the observed total error and is dominated by the engineering
> inversion allowance `b_inv`. That is not vacuous, but it is not a sharp
> physical error estimate either, and the constant 100 was not and must not be
> tuned after seeing this fixture.

## Frozen budgets

Fixed from inputs and certified references before any comparison, in
`reference.py`. The engineering constant 100 is **not** a proved LAPACK constant.

```
B_ij    = gamma2 * (|delta_ij| + |V_ii * chi_ij|)
b_form  = max_i sum_j B_ij                    (row-sum / infinity norm)
b_inv   = 100 * n * u * ||E_hat||_inf * ||R_hat||_inf^2
b_shift = ||R_hat||_inf * b_form * ||R_star||_inf
b_total = b_inv + b_shift
```

| Quantity | Value |
| --- | --- |
| `||E_hat||_inf` | `5.108402084990836` |
| `||R_hat||_inf` | `0.7529063510678852` |
| `||R_star||_inf` | `0.7529063510678852` |
| `b_form` | `1.1342931227599965e-15` |
| `b_inv` | `2.5719777753175876e-13` |
| `b_shift` | `6.429944438293971e-16` |
| `b_total` | `2.578407719755882e-13` |
| **measured** `||X_hat − R_star||_inf` (total) | **`1.8151131880718541e-16`** |
| measured `||X_hat − R_hat||_inf` (inversion) | `1.2883849931305328e-16` |
| measured `||R_hat − R_star||_inf` (shift) | `5.89524274501315e-17` |

All three components are now enforced separately, not only through the total.
The review showed a realizable binary64 candidate that met the total budget
while violating `b_inv`; `decides` and the Lean theorems `inv_error_bound` and
`shift_error_bound` now close that gap.

Both residual normalizations, kept separate rather than reconciled away, with
`r = ||E X − I||_inf`, `p = ||E||_inf ||X||_inf`:

| Convention | Value |
| --- | --- |
| `r / p` | `7.008168410280357e-17` |
| `r / (p + 1)` | `5.562036787802374e-17` |

The second reproduces the earlier review's number exactly; the `+1` is the
identity right-hand side's norm.

## Reproduction

```bash
# snapshot only, no BerkeleyGW and NO kernel check
python3 bgw/m2_screening/run_m2.py

# the acceptance command: rebuild, A/B, snapshot replay AND the Lean proof
python3 bgw/m2_screening/run_m2.py --full --proof \
    --source /tmp/bgw/BerkeleyGW-4.0 \
    --inputs <dir holding WFN and WFNq>

# and the full scientific gate, which is the authoritative proof check
python3 scripts/verify.py --gate all
```

> **Corrected in BGW-M2-R1.** Three driver defects, all found by review:
>
> 1. **The driver could modify the supplied source tree.** It copied with
>    `symlinks=True` and then `shutil.copy` onto `flavor.mk`; a preserved
>    absolute symlink pointing back into the supplied tree made that copy
>    *follow* the link and overwrite the owner's file. `safe_copy_tree` now
>    materializes every symlink whose target escapes the copy, writes are
>    no-follow, and `reproduce` snapshots and re-checks every digest in the
>    supplied tree. A regression asserts the source is untouched.
> 2. **Full reproduction bypassed the strict parser.** It sliced the *first*
>    matching `QSTART`–`QEND` and hashed it, so an appended duplicate of the
>    target block was discarded before validation. The complete dump is now
>    parsed and its run identity checked, and a repeated target block is
>    refused, *before* any block is selected.
> 3. **Neither mode invoked Lean.** `check_lean_literals.py` compares literals
>    only. `--proof` now elaborates the module, and a successful driver run
>    without it is not a kernel check. The authoritative check remains
>    `scripts/verify.py --gate all`.

## Corrupted-certificate check

Adding **one** to the last digit of a single `Rstar` numerator makes
`Rstar_mul_Estar` fail:

```
/tmp/m2corrupt/Corrupt.lean:419:47: error: unsolved goals
case ... ⊢ False
EXIT=1
```

That file is namespaced `GW.BGW.M2Corrupt`, lives outside the repository, and
appears in neither `GW.lean`, `GW/Audit.lean` nor the exhaustive audit log.

### Proof-only corruption, literals unchanged

The numerator corruption above changes a literal, so `check_lean_literals.py`
would catch it on its own. The complementary case is a broken *proof* with
every literal intact: literal checking passes and only elaboration fails. That
is the case `--proof` exists for, and it is recorded in
`bgw/m2_screening/evidence/proof-corruption.log`.

## Corrected in BGW-M2-R2

Three findings from the second acceptance recheck, all reproduced here before
being repaired.

1. **The migrated inversion regression had stopped discriminating.** R1
   rebuilt the review's mutant as `R_hat[0][0] + 2 * b_inv`, whose total error
   `5.144427744414192e-13` also exceeds `b_total = 2.578407719755882e-13`. The
   total rule alone rejects it, so the test passed with the inversion guard
   deleted and therefore certified nothing about the repair it was migrated to
   protect. The review's construction is `b_inv + b_shift / 2`, rounded to
   binary64: inversion error `2.5753467640116286e-13 > b_inv =
   2.5719777753175876e-13` while the total `2.57537166543158e-13` stays inside
   `b_total`. That mutant is restored, the test asserts **both** halves, and
   `test_deleting_only_the_inversion_guard_breaks_that_regression` checks that
   a checker missing only the inversion comparison accepts it.
2. **Input preservation was incomplete.** R1 hashed `WFN`/`WFNq` before the
   run and never again, and placed the source comparison after the build loop,
   so a raised native command skipped it. The run directories link the
   wavefunctions straight at the supplied originals, so a write through those
   links reaches them; review demonstrated the driver returning 0 with a
   modified input. `verify_preserved` now re-checks every regular file in both
   the supplied source tree and the supplied inputs directory, on the success
   path **and** the failure path. This is **detection, not prevention**: the
   driver establishes that nothing was modified on a given run, it does not
   make modification impossible.
3. **Replay evidence was not head-pinned.** This document described the
   earlier native A/B paths. The repaired `--full --proof` path is now
   replayed at the repair head and its log retained under
   `bgw/m2_screening/evidence/`.

## Corrected in BGW-M2-R3

Two further preservation holes, both found by the second recheck and both
reproduced here before repair.

1. **A supplied input that is itself a symlink fell out of the baseline.**
   `need` dereferences, but `tree_digests` skipped every symlink, so with

   ```text
   inputs/WFN       -> ../data/WFN      (supplied)
   run-pristine/WFN -> inputs/WFN       (created by the driver)
   ```

   the real bytes of `data/WFN` were in no baseline; a write through the run
   directory reached them and `reproduce` returned `0`. `tree_digests` now
   dereferences by default, and an input path that *exists* but cannot be
   digested — a dangling link, a directory — is refused before the build
   rather than silently dropping out of the check. On the real fixture this
   widened the source baseline from **1980 to 2096 files**.
2. **The input comparison ignored additions.** The source comparison counted
   new keys; the input comparison iterated over the "before" map only, so a new
   `inputs/unexpected.dat` was reported as unchanged. `_differences` is now one
   rule — modified, removed and added — used for both trees.

The top-level docstring said `--full` "never writes inside TREE or DIR". That
overstated a detection-only contract and now reads: this driver issues no write
of its own there and its copies cannot reach back, but the run directories link
at the supplied wavefunctions, so what is established is that nothing changed on
this run — not that a write is impossible.

A third, non-blocking item: the guard-free checker used by the inversion
meta-check was a hand-maintained copy of `decides`, which could drift as rules
are added. It is now derived from `decides`' own syntax tree, with exactly the
`ref.inf_norm(ref.matsub(Xhat, Rh)) > binv` statement removed, and the
derivation fails loudly if that statement is not found exactly once.

A fourth correction is a claim, not code: an R1 comment said the total bound
is not implied by the components. That is backwards. Because
`b_total = b_inv + b_shift`, the triangle inequality gives
`||X_hat - R_star|| <= ||X_hat - R_hat|| + ||R_hat - R_star|| <= b_inv + b_shift`.
What fails is the converse — the total establishes neither component — which is
why `inv_error_bound` and `shift_error_bound` are proved separately. The direct
finite proof of `total_error_bound` is kept as an endpoint, not because it is
independent.

## What is NOT established

IEEE-754, gfortran, LAPACK, BerkeleyGW as a program, the IO/HDF5 path, the origin
of `chi` from wavefunctions, the frequency convolution `Sigma = i G W`,
self-consistency, physical or convergence accuracy. `X_hat` is the exact decoding
of a floating-point result, not an exact inverse. `WhatRef = R_hat · V` and
`Wstar = R_star · V` are **derived** transformations of exported data, not an
exported production `W`, and no production `W` was compared. Instrumentation
neutrality is empirical for this input only.

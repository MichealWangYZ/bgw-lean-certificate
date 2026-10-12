# BGW-M3-CHI — one chi block's transition-sum provenance

**Status: CHECKPOINT_READY. Not accepted by me.**

Base: `00c9db8` on `bgw-m2/rounding-aware` (PR #17, M2-R3). Branched from the
PR, not `main`, because `main` (`bbf6a6c`) has neither M1 nor M2 and this
stage reuses M2's extraction primitives and its certified run.

Active time: ~5 h 15 min of the 6 h I budgeted in `.agent/tasks/BGW-M3-CHI.md`.

The owner authorized this stage directly, without a reviewer brief. I wrote
`.agent/tasks/BGW-M3-CHI.md` and committed it **before** starting, so the
boundaries are reviewable against something written in advance. Every boundary
in it is my proposal, not a signed contract.

## Against the five endpoints I wrote down

| Endpoint (scope note §5) | Result |
| --- | --- |
| 1. Complete transition inventory, including skipped ones | 280 transitions, 0 skipped, 1792 summed columns; strict parser refuses a partial export |
| 2. Exact rational reconstruction + budget fixed before comparison | all 64 entries inside budget; worst `1.295017e-17` vs `5.756277e-15`, 444x headroom |
| 3. Lean module in the build and the exhaustive audit, no shortcuts | `GW/BGW/M3Chi.lean`, 12 theorems audited, only `propext`/`Classical.choice`/`Quot.sound` |
| 4. Pristine/instrumented A/B on the whole `epsmat` | identical, `4512f63a4a9c28e8…` |
| 5. Mutations rejected, control accepted | 7 mutations rejected; unmodified control accepted by the same rule |

Gate: **480 scientific + 14 workflow**, **273 named / 721 exhaustive** audits,
`AUDIT_MODULE GW.BGW.M3Chi` present, `scripts/verify.py --gate all` exit 0.

## The finding the stage exists for

`Epsilon/mtxel.f90:926`, BerkeleyGW's own comment:

```
! In the static case, we lump sqrt(eden) into the matrix elements gme.
```

with `pol%gme *= sqrt(-1D0*eden)` at :858 and
`chilocal = -fact * gmetempr . gmetempc^T` in `mtxelmultiply.f90`. The
denominator is inside `gme` before the matrix product, so an export taken
there is an already-weighted product. `GMERAW` is taken immediately before it,
and `eval`, `econd`, `occ_v`, `occ_c`, `kfact`, `fact` and the `indt`/`pht`
map are exported separately.

The reference never reads the exported `eden`; it recomputes
`(occ_v - occ_c)/(eval - econd)` exactly. A test corrupts every exported
`eden` and checks the reference does not move.

## What the run ties to

This run's `chi` q-block is **byte-identical to the committed M2 snapshot** up
to the run-id string, and its `epsmat` equals the M2 A/B pair's. So the
transitions here produce exactly the `chi` that M2 took as an input.

## The denominator's rounding path, measured

The exported `eden` is not `fl(occ_diff/(eval-econd))` with the difference
exact — that fits 211 of 280. It is `fl(occ_diff / fl(eval - econd))`, which
fits **280/280**. Same class of empirical determination as M2's
`fl(delta - fl(v*chi))`. It is a measurement for this compiler and these
operands, not a theorem about the compiled code.

## Lean encoding, and why it looks the way it does

All data is scaled to integers. The reason is measured, not stylistic: a
1792-term `Int` fold does not reduce in the kernel at all, while the same fold
over `Nat` checks in ~7 s because `Nat` literal arithmetic is GMP-accelerated.
Each signed sum is a pair of `Nat` sums. `posSum11_eq` and its three siblings
depend on **no axioms at all**.

Three mathlib linters (`unusedTactic`, `unreachableTactic`,
`unnecessarySeqFocus`) overflow the interpreter stack walking the generated
tactic trees. They are disabled in the generated file; they are style checks
and the kernel check is unaffected. `lake build` succeeds without any stack
flag once they are off.

`bgw/m3_chi/make_certificate.py` **emits** the module and `--check`
regenerates and compares. This is the first emitter in the repo — M1's and
M2's equivalents are checkers only — and it exists because nobody hand-writes
or hand-edits 3584 term literals.

Non-vacuity: +1 on one scaled term literal makes `negSum11_eq` fail, exit 1.

## The main remaining gap

**The unconditional Lean statement is against the exported-`eden`
reconstruction, not the unrounded-operand one.** Keeping `eden` as exported
keeps every factor dyadic, which is what makes the kernel arithmetic
tractable. `eden_faithful` separately certifies, over an integer table, that
all 280 exported denominators are the correctly rounded quotient of their own
operands. The operand-level composition is
`entry11_operand_budget` / `entry12_operand_budget`, which is **conditional**:
its hypothesis is the term-wise transfer of `eden_faithful`, stated and not
derived.

Closing it means restructuring the sum so `eden` enters as a variable and
proving a general term-wise transfer lemma. I did not do that. Until it is
done, the operand-level claim for all 64 entries is Python-checked only.

I am flagging this rather than letting the conditional theorem read as more
than it is: the M1 brief said plainly that a conditional lemma with its
numerical assumptions left unproved is not a certificate, and that applies to
`entry*_operand_budget`, not to `entry*_within_budget`.

## Other limitations

Two of 64 entries are certified in Lean; the rest are Python-checked. This run
has **no** skipped and no partially occupied transition, so the
forbidden-transition branch of `get_eden` is untested — the closest approach
is `|eval - econd| = 0.215` Ry and `|occ_v - occ_c| = 1`. Stated as a
limitation, not a proved absence. Unchanged from M2: no claim about
wavefunctions, the FFT, convergence, the frequency-dependent path, spinors,
the q → 0 limits, the compiler, the BLAS, or BerkeleyGW as a program.

## Commands

```
python3 -m pytest tests/test_bgw_m3.py            34 passed
python3 bgw/m3_chi/make_certificate.py --check    exit 0
lake build                                        exit 0
python3 scripts/verify.py --gate all              exit 0
```

Native replay: two clean builds of the pinned source (pristine, instrumented)
and two runs on the M2-pinned inputs; evidence in
`bgw/m3_chi/evidence/ab-neutrality.log`.

## Recommended next decision

Review this against the scope note, and rule on whether the conditional
operand-level composition has to be closed before the stage counts as
complete. If it does, that is a bounded follow-up: one general transfer lemma
plus a restructured sum. No further milestone is authorized and none was
started.

# BGW-M1 handoff — one matched-input production screening comparison

```
Status: CHECKPOINT_READY
```

Not self-acceptance. Nothing was pushed, `main` was not merged, no stack cleanup,
no upstream contact, no dependency or toolchain migration, no next milestone
started, no paid resource used.

## Headline

One real BerkeleyGW 4.0 static screening stage is now checked end to end: the
production pre-inversion dielectric matrix was exported exactly from the running
code, an independent exact-rational reference was computed from it alone, the
production floating-point inverse met numerical criteria fixed in advance, and
**Lean certifies with kernel arithmetic that the reference is the unique solution
of the screening equation for that same represented input.**

This closes the interface the C3/C4 review said kept staying open. It validates
one inversion/screening stage for one represented input — not the program.

## Base, result, versions, active time

* Base: `plan/bgw-m1-production-screening` at `b64e4a4`, on main `bbf6a6c`.
* Work branch `bgw-m1/production-screening`, isolated worktree, local commit only.
* Lean 4.19.0 / mathlib `v4.19.0`; fresh `scripts/bootstrap.sh` in this worktree
  (exit 0). One disclosed reused dependency cache: `~/.cache/mathlib`. No old
  project executable was used as evidence.
* BerkeleyGW 4.0, real flavor, serial; rebuilt from a pristine copy after
  patching (`make clean && make -j8 epsilon`, exit 0).
* **Active time ~24 min** (`05:39:19Z` → `06:03:02Z` = 23 min 43 s) of the
  4-hour allowance; access/data preflight ~25 min of its 45-minute cap.

  > **Correction (BGW-M1 review).** This originally read "~1 h 24 min", which
  > contradicts its own printed interval. The interval is right and the figure
  > was wrong — a subtraction error on my part, not a budget overrun or a
  > different set of timestamps. ~24 minutes is the whole run; the preflight
  > figure inside it was also overstated and is better read as ~5 minutes of
  > data search plus the dependency bootstrap.

## Preflight: the data existed after all

The C3/C4 review was right that "absence of a fixture in Git is a starting
condition". Found under the owner's existing authorized local state:

* real `epsmat`/`eps0mat` from prior epsilon runs in `artifacts/t002-*`, `t003-*`;
* **BerkeleyGW 4.0 source trees and built binaries** in `/tmp/bgw/`, including
  `Epsilon/epsinv.f90` and `Epsilon/epsilon.real.x`;
* the archived `WFN`/`WFNq` and the original `epsilon.inp`;
* working network access to the manual.

`artifacts/` is gitignored, which is why the reviewer saw no fixture.

All archived runs use `epsilon_cutoff 7.0`, giving `nmtx` 65/76/92 — too large
for an in-kernel certificate. Because a built binary was available I **re-ran**
the production code at smaller cutoffs and measured `nmtx`:

| cutoff (Ry) | q0 | q=(0,0,½) | q=(0,½,½) |
| --- | --- | --- | --- |
| 0.5 | 1 | 2 | 2 |
| 1.0 | 1 | 2 | 6 |
| **1.5** | 15 | **8** | 6 |
| 2.0 | 15 | 14 | 14 |

Selected **cutoff 1.5 Ry, q-index 2, `q = (0,0,½)`, `nmtx = 8`**: a regular
nonzero q (no head/wing limit), the **complete** retained basis, nontrivial
off-diagonal structure, small enough to certify. **Deliberately unconverged for
material properties** — this is a screening-stage check, not a materials result.

## Source conventions, read from the pinned code

`Epsilon/epsinv.f90` static branch:

```fortran
eps(irowm,icolm) = ZERO
if (i.eq.j) eps(irowm,icolm) = ONE
eps(irowm,icolm) = eps(irowm,icolm) - vc*chitmp     ! vc = vcoul(i)
```

**`E = I − V·chi`, `V` diagonal on the ROW index, unsymmetrized.** The file
header says "2. Inverts epsilon. 3. Writes the result", and inversion is in
place (`call X(invert_serial)(pol%nmtx, eps)`), so **`epsmat` stores the
inverse**. Read from source, not inferred from a filename. `no truncation` was
active, so there is no Coulomb-truncation convention to reconcile.

`vcoul` takes 2 distinct values over the 8 retained G-vectors, so **`E` is not
symmetric** — a transpose or one-sided permutation mistake is a real error here,
not an invisible symmetry. This matters for the mutation test to be meaningful.

Note the structural match to the C4.1 prototype: `GW.LL.dielectric` is
`1 - v * chi0`, and BerkeleyGW's convention is the same with `v = diag(vcoul)`.

## Input boundary

The **permitted narrower boundary**: actual pre-inversion `E` and Coulomb
diagonal `V` exported from the run, plus the run's post-inversion result.
Formation of `E` from `chi` is an **input** and is NOT verified.

`E` was **not** reverse-engineered from the output under test — it is dumped from
the live `eps` array immediately before the inversion call.

## Export and its independent validation

`bgw/m1_screening/epsinv_dump.patch` adds a read-only dump, `#ifndef CPLX`, that
alters no production arithmetic. Every value is written **twice**: 17-digit
decimal and the raw IEEE-754 bit pattern. `extract.py` requires them to agree
entrywise — **0 mismatches** over all entries.

The run's log, printed by **un-instrumented** pristine code, gives an independent
check. Dumped `EPSINV(1,1)`/`EPSINV(2,2)` equal the printed
`3.448293583556872E-001` exactly. Dumped `EPSPRE(1,1)=3.1043208107546962` agrees
with the printed `3.104320810754696E+000` to the 16 digits that format carries —
the log is the correctly rounded form of the dumped double. That is print
precision, not a discrepancy, and it is stated rather than glossed.

**Interpretation, precisely:** the rationals are the exact values OF THE STORED
DOUBLES. Not the unrounded physical dielectric matrix; forming `E` exactly from
rounded `chi` and `vcoul` is a different problem.

## Predeclared criteria, then the measurement

Fixed in `bgw/m1_screening/reference.py` from export precision, dimension and
measured **input** conditioning, before any difference was examined:

* `forward_rel_inf ≤ 100 · n · κ∞(E) · 2⁻⁵³`
* `normalized_residual ≤ 100 · n · 2⁻⁵³`

Measured `κ∞(E) = 3.8461` (well conditioned), so the limits are `3.416066e-13`
and `8.881784e-14`.

| Metric | Measured | Limit | |
| --- | --- | --- | --- |
| relative forward error (∞-norm) | `1.711215e-16` | `3.416066e-13` | **pass** |
| normalized residual (max-entry) | `8.757691e-17` | `8.881784e-14` | **pass** |
| entrywise max abs error | `9.627035e-17` | reported | |
| normalized residual (∞-norm, added in R1) | `7.008168e-17` | reported | |

> **Correction (BGW-M1 review).** Two labelling fixes. The residual criterion is
> a **max-entry engineering diagnostic**, not a universal proved LAPACK bound —
> both thresholds are input-dependent engineering rules, and the proved
> statements in this milestone are the Lean theorems, not these limits. And
> while the rules were written before the comparison, version history alone
> cannot establish that ordering to a third party and no contemporaneous
> external record exists; the rules are unchanged and were frozen before the
> R1 reproduction.

Production agrees with the exact reference to ~1e-16, about three orders inside
the predeclared limit. No threshold was widened after looking.

## Mutations

Each injected into the checked path; each rejected by the **same** criterion the
unmodified control passes. These are not "differs from an unrelated exact
solution" — the reference is recomputed for the mutated input, so the mutation
has to survive its own consistent comparison, and none does.

| Mutation | relative forward error |
| --- | --- |
| Coulomb prefactor doubled (`I−2Vχ`) | `3.156e-01` |
| one side transposed | `1.923e-01` |
| one-sided row permutation | `7.153e-01` |
| sign of `V·chi` flipped | `9.471e-01` |
| unmodified control | **accepted** |

Also rejected: an ordinary wrong coefficient, a broken decimal/bits round trip,
a duplicate entry, a missing entry.

## The Lean claim, exactly

`GW/BGW/M1Screening.lean`. General lemmas, arbitrary ring and index type:

```text
eq_of_left_inv   : L * E = 1 → E * Y = E * Z → Y = Z
unique_solution  : L * E = 1 → E * Rsol = V → E * Y = V → Y = Rsol
```

Concrete, on the encoded production data (`E`, `V`, `Rref` as exact rational
`8×8` literals):

```text
Rref_mul_E  : Rref * E = 1        -- kernel arithmetic on the exported matrix
E_mul_Rref  : E * Rref = 1
Rref_unique : E * Y = 1 → Y = Rref
E_mul_Wref  : E * Wref = V        -- Wref = Rref * V, the screened interaction
Wref_unique : E * W = V → W = Wref
```

So `Rref` is **the** inverse and `Wref` **the** screened interaction of the
represented input — the requested `L*E = I`, `E*R_ref = V` pattern, with the
uniqueness step carried by the general lemma. Two concrete products are checked;
the screening equation is derived, so no second large product is needed.

Compiles in **64 s**, exit 0. No `sorry`, `admit`, custom axiom, `native_decide`
or unsafe shortcut. All seven theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`.

**The certificate is tied to this data, not to some matrix.**
`tests/test_bgw_m1.py::LeanCertificateMatchesThisData` re-parses the rational
literals out of the Lean source and requires them to equal the dump-derived
exact values entrywise for `E`, `V` and `Rref`. Without that, a valid
certificate could be about an unrelated matrix and say nothing about the run.

## Commands and outcomes

```
bash scripts/bootstrap.sh                                   exit 0
cp -a <pristine> /tmp/bgw/m1-eps-instr; patch epsinv.f90
cp flavor_real.mk flavor.mk && make clean && make -j8 epsilon exit 0
<rundir>/epsilon.real.x  (cutoff 1.5)                       exit 0
lake env lean GW/BGW/M1Screening.lean                       exit 0, 64 s
python3 -m pytest tests/test_bgw_m1.py                      21 passed
python3 scripts/make_manifest.py bgw/.../PROVENANCE-R6.txt  3 refreshed
python3 scripts/verify.py --gate all                        exit 0
```

Gate: **384 scientific + 14 workflow** tests; **240 named / 657 exhaustive**
audits; `AUDIT_MODULE GW.BGW.M1Screening` present; axioms limited to the
existing allowlist. No existing theorem, fixture, target or GPP scope changed.

## Evidence paths

Committed: `GW/BGW/M1Screening.lean`, `bgw/m1_screening/{extract,reference}.py`,
`bgw/m1_screening/epsinv_dump.patch`, `bgw/m1_screening/PROVENANCE.md`,
`bgw/m1_screening/data/m1_eps_dump_q2.txt` (the selected q block, 138 lines),
`tests/test_bgw_m1.py`, and the wiring in `GW.lean`, `GW/Audit.lean`,
`scripts/gates.py`.

Not committed, deliberately: the 159 MB BerkeleyGW tree, the wavefunctions, the
full three-q dump and the gate logs. Reachable via `PROVENANCE.md`; a source
location is not permission to redistribute. Instrumented tree at
`/tmp/bgw/m1-eps-instr`, run at `/tmp/bgw/m1run-1.5` — both regenerable from the
recorded commands and **outside** the repository.

## Failed attempts

1. `make epsilon` in the copied tree failed with `Type mismatch ... REAL(8) to
   COMPLEX(8)`: the tree's leftover `.mod` files were from the complex build
   while `flavor.mk` said real. Fixed by `cp flavor_real.mk flavor.mk` and a
   clean rebuild. Worth recording — the error reads like a source bug.
2. First certificate attempt hit `maxHeartbeats`, then produced a partially
   reduced goal: `Fin.sum_univ_eight` expands the sum but leaves `![…] 2`
   unreduced, because a numeral index does not match `cons_val_zero/one`.
   Resolved with `Fin.sum_univ_succ` plus `Matrix.cons_val_succ`, validated on
   a fast 3×3 case before paying the 8×8 cost.
3. During that 3×3 validation my hand-written inverse was simply wrong and the
   tactic reported `False` — a useful confirmation that the tactic is not
   vacuous before trusting it on the real data.

## The main remaining gap

**The formation of `E` is still an input.** The preferred boundary — production
`chi0` and bare Coulomb `V`, with the epsilon-formation convention checked
separately — was not done. The instrumentation point for it is the same routine,
and `chi` is in scope there (`pol%chi`), so this is a small extension rather
than a new campaign.

Everything else remains open exactly as before: the frequency convolution
`Σ = i·G·W`, self-consistency, the origin of `chi0`, the physical accuracy of
this deliberately unconverged run, general bare-to-bold/skeleton theory, and the
conditional status of C3.1's moment interpretation. Neither original C3 nor C4
roadmap row becomes complete because BGW-M1 succeeded.

> **Correction (BGW-M1 review).** The recommendation below is too strong as
> written. Exact formation `E* = I − V̂·χ̂` from independently exported `χ̂` and
> `V̂` generally differs from the **stored** `Ê` because of rounding, and this
> milestone certifies `Ê⁻¹`, not `E*⁻¹`. A future BGW-M2 must export `χ`
> independently (not recover it from `E`, which `recover_chi` cannot do
> non-circularly), keep the `E*`/`Ê` distinction explicit, and certify either
> the represented reference or a concrete rounding/residual bound. It is not a
> simple exact-equality extension, and "certified end to end" must not be
> claimed before that distinction is handled. Also: the current `Wref` is
> derived from `Rref` and `V`; it has **not** been compared against an exported
> production `W`.

## One recommended next decision

**Extend the same certified path one stage upstream: export `pol%chi` and
`vcoul` and certify the epsilon formation `E = I − V·chi` on the same q and
basis.** It reuses this run, this instrumentation point, this extraction and this
certificate shape, so it is cheap; it converts the one remaining declared input
of this milestone into a checked step; and it would make the chain
`chi → E → E⁻¹ → W` certified end to end for one real represented input. That is
a materially stronger statement than adding a second q-point or a larger basis.

No push, merge, publication or next milestone is authorized. Reporting status
and stopping for review.

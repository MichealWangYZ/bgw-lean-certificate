# BGW-M3-CHI provenance — ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

One static-polarizability q block's `chi` entries, traced back to the
transitions that produced them.

## Run identity

| | |
| --- | --- |
| run id | `m3-20260919-q2-cut15` |
| q index | 2, q = (0, 0, 0.5), nonzero, away from the head/wing limits |
| basis | `nmtx = 8`, the complete retained basis at `epsilon_cutoff 1.5` |
| bands | 18 total, 4 occupied, 14 empty |
| k-points | `nrk = 5` in the irreducible BZ(q) |
| flavor | real, serial, `OMP_NUM_THREADS=1` |
| source | BerkeleyGW 4.0, `/tmp/bgw/BerkeleyGW-4.0`, `Epsilon/epsinv.f90` sha256 `cb7c9fb3…998e1` |
| inputs | `artifacts/t002-codex-final/pristine/{WFN,WFNq}` at the M2 pinned digests |

Committed slices:

| File | sha256 |
| --- | --- |
| `data/m3_dump_q2.txt` | `36ba3844d52c448c4ae6712372c46f627cc28f3c44dd97af7dad647a946b7fed` |
| `data/m3_chi_q2.txt` | `48b5f3f19b944d285820834af6e40e3fa063d958e24c996a04816da624776175` |

## Why the export point matters

BerkeleyGW does not accumulate `chi` from a matrix element and a denominator
separately. Traced in the pinned source:

```
Epsilon/mtxel.f90:926   ! In the static case, we lump sqrt(eden) into the
                        !   matrix elements gme.
Epsilon/mtxel.f90:918   eden = occ_diff / (eval - econd)   [static, else 0]
Epsilon/mtxel.f90:858   pol%gme *= sqrt(-1D0*eden)
Epsilon/mtxelmultiply.f90:64,95
                        negfact = -1D0*fact
                        chilocal = negfact * gmetempr . gmetempc^T
```

By the time the matrix product runs, the denominator is already inside `gme`.
Exporting `gme` there and calling the product a derivation from physical
operands would hide exactly the step this stage exists to check. The
instrumentation therefore takes `GMERAW` **immediately before** the
`sqrt(-eden)` multiply, and exports `eval`, `econd`, `occ_v`, `occ_c`,
`kfact`, `fact`, and the `indt`/`pht` symmetry map separately.

## The reconstruction

With `w = sqrt(-eden)` and `w^2 = -eden` exactly as reals,

    chi(i,j) = fact * sum over (transition, star) of
                 eden * gme(ind_i) * ph_i * gme(ind_j) * ph_j

which is rational in the exported operands — the irrational `w` never
appears. The production value is the same expression evaluated in binary64.

The reference uses `eden_exact = (occ_v - occ_c)/(eval - econd)` computed in
exact rationals. It never reads the exported `eden`, which is already a
derived product; a test corrupts every exported `eden` and checks the
reference is unchanged.

## Measured

| | |
| --- | --- |
| transitions | 280 (5 irk x 4 valence x 14 empty x 1 spin), 0 skipped |
| summed columns | 1792 (nst = 6, 2, 6, 6, 12) |
| entries reconstructed | all 64, every one inside its own budget |
| worst entry | (5,5), `|diff| = 1.295017e-17` against budget `5.756277e-15`, 444x headroom |
| A/B neutrality | pristine and instrumented `epsmat` identical, `4512f63a4a9c28e8…` |

The A/B `epsmat` is also byte-identical to the one M2 certified, and this
run's `chi` q-block is byte-identical to M2's committed snapshot up to the
run-id string. The transition data therefore belongs to precisely the `chi`
that M2 already took as an input.

### The denominator's rounding path, determined empirically

The exported `eden` is **not** `fl(occ_diff/(eval - econd))` with the
difference taken exactly: that fits only 211 of 280 transitions. It is
`fl(occ_diff / fl(eval - econd))` — the subtraction is its own rounding —
which fits **280/280**. This is a measurement for this compiler and these
operands, not a theorem about the compiled code. `ROUNDINGS_PER_TERM = 6`
charges both.

## The budget

Two parts, and they are different in kind.

**Production rounding** — `production_bound`, an estimate.

    B_prod(i,j) = |fact| * gamma_m * S_abs,
    gamma_m = m*u/(1-m*u),  u = 2^-53,
    m = 5 + (ntot-1) + 1,   ntot = 1792

`S_abs` is the sum of absolute magnitudes over every individual product, not
over the per-transition aggregates: cancellation inside a transition must not
shrink the allowance. This is a standard numerical-analysis bound assuming
correctly rounded IEEE-754 operations. It is not a statement about gfortran,
the BLAS, or the order the GEMM accumulates in.

> **Corrected in BGW-M3-R1.** The five roundings per term are
> `sqrt(-eden)` *twice*, `g_i * w`, `g_j * w`, and the product. The single
> rounded `w = fl(sqrt(-eden))` is formed once and multiplied into **both**
> weighted matrix elements, so each product carries `(1 + delta_w)^2` and the
> sqrt rounding counts twice. The original M3 budget charged it once and was
> short by one unit. `eden`'s own rounding is no longer charged here at all —
> it moved into the proved transfer term below, and charging it in both places
> would double count.

**Denominator transfer** — `transfer_bound`, and in Lean a *proved* bound.

    B_tran(i,j) = sum over transitions of |a_t| * |edenHat_t - dStar_t|

with `a_t = fact * qw_t`. The operand-level budget is `B_prod + B_tran`.

On this run the transfer part is small: for the tightest entry (5,5),
`B_prod = 5.753075e-15` against `B_tran = 1.567625e-18`. Every one of the 64
entries lies inside its own operand-level budget, and the tightest uses
`2.250e-03` of its allowance — 444x headroom. The budget is fixed from the
operation/error model and operand magnitudes; a test checks it does not move
when the exported `chi` is scaled.

## The Lean certificate

Two modules.

`GW/BGW/M3Transfer.lean` is hand-written and run-independent: the list
transfer inequality, the integer-witness-to-rational bridge `abs_sub_div_le`,
the sum plumbing, and the `Row`/`Scales` data model with `rowOK` and
`row_bound`.

`GW/BGW/M3Chi.lean` is generated by `bgw/m3_chi/make_certificate.py --emit`
and re-checkable with `--check`. Only the *operands* are generated literals.
Everything downstream is recomputed in Lean and compared against its witness.

The chain, for each of entries (1,1) and (1,2):

| Step | Obligation | How |
| --- | --- | --- |
| star map and matrix elements → `qw` | `products_correct` | `rfl` |
| `evZ, ecZ, ovZ, ocZ` → `dZ, oZ`, residual, `eUp` | `rows_ok11`, `rows_ok12` | `rfl` |
| rows are built from the same table | `rows11 = allTrans.map (toRow false)` | definitional |
| sum with the exported denominators | `chiRecon11_eq` | `recon_eval` + `int_sum_split` + `rfl` sums |
| production rounding | `entry11_within_budget` | `norm_num` |
| exported → operand-implied denominators | `transfer_bound11` | `table_transfer`, discharged from `rows_ok11` |
| **endpoint** | `entry11_endpoint` | triangle inequality |

`chiStar11` and `chiStar12` are **definitions over the operand table**, not
literals:

```lean
def chiStar11 : ℚ := (rows11.map (fun r => r.coefQ S * r.dStarQ S)).sum
```

so severing them from the encoded operands is not possible without failing
one of the obligations above.

Integer scaling throughout, for a measured reason: a 1792-term `Int` fold does
not reduce in the kernel at all, while the `Nat` forms check in seconds.

### What the Lean denominator claim is, and is not

`rowOK` and `row_bound` prove a **bound** on `|edenHat - dStar|`, which is what
the transfer needs. They are **not** a proof that `eden` is correctly rounded;
IEEE rounding is not formalized anywhere in this repository.

The separate empirical result — that the exported `eden` equals
`fl(occ_diff / fl(eval - econd))` on **280/280** transitions, while the
single-rounding model fits only 211/280 — is a Python check in
`tests/test_bgw_m3.py`, for this compiler and these operands only.

### Discriminating mutations

`bgw/m3_chi/mutate_certificate.py` alters one generated witness at a time,
leaves the raw exported operands untouched, and requires Lean to fail at a
**named** obligation. Log: `evidence/mutations.log`.

| Mutation | Obligations reported failing |
| --- | --- |
| one `qw1` product witness (dependent totals repaired) | `products_correct`, and nothing else |
| one `resid` residual witness | `rows_ok11`, `rows_ok12` |

The residual is a property of the transition, not of a target entry, so both
row lists fail — that is correct, not collateral. An earlier version renamed
the mutant's namespace and every declaration became unresolvable; that is a
build failure and proves nothing, so the rename was removed.

## The M3 to M2 linkage is executable

`bgw/m3_chi/link_m2.py` compares the committed M3 chi slice against the block
BGW-M2 consumed, normalising only the documented run-id token, and then
compares the decoded `chi`, `vcoul`, `Ehat`, `Xhat` and basis entry by entry.
It is exercised by the gate, with a negative control that perturbs one value.

## What is NOT established

The wavefunctions, the FFT, the plane-wave basis construction, the
occupations as physics, convergence or material accuracy, the
frequency-dependent path (`freq_dep != 0`), spinors, the q -> 0 head and wing
limits, self-consistency, GPP, the compiler, the BLAS, or BerkeleyGW as a
program.

This run exercises **no** skipped and no partially occupied transition — all
280 have nonzero `eden`, and the closest approach to either branch tolerance
is `|eval - econd| = 0.215` Ry and `|occ_v - occ_c| = 1`. The forbidden-
transition branch of `get_eden` is therefore untested here. That is a stated
limitation, not a proved absence.

Two of the 64 entries are certified in Lean; the other 62 are checked in
Python only.

## Reproduction

```bash
# from the committed slices, no BerkeleyGW needed
python3 -m pytest tests/test_bgw_m3.py
python3 bgw/m3_chi/make_certificate.py --check

# the authoritative check
python3 scripts/verify.py --gate all
```

The native replay applies `bgw/m3_chi/mtxel_m3_dump.patch` and
`bgw/m2_screening/epsinv_m2_dump.patch` to a copy of the pinned source, builds
the real flavor from clean, and runs pristine and instrumented on the same
inputs. Evidence is in `evidence/ab-neutrality.log`.

# BGW-M4-R1 provenance — ARCHIVED (2026-10-01): BGW-M4/M5 lineage, superseded by GW.Endpoint.Kernel.SigmaSpec and Data.S3*; kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Supports `GW/BGW/M4GPP.lean` and `tests/test_bgw_m4.py`. The kernel-checked
claims are the Lean theorems; everything below is source reading and
recorded execution.

## Run identity

Full hashes are in [`evidence/ab-neutrality.log`](evidence/ab-neutrality.log).

| Item | Value |
| --- | --- |
| Source | BerkeleyGW 4.0 archive, sha256 `1a85b03b…6a49` (the pin in `docs/BERKELEYGW_4.0_GPP.md`) |
| Build | real flavor, serial, `bgw/export/arch.mk` with the toolchain prefix changed; conda-forge gfortran 13.4.0, OpenBLAS 0.3.34, FFTW 3.3.11 |
| Threads | `OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=1` |
| Inputs | `artifacts/t002-codex-final/pristine/{WFN,WFNq,WFN_inner,RHO,VXC,sigma.inp}` at the M2-pinned digests; `bgw/m3_chi/data/epsilon.inp` |
| Instrumentation | `instrument_r1.py` (write statements only; `m4r1_instrument.patch` is its diff, and it removes 0 production lines) |
| Export | `data/m4r1_dump.dat.gz` (from `gzip -n -9`), 41 k records, every float as raw IEEE-754 bits |

### The screening file is the M2-certified one

The feasibility run's `/tmp` build, `epsmat`, and raw dump no longer exist, so
nothing from them is used here. `epsmat` was regenerated from the pinned
WFN/WFNq by the pristine `epsilon.real.x`. Its sha256 changes from run to run
because the header embeds the run date (`22-Sep-2026`; this is the only
varying field, and it occurs once). With that field set to `19-Sep-2026`, the
regenerated file hashes to exactly `4512f63a4a9c28e8…`, the M2-R2/M3 pin. The
certificate does not rest on file identity anyway: every consumed value is
checked against M2's committed `Xhat` bits (below).

Side note (corrected after independent audit): `bgw/m2_screening/PROVENANCE.md`
records `83358b72…` for the first M2 run (2026-09-16 CDT). Setting the date field
to `16-Sep-2026` reproduces exactly that digest, so every recorded M2/M3/M4
`epsmat` digest is the same file content with a different header date. An
earlier version of this note claimed otherwise after trying only 17-Sep; that
was wrong.

## The finite map T, as Sigma executes it

Sigma needs eps^-1 at each rq = k − k′. For a stored block nm it reads
`eps(:,:) = epsmpi%eps(:,:,nm)` (`sigma_main.f90`); `fixwings` then rescales
the G = 0 wings; `gmap` then maps consumer G vectors onto stored ones. In
`mtxel_cor.f90` (real GPP) the consumed operand is

```
epsggp(ig,igp) = ph(ig) * ph(igp) * eps(ind(ig), indigp),   igp = indinv(indigp)
```

| Piece | Source | Checked by `bridge.py`, for every record reading nm = 2 |
| --- | --- | --- |
| row index | `gmap_base`: `ind(ig)` = eps index of `S^-1 (G_rq + kg)` | label equals M2's basis label at that index **and** equals `S^-1(G+kg)`, recomputed with an integer inverse |
| column | `indinv` / `inv_igp_index` | `indigp` is the image of G′ under the same map |
| phase | `dphase = cos((G+kg)·tnp)`, required to be ±1 | the bits are exactly ±1, with the sign of the recomputed cosine; 33 of the 195 map entries are −1 |
| wing (`qlen² < avgcut`, q0flag false) | `fixwings.f90`: col G0 → `x*fact*oneoverq/(vcoul(1)*qlen)`; row G0 → `x*oneoverq*qlen/(8*PI_D)`; head unchanged | the consumed bits equal the binary64 re-evaluation of the formula from M2's `Xhat` bits and the exported operands |
| operand | — | `epstemp(ind(ig))` bits equal `Xhat[ind(ig), indigp]` (bulk), or its wing image |

Outcome: the M2 block is read in four q visits (irq 2–5, three k-points each),
and all 8448 surviving GPP records reading it pass. irq 2 has rq = (0,0,½),
the same q as M2's block, yet it reaches the block through symmetry 38 with
umklapp (0,0,1), not the identity. That explains the feasibility report's
"2/64 exact matches with sign flips" under identity labelling. It was never
evidence of a structural break.

## Target, frozen before any residual

**Rule** (`bridge.run`): among records reading nm = 2 that are off-diagonal,
took the real `sqrt` branch (`wtilde2 > 0`), have nonzero `Omega2` and
`I_epsggp`, and have a positive exact squared-pole reference, take the
lexicographically first source pair `(ind(ig), indigp)` in M2's basis order,
then the smallest runtime occurrence. No residual or budget is consulted.

**Result**: source pair (1,2), i.e. G = (0,0,−1), G′ = (0,0,0). It is a
column wing, `kappa ≈ 0.938`. Consumer (ig, igp) = (2,1) at irq 2,
occurrence 1913, band 1; phases +1, +1. 5016 records were eligible.

**Branch survival.** The export sits after every `cycle` of the real GPP
setup, at `wtilde_array(ig,my_igp) = wtilde`, so every exported record
survived. `survives` also checks the source predicates on the decoded values.

## Omega2 reconstruction

`wpeff.f90`, real flavor, q ≠ 0, nspin = 1:

```
fact = wpsq/nelec;  precalc_j = fact*vcoul(G)*(G+q)_j/coulfact
Omega2 = sum_i (G'+q)_i * sum_j bdot_ij * precalc_j * rho(G-G')
```

The reference evaluates this exactly from decoded primitive operands:
`wpsq`, `nelec`, `vcoul(G)`, `coulfact`, `bdot`, q, G, G′, and `rho(G−G′)`.
The exported `wpmtx` is used only as the measured value. Consistent with the
brief, the ground-state, FFT, and Coulomb-averaging provenance of those
operands, and of the wing operands `fact`, `oneoverq`, `vcoul(1)` and `qlen`,
is outside M4.

## Budgets

These are rounding-count models fixed from the operation trace before any
discrepancy was computed (`bridge.N_*`, pinned by a test):

| Budget | Formula | Count |
| --- | --- | --- |
| `B_Omega` | `gam(16) * |expression|` | 13 roundings on the longest term path, rounded up to 16 |
| `B_map` | `|ph ph| * gam(4) * |kappa * Xhat|` | fixwings: up to 4 roundings |
| `B_formation` | `gam(3) * |eps|` | ph·ph, ·eps, 0 − x |
| `B_M2` | `M2.bTotal` | M2's own Lean constant |
| `L_T` | `|ph ph kappa|` | the actual map factor, not assumed to be 1 |
| `B_div` | `u * |Ohat/Ihat|` | one division |
| `B_P` | the brief's composition | proved by `quotient_transfer` |

`gam(n) = n u / (1 − n u)` with `u = 2^-53`. This is a standard rounding
model, not a proof about the compiled code: the compiler, FMA contraction and
evaluation order are covered only because the bound does not depend on the
order and FMA can only remove roundings.

## Values (target)

| | measured | budget |
| --- | --- | --- |
| `|Ohat − OStar|` | 7.1e-15 | 1.1e-13 |
| `|Ihat − IStar|` | 1.5e-17 | 2.4e-13 (dominated by `kappa * M2.bTotal`) |
| `|Phat − Ohat/Ihat|` | 7.2e-15 | 9.8e-14 |
| `|Phat − PStar|` | 9.4e-14 | 3.0e-9 (composed) |

`wtilde2 ≈ 883.26`, `Omega2 ≈ −62.60`, `I_epsggp ≈ −0.0709`. `B_I` is far
below `|IStar|/2`.

## Regenerate

```bash
# data-only checks (no BerkeleyGW needed)
python3 bgw/m4_gpp/bridge.py
python3 bgw/m4_gpp/make_lean.py --check
python3 -m unittest tests.test_bgw_m4
source scripts/env.sh && python3 bgw/m4_gpp/mutate.py
# full replay: extract the pinned archive twice, configure arch.mk,
# python3 bgw/m4_gpp/instrument_r1.py <instr-tree>; make sigma in both;
# regenerate epsmat with the pristine epsilon.real.x; run both sigma.real.x
# in fresh directories and compare the six outputs; gzip -n -9 the dump.
```

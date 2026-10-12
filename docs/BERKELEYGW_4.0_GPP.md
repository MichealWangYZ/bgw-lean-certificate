# BerkeleyGW 4.0: immutable revision, GPP code path, and scalar-model mapping — ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

This document discharges the milestone proposed in
`.agent/handoffs/CODEX-ACCEPTANCE.md` ("record an immutable BerkeleyGW
revision, one relevant code path, and a small genuine export with its units,
weights, precision, occupancy, cutoffs, and checksum"). The revision, the code
path, the units, the weights, the occupancy handling, and the cutoffs are
recorded here. Only restricted exact-real branch algebra is formalized in
`GW/GPP/BerkeleyGWMap.lean`; units, weights, predicates, and cutoffs are not proved.

BerkeleyGW 4.0 was also built and run, and a genuine per-`(G,G')` kernel export
from a benchmark-validated run is included; see section 7. Section 8 states
exactly what that does and does not establish.

## 1. Immutable revision

| Item | Value |
| --- | --- |
| Distribution | `BerkeleyGW-4.0` source release |
| Retrieved | September 10, 2026, from the URL pinned by the Spack recipe |
| URL | `https://app.box.com/shared/static/22edl07muvhfnd900tnctsjjftbtcqc4.gz` |
| Tarball SHA-256 | `1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49` |
| Size | 80,715,740 bytes |

This is not a VCS commit. The official BerkeleyGW GitLab repository is not
publicly readable (an anonymous request redirects to `users/sign_in`), and no
public mirror of the source was found. The tarball is therefore identified
content-addressably by its SHA-256, and that checksum is **independently
corroborated**: the identical digest is published as the `version("4.0", ...)`
`sha256` in the Spack package recipe
[`spack_repo/builtin/packages/berkeleygw/package.py`](https://raw.githubusercontent.com/spack/spack-packages/develop/repos/spack_repo/builtin/packages/berkeleygw/package.py)
on `spack/spack-packages` (rechecked by Codex during acceptance).
A third party's published checksum matching a separately downloaded archive is
weaker than a signed tag, but it is a real, checkable pin rather than a
fabricated revision identifier.

### Files read, with digests

| File | SHA-256 | Lines |
| --- | --- | --- |
| `Sigma/mtxel_cor.f90` | `8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd` | 3968 |
| `Sigma/sigma_main.f90` | `075d882a2151be184ba70ad6aad4be2aeb34dd85ae439ff649e1d13be3731f2b` | 2597 |
| `Sigma/shiftenergy.f90` | `9b0e5d6562e700112d405b8ad22f243d6c32a0d38cb096bf8a6f5fcc0964f550` | 207 |
| `Sigma/inread.f90` | `92b766739cb2d4f18b1666fb4d0898a31daee2b92e70225984183f9ba30bc399` | 1144 |
| `Common/nrtype.f90` | `3ef33f7534d16cd10a1e72d31c6afbd540ea98a21796eed87f85ebae2352d77e` | 213 |

## 2. The one code path

`Sigma/mtxel_cor.f90`, `subroutine sigma_gpp_cpu` (lines 1685-1931), reached
from `sigma_gpp` (lines 1666-1681) when `sigma_gpp_algo == CPU_ALGO`, which is called
from `mtxel_cor` when `sig%freq_dep == 1` or `3` (GPP). The `sigma_gpp_openacc`
and `sigma_gpp_omp_target` variants are **not** covered.

Restriction: positive real modes in the real flavor (`SCALAR = real(DP)`).
Some locals remain complex; real flavor alone does NOT ensure a real pole.
Setup lines 779-801 can produce an imaginary mode under `invalid_gpp_mode = 1`.
Those modes, zero placeholders, and the complex flavor are outside S1's
physical interpretation. The normalized algebra below uses real quantities.

### Occupied branch (`flag_occ = .true.`), lines 1810-1848

```fortran
wtilde = wtilde_array(ig,my_igp)
wtilde2 = wtilde**2
Omega2 = wtilde2 * I_eps_array(ig,my_igp)

wdiff = wxt - wtilde

cden = wdiff
rden = cden * CONJG(cden)
rden = 1D0 / rden
delw = wtilde * CONJG(cden) * rden
delwr = delw*CONJG(delw)
wdiffr = wdiff*CONJG(wdiff)

if (wdiffr.gt.limittwo .and. delwr.lt.limitone) then
  sch = delw * I_eps_array(ig,my_igp)
  cden = wxt**2 - wtilde2
  rden = cden*CONJG(cden)
  rden = 1D0 / rden
  ssx = Omega2 * CONJG(cden) * rden
else if ( delwr .gt. TOL_Zero) then
  sch = 0.0d0
  cden = (4.0d0 * wtilde2 * (delw + 0.5D0 ))
  rden = cden*MYCONJG(cden)
  rden = 1D0 / rden
  ssx = -Omega2 * MYCONJG(cden) * rden * delw
else
  sch = 0.0d0
  ssx = 0.0d0
endif
```

### Unoccupied branch, lines 1879-1897

```fortran
wdiff = wxt - wtilde_array(ig,my_igp)
cden = wdiff
rden = cden * CONJG(cden)
rden = 1D0 / rden
delw = wtilde_array(ig,my_igp) * CONJG(cden) * rden
...
schtt = aqsntemp(ig,n1) * delw * I_eps_array(ig,my_igp)
if (wdiffr.gt.limittwo .and. delwr.lt.limitone) then
  scht = scht + schtt
endif
```

There is no screened-exchange term for an unoccupied state, and no near-pole
branch: if the generic test fails the contribution is simply dropped.

### Accumulation, lines 1854-1855 and 1908-1915

```fortran
ssx_array(iw) = ssx_array(iw) +       ssxt*MYCONJG(aqsmtemp(igp,n1))
sch_array(iw) = sch_array(iw) + 0.5D0*scht*MYCONJG(aqsmtemp(igp,n1))
...
asxtemp(iw) = asxtemp(iw) - ssx_array(iw) * occ * vcoul(igp)
achtemp(iw) = achtemp(iw) + sch_array(iw) * vcoul(igp)
```

Note the asymmetry: `occ` multiplies the screened-exchange accumulation only.

## 3. Mapping to `Specification.md`

For positive real modes at full occupation, with the common external factors
`aqsntemp(ig,n1) * MYCONJG(aqsmtemp(igp,n1)) * vcoul(igp)` divided out, the
correspondence is:

| Specification.md | BerkeleyGW 4.0 |
| --- | --- |
| normalized `A0` in S1 algebra (eV^2) | `Omega2 = wtilde2 * I_eps_array(ig,my_igp)`; not S2's full unitful `A` |
| `w` (pole energy) | `wtilde = wtilde_array(ig,my_igp)` |
| `x = E - eps` | `wxt = wx_array(iw) = e_lk + sig%dw*(iw-2) - e_n1kq` |
| `rawOccupied A x w` | `-occ*ssx + 0.5*sch` in the **generic** branch, at `occ = 1` |
| `occupiedTerm A x w` | `-occ*ssx` in the **near-pole** branch, at `occ = 1` |
| `emptyTerm A0 x w` | `0.5*sch` when the unoccupied generic predicate passes |
| `sigmaX` | the separate bare-exchange `ax`, not part of this kernel |

Because `Omega2 = wtilde^2 * I_eps`, the Coulomb-hole accumulation
`0.5 * delw * I_eps = 0.5 * I_eps * wtilde/(wxt-wtilde)` equals
`Omega2 / (2*wtilde*(wxt-wtilde))`, which is the `CH(E)` formula the source
itself states in its comment at lines 1711-1718 (attributed there to
Hybertsen & Louie Eqs. 34a/34b, p. 5397). The `SX(E)` formula in the same
comment is `Omega2/((E-E_n1)^2 - wtilde^2)`, i.e. `ssx`.

So the identity proved in `GW/GPP/PoleCancellation.lean` is, under this
mapping, the statement that the two exact-real expressions at `occ = 1` agree
away from both poles, before clamps or dropped-mode policies. S1's merged
function supplies a continuous extension. The transcribed near-pole formula
still divides by `x-w` internally: its totalized Lean value at `x=w` is NOT
that extension. No theorem here proves Fortran behavior at an exact pole.
This distinction is checked by `BGW4.exact_pole_transcription_not_extension`.
The algebra is formalized in `GW/GPP/BerkeleyGWMap.lean`:

| Theorem | Statement |
| --- | --- |
| `BGW4.occupiedGeneric_eq_rawOccupied` | generic branch = S1 `rawOccupied` |
| `BGW4.occupiedNearPole_eq_occupiedTerm` | near-pole branch = S1 `occupiedTerm` |
| `BGW4.emptyBranch_eq_emptyTerm` | unoccupied branch = S1 `emptyTerm` |
| `BGW4.branches_agree` | the source's two branches agree where both are defined |
| `BGW4.tendsto_occupiedGeneric` | punctured limit is `Omega2/(4*w^2)` |
| `BGW4.delwComment_eq` | the comment's `delw` is `1/(2*delw_code)` |
| `BGW4.commentFormula_eq_occupiedTerm` | the comment's formula still yields the merged value |
| `BGW4.branch_mismatch` | exact discrepancy when `occ /= 1` |
| `BGW4.branch_mismatch_nonzero_at_half_occupation` | a concrete `occ = 1/2` witness |

The transcription from Fortran to Lean is a **human reading of source text**.
It is evidence, not a kernel-checked fact. `bgw/kernel_transcript.f90` exists to
make that reading falsifiable by machine (section 6).

## 4. Units, weights, occupancy, cutoffs, precision

**Precision.** `DP = kind(1.0d0)`, i.e. binary64, throughout. `DPC` is the
corresponding complex kind. Note that in the real flavor `wtilde`, `delw`,
`wdiff` and `cden` are still declared `complex(DPC)` while `Omega2`, `wtilde2`,
`ssx` and `sch` are `SCALAR = real(DP)`; the assignments between them are
implicit complex-to-real narrowing in the source.

**Units.** The kernel works in **eV**, not Rydberg. `Sigma/input.f90` line 806
converts the mean-field eigenvalues on read:

```fortran
kp%el(:,:,:)=kp%el(:,:,:)*ryd
```

so `e_lk`, `e_n1kq`, `wxt` and `wtilde` are eV and `Omega2` is eV^2 (which is
what `Sigma/wpeff.f90` line 16 states for `wpmtx`). Consequently `ssx` and
`sch` are **dimensionless**: the energy dimension of the accumulated self-energy
is carried entirely by `vcoul(igp)`, which is in Rydberg, and the conversion to
eV happens in `Sigma/shiftenergy.f90` line 113, `fact = ryd / dble(ndeg(ii))`,
with `RYD = 13.60569253` eV (`Common/nrtype.f90` line 155). For **off-diagonal**
elements the `ryd` factor is applied earlier instead, in `Sigma/sigma_main.f90`
lines 1850-1862.

This was confirmed against the running code: the export in section 7 records
`e_lk = -2.552134028802625` for band 1 at k-point 1, which is the eV value
printed in `sigma_hp.log` (`Emf = -2.552134029`). The first exported pole is
approximately `17.168` eV; no experimental plasmon identification is needed.

Since `Specification.md` S2 also works in eV, the mapping into the
specification's coefficient is dimensionally clean:

```
A [eV^3] = ryd * neq/ndeg * aqsntemp * MYCONJG(aqsmtemp) * vcoul(igp) [Ry]
           * Omega2 [eV^2]
```

with `aqs` dimensionless, so `ryd * vcoul` is an energy in eV and `A` is eV^3,
exactly as S2 requires for covered fully occupied or unoccupied terms.
Do NOT absorb arbitrary `occ` into `A`: occupation multiplies only SX, not CH.
The export omits `aqs`, `neq`, and `ndeg`, so it does not instantiate this full
coefficient or certify a unitful finite self-energy sum.
The dimensional bookkeeping of `vcoul` and of the `aqs`
matrix elements themselves has not been audited beyond this consistency check.

**Weights.** Two multiply this kernel's output: the q-star degeneracy `neq(irq)`
(`sigma_main.f90` lines 1586-1587, diagonal; lines 1860-1861, off-diagonal) and the degeneracy average `1/ndeg(ii)`
(`shiftenergy.f90` line 113). Neither is modeled in `Specification.md`; they are
absorbed into `A`.

**Occupancy.** `mtxel_cor.f90` lines 1397-1411:

```fortran
flag_occ = (n1true<=(sig%nvband+sig%ncrit)) .and. ((sig%ncrit==0).or.(e_n1kq<=(sig%efermi+sig%tol)))
if (abs(e_n1kq-sig%efermi)<sig%tol) then
  occ = 0.5d0
else
  occ = 1.0d0
endif
if ( sig%do_smearing ) then
  occ = 0.5*(1-erf(en_fac))-en_fac/(2*sqrt(PI_D))*exp(-en_fac**2)
endif
```

`Specification.md` uses **binary** occupancy, and the mapping above is valid
only at `occ = 1`. This is a substantive restriction, not a formality: since the
source applies `occ` to `ssx` but not to `sch`, at `occ /= 1` the two branches
compute genuinely different numbers and the pole at `x = wtilde` stops being
removable. `BGW4.branch_mismatch` gives the exact difference

```
(1 - occ) * [ Omega2/(2*wtilde*(x+wtilde)) + Omega2/((x-wtilde)*(x+wtilde)) ]
```

which is unbounded as `x -> wtilde` when `occ != 1` and `Omega2 != 0`.
Metals, systems with `ncrit > 0`, and any
run with `do_smearing` therefore fall outside the current formal claim. This is
reported as a **scope limitation of our specification**, not as a defect in
BerkeleyGW: the near-pole branch there is explicitly a model for the case where
SX and CH cancel, and the half-occupied case may be intended to be handled by
`sig%tol` being small enough that it is never reached with `wdiffr <= gamma^2`.
That has not been checked and should not be assumed.

**Cutoffs and tolerances actually present in this path.**

| Name | Value | Source | Modeled? |
| --- | --- | --- | --- |
| `limittwo = sig%gamma**2` | `0.25` (gamma default `0.5` eV) | `inread.f90:151`, `mtxel_cor.f90:1699` | no |
| `limitone = 1/(4*TOL_Small)` | `2.5e5` | `mtxel_cor.f90:1698` | no |
| `TOL_Small` | `1.0d-6` | `nrtype.f90:161` | no |
| `TOL_Zero` | `1.0d-12` | `nrtype.f90:162` | no |
| `ssxcutoff = sig%sexcut*abs(I_eps)` | `sexcut` default `4.0` | `inread.f90:152`, `mtxel_cor.f90:1847-1848` | no |
| `wxt` clamped to `TOL_Zero` if `|wxt| < TOL_Zero` | | `mtxel_cor.f90:1746` | no |
| `abs(Omega2) < TOL_Small` -> skip mode | | `mtxel_cor.f90:748` | no |
| `wtilde2 < 0` -> `sig%invalid_gpp` policy | 5 cases | `mtxel_cor.f90:779-797` | no |

The last two are in the GPP *setup* loop, not in `sigma_gpp_cpu`, but they
determine which `(ig,igp)` modes reach it at all. `Specification.md`'s rejection
of nonpositive `w` is closest to the `wtilde2 < 0` policy, but it is a strict
rejection, whereas the source offers five configurable behaviours including
substituting a fixed 2 Ry mode. (That substitution, `wtilde = CMPLX(2d0*ryd, 0d0)`
at `mtxel_cor.f90:786`, is itself further confirmation of the eV convention:
the constant is written as `2*ryd` precisely because `wtilde` is stored in eV.)

## 5. A consequence worth recording

`sig%gamma` defaults to `0.5` eV, so `limittwo = 0.25`. For finite nonsingular
real inputs, `|wxt-wtilde| <= 0.5` rules out the generic branch, but the
near-pole branch also requires `delwr > TOL_Zero`. At `x=w`, the preceding
division itself is undefined. Subsequent clamps also matter.
The catastrophic cancellation in `Specification.md` S4 concerns the
*unprotected* split. The tested nonsingular near-pole cases here agree with
the merged value; that is not a universal floating-point stability guarantee
and the S4 figure is not evidence of a BerkeleyGW defect.

How often each branch fires is not a matter of speculation --- it was counted
in the occupied loop across a real run (section 7), not the unoccupied loop:

| Branch | Count | Share |
| --- | --- | --- |
| generic (raw split) | 11,845,337 | 98.54% |
| near-pole (merged) | 80,163 | 0.67% |
| `delwr <= TOL_Zero`, contribution dropped | 94,888 | 0.79% |
| `ssxcutoff` clamp fired | 44,937 | 0.37% |

The first three counts partition 12,020,388 occupied-loop evaluations. The
`ssxcutoff` count overlaps those branches; it is not a fourth disjoint branch.
The branch is used about eighty thousand times in this test. The theorem
relates exact-real expressions, not all those rounded outputs.

## 6. Measured cross-check of the transcription

`bgw/kernel_transcript.f90` is a standalone program that reuses the executable
statements quoted in section 2 under the positive-real restriction, with the
same declared types (`MYCONJG` is replaced by `CONJG` here), and with
everything else (G/G' loops, matrix elements, MPI, OpenMP) removed. It is
**not** BerkeleyGW and it does not read BerkeleyGW's input files; it exists so
that the hand transcription into Lean can be checked by machine rather than by
eye. `bgw/oracle.py` recomputes each row exactly over the rationals, using
`Fraction.from_float` on the SAME binary64 `wxt` the program used, so that
input rounding is not confused with evaluation error (the S4 discipline).

Setting `I_eps = 1`, `wtilde = 1` eV (hence `Omega2 = 1` eV^2), and scanning
`wxt = wtilde + offset` for `offset = 10^0 ... 10^-8`:

* the generic branch is taken only at `offset = 1`, and there its exact
  rational value equals the exact rational value of the merged form;
* the near-pole branch is taken for all 16 smaller offsets, as predicted by
  `limittwo = 0.25`;
* every binary64 output agrees with the exact merged value to at most
  `5.8e-17` absolute, at most 2.09 ulps using `math.ulp(output)`;
* at `offset = 1e-8` the program returns `0.24999999875000004`, against the
  proved extension value `Omega2/(4*wtilde^2) = 1/4`.

Regenerate with:

```bash
gfortran -O2 -o kt bgw/kernel_transcript.f90
./kt > kt.out
python3 bgw/oracle.py kt.out
```

The oracle exits nonzero if any generic-branch row disagrees exactly with the
merged form, or if the worst absolute error exceeds `1e-14`.

This is a numerical experiment on a compiled transcript. It is not a proved
floating-point bound, and it does not certify the compiler, the transcript, or
BerkeleyGW.

## 7. A genuine export from a running BerkeleyGW 4.0

BerkeleyGW 4.0 was built and run, and the exported records are in `bgw/export/`.

### 7.1 Build

Serial (no MPI, no ScaLAPACK, no HDF5, no OpenMP), real flavor, with a
user-space conda-forge toolchain: `gfortran 13`/`gcc`/`g++` from
`gfortran_linux-64`/`gxx_linux-64`, `openblas`, and `fftw` (`-DUSEFFTW3`).
The `arch.mk` used is copied verbatim to `bgw/export/arch.mk`. No source file
was modified for this build.

### 7.2 Validation against the shipped benchmarks

The `testsuite/Si-EPM` silicon EPM case was run end to end:
`epm2bgw.x` (WFN, WFNq, WFN_inner) -> `epsilon.real.x` -> `sigma.real.x` with
`sig_GPP.inp`. The input files are copied to `bgw/export/`.

The worker reported 13 selected numerical comparisons. The source actually has
24 assertions in the GPP sigma block, with tolerances `2e-5` and `1e-6`.
The supervisor's harness checks all 24 against the source test file; selected
values below are retained for readability:

| Benchmark (`Si.test`) | Expected | Obtained |
| --- | --- | --- |
| n2, k1 Initial Eigenvalue | 10.035862 | 10.035862116 |
| n2, k1 Exchange | -14.234668 | -14.234668287 |
| n2, k1 Screened Exchange | 9.582573 | 9.582572521 |
| n2, k1 Coulomb Hole | -6.836764 | -6.836764123 |
| n2, k1 CH + Static Remainder | -7.628986 | -7.628985948 |
| n2, k1 Linear QP Correction | 0.163878 | 0.163877748 |
| n2, k1 Znk | 0.803837 | 0.803836714 |
| n5, k2 Screened Exchange | 2.770033 | 2.770033468 |
| n5, k2 Coulomb Hole | -6.456372 | -6.456372293 |
| n5, k2 Linear QP Correction | 4.516284 | 4.516284091 |
| n1 x n1 k1 Screened Exchange | 12.367894 | 12.367894325 |
| n1 x n8 k1 Coulomb Hole | -0.000765 | -0.000765281 |
| n2 x n1 k1 (zero by symmetry) | 0.000000 | 0.000000000 |

Full output: `bgw/export/sigma_hp.log`. This validates the build; it is not a
validation of BerkeleyGW's physics, and the benchmark values are the project's
own regression targets, not experiment.

### 7.3 Instrumentation

The kernel does not export per-`(G,G')` quantities, so `Sigma/mtxel_cor.f90`
was patched to write them. The patch is `bgw/export/instrument.patch` and adds
**only** counters and `write` statements inside `sigma_gpp_cpu`; it changes no
expression, no branch condition, and no accumulation. After patching, the
pristine file was restored and its SHA-256 re-verified as
`8914dc00...5daf1dd`, unchanged.

Evidence that the instrumentation does not perturb the result: the instrumented
binary reproduces `sigma_hp.log` identically, so the table in 7.2 holds for the
instrumented run too.

### 7.4 What was exported

| File | Contents |
| --- | --- |
| `gpp_kernel_dump.dat` | first 64 eligible occupied-loop records: `iw = 2`, `my_igp = 1`, `ig <= 4`, after `sexcut` |
| `gpp_nearpole_dump.dat` | first 32 occupied near-pole records, before `sexcut` |
| `gpp_branch_counts.dat` | occupied-loop tallies across the run (section 5) |
| `sigma_hp.log` | the full high-precision self-energy output |
| `instrument.patch`, `arch.mk`, `*.in`, `*.inp` | build and input provenance |
| `SHA256SUMS` | digest of every file in the directory |

Each record holds `n1true, iw, igp, ig, occ, vcoul(igp), I_eps_array(ig,my_igp),
wtilde, wxt, Omega2, ssx, sch, e_lk, e_n1kq` in `es24.17` format, i.e. enough
digits to recover the binary64 value.

Weights, occupancy, cutoffs and precision for this export: `occ = 1` on every
record (no `ncrit`, no smearing --- `screening_semiconductor`); `neq` and `ndeg`
are outside the kernel and are not in the records; binary64 throughout;
`gpp_broadening` and `gpp_sexcutoff` at their defaults `0.5` and `4.0`;
`epsilon_cutoff 7.0` Ry; 18 bands; 3 k-points; 3 q-points.

### 7.5 Checking the export against the model

`bgw/verify_export.py` recomputes, exactly over the rationals from each
record's own binary64 inputs, an exact-real branch prediction, its `ssx` and
`sch`, and the `Specification.md` S1 closed form at `A = Omega2`, `x = wxt`,
`w = wtilde`. Results:

| Set | Records | Branch | max &#124;error&#124; vs `ssx` | vs `sch` | vs S1 closed form |
| --- | --- | --- | --- | --- | --- |
| `gpp_kernel_dump.dat` | 64 (16 with `Omega2 != 0`) | generic, and `zero` | 5.8e-16 | 1.2e-16 | 6.3e-16 |
| `gpp_nearpole_dump.dat` | 32 | near-pole | 2.5e-19 | 0 | 2.5e-19 |

The general set has 34 predicted generic records (16 nonzero, 18 zero) and
30 dropped zero records. Its 48 zero placeholders are checked as source
outputs but are NOT valid S1 inputs, since `w=0`. There are therefore **48
nontrivial S1 comparisons**, 16 general plus 32 near-pole, not 96.
The near-pole capture location independently identifies its branch. The
general dump has no recorded branch label; its predictions are not independent
observations of branch decisions. Exact-real predicates do not emulate IEEE
threshold rounding. The near-pole set is the important one: real evaluations, in
a real calculation, of the merged expression whose equality with the raw split
is the theorem in `GW/GPP/PoleCancellation.lean`, and they agree with
`occupiedTerm` to under `2.6e-19` absolute.

Reproduce with:

```bash
python3 bgw/verify_export.py bgw/export/gpp_kernel_dump.dat
python3 bgw/verify_export.py bgw/export/gpp_nearpole_dump.dat
```

Both reject missing coverage, malformed/nonfinite rows, changed occupation,
unsupported singularities, and output discrepancies above the empirical
`1e-10` absolute threshold. `Omega2` is checked against `wtilde^2*I_eps` with
relative-to-`max(1,abs(Omega2))` threshold `1e-12`.
`python3 bgw/verify_export.py --all` additionally verifies every saved checksum.
No saved record triggers `sexcut`; the checker distinguishes pre/post-clamp
capture stages and rejects clamped data from this S1 comparison.

### 7.6 What this export does and does not establish

It establishes small measured residuals on 48 nonzero modes from one
BerkeleyGW 4.0 Si-EPM calculation, plus zero outputs on 48 placeholders.
This is normalized local arithmetic, not a full material self-energy or a
certified rounding bound. All records are fully occupied; no unoccupied or
fractional-occupation export was tested.

It does not establish that the transcription is complete (96 records out of
~12 million evaluations, all with `occ = 1`, from one material, one flavor, one
algorithm, one build), that BerkeleyGW's GPP model is physically accurate, or
that the agreement tolerance has any physical meaning. No tolerance here is an
acceptance criterion for any theorem.

### 7.7 Regeneration and build traps

Saved-data checks need only Python and this repository. Regeneration needs
the checksummed archive, compatible compilers, OpenBLAS, FFTW, `make`, `cpp`,
and `patch`. The historical `arch.mk` has absolute toolchain paths; adapt
them in new build trees, not in the archived provenance file. Compiler/library
packages are not locked. This is not a hermetic or portable bitwise build.

1. Verify the archive digest above and extract it into two fresh trees.
2. Configure each tree's `arch.mk` using `bgw/export/arch.mk` as the serial,
   real-flavor template, with actual compiler/library paths.
3. Apply `bgw/export/instrument.patch` to the second tree's
   `Sigma/mtxel_cor.f90` using `patch --batch TARGET PATCHFILE`.
4. Run `make -C TREE real` for each clean tree. Do not reuse complex `.mod`
   files for a real build. For an existing real tree, the Sigma default make
   target works; `make -C Sigma sigma.real.x` is not a reliable rebuild target.
5. Run this harness from the repository, with absolute tree paths and a new
   output directory:

```bash
python3 bgw/reproduce.py --pristine /path/to/pristine-tree \
  --instrumented /path/to/instrumented-tree --output /path/to/new-run
```

It checks source/patch identity, generates three EPM wavefunctions, runs epsilon
and sigma twice, checks 24 GPP assertions per run, and compares logs/exports to
the saved evidence. The archived `WFN_co.in` writes `WFN_inner` directly;
do not rename a nonexistent `WFN_co`. Output directories must be fresh because
the instrumentation appends records. The harness tests existing binaries, not
their build provenance. Exact-byte comparison is deliberately strict for this
historical dataset, not a portable physics tolerance.

Supervisor reproduction also encountered a stale binary called
`epsilon.real.x` which expected complex wavefunctions, and a missing pristine
`sigma.real.x`. A disposable copy of the working real instrumented build was
used to recompile pristine `mtxel_cor.f90`. Restoring a source file with its
old timestamp can leave newer objects untouched; force recompilation or use a
clean tree. Executable names alone are not flavor evidence.

### 7.8 Observed fresh-run reproduction and its threading sensitivity

A fresh reproduction was run on 2026-09-10 with the harness above, using a
reviewed-pristine tree and the instrumented tree. Both builds regenerated the
three EPM wavefunctions, epsilon and sigma; all 24 upstream GPP assertions held
in each run, with a worst absolute error of `7.61e-7` against tolerances `2e-5`
and `1e-6`. `sigma_hp.log`, `gpp_branch_counts.dat` and both dumps came back
byte-identical to `bgw/export/`, and the pristine and instrumented
`sigma_hp.log` were byte-identical to each other. Report:
`artifacts/t002-claude-reproduction-2/report.json`.

Qualification: the reviewed-pristine tree is an incremental pristine `Sigma`
rebuild that reuses previously compiled real-flavor dependencies. It is not an
independent clean-toolchain build, and this reproduction does not certify the
compiler or libraries.

Two reproducibility limits were measured rather than assumed.

1. **Binary outputs carry a timestamp.** `WFN`, `WFNq`, `WFN_inner`, `RHO`,
   `VXC`, `eps0mat` and `epsmat` embed the run date and time in their headers;
   two runs of the same binary on the same input differ in exactly those bytes.
   Only the text outputs are therefore byte-compared.
2. **The mean-field step depends on BLAS threading.** With
   `OPENBLAS_NUM_THREADS=1` and `OMP_NUM_THREADS=1` the EPM diagonalization
   changes the generated wavefunctions. A basis change inside degenerate
   subspaces is a plausible explanation; physical equivalence of the changed
   off-diagonal outputs has not been established. The diagonal table and all 24 assertions
   are unchanged, but `sigma_hp.log` lines 111-113 --- the second, symmetrized
   off-diagonal block, which no upstream assertion covers --- change in the
   fourth decimal, and the exported kernel inputs shift by up to `2.5e-12`
   relative. The archived run used the host default threading, so
   `bgw/reproduce.py` inherits the ambient environment and exposes
   `--blas-threads` for deliberate experiments. A failing comparison is written
   to `report.json` with the differing line numbers and per-column deviations;
   `artifacts/t002-claude-reproduction-1thread/report.json` is a retained
   example.

In the reported rerun on this host, executing the instrumented
`sigma.real.x` on the archived `WFN_inner`/`eps0mat`/`epsmat` inputs reproduced
`sigma_hp.log` and all three exported records byte-for-byte. This isolates the
observed sensitivity to the upstream-generated inputs in that experiment; it
is not a general determinism or gauge-invariance proof.

Codex independently reran the full workflow with the inherited host threading:
`artifacts/t002-codex-reproduction/report.json`. All 24 assertions passed for
each build; the four saved text outputs were byte-identical. The accepted
scope retains that host-specific comparison and does not introduce a new
off-diagonal physics tolerance.

## 8. Boundary

Obtained: an immutable, checksummed, independently corroborated revision; one
fully identified code path; its units, weights, occupancy rules, tolerances and
cutoffs, documented by reading the source; a restricted kernel-checked algebraic
correspondence to `Specification.md` S1; a measured binary64 cross-check of the
transcription; and a genuine export from a benchmark-validated BerkeleyGW run,
including 32 records that exercise the merged branch.

Still out of scope, unchanged from `docs/SOURCE_MAP.md`: the complex flavor, the
GPU code paths, the full-frequency and COHSEX paths, the dielectric matrix
construction and `wpeff` (which produces `wpmtx`/`Omega2`), the static remainder
`achcor`, the quasiparticle root solve, roundoff bounds, and any claim about
physical accuracy. Partial occupation (`occ != 1`) remains outside the formal
claim, for the reason proved in `BGW4.branch_mismatch`, and the export contains
no `occ != 1` record with which to study it.

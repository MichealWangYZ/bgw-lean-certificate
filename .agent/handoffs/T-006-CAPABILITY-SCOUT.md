# T-006 Capability Scout: complex flavor, HDF5, and a metallic / band-touching witness

Status: `ready_for_review`
Date: 2026-09-13
Scope: scouting + timeboxed build attempt. No repo file other than this handoff was
written. No commit, no push, no install, no sudo, no network access.

## 0. Headline

Three claims, in decreasing order of confidence, all OBSERVED unless marked.

1. **The complex flavor and HDF5 are no longer blockers.** Three fresh BerkeleyGW 4.0
   trees were built from scratch today, each in about 2.5 minutes of serial `make`:
   complex/no-HDF5, **complex + HDF5**, and real/no-HDF5. All returned
   `MAKE_EXIT=0`. The complex+HDF5 build reproduces the upstream `Na_smearing`
   metal benchmark to every printed digit, and the fresh real build reproduces the
   upstream `Graphene` metal-screening benchmark to every printed digit.
   HDF5 required **no download and no install**: a serial HDF5 2.2.0 with Fortran
   bindings already exists on this machine in an unrelated user-space conda env.
2. **The premise recorded in `.agent/handoffs/T-003.md` and `STATE.md` -- that a
   self-consistent metallic/band-touching witness "needs the complex flavor and
   HDF5, a substantial campaign" -- is not the real blocker.** The real blockers are
   different and are stated precisely in section 5. In particular the testsuite
   already ships a **real-flavor, binary (non-HDF5), GPP, self-consistent DFT
   semimetal asset** (`testsuite/Graphene`, PARATEC graphene, 1.3 MB, in-tree) that
   T-003's search missed. I ran it today. It does **not** produce fractional
   occupation, for a reason that is now measured rather than assumed.
3. **What is actually missing is a new mean-field calculation**, not a flavor, not a
   library, and not a toolchain: a WFN whose `ifmax` varies across k-points (a real
   Fermi-surface crossing), together with an `RHO` file. No installed code on this
   machine can produce one. Details and cost in section 6.

Nothing here changes any Lean file, tolerance, fixture, provenance, or test.

## 1. How the existing real-flavor build was produced

Source of record: `docs/BERKELEYGW_4.0_GPP.md` sections 7.1 and 7.7, and
`bgw/export/arch.mk`.

- Serial. No MPI, no ScaLAPACK, no HDF5, no OpenMP. Real flavor.
- User-space conda-forge toolchain rooted at `/tmp/mm/root/envs/bgw`:
  `x86_64-conda-linux-gnu-gfortran` / `-gcc` / `-g++`, `openblas`, `fftw`
  (`-DUSEFFTW3`). System `cpp` is used as `FCPP`.
- `arch.mk` is copied verbatim to `bgw/export/arch.mk`; it hardcodes absolute
  toolchain paths under `/tmp/mm/root/envs/bgw`.
- Flavor selection: BerkeleyGW's own `Makefile` target `make real` does
  `cp flavor_real.mk flavor.mk && make all`. The file is
  `flavor_real.mk` (the repo does not ship `flavor_complex.mk`; the complex file is
  named **`flavor_cplx.mk`**).

**Toolchain drift, OBSERVED.** `docs/BERKELEYGW_4.0_GPP.md` 7.1 records "gfortran
13". The env today reports:

```
$ /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gfortran --version | head -1
GNU Fortran (conda-forge gcc 16.2.0-4) 16.2.0
$ /tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-gcc --version | head -1
x86_64-conda-linux-gnu-gcc (conda-forge gcc 16.2.0-4) 16.2.0
$ cpp --version | head -1
cpp (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
```

So the conda env was upgraded at some point after the archived build. Every build
in this report used gcc/gfortran **16.2.0**, not 13. Section 7.7 of the doc already
warns that compiler/library packages are not locked and that this is not a hermetic
build; this is a concrete instance of that. INFERRED, not tested: the archived
Si-EPM byte-exact reproduction in `bgw/reproduce.py` may no longer hold under
gfortran 16. I did **not** run `bgw/reproduce.py` and make no claim about it.

## 2. What changes for complex flavor

Exactly one preprocessor symbol, plus a flavored clean. OBSERVED from source:

```
$ cat /tmp/bgw/BerkeleyGW-4.0/flavor_cplx.mk
TYPEFLAG  = -DCPLX
$ cat /tmp/bgw/BerkeleyGW-4.0/flavor_real.mk
TYPEFLAG  =
```

`Common/common-rules.mk:49` folds `TYPEFLAG` into `CPPOPT`, and line 10 branches on
`ifeq ($(TYPEFLAG),-DCPLX)` to set the `.cplx.x` binary suffix. There is no extra
library dependency and no extra source. The only operational caution, already in
`docs/BERKELEYGW_4.0_GPP.md` 7.7 step 4, is that real and complex `.mod` files must
not be mixed; I avoided this entirely by building each flavor in its own fresh tree.

**Complex flavor does not require HDF5. HDF5 does not require complex flavor.**
They are orthogonal switches. The coupling in the prior handoffs came from the one
metal asset (`Na_smearing`) happening to need both, not from the build system.

## 3. HDF5 on this machine

### 3.1 What is absent

```
$ which h5fc h5pfc h5cc
(only /usr/bin/gcc matched; h5fc, h5pfc, h5cc: not found on PATH)
$ pkg-config --list-all | grep -i hdf5     -> no output (pkg-config itself absent)
$ ls /usr/include/hdf5*                    -> no such file
$ ls /usr/lib/x86_64-linux-gnu | grep -i hdf5 -> no output
$ ls /tmp/mm/root/envs/bgw/lib | grep -i hdf5 -> no output
```

So: no system HDF5, no HDF5 in the BerkeleyGW conda env, no `pkg-config`.

### 3.2 What is present

A full serial HDF5 **2.2.0** with Fortran bindings, in an unrelated user-space
mamba env belonging to another project:

```
~/<other-project>/mamba/envs/recon
  bin/h5fc, h5cc, h5dump, h5ls, ...
  include/hdf5.mod, include/mod/shared/hdf5.mod
  lib/libhdf5.so, libhdf5_fortran.so, libhdf5_hl.so, libhdf5_hl_fortran.so
```

`lib/libhdf5.settings` reports: `HDF5 Version: 2.2.0`, `Fortran: ON`,
`Parallel HDF5: OFF`, `Configured on: 2026-08-08`, Fortran compiler
`x86_64-conda-linux-gnu-gfortran` (conda-forge feedstock). Serial only, which is
fine: every build here is serial.

Two traps, both OBSERVED and both worked around without touching that env:

- `h5fc -show` fails: `pkg-config: not found`. The wrapper is unusable; the
  libraries are not.
- That env's `lib/libgfortran.so.5.0.0` is **truncated** (8388608 bytes exactly;
  `file` reports `missing section headers at 11586760`). Any link line containing
  `-L<recon>/lib` makes the linker prefer it and die:

```
$ x86_64-conda-linux-gnu-gfortran -I<recon>/include -o t t.f90 -L<recon>/lib -lhdf5_fortran -lhdf5 ...
/tmp/mm/root/envs/bgw/bin/x86_64-conda-linux-gnu-ld: error: <recon>/lib/libgfortran.so: file too short
collect2: error: ld returned 1 exit status
```

  Workaround: reference the four HDF5 shared objects by **absolute path** instead
  of `-L`/`-l`. That is not a fix to the other project's env (I changed nothing
  there), just a link-line that does not walk into it.

Minimal compatibility probe, OBSERVED to compile, link, and run:

```
$ x86_64-conda-linux-gnu-gfortran -I<recon>/include -o t t.f90 \
    <recon>/lib/libhdf5_fortran.so <recon>/lib/libhdf5.so -Wl,-rpath,<recon>/lib
$ ./t
 hdf5 ok           0
```

So the `hdf5.mod` (GFORTRAN module version 15) is readable by gfortran 16.2.0.
This was the single riskiest unknown and it is resolved empirically.

### 3.3 What HDF5 changes in the build

`Common/common-rules.mk:70-72` adds `$(HDF5INCLUDE)` to `FTNINC` when `-DHDF5` is
in `MATHFLAG`; link rules append `$(HDF5LIB)`. The `arch.mk` delta is four lines:

```
MATHFLAG     = -DUSEFFTW3 -DHDF5
HDF5_ROOT    = ~/<other-project>/mamba/envs/recon
HDF5INCLUDE  = $(HDF5_ROOT)/include
HDF5LIB      = $(HDF5_ROOT)/lib/libhdf5_hl_fortran.so $(HDF5_ROOT)/lib/libhdf5_fortran.so \
               $(HDF5_ROOT)/lib/libhdf5_hl.so $(HDF5_ROOT)/lib/libhdf5.so -Wl,-rpath,$(HDF5_ROOT)/lib
```

Note this points at another project's env. That is acceptable for a scouting
experiment and **not** acceptable as durable provenance: the path is outside this
project's control and contains a known-corrupt `libgfortran`. See section 7.

## 4. Build attempt: exact outcome

Three fresh disposable trees, each extracted from the checksummed archive
`/tmp/bgw/bgw40.tar.gz`. **No existing tree was touched**: verified afterwards with
`find /tmp/bgw/BerkeleyGW-4.0 /tmp/bgw/t003-instr /tmp/bgw/t004-instr -newermt '2026-09-13 16:30'`
-> empty, and their directory mtimes are still 2026-09-10. I read source and
testsuite files out of `/tmp/bgw/BerkeleyGW-4.0` read-only; I wrote nothing there.

| Tree | arch.mk | Target | Result | Wall |
| --- | --- | --- | --- | --- |
| `/tmp/bgw/t006-complex` | `bgw/export/arch.mk` verbatim | `make cplx` | `MAKE_EXIT=0` | ~2m18s |
| `/tmp/bgw/t006-complex-hdf5` | same + `-DHDF5` block above | `make cplx` | `MAKE_EXIT=0` | ~2m40s |
| `/tmp/bgw/t006-real` | `bgw/export/arch.mk` verbatim | `make real` | `MAKE_EXIT=0` | ~2m12s |

Each build was driven by a tiny script (`build_*.sh` in each tree's parent) that
sets `PATH=/tmp/mm/root/envs/bgw/bin:/usr/bin:/bin` and runs `make`. Logs:
`/tmp/bgw/t006-complex/build_cplx.log`, `/tmp/bgw/t006-complex-hdf5/build.log`,
`/tmp/bgw/t006-real/build.log`. Zero occurrences of `error:` in any log. 51 `.x`
binaries in the complex tree's `bin/`, including `epsilon.cplx.x` and
`sigma.cplx.x`; the HDF5 tree's `bin/` likewise; `epsilon.real.x`, `sigma.real.x`,
`epm2bgw.x` in the real tree.

Disk: 143 MB, 153 MB, 142 MB. All three trees are disposable and under `/tmp`.

### 4.1 Independent validation of the complex + HDF5 build

Ran the shipped `testsuite/Na_smearing` case end to end, serially (1 rank, not the
4 the test nominally asks for; the test's own `TestGroups` line lists `serial`).
Assets unpacked into a fresh `/tmp/bgw/t006-run-na`. Runtime: 71 s for sigma.

Every upstream `match` value in `Na_smearing.test` that I checked reproduced to all
printed digits:

| Quantity | Upstream expected | Obtained |
| --- | --- | --- |
| Occupation (epsilon + sigma) | .544637 | .544637 |
| Energy (eV) | 2.073520 | 2.073520 |
| q1 Head of Epsilon | 7.86116311401E+000 | 7.861163114015898E+000 |
| q1 Head of Epsilon Inverse | 1.28265044163E-001 | 1.282650441634741E-001 |
| q2 Head of Epsilon Inverse | 1.28262878329E-001 | 1.282628783293273E-001 |
| q3 Head of Epsilon | 2.36002569690E+000 | 2.360025696904269E+000 |
| q3 Head of Epsilon Inverse | 4.26502006162E-001 | 4.265020061628928E-001 |
| n4 k1 initial eigenvalue | -24.037817 | -24.037816 (n=4 row) / -24.037817 (n=3) |
| n4 k1 exchange | -37.908680 | -37.908680 |
| n4 k1 screened exchange | 11.402532 | 11.402532 |
| n4 k1 Coulomb hole | -4.285227 | -4.285227 |
| n4 k1 linear qp correction | -30.121010 | -30.121010 (n=3) / -30.121009 (n=4) |

The upstream test tolerance is 1e-10 for the epsilon heads and 2e-5 for sigma. This
is a genuine complex-flavor, HDF5, metal-with-smearing calculation, so it exercises
exactly the two capabilities that were previously declared missing.

### 4.2 Independent validation of the fresh real build

Ran the shipped `testsuite/Graphene` case (epsilon x2, then sigma with
`screening_metal`) in a fresh `/tmp/bgw/t006-run-graphene`. Runtime: under a minute
total. Upstream expected vs obtained, `sigma_hp_metal.log`, ik = 1:

| Quantity | Upstream expected | Obtained |
| --- | --- | --- |
| n4 Initial Eigenvalue | -3.573425 | -3.573424857 |
| n4 Exchange | -19.936399 | -19.936399363 |
| n4 Screened Exchange | 8.893858 | 8.893858147 |
| n4 Coulomb Hole | -5.143640 | -5.143639890 |
| n4 Linear QP Correction | -2.690917 | -2.690916593 |
| n5 Initial Eigenvalue | 1.648540 | 1.648539513 |
| n5 Exchange | -1.100480 | -1.100480182 |
| n5 Screened Exchange | 0.271765 | 0.271764537 |
| n5 Coulomb Hole | -1.601716 | -1.601716104 |
| n5 Linear QP Correction | 2.818883 | 2.818882835 |

This is a second, previously unused upstream benchmark for the real-flavor GPP
path, and the gfortran-16 build passes it.

## 5. What a metallic / band-touching GPP witness actually requires

This section is the substantive result. All source line numbers are BerkeleyGW 4.0.

### 5.1 The only two routes to `occ != 1` in the GPP kernel

`Sigma/mtxel_cor.f90:1397-1411` (and the identical blocks at 3462 and 3726):

```fortran
flag_occ = (n1true<=(sig%nvband+sig%ncrit)) &
  .and.((sig%ncrit==0).or. (e_n1kq<=(sig%efermi+sig%tol)))
if (abs(e_n1kq-sig%efermi)<sig%tol) then
  occ = 0.5d0 ! Fermi-Dirac distribution = 1/2 at Fermi level
else
  occ = 1.0d0
endif
if ( sig%do_smearing ) then
  ... occ = 0.5*(1-erf(en_fac))-en_fac/(2*sqrt(PI_D))*exp(-en_fac**2)
endif
```

- Route A, **smearing**: gives a genuinely continuous `occ`, and is the physically
  intended mechanism. It is hard-rejected outside full frequency:
  `Sigma/inread.f90:528-532` dies with
  `occ_broadening must be used with frequency_dependence = 2 and frequency_dependence_method = 2`.
  This is unchanged and confirms the T-003 finding. Full frequency does not use
  `sigma_gpp_cpu` at all, so route A is disjoint from the mapped GPP algebra.
- Route B, **exact Fermi-level degeneracy**: `occ = 0.5` iff some band energy sits
  within `sig%tol` of `sig%efermi`. `sig%tol = TOL_Degeneracy = 1.0d-6`
  (`Sigma/inread.f90:130`, `Common/nrtype.f90:163`), converted to eV at
  `inread.f90:501`. This is the only route that reaches the GPP branch, and it is
  what T-003 hit.

There is a third, weaker metallic effect: `ncrit > 0` changes `flag_occ`, i.e. which
terms take the occupied branch at all, without changing `occ` away from 1.0.

### 5.2 `ncrit` cannot be set by the user in 4.0

`grep -n 'ncrit' Sigma/inread.f90` shows `sig%ncrit=0` at line 157 and **no input
keyword that assigns it**. The warning strings mention `number_partial_occup`, but
there is no `elseif(trim(keyword).eq.'number_partial_occup')` branch. `ncrit` is
derived, in `Sigma/input.f90`:

- with smearing: `get_nband_ncrit(...)` at line 302;
- without smearing: `sig%ncrit = maxval(kp%ifmax) - minval(kp%ifmax)` at line 337.

So in GPP mode `ncrit > 0` **requires a WFN whose `ifmax` genuinely varies across
k-points**. That is the crux.

### 5.3 GPP additionally requires an `RHO` file

`Sigma/input.f90:872-875`:

```fortran
if(sig%freq_dep.eq.1) then
  call read_rho(wpg, gvec, kp, syms, crys, isrti, isrt, 'WFN_inner', ...)
```

So any GPP run needs `WFN_inner` (+ `.h5`), `vxc.dat`, **and** `RHO`. Full-frequency
runs do not. This is why the `Na_smearing` assets are insufficient for GPP: they
ship only `jdft.bgw.wfn.h5` and `jdft.bgw.vxc.dat`.

### 5.4 Measured status of every asset actually on this machine

I tested all of them today.

**(a) `testsuite/Graphene` -- PARATEC graphene. Self-consistent DFT, real flavor,
binary (no HDF5), GPP by default, fully offline, 1.3 MB in-tree.**
This is precisely the "real-flavor, non-HDF5 metallic or band-touching test asset"
that `.agent/handoffs/T-003.md` section 6 declared missing. It was missed because
`grep -rln 'screening_metal' testsuite/` matches only `Na_smearing`: the Graphene
test injects metal screening at run time with
`sed -e 's/\(screening_\).*/\1metal/' sigma_orig.inp > sigma.inp`.
The tarball `PARATEC_graphene.tar.xz` contains `WFN_co`, `WFN_fi`, `RHO`, `vxc.dat`
-- everything GPP needs.

OBSERVED outcome of running it with `screening_metal`:

```
 - Number of fully occupied valence bands: 4
 - Number of partially occ. conduction bands: 0
 Valence max    (unshifted grid) = -2.632903 eV
 Fermi  energy  (unshifted grid) = -1.153333 eV
 WARNING: Metal screening usually should have number_partial_occup > 0.
```

`ncrit = 0`, and the Fermi level is 1.48 eV away from the nearest band, so route B
never fires either. Every kernel record is `occ = 1`. **Reason:** the shipped
k-grids do not contain the Dirac point. `WFN_co` is the 5x5 grid used by
`sigma.inp` (k = 0, 0.2, 0.4); `WFN_fi` is a 16x16 grid (epsilon reports
"Number of k-points in the full BZ of WFN: 256"). K = (1/3, 1/3, 0) is on neither.
A graphene grid must have its in-plane divisions **divisible by 3** to sample the
band touching.

**(b) `testsuite/Na_smearing` -- jdftx sodium. Self-consistent DFT metal with real
partial occupations, complex flavor, HDF5, fully offline, 0.4 MB in-tree.**
Works perfectly in its shipped full-frequency configuration (section 4.1), where
`occ = 0.544637`. I then wrote a GPP variant (static epsilon, `frequency_dependence`
left at its default 1, `screening_metal`, no `occ_broadening`) and ran it. OBSERVED:

```
 WARNING: Metal screening usually should have number_partial_occup > 0.
 WARNING: Fractional number of electrons per unit cell (from ifmax).
 WARNING: Discrepancy between number of electron per unit cell from ifmax and from occupations.
ERROR: Cannot open file 'RHO' for reading: does not exist.
Program received signal SIGABRT: Process abort signal.
```

Two independent failures, both fatal for this purpose:
  - no `RHO` in the asset, so the GPP path in 5.3 cannot even start;
  - `ncrit = 0` anyway. jdftx wrote a single constant `ifmax` (it used smearing, so
    its occupations live in the occupations array, not in `ifmax`), so 5.2 gives
    `maxval - minval = 0`. Dropping smearing does not recover a metal here.

**(c) `MeanField/EPM/epm2bgw.x` -- the generator used for the archived Si witness.**
Structurally incapable of producing `ncrit > 0`. `MeanField/EPM/epm2bgw.f90:456`:

```fortran
ifmax(1:kPoints%numKPoints,1:nspin)=kPoints%numOccupiedBands
```

a single scalar for every k-point and spin. So route 5.2 is closed for EPM by
construction, permanently, for any material.

It is also far more limited in materials than `form_factors.dat` suggests.
`MeanField/EPM/atomPotentialMod.f90:33-53` is a `select case` over exactly
`"H"`, `"Si"`, `"Ga"`, `"As"`, `"El"`, with
`case default: stop 'Error: pseudopotential not coded for this element.'`.
`form_factors.dat` (which lists Sn, InSb, CdTe, ...) is **not read by `epm2bgw`**;
it feeds the separate `ff2vq.py`. I confirmed this the hard way: an `Sn` input ran
to `RC=0` and silently produced no files, because Fortran `stop` exits 0. So grey
tin / any other zero-gap EPM semimetal is not reachable without patching
`atomPotentialMod.f90`, which is out of scope and would not fix 5.2 anyway.

**(d) The `"El"` free-electron EPM case -- a partial, honest curiosity.**
It does work and it does produce a band-touching band structure, fully offline,
real flavor, with `RHO` and `vxc.dat`. OBSERVED, `wfn_rho_vxc_info.x` on a
Gamma-inclusive 2x2x2 run (`ifmax = 4` at all three k-points):

```
k-point 1 (Gamma): 0.000000  0.787373 x8  1.049831 x6  2.099662 x4   (Ry)
k-point 2:         0.196843 x2  0.721759 x6  1.246674 x6  1.771590 x5
k-point 3:         0.262458 x2  0.524915 x4  1.312289 x8  1.574746 x5
```

Band 4 and band 5 are **exactly degenerate at every k-point**, and the bands
overlap across k (VBM = 0.787373 Ry at Gamma > CBM = 0.524915 Ry at k3): a textbook
metal. But `ifmax` is still constant, so `ncrit = 0` (5.2), and BerkeleyGW's default
`efermi = (VBM+CBM)/2 = 0.656144` Ry coincides with no eigenvalue, so route B does
not fire either. One could force it with `fermi_level <VBM> / fermi_level_absolute`,
which lands E_F exactly on the Gamma manifold and would give real `occ = 0.5`
records -- but that Fermi level is a user choice, not an outcome of the calculation,
which is close to the same objection already recorded against the T-004 witness.
I did **not** run that; it is a proposal, not a result.

### 5.5 Bottom line on the witness

A **physically self-consistent** metallic or band-touching GPP witness requires,
concretely:

1. a mean-field code that writes per-k `ifmax` (any real DFT code does: QE's
   `pw2bgw`, PARATEC, ABINIT, jdftx without smearing);
2. run on a **metal or semimetal**, on a k-grid that actually samples the Fermi
   surface -- for graphene, in-plane divisions divisible by 3 so K is a grid point;
3. exporting `WFN`/`WFN_inner` (+`WFNq`), **`RHO`**, and `vxc.dat`;
4. then `sigma` with `screening_metal` (or `screening_graphene`) and
   `frequency_dependence 1`.

None of steps 1-3 is available on this machine. Checked: no `pw.x`, no `pw2bgw.x`,
no PARATEC, no jdftx, no ABINIT anywhere on PATH or in either conda env; the only
mean-field generator present is `epm2bgw.x`, which 5.4(c) rules out structurally.

**What would have to be obtained.** Either (i) a Quantum ESPRESSO (or jdftx)
installation plus a carbon pseudopotential, then a graphene SCF + NSCF on a 6x6x1
or 12x12x1 grid and `pw2bgw.x` export; or (ii) someone else's pre-made
graphene-on-a-3n-grid BGW asset. Both are **network-dependent**. Per the task's
hard constraint I stopped this thread rather than assume access. The specific
assets that would be needed, for the record, are: a conda-forge `qe` package (or
equivalent), and a C pseudopotential such as `C.UPF` from PseudoDojo /
SSSP / the QE pslibrary. I did not attempt any download and make no claim about
whether these are reachable.

**Run cost, once assets exist, INFERRED from today's measurements.** The shipped
graphene case (8 bands, 6 Ry cutoff, 5 sigma k-points) ran epsilon twice and sigma
once in under a minute serially. A 6x6x1 graphene grid with, say, 30 bands would be
maybe 1-2 orders of magnitude more: minutes to an hour serially, still trivially
affordable. The mean-field SCF/NSCF for graphene at that size is likewise minutes.
**The witness is cheap. Only the missing DFT code and pseudopotential are not.**

## 6. Effect on the three blocked items

- **"Any fully weighted change in Sigma, Z, or QP energy."** Not blocked by flavor
  or HDF5, and never was. The Graphene and Na benchmarks above already produce full
  weighted Sigma/Znk/Eqp tables. What is missing for a *weighted* statement about
  the `occ != 1` branch specifically is still the witness of section 5.5, because
  every record in every asset available today has `occ = 1`.
- **"The self-consistent metallic witness."** Reclassified: blocked on a mean-field
  calculation, not on a build. See 5.5.
- **"q-star symmetry with outer factors."** I did **not** investigate this. I note
  only that `docs/BERKELEYGW_4.0_GPP.md` 7.4 records `neq` and `ndeg` as living
  outside the kernel, and that nothing I saw suggests complex flavor is needed for
  it. That is an impression, not a finding; treat it as untested.

## 7. Recommended next step, with cost

**Recommended: do not start a DFT campaign. Do this instead, in one bounded task.**

Take the free-electron EPM route from 5.4(d) and use it as an *honest, clearly
labelled, non-self-consistent* band-touching probe, because it is the only route
that is 100% offline, real-flavor, GPP, and reaches `occ = 0.5` through a genuine
band degeneracy rather than a manual energy shift. Concretely: `epm2bgw.x` with
`ChemicalSpeciesLabel 1 1 El` on a Gamma-inclusive grid, then epsilon, then sigma
with `screening_metal` and `fermi_level` pinned to the Gamma degenerate manifold,
with `bgw/export/instrument.patch` applied to count and dump `occ = 0.5` records.
Cost: roughly 1-2 hours, entirely on this machine, no downloads, no installs. The
deliverable is a measured count of `occ = 0.5` GPP records arising from an actual
degenerate band structure, plus their weighted contribution.

**Its honest limitation, which must be stated in any such handoff:** jellium is not
a material, the Fermi level is pinned by hand, and this is still not a
charge-self-consistent witness. It is strictly better than the T-004 manually
shifted configuration (the band degeneracy is real and symmetry-protected rather
than manufactured) and strictly worse than a real graphene-at-K run.

**If instead a genuinely self-consistent witness is wanted**, the decision the owner
has to make is whether to authorize network access for a Quantum ESPRESSO install
plus a carbon pseudopotential. Cost estimate, INFERRED: ~1 GB of downloads, then
half a day of work, then minutes of compute. I did not attempt it.

**Do not** promote the HDF5 configuration in section 3.3 to durable provenance as
written. It points into `~/<other-project>/mamba/envs/recon`,
which this project does not own and which contains a corrupt `libgfortran.so.5.0.0`.
If HDF5 is ever needed durably, HDF5 should be installed into the project's own
`/tmp/mm/root/envs/bgw` env (a download) or the recon env's HDF5 copied into a
project-controlled prefix (no download, but a provenance decision).

## 8. Artifacts, all disposable, all under /tmp

```
/tmp/bgw/t006-complex/          complex, no HDF5      MAKE_EXIT=0
/tmp/bgw/t006-complex-hdf5/     complex + HDF5        MAKE_EXIT=0
/tmp/bgw/t006-real/             real, no HDF5         MAKE_EXIT=0
/tmp/bgw/t006-run-na/           Na_smearing reproduction (FF) + failed GPP variant
/tmp/bgw/t006-run-graphene/     Graphene metal-screening reproduction (GPP)
/tmp/bgw/t006-run-sn/           EPM Sn (failed, unsupported element) and El (free electron)
/tmp/bgw/t006-scratch/          HDF5 Fortran compatibility probe
```

Nothing was written to `bgw/`, to any existing `/tmp/bgw` tree, to `.agent/STATE.md`,
to `.agent/handoffs/CODEX-T-003-T-004-ACCEPTANCE.md`, to any Lean file, fixture,
provenance file, tolerance, or test. The only repository file created is this one.

## 9. Honesty ledger

- OBSERVED: all three `MAKE_EXIT=0` values, all benchmark numbers in 4.1 and 4.2,
  all error text in 3.2 and 5.4(b), the free-electron eigenvalue table in 5.4(d),
  every source line quoted in section 5, the absence of HDF5 in 3.1, the toolchain
  versions in section 1.
- INFERRED, flagged as such in text: that gfortran 16 may break the archived
  byte-exact Si-EPM reproduction (untested); the run-cost estimates in 5.5; the
  remark about q-star symmetry in section 6.
- NOT DONE: `bgw/reproduce.py`; any download; any install; any MPI build; any
  run of the proposed free-electron witness; any investigation of q-star outer
  factors; any parallel (4-rank) execution of the testsuite cases.

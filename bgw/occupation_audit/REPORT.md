# T-003: can nonbinary occupation reach the GPP near-pole branch? — ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md.

Scope: BerkeleyGW 4.0, archive SHA-256 `1a85b03b...`, `Sigma/mtxel_cor.f90`
(`8914dc00...`), `subroutine sigma_gpp_cpu`, real flavor, CPU algorithm.
Provenance in `PROVENANCE.txt`. This is a source audit plus one small executed
probe; it is not a bug report against BerkeleyGW and changes no theorem.

## Answer, split three ways

The question has three different answers depending on which occupation
mechanism is meant. Conflating them is the main trap here.

| Occupation mechanism | Near-pole branch reachable? | Basis |
| --- | --- | --- |
| `occ = 0.5` from Fermi-level proximity (`mtxel_cor.f90:1399-1403`) | **Yes** | executed: 3,702 events in one Si run |
| `occ` from MP1 smearing (`mtxel_cor.f90:1405-1411`), range `[-0.0355, 1.0355]` | **No, excluded by input validation** | `inread.f90:528-532` dies unless `freq_dep==2 .and. freq_dep_method==2` |
| `occ = 0.5` reached without a manual Fermi level, from a self-consistent band structure | **Inconclusive; one deterministic case derived** | see section 4 |

## 1. The occupation variables and their actual constraints

```fortran
! Sigma/mtxel_cor.f90:1397-1411
flag_occ = (n1true<=(sig%nvband+sig%ncrit)) &
  .and.((sig%ncrit==0).or. (e_n1kq<=(sig%efermi+sig%tol)))
if (abs(e_n1kq-sig%efermi)<sig%tol) then
  occ = 0.5d0
else
  occ = 1.0d0
endif
if ( sig%do_smearing ) then
  occ = 0.5*(1-erf(en_fac))-en_fac/(2*sqrt(PI_D))*exp(-en_fac**2)
endif
```

They are **not** independent inputs:

* `sig%tol = TOL_Degeneracy` = `1e-6` Ry (`inread.f90:130`), then converted at
  `inread.f90:501` (`sig%tol = sig%tol * RYD`), so **`sig%tol = 1.3606e-5 eV`**.
* Energies in `mtxel_cor` are **eV**: `Sigma/input.f90:806` does
  `kp%el(:,:,:)=kp%el(:,:,:)*ryd` on read. `sig%efermi` is also eV
  (`Common/input_utils.f90` compares `efermi / ryd` against `kp%el`).
* `sig%efermi` comes from `find_efermi` (`Common/input_utils.f90:120-313`).
  With the default `rfermi = .true.` (`inread.f90:159`) and
  `efermi_input = 0`, `efermi = emiddle * ryd` where
  `emiddle = (maxval(vbm) + minval(cbm)) / 2`. With `fermi_level_absolute`
  (`inread.f90:425`) plus `fermi_level X` (`inread.f90:423`),
  `efermi = X` exactly, in eV.
* `sig%nvband` and `sig%ncrit` are *derived*, not free: when
  `number_valence_bands` is absent (`sig%nvband==0`), `Sigma/input.f90:336-337`
  sets `nvband = minval(kp%ifmax)` and `ncrit = maxval(kp%ifmax) - minval(kp%ifmax)`,
  so `ncrit > 0` requires a k-dependent occupied-band count, i.e. a metal.
* `sig%do_smearing` has **no direct keyword**: it is switched on as a side
  effect of `occ_broadening` (`inread.f90:314-316`). There is also no
  `smearing_type` keyword in `Sigma/inread.f90`, so `smearing_type` is always
  `1` (MP1) there (`inread.f90:139`).
* `wxt = e_lk + sig%dw*(iw-2) - e_n1kq` with `sig%dw = 1.0` eV default
  (`inread.f90:149`), clamped away from zero at `mtxel_cor.f90:1746`.
* `sig%gamma = 0.5` and `sig%sexcut = 4.0` (`inread.f90:151-152`).

### The MP1 occupation range is not [0, 1]

With `f(y) = 0.5*(1-erf(y)) - y/(2*sqrt(pi))*exp(-y^2)`,

```
f'(y) = exp(-y^2)/sqrt(pi) * (y^2 - 3/2)
```

so the extrema are at `y = -+sqrt(3/2)` and

```
range(f) = [ -0.03545790657010946 , 1.0354579065701095 ]
```

`f` exceeds 1 for `y < -0.8418822163923423` and is negative for
`y > 0.8418822163923416`. So under smearing the occupation can be **greater
than one and negative**, not merely fractional. Tested in
`tests/test_occupation_audit.py::SmearingRangeTests`.

These are the extrema of the **real** function. The decimal values quoted are
the binary64 evaluation of the formula at `y = -+sqrt(3/2)`; they are not a
claim that the floating-point implementation attains the exact real extremum,
and `erf`/`exp` accuracy is compiler- and libm-dependent. The qualitative
conclusion (the range is not contained in `[0, 1]`) is robust to that, since
the overshoot is `3.5e-2`, fourteen orders of magnitude above double rounding.
Note also that **this range is unreachable in the GPP path**, for the reason in
section 4; it matters only where smearing is permitted. This matters because
`occ` multiplies only the screened-exchange accumulation
(`mtxel_cor.f90:1908`), so `occ > 1` over-weights SX against CH.

## 2. The complete near-pole predicate

```fortran
! mtxel_cor.f90:1828-1843
if (wdiffr.gt.limittwo .and. delwr.lt.limitone) then      ! generic
else if ( delwr .gt. TOL_Zero) then                        ! near-pole
else                                                       ! dropped
```

with `limitone = 1/(4*TOL_Small) = 2.5e5` and `limittwo = sig%gamma**2 = 0.25`
(`mtxel_cor.f90:1698-1699`). The near-pole branch needs

```
( wdiffr <= limittwo  OR  delwr >= limitone )  AND  delwr > TOL_Zero
```

Failure of the generic test is **not** equivalent to `wdiffr <= limittwo`. In
the real flavor `delwr = wtilde^2 / wdiffr`, so the `limitone` clause opens a
second door: `wdiffr > limittwo` together with `delwr >= limitone` requires
`wtilde^2 >= limitone*wdiffr > 6.25e4`, i.e. `|wtilde| > 250` eV. Such modes
exist in principle, and the checker covers this case
(`BranchPredicateTests::test_nearpole_via_limitone_with_large_wdiffr`).

**The predicate in closed form.** Writing `d = |wxt - wtilde|` and using
`wdiffr = d^2`, `delwr = wtilde^2/d^2` (real flavor), the two generic tests are
`d > gamma` and `d > |wtilde|/sqrt(limitone)`. Since `sqrt(limitone) = 500`
exactly and `gamma = 0.5`,

```text
generic    <=>  d >  max(gamma, |wtilde|/500)
near-pole  <=>  d <= max(gamma, |wtilde|/500)   and   delwr > TOL_Zero
```

**`d <= 0.5` is therefore sufficient but NOT necessary** (review finding
`CODEX-T-003-R1-REVIEW.md` item 2). The `delwr` route dominates once
`|wtilde| > gamma*sqrt(limitone) = 250` eV. Codex's counterexample:
`wtilde = 1e12`, `wxt = wtilde + 1e6` gives `wdiffr = delwr = 1e12`, so the
first generic test passes while the second fails and branch 2 is selected at a
distance of `1e6` eV -- see
`artifacts/t003-r1-codex-review/sentinel-branch-counterexample.json`. That is
exact-rational algebra, not an executed material witness.

All 48 archived witness records sit in the `gamma`-dominated regime
(`wtilde` from `12.0926` to `14.0659` eV, far below the 250 eV crossover;
`d` from `0.0018` to `0.4954` eV), so every one of them was selected through
the `wdiffr` route.

**Exact-real prediction versus the decision the source actually made.** The
checker evaluates this predicate over exact rationals built from the *recorded*
(already rounded) inputs. The Fortran compared its own binary64 `wdiffr` and
`delwr`. For a record sitting close to a threshold the two routes could in
principle disagree, so the checker now classifies both ways -- once from the
rational recomputation and once from the recorded `wdiffr`/`delwr` -- and
reports `exact_and_recorded_branch_agree`. On all 48 archived records they
agree. That is an observation about these records, not a guarantee for every
record.

Upstream of the branch, `if (abs(Omega2).lt.TOL_Small) cycle`
(`mtxel_cor.f90:748`) drops weak modes in the GPP setup loop, and invalid modes
are redirected by a selectable policy, treated separately in section 2.1.

Downstream, the `sexcut` clamp (`mtxel_cor.f90:1847-1848`) can zero `ssx`
afterwards; it fired on **0** of the exported occ != 1 records, and the checker
now verifies that decision against its predicate rather than merely reporting it.

### 2.1 Invalid modes: the policy, per policy

**Correction (T-003-R1, review finding F3).** The first version of this report
and source deduction S9 of `.agent/handoffs/T-003.md` claimed that the default
policy maps an invalid mode to `wtilde = 0` and that invalid modes therefore
"go to branch 3, never to the near-pole branch". **Both halves are wrong.**

Every assignment to the policy variable in the pinned source:

* `Sigma/inread.f90:82` -- `sig%invalid_gpp_mode = -1` (the default);
* `Sigma/inread.f90:455-456` -- the optional `invalid_gpp_mode` keyword.

There is no other assignment. The dispatch at `mtxel_cor.f90:779-793` is:

| `sig%invalid_gpp_mode` | `wtilde` becomes | comment in source |
| --- | --- | --- |
| `0` | `(0d0,0d0)` | skip the mode, ignore its contribution |
| `1` | `sqrt(COMPLEXIFY(wtilde2))`, purely imaginary | "find" an imaginary mode |
| `2` | `CMPLX(2d0*ryd, 0d0)` = `27.21138506` eV | fixed mode frequency of 2 Ry |
| `3` | `CMPLX(1d0/TOL_ZERO, 0d0)` = `1e12` eV | static COHSEX for that mode |
| anything else, **including the default `-1`** | `CMPLX(1d0/TOL_ZERO, 0d0)` = `1e12` eV | `case default` |

So the default is the large positive sentinel, identical to case 3, **not**
zero. Near-pole reachability then differs by policy, and each statement below
carries its own domain assumption:

* **Default (`-1`) and case 3, `wtilde = 1e12` eV.** For `wxt` of ordinary
  band-structure magnitude (`|wxt|` up to, say, `1e3` eV, which covers every
  value in this project's evidence), the near-pole half-width of section 2 is
  `max(gamma, |wtilde|/500) = 2e9` eV, and `|wxt - wtilde| ~ 1e12` exceeds it,
  so the **generic** branch is taken. This remains an **asymptotic statement
  for ordinary `wxt`**, not a claim for every possible `wxt`.

  **Correction (T-004 item 1; review `CODEX-T-003-R1-REVIEW.md` item 1).** The
  T-003-R1 version of this bullet said `ssx -> 0` here and identified the
  result with the static COHSEX value. Both were wrong, for the same reason:
  the kernel **recomputes** `Omega2` from the sentinel at
  `mtxel_cor.f90:1810-1812`,

  ```fortran
  wtilde  = wtilde_array(ig,my_igp)
  wtilde2 = wtilde**2
  Omega2  = wtilde2 * I_eps_array(ig,my_igp)
  ```

  so `Omega2` grows as `wtilde^2` instead of staying fixed, and at fixed finite
  `x = wxt` and `ieps`

  ```text
  ssx      = w^2*ieps / (x^2 - w^2)  ->  -ieps            (NOT 0)
  sch/2    = w*ieps / (2*(x - w))    ->  -ieps/2
  -occ*ssx + sch/2                   ->  (occ - 1/2)*ieps
  ```

  The setup loop stores `I_eps_array` before the invalid-mode policy is applied
  and does not zero it when the sentinel is selected, so `ieps` survives into
  this limit. The `sexcut` clamp does not suppress it: at
  `w = 1e12, x = 10, ieps = -1/4, occ = 1` nothing is exactly `1/4` or `1/8`.
  The exact rationals at that finite `w` are

  ```text
  ssx   = 2500000000000000000000/9999999999999999999999   ~ +0.25
  sch/2 = 12500000000/99999999999                         ~ +0.12500000000125
  local = -12500000000/100000000001                       ~ -0.12499999999875
  ```

  and `-ieps = 1/4`, `-ieps/2 = 1/8`, `(occ-1/2)*ieps = -1/8` are the
  `w -> infinity` **limits**. An earlier revision called the decimals "the
  exact rational values"; that was wrong.

  **The finite value is not the limit, and it still depends on `x`.** At
  `w = 1e12` the local combination is

  ```text
  x = 1      ->  -125000000000/1000000000001  = -0.124999999999875
  x = 10     ->  -12500000000/100000000001    = -0.12499999999875
  x = 100    ->  -1250000000/10000000001      = -0.1249999999875
  x = 1000   ->  -125000000/1000000001        = -0.124999999875
  ```

  so it varies by about `1.1e-11` between `x = 10` and `x = 100`, and only
  approaches `-1/8` as `w -> infinity`. It never attains it. Calling the
  sentinel contribution "frequency-independent" is therefore shorthand for the
  limit, not a statement about the finite value; the `x` dependence is real but
  suppressed by roughly `x/w`.

  The `sexcut` clamp does not suppress the contribution either: its predicate
  requires `|ssx| > sig%sexcut*|ieps|` **and** `wxt < 0`, and at this point
  `|ssx| ~ 0.25` is not greater than `4*0.25 = 1`, while `wxt = 10 > 0`. So
  neither conjunct holds. Codex's exact evaluation:
  `artifacts/t003-r1-codex-review/sentinel-counterexample.json`.

  Such a mode is therefore neither dropped nor near-pole: it contributes a
  **finite** amount through the generic branch, with the common matrix-element
  and Coulomb factors stripped, which **approaches** `(occ - 1/2)*ieps` as
  `w -> infinity` without reaching it. "Static" in the source comment is read
  here only as that limiting, `x`-independent behaviour; the finite value
  retains the weak `x` dependence tabulated above.

  **No equality with `sigma_cohsex` is claimed, and the comparison does not
  apply to this witness.** The T-003-R1 text asserted such an equality and it
  does not hold. A T-003-R2 revision then compared the two kernels channel by
  channel; **that comparison was itself incomplete** (review finding 4) and is
  withdrawn here. The reason is that `sigma_cohsex` accumulates its Coulomb-hole
  channel only under a condition:

  ```fortran
  if (sig%exact_ch==0) then
    achtemp_loc = achtemp_loc + 0.5d0*aqsn_Ieps
  endif
  ...
  if (sig%exact_ch==0) then
    achtemp(2) = achtemp(2) + achtemp_loc*vcoul(igp)*MYCONJG(aqsmtemp(igp,n1))
  ```

  The witness of section 3 runs with `exact_static_ch 1`
  (`fixtures/fermi_sigma.inp`), i.e. `sig%exact_ch /= 0`, so in this
  configuration `sigma_cohsex` would contribute **no CH channel at all** and a
  two-channel comparison against it is not defined. Any such comparison must be
  conditioned on `sig%exact_ch == 0`, which no run in this project uses.

  What survives and is used: the sentinel limit is
  `(occ - 1/2)*ieps`, finite and frequency-independent. Nothing here identifies
  it with `sigma_cohsex`'s output, in either direction.

* **Case 0, `wtilde = 0`.** Then `delw = 0/wdiff = 0` exactly whenever
  `wdiff != 0`, so `delwr = 0` and `delwr > TOL_Zero` fails: the near-pole
  branch is **excluded**. Which of the other two branches is taken depends on
  the predicate, not on the policy: `wdiffr = wxt^2 > limittwo` gives the
  generic branch with `ssx = sch = 0`, and `wdiffr <= limittwo` gives the
  dropped branch. `wdiff = 0` cannot occur here because `wxt` is clamped away
  from zero at `mtxel_cor.f90:1746`.
* **Case 1, purely imaginary `wtilde`.** Outside the mapped real-mode scope of
  `Specification.md` and of `GW.GPP.BGW4`. `delw`/`delwr` are then complex
  quantities and `delwr` is a squared modulus; **no claim is made**. The checker
  rejects any record with a nonzero `wtilde_im`.
* **Case 2, `wtilde = 2 Ry = 27.21138506` eV.** An ordinary positive real mode.
  The near-pole branch **is** reachable, governed by the complete predicate of
  section 2. Since `27.21 eV < 250 eV` the half-width is `gamma`, so the
  condition is `0 < |wxt - 27.21138506| <= 0.5` eV. The strict lower bound
  matters: at `wxt = wtilde` exactly, `wdiff = 0`, `delw` is singular, and the
  record lies outside the nonsingular domain of this report and of
  `GW.GPP.BGW4`; the checker rejects such a record. This is an **algebraic
  possibility under a non-default policy, not an executed witness**: no run in
  this project sets `invalid_gpp_mode 2`, and nothing here shows such a state
  occurs in practice.

There is therefore **no blanket exclusion of invalid modes**. The correction
does not touch the executed witness of section 3, which involves only ordinary
positive real modes with `wtilde2 > 0`, nor the exclusion of smearing in
section 4.

## 3. Executed witness: `occ = 0.5` on the near-pole branch

### Configuration

The accepted Si-EPM GPP input (`bgw/export/sig_GPP.inp`) plus two lines:

```text
fermi_level_absolute
fermi_level -2.55213402880262530
```

`-2.55213402880262530` eV is the exported inner-band-1 energy `e_n1kq` from the
accepted T-002 evidence, i.e. the band that already reaches the near-pole
branch. Setting `efermi` to it makes `abs(e_n1kq - sig%efermi) = 0 < sig%tol`,
so `mtxel_cor.f90:1400` assigns `occ = 0.5`.

The archived `WFN_inner`, `eps0mat`, `epsmat`, `RHO` and `VXC` were **reused,
not regenerated**, so the threading-sensitive mean-field and epsilon stages
identified in T-002-R1 are not re-entered. BLAS threading was inherited, not
forced. Only `sigma.real.x` was rerun.

### Result

| Branch | `occ == 1` | `occ != 1` |
| --- | --- | --- |
| generic | 11,500,172 | 345,165 |
| **near-pole** | 76,461 | **3,702** |
| dropped | 92,920 | 1,968 |
| `sexcut` clamp fired | 44,937 | 0 |

The control (input verbatim, same binary) gives
`11,845,337 / 80,163 / 94,888 / 44,937` with **zero** `occ != 1` in every
branch, reproducing the accepted T-002 branch counts exactly.

48 records were exported: `fixtures/t003_nearpole_occ.dat`, checked by
`check_occupation.py`. **These 48 records are the first 48 qualifying
evaluations encountered in loop order, not a sample of the 3,702 counted
events**, and the checker reports both numbers side by side so the two cannot
be confused.

Section 7 states exactly which of the 29 exported fields are verified and how.
In summary, every record has `occ = 0.5` exactly, `|e_n1kq - efermi| = 0`
(so the half-occupation condition of `mtxel_cor.f90:1399` genuinely holds),
purely real `wtilde > 0`, `sch = 0` exactly, `limittwo`/`limitone` exactly at
their source values, nonvanishing merged and near-pole denominators both as
recorded and as recomputed, a `sexcut` decision matching its predicate, finite
fields, and branch 2 by three independent routes (exported label, rational
recomputation, and the recorded `wdiffr`/`delwr`). Worst binary64 residual
against the exact rational value of the source's own branch-2 expression:
**4.24e-19**.

### This state is reachable but not physically self-consistent

BerkeleyGW itself flags it (`fixtures/fermi_run_notices.txt`):

```text
WARNING: Discrepancy between number of electron per unit cell from ifmax and from occupations.
WARNING: RHO has total charge  8.00000     but WFN_inner occupations give charge  7.00000
WARNING: GPP plasma frequency does not respond to manual adjustment of the Fermi level.
```

The run does **not** die. `kp%ifmax` is not reset, because the reset loop at
`Common/input_utils.f90:285` uses strict inequalities and `el(1)` equals
`efermi` exactly; so `nvband = 4`, `ncrit = 0`, and band 1 is simultaneously
treated as occupied and assigned `occ = 0.5`. The Fermi level sits below the
valence maximum, which no self-consistent calculation would produce. The
witness therefore demonstrates that **no guard in the GPP path prevents the
combination**, not that a physical calculation reaches it.

## 4. What is excluded, and what remains open

**Excluded (smearing).** `do_smearing` is the only route to an occupation
outside `{0.5, 1}`, and `inread.f90:528-532` rejects it outside full-frequency
contour deformation:

```fortran
if(sig%do_smearing ) then
  if (.not. (sig%freq_dep==2 .and. sig%freq_dep_method==2)) then
    call die('occ_broadening must be used with frequency_dependence = 2 and &
             &frequency_dependence_method = 2', only_root_writes = .true.)
```

Observed: adding `occ_broadening 5.0` to the GPP input aborts with exactly that
message and exit 134 (`fixtures/smear_rejected.out`). GPP is `freq_dep = 1` or
`3`, so in BerkeleyGW 4.0 `sigma_gpp_cpu` can never see a smeared occupation,
and the `occ > 1` / `occ < 0` range of section 1 is unreachable there.
Hypotheses: this revision, this validation path, no source edits, and
`sig%do_smearing` set only through `occ_broadening`.

**A deterministic route that needs no manual Fermi level (source deduction,
not executed).** With the default `rfermi = .true.` and `efermi_input = 0`,
`Common/input_utils.f90:237-238` gives `efermi = emiddle*ryd` with
`emiddle = (maxval(vbm) + minval(cbm))/2`. If a band structure has
`maxval(vbm) == minval(cbm) == E` -- a band-touching semimetal, and in binary64
`(E+E)/2` is exact -- then `efermi = fl(E*ryd)`, while `e_n1kq` for that band is
`fl(E*ryd)` computed the same way at `Sigma/input.f90:806`. The difference is
then exactly `0 < sig%tol`, giving `occ = 0.5` with no manual input. This is a
deduction from the arithmetic, **not** an observation: I have no real-flavor
semimetal asset to run, and it additionally requires that band to satisfy the
independent near-pole energy condition.

**Inconclusive.** Whether an ordinary metal (`ncrit > 0`, no manual Fermi
level, no band touching) reaches `occ = 0.5` depends on whether a band energy
falls within `1.3606e-5` eV of the computed `emiddle*ryd`. That is
input-dependent and I did not resolve it. Missing constraint, stated precisely:
**a real-flavor, non-HDF5 metallic or semimetallic test asset**. The shipped
`testsuite/Na_smearing` does not serve: it requires `epsilon.cplx.x` and
`sigma.cplx.x` (complex flavor) and HDF5 (`WFN.h5`, `eps0mat.h5`), none of
which is in the accepted builds, and its sigma inputs use the
full-frequency/smearing mode that section 4 shows is disjoint from GPP.

## 5. Comparing the two expressions on the exported inputs

`check_occupation.py` evaluates, exactly over the rationals from each record's
own binary64 fields, the two `GW.GPP.BGW4` expressions at the record's `occ`,
and their difference both directly and through the closed form of
`GW.GPP.BGW4.branch_mismatch`, used unchanged:

```
(1-occ) * ( Omega2/(2*w*(x+w)) + Omega2/((x-w)*(x+w)) )
```

The closed form equalled the direct difference on all 48 records.

Three quantities, deliberately kept apart:

| Quantity | Value over the 48 records | What it is |
| --- | --- | --- |
| `fp_residual` | <= **4.24e-19** | binary64 rounding in the branch the source took |
| `mismatch_exact` | up to **6.5577** in magnitude | the mathematical difference between the two formulas at `occ = 0.5` |
| `mismatch_over_local_value` | up to **13735** | that difference divided by the local value the source accumulates |

So at `occ = 0.5` the branch choice changes the *local* per-`(G,G')` quantity by
up to four orders of magnitude more than the quantity itself. That is the
algebra of `branch_mismatch`, not a floating-point defect and not a bug
diagnosis.

**It is not a statement about the self-energy.** The local expression is
multiplied by `vcoul(igp)` and by `aqsntemp(ig,n1)*MYCONJG(aqsmtemp(igp,n1))`,
summed over ~12 million `(ig,igp,n1)` terms, and weighted by `neq`/`ndeg`. The
matrix elements are **not** in these records, so no weighted or physical
magnitude can be computed from this file. A `vcoul`-weighted figure is reported
only to show the scale is not trivially suppressed by `vcoul`.

**The source's intended approximation is a third, separate thing.** The
comment at `mtxel_cor.f90:1780-1783` states the near-pole branch is used
because "both SX and CH blow up, but their sum (for an occupied state n1) is
finite". That reasoning presumes the SX and CH poles cancel, which holds only
when they carry the same prefactor, i.e. `occ = 1`. At `occ = 0.5` the
premise of the branch does not hold. Whether the developers intend `occ = 0.5`
to be excluded here, or regard the resulting error as negligible after
summation, is **not determined by anything I read**, and I make no claim about it.

## 6. Reproducing

```bash
# full-fixture validation of the saved 48-record export (the default)
python3 bgw/occupation_audit/check_occupation.py

# explicitly labelled subset analysis; establishes existence only
python3 bgw/occupation_audit/check_occupation.py path/to/records.dat --subset

python3 -m unittest tests.test_occupation_audit         # 60 tests
```

The default mode requires exactly 48 records with ids `1..48` and no
duplicates, so it cannot be satisfied by a single record or by one record
repeated. `--subset` relaxes the count, reports `mode: "subset"` and
`full_fixture_validated: false`, and still rejects duplicates.

Regenerating the runs needs a BerkeleyGW tree; the exact commands, hashes and
threading are in `PROVENANCE.txt` (original) and `PROVENANCE-R1.txt` (repair
revision). The instrumentation patch (`t003_instrument.patch`) adds only
counters, `write` statements and four local variables; it changes no
expression, condition or accumulation, and it was **not** modified by the
repair.

## 7. What is verified, and with which threshold

Review finding F1 was that a successful exit did not enforce the record
contract: the only numeric gate was the `ssx_post` residual, and 12 of the 29
exported fields were parsed and then never read, while section 3 claimed the
records "all verify". This section is the corrected accounting.

### 7.1 Exactly-determined fields (equality, no tolerance)

These are literals, input parameters, or integer-valued in the source, so exact
comparison is the right check and no tolerance is involved.

| Field | Required value | Source |
| --- | --- | --- |
| `sch` | `0.0` exactly, in branch 2 | `mtxel_cor.f90:1835` assigns the literal |
| `limittwo` | `0.25` | `sig%gamma**2`, `inread.f90:151`, `mtxel_cor.f90:1699` |
| `limitone` | `250000.0` | `1/(4*TOL_Small)`, `mtxel_cor.f90:1698` |
| `wtilde_im` | `0.0` | real-flavor mapped scope |
| `wtilde_re` | `> 0` | positive real mode |
| `occ` | exactly `0.5` or `1.0` | smearing excluded, so `mtxel_cor.f90:1399-1403` |
| `abs(e_n1kq - efermi)` | `< sig%tol = 1.3606e-5` eV when `occ = 0.5` | `mtxel_cor.f90:1399`, `inread.f90:130,501` |
| `branch` | `2`, agreeing with both recomputations | `mtxel_cor.f90:1828-1843` |
| `ssx_post` vs `ssx_pre` | equal if the clamp predicate is false, `0` if true | `mtxel_cor.f90:1847-1848` |
| `den_nearpole`, `den_merged` | nonzero as recorded *and* as recomputed | -- |
| record ids | unique; `1..48` in full-fixture mode | -- |

Observed: `abs(e_n1kq - efermi)` is **exactly 0.0** on all 48 records, so the
half-occupation condition is satisfied with the largest possible margin.

### 7.2 Rounded derived intermediates (measured residual thresholds)

These were computed by the Fortran from other recorded fields, in its own
operation order, so they carry binary64 rounding and **exact-real equality
would be wrong**. Each is compared against its exact rational value and bounded
by a relative residual. The observed maxima below are measurements on the 48
archived records; they are **not proved universal error bounds**. The limits
carry two to three orders of magnitude of headroom, which is enough to reject
the review's corruptions (the two corruptions that these thresholds catch land 20 and 23
orders of magnitude above the limit)
without flagging legitimate rounding.

| Field | Kind | Observed max | Limit | Headroom |
| --- | --- | --- | --- | --- |
| `wtilde2` | relative | 9.361e-17 | 1e-14 | ~107x |
| `omega2` | relative | 1.774e-16 | 1e-14 | ~56x |
| `delw` | relative | 2.074e-16 | 1e-14 | ~48x |
| `delwr` | relative | 4.469e-16 | 1e-14 | ~22x |
| `wdiffr` | relative | 8.427e-17 | 1e-14 | ~119x |
| `den_nearpole` | relative | 3.071e-16 | 1e-14 | ~33x |
| `den_merged` | relative | 1.598e-16 | 1e-14 | ~63x |
| `den_generic` | **scaled** by `wxt**2 + wtilde2` | 6.813e-17 | 1e-14 | ~147x |
| `ssx_pre` | relative | 2.743e-16 | 1e-14 | ~36x |
| `ssx_post` | absolute vs exact | 4.2435598287864196e-19 | 1e-10 | unchanged |
| `wxt` vs `e_lk + sig%dw*(iw-2) - e_n1kq` | absolute | 4.441e-16 | 1e-12 | ~2250x |

`den_generic` is the one field needing a different bound. `wxt**2 - wtilde2` is
a difference of nearly equal quantities near the pole, so its *plain* relative
residual reaches **4.094e-13** from cancellation alone -- about 2722 ulps -- with
nothing wrong. Bounded instead against the magnitude of its operands,
`wxt**2 + wtilde2`, the residual is sub-ulp at 6.813e-17. Using a plain
relative limit here would have been either vacuous or a false alarm.

The `ssx_post` limit of `1e-10` is deliberately left exactly as it was before
the repair, and the observed value is unchanged at `4.2435598287864196e-19`.

`wxt` depends on `sig%dw`, which is **not** an exported field. The probe input
does not set `finite_difference_spacing`, so `sig%dw = 1.0` by
`inread.f90:149`; that is an assumption about the input, and the check above is
what tests it. The recorded offsets are exactly `(iw-2)*1.0` for the observed
`iw` values `2` and `3`.

### 7.3 Fields explicitly NOT verified

Reported as recorded and labelled `unmodeled_fields` in the JSON output,
because no relation internal to a record constrains them:

| Field | Why not |
| --- | --- |
| `vcoul` | Coulomb factor; no internal relation available |
| `ieps` | constrained only indirectly, through the `omega2` residual |
| `e_lk`, `e_n1kq` | only their difference is constrained, through `wxt` |
| `n1true`, `igp`, `ig` | indices; only record-id integrity is checked |
| `occ_broadening` | see below |

`occ_broadening` deserves its own note, because reading it as evidence would be
a mistake. Its recorded value is `0.10000000149011612` on every record. That is
the float32 image of `0.1`, because `Sigma/inread.f90:135` writes
`sig%occ_broadening=0.1` with no kind suffix. It is therefore the **untouched
stored default**, and `sig%do_smearing` is a separate flag that is not
exported. A nonzero `occ_broadening` in a record does **not** mean smearing was
active; in these runs it certainly was not, since `inread.f90:528-532` would
have aborted the GPP calculation (section 4).

### 7.4 Tally and cross-run integrity

The tally files are now validated rather than read: exactly the four expected
rows, no duplicates, no unknown rows, integer and **nonnegative** counts, and
`sexcut` not exceeding the total evaluations in its column.

Across the pair, the control must have zero `occ != 1` events in every row, the
probe must have a nonzero `occ != 1` near-pole count, and each row's column sum
must be **invariant** between control and probe. That last invariant holds
because the manual Fermi level changes only the occupation classification, not
which `(ig,igp,n1,iw)` evaluations occur: `flag_occ` still admits bands 1 to 4,
since `nvband = 4` and `ncrit = 0` in both runs. Measured:
`11,500,172 + 345,165 = 11,845,337`, `76,461 + 3,702 = 80,163`,
`92,920 + 1,968 = 94,888`, total `12,020,388` evaluations in both runs. This
invariant is what catches a count tampered to another nonnegative value, which
a nonnegativity check alone would miss.

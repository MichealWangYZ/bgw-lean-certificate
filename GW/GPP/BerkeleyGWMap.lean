/- ARCHIVED (2026-10-01): T-001..T-005 transcript/branch-audit lineage, superseded by bgw/endpoint/cert.py and GW.Bridge (docs/BRIDGE.md rows 8-15); kept, not extended, outside the fast gate. See docs/CODEMAP.md.
# Correspondence with the BerkeleyGW 4.0 real-flavor GPP kernel

This module transcribes the arithmetic of ONE specific code path of ONE
immutable BerkeleyGW revision and proves that it coincides with the scalar
model of `Specification.md` S1/S2.

## Provenance of the transcribed code

* Distribution: `BerkeleyGW-4.0`, source tarball
  SHA-256 `1a85b03b83b339056f65124bfa96832ca61152236d9bb1cb372e3040fc686a49`
  (the same checksum independently published in the Spack package recipe
  `spack_repo/builtin/packages/berkeleygw/package.py`, version `4.0`).
* File: `Sigma/mtxel_cor.f90`, SHA-256
  `8914dc00ac8d80d99e78f9b76a6d398491240bf147fa8714a65fed4ce5daf1dd`, 3968 lines.
* Code path: `subroutine sigma_gpp_cpu`, lines 1685-1931; occupied inner loop
  lines 1810-1848, unoccupied inner loop lines 1879-1897; accumulation lines
  1854-1855 and 1908-1915. CPU algorithm only (`sigma_gpp_algo = CPU_ALGO`); the OpenACC and
  OpenMP-target variants are NOT transcribed.
* Restriction: positive real modes in the real flavor. Some Fortran locals
  remain complex even in this flavor; imaginary and zero modes are not covered
  by the physical interpretation of these identities.

See `docs/BERKELEYGW_4.0_GPP.md` for the quoted Fortran, the tolerance and
cutoff policies that are deliberately NOT modeled, and the unit bookkeeping.

## What is and is not claimed

Proved here: a set of real-number identities between Lean functions that were
transcribed by hand from the listed lines and the S1 definitions. The
transcription itself is a human reading of Fortran source; it is evidence, not
a theorem. Nothing here claims that BerkeleyGW is correct, that its
floating-point evaluation matches these real-number identities, or that the
omitted cutoffs are unimportant.
-/
import GW.GPP.PoleCancellation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace GW.GPP.BGW4

open GW.GPP

/-! ## Transcribed quantities

Naming follows the Fortran locals. For a fixed pair of reciprocal-lattice
indices `(ig, igp)` and band `n1`:

| Lean argument | Fortran | meaning |
| --- | --- | --- |
| `ieps` | `I_eps_array(ig,my_igp)` | inverse dielectric matrix element |
| `wt`   | `wtilde_array(ig,my_igp)` | GPP mode energy, eV |
| `x`    | `wxt = wx_array(iw)` | `E - E_n1(k-q)`, eV |

Energies inside `mtxel_cor` are in eV: `Sigma/input.f90` line 806 multiplies the
mean-field eigenvalues by `ryd` on read. `Omega2` is then eV^2 and `ssx`, `sch`
are dimensionless; the energy dimension of the accumulated self-energy comes
from `vcoul(igp)`, which `Sigma/shiftenergy.f90` line 113 converts with `ryd`.

Common matrix, Coulomb, and degeneracy factors are divided out below. Thus
`omega2` is a normalized coefficient in eV^2, not S2's full coefficient in
eV^3. Occupation is NOT a common prefactor: it multiplies only SX. -/

/-- `Omega2 = wtilde2 * I_eps_array(ig,my_igp)` (line 1812). -/
def omega2 (ieps wt : ℝ) : ℝ := wt ^ 2 * ieps

/-- `delw = wtilde * CONJG(cden) * rden` with `cden = wdiff = wxt - wtilde`
and `rden = 1/(cden*CONJG(cden))` (lines 1817-1822). For real modes and
nonzero `x - wt`, the exact-arithmetic rewrite is `wtilde / (wxt - wtilde)`.
Lean's totalized division does not model Fortran at a zero denominator. -/
noncomputable def delw (x wt : ℝ) : ℝ := wt / (x - wt)

/-- Generic branch, taken when `wdiffr > limittwo` and `delwr < limitone`
(line 1828): `sch = delw * I_eps_array(ig,my_igp)` (line 1829). -/
noncomputable def schGeneric (ieps x wt : ℝ) : ℝ := delw x wt * ieps

/-- Generic branch: `cden = wxt**2 - wtilde2; ssx = Omega2*CONJG(cden)*rden`
(lines 1830-1833), i.e. `Omega2 / (wxt^2 - wtilde^2)` in the real flavor. -/
noncomputable def ssxGeneric (ieps x wt : ℝ) : ℝ :=
  omega2 ieps wt / (x ^ 2 - wt ^ 2)

/-- Near-pole branch, taken when the generic test fails but `delwr > TOL_Zero`
(line 1834): `sch = 0` and
`ssx = -Omega2*MYCONJG(cden)*rden*delw` with `cden = 4*wtilde2*(delw + 0.5)`
(lines 1835-1839). -/
noncomputable def ssxNearPole (ieps x wt : ℝ) : ℝ :=
  -omega2 ieps wt * delw x wt / (4 * wt ^ 2 * (delw x wt + 1 / 2))

/-! ## Accumulation

Lines 1854-1855 put `ssxt` into `ssx_array` with weight `1` and `scht` into
`sch_array` with weight `0.5`. Lines 1908 and 1915 then accumulate

```fortran
asxtemp(iw) = asxtemp(iw) - ssx_array(iw) * occ * vcoul(igp)
achtemp(iw) = achtemp(iw) + sch_array(iw) * vcoul(igp)
```

so the dynamic correlation contribution of one `(ig,igp)` pair, with the common
factor `aqsntemp*MYCONJG(aqsmtemp)*vcoul(igp)` divided out, is
`-occ*ssx + 0.5*sch`. -/

/-- Occupied state (`flag_occ = .true.`), generic branch, general occupation
`occ`. Note the asymmetry present in the source: `occ` multiplies only the
screened-exchange piece. -/
noncomputable def occupiedGenericOcc (occ ieps x wt : ℝ) : ℝ :=
  -occ * ssxGeneric ieps x wt + (1 / 2) * schGeneric ieps x wt

/-- Occupied state, near-pole branch (`sch` is set to zero there). -/
noncomputable def occupiedNearPoleOcc (occ ieps x wt : ℝ) : ℝ :=
  -occ * ssxNearPole ieps x wt

/-- Occupied state, generic branch, at full occupation `occ = 1`. -/
noncomputable def occupiedGeneric (ieps x wt : ℝ) : ℝ :=
  occupiedGenericOcc 1 ieps x wt

/-- Occupied state, near-pole branch, at full occupation `occ = 1`. -/
noncomputable def occupiedNearPole (ieps x wt : ℝ) : ℝ :=
  occupiedNearPoleOcc 1 ieps x wt

/-- Unoccupied state (`flag_occ = .false.`, lines 1879-1897), when its generic
predicate passes: only the Coulomb hole is accumulated, with factor `0.5`.
The source drops other unoccupied cases; that policy is not modeled here. -/
noncomputable def emptyBranch (ieps x wt : ℝ) : ℝ :=
  (1 / 2) * schGeneric ieps x wt

/-! ## A shared algebraic step

Both the occupied and the unoccupied accumulation multiply `sch` by `1/2`.
Turning that into the S1 Coulomb-hole denominator `2*w*(x-w)` is the one
rewrite they share. It needs `wt ≠ 0` but holds for every `x`, including
`x = wt` where both sides are Lean's totalized `0`. -/
theorem ch_term_eq (ieps x wt : ℝ) (hw : wt ≠ 0) :
    (1 / 2 : ℝ) * (wt / (x - wt) * ieps) = wt ^ 2 * ieps / (2 * wt * (x - wt)) := by
  rcases eq_or_ne (x - wt) 0 with h | h
  · rw [h]
    simp
  · field_simp
    ring

/-! ## The code's own two branches are the S1 raw and merged expressions

With the scalar coefficient identified as `A = Omega2 = wtilde^2 * I_eps`, the
generic branch at full occupation rewrites to `rawOccupied`. Away from both
poles, its near-pole branch rewrites to `occupiedTerm`. -/

/-- **Generic branch = S1 raw split expression.** Needs only `wt ≠ 0`; the
identity holds even at `x = wt`, where both sides are Lean's totalized `0`. -/
theorem occupiedGeneric_eq_rawOccupied (ieps x wt : ℝ) (hw : wt ≠ 0) :
    occupiedGeneric ieps x wt = rawOccupied (omega2 ieps wt) x wt := by
  unfold occupiedGeneric occupiedGenericOcc ssxGeneric schGeneric delw
    rawOccupied omega2
  rw [neg_div]
  rw [ch_term_eq ieps x wt hw]
  ring

/-- **Near-pole branch = S1 merged expression.** -/
theorem occupiedNearPole_eq_occupiedTerm (ieps x wt : ℝ) (hw : wt ≠ 0)
    (hp : x ≠ wt) (hm : x ≠ -wt) :
    occupiedNearPole ieps x wt = occupiedTerm (omega2 ieps wt) x wt := by
  have hp' : x - wt ≠ 0 := sub_ne_zero.mpr hp
  have hm' : x + wt ≠ 0 := fun h => hm (by linarith)
  unfold occupiedNearPole occupiedNearPoleOcc ssxNearPole delw occupiedTerm omega2
  have hd : wt / (x - wt) + 1 / 2 = (x + wt) / (2 * (x - wt)) := by
    field_simp; ring
  rw [hd]
  field_simp
  ring

/-- **Unoccupied branch = S1 empty expression.** -/
theorem emptyBranch_eq_emptyTerm (ieps x wt : ℝ) (hw : wt ≠ 0) :
    emptyBranch ieps x wt = emptyTerm (omega2 ieps wt) x wt := by
  unfold emptyBranch schGeneric delw emptyTerm omega2
  exact ch_term_eq ieps x wt hw

/-! ## Consequences for the source code

These are consequences for the manually transcribed exact-real expressions,
not formal verification of the Fortran program. -/

/-- **Branch consistency at full occupation.** The two exact-real expressions
agree away from both poles, before any additional clamp or dropped-mode policy.
This does not prove floating-point branch selection or rounding behavior. -/
theorem branches_agree (ieps x wt : ℝ) (hw : wt ≠ 0) (hp : x ≠ wt)
    (hm : x ≠ -wt) :
    occupiedGeneric ieps x wt = occupiedNearPole ieps x wt := by
  rw [occupiedGeneric_eq_rawOccupied ieps x wt hw,
    occupiedNearPole_eq_occupiedTerm ieps x wt hw hp hm]
  exact rawOccupied_eq_occupiedTerm _ x wt hw hp hm

/-- The generic expression has this punctured limit. This is not a statement
about the Fortran branch's evaluation at an exactly zero denominator. -/
theorem tendsto_occupiedGeneric (ieps wt : ℝ) (hw : wt ≠ 0) :
    Filter.Tendsto (fun x : ℝ => occupiedGeneric ieps x wt) (nhdsWithin wt {wt}ᶜ)
      (nhds (omega2 ieps wt / (4 * wt ^ 2))) := by
  have h := tendsto_rawOccupied_nhdsWithin_ne (omega2 ieps wt) wt hw
  refine h.congr fun x => ?_
  exact (occupiedGeneric_eq_rawOccupied ieps x wt hw).symm

/-- S1's merged extension has this value at the pole. Despite the historical
name, the theorem is about `occupiedTerm`, NOT `occupiedNearPole` at the pole. -/
theorem occupiedNearPole_limit_value (ieps wt : ℝ) (hw : wt ≠ 0) :
    occupiedTerm (omega2 ieps wt) wt wt = omega2 ieps wt / (4 * wt ^ 2) :=
  occupiedTerm_at_pole _ wt hw

/-- Totalized transcription and merged extension differ at an exact pole.
Neither totalized value asserts how Fortran handles its zero denominator. -/
theorem exact_pole_transcription_not_extension :
    occupiedNearPole 1 1 1 = 0 ∧ occupiedTerm (omega2 1 1) 1 1 = 1 / 4 := by
  norm_num [occupiedNearPole, occupiedNearPoleOcc, ssxNearPole, delw,
    occupiedTerm, omega2]

/-! ## The source comment uses a different `delw` than the source code

`mtxel_cor.f90` line 1777 documents

```
delw = (E - E_n1(k-q) - wtilde) / (2 * wtilde)
```

but line 1822 computes `delw = wtilde * CONJG(cden) * rden`, i.e.
`wtilde / (wx - wtilde)`. The two are not equal and not reciprocal; the
documented quantity is `1 / (2 * delw_code)`. Correspondingly, lines 1780-1782
assert that near the pole the sum "is `Omega^2 / (4 * wtilde2) / (1 + delw)`",
which is the merged value only when read with the *comment's* `delw`, while the
executable statement at line 1839 uses `4*wtilde2*(delw + 0.5)` with the
*code's* `delw`. Both reach the same number, so this is a naming defect in the
comments rather than a numerical one --- which is precisely what the next two
theorems establish. -/

/-- The quantity the comment at line 1777 calls `delw`. -/
noncomputable def delwComment (x wt : ℝ) : ℝ := (x - wt) / (2 * wt)

/-- The comment's `delw` and the code's `delw` are related by `1/(2*d)`, not by
equality and not by reciprocal. -/
theorem delwComment_eq (x wt : ℝ) (hw : wt ≠ 0) (hp : x ≠ wt) :
    delwComment x wt = 1 / (2 * delw x wt) := by
  have hp' : x - wt ≠ 0 := sub_ne_zero.mpr hp
  unfold delwComment delw
  field_simp

/-- The formula asserted by the comment at lines 1780-1782, read with the
comment's own `delw`, is the merged value --- so the comment and the code agree
numerically even though they disagree about what `delw` denotes. -/
theorem commentFormula_eq_occupiedTerm (ieps x wt : ℝ) (hw : wt ≠ 0)
    (hm : x ≠ -wt) :
    omega2 ieps wt / (4 * wt ^ 2) / (1 + delwComment x wt) =
      occupiedTerm (omega2 ieps wt) x wt := by
  have hm' : x + wt ≠ 0 := fun h => hm (by linarith)
  unfold delwComment occupiedTerm omega2
  have h1 : 1 + (x - wt) / (2 * wt) = (x + wt) / (2 * wt) := by
    field_simp; ring
  rw [h1]
  field_simp
  ring

/-! ## The occupation factor breaks the cancellation

`occ` is `1` for a state strictly below the Fermi level, but `0.5` for a state
within `sig%tol` of it (`mtxel_cor.f90` lines 1399-1403), and an arbitrary
value in `(0,1)` under `sig%do_smearing` (lines 1405-1411). Because the source
applies `occ` to the screened-exchange term only, the two branches then do NOT
agree in general. With nonzero `ieps` and `occ ≠ 1`, the generic pole is no
longer removable. Reachability in a physical run has not been established. -/

/-- **Exact branch mismatch at partial occupation.** -/
theorem branch_mismatch (occ ieps x wt : ℝ) (hw : wt ≠ 0) (hp : x ≠ wt)
    (hm : x ≠ -wt) :
    occupiedGenericOcc occ ieps x wt - occupiedNearPoleOcc occ ieps x wt =
      (1 - occ) * (omega2 ieps wt / (2 * wt * (x + wt))
        + omega2 ieps wt / ((x - wt) * (x + wt))) := by
  have hp' : x - wt ≠ 0 := sub_ne_zero.mpr hp
  have hm' : x + wt ≠ 0 := fun h => hm (by linarith)
  have hd : wt / (x - wt) + 1 / 2 = (x + wt) / (2 * (x - wt)) := by
    field_simp; ring
  unfold occupiedGenericOcc occupiedNearPoleOcc ssxGeneric ssxNearPole
    schGeneric delw omega2
  rw [hd]
  have hsq : x ^ 2 - wt ^ 2 = (x - wt) * (x + wt) := by ring
  rw [hsq]
  field_simp
  ring

/-- At full occupation the mismatch vanishes, recovering `branches_agree`. -/
theorem branch_mismatch_zero_of_occ_one (ieps x wt : ℝ) (hw : wt ≠ 0)
    (hp : x ≠ wt) (hm : x ≠ -wt) :
    occupiedGenericOcc 1 ieps x wt - occupiedNearPoleOcc 1 ieps x wt = 0 := by
  rw [branch_mismatch 1 ieps x wt hw hp hm]
  ring

/-- A concrete half-occupied witness: at `occ = 1/2`, `I_eps = 1`, `wtilde = 1`
and `x = 3/2` the two branches of the source differ. So the S1 cancellation
theorem applies to this code path only under the stated `occ = 1` hypothesis. -/
theorem branch_mismatch_nonzero_at_half_occupation :
    occupiedGenericOcc (1 / 2) 1 (3 / 2) 1 - occupiedNearPoleOcc (1 / 2) 1 (3 / 2) 1
      = 1 / 2 := by
  have h := branch_mismatch (1 / 2) 1 (3 / 2) 1 (by norm_num) (by norm_num)
    (by norm_num)
  rw [h]
  norm_num [omega2]

end GW.GPP.BGW4

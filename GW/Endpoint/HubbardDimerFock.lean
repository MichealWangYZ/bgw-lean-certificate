/-
A3(b), part 1: the two-site Hubbard model on its 16-dimensional Fock space,
built from Jordan-Wigner fermion operators. (Its exact sector ground-state
energies at N = 1, 2, 3 electrons are in part 2, `HubbardDimerExact.lean`.)

Modes (spin-orbitals) `m : Fin 4`: 0 = site 1 up, 1 = site 1 down,
2 = site 2 up, 3 = site 2 down. A basis state `s : Fin 16` has mode `m`
occupied iff bit `m` of `s` is set, and
`c_m |s> = (-1)^(number of occupied modes below m) |s - 2^m>`.
The canonical anticommutation relations of these integer matrices are
kernel-checked below (`car_anti`, `car_ann`), so `ann`/`cre` are genuine
fermion operators and not a transcription of someone else's Hamiltonian.

    H = -t sum_sigma (c†_{1s} c_{2s} + c†_{2s} c_{1s}) + U sum_i n_{i up} n_{i dn}

What this file does NOT say: nothing about GW here (see `HubbardDimer.lean`);
the model is a two-site toy, not silicon and not the BerkeleyGW run.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace GW.Endpoint.HubbardDimer

open Matrix

/-! ### Fermion operators on the Fock space -/

/-- Occupation of mode `m` in basis state `s`. -/
def occ (s : Fin 16) (m : Fin 4) : Bool := Nat.testBit s.val m.val

/-- Number of occupied modes strictly below `m` (the Jordan-Wigner string). -/
def below (s : Fin 16) (m : Fin 4) : ℕ :=
  ((List.finRange 4).filter (fun k => decide (k < m) && occ s k)).length

/-- Jordan-Wigner sign. -/
def jw (s : Fin 16) (m : Fin 4) : ℤ := (-1) ^ below s m

/-- Annihilation operator `c_m` as an integer matrix (column = input state). -/
def ann (m : Fin 4) : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun s' s => if occ s m = true ∧ s'.val + 2 ^ m.val = s.val then jw s m else 0

/-- Creation operator `c†_m` (real matrices: adjoint = transpose). -/
def cre (m : Fin 4) : Matrix (Fin 16) (Fin 16) ℤ := (ann m).transpose

/-- Canonical anticommutation relations `{c_m, c†_m'} = δ_{mm'}`. -/
theorem car_anti : ∀ m m' : Fin 4,
    ann m * cre m' + cre m' * ann m = if m = m' then 1 else 0 := by
  decide +kernel

/-- `{c_m, c_m'} = 0` (hence also `{c†_m, c†_m'} = 0` by transposition). -/
theorem car_ann : ∀ m m' : Fin 4, ann m * ann m' + ann m' * ann m = 0 := by
  decide +kernel

/-- Number operator of one mode. -/
def num (m : Fin 4) : Matrix (Fin 16) (Fin 16) ℤ := cre m * ann m

/-- Hopping operator `sum_sigma (c†_{1s} c_{2s} + h.c.)`. -/
def hopZ : Matrix (Fin 16) (Fin 16) ℤ :=
  cre 0 * ann 2 + cre 2 * ann 0 + cre 1 * ann 3 + cre 3 * ann 1

/-- Double-occupancy operator `sum_i n_{i up} n_{i dn}`. -/
def dblZ : Matrix (Fin 16) (Fin 16) ℤ := num 0 * num 1 + num 2 * num 3

/-- Total particle number. -/
def numZ : Matrix (Fin 16) (Fin 16) ℤ := num 0 + num 1 + num 2 + num 3

/-- The Hubbard interaction is the normal-ordered spin-independent contact
interaction `(1/2) sum_i sum_{s s'} c†_{is} c†_{is'} c_{is'} c_{is}`, i.e.
`v_{ij} = U δ_ij` for all spin pairs. This is the `v` that the GW part screens. -/
theorem two_dbl_eq_normal_ordered :
    2 • dblZ = ∑ i : Fin 2, ∑ σ : Fin 2, ∑ σ' : Fin 2,
      cre (2 * i + σ) * cre (2 * i + σ') * ann (2 * i + σ') * ann (2 * i + σ) := by
  decide +kernel

/-- Both terms conserve particle number, so each `N`-sector is invariant. -/
theorem hop_conserves : hopZ * numZ = numZ * hopZ := by decide +kernel
theorem dbl_conserves : dblZ * numZ = numZ * dblZ := by decide +kernel

/-- `numZ` is diagonal with the popcount of the state. -/
def popcount (s : Fin 16) : ℕ := ((List.finRange 4).filter (occ s)).length

theorem numZ_diag : ∀ s s' : Fin 16, numZ s' s = if s' = s then (popcount s : ℤ) else 0 := by
  decide +kernel

/-- The hopping operator, entry by entry (kernel-checked against the definition). -/
theorem hopZ_eq : hopZ = !![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0;
                            0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0;
                            0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,-1,0,0,0,0,0,0,0,0,-1,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0;
                            0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0;
                            0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0;
                            0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0;
                            0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  decide +kernel

/-- The double-occupancy operator is diagonal with these entries. -/
theorem dblZ_eq : dblZ = Matrix.diagonal ![0,0,0,1,0,0,0,1,0,0,0,1,1,1,1,2] := by
  decide +kernel

/-! ### The real Hamiltonian -/

/-- The two-site Hubbard Hamiltonian on the Fock space. -/
noncomputable def H (t U : ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  (-t) • hopZ.map (Int.cast : ℤ → ℝ) + U • dblZ.map (Int.cast : ℤ → ℝ)

/-- The action of `H` on an arbitrary vector, component by component. -/
theorem H_mulVec (t U : ℝ) (v : Fin 16 → ℝ) :
    H t U *ᵥ v = ![0, -t * v 4, -t * v 8, U * v 3 + t * v 6 - t * v 9,
      -t * v 1, 0, t * v 3 + t * v 12, U * v 7 + t * v 13,
      -t * v 2, -t * v 3 - t * v 12, 0, U * v 11 + t * v 14,
      U * v 12 + t * v 6 - t * v 9, U * v 13 + t * v 7, U * v 14 + t * v 11, 2 * U * v 15] := by
  rw [H, hopZ_eq, dblZ_eq]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.add_apply, Matrix.smul_apply,
      Matrix.diagonal] <;>
    first | ring1 | exact Or.inl (by ring)

end GW.Endpoint.HubbardDimer

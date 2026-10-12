/-
A3(b), part 2: exact sector ground-state energies of the two-site Hubbard
model (`HubbardDimerFock.lean`) and the exact fundamental gap at half filling,

    E_gap = E0(3) + E0(1) - 2 E0(2) = sqrt(U^2 + 16 t^2) - 2 t      (t > 0).

"Ground-state energy of sector N" is `IsSectorGround t U N E`: an eigenvector
with eigenvalue `E` supported on the `N`-particle states exists, AND the
variational bound `E |v|^2 <= <v, H v>` holds for every `N`-particle vector.
The second clause is proved by an explicit sum-of-squares decomposition, so
`E` is the lowest eigenvalue of the sector (`eigen_ge`), and it is unique
(`IsSectorGround.unique`). No numerical diagonalisation enters the proofs.
-/
import GW.Endpoint.HubbardDimerFock
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace GW.Endpoint.HubbardDimer

open Matrix

/-- `v` is supported on the `N`-particle states. -/
def InSector (N : ℕ) (v : Fin 16 → ℝ) : Prop := ∀ s : Fin 16, popcount s ≠ N → v s = 0

/-- `E` is the ground-state energy of the `N`-particle sector of `H t U`. -/
def IsSectorGround (t U : ℝ) (N : ℕ) (E : ℝ) : Prop :=
  (∃ v : Fin 16 → ℝ, v ≠ 0 ∧ InSector N v ∧ H t U *ᵥ v = E • v) ∧
    ∀ v : Fin 16 → ℝ, InSector N v → E * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H t U *ᵥ v)

theorem dot_self_pos {v : Fin 16 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv

/-- The ground energy bounds every eigenvalue of the sector from below. -/
theorem eigen_ge {t U E lam : ℝ} {N : ℕ} (hg : IsSectorGround t U N E) {v : Fin 16 → ℝ}
    (hv : v ≠ 0) (hs : InSector N v) (he : H t U *ᵥ v = lam • v) : E ≤ lam := by
  have h1 := hg.2 v hs
  rw [he, dotProduct_smul, smul_eq_mul] at h1
  exact le_of_mul_le_mul_right h1 (dot_self_pos hv)

/-- The sector ground-state energy is unique. -/
theorem IsSectorGround.unique {t U E E' : ℝ} {N : ℕ} (h : IsSectorGround t U N E)
    (h' : IsSectorGround t U N E') : E = E' := by
  obtain ⟨v, hv, hs, he⟩ := h.1
  obtain ⟨v', hv', hs', he'⟩ := h'.1
  exact le_antisymm (eigen_ge h hv' hs' he') (eigen_ge h' hv hs he)

/-- Quadratic form of `H`, written out. -/
theorem quad_form (t U : ℝ) (v : Fin 16 → ℝ) :
    v ⬝ᵥ (H t U *ᵥ v) =
      -2 * t * (v 1 * v 4 + v 2 * v 8)
      + U * (v 3 ^ 2 + v 12 ^ 2) - 2 * t * (v 3 + v 12) * (v 9 - v 6)
      + U * (v 7 ^ 2 + v 11 ^ 2 + v 13 ^ 2 + v 14 ^ 2) + 2 * t * (v 7 * v 13 + v 11 * v 14)
      + 2 * U * v 15 ^ 2 := by
  rw [H_mulVec]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

theorem norm_sq (v : Fin 16 → ℝ) :
    v ⬝ᵥ v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2 + v 6 ^ 2 + v 7 ^ 2
      + v 8 ^ 2 + v 9 ^ 2 + v 10 ^ 2 + v 11 ^ 2 + v 12 ^ 2 + v 13 ^ 2 + v 14 ^ 2
      + v 15 ^ 2 := by
  simp [dotProduct, Fin.sum_univ_succ]
  ring

/-! ### N = 1: E0 = -t -/

theorem ground_one {t U : ℝ} (ht : 0 ≤ t) : IsSectorGround t U 1 (-t) := by
  refine ⟨⟨![0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0], ?_, ?_, ?_⟩, ?_⟩
  · intro h; have := congrFun h 1; simp at this
  · intro s hs; fin_cases s <;> first | rfl | exact absurd (by decide) hs
  · rw [H_mulVec]; funext i; fin_cases i <;> simp
  · intro v hs
    have z : ∀ s : Fin 16, popcount s ≠ 1 → v s = 0 := hs
    rw [quad_form, norm_sq, z 0 (by decide), z 3 (by decide), z 5 (by decide), z 6 (by decide),
      z 7 (by decide), z 9 (by decide), z 10 (by decide), z 11 (by decide), z 12 (by decide),
      z 13 (by decide), z 14 (by decide), z 15 (by decide)]
    nlinarith [mul_nonneg ht (sq_nonneg (v 1 - v 4)), mul_nonneg ht (sq_nonneg (v 2 - v 8))]

/-! ### N = 3: E0 = U - t -/

theorem ground_three {t U : ℝ} (ht : 0 ≤ t) : IsSectorGround t U 3 (U - t) := by
  refine ⟨⟨![0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0], ?_, ?_, ?_⟩, ?_⟩
  · intro h; have := congrFun h 7; simp at this
  · intro s hs; fin_cases s <;> first | rfl | exact absurd (by decide) hs
  · rw [H_mulVec]; funext i; fin_cases i <;> simp <;> ring
  · intro v hs
    have z : ∀ s : Fin 16, popcount s ≠ 3 → v s = 0 := hs
    rw [quad_form, norm_sq, z 0 (by decide), z 1 (by decide), z 2 (by decide), z 3 (by decide),
      z 4 (by decide), z 5 (by decide), z 6 (by decide), z 8 (by decide), z 9 (by decide),
      z 10 (by decide), z 12 (by decide), z 15 (by decide)]
    nlinarith [mul_nonneg ht (sq_nonneg (v 7 + v 13)), mul_nonneg ht (sq_nonneg (v 11 + v 14))]

/-! ### N = 2: E0 = (U - sqrt(U^2 + 16 t^2)) / 2 -/

/-- `r = sqrt(U^2 + 16 t^2)`. -/
noncomputable def rEx (t U : ℝ) : ℝ := Real.sqrt (U ^ 2 + 16 * t ^ 2)

theorem rEx_sq (t U : ℝ) : rEx t U ^ 2 = U ^ 2 + 16 * t ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem rEx_gt {t U : ℝ} (ht : 0 < t) : U < rEx t U := by
  have h := rEx_sq t U
  have h0 : 0 ≤ rEx t U := Real.sqrt_nonneg _
  nlinarith

theorem ground_two {t U : ℝ} (ht : 0 < t) : IsSectorGround t U 2 ((U - rEx t U) / 2) := by
  have hr := rEx_sq t U
  have hgt := rEx_gt (U := U) ht
  set r := rEx t U
  refine ⟨⟨![0,0,0,(r - U) / 2,0,0,-2 * t,0,0,2 * t,0,0,(r - U) / 2,0,0,0], ?_, ?_, ?_⟩, ?_⟩
  · intro h; have := congrFun h 9; simp at this; exact ht.ne' this
  · intro s hs; fin_cases s <;> first | rfl | exact absurd (by decide) hs
  · rw [H_mulVec]; funext i
    fin_cases i <;> simp <;> first | ring1 | linear_combination (1/4 : ℝ) * hr
  · intro v hs
    have z : ∀ s : Fin 16, popcount s ≠ 2 → v s = 0 := hs
    rw [quad_form, norm_sq, z 0 (by decide), z 1 (by decide), z 2 (by decide), z 4 (by decide),
      z 7 (by decide), z 8 (by decide), z 11 (by decide), z 13 (by decide), z 14 (by decide),
      z 15 (by decide)]
    -- B = -E0 > 0, A = U - E0, A B = 4 t^2; with p = v3 + v12, q = v9 - v6:
    -- 2B (Q - E0 |v|^2) = (B q - 2 t p)^2 + A B (v3 - v12)^2 + B^2 (v6 + v9)^2 + 2 B^2 (v5^2 + v10^2)
    set B := (r - U) / 2 with hB
    have hBpos : 0 < B := by rw [hB]; linarith
    have hAB : (U + r) / 2 * B = 4 * t ^ 2 := by rw [hB]; linear_combination (1/4 : ℝ) * hr
    have key : 2 * B * (-2 * t * (0 * v 4 + 0 * 0) + U * (v 3 ^ 2 + v 12 ^ 2)
        - 2 * t * (v 3 + v 12) * (v 9 - v 6) + U * (0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2)
        + 2 * t * (0 * 0 + 0 * 0) + 2 * U * 0 ^ 2
        - (U - r) / 2 * (0 ^ 2 + 0 ^ 2 + 0 ^ 2 + v 3 ^ 2 + 0 ^ 2 + v 5 ^ 2 + v 6 ^ 2 + 0 ^ 2
          + 0 ^ 2 + v 9 ^ 2 + v 10 ^ 2 + 0 ^ 2 + v 12 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2))
        = (B * (v 9 - v 6) - 2 * t * (v 3 + v 12)) ^ 2 + (U + r) / 2 * B * (v 3 - v 12) ^ 2
          + B ^ 2 * (v 6 + v 9) ^ 2 + 2 * B ^ 2 * (v 5 ^ 2 + v 10 ^ 2) := by
      rw [hAB, hB]; linear_combination ((v 3 + v 12) ^ 2 + (v 3 - v 12) ^ 2) / 4 * hr
    have hsos : 0 ≤ (B * (v 9 - v 6) - 2 * t * (v 3 + v 12)) ^ 2 + (U + r) / 2 * B * (v 3 - v 12) ^ 2
          + B ^ 2 * (v 6 + v 9) ^ 2 + 2 * B ^ 2 * (v 5 ^ 2 + v 10 ^ 2) := by
      rw [hAB]; positivity
    rw [← key] at hsos
    nlinarith

/-! ### The exact gap -/

/-- The exact fundamental gap of the half-filled dimer. -/
noncomputable def gapExact (t U : ℝ) : ℝ := Real.sqrt (U ^ 2 + 16 * t ^ 2) - 2 * t

/-- The three sector ground energies (existence, with the lowest-eigenvalue property). -/
theorem sector_grounds {t U : ℝ} (ht : 0 < t) :
    IsSectorGround t U 1 (-t) ∧ IsSectorGround t U 2 ((U - Real.sqrt (U ^ 2 + 16 * t ^ 2)) / 2) ∧
      IsSectorGround t U 3 (U - t) :=
  ⟨ground_one ht.le, ground_two ht, ground_three ht.le⟩

/-- **Exact gap.** For ANY ground energies of the N = 1, 2, 3 sectors,
`E0(3) + E0(1) - 2 E0(2) = sqrt(U^2 + 16 t^2) - 2t`. -/
theorem exact_gap {t U E1 E2 E3 : ℝ} (ht : 0 < t) (h1 : IsSectorGround t U 1 E1)
    (h2 : IsSectorGround t U 2 E2) (h3 : IsSectorGround t U 3 E3) :
    E3 + E1 - 2 * E2 = gapExact t U := by
  rw [h1.unique (ground_one ht.le), h2.unique (ground_two ht), h3.unique (ground_three ht.le)]
  unfold gapExact rEx
  ring

end GW.Endpoint.HubbardDimer

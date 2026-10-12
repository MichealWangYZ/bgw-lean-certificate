/-
G3: the exact self-energy of the half-filled Hubbard dimer, derived from the
exact many-body problem, and its identification with the closed-shell
second-order (direct + exchange) self-energy of `HubbardDimerSecondOrder.lean`.

Everything is built on the Jordan-Wigner Fock space of `HubbardDimerFock.lean`:

* Spin-up orbital operators `annO p = Σ_i φ_p(i) c_{i↑}`, `creO p` (p = 0 bonding
  B, 1 antibonding A, orbitals `orb` of `HubbardDimerSecondOrder.lean`).
* Complete orthogonal eigenbases `ev1` (N = 1, energies -t, t, -t, t) and `ev3`
  (N = 3, energies U+t, U-t, U+t, U-t): eigen (`ev*_eigen`), in-sector,
  orthogonal, complete (`ev*_complete`).
* The N = 2 ground state `psi0` with energy `E0 = (U - r)/2`,
  `r = sqrt(U² + 16t²)`; it is the sector ground state (`psi0_ground`) and is
  nondegenerate (`psi0_unique`).
* `Gex`: the spin-up Lehmann Green's function over ALL N±1 eigenstates, with
  the matrix elements `<m|c†_q|ψ0>`, `<m|c_p|ψ0>` computed from the operator
  matrices (`creB_psi0` etc.). `GL_ground_eq`: any ground eigenvector gives the
  same G. `Gex_resolvent`: the Lehmann sum is
  `<ψ0|c_p (ω - (H - E0))⁻¹ c†_q|ψ0> + <ψ0|c†_q (ω + (H - E0))⁻¹ c_p|ψ0>`.

Results (t > 0):
* `Gex_offdiag`: G is diagonal in the B/A basis (parity).
* `Gex_BB`, `Gex_AA`, `weights_eq`: two poles per orbital with weights
  `(1 ± 4t/r)/2`; `Gex_U0`: at U = 0, `G = G0 = 1/(ω - eps0)`.
* Convention: `sigEx p ω = (ω - eps0_p) - 1/G_pp(ω)`, Dyson with the U = 0
  reference `G0`; `hf_shift`: its first-order part is `epsOrb - eps0 = U/2`, the
  HF shift of the GW files, so `sigEx - (epsOrb - eps0) = Σ_exact - Σ_HF`.
* **`sigEx_B`, `sigEx_A`** (all U, off the poles and zeros of G):
  `Σ_exact,p(ω) = (epsOrb_p - eps0_p) + sig2dir_p(ω) + sig2x_p(ω)` EXACTLY, with
  `sig2dir`, `sig2x` the textbook formula of `HubbardDimerSecondOrder.lean`
  (spin factors 2 and -1, HF denominators), imported, not restated.
* `sigEx_B_expansion`, `sigEx_A_expansion`: explicit cubic remainder
  `|Σ_p(ω) - (U/2 + U² Σ2_p(ω))| ≤ |U|³/(4 d_p²)`, `Σ2_B = 1/(4(ω - 3t))`,
  `Σ2_A = 1/(4(ω + 3t))`, on stated U-neighbourhoods; `sigEx_*_U2_limit` and
  `sig2_*_U2_limit`: both `(Σ - U/2)/U²` and `(sig2dir + sig2x)/U²` tend to Σ2
  as U → 0 (two-sided).
* `sig2x_eq_neg_half_dir`, `sigEx_*_ne_direct_only`: the direct (ring/GW-like)
  term alone is NOT the exact Σ for any U ≠ 0.

What this does NOT say: spin-up only (spin-down is the mirror image, not
proved); this two-site model and its restricted-HF reference only; that
second order is exact here is a property of this model, not a general fact;
real division is totalised, so the Σ statements carry explicit off-pole
hypotheses; no general diagrammatic/Wick derivation of the second-order
formula is given (it is shown to coincide with the exact Σ for this model).
-/
import GW.Endpoint.HubbardDimerExact
import GW.Endpoint.HubbardDimerSecondOrder

namespace GW.Endpoint.HubbardDimer

open Matrix Filter Topology

/-! ### Spin-up fermion operators, explicitly -/

theorem ann0_eq : ann 0 = !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem cre0_eq : cre 0 = !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

theorem ann2_eq : ann 2 = !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem cre2_eq : cre 2 = !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by
  decide +kernel

/-- Real-valued Jordan-Wigner operators. -/
noncomputable def annR (m : Fin 4) : Matrix (Fin 16) (Fin 16) ℝ := (ann m).map (Int.cast : ℤ → ℝ)
noncomputable def creR (m : Fin 4) : Matrix (Fin 16) (Fin 16) ℝ := (cre m).map (Int.cast : ℤ → ℝ)

theorem annR0_mulVec (v : Fin 16 → ℝ) : annR 0 *ᵥ v =
    ![v 1, 0, v 3, 0, v 5, 0, v 7, 0, v 9, 0, v 11, 0, v 13, 0, v 15, 0] := by
  rw [annR, ann0_eq]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem annR2_mulVec (v : Fin 16 → ℝ) : annR 2 *ᵥ v =
    ![v 4, -v 5, -v 6, v 7, 0, 0, 0, 0, v 12, -v 13, -v 14, v 15, 0, 0, 0, 0] := by
  rw [annR, ann2_eq]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem creR0_mulVec (v : Fin 16 → ℝ) : creR 0 *ᵥ v =
    ![0, v 0, 0, v 2, 0, v 4, 0, v 6, 0, v 8, 0, v 10, 0, v 12, 0, v 14] := by
  rw [creR, cre0_eq]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem creR2_mulVec (v : Fin 16 → ℝ) : creR 2 *ᵥ v =
    ![0, 0, 0, 0, v 0, -v 1, -v 2, v 3, 0, 0, 0, 0, v 8, -v 9, -v 10, v 11] := by
  rw [creR, cre2_eq]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-! ### Bonding / antibonding spin-up orbital operators -/

/-- Spin-up mode of site `i`. -/
def upMode : Fin 2 → Fin 4 := ![0, 2]

/-- `c_{p↑} = Σ_i φ_p(i) c_{i↑}` with the orbitals `orb` of `HubbardDimerSecondOrder.lean`. -/
noncomputable def annO (p : Fin 2) : Matrix (Fin 16) (Fin 16) ℝ := ∑ i : Fin 2, orb p i • annR (upMode i)
/-- `c†_{p↑}`. -/
noncomputable def creO (p : Fin 2) : Matrix (Fin 16) (Fin 16) ℝ := ∑ i : Fin 2, orb p i • creR (upMode i)

theorem annO_mulVec (v : Fin 16 → ℝ) :
    annO 0 *ᵥ v = s2 • (annR 0 *ᵥ v + annR 2 *ᵥ v) ∧
      annO 1 *ᵥ v = s2 • (annR 0 *ᵥ v - annR 2 *ᵥ v) := by
  simp only [annO, Fin.sum_univ_two, orb, phiB, phiA, upMode, Matrix.add_mulVec,
    Matrix.smul_mulVec_assoc, Matrix.neg_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨by rw [smul_add], ?_⟩
  simp only [neg_smul, Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, smul_sub, sub_eq_add_neg, smul_add, smul_neg]

theorem creO_mulVec (v : Fin 16 → ℝ) :
    creO 0 *ᵥ v = s2 • (creR 0 *ᵥ v + creR 2 *ᵥ v) ∧
      creO 1 *ᵥ v = s2 • (creR 0 *ᵥ v - creR 2 *ᵥ v) := by
  simp only [creO, Fin.sum_univ_two, orb, phiB, phiA, upMode, Matrix.add_mulVec,
    Matrix.smul_mulVec_assoc, Matrix.neg_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨by rw [smul_add], ?_⟩
  simp only [neg_smul, Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, smul_sub, sub_eq_add_neg, smul_add, smul_neg]

/-! ### Exact eigenstates of the N = 1 and N = 3 sectors (all of them) -/

/-- An orthogonal eigenbasis of the 4-dimensional `N = 1` sector
(states 1, 2, 4, 8): `B↑, A↑, B↓, A↓` (unnormalised, norm² = 2). -/
def ev1 : Fin 4 → Fin 16 → ℝ :=
  ![![0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0]]

/-- Their energies. -/
def en1 (t : ℝ) : Fin 4 → ℝ := ![-t, t, -t, t]

/-- An orthogonal eigenbasis of the 4-dimensional `N = 3` sector
(states 7, 11, 13, 14), unnormalised (norm² = 2). -/
def ev3 : Fin 4 → Fin 16 → ℝ :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0]]

/-- Their energies. -/
def en3 (t U : ℝ) : Fin 4 → ℝ := ![U + t, U - t, U + t, U - t]

theorem ev1_eigen (t U : ℝ) (k : Fin 4) : H t U *ᵥ ev1 k = en1 t k • ev1 k := by
  rw [H_mulVec]; fin_cases k <;> funext i <;> fin_cases i <;> simp [ev1, en1]

theorem ev3_eigen (t U : ℝ) (k : Fin 4) : H t U *ᵥ ev3 k = en3 t U k • ev3 k := by
  rw [H_mulVec]; fin_cases k <;> funext i <;> fin_cases i <;> simp [ev3, en3] <;> ring

theorem ev1_sector (k : Fin 4) : InSector 1 (ev1 k) := by
  intro s hs; fin_cases k <;> fin_cases s <;> first | rfl | exact absurd (by decide) hs

theorem ev3_sector (k : Fin 4) : InSector 3 (ev3 k) := by
  intro s hs; fin_cases k <;> fin_cases s <;> first | rfl | exact absurd (by decide) hs

theorem ev1_orth (j k : Fin 4) : ev1 j ⬝ᵥ ev1 k = if j = k then 2 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [ev1, dotProduct, Fin.sum_univ_succ] <;> norm_num

theorem ev3_orth (j k : Fin 4) : ev3 j ⬝ᵥ ev3 k = if j = k then 2 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [ev3, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Completeness: every `N = 1` vector is the sum of its components along `ev1`. -/
theorem ev1_complete (v : Fin 16 → ℝ) (hv : InSector 1 v) :
    v = ∑ k : Fin 4, ((ev1 k ⬝ᵥ v) / (ev1 k ⬝ᵥ ev1 k)) • ev1 k := by
  have z : ∀ s : Fin 16, popcount s ≠ 1 → v s = 0 := hv
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  simp [ev1, dotProduct, Fin.sum_univ_succ]
  fin_cases s <;> simp <;> first | exact z _ (by decide) | ring1

theorem ev3_complete (v : Fin 16 → ℝ) (hv : InSector 3 v) :
    v = ∑ k : Fin 4, ((ev3 k ⬝ᵥ v) / (ev3 k ⬝ᵥ ev3 k)) • ev3 k := by
  have z : ∀ s : Fin 16, popcount s ≠ 3 → v s = 0 := hv
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  simp [ev3, dotProduct, Fin.sum_univ_succ]
  fin_cases s <;> simp <;> first | exact z _ (by decide) | ring1

/-! ### The exact N = 2 ground state -/

/-- `k = (r - U)/2 > 0`, `r = sqrt(U² + 16t²)`. -/
noncomputable def kEx (t U : ℝ) : ℝ := (rEx t U - U) / 2

/-- Exact N = 2 ground-state energy `E0 = (U - r)/2 = -k`. -/
noncomputable def E0 (t U : ℝ) : ℝ := (U - rEx t U) / 2

/-- The exact N = 2 ground state (unnormalised), as in `ground_two`. -/
noncomputable def psi0 (t U : ℝ) : Fin 16 → ℝ :=
  ![0, 0, 0, kEx t U, 0, 0, -2 * t, 0, 0, 2 * t, 0, 0, kEx t U, 0, 0, 0]

theorem kEx_pos {t U : ℝ} (ht : 0 < t) : 0 < kEx t U := by
  unfold kEx; linarith [rEx_gt (U := U) ht]

theorem kEx_rel (t U : ℝ) : kEx t U * (kEx t U + U) = 4 * t ^ 2 := by
  unfold kEx; linear_combination (1 / 4 : ℝ) * rEx_sq t U

theorem psi0_eigen (t U : ℝ) : H t U *ᵥ psi0 t U = E0 t U • psi0 t U := by
  have hk := kEx_rel t U
  have hE : E0 t U = -kEx t U := by unfold E0 kEx; ring
  rw [H_mulVec, hE]; funext i
  fin_cases i <;> simp [psi0] <;> first | ring1 | linear_combination hk

theorem psi0_sector (t U : ℝ) : InSector 2 (psi0 t U) := by
  intro s hs; fin_cases s <;> first | rfl | exact absurd (by decide) hs

theorem psi0_ne {t U : ℝ} (ht : 0 < t) : psi0 t U ≠ 0 := by
  intro h; have := congrFun h 9; simp [psi0] at this; exact ht.ne' this

theorem psi0_ground {t U : ℝ} (ht : 0 < t) : IsSectorGround t U 2 (E0 t U) := ground_two ht

theorem psi0_norm (t U : ℝ) : psi0 t U ⬝ᵥ psi0 t U = 2 * kEx t U ^ 2 + 8 * t ^ 2 := by
  simp [psi0, dotProduct, Fin.sum_univ_succ]; ring

/-- **The N = 2 ground state is nondegenerate**: every N = 2 eigenvector with
eigenvalue `E0` is a multiple of `psi0`. -/
theorem psi0_unique {t U : ℝ} (ht : 0 < t) (v : Fin 16 → ℝ) (hs : InSector 2 v)
    (he : H t U *ᵥ v = E0 t U • v) : v = (v 3 / kEx t U) • psi0 t U := by
  have z : ∀ s : Fin 16, popcount s ≠ 2 → v s = 0 := hs
  have hk := kEx_pos (U := U) ht
  have hkr := kEx_rel t U
  have hE : E0 t U = -kEx t U := by unfold E0 kEx; ring
  rw [H_mulVec, hE] at he
  have e3 := congrFun he 3; have e5 := congrFun he 5; have e6 := congrFun he 6
  have e9 := congrFun he 9; have e10 := congrFun he 10; have e12 := congrFun he 12
  simp at e3 e5 e6 e9 e10 e12
  have hk0 : kEx t U ≠ 0 := hk.ne'
  have v5 : v 5 = 0 := e5.resolve_left hk0
  have v10 : v 10 = 0 := e10.resolve_left hk0
  have hUk : 0 < kEx t U + U := by nlinarith
  have v12 : v 12 = v 3 := by
    have : (kEx t U + U) * (v 3 - v 12) = 0 := by linear_combination e3 - e12
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have v6 : v 6 = -(2 * t) * v 3 / kEx t U := by
    field_simp; linear_combination e6 - t * v12
  have v9 : v 9 = 2 * t * v 3 / kEx t U := by
    field_simp; linear_combination e9 + t * v12
  funext s
  fin_cases s <;> simp [psi0] <;> first | exact z _ (by decide) | skip
  all_goals first
    | exact v5
    | exact v10
    | exact (div_mul_cancel₀ _ hk0).symm
    | (rw [v12]; exact (div_mul_cancel₀ _ hk0).symm)
    | (rw [v6]; field_simp; first | ring1 | exact Or.inl (by ring))
    | (rw [v9]; field_simp; ring1)

/-! ### c, c† acting on the ground state (computed from the Fock operators) -/

theorem creB_psi0 (t U : ℝ) : creO 0 *ᵥ psi0 t U = (s2 * (kEx t U - 2 * t)) • ev3 0 := by
  rw [(creO_mulVec _).1, creR0_mulVec, creR2_mulVec]
  funext i; fin_cases i <;> simp [psi0, ev3] <;> first | ring1 | exact Or.inl (by ring)

theorem creA_psi0 (t U : ℝ) : creO 1 *ᵥ psi0 t U = (-(s2 * (kEx t U + 2 * t))) • ev3 1 := by
  rw [(creO_mulVec _).2, creR0_mulVec, creR2_mulVec]
  funext i; fin_cases i <;> simp [psi0, ev3]
  all_goals ring1

theorem annB_psi0 (t U : ℝ) : annO 0 *ᵥ psi0 t U = (s2 * (kEx t U + 2 * t)) • ev1 2 := by
  rw [(annO_mulVec _).1, annR0_mulVec, annR2_mulVec]
  funext i; fin_cases i <;> simp [psi0, ev1]
  all_goals first | ring1 | exact Or.inl (by ring)

theorem annA_psi0 (t U : ℝ) : annO 1 *ᵥ psi0 t U = (s2 * (kEx t U - 2 * t)) • ev1 3 := by
  rw [(annO_mulVec _).2, annR0_mulVec, annR2_mulVec]
  funext i; fin_cases i <;> simp [psi0, ev1]
  all_goals ring1

/-! ### The exact Green's function (Lehmann representation) -/

/-- Spin-up time-ordered Green's function in the orbital basis, Lehmann form,
for an N = 2 state `ψ` of energy `E`, summed over the full N = 3 and N = 1
eigenbases `ev3`, `ev1` (every eigenstate, normalised by `|m|²|ψ|²`):

  G_pq(ω) = Σ_{m ∈ N+1} <ψ|c_p|m><m|c†_q|ψ> / (ω - (E_m - E))
          + Σ_{m ∈ N-1} <ψ|c†_q|m><m|c_p|ψ> / (ω - (E - E_m)).

Real matrices, so `<ψ|c_p|m> = (c†_p ψ)·m`. -/
noncomputable def GL (t U : ℝ) (ψ : Fin 16 → ℝ) (E : ℝ) (p q : Fin 2) (ω : ℝ) : ℝ :=
  (∑ m : Fin 4, (ev3 m ⬝ᵥ (creO p *ᵥ ψ)) * (ev3 m ⬝ᵥ (creO q *ᵥ ψ)) /
      ((ev3 m ⬝ᵥ ev3 m) * (ψ ⬝ᵥ ψ)) / (ω - (en3 t U m - E))) +
    ∑ m : Fin 4, (ev1 m ⬝ᵥ (annO q *ᵥ ψ)) * (ev1 m ⬝ᵥ (annO p *ᵥ ψ)) /
      ((ev1 m ⬝ᵥ ev1 m) * (ψ ⬝ᵥ ψ)) / (ω - (E - en1 t m))

/-- The exact Green's function of the half-filled dimer. -/
noncomputable def Gex (t U : ℝ) (p q : Fin 2) (ω : ℝ) : ℝ := GL t U (psi0 t U) (E0 t U) p q ω

theorem GL_smul (t U : ℝ) (ψ : Fin 16 → ℝ) (E c : ℝ) (hc : c ≠ 0) (p q : Fin 2) (ω : ℝ) :
    GL t U (c • ψ) E p q ω = GL t U ψ E p q ω := by
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  unfold GL
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun m _ => ?_ <;> congr 1 <;>
    rw [show ∀ a b n s : ℝ, c * a * (c * b) / (n * (c * (c * s))) = (c * c) * (a * b) / ((c * c) * (n * s))
      from fun a b n s => by ring, mul_div_mul_left _ _ hc2]

/-- **G does not depend on the choice of ground state**: for ANY nonzero N = 2
eigenvector `v` whose eigenvalue `E` is the N = 2 ground energy, the Lehmann
Green's function built on `(v, E)` is `Gex`. -/
theorem GL_ground_eq {t U : ℝ} (ht : 0 < t) {E : ℝ} (hg : IsSectorGround t U 2 E)
    {v : Fin 16 → ℝ} (hv : v ≠ 0) (hs : InSector 2 v) (he : H t U *ᵥ v = E • v)
    (p q : Fin 2) (ω : ℝ) : GL t U v E p q ω = Gex t U p q ω := by
  have hE : E = E0 t U := hg.unique (psi0_ground ht)
  subst hE
  have hv' := psi0_unique ht v hs he
  have hc : v 3 / kEx t U ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hv'; exact hv hv'
  rw [hv', GL_smul _ _ _ _ _ hc]; rfl

/-! ### Closed forms of the exact G -/

/-- Norm² of the ground state. -/
noncomputable def nrm (t U : ℝ) : ℝ := 2 * kEx t U ^ 2 + 8 * t ^ 2

/-- Lehmann weights: `wPlus = (k + 2t)²/|ψ|²`, `wMinus = (k - 2t)²/|ψ|²`. -/
noncomputable def wPlus (t U : ℝ) : ℝ := (kEx t U + 2 * t) ^ 2 / nrm t U
noncomputable def wMinus (t U : ℝ) : ℝ := (kEx t U - 2 * t) ^ 2 / nrm t U

theorem sum_ev3 (c : ℝ) (j : Fin 4) (f : Fin 4 → ℝ) :
    ∑ m : Fin 4, (ev3 m ⬝ᵥ (c • ev3 j)) * f m = 2 * c * f j := by
  simp only [dotProduct_smul, ev3_orth, smul_eq_mul]
  fin_cases j <;> simp [Fin.sum_univ_four, mul_comm, mul_left_comm, mul_assoc]

theorem sum_ev1 (c : ℝ) (j : Fin 4) (f : Fin 4 → ℝ) :
    ∑ m : Fin 4, (ev1 m ⬝ᵥ (c • ev1 j)) * f m = 2 * c * f j := by
  simp only [dotProduct_smul, ev1_orth, smul_eq_mul]
  fin_cases j <;> simp [Fin.sum_univ_four, mul_comm, mul_left_comm, mul_assoc]

theorem s2_weight (x N : ℝ) : s2 * x * 2 * (s2 * x * 2) / (2 * N) = x ^ 2 / N := by
  rw [show s2 * x * 2 * (s2 * x * 2) = 2 * x ^ 2 by linear_combination 4 * x ^ 2 * s2_sq,
    mul_div_mul_left _ _ two_ne_zero]

/-- **Exact G, bonding element**, for every real `ω` (division totalised; off the
poles this is the physical G): removal pole `E0 + t` with weight `wPlus`,
addition pole `U + t - E0` with weight `wMinus`. -/
theorem Gex_BB (t U ω : ℝ) :
    Gex t U 0 0 ω = wMinus t U / (ω - (U + t - E0 t U)) + wPlus t U / (ω - (E0 t U + t)) := by
  unfold Gex GL
  rw [creB_psi0, annB_psi0, psi0_norm]
  simp only [dotProduct_smul, smul_eq_mul, ev3_orth, ev1_orth, Fin.sum_univ_four, en3, en1]
  simp only [Fin.isValue, if_true, if_false, reduceCtorEq]
  simp
  rw [s2_weight, s2_weight]; rfl

/-- Exact G, antibonding element: removal pole `E0 - t` (weight `wMinus`),
addition pole `U - t - E0` (weight `wPlus`). -/
theorem Gex_AA (t U ω : ℝ) :
    Gex t U 1 1 ω = wPlus t U / (ω - (U - t - E0 t U)) + wMinus t U / (ω - (E0 t U - t)) := by
  unfold Gex GL
  rw [creA_psi0, annA_psi0, psi0_norm]
  simp only [dotProduct_smul, smul_eq_mul, ev3_orth, ev1_orth, Fin.sum_univ_four, en3, en1]
  simp
  rw [s2_weight, s2_weight]; rfl

/-- **Parity**: the exact G is diagonal in the bonding/antibonding basis. -/
theorem Gex_offdiag (t U ω : ℝ) : Gex t U 0 1 ω = 0 ∧ Gex t U 1 0 ω = 0 := by
  unfold Gex GL
  rw [creA_psi0, annA_psi0, creB_psi0, annB_psi0]
  simp [dotProduct_smul, ev3_orth, ev1_orth, Fin.sum_univ_four]


theorem nrm_pos {t U : ℝ} (ht : 0 < t) : 0 < nrm t U := by unfold nrm; positivity

theorem E0_eq (t U : ℝ) : E0 t U = -kEx t U := by unfold E0 kEx; ring

/-- The weights in terms of `r = sqrt(U² + 16t²)`: `(1 ± 4t/r)/2`. -/
theorem weights_eq {t U : ℝ} (ht : 0 < t) :
    wPlus t U = (1 + 4 * t / rEx t U) / 2 ∧ wMinus t U = (1 - 4 * t / rEx t U) / 2 := by
  have hr := rEx_sq t U
  have hr0 : 0 < rEx t U := Real.sqrt_pos.mpr (by positivity)
  have hn := nrm_pos (U := U) ht
  unfold wPlus wMinus nrm kEx at *
  constructor <;> rw [div_eq_div_iff hn.ne' (by norm_num)] <;> field_simp
  · linear_combination 32 * t * hr
  · linear_combination -32 * t * hr


/-- Rational form of `G_BB` off its two poles: its only zero is `ω = 3t + U/2`. -/
theorem Gex_BB_rat {t U ω : ℝ} (ht : 0 < t) (ha : ω - (E0 t U + t) ≠ 0)
    (hb : ω - (U + t - E0 t U) ≠ 0) :
    Gex t U 0 0 ω = (ω - (3 * t + U / 2)) / ((ω - (E0 t U + t)) * (ω - (U + t - E0 t U))) := by
  have hn := nrm_pos (U := U) ht
  have hk := kEx_rel t U
  rw [Gex_BB]; unfold wPlus wMinus
  rw [div_div, div_div, div_add_div _ _ (mul_ne_zero hn.ne' hb) (mul_ne_zero hn.ne' ha),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hn.ne' hb) (mul_ne_zero hn.ne' ha)) (mul_ne_zero ha hb)]
  unfold nrm; rw [E0_eq]
  linear_combination -8 * t * (kEx t U ^ 2 + 4 * t ^ 2) * (-kEx t U + t - ω) * (U + kEx t U + t - ω) * hk

theorem Gex_AA_rat {t U ω : ℝ} (ht : 0 < t) (ha : ω - (E0 t U - t) ≠ 0)
    (hb : ω - (U - t - E0 t U) ≠ 0) :
    Gex t U 1 1 ω = (ω - (U / 2 - 3 * t)) / ((ω - (E0 t U - t)) * (ω - (U - t - E0 t U))) := by
  have hn := nrm_pos (U := U) ht
  have hk := kEx_rel t U
  rw [Gex_AA]; unfold wPlus wMinus
  rw [div_div, div_div, div_add_div _ _ (mul_ne_zero hn.ne' hb) (mul_ne_zero hn.ne' ha),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hn.ne' hb) (mul_ne_zero hn.ne' ha)) (mul_ne_zero ha hb)]
  unfold nrm; rw [E0_eq]
  linear_combination 8 * t * (kEx t U ^ 2 + 4 * t ^ 2) * (kEx t U + t + ω) * (-U - kEx t U + t + ω) * hk


/-! ### The second-order self-energy of `HubbardDimerSecondOrder.lean`, in closed form -/

theorem sig2dir_B_eq (t U E : ℝ) : sig2dir t U 0 E = U ^ 2 / 2 / (E - (3 * t + U / 2)) := by
  simp [sig2dir, occS, virS, eri_eq, epsOrb, epsA, epsB]
  congr 1 <;> ring

theorem sig2x_B_eq (t U E : ℝ) : sig2x t U 0 E = -(U ^ 2 / 4) / (E - (3 * t + U / 2)) := by
  simp [sig2x, occS, virS, eri_eq, epsOrb, epsA, epsB]
  congr 1 <;> ring

theorem sig2dir_A_eq (t U E : ℝ) : sig2dir t U 1 E = U ^ 2 / 2 / (E - (U / 2 - 3 * t)) := by
  simp [sig2dir, occS, virS, eri_eq, epsOrb, epsA, epsB]
  congr 1 <;> ring

theorem sig2x_A_eq (t U E : ℝ) : sig2x t U 1 E = -(U ^ 2 / 4) / (E - (U / 2 - 3 * t)) := by
  simp [sig2x, occS, virS, eri_eq, epsOrb, epsA, epsB]
  congr 1 <;> ring


/-- Direct + exchange, bonding: `(U²/4)/(E - (3t + U/2))` (all `E`, totalised). -/
theorem sig2_B_eq (t U E : ℝ) :
    sig2dir t U 0 E + sig2x t U 0 E = U ^ 2 / 4 / (E - (3 * t + U / 2)) := by
  rw [sig2dir_B_eq, sig2x_B_eq, ← add_div]; congr 1; ring

/-- Direct + exchange, antibonding: `(U²/4)/(E - (U/2 - 3t))`. -/
theorem sig2_A_eq (t U E : ℝ) :
    sig2dir t U 1 E + sig2x t U 1 E = U ^ 2 / 4 / (E - (U / 2 - 3 * t)) := by
  rw [sig2dir_A_eq, sig2x_A_eq, ← add_div]; congr 1; ring

/-! ### The exact self-energy -/

/-- Non-interacting (`U = 0`) orbital energies: `h0 φ_B = -t φ_B`, `h0 φ_A = t φ_A`
(`h0_orbitals`). -/
noncomputable def eps0 (t : ℝ) : Fin 2 → ℝ := ![-t, t]

/-- **Exact self-energy** by Dyson's equation with the `U = 0` reference,
orbital by orbital (G and G0 are both diagonal in the orbital basis):
`Σ_p(ω) = G0_p(ω)⁻¹ - G_pp(ω)⁻¹ = (ω - eps0_p) - 1/G_pp(ω)`.
Physically meaningful only where `G_pp(ω) ≠ 0` and `ω` is not a pole of G. -/
noncomputable def sigEx (t U : ℝ) (p : Fin 2) (ω : ℝ) : ℝ := (ω - eps0 t p) - 1 / Gex t U p p ω

/-- The `U = 0` limit of the exact G is `G0 = 1/(ω - eps0)`: the reference
propagator is itself the Lehmann G of the non-interacting ground state. -/
theorem Gex_U0 {t : ℝ} (ht : 0 < t) (p : Fin 2) (ω : ℝ) :
    Gex t 0 p p ω = 1 / (ω - eps0 t p) := by
  have hr : rEx t 0 = 4 * t := by
    unfold rEx; rw [show (0 : ℝ) ^ 2 + 16 * t ^ 2 = (4 * t) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  have hk : kEx t 0 = 2 * t := by unfold kEx; rw [hr]; ring
  have hE : E0 t 0 = -(2 * t) := by rw [E0_eq, hk]
  have hn : nrm t 0 = 16 * t ^ 2 := by unfold nrm; rw [hk]; ring
  have ht2 : (16 : ℝ) * t ^ 2 ≠ 0 := by positivity
  fin_cases p
  · show Gex t 0 0 0 ω = 1 / (ω - eps0 t 0)
    rw [Gex_BB]; unfold wPlus wMinus; rw [hk, hn, hE]
    simp [eps0]; rw [show (2 * t + 2 * t) ^ 2 = 16 * t ^ 2 by ring, div_self ht2]; ring_nf
  · show Gex t 0 1 1 ω = 1 / (ω - eps0 t 1)
    rw [Gex_AA]; unfold wPlus wMinus; rw [hk, hn, hE]
    simp [eps0]; rw [show (2 * t + 2 * t) ^ 2 = 16 * t ^ 2 by ring, div_self ht2]; ring_nf


/-- **Main theorem, bonding orbital.** Off the poles of G (`E0 + t`, `U + t - E0`)
and off the zero of G (`3t + U/2`, the pole of Σ), the exact self-energy is
the HF shift plus the closed-shell second-order direct + exchange self-energy
of `HubbardDimerSecondOrder.lean`, with its HF denominators, EXACTLY (all U):
`Σ_B(ω) = (epsB - eps0_B) + sig2dir_B(ω) + sig2x_B(ω)`. -/
theorem sigEx_B {t U ω : ℝ} (ht : 0 < t) (ha : ω - (E0 t U + t) ≠ 0)
    (hb : ω - (U + t - E0 t U) ≠ 0) (hc : ω - (3 * t + U / 2) ≠ 0) :
    sigEx t U 0 ω = (epsOrb t U 0 - eps0 t 0) + (sig2dir t U 0 ω + sig2x t U 0 ω) := by
  have hk := kEx_rel t U
  unfold sigEx
  rw [Gex_BB_rat ht ha hb, sig2_B_eq, one_div_div]
  simp only [epsOrb, eps0, epsB, Matrix.cons_val_zero]
  rw [E0_eq] at ha hb ⊢
  have key : (ω - (-kEx t U + t)) * (ω - (U + t - -kEx t U)) =
      (ω + t - U / 2) * (ω - (3 * t + U / 2)) - U ^ 2 / 4 := by linear_combination (-1 : ℝ) * hk
  rw [key, sub_div, mul_div_cancel_right₀ _ hc]; ring

/-- **Main theorem, antibonding orbital.** Same statement with the poles
`E0 - t`, `U - t - E0` of G and its zero `U/2 - 3t`. -/
theorem sigEx_A {t U ω : ℝ} (ht : 0 < t) (ha : ω - (E0 t U - t) ≠ 0)
    (hb : ω - (U - t - E0 t U) ≠ 0) (hc : ω - (U / 2 - 3 * t) ≠ 0) :
    sigEx t U 1 ω = (epsOrb t U 1 - eps0 t 1) + (sig2dir t U 1 ω + sig2x t U 1 ω) := by
  have hk := kEx_rel t U
  unfold sigEx
  rw [Gex_AA_rat ht ha hb, sig2_A_eq, one_div_div]
  simp only [epsOrb, eps0, epsA, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [E0_eq] at ha hb ⊢
  have key : (ω - (-kEx t U - t)) * (ω - (U - t - -kEx t U)) =
      (ω - t - U / 2) * (ω - (U / 2 - 3 * t)) - U ^ 2 / 4 := by linear_combination (-1 : ℝ) * hk
  rw [key, sub_div, mul_div_cancel_right₀ _ hc]; ring


/-- The first-order term is the HF shift of the GW files: `epsOrb - eps0 = U/2`
for both orbitals (`fock_eq`: `F = h0 + (U/2)·1`). -/
theorem hf_shift (t U : ℝ) (p : Fin 2) : epsOrb t U p - eps0 t p = U / 2 := by
  fin_cases p <;> simp [epsOrb, eps0, epsA, epsB]

/-! ### Expansion in U at fixed ω -/

/-- `|k - 2t| ≤ |U|`: the U-dependent poles of G move by at most O(|U|). -/
theorem kEx_near {t U : ℝ} (ht : 0 < t) : |kEx t U - 2 * t| ≤ |U| := by
  have hr := rEx_sq t U
  have hr0 : 0 ≤ rEx t U := Real.sqrt_nonneg _
  have hU := sq_abs U
  have hU0 := abs_nonneg U
  have h1 : 4 * t ≤ rEx t U := by nlinarith
  have h2 : rEx t U ≤ |U| + 4 * t := by nlinarith
  have h3 := neg_abs_le U
  have h4 := le_abs_self U
  unfold kEx; rw [abs_le]; constructor <;> linarith

/-- Scalar remainder: `|(U²/4)/(d - U/2) - U²/(4d)| ≤ |U|³/(4d²)` for `|U| ≤ |d|`. -/
theorem rem_bound {d U : ℝ} (hd : d ≠ 0) (hU : |U| ≤ |d|) :
    |U ^ 2 / 4 / (d - U / 2) - U ^ 2 * (1 / (4 * d))| ≤ |U| ^ 3 / (4 * d ^ 2) := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hdh : |d| / 2 ≤ |d - U / 2| := by
    have := abs_sub_abs_le_abs_sub d (U / 2)
    rw [abs_div, abs_two] at this; linarith
  have hne : d - U / 2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hdh; linarith
  have e : U ^ 2 / 4 / (d - U / 2) - U ^ 2 * (1 / (4 * d)) = U ^ 3 / (8 * d * (d - U / 2)) := by
    rw [div_div, mul_one_div, div_sub_div _ _ (mul_ne_zero four_ne_zero hne) (mul_ne_zero four_ne_zero hd)]
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero four_ne_zero hne) (mul_ne_zero four_ne_zero hd))
      (mul_ne_zero (mul_ne_zero (by norm_num) hd) hne)]
    ring
  rw [e, abs_div, abs_mul, abs_mul, abs_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hd2 : d ^ 2 = |d| * |d| := by rw [← sq_abs]; ring
  rw [hd2, show |(8 : ℝ)| = 8 by norm_num]
  have : |U| ^ 3 * (8 * |d| * (|d| / 2)) ≤ |U| ^ 3 * (8 * |d| * |d - U / 2|) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hdh (by positivity)
  nlinarith [this]

/-- **U expansion, bonding orbital, explicit remainder.** For fixed `ω` with
`ω ≠ 3t`, `ω ≠ -t` (the U = 0 poles), and every `U` with `2|U| < |ω - 3t|`,
`|U| < |ω + t|`:
`|Σ_B(ω) - (U·Σ1 + U²·Σ2_B(ω))| ≤ |U|³/(4(ω - 3t)²)` with `Σ1 = 1/2` (HF) and
`Σ2_B(ω) = 1/(4(ω - 3t))`. -/
theorem sigEx_B_expansion {t ω U : ℝ} (ht : 0 < t) (hd : ω - 3 * t ≠ 0)
    (hU1 : 2 * |U| < |ω - 3 * t|) (hU2 : |U| < |ω + t|) :
    |sigEx t U 0 ω - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω - 3 * t))))| ≤
      |U| ^ 3 / (4 * (ω - 3 * t) ^ 2) := by
  have hk := kEx_near (U := U) ht
  rw [abs_le] at hk
  have hU0 := abs_nonneg U
  have ha : ω - (E0 t U + t) ≠ 0 := by
    rw [E0_eq]; intro h
    have : ω + t = -(kEx t U - 2 * t) := by linarith
    rw [this, abs_neg] at hU2; linarith [abs_le.mpr hk]
  have hb : ω - (U + t - E0 t U) ≠ 0 := by
    rw [E0_eq]; intro h
    have : ω - 3 * t = U + (kEx t U - 2 * t) := by linarith
    rw [this] at hU1; linarith [abs_add U (kEx t U - 2 * t), abs_le.mpr hk]
  have hc : ω - (3 * t + U / 2) ≠ 0 := by
    intro h
    have : ω - 3 * t = U / 2 := by linarith
    rw [this, abs_div, abs_two] at hU1; linarith
  rw [sigEx_B ht ha hb hc, hf_shift, sig2_B_eq,
    show U / 2 + U ^ 2 / 4 / (ω - (3 * t + U / 2)) - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω - 3 * t))))
      = U ^ 2 / 4 / ((ω - 3 * t) - U / 2) - U ^ 2 * (1 / (4 * (ω - 3 * t))) by ring_nf]
  exact rem_bound hd (by linarith)


/-- **U expansion, antibonding orbital**: for `ω ≠ -3t`, `ω ≠ t`, `2|U| < |ω - t|`,
`|U| < |ω + 3t|`: `|Σ_A(ω) - (U/2 + U²/(4(ω + 3t)))| ≤ |U|³/(4(ω + 3t)²)`. -/
theorem sigEx_A_expansion {t ω U : ℝ} (ht : 0 < t) (hd : ω + 3 * t ≠ 0)
    (hU1 : 2 * |U| < |ω - t|) (hU2 : |U| < |ω + 3 * t|) :
    |sigEx t U 1 ω - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω + 3 * t))))| ≤
      |U| ^ 3 / (4 * (ω + 3 * t) ^ 2) := by
  have hk := kEx_near (U := U) ht
  rw [abs_le] at hk
  have hU0 := abs_nonneg U
  have ha : ω - (E0 t U - t) ≠ 0 := by
    rw [E0_eq]; intro h
    have : ω + 3 * t = -(kEx t U - 2 * t) := by linarith
    rw [this, abs_neg] at hU2; linarith [abs_le.mpr hk]
  have hb : ω - (U - t - E0 t U) ≠ 0 := by
    rw [E0_eq]; intro h
    have : ω - t = U + (kEx t U - 2 * t) := by linarith
    rw [this] at hU1; linarith [abs_add U (kEx t U - 2 * t), abs_le.mpr hk]
  have hc : ω - (U / 2 - 3 * t) ≠ 0 := by
    intro h
    have : ω + 3 * t = U / 2 := by linarith
    rw [this, abs_div, abs_two] at hU2; linarith
  rw [sigEx_A ht ha hb hc, hf_shift, sig2_A_eq,
    show U / 2 + U ^ 2 / 4 / (ω - (U / 2 - 3 * t)) - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω + 3 * t))))
      = U ^ 2 / 4 / ((ω + 3 * t) - U / 2) - U ^ 2 * (1 / (4 * (ω + 3 * t))) by ring_nf]
  exact rem_bound hd hU2.le

/-- Squeeze helper: `|f U - c| ≤ K|U|` on a punctured neighbourhood gives
`f → c` as `U → 0`, `U ≠ 0`. -/
theorem tendsto_of_abs_le_mul {f : ℝ → ℝ} {c K δ : ℝ} (hδ : 0 < δ)
    (h : ∀ U, U ≠ 0 → |U| < δ → |f U - c| ≤ K * |U|) : Tendsto f (𝓝[≠] 0) (𝓝 c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min δ (ε / (|K| + 1)), lt_min hδ (by positivity), fun U hU hd => ?_⟩
  rw [Real.dist_eq, sub_zero] at hd
  rw [Real.dist_eq]
  have h1 := h U hU (lt_of_lt_of_le hd (min_le_left _ _))
  have h2 : |U| < ε / (|K| + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hK : K * |U| ≤ |K| * |U| := mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg U)
  have h3 : |K| * |U| < ε := by
    have hK1 : 0 < |K| + 1 := by positivity
    rw [lt_div_iff₀ hK1] at h2
    nlinarith [abs_nonneg K, abs_nonneg U]
  linarith

/-- `|(Σ - U/2)/U² - Σ2|` from the cubic remainder. -/
theorem div_sq_bound {S U c d : ℝ} (hU : U ≠ 0) (h : |S - (U * (1 / 2) + U ^ 2 * c)| ≤ |U| ^ 3 / (4 * d ^ 2)) :
    |(S - U / 2) / U ^ 2 - c| ≤ 1 / (4 * d ^ 2) * |U| := by
  have hU2 : 0 < U ^ 2 := by positivity
  have e : (S - U / 2) / U ^ 2 - c = (S - (U * (1 / 2) + U ^ 2 * c)) / U ^ 2 := by field_simp; ring
  rw [e, abs_div, abs_of_pos hU2, div_le_iff₀ hU2]
  have : 1 / (4 * d ^ 2) * |U| * U ^ 2 = |U| ^ 3 / (4 * d ^ 2) := by
    rw [← sq_abs U]; ring
  rw [this]; exact h

/-- **Second-order coefficient of the exact Σ, bonding orbital**:
`(Σ_B(ω) - U·Σ1)/U² → 1/(4(ω - 3t))` as `U → 0` (two-sided). -/
theorem sigEx_B_U2_limit {t ω : ℝ} (ht : 0 < t) (hd : ω - 3 * t ≠ 0) (he : ω + t ≠ 0) :
    Tendsto (fun U => (sigEx t U 0 ω - U / 2) / U ^ 2) (𝓝[≠] 0) (𝓝 (1 / (4 * (ω - 3 * t)))) := by
  refine tendsto_of_abs_le_mul (K := 1 / (4 * (ω - 3 * t) ^ 2))
    (lt_min (half_pos (abs_pos.mpr hd)) (abs_pos.mpr he)) fun U hU hδ => ?_
  have h1 : |U| < |ω - 3 * t| / 2 := lt_of_lt_of_le hδ (min_le_left _ _)
  have h2 : |U| < |ω + t| := lt_of_lt_of_le hδ (min_le_right _ _)
  exact div_sq_bound hU (sigEx_B_expansion ht hd (by linarith) h2)

/-- Same for the antibonding orbital: `→ 1/(4(ω + 3t))`. -/
theorem sigEx_A_U2_limit {t ω : ℝ} (ht : 0 < t) (hd : ω + 3 * t ≠ 0) (he : ω - t ≠ 0) :
    Tendsto (fun U => (sigEx t U 1 ω - U / 2) / U ^ 2) (𝓝[≠] 0) (𝓝 (1 / (4 * (ω + 3 * t)))) := by
  refine tendsto_of_abs_le_mul (K := 1 / (4 * (ω + 3 * t) ^ 2))
    (lt_min (half_pos (abs_pos.mpr he)) (abs_pos.mpr hd)) fun U hU hδ => ?_
  have h1 : |U| < |ω - t| / 2 := lt_of_lt_of_le hδ (min_le_left _ _)
  have h2 : |U| < |ω + 3 * t| := lt_of_lt_of_le hδ (min_le_right _ _)
  exact div_sq_bound hU (sigEx_A_expansion ht hd (by linarith) h2)


/-- The textbook second-order self-energy has the same U² coefficient:
`(sig2dir_B + sig2x_B)(ω)/U² → 1/(4(ω - 3t))`. -/
theorem sig2_B_U2_limit {t ω : ℝ} (hd : ω - 3 * t ≠ 0) :
    Tendsto (fun U => (sig2dir t U 0 ω + sig2x t U 0 ω) / U ^ 2) (𝓝[≠] 0)
      (𝓝 (1 / (4 * (ω - 3 * t)))) := by
  refine tendsto_of_abs_le_mul (K := 1 / (4 * (ω - 3 * t) ^ 2)) (abs_pos.mpr hd) fun U hU hδ => ?_
  have h := rem_bound hd hδ.le
  have e : (sig2dir t U 0 ω + sig2x t U 0 ω) =
      (U / 2 + U ^ 2 / 4 / ((ω - 3 * t) - U / 2)) - U / 2 := by
    rw [sig2_B_eq]; ring_nf
  rw [e]
  refine div_sq_bound hU ?_
  rw [show U / 2 + U ^ 2 / 4 / (ω - 3 * t - U / 2) - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω - 3 * t))))
    = U ^ 2 / 4 / (ω - 3 * t - U / 2) - U ^ 2 * (1 / (4 * (ω - 3 * t))) by ring]
  exact h

/-- Antibonding: `(sig2dir_A + sig2x_A)(ω)/U² → 1/(4(ω + 3t))`. -/
theorem sig2_A_U2_limit {t ω : ℝ} (hd : ω + 3 * t ≠ 0) :
    Tendsto (fun U => (sig2dir t U 1 ω + sig2x t U 1 ω) / U ^ 2) (𝓝[≠] 0)
      (𝓝 (1 / (4 * (ω + 3 * t)))) := by
  refine tendsto_of_abs_le_mul (K := 1 / (4 * (ω + 3 * t) ^ 2)) (abs_pos.mpr hd) fun U hU hδ => ?_
  have h := rem_bound hd hδ.le
  have e : (sig2dir t U 1 ω + sig2x t U 1 ω) =
      (U / 2 + U ^ 2 / 4 / ((ω + 3 * t) - U / 2)) - U / 2 := by
    rw [sig2_A_eq]; ring_nf
  rw [e]
  refine div_sq_bound hU ?_
  rw [show U / 2 + U ^ 2 / 4 / (ω + 3 * t - U / 2) - (U * (1 / 2) + U ^ 2 * (1 / (4 * (ω + 3 * t))))
    = U ^ 2 / 4 / (ω + 3 * t - U / 2) - U ^ 2 * (1 / (4 * (ω + 3 * t))) by ring]
  exact h

/-- In this model the exchange (SOX, spin factor −1) term is exactly `−1/2` of
the direct (ring, spin factor 2) term, for both orbitals and every `E`. -/
theorem sig2x_eq_neg_half_dir (t U E : ℝ) (p : Fin 2) : sig2x t U p E = -(1 / 2) * sig2dir t U p E := by
  fin_cases p
  · show sig2x t U 0 E = -(1 / 2) * sig2dir t U 0 E
    rw [sig2x_B_eq, sig2dir_B_eq]; ring
  · show sig2x t U 1 E = -(1 / 2) * sig2dir t U 1 E
    rw [sig2x_A_eq, sig2dir_A_eq]; ring

/-- **The direct (GW-like) term alone is not the exact Σ**: for `U ≠ 0`, off
the poles, `Σ_B ≠ HF + sig2dir_B` (the difference is `sig2x_B ≠ 0`). -/
theorem sigEx_B_ne_direct_only {t U ω : ℝ} (ht : 0 < t) (hU : U ≠ 0)
    (ha : ω - (E0 t U + t) ≠ 0) (hb : ω - (U + t - E0 t U) ≠ 0) (hc : ω - (3 * t + U / 2) ≠ 0) :
    sigEx t U 0 ω ≠ (epsOrb t U 0 - eps0 t 0) + sig2dir t U 0 ω := by
  rw [sigEx_B ht ha hb hc]; intro h
  have h0 : sig2x t U 0 ω = 0 := by linarith
  rw [sig2x_B_eq, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hU (by nlinarith [sq_nonneg U])
  · exact hc h0

theorem sigEx_A_ne_direct_only {t U ω : ℝ} (ht : 0 < t) (hU : U ≠ 0)
    (ha : ω - (E0 t U - t) ≠ 0) (hb : ω - (U - t - E0 t U) ≠ 0) (hc : ω - (U / 2 - 3 * t) ≠ 0) :
    sigEx t U 1 ω ≠ (epsOrb t U 1 - eps0 t 1) + sig2dir t U 1 ω := by
  rw [sigEx_A ht ha hb hc]; intro h
  have h0 : sig2x t U 1 ω = 0 := by linarith
  rw [sig2x_A_eq, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hU (by nlinarith [sq_nonneg U])
  · exact hc h0


/-! ### The Lehmann sum is the resolvent matrix element -/

theorem hopZ_symm : hopZᵀ = hopZ := by decide +kernel
theorem dblZ_symm : dblZᵀ = dblZ := by decide +kernel

/-- `H` is symmetric (real Hermitian). -/
theorem H_symm (t U : ℝ) : (H t U)ᵀ = H t U := by
  rw [H, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    ← Matrix.transpose_map, ← Matrix.transpose_map, hopZ_symm, dblZ_symm]

/-- Resolvent in an eigenbasis: for a symmetric `M` with a complete orthogonal
eigenbasis `v` of a subspace `S`, and `z` not an eigenvalue, the unique
solution `y ∈ S` of `(z - M) y = b` (`b ∈ S`) is `Σ_k (v_k·b)/(|v_k|²(z - e_k)) v_k`. -/
theorem sector_resolvent {M : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mᵀ = M)
    {v : Fin 4 → Fin 16 → ℝ} {e : Fin 4 → ℝ} (heig : ∀ k, M *ᵥ v k = e k • v k)
    {S : (Fin 16 → ℝ) → Prop} (hcomp : ∀ y, S y → y = ∑ k, ((v k ⬝ᵥ y) / (v k ⬝ᵥ v k)) • v k)
    {z : ℝ} (hz : ∀ k, z - e k ≠ 0) {b y : Fin 16 → ℝ} (hb : S b) (hy : S y) :
    z • y - M *ᵥ y = b ↔ y = ∑ k, ((v k ⬝ᵥ b) / (v k ⬝ᵥ v k) / (z - e k)) • v k := by
  constructor
  · intro h
    have hc : ∀ k, v k ⬝ᵥ b = (z - e k) * (v k ⬝ᵥ y) := by
      intro k
      rw [← h, dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        hM, heig, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
    conv_lhs => rw [hcomp y hy]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc k]; congr 1; rw [div_right_comm, mul_div_cancel_left₀ _ (hz k)]
  · intro h
    rw [h, show M *ᵥ (∑ k, ((v k ⬝ᵥ b) / (v k ⬝ᵥ v k) / (z - e k)) • v k) =
      ∑ k, M *ᵥ (((v k ⬝ᵥ b) / (v k ⬝ᵥ v k) / (z - e k)) • v k) by
        simp only [Fin.sum_univ_four, Matrix.mulVec_add], Finset.smul_sum, ← Finset.sum_sub_distrib]
    conv_rhs => rw [hcomp b hb]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, heig, smul_comm z, smul_smul, smul_smul, ← sub_smul, ← mul_sub,
      div_mul_cancel₀ _ (hz k)]

theorem sum_sector {N : ℕ} {v : Fin 4 → Fin 16 → ℝ} (hv : ∀ k, InSector N (v k)) (c : Fin 4 → ℝ) :
    InSector N (∑ k, c k • v k) := by
  intro s hs; simp [Finset.sum_apply, hv _ s hs]

theorem creO_psi0_sector (t U : ℝ) (q : Fin 2) : InSector 3 (creO q *ᵥ psi0 t U) := by
  intro s hs
  fin_cases q
  · show (creO 0 *ᵥ psi0 t U) s = 0
    rw [creB_psi0, Pi.smul_apply, ev3_sector 0 s hs, smul_zero]
  · show (creO 1 *ᵥ psi0 t U) s = 0
    rw [creA_psi0, Pi.smul_apply, ev3_sector 1 s hs, smul_zero]

theorem annO_psi0_sector (t U : ℝ) (p : Fin 2) : InSector 1 (annO p *ᵥ psi0 t U) := by
  intro s hs
  fin_cases p
  · show (annO 0 *ᵥ psi0 t U) s = 0
    rw [annB_psi0, Pi.smul_apply, ev1_sector 2 s hs, smul_zero]
  · show (annO 1 *ᵥ psi0 t U) s = 0
    rw [annA_psi0, Pi.smul_apply, ev1_sector 3 s hs, smul_zero]

/-- **Lehmann = resolvent.** Off the poles, for ANY `xP` in the N = 3 sector with
`(ω + E0 - H) xP = c†_q ψ0` and ANY `xH` in the N = 1 sector with
`(ω - E0 + H) xH = c_p ψ0` (such solutions exist, `Gex_resolvent_exists`),
`G_pq(ω) = (<c†_p ψ0, xP> + <c_q ψ0, xH>)/|ψ0|²`, i.e.
`G_pq(ω) = <ψ0|c_p (ω - (H - E0))⁻¹ c†_q|ψ0> + <ψ0|c†_q (ω + (H - E0))⁻¹ c_p|ψ0>`. -/
theorem Gex_resolvent {t U ω : ℝ} (p q : Fin 2)
    (hP : ∀ k, (ω + E0 t U) - en3 t U k ≠ 0) (hH : ∀ k, (ω - E0 t U) - (-en1 t k) ≠ 0)
    {xP xH : Fin 16 → ℝ} (sP : InSector 3 xP) (sH : InSector 1 xH)
    (eP : (ω + E0 t U) • xP - H t U *ᵥ xP = creO q *ᵥ psi0 t U)
    (eH : (ω - E0 t U) • xH - (-H t U) *ᵥ xH = annO p *ᵥ psi0 t U) :
    Gex t U p q ω = ((creO p *ᵥ psi0 t U) ⬝ᵥ xP + (annO q *ᵥ psi0 t U) ⬝ᵥ xH) /
      (psi0 t U ⬝ᵥ psi0 t U) := by
  have rP := (sector_resolvent (H_symm t U) (ev3_eigen t U) (S := InSector 3) ev3_complete hP
    (creO_psi0_sector t U q) sP).1 eP
  have hsymm : (-H t U)ᵀ = -H t U := by rw [Matrix.transpose_neg, H_symm]
  have heig : ∀ k, (-H t U) *ᵥ ev1 k = (-en1 t k) • ev1 k := fun k => by
    rw [Matrix.neg_mulVec, ev1_eigen, neg_smul]
  have rH := (sector_resolvent hsymm heig (S := InSector 1) ev1_complete hH
    (annO_psi0_sector t U p) sH).1 eH
  rw [rP, rH, add_div]
  unfold Gex GL
  simp only [Fin.sum_univ_four, dotProduct_add, dotProduct_smul, smul_eq_mul, add_div]
  have e3 : ∀ k, ω + E0 t U - en3 t U k = ω - (en3 t U k - E0 t U) := fun k => by ring
  have e1 : ∀ k, ω - E0 t U - -en1 t k = ω - (E0 t U - en1 t k) := fun k => by ring
  simp only [e3, e1, dotProduct_comm (creO p *ᵥ psi0 t U), dotProduct_comm (annO q *ᵥ psi0 t U)]
  ring

/-- Existence of the resolvent solutions used in `Gex_resolvent`. -/
theorem Gex_resolvent_exists {t U ω : ℝ} (p q : Fin 2)
    (hP : ∀ k, (ω + E0 t U) - en3 t U k ≠ 0) (hH : ∀ k, (ω - E0 t U) - (-en1 t k) ≠ 0) :
    (∃ xP, InSector 3 xP ∧ (ω + E0 t U) • xP - H t U *ᵥ xP = creO q *ᵥ psi0 t U) ∧
      ∃ xH, InSector 1 xH ∧ (ω - E0 t U) • xH - (-H t U) *ᵥ xH = annO p *ᵥ psi0 t U := by
  have hsymm : (-H t U)ᵀ = -H t U := by rw [Matrix.transpose_neg, H_symm]
  have heig : ∀ k, (-H t U) *ᵥ ev1 k = (-en1 t k) • ev1 k := fun k => by
    rw [Matrix.neg_mulVec, ev1_eigen, neg_smul]
  have s3 := sum_sector ev3_sector
  have s1 := sum_sector ev1_sector
  exact ⟨⟨_, s3 _, ((sector_resolvent (H_symm t U) (ev3_eigen t U) (S := InSector 3) ev3_complete hP
    (creO_psi0_sector t U q) (s3 _)).2 rfl)⟩,
    ⟨_, s1 _, ((sector_resolvent hsymm heig (S := InSector 1) ev1_complete hH
    (annO_psi0_sector t U p) (s1 _)).2 rfl)⟩⟩

end GW.Endpoint.HubbardDimer

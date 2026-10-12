/-
A3(a): real-level facts on the doubled space `Kap n = Fock n ⊕ Fock n` used to
extract the coefficients of the Feshbach form.

* `Ar x`: column `p` is `(c_p† x, c_p x)`; `A0 = Ar Φ` has orthonormal columns
  (`A0_gram`) that are eigenvectors of `𝓗0 = Hr (H0 - E0)` (`H0r_A0`);
* `Y2`: column `q` is `(y2p q, y2h q)`, the 2p1h / 2h1p vectors; `A0ᵀ Y2 = 0`;
* `first_order_cols`: `𝓗0 A1 + 𝓗1 A0 - A1 ε = Y2 + A0 Σ1` (this is where the
  commutators `[V, c_q†] Φ`, `[c_q, V] Φ` and the first-order eigenvalue equation
  enter);
* `L0_mul_N0`: an explicit inverse of the constant term `ω - Q0 𝓗0 Q0`;
* `L0_Y2`: on `Y2` that inverse is the diagonal resolvent `Dk`.
-/
import GW.Endpoint.ManyBody.Bridge

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

noncomputable def Ar (x : Fock n → ℝ) : Matrix (Kap n) (Fin n) ℝ :=
  fromRows (colM fun p => cre p *ᵥ x) (colM fun p => ann p *ᵥ x)

noncomputable def Hr (M : Matrix (Fock n) (Fock n) ℝ) : Matrix (Kap n) (Kap n) ℝ :=
  fromBlocks M 0 0 (-M)

noncomputable def Dk : Matrix (Kap n) (Kap n) ℝ := fromBlocks (Dp ε O ω) 0 0 (Dm ε O ω)

noncomputable def Y2 : Matrix (Kap n) (Fin n) ℝ :=
  fromRows (colM fun q => y2p v O q) (colM fun q => y2h v O q)

noncomputable def sig1M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (sig1 v O)

/-- The constant term of `ω - Q 𝓗 Q`. -/
noncomputable def N0 : Matrix (Kap n) (Kap n) ℝ :=
  ω • 1 - (1 - Ar (phi O) * (Ar (phi O))ᵀ) * Hr (H0 ε - E0 ε O • 1) *
    (1 - Ar (phi O) * (Ar (phi O))ᵀ)

/-- Its explicit inverse. -/
noncomputable def L0 : Matrix (Kap n) (Kap n) ℝ :=
  ω⁻¹ • (Ar (phi O) * (Ar (phi O))ᵀ) + Dk ε O ω * (1 - Ar (phi O) * (Ar (phi O))ᵀ)

variable {ε v O ω}

theorem colM_mul_diagonal {ι : Type*} (f : Fin n → ι → ℝ) (d : Fin n → ℝ) :
    colM f * diagonal d = colM fun p => d p • f p := by
  ext S p; simp [colM, mul_diagonal, mul_comm]

theorem colM_mul {ι : Type*} (f : Fin n → ι → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    colM f * M = colM fun q => ∑ p, M p q • f p := by
  ext S q; simp [colM, mul_apply, Finset.sum_apply, mul_comm]

theorem colM_add {ι : Type*} (f g : Fin n → ι → ℝ) : colM f + colM g = colM fun p => f p + g p := by
  ext; simp [colM]

theorem colM_sub {ι : Type*} (f g : Fin n → ι → ℝ) : colM f - colM g = colM fun p => f p - g p := by
  ext; simp [colM]

theorem colM_zero {ι : Type*} : colM (fun _ : Fin n => (0 : ι → ℝ)) = 0 := by ext; simp [colM]

theorem A0_gram : (Ar (phi O))ᵀ * Ar (phi O) = 1 := by
  rw [Ar, transpose_fromRows, fromCols_mul_fromRows, colM_transpose_mul_colM,
    colM_transpose_mul_colM]
  ext p q
  simp only [add_apply, of_apply, dot_cre_phi, dot_ann_phi, one_apply]
  by_cases h : p = q
  · subst h; by_cases hp : p ∈ O <;> simp [hp]
  · simp [h]

theorem H0r_A0 : Hr (H0 ε - E0 ε O • 1) * Ar (phi O) = Ar (phi O) * diagonal ε := by
  rw [Hr, Ar, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
    zero_add, mul_colM, mul_colM, colM_mul_diagonal, colM_mul_diagonal]
  have e1 : (fun p => (H0 ε - E0 ε O • 1) *ᵥ cre p *ᵥ phi O) = fun p => ε p • cre p *ᵥ phi O := by
    funext p
    rw [sub_smul_one_mulVec, ((phi_isEig ε O).cre p), E0, add_smul, add_sub_cancel_left]
  have e2 : (fun p => -(H0 ε - E0 ε O • 1) *ᵥ ann p *ᵥ phi O) = fun p => ε p • ann p *ᵥ phi O := by
    funext p
    rw [neg_mulVec, sub_smul_one_mulVec, ((phi_isEig ε O).ann p), E0, sub_smul, sub_sub_cancel_left,
      neg_neg]
  rw [e1, e2]

theorem Hr_transpose (M : Matrix (Fock n) (Fock n) ℝ) (hM : Mᵀ = M) : (Hr M)ᵀ = Hr M := by
  rw [Hr, fromBlocks_transpose, transpose_neg, hM, transpose_zero]

theorem H0mE0_transpose : (H0 ε - E0 ε O • (1 : Matrix (Fock n) (Fock n) ℝ))ᵀ =
    H0 ε - E0 ε O • 1 := by
  rw [transpose_sub, transpose_smul, transpose_one, H0_transpose]

theorem A0_H0r : (Ar (phi O))ᵀ * Hr (H0 ε - E0 ε O • 1) = diagonal ε * (Ar (phi O))ᵀ := by
  have h := congrArg transpose (H0r_A0 (ε := ε) (O := O))
  rwa [transpose_mul, transpose_mul, Hr_transpose _ H0mE0_transpose, diagonal_transpose] at h

theorem A0_Y2 : (Ar (phi O))ᵀ * Y2 v O = 0 := by
  rw [Ar, Y2, transpose_fromRows, fromCols_mul_fromRows, colM_transpose_mul_colM,
    colM_transpose_mul_colM]
  ext p q
  simp only [add_apply, of_apply, zero_apply, y2p, y2h, dotProduct_smul, dot_sum', smul_eq_mul]
  rw [sum_eq_zero fun r hr => sum_eq_zero fun s hs => sum_eq_zero fun a _ => by
      rw [orth_1p_2p1h p (mem_compl.mp hr) (mem_compl.mp hs), mul_zero],
    sum_eq_zero fun r hr => sum_eq_zero fun a _ => sum_eq_zero fun b _ => by
      rw [orth_1h_2h1p p (mem_compl.mp hr), mul_zero]]
  simp

theorem fromRows_add' {R : Type*} [Add R] {m₁ m₂ k : Type*} (A B : Matrix m₁ k R)
    (C D : Matrix m₂ k R) : fromRows A C + fromRows B D = fromRows (A + B) (C + D) := by
  ext (i | i) j <;> simp

theorem fromRows_sub' {R : Type*} [Sub R] {m₁ m₂ k : Type*} (A B : Matrix m₁ k R)
    (C D : Matrix m₂ k R) : fromRows A C - fromRows B D = fromRows (A - B) (C - D) := by
  ext (i | i) j <;> simp

theorem Hr_mul_Ar (M : Matrix (Fock n) (Fock n) ℝ) (x : Fock n → ℝ) :
    Hr M * Ar x = fromRows (colM fun p => M *ᵥ cre p *ᵥ x) (colM fun p => -M *ᵥ ann p *ᵥ x) := by
  rw [Hr, Ar, fromBlocks_mul_fromRows, Matrix.zero_mul, Matrix.zero_mul, add_zero, zero_add,
    mul_colM, mul_colM]

theorem Ar_mul (x : Fock n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Ar x * M = fromRows (colM fun q => ∑ p, M p q • (cre p *ᵥ x))
      (colM fun q => ∑ p, M p q • (ann p *ᵥ x)) := by
  rw [Ar, fromRows_mul, colM_mul, colM_mul]

/-- Particle columns of the first-order residual. -/
theorem first_order_part (hnd : NonDeg ε O) (hv1 : ∀ p q r s, v p q r s = v q p s r) (q : Fin n) :
    (H0 ε - E0 ε O • 1) *ᵥ cre q *ᵥ psi1 ε v O + (vop v - E1 v O • 1) *ᵥ cre q *ᵥ phi O -
        ε q • cre q *ᵥ psi1 ε v O =
      y2p v O q + ∑ p, sig1 v O p q • (cre p *ᵥ phi O) := by
  have h1 := eig_order1 (v := v) hnd
  have hc : H0 ε *ᵥ cre q *ᵥ psi1 ε v O = cre q *ᵥ H0 ε *ᵥ psi1 ε v O + ε q • cre q *ᵥ psi1 ε v O := by
    rw [mulVec_mulVec, H0_mul_cre, add_mulVec, ← mulVec_mulVec, smul_mulVec_assoc]
  have hv : vop v *ᵥ cre q *ᵥ phi O = cre q *ᵥ vop v *ᵥ phi O + ccre v q *ᵥ phi O := by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, ← vop_mul_cre, add_sub_cancel]
  rw [sub_smul_one_mulVec, sub_smul_one_mulVec, hc, hv, ccre_phi hv1]
  have h1' : H0 ε *ᵥ psi1 ε v O = E0 ε O • psi1 ε v O - (vop v *ᵥ phi O - E1 v O • phi O) := by
    rw [← sub_eq_zero, ← h1]; abel
  rw [h1', mulVec_sub, mulVec_sub]
  simp only [mulVec_smul]
  rw [sum_univ_eq_sum_of Oᶜ _ (fun p hp => by
    rw [cre_phi (by simpa using hp), smul_zero])]
  abel

/-- Hole columns of the first-order residual. -/
theorem first_order_hole (hnd : NonDeg ε O) (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (q : Fin n) :
    -(H0 ε - E0 ε O • 1) *ᵥ ann q *ᵥ psi1 ε v O + -(vop v - E1 v O • 1) *ᵥ ann q *ᵥ phi O -
        ε q • ann q *ᵥ psi1 ε v O =
      y2h v O q + ∑ p, sig1 v O p q • (ann p *ᵥ phi O) := by
  have h1 := eig_order1 (v := v) hnd
  have hc : H0 ε *ᵥ ann q *ᵥ psi1 ε v O = ann q *ᵥ H0 ε *ᵥ psi1 ε v O - ε q • ann q *ᵥ psi1 ε v O := by
    rw [mulVec_mulVec, H0_mul_ann, sub_mulVec, ← mulVec_mulVec, smul_mulVec_assoc]
  have hv : vop v *ᵥ ann q *ᵥ phi O = ann q *ᵥ vop v *ᵥ phi O - cann v q *ᵥ phi O := by
    rw [mulVec_mulVec, mulVec_mulVec, ← sub_mulVec, ← ann_mul_vop v hv1, sub_sub_cancel]
  rw [neg_mulVec, neg_mulVec, sub_smul_one_mulVec, sub_smul_one_mulVec, hc, hv, cann_phi]
  have h1' : H0 ε *ᵥ psi1 ε v O = E0 ε O • psi1 ε v O - (vop v *ᵥ phi O - E1 v O • phi O) := by
    rw [← sub_eq_zero, ← h1]; abel
  rw [h1', mulVec_sub, mulVec_sub]
  simp only [mulVec_smul]
  rw [sum_univ_eq_sum_of O _ (fun p hp => by rw [ann_phi hp, smul_zero])]
  rw [sum_congr rfl fun a _ => by rw [sig1_symm hv1 hv2 q a]]
  abel

/-- **First-order columns**: `𝓗0 A1 + 𝓗1 A0 - A1 ε = Y2 + A0 Σ1`. -/
theorem first_order_cols (hnd : NonDeg ε O) (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) :
    Hr (H0 ε - E0 ε O • 1) * Ar (psi1 ε v O) + Hr (vop v - E1 v O • 1) * Ar (phi O) -
        Ar (psi1 ε v O) * diagonal ε = Y2 v O + Ar (phi O) * sig1M v O := by
  have hd : Ar (psi1 ε v O) * diagonal ε = fromRows (colM fun p => ε p • cre p *ᵥ psi1 ε v O)
      (colM fun p => ε p • ann p *ᵥ psi1 ε v O) := by
    rw [Ar, fromRows_mul, colM_mul_diagonal, colM_mul_diagonal]
  rw [Hr_mul_Ar, Hr_mul_Ar, Ar_mul (phi O), hd, fromRows_add', fromRows_sub', Y2, fromRows_add',
    colM_add, colM_add, colM_sub, colM_sub, colM_add, colM_add]
  simp only [first_order_part hnd hv1, first_order_hole hnd hv1 hv2, sig1M, of_apply]

/-! ### The constant term of `ω - Q 𝓗 Q` and its inverse -/

theorem H0mE0_diag : H0 ε - E0 ε O • (1 : Matrix (Fock n) (Fock n) ℝ) =
    diagonal fun S => energy ε S - energy ε O := by
  rw [H0_eq_diagonal, smul_one_eq_diagonal, diagonal_sub]; rfl

theorem Dk_mul (hω : OffPoles ε O ω) :
    Dk ε O ω * (ω • (1 : Matrix (Kap n) (Kap n) ℝ) - Hr (H0 ε - E0 ε O • 1)) = 1 := by
  rw [Dk, Hr, ← fromBlocks_one, fromBlocks_smul, H0mE0_diag]
  rw [show fromBlocks (ω • (1 : Matrix (Fock n) (Fock n) ℝ)) (ω • 0) (ω • 0) (ω • 1) -
      fromBlocks (diagonal fun S => energy ε S - energy ε O) 0 0
        (-diagonal fun S => energy ε S - energy ε O) =
      fromBlocks (diagonal fun S => ω - (energy ε S - energy ε O)) 0 0
        (diagonal fun S => ω + (energy ε S - energy ε O)) by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [diagonal, one_apply, h] <;> ring]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Dp, Dm]
  rw [diag_inv_mul _ fun S => (hω S).1, diag_inv_mul _ fun S => (hω S).2, fromBlocks_one]

theorem omega_ne_zero (hω : OffPoles ε O ω) : ω ≠ 0 := by
  have := (hω O).1; simpa using this

/-- A ring identity: the explicit inverse of `c - Q H Q` for a projector `P = 1 - Q`
commuting with `H`, a central `c` and a left inverse `D` of `c - H`. -/
theorem proj_inverse {R : Type*} [Ring R] (c ci P H D : R) (hci : ci * c = 1)
    (hc : ∀ x, c * x = x * c) (hPP : P * P = P) (hHP : H * P = P * H) (hD : D * (c - H) = 1) :
    (ci * P + D * (1 - P)) * (c - (1 - P) * H * (1 - P)) = 1 := by
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    have : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by noncomm_ring
    rw [this, hPP, sub_self, sub_zero]
  have hQH' : (1 - P) * H = H * (1 - P) := by
    have : (1 - P) * H - H * (1 - P) = H * P - P * H := by noncomm_ring
    rw [← sub_eq_zero, this, hHP, sub_self]
  have hQH : (1 - P) * H * (1 - P) = H * (1 - P) := by rw [hQH', mul_assoc, hQQ]
  rw [hQH]
  have h1 : ci * P * c = P := by rw [mul_assoc, ← hc, ← mul_assoc, hci, one_mul]
  have h2 : P * (H * (1 - P)) = 0 := by
    rw [← mul_assoc, ← hHP, mul_assoc, mul_sub, mul_one, hPP, sub_self, mul_zero]
  have h3 : D * (1 - P) * (c - H * (1 - P)) = D * (c - H) * (1 - P) := by
    calc D * (1 - P) * (c - H * (1 - P)) = D * ((1 - P) * c) - D * ((1 - P) * H * (1 - P)) := by
          noncomm_ring
      _ = D * (c * (1 - P)) - D * (H * (1 - P)) := by rw [hc (1 - P), hQH]
      _ = D * (c - H) * (1 - P) := by noncomm_ring
  calc (ci * P + D * (1 - P)) * (c - H * (1 - P))
      = ci * P * c - ci * (P * (H * (1 - P))) + D * (1 - P) * (c - H * (1 - P)) := by noncomm_ring
    _ = 1 := by rw [h1, h2, h3, hD, mul_zero, sub_zero, one_mul]; noncomm_ring

theorem L0_mul_N0 (hω : OffPoles ε O ω) : L0 ε O ω * N0 ε O ω = 1 := by
  have hω0 := omega_ne_zero hω
  have hAA := A0_gram (O := O)
  set A := Ar (phi O)
  set H := Hr (H0 ε - E0 ε O • 1)
  have hPP : A * Aᵀ * (A * Aᵀ) = A * Aᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hAA, Matrix.one_mul]
  have hHP : H * (A * Aᵀ) = A * Aᵀ * H := by
    rw [← Matrix.mul_assoc, H0r_A0, Matrix.mul_assoc, Matrix.mul_assoc, ← A0_H0r]
  have key := proj_inverse (ω • (1 : Matrix (Kap n) (Kap n) ℝ)) (ω⁻¹ • 1) (A * Aᵀ) H (Dk ε O ω)
    (by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hω0, one_smul])
    (fun x => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
    hPP hHP (Dk_mul hω)
  rw [L0, N0]
  rw [Matrix.smul_mul, Matrix.one_mul] at key
  exact key

theorem L0_Y2 : L0 ε O ω * Y2 v O = Dk ε O ω * Y2 v O := by
  rw [L0, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, A0_Y2, Matrix.mul_zero, smul_zero,
    zero_add, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, A0_Y2,
    Matrix.mul_zero, sub_zero]

/-- The dynamic second-order term: `Y2ᵀ Dk Y2 = Σ2(2p1h) + Σ2(2h1p)`. -/
theorem Y2_Dk_Y2 (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) :
    (Y2 v O)ᵀ * Dk ε O ω * Y2 v O = Matrix.of fun p q => sig2p ε v O ω p q + sig2h ε v O ω p q := by
  rw [Y2, Dk, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_colM, mul_colM, colM_transpose_mul_colM,
    colM_transpose_mul_colM]
  ext p q
  simp only [add_apply, of_apply, dyn_particle hv1 hv2, dyn_hole hv1 hv2]

end GW.Endpoint.ManyBody

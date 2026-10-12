/-
G2-coulomb (12/n): the averages are invariant under the 12 signed coordinate permutations
(`cavg_symm`): they preserve the metric `B` (equal diagonal, equal off-diagonal entries), map the
cell `P` onto itself (`symOK`: the 26 normals are permuted) and preserve volume (`|det| = 1`).
-/
import GW.Endpoint.Coulomb.Average
import GW.Endpoint.Coulomb.SymmDefs

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset

noncomputable def sR (g : SG) : ℝ := if g.neg then -1 else 1

theorem sR_sq (g : SG) : sR g * sR g = 1 := by unfold sR; split_ifs <;> norm_num

/-- The action on points. -/
noncomputable def gF (g : SG) (x : E3) : E3 := fun i => sR g * x (g.pm i)

theorem valid_cases (g : SG) (hv : g.valid = true) :
    (g.a = 0 ∧ g.b = 1 ∧ g.c = 2) ∨ (g.a = 0 ∧ g.b = 2 ∧ g.c = 1) ∨ (g.a = 1 ∧ g.b = 0 ∧ g.c = 2) ∨
    (g.a = 1 ∧ g.b = 2 ∧ g.c = 0) ∨ (g.a = 2 ∧ g.b = 0 ∧ g.c = 1) ∨ (g.a = 2 ∧ g.b = 1 ∧ g.c = 0) := by
  obtain ⟨a, b, c, n⟩ := g
  simp only [SG.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

theorem sum_pm (g : SG) (hv : g.valid = true) (f : Fin 3 → ℝ) : ∑ i, f (g.pm i) = ∑ i, f i := by
  simp only [Fin.sum_univ_three, SG.pm]
  rcases valid_cases g hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3] <;> ring

theorem pm_iv (g : SG) (hv : g.valid = true) (j : Fin 3) : g.pm (g.iv j) = j := by
  rcases valid_cases g hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ <;> fin_cases j <;> simp [SG.iv, SG.pm, h1, h2, h3]

theorem iv_pm (g : SG) (hv : g.valid = true) (i : Fin 3) : g.iv (g.pm i) = i := by
  rcases valid_cases g hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ <;> fin_cases i <;> simp [SG.iv, SG.pm, h1, h2, h3]

theorem inv_pm (g : SG) (i : Fin 3) : g.inv.pm i = g.iv i := by fin_cases i <;> rfl

theorem gF_inv_gF (g : SG) (hv : g.valid = true) (x : E3) : gF g.inv (gF g x) = x := by
  funext i; simp only [gF, inv_pm, pm_iv g hv]
  have : sR g.inv = sR g := rfl
  rw [this, ← mul_assoc, sR_sq, one_mul]

theorem gF_gF_inv (g : SG) (hv : g.valid = true) (x : E3) : gF g (gF g.inv x) = x := by
  funext i; simp only [gF, inv_pm, iv_pm g hv]
  have : sR g.inv = sR g := rfl
  rw [this, ← mul_assoc, sR_sq, one_mul]

/-! ### The metric is invariant -/

def Bp : ℤ := 20263033028603940
def Bq : ℤ := -6754344342867979

theorem Bmat_eq (i j : Fin 3) : Bmat i j = if i = j then (Bp : ℝ) / 2 ^ 54 else (Bq : ℝ) / 2 ^ 54 := by
  fin_cases i <;> fin_cases j <;> simp [Bmat, IM.rw, Bint, IV.g, Bp, Bq]

theorem bil_closed (x y : E3) :
    QB.bil x y = (((Bp : ℝ) - Bq) * ∑ i, x i * y i + Bq * (∑ i, x i) * (∑ i, y i)) / 2 ^ 54 := by
  show ∑ i, ∑ j, Bmat i j * x i * y j = _
  simp only [Bmat_eq, Fin.sum_univ_three]
  simp; ring

theorem bil_gF (g : SG) (hv : g.valid = true) (x y : E3) : QB.bil (gF g x) (gF g y) = QB.bil x y := by
  rw [bil_closed, bil_closed]
  simp only [gF]
  have e1 : ∑ i, sR g * x (g.pm i) * (sR g * y (g.pm i)) = ∑ i, x i * y i := by
    rw [← sum_pm g hv (fun i => x i * y i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := sR_sq g; linear_combination (x (g.pm i) * y (g.pm i)) * this
  have e2 : ∀ z : E3, ∑ i, sR g * z (g.pm i) = sR g * ∑ i, z i := by
    intro z; rw [← Finset.mul_sum, sum_pm g hv z]
  rw [e1, e2 x, e2 y]
  have := sR_sq g
  congr 1; linear_combination ((Bq : ℝ) * (∑ i, x i) * (∑ i, y i)) * this

theorem q_gF (g : SG) (hv : g.valid = true) (x : E3) : QB.q (gF g x) = QB.q x := bil_gF g hv x x

theorem fk_gF (g : SG) (hv : g.valid = true) (k : ℕ) (x : E3) : QB.fk k (gF g x) = QB.fk k x := by
  unfold QF.fk; rw [q_gF g hv]

theorem gF_add (g : SG) (x y : E3) : gF g (x + y) = gF g x + gF g y := by
  funext i; simp [gF]; ring

theorem gF_r (g : SG) (n : IV) : gF g (n.r 2) = (g.actI n).r 2 := by
  funext i; simp only [gF, IV.r]
  fin_cases i <;> simp [SG.actI, IV.g, sR] <;> split_ifs <;> ring

theorem sym_ok : symOK cellNs = true := by decide +kernel

theorem G12_facts {g : SG} (hg : g ∈ G12) :
    g.valid = true ∧ g.inv ∈ G12 ∧ ∀ n ∈ cellNs, g.actI n ∈ cellNs := by
  have h := sym_ok
  simp only [symOK, List.all_eq_true, Bool.and_eq_true, List.elem_eq_mem, decide_eq_true_eq] at h
  obtain ⟨⟨a, b⟩, c⟩ := h g hg
  exact ⟨a, b, c⟩

theorem gF_mem {g : SG} (hg : g ∈ G12) {u : E3} (hu : u ∈ cellP) : gF g u ∈ cellP := by
  obtain ⟨hv, hinv, -⟩ := G12_facts hg
  obtain ⟨hv', -, hcl'⟩ := G12_facts hinv
  intro n hn
  have hm : n.r 2 = gF g ((g.inv.actI n).r 2) := by rw [← gF_r, gF_gF_inv g hv]
  rw [hm, bil_gF g hv, q_gF g hv]
  exact hu _ (hcl' n hn)

theorem gF_pre {g : SG} (hg : g ∈ G12) : gF g ⁻¹' cellP = cellP := by
  obtain ⟨hv, hinv, -⟩ := G12_facts hg
  ext u; constructor
  · intro h; have := gF_mem hinv h; rwa [gF_inv_gF g hv] at this
  · exact gF_mem hg

/-- The matrix of `gF`. -/
noncomputable def gMat (g : SG) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if g.pm i = j then sR g else 0

theorem mv_gMat (g : SG) : mv (gMat g) = gF g := by
  funext x i
  simp only [mv, gMat, Matrix.mulVec, dotProduct, gF, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

theorem gMat_det (g : SG) (hv : g.valid = true) : |(gMat g).det| = 1 := by
  rw [Matrix.det_fin_three]
  have hs : sR g = 1 ∨ sR g = -1 := by unfold sR; split_ifs <;> simp
  rcases valid_cases g hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ <;> rcases hs with hs | hs <;> simp [gMat, SG.pm, h1, h2, h3, hs]

theorem gF_mp {g : SG} (hg : g ∈ G12) : MeasurePreserving (gF g) volume volume := by
  have hv := (G12_facts hg).1
  have hdet := gMat_det g hv
  have hd0 : (gMat g).det ≠ 0 := by intro h; rw [h] at hdet; simp at hdet
  rw [← mv_gMat, mv_eq]
  refine ⟨(Matrix.toLin' (gMat g)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', abs_inv, hdet]
  simp

theorem gF_emb {g : SG} (hg : g ∈ G12) : MeasurableEmbedding (gF g) := by
  obtain ⟨hv, -, -⟩ := G12_facts hg
  have hinj : Function.Injective (gF g) := fun x y h => by
    rw [← gF_inv_gF g hv x, h, gF_inv_gF g hv y]
  rw [← mv_gMat, mv_eq] at hinj ⊢
  exact (Matrix.toLin' (gMat g)).continuous_of_finiteDimensional.measurableEmbedding hinj
    |> fun h => by
      exact (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- **Symmetry of the averages.** -/
theorem cavg_symm {g : SG} (hg : g ∈ G12) (k : ℕ) (Q : E3) : cavg k (gF g Q) = cavg k Q := by
  obtain ⟨hv, hinv, -⟩ := G12_facts hg
  unfold cavg
  congr 1
  have e : ∀ u, QB.fk k (gF g Q + u) = (fun w => QB.fk k (Q + w)) (gF g.inv u) := by
    intro u
    conv_lhs => rw [← gF_gF_inv g hv u, ← gF_add, fk_gF g hv]
  simp_rw [e]
  have := (gF_mp hinv).setIntegral_preimage_emb (gF_emb hinv) (fun w => QB.fk k (Q + w)) cellP
  rw [gF_pre hinv] at this
  exact this

theorem keyQ_act (g : SG) (key : ℤ × ℤ × ℤ) : keyQ (g.actK key) = gF g (keyQ key) := by
  simp only [keyQ, gF_r]
  rfl

end GW.Endpoint.Coulomb

/-
G2-coulomb (11/n): the mini-BZ averages and their exact reduction for a given key.

`cavg k Q = (1/|P|) ∫_P 8π |Q + u|_B^{-k} du` (`P = cellP`, crystal coordinates; `k = 2`:
BerkeleyGW's `vbar`, `k = 1`: `oneoverq`), `vbTrue key = cavg 2 (key/2)`, `oqTrue key = cavg 1 (key/2)`.
`cavg_formula`: `cavg k Q = 64 π Σ_i sg(c₀ⁱ(Q)) Cc k Q i 0`; the integer images of all quantities
for `Q = key/2` (`alN`, `detN`, `qcOf`).
-/
import GW.Endpoint.Coulomb.Cell
import GW.Endpoint.Coulomb.CheckSound

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

/-- The mini-BZ average of `8π |Q + p|_B^{-k}` over the Wigner–Seitz cell `P`. -/
noncomputable def cavg (k : ℕ) (Q : E3) : ℝ :=
  8 * Real.pi / (volume cellP).toReal * ∫ u in cellP, QB.fk k (Q + u)

/-- `key = 2Q` in crystal coordinates. -/
noncomputable def keyQ (key : ℤ × ℤ × ℤ) : E3 := (keyIV key).r 2

/-- `vbar(Q) = (1/|P|) ∫_P 8π / |Q+p|²_B dp` at `Q = key/2`. -/
noncomputable def vbTrue (key : ℤ × ℤ × ℤ) : ℝ := cavg 2 (keyQ key)

/-- `oneoverq(q) = (1/|P|) ∫_P 8π / |q+p|_B dp` at `q = key/2`. -/
noncomputable def oqTrue (key : ℤ × ℤ × ℤ) : ℝ := cavg 1 (keyQ key)

theorem volume_cell_real : (volume cellP).toReal = 1 / 8 := by
  rw [volume_cell, ENNReal.toReal_ofReal (by norm_num)]

theorem cavg_formula (k : ℕ) (hk : k ≤ 2) (Q : E3) :
    cavg k Q = 64 * Real.pi * ∑ i : Fin 72, sg ((tetQ i Q).al 0) * Cc k Q i 0 := by
  obtain ⟨-, h⟩ := cell_lintegral Q hk
  unfold cavg
  rw [volume_cell_real, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun u => QB.fk_nonneg k _)
    ((QB.measurable_fk k).comp (measurable_const_add Q)).aestronglyMeasurable, h]
  ring

/-! ### Integer images -/

theorem IV.r_eq (v : IV) (D : ℝ) (i : Fin 3) : v.r D i = (v.g i : ℝ) / D := rfl

theorem QB_bil_r (u v : IV) (D : ℝ) (hD : D ≠ 0) :
    QB.bil (u.r D) (v.r D) * (D ^ 2 * 2 ^ 54) = (u.dot (Bint.mulV v) : ℝ) := by
  simp only [QB_bil, IV.r, Fin.sum_univ_three, IV.dot, IM.mulV, IM.rw, IV.g0, IV.g1, IV.g2, Bint]
  push_cast
  field_simp; ring

theorem IV.r_add (u v : IV) (D : ℝ) : (IV.add u v).r D = u.r D + v.r D := by
  funext i; simp only [IV.r, Pi.add_apply]; fin_cases i <;> simp [IV.add, IV.g0, IV.g1, IV.g2] <;> ring

theorem IV.r_sub (u v : IV) (D : ℝ) : (IV.sub u v).r D = u.r D - v.r D := by
  funext i; simp only [IV.r, Pi.sub_apply]; fin_cases i <;> simp [IV.sub, IV.g0, IV.g1, IV.g2] <;> ring

theorem Dv_half : ((Dvc / 2 : ℤ) : ℝ) = Dv / 2 := by norm_num [Dv, Dvc]

theorem keyQ_eq (key : ℤ × ℤ × ℤ) : keyQ key = (IV.smul (Dvc / 2) (keyIV key)).r Dv := by
  have hD := Dv_pos
  funext i; simp only [keyQ, IV.r]
  fin_cases i <;> simp [IV.smul, IV.g0, IV.g1, IV.g2, Dv_half] <;> field_simp <;> ring

theorem outA_eq (i : Fin 72) (key : ℤ × ℤ × ℤ) : outA i (keyQ key) = (ncol Dvc (td i) key 0).r Dv := by
  rw [outA, keyQ_eq, ncol, IV.r_add, add_comm]

theorem outD_eq (i : Fin 72) : outD i = (IV.sub (td i).a (td i).c).r Dv := by
  rw [outD, IV.r_sub]; rfl

theorem outE_eq (i : Fin 72) : outE i = (IV.sub (td i).b (td i).c).r Dv := by
  rw [outE, IV.r_sub]; rfl

theorem gram_out (i : Fin 72) (key : ℤ × ℤ × ℤ) :
    GramOK QB (outA i (keyQ key)) (outD i) (outE i) ((Dv * 2 ^ 27) ^ 2)
      (qcOf Bint Dvc (td i) key).q00 (qcOf Bint Dvc (td i) key).q01 (qcOf Bint Dvc (td i) key).q02
      (qcOf Bint Dvc (td i) key).q11 (qcOf Bint Dvc (td i) key).q12 (qcOf Bint Dvc (td i) key).q22 := by
  have hS : (Dv * 2 ^ 27) ^ 2 = Dv ^ 2 * 2 ^ 54 := by ring
  have hD : Dv ≠ 0 := ne_of_gt Dv_pos
  rw [outA_eq, outD_eq, outE_eq, hS]
  exact ⟨QB_bil_r _ _ _ hD, QB_bil_r _ _ _ hD, QB_bil_r _ _ _ hD, QB_bil_r _ _ _ hD, QB_bil_r _ _ _ hD,
    QB_bil_r _ _ _ hD⟩

theorem al0_eq (i : Fin 72) (key : ℤ × ℤ × ℤ) :
    (tetQ i (keyQ key)).al 0 = (alN Dvc (td i) key : ℝ) / (2 * (td i).d) := by
  have hd := td_d_pos i
  simp only [tetQ, alN, beR, keyQ, IV.r, Fin.sum_univ_three, IV.dot, IV.add, keyIV, IV.g0, IV.g1, IV.g2]
  push_cast
  simp only [TD.row, Dv]
  field_simp; ring

theorem sg_div_pos {a b : ℝ} (hb : 0 < b) : sg (a / b) = sg a := by
  rw [div_eq_inv_mul]; exact sg_mul_pos (inv_pos.mpr hb)

theorem sg_al0 (i : Fin 72) (key : ℤ × ℤ × ℤ) :
    sg ((tetQ i (keyQ key)).al 0) = sg (alN Dvc (td i) key : ℝ) := by
  rw [al0_eq, sg_div_pos (by have := td_d_pos i; positivity)]

theorem det_out (i : Fin 72) (key : ℤ × ℤ × ℤ) :
    ((tetQ i (keyQ key)).faceM 0).det = (detN Dvc (td i) key : ℝ) / Dv ^ 3 := by
  rw [detN, ← det3_real _ _ _ Dv (ne_of_gt Dv_pos)]
  congr 1
  have e : ∀ m, (tetQ i (keyQ key)).p (Fin.succ m) = (ncol Dvc (td i) key m.val).r Dv := by
    intro m
    rw [ncol, IV.r_add, ← keyQ_eq, add_comm]
    fin_cases m <;> rfl
  ext r c
  simp only [Tet.faceM, Matrix.of_apply, Fin.succAbove_zero, e]
  fin_cases c <;> rfl

/-! ### The enclosure of an average -/

theorem lpt_zero (s : ℝ × ℝ) : lpt 0 0 0 false s = s := by
  simp [lpt, epsR]

theorem sg_int (a : ℤ) : sg (a : ℝ) = (Int.sign a : ℝ) := by
  unfold sg
  rcases lt_trichotomy a 0 with h | h | h
  · have : (a : ℝ) < 0 := by exact_mod_cast h
    simp [Int.sign_eq_neg_one_of_neg h, this, not_lt.mpr (le_of_lt this)]
  · simp [h]
  · have : (0 : ℝ) < a := by exact_mod_cast h
    simp [Int.sign_eq_one_of_pos h, this]

/-- One outer face: `sg(c₀) Cc ∈ [tLo, tHi] / (SK Dv³ (3-k))`. -/
theorem face_bound (i : Fin 72) (key : ℤ × ℤ × ℤ) {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hDeg : ∀ d ∈ degList, ruleOK d WCc (gmM d) (gmRule d) = true) {t : QT} {lo hi : ℤ}
    (h : alN Dvc (td i) key = 0 ∨
      (detN Dvc (td i) key ≠ 0 ∧ treeChk (qcOf Bint Dvc (td i) key) k t 0 0 0 false = some (lo, hi))) :
    let N := SK k (Dv * 2 ^ 27) * Dv ^ 3 * (3 - k : ℕ)
    ((if alN Dvc (td i) key = 0 then 0 else tLo Dvc (td i) key lo hi : ℤ) : ℝ) / N ≤
        sg ((tetQ i (keyQ key)).al 0) * Cc k (keyQ key) i 0 ∧
      sg ((tetQ i (keyQ key)).al 0) * Cc k (keyQ key) i 0 ≤
        ((if alN Dvc (td i) key = 0 then 0 else tHi Dvc (td i) key lo hi : ℤ) : ℝ) / N := by
  intro N
  have hk2 : k ≤ 2 := by omega
  by_cases h0 : alN Dvc (td i) key = 0
  · rw [sg_al0, h0]; simp [sg]
  obtain ⟨hdet, htr⟩ := h.resolve_left h0
  simp only [h0, if_false]
  have hD := Dv_pos
  have hsD : (0 : ℝ) < Dv * 2 ^ 27 := by positivity
  obtain ⟨-, hlo, hhi⟩ := treeChk_sound QB hsD (gram_out i key) hk hDeg t 0 0 0 false lo hi htr
  simp only [lpt_zero, pow_zero, div_one] at hlo hhi
  have hdetR : ((tetQ i (keyQ key)).faceM 0).det ≠ 0 := by
    rw [det_out]; have : (detN Dvc (td i) key : ℝ) ≠ 0 := by exact_mod_cast hdet
    positivity
  have halR : (tetQ i (keyQ key)).al 0 ≠ 0 := by
    rw [al0_eq]; have : (alN Dvc (td i) key : ℝ) ≠ 0 := by exact_mod_cast h0
    have := td_d_pos i; positivity
  rw [outer_value i _ hk2 hdetR halR, sg_al0, sg_int, det_out]
  set J := ∫ s in T2, QB.fk k (aff (outA i (keyQ key)) (outD i) (outE i) s)
  set S := SK k (Dv * 2 ^ 27)
  have hS : 0 < S := by
    simp only [S, SK]; have := WCc_pos; positivity
  have hk3 : (0 : ℝ) < ((3 - k : ℕ) : ℝ) := by
    have : 0 < 3 - k := by omega
    exact_mod_cast this
  have hN : 0 < N := by simp only [N]; positivity
  have hc : (Int.sign (alN Dvc (td i) key) : ℝ) * |(detN Dvc (td i) key : ℝ) / Dv ^ 3| =
      (cN Dvc (td i) key : ℝ) / Dv ^ 3 := by
    simp only [cN]; push_cast
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Dv ^ 3)]; ring
  have e : (Int.sign (alN Dvc (td i) key) : ℝ) * (|(detN Dvc (td i) key : ℝ) / Dv ^ 3| * (1 / ((3 - k : ℕ) : ℝ)) * J) =
      ((cN Dvc (td i) key : ℝ) * (S * J)) / N := by
    rw [← mul_assoc, ← mul_assoc, hc]; simp only [N]; field_simp; ring
  rw [e]
  simp only [tLo, tHi]
  constructor
  · rw [div_le_div_iff_of_pos_right hN]
    split_ifs with hcn
    · push_cast; exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hcn)
    · push_cast
      have : (cN Dvc (td i) key : ℝ) < 0 := by exact_mod_cast (not_le.mp hcn)
      nlinarith
  · rw [div_le_div_iff_of_pos_right hN]
    split_ifs with hcn
    · push_cast; exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast hcn)
    · push_cast
      have : (cN Dvc (td i) key : ℝ) < 0 := by exact_mod_cast (not_le.mp hcn)
      nlinarith

/-- The per-face lower / upper integers. -/
def fLo (key : ℤ × ℤ × ℤ) (i : Fin 72) (lo hi : ℤ) : ℤ :=
  if alN Dvc (td i) key = 0 then 0 else tLo Dvc (td i) key lo hi
def fHi (key : ℤ × ℤ × ℤ) (i : Fin 72) (lo hi : ℤ) : ℤ :=
  if alN Dvc (td i) key = 0 then 0 else tHi Dvc (td i) key lo hi

theorem denN_eq {k : ℕ} (hk : k = 1 ∨ k = 2) :
    SK k (Dv * 2 ^ 27) * Dv ^ 3 * (3 - k : ℕ) = (denN WCc Dvc k : ℝ) := by
  have hD := Dv_pos
  rcases hk with rfl | rfl
  · simp only [SK, denN, KB1, show (1 : ℕ) ≠ 2 by norm_num, if_false, pow_one]
    push_cast; simp only [Dv]; field_simp; ring
  · simp only [SK, denN, KB, if_true]
    push_cast; simp only [Dv]; field_simp; ring

/-- **The enclosure of `cavg` from the 72 face checks.** -/
theorem cavg_bound (key : ℤ × ℤ × ℤ) {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hDeg : ∀ d ∈ degList, ruleOK d WCc (gmM d) (gmRule d) = true) (lo hi : Fin 72 → ℤ) (tr : Fin 72 → QT)
    (h : ∀ i, alN Dvc (td i) key = 0 ∨
      (detN Dvc (td i) key ≠ 0 ∧ treeChk (qcOf Bint Dvc (td i) key) k (tr i) 0 0 0 false = some (lo i, hi i))) :
    64 * Real.pi * ((∑ i, fLo key i (lo i) (hi i) : ℤ) : ℝ) / denN WCc Dvc k ≤ cavg k (keyQ key) ∧
      cavg k (keyQ key) ≤ 64 * Real.pi * ((∑ i, fHi key i (lo i) (hi i) : ℤ) : ℝ) / denN WCc Dvc k := by
  have hk2 : k ≤ 2 := by omega
  rw [cavg_formula k hk2]
  have hb := fun i => face_bound i key hk hDeg (h i)
  simp only at hb
  rw [denN_eq hk] at hb
  have hN : (0 : ℝ) < denN WCc Dvc k := by
    rw [← denN_eq hk]; simp only [SK]; have := WCc_pos; have := Dv_pos
    have h3 : 0 < 3 - k := by omega
    have : (0 : ℝ) < ((3 - k : ℕ) : ℝ) := by exact_mod_cast h3
    positivity
  have hpi := Real.pi_pos
  push_cast
  constructor
  · rw [mul_div_assoc, Finset.sum_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun i _ => (hb i).1
  · rw [mul_div_assoc, Finset.sum_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun i _ => (hb i).2

/-- From `boxOK` to the box. -/
theorem box_of (N : ℤ) (SV : ℕ) {SL SH lo hi : ℤ} (hb : boxOK N SV SL SH lo hi = true) {x : ℝ}
    (hx : 64 * Real.pi * (SL : ℝ) / N ≤ x ∧ x ≤ 64 * Real.pi * (SH : ℝ) / N) :
    (lo : ℝ) / 2 ^ SV ≤ x ∧ x ≤ (hi : ℝ) / 2 ^ SV := by
  simp only [boxOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hSL, hN⟩, h1⟩, h2⟩ := hb
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hSL' : (0 : ℝ) ≤ SL := by exact_mod_cast hSL
  have h1' : (lo : ℝ) * N * 10 ^ 20 ≤ 64 * 314159265358979323846 * SL * 2 ^ SV := by exact_mod_cast h1
  have h2' : 64 * 314159265358979323847 * (SH : ℝ) * 2 ^ SV ≤ hi * N * 10 ^ 20 := by exact_mod_cast h2
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  have hSH' : (0 : ℝ) ≤ SH := by
    by_contra hc; push_neg at hc
    have : 64 * Real.pi * (SL : ℝ) / N ≤ 64 * Real.pi * (SH : ℝ) / N := le_trans hx.1 hx.2
    rw [div_le_div_iff_of_pos_right hN'] at this
    nlinarith [Real.pi_pos]
  have hP : (0 : ℝ) < 2 ^ SV := by positivity
  have q1 : (314159265358979323846 : ℝ) / 10 ^ 20 * (SL * 2 ^ SV) ≤ Real.pi * (SL * 2 ^ SV) :=
    mul_le_mul_of_nonneg_right (by norm_num at p1 ⊢; linarith) (by positivity)
  have q2 : Real.pi * (SH * 2 ^ SV) ≤ (314159265358979323847 : ℝ) / 10 ^ 20 * (SH * 2 ^ SV) :=
    mul_le_mul_of_nonneg_right (by norm_num at p2 ⊢; linarith) (by positivity)
  constructor
  · refine le_trans ?_ hx.1
    rw [div_le_div_iff₀ hP hN']
    nlinarith
  · refine le_trans hx.2 ?_
    rw [div_le_div_iff₀ hN' hP]
    nlinarith

end GW.Endpoint.Coulomb

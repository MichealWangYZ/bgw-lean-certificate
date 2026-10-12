/-
G2-coulomb (10/n): the translated tetrahedra `T_i + Q` as `Tet`s, and the exact reduction of
`∫_P |Q+u|_B^{-k} du` to the 72 outer face integrals (`cell_formula`).
-/
import GW.Endpoint.Coulomb.Geometry

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

theorem inv_row_col (i : Fin 72) (k m : ℕ) (hk : k < 3) (hm : m < 3) :
    ((td i).row k).dot ((td i).col m) = if k = m then (td i).d else 0 := by
  have := (td_facts i).1
  simp only [invOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at this
  exact (this.2 k hk m hm).2

/-- The barycentric row `k` of `T_i + Q` (linear part). -/
noncomputable def beR (i : Fin 72) (k : ℕ) (m : Fin 3) : ℝ := Dv * ((td i).row k).g m / (td i).d

/-- `T_i + Q` as a tetrahedron (vertices `Q, Q + c, Q + a, Q + b`). -/
noncomputable def tetQ (i : Fin 72) (Q : E3) : Tet where
  p := fun j => match j with
    | ⟨0, _⟩ => Q
    | ⟨1, _⟩ => Q + ((td i).col 0).r Dv
    | ⟨2, _⟩ => Q + ((td i).col 1).r Dv
    | _ => Q + ((td i).col 2).r Dv
  be := fun j m => match j with
    | ⟨0, _⟩ => -(beR i 0 m + beR i 1 m + beR i 2 m)
    | ⟨1, _⟩ => beR i 0 m
    | ⟨2, _⟩ => beR i 1 m
    | _ => beR i 2 m
  al := fun j => match j with
    | ⟨0, _⟩ => 1 + ∑ m, (beR i 0 m + beR i 1 m + beR i 2 m) * Q m
    | ⟨1, _⟩ => -∑ m, beR i 0 m * Q m
    | ⟨2, _⟩ => -∑ m, beR i 1 m * Q m
    | _ => -∑ m, beR i 2 m * Q m

/-- The barycentric coordinate `k+1` is `Dv row_k · (x - Q) / d`. -/
theorem lamQ_succ (i : Fin 72) (Q x : E3) (k : Fin 3) :
    (tetQ i Q).lam k.succ x = Dv * ((td i).row k.val).lin (x - Q) / (td i).d := by
  simp only [Tet.lam, IV.lin, Finset.mul_sum, Finset.sum_div]
  fin_cases k <;> simp [tetQ, beR, Fin.sum_univ_three] <;> ring

theorem lamQ_zero (i : Fin 72) (Q x : E3) :
    (tetQ i Q).lam 0 x = 1 - ∑ k : Fin 3, (tetQ i Q).lam k.succ x := by
  simp only [Fin.sum_univ_three]
  simp [Tet.lam, tetQ, Fin.sum_univ_three]; ring

theorem lin_col (i : Fin 72) (k m : ℕ) (hk : k < 3) (hm : m < 3) :
    Dv * ((td i).row k).lin (((td i).col m).r Dv) / (td i).d = if k = m then 1 else 0 := by
  rw [IV.lin_r, inv_row_col i k m hk hm]
  have hd := td_d_pos i; have hD := Dv_pos
  split_ifs <;> field_simp

theorem lin_zero (v : IV) : v.lin 0 = 0 := by simp [IV.lin]

theorem mv_Mof_sum (t : TD) (v : E3) : mv (Mof t) v = ∑ k : Fin 3, v k • (t.col k.val).r Dv := by
  funext r; rw [mv_Mof]; simp [IV.r, Finset.sum_apply]; refine Finset.sum_congr rfl fun k _ => ?_; ring

theorem tetQ_ok (i : Fin 72) (Q : E3) : (tetQ i Q).Ok := by
  constructor
  · intro x; rw [Fin.sum_univ_succ, lamQ_zero]; ring
  · intro x
    rw [Fin.sum_univ_succ, lamQ_zero]
    have hr := recon_td i (x - Q)
    rw [mv_Mof_sum] at hr
    have e : ∀ k : Fin 3, (tetQ i Q).p k.succ = Q + ((td i).col k.val).r Dv := by
      intro k; fin_cases k <;> rfl
    simp only [e, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, lamQ_succ]
    rw [hr]
    have hp0 : (tetQ i Q).p 0 = Q := rfl
    rw [hp0, sub_smul, one_smul]; abel
  · intro a b
    have hd := td_d_pos i; have hD := Dv_pos
    have pv : ∀ a : Fin 4, (tetQ i Q).p a - Q = if h : a = 0 then 0 else ((td i).col (a.val - 1)).r Dv := by
      intro a; fin_cases a <;> simp [tetQ]
    have hs : ∀ k : Fin 3, ∀ a : Fin 4, (tetQ i Q).lam k.succ ((tetQ i Q).p a) = if a = k.succ then 1 else 0 := by
      intro k a
      rw [lamQ_succ, pv]
      split_ifs with h1 h2 h2
      · subst h1; exact absurd h2 (Fin.succ_ne_zero k).symm
      · rw [lin_zero]; simp
      · subst h2; rw [lin_col i _ _ k.isLt (by omega)]; simp
      · rw [lin_col i _ _ k.isLt (by have := a.isLt; omega)]
        rw [if_neg]; intro hk; apply h2; ext; simp; omega
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨k, rfl⟩
    · rw [lamQ_zero, Fin.sum_univ_three]
      simp only [hs]
      fin_cases a <;> simp
    · rw [hs k a]

theorem lam_mv (i : Fin 72) (Q : E3) (v : E3) (k : Fin 3) :
    (tetQ i Q).lam k.succ (Q + mv (Mof (td i)) v) = v k := by
  rw [lamQ_succ, add_sub_cancel_left, lin_mv]
  have hd := td_d_pos i; have hD := Dv_pos
  simp only [Fin.sum_univ_three]
  have h0 := inv_row_col i k.val 0 k.isLt (by norm_num)
  have h1 := inv_row_col i k.val 1 k.isLt (by norm_num)
  have h2 := inv_row_col i k.val 2 k.isLt (by norm_num)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  fin_cases k <;> simp at h0 h1 h2 ⊢ <;> rw [h0, h1, h2] <;> push_cast <;> field_simp

theorem mem_KQ (i : Fin 72) (Q x : E3) : x ∈ (tetQ i Q).K ↔ x - Q ∈ Tset (td i) := by
  constructor
  · intro hx
    refine ⟨fun k => (tetQ i Q).lam k.succ x, ⟨hx 1, hx 2, hx 3, ?_⟩, ?_⟩
    · have h0 := hx 0; rw [lamQ_zero, Fin.sum_univ_three] at h0
      show (tetQ i Q).lam (0 : Fin 3).succ x + (tetQ i Q).lam (1 : Fin 3).succ x +
        (tetQ i Q).lam (2 : Fin 3).succ x ≤ 1
      linarith
    · have := recon_td i (x - Q)
      rw [← this]
      have e : (fun k : Fin 3 => (tetQ i Q).lam k.succ x) = fun k => Dv * ((td i).row k.val).lin (x - Q) / (td i).d := by
        funext k; exact lamQ_succ i Q x k
      rw [e]
  · rintro ⟨v, hv, hvx⟩
    have hx : x = Q + mv (Mof (td i)) v := by rw [hvx]; abel
    rw [hx]
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · rw [lamQ_zero, Fin.sum_univ_three, lam_mv, lam_mv, lam_mv]
      have := D3_sum hv; simp only [Fin.sum_univ_three] at this; linarith
    · rw [lam_mv]; exact D3_nonneg hv k

/-- Translation: `∫⁻_{T_i} G(Q + u) du = ∫⁻_{T_i + Q} G`. -/
theorem lintegral_translate (i : Fin 72) (Q : E3) (G : E3 → ℝ≥0∞) :
    ∫⁻ u in Tset (td i), G (Q + u) = ∫⁻ x in (tetQ i Q).K, G x := by
  have hmp : MeasurePreserving (fun u : E3 => Q + u) volume volume := measurePreserving_add_left volume Q
  have hpre : (fun u : E3 => Q + u) ⁻¹' (tetQ i Q).K = Tset (td i) := by
    ext u; simp only [Set.mem_preimage, mem_KQ, add_sub_cancel_left]
  rw [← hpre]
  exact hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addLeft Q) G _

/-! ### The inner faces cancel -/

/-- The matrix with columns `u, v, w`. -/
def colsM (u v w : E3) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun r c => match c with
  | ⟨0, _⟩ => u r
  | ⟨1, _⟩ => v r
  | _ => w r

theorem cone_swap (u v w : E3) : mv (colsM u w v) '' D3 = mv (colsM u v w) '' D3 := by
  have key : ∀ v' w' : E3, mv (colsM u w' v') '' D3 ⊆ mv (colsM u v' w') '' D3 := by
    intro v' w'
    rintro _ ⟨s, ⟨h0, h1, h2, h3⟩, rfl⟩
    refine ⟨![s 0, s 2, s 1], ⟨by simpa using h0, by simpa using h2, by simpa using h1, by simp; linarith⟩, ?_⟩
    funext r; simp [mv, colsM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  exact Set.Subset.antisymm (key v w) (key w v)

theorem faceM_succ (i : Fin 72) (Q : E3) (k : Fin 3) :
    (tetQ i Q).faceM k.succ = colsM Q (Q + (shared (td i) k.val).1.r Dv) (Q + (shared (td i) k.val).2.r Dv) := by
  ext r c
  fin_cases k <;> fin_cases c <;> rfl

theorem cone_succ (i : Fin 72) (Q : E3) (k : Fin 3) :
    (tetQ i Q).cone k.succ = mv (colsM Q (Q + (shared (td i) k.val).1.r Dv) (Q + (shared (td i) k.val).2.r Dv)) '' D3 := by
  rw [Tet.cone, faceM_succ]

theorem nb_data (i : Fin 72) (k : Fin 3) :
    (td i).nk k.val < 3 ∧ (td (nbF i k)).nb ((td i).nk k.val) = i.val ∧ (td (nbF i k)).nk ((td i).nk k.val) = k.val ∧
      (shared (td (nbF i k)) ((td i).nk k.val) = shared (td i) k.val ∨
        shared (td (nbF i k)) ((td i).nk k.val) = ((shared (td i) k.val).2, (shared (td i) k.val).1)) := by
  have h := nb_facts i
  simp only [nbOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, a⟩, b⟩, c⟩, d⟩ := h k.val k.isLt
  exact ⟨a, b, c, d⟩

/-- The partner of an inner face. -/
def partner (x : Fin 72 × Fin 3) : Fin 72 × Fin 3 :=
  (nbF x.1 x.2, ⟨(td x.1).nk x.2.val, (nb_data x.1 x.2).1⟩)

theorem partner_invol (x : Fin 72 × Fin 3) : partner (partner x) = x := by
  obtain ⟨i, k⟩ := x
  obtain ⟨-, h1, h2, -⟩ := nb_data i k
  simp only [partner, Prod.mk.injEq]
  constructor
  · ext; exact h1
  · ext; exact h2

theorem cone_partner (Q : E3) (x : Fin 72 × Fin 3) :
    (tetQ (partner x).1 Q).cone (partner x).2.succ = (tetQ x.1 Q).cone x.2.succ := by
  obtain ⟨i, k⟩ := x
  obtain ⟨-, -, -, h⟩ := nb_data i k
  simp only [partner]
  rw [cone_succ, cone_succ]
  rcases h with h | h <;> simp only [h]
  exact cone_swap _ _ _

theorem al_succ (i : Fin 72) (Q : E3) (k : Fin 3) :
    (tetQ i Q).al k.succ = -(Dv * ((td i).row k.val).lin Q / (td i).d) := by
  have := lamQ_succ i Q 0 k
  have h0 : (tetQ i Q).lam k.succ 0 = (tetQ i Q).al k.succ := by simp [Tet.lam]
  rw [h0] at this; rw [this, zero_sub]
  simp [IV.lin]; ring

theorem row_lin_cert (i : Fin 72) (k : Fin 3) (u : E3) :
    ∃ c : ℝ, 0 < c ∧ ((td i).row k.val).lin u =
      c * ((td (nbF i k)).d * (td i).W.lin u - (td i).d * (td (nbF i k)).W.lin u) := by
  have hc := (td_facts i).2.1
  simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hkn, hkd⟩, heq⟩ := hc k.val k.isLt
  rw [td_nbF] at heq
  have hl := congrArg (fun v => IV.lin v u) heq
  simp only [IV.lin_smul, IV.lin_sub] at hl
  push_cast at hl
  have hdn := td_d_pos (nbF i k)
  have hkn' : (0 : ℝ) < (td i).kn k.val := by exact_mod_cast hkn
  have hkd' : (0 : ℝ) < (td i).kd k.val := by exact_mod_cast hkd
  refine ⟨(td i).kn k.val / ((td (nbF i k)).d * (td i).kd k.val), by positivity, ?_⟩
  field_simp; linarith

theorem sg_neg (a : ℝ) : sg (-a) = -sg a := by
  unfold sg
  by_cases h1 : 0 < a
  · simp [h1, show ¬ 0 < -a by linarith, show -a < 0 by linarith]
  · by_cases h2 : a < 0
    · simp [h1, h2, show 0 < -a by linarith]
    · have : a = 0 := by linarith
      simp [this]

theorem sg_mul_pos {c a : ℝ} (hc : 0 < c) : sg (c * a) = sg a := by
  unfold sg
  by_cases h1 : 0 < a
  · simp [h1, mul_pos hc h1]
  · by_cases h2 : a < 0
    · simp [h1, h2, mul_neg_of_pos_of_neg hc h2, show ¬ 0 < c * a by nlinarith]
    · have : a = 0 := by linarith
      simp [this]

theorem sg_partner (Q : E3) (x : Fin 72 × Fin 3) :
    sg ((tetQ (partner x).1 Q).al (partner x).2.succ) = -sg ((tetQ x.1 Q).al x.2.succ) := by
  obtain ⟨i, k⟩ := x
  obtain ⟨-, h1, -, -⟩ := nb_data i k
  set n := nbF i k
  set k' : Fin 3 := ⟨(td i).nk k.val, (nb_data i k).1⟩
  have hn : nbF n k' = i := by ext; exact h1
  simp only [partner]
  rw [al_succ, al_succ]
  obtain ⟨c1, hc1, e1⟩ := row_lin_cert i k Q
  obtain ⟨c2, hc2, e2⟩ := row_lin_cert n k' Q
  rw [hn] at e2
  have hdi := td_d_pos i; have hdn := td_d_pos n; have hD := Dv_pos
  set X := (td n).d * (td i).W.lin Q - (td i).d * (td n).W.lin Q
  have e2' : ((td n).row k'.val).lin Q = -(c2 * X) := by rw [e2]; simp only [X]; ring
  show sg (-(Dv * ((td n).row k'.val).lin Q / (td n).d)) = -sg (-(Dv * ((td i).row k.val).lin Q / (td i).d))
  rw [e2', e1]
  rw [show -(Dv * -(c2 * X) / (td n).d) = (Dv * c2 / (td n).d) * X by ring,
    show -(Dv * (c1 * X) / (td i).d) = -((Dv * c1 / (td i).d) * X) by ring,
    sg_neg, neg_neg, sg_mul_pos (by positivity), sg_mul_pos (by positivity)]

/-- The cone integrals (real). -/
noncomputable def Cc (k : ℕ) (Q : E3) (i : Fin 72) (j : Fin 4) : ℝ :=
  (∫⁻ x in (tetQ i Q).cone j, ENNReal.ofReal (QB.fk k x)).toReal

theorem inner_cancel (k : ℕ) (Q : E3) :
    ∑ i : Fin 72, ∑ c : Fin 3, sg ((tetQ i Q).al c.succ) * Cc k Q i c.succ = 0 := by
  have e := Fintype.sum_prod_type' (fun i (c : Fin 3) => sg ((tetQ i Q).al c.succ) * Cc k Q i c.succ)
  rw [← e]
  refine Finset.sum_involution (fun x _ => partner x) ?_ ?_ (fun x _ => by simp)
    (fun x _ => partner_invol x)
  · intro x _
    have hc : Cc k Q (partner x).1 (partner x).2.succ = Cc k Q x.1 x.2.succ := by
      simp only [Cc]; rw [cone_partner]
    rw [hc, sg_partner]; ring
  · intro x _ hne heq
    apply hne
    have hc : Cc k Q (partner x).1 (partner x).2.succ = Cc k Q x.1 x.2.succ := by
      simp only [Cc]; rw [cone_partner]
    have := sg_partner Q x
    have heq' : partner x = x := heq
    rw [heq'] at this
    have h0 : sg ((tetQ x.1 Q).al x.2.succ) = 0 := by linarith
    rw [h0, zero_mul]

/-- **Exact reduction to the outer cones.** -/
theorem cell_lintegral (Q : E3) {k : ℕ} (hk : k ≤ 2) :
    ∫⁻ u in cellP, ENNReal.ofReal (QB.fk k (Q + u)) < ⊤ ∧
    (∫⁻ u in cellP, ENNReal.ofReal (QB.fk k (Q + u))).toReal =
      ∑ i : Fin 72, sg ((tetQ i Q).al 0) * Cc k Q i 0 := by
  rw [lintegral_cell (fun u => ENNReal.ofReal (QB.fk k (Q + u))),
    Finset.sum_congr rfl fun i _ => lintegral_translate i Q (fun x => ENNReal.ofReal (QB.fk k x))]
  have hs := fun i : Fin 72 => Tet.real_signed QB (tetQ_ok i Q) hk
  refine ⟨ENNReal.sum_lt_top.mpr fun i _ => (hs i).1, ?_⟩
  rw [ENNReal.toReal_sum fun i _ => ne_of_lt (hs i).1]
  rw [Finset.sum_congr rfl fun i _ => (hs i).2]
  simp_rw [Fin.sum_univ_succ (n := 3)]
  rw [Finset.sum_add_distrib]
  have := inner_cancel k Q
  simp only [Cc] at this
  simp only [Cc]
  linarith

/-- The outer face as an affine map of `T2`. -/
noncomputable def outA (i : Fin 72) (Q : E3) : E3 := Q + ((td i).col 0).r Dv
noncomputable def outD (i : Fin 72) : E3 := ((td i).col 1).r Dv - ((td i).col 0).r Dv
noncomputable def outE (i : Fin 72) : E3 := ((td i).col 2).r Dv - ((td i).col 0).r Dv

theorem faceM_zero_fm (i : Fin 72) (Q : E3) (s : ℝ × ℝ) :
    mv ((tetQ i Q).faceM 0) (fm s) = aff (outA i Q) (outD i) (outE i) s := by
  rw [mv_fm]
  ext r
  simp [aff, outA, outD, outE, Tet.faceM, tetQ, Fin.succAbove]

/-- The value of an outer cone. -/
theorem outer_value (i : Fin 72) (Q : E3) {k : ℕ} (hk : k ≤ 2) (hdet : ((tetQ i Q).faceM 0).det ≠ 0)
    (hal : (tetQ i Q).al 0 ≠ 0) :
    Cc k Q i 0 = |((tetQ i Q).faceM 0).det| * (1 / (3 - k : ℕ)) *
      ∫ s in T2, QB.fk k (aff (outA i Q) (outD i) (outE i) s) := by
  have hne := Tet.face_ne_zero (tetQ_ok i Q) hal
  simp only [Cc, Tet.cone]
  rw [lintegral_cone _ hdet (QB.fk k) (QB.measurable_fk k) (QB.fk_nonneg k) k hk (QB.fk_hom k)]
  simp_rw [faceM_zero_fm]
  have hcont : ContinuousOn (fun s => QB.fk k (aff (outA i Q) (outD i) (outE i) s)) T2 := by
    apply (QB.continuousOn_fk k (S := (aff (outA i Q) (outD i) (outE i)) '' T2) ?_).comp
    · exact (by unfold aff; fun_prop : Continuous (aff (outA i Q) (outD i) (outE i))).continuousOn
    · intro s hs; exact ⟨s, hs, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩; rw [← faceM_zero_fm]; exact hne s hs
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_T2 hcont)
    (Filter.Eventually.of_forall fun s => QB.fk_nonneg k _)]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.toReal_ofReal]
  · ring
  · exact mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity)
      (setIntegral_nonneg T2_meas fun s _ => QB.fk_nonneg k _))

end GW.Endpoint.Coulomb

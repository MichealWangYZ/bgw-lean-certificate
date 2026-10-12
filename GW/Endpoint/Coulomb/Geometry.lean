/-
G2-coulomb (9/n): the Wigner–Seitz cell and its decomposition into 72 tetrahedra.

* `QB` — the metric `B = Bint / 2^54` of the file (positive definite);
* `cellP` — the Wigner–Seitz cell of the q-lattice `(ℤ/2)³` in crystal coordinates:
  `{u | 2 ⟨u, n/2⟩_B ≤ |n/2|²_B for the 26 n ∈ {-1,0,1}³ \ 0}`;
* `Tset i = M_i '' D3` the tetrahedra, `cell_eq_union` (`P = ⋃ T_i`), `Tset_aedisj`,
  from the integer certificates `geomOK` (kernel).
-/
import GW.Endpoint.Coulomb.Assemble
import GW.Endpoint.Coulomb.GeomData

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

/-! ### Real embeddings of the integer data -/

theorem IV.gi_fin (v : IV) (i : Fin 3) : v.gi i.val = v.g i := by
  fin_cases i <;> rfl

/-- `v / D` as a point. -/
noncomputable def IV.r (v : IV) (D : ℝ) : E3 := fun i => (v.g i : ℝ) / D

/-- The linear form `u ↦ Σ v_i u_i`. -/
noncomputable def IV.lin (v : IV) (u : E3) : ℝ := ∑ i, (v.g i : ℝ) * u i

theorem IV.g0 (v : IV) : v.g 0 = v.x := rfl
theorem IV.g1 (v : IV) : v.g 1 = v.y := rfl
theorem IV.g2 (v : IV) : v.g 2 = v.z := rfl

theorem IV.lin_eq (v : IV) (u : E3) : v.lin u = v.x * u 0 + v.y * u 1 + v.z * u 2 := by
  simp [IV.lin, Fin.sum_univ_three, IV.g0, IV.g1, IV.g2]

theorem IV.dot_cast (a b : IV) : ((a.dot b : ℤ) : ℝ) = a.lin (b.r 1) := by
  simp [IV.dot, IV.lin_eq, IV.r, IV.g0, IV.g1, IV.g2]

theorem IV.lin_r (a b : IV) (D : ℝ) : a.lin (b.r D) = (a.dot b : ℝ) / D := by
  simp only [IV.lin_eq, IV.r, IV.g0, IV.g1, IV.g2, IV.dot]; push_cast; ring

theorem IV.ext' {a b : IV} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

/-! ### The metric -/

def IM.rw (M : IM) (i : Fin 3) : IV := match i with
  | ⟨0, _⟩ => M.r0
  | ⟨1, _⟩ => M.r1
  | _ => M.r2

/-- `B = Bint / 2^54`. -/
noncomputable def Bmat : Matrix (Fin 3) (Fin 3) ℝ := fun i j => ((Bint.rw i).g j : ℝ) / 2 ^ 54

theorem Bint_pos (x : E3) (hx : x ≠ 0) : 0 < ∑ i, ∑ j, Bmat i j * x i * x j := by
  simp only [Bmat, Fin.sum_univ_three, IM.rw, Bint, IV.g0, IV.g1, IV.g2]
  have : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  have hi2 : 0 < x i ^ 2 := by positivity
  have key : (20263033028603940 : ℝ) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) - 2 * 6754344342867979 *
      (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) = (20263033028603940 - 2 * 6754344342867979) *
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) + 6754344342867979 * ((x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 + (x 1 - x 2) ^ 2) := by
    ring
  have hs : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    fin_cases i <;> simp at hi2 <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  push_cast
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2)]

/-- The metric of the file as a positive definite form. -/
noncomputable def QB : QF where
  M := Bmat
  symm := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  pos := Bint_pos

theorem QB_bil (u v : E3) : QB.bil u v = ∑ i, ∑ j, ((Bint.rw i).g j : ℝ) / 2 ^ 54 * u i * v j := rfl

theorem mulV_g (M : IM) (v : IV) (i : Fin 3) : (M.mulV v).g i = ∑ j, (M.rw i).g j * v.g j := by
  fin_cases i <;> simp [IM.mulV, IV.dot, IM.rw, IV.g, Fin.sum_univ_three]

theorem QB_bil_n (u : E3) (n : IV) : 2 * QB.bil u (n.r 2) = (Bint.mulV n).lin u / 2 ^ 54 := by
  simp only [QB_bil, IV.lin, IV.r, mulV_g]
  push_cast
  simp only [Fin.sum_univ_three]
  have hs : ∀ i j : Fin 3, (Bint.rw i).g j = (Bint.rw j).g i := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [hs 0 1, hs 0 2, hs 1 2]
  ring

theorem QB_q_n (n : IV) : QB.q (n.r 2) = (n.dot (Bint.mulV n) : ℝ) / (4 * 2 ^ 54) := by
  have h := QB_bil_n (n.r 2) n
  rw [IV.lin_r] at h
  simp only [QF.q]
  have hd : (Bint.mulV n).dot n = n.dot (Bint.mulV n) := by simp [IV.dot]; ring
  rw [hd] at h
  field_simp at h ⊢; linarith

/-! ### The cell and the tetrahedra -/

noncomputable abbrev Dv : ℝ := (Dvc : ℝ)

theorem Dv_pos : (0 : ℝ) < Dv := by norm_num [Dv, Dvc]

/-- The Wigner–Seitz cell of the q-lattice (26 half-spaces, metric `B`). -/
def cellP : Set E3 := {u | ∀ n ∈ cellNs, 2 * QB.bil u (n.r 2) ≤ QB.q (n.r 2)}

theorem mem_cellP (u : E3) :
    u ∈ cellP ↔ ∀ n ∈ cellNs, 4 * (Bint.mulV n).lin u ≤ (n.dot (Bint.mulV n) : ℝ) := by
  simp only [cellP, mem_setOf_eq, QB_bil_n, QB_q_n]
  refine forall₂_congr fun n _ => ?_
  constructor <;> intro h
  · have : (Bint.mulV n).lin u / 2 ^ 54 ≤ (n.dot (Bint.mulV n) : ℝ) / (4 * 2 ^ 54) := h
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- The vertex matrix of a tetrahedron (columns `c, a, b` over `Dv`). -/
noncomputable def Mof (t : TD) : Matrix (Fin 3) (Fin 3) ℝ := fun r k => ((t.col k.val).g r : ℝ) / Dv

/-- The tetrahedron `conv(0, c, a, b)`. -/
noncomputable def Tset (t : TD) : Set E3 := mv (Mof t) '' D3

theorem mv_Mof (t : TD) (v : E3) (r : Fin 3) : mv (Mof t) v r = ∑ k : Fin 3, v k * (t.col k.val).g r / Dv := by
  simp [mv, Mof, Matrix.mulVec, dotProduct]; refine Finset.sum_congr rfl fun k _ => ?_; ring

theorem lin_mv (t : TD) (w : IV) (v : E3) : w.lin (mv (Mof t) v) = ∑ k : Fin 3, v k * (w.dot (t.col k.val) : ℝ) / Dv := by
  simp only [IV.lin, mv_Mof, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [IV.dot, Fin.sum_univ_three, IV.g0, IV.g1, IV.g2]; push_cast; ring

theorem D3_sum {v : E3} (hv : v ∈ D3) : ∑ k : Fin 3, v k ≤ 1 := by
  obtain ⟨-, -, -, h⟩ := hv; simpa [Fin.sum_univ_three] using h

theorem D3_nonneg {v : E3} (hv : v ∈ D3) (k : Fin 3) : 0 ≤ v k := by
  obtain ⟨h0, h1, h2, -⟩ := hv; fin_cases k <;> assumption

/-- `T ⊆ P` from the vertex checks. -/
theorem Tset_sub (t : TD) (h : vertOK Bint Dvc cellNs t = true) : Tset t ⊆ cellP := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_cellP]
  intro n hn
  simp only [vertOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨hH, hk⟩ := h n hn
  have hH' : (0 : ℝ) < (n.dot (Bint.mulV n) : ℝ) := by exact_mod_cast hH
  rw [lin_mv, Finset.mul_sum]
  calc ∑ k : Fin 3, 4 * (v k * ((Bint.mulV n).dot (t.col k.val) : ℝ) / Dv)
      ≤ ∑ k : Fin 3, v k * (n.dot (Bint.mulV n) : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        have h1 : (4 * (Bint.mulV n).dot (t.col k.val) : ℝ) ≤ (n.dot (Bint.mulV n) : ℝ) * Dv := by
          exact_mod_cast hk k.val k.isLt
        have := D3_nonneg hv k
        have hD := Dv_pos
        rw [show 4 * (v k * ((Bint.mulV n).dot (t.col k.val) : ℝ) / Dv) =
          v k * ((4 * (Bint.mulV n).dot (t.col k.val) : ℝ) / Dv) by ring]
        apply mul_le_mul_of_nonneg_left _ this
        rw [div_le_iff₀ hD]; exact h1
    _ = (∑ k : Fin 3, v k) * (n.dot (Bint.mulV n) : ℝ) := by rw [Finset.sum_mul]
    _ ≤ 1 * (n.dot (Bint.mulV n) : ℝ) := mul_le_mul_of_nonneg_right (D3_sum hv) (le_of_lt hH')
    _ = _ := one_mul _

theorem IV.lin_smul (a : ℤ) (v : IV) (u : E3) : (IV.smul a v).lin u = a * v.lin u := by
  simp [IV.lin_eq, IV.smul]; ring
theorem IV.lin_add (v w : IV) (u : E3) : (IV.add v w).lin u = v.lin u + w.lin u := by
  simp [IV.lin_eq, IV.add]; ring
theorem IV.lin_sub (v w : IV) (u : E3) : (IV.sub v w).lin u = v.lin u - w.lin u := by
  simp [IV.lin_eq, IV.sub]; ring

/-- The certified cell data. -/
theorem geom_ok : geomOK Bint Dvc cellNs cellTs = true := by decide +kernel

theorem cellTs_len : cellTs.length = 72 := rfl

/-- The `i`-th tetrahedron. -/
def td (i : Fin 72) : TD := cellTs.getD i.val dflt

theorem td_mem (i : Fin 72) : td i ∈ cellTs := by
  unfold td; rw [List.getD_eq_getElem _ _ (by rw [cellTs_len]; exact i.isLt)]; exact List.getElem_mem _

theorem td_facts (i : Fin 72) : invOK (td i) = true ∧ certOK cellTs (td i) = true ∧
    outerOK Bint Dvc cellNs (td i) = true ∧ vertOK Bint Dvc cellNs (td i) = true ∧ (td i).f < cellNs.length := by
  have h := geom_ok
  simp only [geomOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ht, -⟩, -⟩, -⟩ := h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := ht (td i) (td_mem i)
  exact ⟨a, b, c, d, e⟩

theorem nb_facts (i : Fin 72) : nbOK cellTs i.val (td i) = true := by
  have h := geom_ok
  simp only [geomOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact h.1.2 i.val (by rw [cellTs_len]; exact i.isLt)

theorem td_nb_lt (i : Fin 72) (k : ℕ) (hk : k < 3) : (td i).nb k < 72 := by
  have := nb_facts i
  simp only [nbOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at this
  have := (this k hk).1.1.1.1; rwa [cellTs_len] at this

/-- The neighbour of `i` across the face opposite vertex `k`. -/
def nbF (i : Fin 72) (k : Fin 3) : Fin 72 := ⟨(td i).nb k.val, td_nb_lt i k.val k.isLt⟩

theorem td_nbF (i : Fin 72) (k : Fin 3) : cellTs.getD ((td i).nb k.val) dflt = td (nbF i k) := rfl

theorem td_d_pos (i : Fin 72) : (0 : ℝ) < (td i).d := by
  have := (td_facts i).1
  simp only [invOK, Bool.and_eq_true, decide_eq_true_eq] at this
  exact_mod_cast this.1

theorem inv_col_row (i : Fin 72) (r m : Fin 3) :
    ∑ k : Fin 3, ((td i).col k.val).g r * ((td i).row k.val).g m = if r = m then (td i).d else 0 := by
  have := (td_facts i).1
  simp only [invOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at this
  have h := (this.2 r.val r.isLt m.val m.isLt).1
  simp only [List.range_succ, List.range_zero, List.map, List.sum_cons, List.sum_nil, List.nil_append,
    List.cons_append, List.singleton_append, List.map_cons, List.map_nil] at h
  simp only [Fin.sum_univ_three, ← IV.gi_fin]
  have e : (if r = m then (td i).d else 0) = if r.val = m.val then (td i).d else 0 := by
    by_cases hrm : r = m
    · simp [hrm]
    · simp [hrm, Fin.val_ne_of_ne hrm]
  rw [e]
  simpa [add_assoc] using h

/-- The lifted form `φ_i`. -/
noncomputable def phiT (i : Fin 72) (u : E3) : ℝ := (td i).W.lin u / (td i).d

/-- `row_k · u ≥ 0` where `φ_i` is maximal. -/
theorem row_nonneg (i : Fin 72) (k : Fin 3) (u : E3) (hmax : phiT (nbF i k) u ≤ phiT i u) :
    0 ≤ ((td i).row k.val).lin u := by
  have hc := (td_facts i).2.1
  simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hkn, hkd⟩, heq⟩ := hc k.val k.isLt
  rw [td_nbF] at heq
  have hl := congrArg (fun v => IV.lin v u) heq
  simp only [IV.lin_smul, IV.lin_sub] at hl
  push_cast at hl
  have hdi := td_d_pos i
  have hdn := td_d_pos (nbF i k)
  have hkn' : (0 : ℝ) < (td i).kn k.val := by exact_mod_cast hkn
  have hkd' : (0 : ℝ) < (td i).kd k.val := by exact_mod_cast hkd
  simp only [phiT] at hmax
  rw [div_le_div_iff₀ hdn hdi] at hmax
  have : 0 ≤ ((td (nbF i k)).d * (td i).kd k.val) * ((td i).row k.val).lin u := by
    rw [hl]; apply mul_nonneg (le_of_lt hkn'); linarith
  have hp : (0:ℝ) < (td (nbF i k)).d * (td i).kd k.val := by positivity
  exact (mul_nonneg_iff_of_pos_left hp).mp this

/-- `M_i (Dv adj_i y / d_i) = y`. -/
theorem recon_td (i : Fin 72) (u : E3) :
    mv (Mof (td i)) (fun k => (Dv * ((td i).row k.val).lin u) / (td i).d) = u := by
  have hd := td_d_pos i
  have hD := Dv_pos
  funext r
  rw [mv_Mof]
  have h0 := inv_col_row i r 0
  have h1 := inv_col_row i r 1
  have h2 := inv_col_row i r 2
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have c0 : ((((td i).col 0).g r * ((td i).row 0).g 0 + ((td i).col 1).g r * ((td i).row 1).g 0 +
      ((td i).col 2).g r * ((td i).row 2).g 0 : ℤ) : ℝ) = ((if r = 0 then (td i).d else 0 : ℤ) : ℝ) := by
    exact_mod_cast h0
  have c1 : ((((td i).col 0).g r * ((td i).row 0).g 1 + ((td i).col 1).g r * ((td i).row 1).g 1 +
      ((td i).col 2).g r * ((td i).row 2).g 1 : ℤ) : ℝ) = ((if r = 1 then (td i).d else 0 : ℤ) : ℝ) := by
    exact_mod_cast h1
  have c2 : ((((td i).col 0).g r * ((td i).row 0).g 2 + ((td i).col 1).g r * ((td i).row 1).g 2 +
      ((td i).col 2).g r * ((td i).row 2).g 2 : ℤ) : ℝ) = ((if r = 2 then (td i).d else 0 : ℤ) : ℝ) := by
    exact_mod_cast h2
  push_cast at c0 c1 c2
  simp only [IV.lin, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hd0 : ((td i).d : ℝ) ≠ 0 := ne_of_gt hd
  have hD0 : Dv ≠ 0 := ne_of_gt hD
  fin_cases r <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at c0 c1 c2 ⊢ <;>
    simp only [if_true, if_false, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide, Int.cast_zero] at c0 c1 c2 <;>
    field_simp <;> linear_combination Dv * ((u 0) * c0 + (u 1) * c1 + (u 2) * c2)

/-- **Covering**: `P ⊆ ⋃ T_i`. -/
theorem cell_cover (u : E3) (hu : u ∈ cellP) : ∃ i : Fin 72, u ∈ Tset (td i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => phiT i u) Finset.univ_nonempty
  have hd := td_d_pos i
  have hD := Dv_pos
  have hr : ∀ k : Fin 3, 0 ≤ ((td i).row k.val).lin u := fun k => row_nonneg i k u (hi _ (Finset.mem_univ _))
  refine ⟨i, fun k => (Dv * ((td i).row k.val).lin u) / (td i).d, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hr 0; positivity
  · have := hr 1; positivity
  · have := hr 2; positivity
  · -- the outer face
    have ho := (td_facts i).2.2.1
    have hf := (td_facts i).2.2.2.2
    simp only [outerOK, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨hH, heq⟩ := ho
    set n := cellNs.getD (td i).f ⟨0, 0, 0⟩
    have hn : n ∈ cellNs := by
      simp only [n]; rw [List.getD_eq_getElem _ _ hf]; exact List.getElem_mem _
    have hP := (mem_cellP u).mp hu n hn
    have hl := congrArg (fun v => IV.lin v u) heq
    simp only [IV.lin_smul, IV.lin_add] at hl
    push_cast at hl
    have hH' : (0 : ℝ) < (n.dot (Bint.mulV n) : ℝ) := by exact_mod_cast hH
    show Dv * ((td i).row 0).lin u / (td i).d + Dv * ((td i).row 1).lin u / (td i).d +
      Dv * ((td i).row 2).lin u / (td i).d ≤ 1
    rw [← add_div, ← add_div, div_le_one hd]
    have e : ((td i).row 0).lin u = (td i).q0.lin u := rfl
    have e1 : ((td i).row 1).lin u = (td i).q1.lin u := rfl
    have e2 : ((td i).row 2).lin u = (td i).q2.lin u := rfl
    rw [e, e1, e2]
    have key : (n.dot (Bint.mulV n) : ℝ) * (Dv * (td i).q0.lin u + Dv * (td i).q1.lin u + Dv * (td i).q2.lin u) ≤
        (n.dot (Bint.mulV n) : ℝ) * (td i).d := by
      have : (n.dot (Bint.mulV n) : ℝ) * (Dv * (td i).q0.lin u + Dv * (td i).q1.lin u + Dv * (td i).q2.lin u) =
          (td i).d * (4 * (Bint.mulV n).lin u) := by simp only [Dv]; linarith
      rw [this]; nlinarith
    exact le_of_mul_le_mul_left key hH'
  · exact recon_td i u

theorem sep_facts (i j : Fin 72) (hij : i ≠ j) :
    (∀ k : Fin 3, ((td j).W.dot ((td i).col k.val)) * (td i).d ≤ ((td i).W.dot ((td i).col k.val)) * (td j).d) ∧
      IV.smul (td j).d (td i).W ≠ IV.smul (td i).d (td j).W := by
  have h := geom_ok
  simp only [geomOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  have hs := h.1.1.2
  simp only [sepOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, cellTs_len] at hs
  rcases hs i.val i.isLt j.val j.isLt with h1 | ⟨h2, h3⟩
  · exact absurd (Fin.ext h1) hij
  · exact ⟨fun k => h2 k.val k.isLt, h3⟩

theorem phi_le_on (i j : Fin 72) (hij : i ≠ j) {u : E3} (hu : u ∈ Tset (td i)) :
    (td j).W.lin u * (td i).d ≤ (td i).W.lin u * (td j).d := by
  obtain ⟨v, hv, rfl⟩ := hu
  rw [lin_mv, lin_mv, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum; intro k _
  have := (sep_facts i j hij).1 k
  have h' : (((td j).W.dot ((td i).col k.val)) * (td i).d : ℝ) ≤ (((td i).W.dot ((td i).col k.val)) * (td j).d : ℝ) := by
    exact_mod_cast this
  have hv0 := D3_nonneg hv k
  have hD := Dv_pos
  rw [show v k * ((td j).W.dot ((td i).col k.val) : ℝ) / Dv * (td i).d =
      v k / Dv * (((td j).W.dot ((td i).col k.val)) * (td i).d : ℝ) by ring,
    show v k * ((td i).W.dot ((td i).col k.val) : ℝ) / Dv * (td j).d =
      v k / Dv * (((td i).W.dot ((td i).col k.val)) * (td j).d : ℝ) by ring]
  exact mul_le_mul_of_nonneg_left h' (by positivity)

theorem Tset_aedisj (i j : Fin 72) (hij : i ≠ j) : AEDisjoint volume (Tset (td i)) (Tset (td j)) := by
  set w := IV.sub (IV.smul (td j).d (td i).W) (IV.smul (td i).d (td j).W)
  have hw : ∃ k, (w.g k : ℝ) ≠ 0 := by
    by_contra hc; push_neg at hc
    apply (sep_facts i j hij).2
    have h0 : w.x = 0 := by exact_mod_cast hc 0
    have h1 : w.y = 0 := by exact_mod_cast hc 1
    have h2 : w.z = 0 := by exact_mod_cast hc 2
    simp only [w, IV.sub, IV.smul] at h0 h1 h2
    exact IV.ext' (by simp [IV.smul]; linarith) (by simp [IV.smul]; linarith) (by simp [IV.smul]; linarith)
  have hnull := null_affine 0 (fun k => (w.g k : ℝ)) hw
  refine measure_mono_null (fun u ⟨hi, hj⟩ => ?_) hnull
  have a1 := phi_le_on i j hij hi
  have a2 := phi_le_on j i (Ne.symm hij) hj
  simp only [mem_setOf_eq, zero_add]
  have : w.lin u = 0 := by
    simp only [w, IV.lin_sub, IV.lin_smul]; linarith
  simpa [IV.lin] using this

theorem Tset_meas (t : TD) : MeasurableSet (Tset t) := by
  have hc : IsCompact D3 := by
    apply (isCompact_Icc (a := (0 : E3)) (b := 1)).of_isClosed_subset D3_closed
    rintro v ⟨h0, h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
  have hcont : Continuous (mv (Mof t)) := by
    rw [mv_eq]; exact (Matrix.toLin' (Mof t)).continuous_of_finiteDimensional
  exact (hc.image hcont).isClosed.measurableSet

theorem cell_eq_union : cellP = ⋃ i ∈ (Finset.univ : Finset (Fin 72)), Tset (td i) := by
  ext u; simp only [mem_iUnion, Finset.mem_univ, exists_true_left]
  constructor
  · exact cell_cover u
  · rintro ⟨i, hi⟩; exact Tset_sub (td i) (td_facts i).2.2.2.1 hi

/-- **The decomposition** (lintegral). -/
theorem lintegral_cell (G : E3 → ℝ≥0∞) :
    ∫⁻ u in cellP, G u = ∑ i : Fin 72, ∫⁻ u in Tset (td i), G u := by
  rw [cell_eq_union, lintegral_biUnion_finset₀]
  · intro i _ j _ hij; exact Tset_aedisj i j hij
  · intro i _; exact (Tset_meas _).nullMeasurableSet

theorem det_ok : detOK Dvc cellTs = true := by decide +kernel

theorem det3_real (c a b : IV) (D : ℝ) (hD : D ≠ 0) :
    (Matrix.of fun r k : Fin 3 => (((match k with | ⟨0, _⟩ => c | ⟨1, _⟩ => a | _ => b) : IV).g r : ℝ) / D).det =
      (det3I c a b : ℝ) / D ^ 3 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, det3I, IV.g0, IV.g1, IV.g2]
  push_cast
  field_simp; ring

theorem Mof_det (i : Fin 72) : (Mof (td i)).det = ((td i).d : ℝ) / Dv ^ 3 := by
  have hd : (td i).d = det3I (td i).c (td i).a (td i).b := by
    have := det_ok
    simp only [detOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact this.1 _ (td_mem i)
  rw [hd, ← det3_real _ _ _ Dv (ne_of_gt Dv_pos)]
  congr 1; ext r k; fin_cases k <;> rfl

theorem volume_D3 : volume D3 = ENNReal.ofReal (1 / 6) := by
  have h := lintegral_cone (1 : Matrix (Fin 3) (Fin 3) ℝ) (by simp) (fun _ => 1) measurable_const
    (fun _ => zero_le_one) 0 (by norm_num) (fun r _ x => by simp)
  have him : mv (1 : Matrix (Fin 3) (Fin 3) ℝ) '' D3 = D3 := by
    ext v; simp [mv]
  rw [him] at h
  simp only [ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    one_mul, Matrix.det_one, abs_one] at h
  rw [h]
  have := volume_T2
  rw [Measure.real] at this
  rw [← ENNReal.ofReal_toReal (ne_of_lt volume_T2_lt), this, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem volume_Tset (i : Fin 72) : volume (Tset (td i)) = ENNReal.ofReal (((td i).d : ℝ) / Dv ^ 3 / 6) := by
  have hd := td_d_pos i
  have hdet : (Mof (td i)).det ≠ 0 := by rw [Mof_det]; have := Dv_pos; positivity
  have h := lintegral_image_mv (Mof (td i)) hdet D3_meas (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at h
  rw [Tset, h, volume_D3, Mof_det, abs_of_pos (by have := Dv_pos; positivity), ← ENNReal.ofReal_mul (by
    have := Dv_pos; positivity)]
  congr 1; ring

/-- **`|P| = 1/8`** (the crystal volume of the mini-BZ cell for the 2×2×2 grid). -/
theorem volume_cell : volume cellP = ENNReal.ofReal (1 / 8) := by
  have h := lintegral_cell (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at h
  rw [h]
  simp_rw [volume_Tset]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := td_d_pos i; have := Dv_pos; positivity)]
  congr 1
  have hs := det_ok
  simp only [detOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hsum : (cellTs.map TD.d).sum = ∑ i : Fin 72, (td i).d := by
    rw [← List.sum_ofFn]; congr 1
  rw [hsum] at hs
  have hs' : (4 : ℝ) * ∑ i : Fin 72, ((td i).d : ℝ) = 3 * Dv ^ 3 := by exact_mod_cast hs.2
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hD := Dv_pos
  field_simp; linarith

end GW.Endpoint.Coulomb

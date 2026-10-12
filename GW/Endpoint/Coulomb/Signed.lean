/-
G2-coulomb (7/n): the signed cone identity of a tetrahedron.

A tetrahedron `T` (vertices `p j`, barycentric affine functions `lam j`, `T.Ok`) and the four
cones `cone j = conv(0, faces j)` from the origin over its faces. With `c j = lam j 0` (the
barycentric coordinates of the origin), for every measurable `g ≥ 0`:

  Σ_{c j > 0} ∫⁻_{cone j} g = ∫⁻_T g + Σ_{c j < 0} ∫⁻_{cone j} g        (`lintegral_signed`).

Pointwise, off a finite union of affine hyperplanes: with `A = {s ≥ 0 : s c_i ≤ lam_i x ∀ i}`,
`x ∈ cone j ↔ s_j = lam_j x / c_j ∈ A`, `x ∈ T ↔ 0 ∈ A`; the far cones containing `x` number
`[A ≠ ∅]` (the minimiser of `s_j` over `c_j > 0`), the near ones `[A ≠ ∅ ∧ 0 ∉ A]`.
-/
import GW.Endpoint.Coulomb.Cone

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset
open scoped ENNReal

/-- A tetrahedron with barycentric coordinates `lam j x = al j + Σ_k be j k x_k`. -/
structure Tet where
  p : Fin 4 → E3
  al : Fin 4 → ℝ
  be : Fin 4 → Fin 3 → ℝ

namespace Tet

variable (T : Tet)

def lam (j : Fin 4) (x : E3) : ℝ := T.al j + ∑ k, T.be j k * x k

/-- The barycentric identities. -/
structure Ok : Prop where
  sum1 : ∀ x, ∑ j, T.lam j x = 1
  recon : ∀ x, ∑ j, T.lam j x • T.p j = x
  vert : ∀ i j, T.lam j (T.p i) = if i = j then 1 else 0

/-- The (closed) tetrahedron. -/
def K : Set E3 := {x | ∀ j, 0 ≤ T.lam j x}

/-- The matrix of the three vertices other than `j` (in increasing order). -/
def faceM (j : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun r c => T.p (j.succAbove c) r

/-- The cone from the origin over face `j`. -/
def cone (j : Fin 4) : Set E3 := mv (T.faceM j) '' D3

variable {T}

theorem lam_comb (hT : T.Ok) (μ : Fin 4 → ℝ) (i : Fin 4) :
    T.lam i (∑ j, μ j • T.p j) = (1 - ∑ j, μ j) * T.al i + μ i := by
  have hv : ∀ j, ∑ k, T.be i k * T.p j k = (if j = i then 1 else 0) - T.al i := by
    intro j; have := hT.vert j i; simp only [lam] at this; linarith
  have : ∑ k, T.be i k * (∑ j, μ j • T.p j) k = ∑ j, μ j * ((if j = i then 1 else 0) - T.al i) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  simp only [lam, this, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.sum_mul]
  ring

theorem al_sum (hT : T.Ok) : ∑ j, T.al j = 1 := by
  have := hT.sum1 0; simpa [lam] using this

theorem al_recon (hT : T.Ok) : ∑ j, T.al j • T.p j = 0 := by
  have := hT.recon 0; simpa [lam] using this

theorem mv_faceM (j : Fin 4) (v : E3) : mv (T.faceM j) v = ∑ c, v c • T.p (j.succAbove c) := by
  ext r; simp [mv, faceM, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **Membership in a cone** (`c_j ≠ 0`). -/
theorem mem_cone_iff (hT : T.Ok) {j : Fin 4} (hj : T.al j ≠ 0) (x : E3) :
    x ∈ T.cone j ↔ 0 ≤ T.lam j x / T.al j ∧ ∀ i, T.lam j x / T.al j * T.al i ≤ T.lam i x := by
  constructor
  · rintro ⟨v, ⟨h0, h1, h2, h3⟩, rfl⟩
    rw [mv_faceM]
    set μ : Fin 4 → ℝ := Fin.insertNth j 0 v
    have hμ : ∑ c, v c • T.p (j.succAbove c) = ∑ i, μ i • T.p i := by
      rw [Fin.sum_univ_succAbove _ j]; simp [μ]
    have hμs : ∑ i, μ i = v 0 + v 1 + v 2 := by
      rw [Fin.sum_univ_succAbove _ j]; simp [μ, Fin.sum_univ_three]
    have hμ0 : ∀ i, 0 ≤ μ i := by
      intro i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨c, rfl⟩
      · simp [μ]
      · simp only [μ, Fin.insertNth_apply_succAbove]
        fin_cases c <;> assumption
    rw [hμ]
    have hl := fun i => lam_comb hT μ i
    have hlj : T.lam j (∑ i, μ i • T.p i) = (1 - ∑ i, μ i) * T.al j := by rw [hl]; simp [μ]
    have hs : T.lam j (∑ i, μ i • T.p i) / T.al j = 1 - ∑ i, μ i := by rw [hlj]; field_simp
    rw [hs, hμs]
    refine ⟨by linarith, fun i => ?_⟩
    rw [hl, hμs]; linarith [hμ0 i]
  · rintro ⟨hs0, hsi⟩
    set s := T.lam j x / T.al j
    have hjs : T.lam j x = s * T.al j := by simp only [s]; field_simp
    refine ⟨fun c => T.lam (j.succAbove c) x - s * T.al (j.succAbove c), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · dsimp only; linarith [hsi (j.succAbove 0)]
    · dsimp only; linarith [hsi (j.succAbove 1)]
    · dsimp only; linarith [hsi (j.succAbove 2)]
    · dsimp only
      have h1 := hT.sum1 x
      have h2 := al_sum hT
      rw [Fin.sum_univ_succAbove _ j] at h1 h2
      simp only [Fin.sum_univ_three] at h1 h2
      nlinarith
    · rw [mv_faceM]
      have h1 := hT.recon x
      have h2 := al_recon hT
      have : ∑ c, (T.lam (j.succAbove c) x - s * T.al (j.succAbove c)) • T.p (j.succAbove c) =
          ∑ i, (T.lam i x - s * T.al i) • T.p i := by
        rw [Fin.sum_univ_succAbove (fun i => (T.lam i x - s * T.al i) • T.p i) j, hjs]; simp
      rw [this]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, h2, smul_zero, sub_zero]

/-! ### The pointwise count -/

open Classical

/-- `s` is feasible: `s ≥ 0` and `s c_i ≤ lam_i x` for all `i`. -/
def feas (T : Tet) (x : E3) (s : ℝ) : Prop := 0 ≤ s ∧ ∀ i, s * T.al i ≤ T.lam i x

/-- Generic points: no barycentric coordinate vanishes and the ratios `lam_i / c_i` are distinct. -/
def gen (T : Tet) (x : E3) : Prop :=
  (∀ i, T.lam i x ≠ 0) ∧ ∀ i i', i ≠ i' → T.al i ≠ 0 → T.al i' ≠ 0 → T.al i' * T.lam i x ≠ T.al i * T.lam i' x

theorem cone_feas (hT : T.Ok) {j : Fin 4} (hj : T.al j ≠ 0) (x : E3) :
    x ∈ T.cone j ↔ feas T x (T.lam j x / T.al j) := mem_cone_iff hT hj x

theorem ratio_le_pos {a l s : ℝ} (ha : 0 < a) (h : s * a ≤ l) : s ≤ l / a := by
  rw [le_div_iff₀ ha]; exact h

theorem ratio_ge_neg {a l s : ℝ} (ha : a < 0) (h : s * a ≤ l) : l / a ≤ s := by
  rw [div_le_iff_of_neg ha]; exact h

theorem far_card (hT : T.Ok) {x : E3} (hg : gen T x) :
    (Finset.univ.filter fun j => 0 < T.al j ∧ x ∈ T.cone j).card = if ∃ s, feas T x s then 1 else 0 := by
  classical
  set Fs := Finset.univ.filter fun j => 0 < T.al j ∧ x ∈ T.cone j
  have hmem : ∀ j, j ∈ Fs ↔ 0 < T.al j ∧ feas T x (T.lam j x / T.al j) := by
    intro j; simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hc⟩; exact ⟨h, (cone_feas hT (ne_of_gt h) x).mp hc⟩
    · rintro ⟨h, hc⟩; exact ⟨h, (cone_feas hT (ne_of_gt h) x).mpr hc⟩
  -- uniqueness
  have huniq : ∀ j ∈ Fs, ∀ j' ∈ Fs, j = j' := by
    intro j hj j' hj'
    obtain ⟨hj0, hf⟩ := (hmem j).mp hj
    obtain ⟨hj0', hf'⟩ := (hmem j').mp hj'
    by_contra hne
    have h1 := ratio_le_pos hj0' (hf.2 j')
    have h2 := ratio_le_pos hj0 (hf'.2 j)
    have heq : T.lam j x / T.al j = T.lam j' x / T.al j' := le_antisymm h1 h2
    rw [div_eq_div_iff (ne_of_gt hj0) (ne_of_gt hj0')] at heq
    exact hg.2 j j' hne (ne_of_gt hj0) (ne_of_gt hj0') (by linarith)
  split_ifs with hex
  · obtain ⟨s0, hs0⟩ := hex
    -- the minimiser over the far indices
    have hpos : (Finset.univ.filter fun j => 0 < T.al j).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
      have := al_sum hT
      have : ∑ j, T.al j ≤ 0 := Finset.sum_nonpos fun j _ => not_lt.mp (hne (Finset.mem_univ j))
      linarith
    obtain ⟨j, hjm, hjmin⟩ := Finset.exists_min_image _ (fun j => T.lam j x / T.al j) hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjm hjmin
    have hjF : j ∈ Fs := by
      rw [hmem]
      refine ⟨hjm, ?_, fun i => ?_⟩
      · exact le_trans hs0.1 (ratio_le_pos hjm (hs0.2 j))
      · rcases lt_trichotomy (T.al i) 0 with hi | hi | hi
        · have h1 := ratio_ge_neg hi (hs0.2 i)
          have h2 := ratio_le_pos hjm (hs0.2 j)
          have : T.lam i x / T.al i ≤ T.lam j x / T.al j := le_trans h1 h2
          rw [div_le_iff_of_neg hi] at this; linarith
        · rw [hi, mul_zero]; have := hs0.2 i; rw [hi, mul_zero] at this; exact this
        · have := hjmin i hi
          rw [le_div_iff₀ hi] at this; linarith
    rw [Finset.card_eq_one]
    exact ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨hjF, fun j' hj' => huniq j' hj' j hjF⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
    intro j hj
    exact hex ⟨_, ((hmem j).mp hj).2⟩

theorem near_card (hT : T.Ok) {x : E3} (hg : gen T x) :
    (Finset.univ.filter fun j => T.al j < 0 ∧ x ∈ T.cone j).card =
      if (∃ s, feas T x s) ∧ ¬ feas T x 0 then 1 else 0 := by
  classical
  set Ns := Finset.univ.filter fun j => T.al j < 0 ∧ x ∈ T.cone j
  have hmem : ∀ j, j ∈ Ns ↔ T.al j < 0 ∧ feas T x (T.lam j x / T.al j) := by
    intro j; simp only [Ns, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hc⟩; exact ⟨h, (cone_feas hT (ne_of_lt h) x).mp hc⟩
    · rintro ⟨h, hc⟩; exact ⟨h, (cone_feas hT (ne_of_lt h) x).mpr hc⟩
  have huniq : ∀ j ∈ Ns, ∀ j' ∈ Ns, j = j' := by
    intro j hj j' hj'
    obtain ⟨hj0, hf⟩ := (hmem j).mp hj
    obtain ⟨hj0', hf'⟩ := (hmem j').mp hj'
    by_contra hne
    have h1 := ratio_ge_neg hj0' (hf.2 j')
    have h2 := ratio_ge_neg hj0 (hf'.2 j)
    have heq : T.lam j x / T.al j = T.lam j' x / T.al j' := le_antisymm h2 h1
    rw [div_eq_div_iff (ne_of_lt hj0) (ne_of_lt hj0')] at heq
    exact hg.2 j j' hne (ne_of_lt hj0) (ne_of_lt hj0') (by linarith)
  split_ifs with hex
  · obtain ⟨⟨s0, hs0⟩, hn0⟩ := hex
    -- some coordinate is negative at x, necessarily with a negative c
    have : ∃ i0, T.lam i0 x < 0 := by
      by_contra hc; push_neg at hc
      exact hn0 ⟨le_rfl, fun i => by rw [zero_mul]; exact hc i⟩
    obtain ⟨i0, hi0⟩ := this
    have hai0 : T.al i0 < 0 := by
      rcases lt_trichotomy (T.al i0) 0 with h | h | h
      · exact h
      · have := hs0.2 i0; rw [h, mul_zero] at this; linarith
      · have := hs0.2 i0; nlinarith [hs0.1]
    have hneg : (Finset.univ.filter fun j => T.al j < 0).Nonempty := ⟨i0, by simp [hai0]⟩
    obtain ⟨j, hjm, hjmax⟩ := Finset.exists_max_image _ (fun j => T.lam j x / T.al j) hneg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjm hjmax
    have hjN : j ∈ Ns := by
      rw [hmem]
      refine ⟨hjm, ?_, fun i => ?_⟩
      · have h1 := hjmax i0 hai0
        have h2 : 0 < T.lam i0 x / T.al i0 := div_pos_of_neg_of_neg hi0 hai0
        linarith
      · rcases lt_trichotomy (T.al i) 0 with hi | hi | hi
        · have := hjmax i hi
          rw [div_le_iff_of_neg hi] at this; linarith
        · rw [hi, mul_zero]; have := hs0.2 i; rw [hi, mul_zero] at this; exact this
        · have h1 := ratio_ge_neg hjm (hs0.2 j)
          have h2 := hs0.2 i
          nlinarith
    rw [Finset.card_eq_one]
    exact ⟨j, Finset.eq_singleton_iff_unique_mem.mpr ⟨hjN, fun j' hj' => huniq j' hj' j hjN⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
    intro j hj
    obtain ⟨hj0, hf⟩ := (hmem j).mp hj
    apply hex
    refine ⟨⟨_, hf⟩, fun h0 => ?_⟩
    have hl := h0.2 j
    rw [zero_mul] at hl
    have : T.lam j x / T.al j ≤ 0 := div_nonpos_of_nonneg_of_nonpos hl (le_of_lt hj0)
    have : T.lam j x / T.al j = 0 := le_antisymm this hf.1
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hg.1 j h
    · exact ne_of_lt hj0 h

theorem mem_K_iff (x : E3) : x ∈ T.K ↔ feas T x 0 :=
  ⟨fun h => ⟨le_rfl, fun i => by rw [zero_mul]; exact h i⟩, fun h i => by have := h.2 i; rwa [zero_mul] at this⟩

/-- **The pointwise identity** at generic points. -/
theorem count_identity (hT : T.Ok) {x : E3} (hg : gen T x) :
    (Finset.univ.filter fun j => 0 < T.al j ∧ x ∈ T.cone j).card =
      (if x ∈ T.K then 1 else 0) + (Finset.univ.filter fun j => T.al j < 0 ∧ x ∈ T.cone j).card := by
  rw [far_card hT hg, near_card hT hg]
  by_cases h0 : feas T x 0
  · have : ∃ s, feas T x s := ⟨0, h0⟩
    simp [this, h0, (mem_K_iff x).mpr h0]
  · have hk : x ∉ T.K := fun h => h0 ((mem_K_iff x).mp h)
    by_cases hex : ∃ s, feas T x s <;> simp [hex, h0, hk]

end Tet

/-! ### Null hyperplanes -/

/-- An affine hyperplane `{a + Σ b_k x_k = 0}` (`b ≠ 0`) is null. -/
theorem null_affine (a : ℝ) (b : Fin 3 → ℝ) (hb : ∃ k, b k ≠ 0) :
    volume {x : E3 | a + ∑ k, b k * x k = 0} = 0 := by
  obtain ⟨k, hk⟩ := hb
  set ℓ : E3 →ₗ[ℝ] ℝ := ∑ i, b i • LinearMap.proj i
  have hℓ : ∀ x, ℓ x = ∑ i, b i * x i := by intro x; simp [ℓ]
  set x0 : E3 := Pi.single k (-a / b k)
  have hx0 : ℓ x0 = -a := by
    rw [hℓ]; simp [x0, Pi.single_apply]; field_simp; ring
  have hS : {x : E3 | a + ∑ k, b k * x k = 0} = (fun x => x + (-x0)) ⁻¹' (LinearMap.ker ℓ : Set E3) := by
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, map_add, map_neg, hx0, hℓ, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have htop : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have : Pi.single k (1 : ℝ) ∈ LinearMap.ker ℓ := by rw [h]; trivial
    rw [LinearMap.mem_ker, hℓ] at this
    simp [Pi.single_apply] at this
    exact hk this
  rw [hS, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ htop

namespace Tet

variable {T : Tet}

theorem be_ne (hT : T.Ok) (i : Fin 4) : ∃ k, T.be i k ≠ 0 := by
  by_contra h; push_neg at h
  obtain ⟨i', hi'⟩ : ∃ i', i' ≠ i := ⟨i + 1, by simp⟩
  have h1 := hT.vert i i
  have h2 := hT.vert i' i
  simp only [lam, h, zero_mul, Finset.sum_const_zero, add_zero, if_true, if_neg hi'] at h1 h2
  linarith

theorem ratio_ne (hT : T.Ok) {i i' : Fin 4} (hii : i ≠ i') (hi' : T.al i' ≠ 0) :
    ∃ k, T.al i' * T.be i k - T.al i * T.be i' k ≠ 0 := by
  by_contra h; push_neg at h
  -- evaluate the linear part at p_i - p_i'' (i'' ∉ {i, i'})
  obtain ⟨i'', h1, h2⟩ : ∃ i'', i'' ≠ i ∧ i'' ≠ i' := by
    by_contra hc; push_neg at hc
    have : (Finset.univ : Finset (Fin 4)) ⊆ {i, i'} := by
      intro z _; by_cases hz : z = i
      · simp [hz]
      · simp [hc z hz]
    have := Finset.card_le_card this
    simp at this
    have := Finset.card_le_two (a := i) (b := i')
    omega
  have v1 := hT.vert i i; have v2 := hT.vert i'' i; have v3 := hT.vert i i'; have v4 := hT.vert i'' i'
  simp only [lam, if_true, if_neg h1, if_neg hii] at v1 v2 v3 v4
  have e : ∑ k, (T.al i' * T.be i k - T.al i * T.be i' k) * (T.p i k - T.p i'' k) = 0 := by
    simp [h]
  have e2 : ∑ k, (T.al i' * T.be i k - T.al i * T.be i' k) * (T.p i k - T.p i'' k) =
      T.al i' * (∑ k, T.be i k * T.p i k - ∑ k, T.be i k * T.p i'' k) -
      T.al i * (∑ k, T.be i' k * T.p i k - ∑ k, T.be i' k * T.p i'' k) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf; simp only [Finset.sum_sub_distrib]; ring_nf
  rw [e2] at e
  have hv4 : T.lam i' (T.p i'') = 0 := by rw [hT.vert]; simp [h2]
  simp only [lam] at hv4
  have : T.al i' * (1 - 0) - T.al i * (0 - 0) = 0 := by
    rw [← e]; congr 1 <;> [congr 1; congr 1] <;> linarith
  simp at this; exact hi' this

/-- Non-generic points form a null set. -/
theorem ae_gen (hT : T.Ok) : ∀ᵐ x ∂(volume : Measure E3), gen T x := by
  have hlam : ∀ i, ∀ᵐ x ∂(volume : Measure E3), T.lam i x ≠ 0 := by
    intro i
    rw [ae_iff]; push_neg
    simpa [lam] using null_affine (T.al i) (T.be i) (be_ne hT i)
  have hrat : ∀ i i', ∀ᵐ x ∂(volume : Measure E3), i ≠ i' → T.al i ≠ 0 → T.al i' ≠ 0 →
      T.al i' * T.lam i x ≠ T.al i * T.lam i' x := by
    intro i i'
    by_cases hii : i ≠ i'
    · by_cases hi : T.al i ≠ 0
      · by_cases hi' : T.al i' ≠ 0
        · rw [ae_iff]; push_neg
          have := null_affine (T.al i' * T.al i - T.al i * T.al i')
            (fun k => T.al i' * T.be i k - T.al i * T.be i' k) (ratio_ne hT hii hi')
          refine measure_mono_null (fun x hx => ?_) this
          simp only [mem_setOf_eq] at hx ⊢
          obtain ⟨-, -, -, hx⟩ := hx
          simp only [lam] at hx
          rw [← sub_eq_zero] at hx
          rw [← hx]; simp only [mul_add, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]; ring
        · exact Filter.Eventually.of_forall fun x _ _ h => absurd h hi'
      · exact Filter.Eventually.of_forall fun x _ h => absurd h hi
    · exact Filter.Eventually.of_forall fun x h => absurd h hii
  have h1 : ∀ᵐ x ∂(volume : Measure E3), ∀ i, T.lam i x ≠ 0 := ae_all_iff.mpr hlam
  have h2 : ∀ᵐ x ∂(volume : Measure E3), ∀ i i', i ≠ i' → T.al i ≠ 0 → T.al i' ≠ 0 →
      T.al i' * T.lam i x ≠ T.al i * T.lam i' x := ae_all_iff.mpr fun i => ae_all_iff.mpr fun i' => hrat i i'
  filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩

theorem cone_meas (j : Fin 4) : MeasurableSet (T.cone j) := by
  have hc : IsCompact D3 := by
    apply (isCompact_Icc (a := (0 : E3)) (b := 1)).of_isClosed_subset D3_closed
    rintro v ⟨h0, h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
  have hcont : Continuous (mv (T.faceM j)) := by
    rw [mv_eq]; exact (Matrix.toLin' (T.faceM j)).continuous_of_finiteDimensional
  exact (hc.image hcont).isClosed.measurableSet

theorem K_meas : MeasurableSet T.K := by
  have : T.K = ⋂ j, {x | 0 ≤ T.lam j x} := by ext x; simp [K]
  rw [this]
  refine MeasurableSet.iInter fun j => measurableSet_le measurable_const ?_
  unfold lam; fun_prop

open Classical in
theorem sum_ind (S : Finset (Fin 4)) (G : E3 → ℝ≥0∞) (x : E3) :
    ∑ j ∈ S, (T.cone j).indicator G x = ((S.filter fun j => x ∈ T.cone j).card : ℝ≥0∞) * G x := by
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- **The signed cone identity** (lintegral form). -/
theorem lintegral_signed (hT : T.Ok) (G : E3 → ℝ≥0∞) (hG : Measurable G) :
    ∑ j ∈ Finset.univ.filter (fun j => 0 < T.al j), ∫⁻ x in T.cone j, G x =
      (∫⁻ x in T.K, G x) + ∑ j ∈ Finset.univ.filter (fun j => T.al j < 0), ∫⁻ x in T.cone j, G x := by
  simp_rw [← lintegral_indicator (cone_meas _), ← lintegral_indicator K_meas]
  rw [← lintegral_finset_sum _ (fun j _ => hG.indicator (cone_meas j)),
    ← lintegral_finset_sum _ (fun j _ => hG.indicator (cone_meas j)),
    ← lintegral_add_left (hG.indicator K_meas)]
  apply lintegral_congr_ae
  filter_upwards [ae_gen hT] with x hx
  rw [sum_ind, sum_ind]
  have hc := count_identity hT hx
  rw [Finset.filter_filter, Finset.filter_filter, hc, Set.indicator_apply]
  split_ifs <;> push_cast <;> ring

end Tet

end GW.Endpoint.Coulomb

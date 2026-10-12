/-
R28-F4: the static remainder of the spec's Σ with ALL bands is NOT zero in general. It is
named here and split exactly into three explicit terms (REVIEW-28 finding F4).

`Cor.SigAall = SigA + tailS` adds the omitted bands' `ACq + Pq` (`specK = IeU/4 + ½ CH`) to
the run's Σ. Its static part (`sigAall_static_split`) is

    CORall = Σ_q (CSq + Σ_{n computed} ACq + tailA),   tailA = the omitted bands' ACq,

the static CH term `CSq` (BerkeleyGW's `ρ_aa` closure restricted to `Gch`) plus the band
sum of the static CH terms of ALL bands (computed and omitted). With the weights
`w_ij = v_i IeU(I_ji)/4` and `cloP(G_i, G_j) = Σ_v A_v(G_i) A_v(G_j)` (the closure of the
`k - q` sphere, `Cor.cloP`), under `CompleteK κ` (and nothing else) it is EXACTLY
(`cor_q_decomp`, `cor_all_decomp`)

    CORall = Σ_q [ corScale κ + corShift + corGch ],
      corScale κ = (κ - 1) Σ_ij w_ij cloP_ij                  (closure scale),
      corShift   = Σ_ij w_ij (cloP_ij - ρ_aa(G_i - G_j))       (shift-closure defect),
      corGch     = Σ_ij w_ij [G_j - G_i ∉ Gch] ρ_aa(G_i - G_j)  (Gch coverage).

Each vanishes under a named condition: `corScale_one` (`κ = 1`), `corShift_eq_zero`
(`ShiftClosed` for every pair with `|I_ji| ≥ TOL_Small`), `corGch_eq_zero` (`Gch` covers the
kept differences: the hypothesis `hch` of `Compare.chpart_sum_eq_exact`); all three:
`cor_all_eq_zero`. The conditions are sufficient, not necessary. `corShift` and `corGch`
do not depend on any band at `k - q`: they are fixed by the state `a`, the spheres,
`eps⁻¹` and `v`, so adding bands never removes them.

Relation to the existing closure theorem. For a state whose own bands are complete
(`Bloch.Complete`, the `hc` of `chpart_sum_eq_exact`) `COR = Σ_q (corShift + corGch)`
(`cor_decomp_complete`), so the `hs`, `hch` hypotheses of `chpart_sum_eq_exact` /
`sigA_eq_theory_complete` are exactly what removes the two remaining terms
(`cor_eq_zero_of_closure`). For the completion by a larger dyadic state, `CORall` is that
state's `COR` (`corAll_of_state`).

Witnesses (`Witness` section). The reviewer's: WFN sphere `{0}`, `c(0) = 1` (complete:
`wit_complete`), eps sphere `{0, b}`, unit Coulomb weights, `I_eps = diag(0, ½)`,
`0 ∈ Gch`: `COR = corShift = -1/8`, `corGch = 0` (`wit_cor`, `wit_shift`, `wit_gch`), and
the sphere is not shift-closed (`wit_not_shiftClosed`). The scaled-closure case: one unit
channel, `I_eps = c`, one computed band and one completion row `r`: `CompleteK (1 + r²)`,
`CORall = r²·c/4 = (κ - 1)·c/4` for `|c| ≥ TOL_Small` (`sc_completeK`, `sc_corAll`,
`sc_scale`).
-/
import GW.Bridge.Cor

namespace GW.Bridge

open Finset GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

section residual

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

/-- The weight `w_ij = v_i IeU(I_ji) / 4` of the pair `(i, j)` in the static remainder. -/
noncomputable def wR (t i j : ℕ) : ℝ :=
  vS gl vb (gl.qs.getD t default) i * IeU (Iq gl E vb oq t j i) / 4

/-- BerkeleyGW's closure value `ρ_aa(G_i - G_j)`. -/
noncomputable def rhoR (t a i j : ℕ) : ℝ :=
  pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a [])
    (gs (gl.qs.getD t default) i - gs (gl.qs.getD t default) j)

/-- The finite-sphere closure value `Σ_v A_v(G_i) A_v(G_j)` (`Cor.cloP`). -/
noncomputable def cloR (t a i j : ℕ) : ℝ :=
  cloP gl st t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j)

/-- **Closure-scale term** `(κ - 1) Σ_ij w_ij cloP_ij`: zero iff `κ = 1` or the sum is `0`. -/
noncomputable def corScale (κ : ℝ) (t a : ℕ) : ℝ :=
  (κ - 1) * ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wR gl E vb oq t i j * cloR gl st t a i j

/-- **Shift-closure defect** `Σ_ij w_ij (cloP_ij - ρ_aa(G_i - G_j))`. -/
noncomputable def corShift (t a : ℕ) : ℝ :=
  ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    wR gl E vb oq t i j * (cloR gl st t a i j - rhoR gl st t a i j)

/-- **`Gch`-coverage term** `Σ_ij w_ij [G_j - G_i ∉ Gch] ρ_aa(G_i - G_j)`. -/
noncomputable def corGch (t a : ℕ) : ℝ :=
  ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    wR gl E vb oq t i j *
      (if gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch then 0
       else rhoR gl st t a i j)

/-- The omitted bands' static terms `ACq` (the `IeU/4` of `specK`) at `q_t`. -/
noncomputable def tailA (cp : Compl) (t a : ℕ) : ℝ :=
  ∑ n ∈ range (cp.K t), quadR gl vb t (mR gl st cp t a n) (fun j i => IeU (Iq gl E vb oq t j i) / 4)

/-- The omitted bands' dynamic terms `½ CH` (the rest of `specK`). -/
noncomputable def tailD (cp : Compl) (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vb t (mR gl st cp t a n)
    (fun j i => (1 / 2) * schM (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw))

/-- **The static remainder of `SigAall`**: `CSq` plus the static CH terms of all bands. -/
noncomputable def CORall (cp : Compl) (a : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (CSq gl E vb oq st t a +
    ∑ n ∈ range (nbq st t), ACq gl E vb oq st t a n + tailA gl st E vb oq cp t a)

theorem quadR_add (vc : V3 → ℝ) (t : ℕ) (u : V3 → ℝ) (F G : ℕ → ℕ → ℝ) :
    quadR gl vc t u (fun j i => F j i + G j i) = quadR gl vc t u F + quadR gl vc t u G := by
  simp only [quadR, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- **`SigAall` keeps a static remainder.** It is the GPP parts of all bands plus the
exchange plus `CORall`; `CORall` is not assumed to vanish. -/
theorem sigAall_static_split (cp : Compl) (a iw : ℕ) :
    SigAall gl st E vb oq cp a iw =
      (∑ t ∈ range gl.qs.length,
        (Xq gl vb st t a + ∑ n ∈ range (nbq st t), Pq gl E vb oq st t a n iw)) +
      tailD gl st E vb oq cp a iw + CORall gl st E vb oq cp a := by
  have hq : ∀ t n, quadR gl vb t (mR gl st cp t a n)
      (fun j i => specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw)) =
      quadR gl vb t (mR gl st cp t a n) (fun j i => IeU (Iq gl E vb oq t j i) / 4) +
      quadR gl vb t (mR gl st cp t a n)
        (fun j i => (1 / 2) * schM (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw)) :=
    fun t n => quadR_add gl vb t _ _ _
  unfold SigAall SigA tailS tailD CORall tailA
  simp only [hq, sum_add_distrib]
  ring

/-! ### The three forms as weighted double sums -/

theorem csq_eq_w (t a : ℕ) :
    CSq gl E vb oq st t a =
      -∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wR gl E vb oq t i j *
        (if gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch then
          rhoR gl st t a i j else 0) := by
  unfold CSq wR rhoR nG
  simp only [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hr : pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a [])
      (gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i) =
      pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a [])
        (gs (gl.qs.getD t default) i - gs (gl.qs.getD t default) j) := by
    rw [← pd_neg, neg_sub]
  have hI : Iq gl E vb oq t j i = IeS gl E vb oq (gl.qs.getD t default) j i := rfl
  rw [hr, hI]
  by_cases h1 : TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i|
  · simp only [IeU, if_pos h1]
    by_cases h2 : gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch
    · rw [if_pos ⟨h1, h2⟩, if_pos h2]; unfold IeS; ring
    · rw [if_neg (fun h => h2 h.2), if_neg h2]; ring
  · simp only [IeU, if_neg h1]
    rw [if_neg (fun h => h1 h.1)]; ring

theorem acq_eq_w (t a n : ℕ) :
    ACq gl E vb oq st t a n =
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wR gl E vb oq t i j *
        (xS gl st t a n (gs (gl.qs.getD t default) i) * xS gl st t a n (gs (gl.qs.getD t default) j)) := by
  unfold ACq quad wR nG
  simp only [mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem acq_sum_eq_w (t a : ℕ) :
    ∑ n ∈ range (nbq st t), ACq gl E vb oq st t a n =
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wR gl E vb oq t i j *
        parP gl st t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j) := by
  simp only [acq_eq_w, parP, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]

theorem tailA_eq_w (cp : Compl) (t a : ℕ) :
    tailA gl st E vb oq cp t a =
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wR gl E vb oq t i j *
        ∑ n ∈ range (cp.K t), mR gl st cp t a n (gs (gl.qs.getD t default) i) *
          mR gl st cp t a n (gs (gl.qs.getD t default) j) := by
  unfold tailA quadR wR
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun n _ => ?_
  ring

/-! ### The exact decomposition -/

/-- **Decomposition at one q-point.** Under `CompleteK κ` only, the static remainder of
`SigAall` at `q_t` is closure scale + shift-closure defect + `Gch` coverage. -/
theorem cor_q_decomp (κ : ℝ) (cp : Compl) (t a : ℕ) (hc : CompleteK gl st κ cp t) :
    CSq gl E vb oq st t a + ∑ n ∈ range (nbq st t), ACq gl E vb oq st t a n +
        tailA gl st E vb oq cp t a =
      corScale gl st E vb oq κ t a + corShift gl st E vb oq t a + corGch gl st E vb oq t a := by
  rw [csq_eq_w, acq_sum_eq_w, tailA_eq_w]
  simp only [tailK_eq gl st κ cp t a _ _ hc, tailK]
  unfold corScale corShift corGch cloR
  simp only [mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **Decomposition of `CORall`** (`CompleteK κ` at every q-point). -/
theorem cor_all_decomp (κ : ℝ) (cp : Compl) (a : ℕ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st κ cp t) :
    CORall gl st E vb oq cp a =
      ∑ t ∈ range gl.qs.length,
        (corScale gl st E vb oq κ t a + corShift gl st E vb oq t a + corGch gl st E vb oq t a) :=
  sum_congr rfl fun t ht => cor_q_decomp gl st E vb oq κ cp t a (hc t (mem_range.mp ht))

/-! ### When each term vanishes -/

theorem corScale_one (t a : ℕ) : corScale gl st E vb oq 1 t a = 0 := by
  simp [corScale]

/-- Shift-closure alone (no completeness) makes the sphere closure `ρ_aa`. -/
theorem amp_sum_shift (Gk : List V3) (ca : List ℤ) (Gq : List V3) (G G' : V3)
    (hs : ShiftClosed Gk Gq G G') :
    ∑ v ∈ range Gq.length, amp gl Gk ca Gq v G * amp gl Gk ca Gq v G' =
      pd gl Gk ca Gk ca (G - G') := by
  unfold amp pd
  simp_rw [sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_comm]
  refine sum_congr rfl fun u' hu' => ?_
  have h := hs u (mem_range.mp hu) u' (mem_range.mp hu')
  have e : ∀ v ∈ range Gq.length,
      (if Gk.getD u 0 - Gq.getD v 0 = G then dy gl.SC (ca.getD u 0) else 0) *
        (if Gk.getD u' 0 - Gq.getD v 0 = G' then dy gl.SC (ca.getD u' 0) else 0) =
      (if Gk.getD u 0 - Gq.getD v 0 = G ∧ Gk.getD u' 0 - Gq.getD v 0 = G' then (1 : ℝ) else 0) *
        (dy gl.SC (ca.getD u 0) * dy gl.SC (ca.getD u' 0)) := by
    intro v _
    by_cases h1 : Gk.getD u 0 - Gq.getD v 0 = G <;> by_cases h2 : Gk.getD u' 0 - Gq.getD v 0 = G'
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, one_mul]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), mul_zero, zero_mul]
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), zero_mul, zero_mul]
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), zero_mul, zero_mul]
  rw [sum_congr rfl e, ← sum_mul, h]
  split_ifs <;> simp

/-- **Shift-closure removes `corShift`** (needed only for pairs with `|I_ji| ≥ TOL_Small`). -/
theorem corShift_eq_zero (t a : ℕ)
    (hs : ∀ i < nG gl t, ∀ j < nG gl t, TS ≤ |Iq gl E vb oq t j i| →
      ShiftClosed st.Gk (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i)
        (gs (gl.qs.getD t default) j)) :
    corShift gl st E vb oq t a = 0 := by
  unfold corShift
  refine sum_eq_zero fun i hi => sum_eq_zero fun j hj => ?_
  by_cases h : TS ≤ |Iq gl E vb oq t j i|
  · have e : cloR gl st t a i j = rhoR gl st t a i j :=
      amp_sum_shift gl _ _ _ _ _ (hs i (mem_range.mp hi) j (mem_range.mp hj) h)
    rw [e, sub_self, mul_zero]
  · simp [wR, IeU, h]

/-- **`Gch` coverage removes `corGch`** (the `hch` of `chpart_sum_eq_exact`). -/
theorem corGch_eq_zero (t a : ℕ)
    (hch : ∀ i < nG gl t, ∀ j < nG gl t, TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
      gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    corGch gl st E vb oq t a = 0 := by
  unfold corGch
  refine sum_eq_zero fun i hi => sum_eq_zero fun j hj => ?_
  by_cases h : TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i|
  · rw [if_pos (hch i (mem_range.mp hi) j (mem_range.mp hj) h), mul_zero]
  · have : IeU (Iq gl E vb oq t j i) = 0 := by
      simp only [IeU, Iq]; rw [if_neg h]
    simp [wR, this]

/-- **All three conditions together**: `κ = 1`, shift-closure and `Gch` coverage make the
static remainder of `SigAall` vanish. They are sufficient, not necessary (`nn_corAll_zero`). The witnesses
show that the `κ` and shift-closure conditions cannot simply be dropped: with the other
terms zero, either failing can leave a nonzero remainder (`sc_corAll`, `wit_cor`). -/
theorem cor_all_eq_zero (cp : Compl) (a : ℕ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st 1 cp t)
    (hs : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t, TS ≤ |Iq gl E vb oq t j i| →
      ShiftClosed st.Gk (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i)
        (gs (gl.qs.getD t default) j))
    (hch : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t,
      TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
        gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    CORall gl st E vb oq cp a = 0 := by
  rw [cor_all_decomp gl st E vb oq 1 cp a hc]
  refine sum_eq_zero fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [corScale_one, corShift_eq_zero gl st E vb oq t a (hs t ht'),
    corGch_eq_zero gl st E vb oq t a (hch t ht')]
  ring

/-- With the residual removed, `SigAall` is the exchange plus the GPP parts of all bands. -/
theorem sigAall_of_closure (cp : Compl) (a iw : ℕ)
    (hc : ∀ t < gl.qs.length, CompleteK gl st 1 cp t)
    (hs : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t, TS ≤ |Iq gl E vb oq t j i| →
      ShiftClosed st.Gk (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i)
        (gs (gl.qs.getD t default) j))
    (hch : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t,
      TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
        gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    SigAall gl st E vb oq cp a iw =
      (∑ t ∈ range gl.qs.length,
        (Xq gl vb st t a + ∑ n ∈ range (nbq st t), Pq gl E vb oq st t a n iw)) +
      tailD gl st E vb oq cp a iw := by
  rw [sigAall_static_split, cor_all_eq_zero gl st E vb oq cp a hc hs hch, add_zero]

/-! ### Relation to `chpart_sum_eq_exact` / `sigA_eq_theory_complete` -/

/-- **A complete state keeps `corShift + corGch`.** `Bloch.Complete` (the `hc` of
`chpart_sum_eq_exact`) removes only the scale term: the static remainder of such a state is
`corShift + corGch`, which the `hs`, `hch` hypotheses then remove. -/
theorem cor_decomp_complete (t a : ℕ)
    (hc : Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t)) :
    CSq gl E vb oq st t a + ∑ n ∈ range (nbq st t), ACq gl E vb oq st t a n =
      corShift gl st E vb oq t a + corGch gl st E vb oq t a := by
  have hp : ∀ G G', parP gl st t a G G' = cloP gl st t a G G' := fun G G' => by
    unfold parP cloP xS
    exact pd_closure_amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq
      (st.kq.getD t default).cq (nbq st t) G G' hc
  rw [csq_eq_w, acq_sum_eq_w]
  simp only [hp]
  unfold corShift corGch cloR
  simp only [mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem COR_decomp_complete (a : ℕ)
    (hc : ∀ t < gl.qs.length, Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t)) :
    COR gl E vb oq st a =
      ∑ t ∈ range gl.qs.length, (corShift gl st E vb oq t a + corGch gl st E vb oq t a) :=
  sum_congr rfl fun t ht => cor_decomp_complete gl st E vb oq t a (hc t (mem_range.mp ht))

/-- The hypotheses `hs`, `hch` of `chpart_sum_eq_exact` remove exactly the two remaining
terms (re-deriving `COR = 0` of `sigA_eq_theory_complete` through the decomposition). -/
theorem cor_eq_zero_of_closure (a : ℕ)
    (hc : ∀ t < gl.qs.length, Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t))
    (hs : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t, ShiftClosed st.Gk
      (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j))
    (hch : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t,
      TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
        gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    COR gl E vb oq st a = 0 := by
  rw [COR_decomp_complete gl st E vb oq a hc]
  refine sum_eq_zero fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [corShift_eq_zero gl st E vb oq t a (fun i hi j hj _ => hs t ht' i hi j hj),
    corGch_eq_zero gl st E vb oq t a (hch t ht'), add_zero]

end residual

/-! ### The completion by a larger dyadic state: `CORall` is its `COR` -/

section ofState

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

theorem tailA_term_complOf (st' : St) (nb t a n : ℕ) :
    quadR gl vb t (mR gl (trunc nb st') (complOf gl st' nb) t a n)
        (fun j i => IeU (Iq gl E vb oq t j i) / 4) = ACq gl E vb oq st' t a (nb + n) := by
  rw [quadR_complOf]
  unfold ACq quad
  simp only [mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- **Consistency.** For the completion by the further rows of a larger dyadic state `st'`,
the static remainder of `SigAall` is `st'`'s own `COR` (so `corAll` of the 168-band
diagnostic is the 168-band state's static remainder, not zero). -/
theorem corAll_of_state (st' : St) (a nb : ℕ) (hnb : ∀ t < gl.qs.length, nb ≤ nbq st' t) :
    CORall gl (trunc nb st') E vb oq (complOf gl st' nb) a = COR gl E vb oq st' a := by
  unfold CORall COR
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hA : ∑ n ∈ range nb, ACq gl E vb oq (trunc nb st') t a n =
      ∑ n ∈ range nb, ACq gl E vb oq st' t a n :=
    sum_congr rfl fun n hn => ACq_trunc gl E vb oq st' nb (mem_range.mp hn)
  have hT : tailA gl (trunc nb st') E vb oq (complOf gl st' nb) t a =
      ∑ n ∈ Ico nb (nbq st' t), ACq gl E vb oq st' t a n := by
    unfold tailA
    rw [sum_Ico_eq_sum_range]
    refine sum_congr rfl fun n _ => tailA_term_complOf gl E vb oq st' nb t a n
  rw [nbq_trunc st' nb (hnb t ht'), CSq_trunc, hA, hT, add_assoc,
    sum_range_add_sum_Ico _ (hnb t ht')]

end ofState

/-! ### Witnesses -/

section Witness

/-- The reviewer's run: WFN sphere `{0}`, eps sphere `{0, b}` (`b = (1,0,0)`), `q = 0`
with the head index `z = 0`, unit cell volume, one q-point, `Gch = {0}`. -/
def witGl : Gl :=
  { SC := 0, SEn := 0, SB := 0, B := [], SOm := 0, Om := 1, SR := 0, rho := [], Gch := [0],
    qs := [⟨0, [0, (1, 0, 0)], [], 0, [0, 1], [], 0⟩], nocc := 1 }

/-- The state: `c(0) = 1` at `k` and one band `c(0) = 1` at `k - q` (complete). -/
def witSt : St := ⟨[0], [[1]], [0], [⟨[0], [[1]], [0]⟩]⟩

/-- `eps⁻¹ = diag(1, ½)`, i.e. `I_eps = diag(0, ½)`. -/
noncomputable def witE : ℕ → ℕ → ℕ → ℝ := fun _ i j => if i = j then (if i = 0 then 1 else 1 / 2) else 0

/-- Unit Coulomb weights. -/
noncomputable def witV : V3 → ℝ := fun _ => 1

noncomputable def witO : V3 → ℝ := fun _ => 0

theorem TS_le_half : TS ≤ 1 / 2 := by unfold TS; norm_num

theorem wit_complete :
    Complete witGl (witSt.kq.getD 0 default).Gq (witSt.kq.getD 0 default).cq (nbq witSt 0) := by
  intro v hv v' hv'
  have hv0 : v = 0 := by simpa [witSt] using hv
  have hv0' : v' = 0 := by simpa [witSt] using hv'
  subst hv0 hv0'
  simp [witSt, witGl, nbq, dy]

theorem wit_not_shiftClosed :
    ¬ ShiftClosed witSt.Gk (witSt.kq.getD 0 default).Gq (1, 0, 0) (1, 0, 0) := by
  intro h
  have := h 0 (by simp [witSt]) 0 (by simp [witSt])
  simp [witSt, Prod.ext_iff, Finset.filter_singleton] at this

theorem wit_wR (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    wR witGl witE witV witO 0 i j = if i = 1 ∧ j = 1 then 1 / 8 else 0 := by
  have hA : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
  have hTS := TS_le_half
  interval_cases i <;> interval_cases j <;>
    (simp [wR, vS, IeU, Iq, IeS, epsS, witE, witV, witGl, Nq, vol, dy, gs]; try norm_num [hA, hTS])

theorem wit_shift : corShift witGl witSt witE witV witO 0 0 = -1 / 8 := by
  unfold corShift
  simp only [show nG witGl 0 = 2 from rfl, sum_range_succ, sum_range_zero]
  rw [wit_wR 0 0 (by norm_num) (by norm_num), wit_wR 0 1 (by norm_num) (by norm_num),
    wit_wR 1 0 (by norm_num) (by norm_num), wit_wR 1 1 (by norm_num) (by norm_num)]
  simp [cloR, rhoR, cloP, amp, pd, witSt, witGl, gs, dy, Prod.ext_iff]
  norm_num

theorem wit_gch : corGch witGl witSt witE witV witO 0 0 = 0 := by
  unfold corGch
  simp only [show nG witGl 0 = 2 from rfl, sum_range_succ, sum_range_zero]
  rw [wit_wR 0 0 (by norm_num) (by norm_num), wit_wR 0 1 (by norm_num) (by norm_num),
    wit_wR 1 0 (by norm_num) (by norm_num), wit_wR 1 1 (by norm_num) (by norm_num)]
  simp [witGl, gs]

/-- **The reviewer's witness.** The bands are complete, yet the static remainder is
`-1/8`, all of it shift-closure defect. -/
theorem wit_cor : COR witGl witE witV witO witSt 0 = -1 / 8 := by
  rw [COR_decomp_complete witGl witSt witE witV witO 0 (fun t ht => by
    have : t = 0 := by simpa [witGl] using ht
    subst this; exact wit_complete)]
  simp only [show witGl.qs.length = 1 from rfl, sum_range_one, wit_shift, wit_gch]
  norm_num

/-- The scaled-closure case: one unit channel `G = 0` with `I_eps = c`. -/
def scGl : Gl :=
  { SC := 0, SEn := 0, SB := 0, B := [], SOm := 0, Om := 1, SR := 0, rho := [], Gch := [0],
    qs := [⟨0, [0], [], 0, [0], [], 0⟩], nocc := 1 }

noncomputable def scE (c : ℝ) : ℕ → ℕ → ℕ → ℝ := fun _ _ _ => 1 - c

/-- One completion row `r` on the one-vector `k - q` sphere. -/
noncomputable def scCp (r : ℝ) : Compl := ⟨fun _ => 1, fun _ _ _ => r, fun _ _ => 0⟩

theorem sc_completeK (r : ℝ) : CompleteK scGl witSt (1 + r ^ 2) (scCp r) 0 := by
  intro v hv v' hv'
  have hv0 : v = 0 := by simpa [witSt] using hv
  have hv0' : v' = 0 := by simpa [witSt] using hv'
  subst hv0 hv0'
  simp [witSt, scGl, scCp, nbq, dy]
  ring

theorem sc_corAll (c r : ℝ) (hc : TS ≤ |c|) :
    CORall scGl witSt (scE c) witV witO (scCp r) 0 = r ^ 2 * c / 4 := by
  simp [CORall, tailA, CSq, ACq, quad, quadR, mR, amp, xS, pd, vS, IeU, Iq, IeS, epsS, scE,
    witV, witSt, scGl, scCp, Nq, vol, dy, gs, nbq, nG, hc]
  ring

/-- **The `(κ - 1) I/4` case**: here `CORall` is exactly the closure-scale term. -/
theorem sc_scale (c r : ℝ) (hc : TS ≤ |c|) :
    CORall scGl witSt (scE c) witV witO (scCp r) 0 = ((1 + r ^ 2) - 1) * c / 4 ∧
      corShift scGl witSt (scE c) witV witO 0 0 = 0 ∧ corGch scGl witSt (scE c) witV witO 0 0 = 0 := by
  refine ⟨by rw [sc_corAll c r hc]; ring, ?_, ?_⟩
  · simp [corShift, cloR, rhoR, cloP, amp, pd, witSt, scGl, gs, nG, dy]
  · simp [corGch, scGl, gs, nG]

/-! The three conditions of `cor_all_eq_zero` are not necessary (post-review R2). On the
reviewer's two-vector sphere with `Gch = ∅` and one completion row with `κ = 2`, all three
fail (`nn_scale_fails`, `nn_not_shiftClosed`, `nn_gch_misses`), and yet `CORall = 0`: the
shift-closure defect `-1/8` and the `Gch` term `+1/8` cancel (`nn_corAll_zero`). -/

/-- The reviewer's run with an empty `Gch`. -/
def nnGl : Gl :=
  { SC := 0, SEn := 0, SB := 0, B := [], SOm := 0, Om := 1, SR := 0, rho := [], Gch := [],
    qs := [⟨0, [0, (1, 0, 0)], [], 0, [0, 1], [], 0⟩], nocc := 1 }

/-- One completion row with unit coefficients, so `κ = 2`. -/
noncomputable def nnCp : Compl := ⟨fun _ => 1, fun _ _ _ => 1, fun _ _ => 0⟩

theorem nn_completeK : CompleteK nnGl witSt 2 nnCp 0 := by
  intro v hv v' hv'
  have hv0 : v = 0 := by simpa [witSt] using hv
  have hv0' : v' = 0 := by simpa [witSt] using hv'
  subst hv0 hv0'
  simp [witSt, nnGl, nnCp, nbq, dy]
  norm_num

theorem nn_wR (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    wR nnGl witE witV witO 0 i j = if i = 1 ∧ j = 1 then 1 / 8 else 0 := by
  have hA : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
  have hTS := TS_le_half
  interval_cases i <;> interval_cases j <;>
    (simp [wR, vS, IeU, Iq, IeS, epsS, witE, witV, nnGl, Nq, vol, dy, gs]; try norm_num [hA, hTS])

theorem nn_shift : corShift nnGl witSt witE witV witO 0 0 = -1 / 8 := by
  unfold corShift
  simp only [show nG nnGl 0 = 2 from rfl, sum_range_succ, sum_range_zero]
  rw [nn_wR 0 0 (by norm_num) (by norm_num), nn_wR 0 1 (by norm_num) (by norm_num),
    nn_wR 1 0 (by norm_num) (by norm_num), nn_wR 1 1 (by norm_num) (by norm_num)]
  simp [cloR, rhoR, cloP, amp, pd, witSt, nnGl, gs, dy, Prod.ext_iff]
  norm_num

theorem nn_gch : corGch nnGl witSt witE witV witO 0 0 = 1 / 8 := by
  unfold corGch
  simp only [show nG nnGl 0 = 2 from rfl, sum_range_succ, sum_range_zero]
  rw [nn_wR 0 0 (by norm_num) (by norm_num), nn_wR 0 1 (by norm_num) (by norm_num),
    nn_wR 1 0 (by norm_num) (by norm_num), nn_wR 1 1 (by norm_num) (by norm_num)]
  simp [rhoR, pd, witSt, nnGl, gs, dy, Prod.ext_iff]

theorem nn_scale : corScale nnGl witSt witE witV witO 2 0 0 = 0 := by
  unfold corScale
  simp only [show nG nnGl 0 = 2 from rfl, sum_range_succ, sum_range_zero]
  rw [nn_wR 0 0 (by norm_num) (by norm_num), nn_wR 0 1 (by norm_num) (by norm_num),
    nn_wR 1 0 (by norm_num) (by norm_num), nn_wR 1 1 (by norm_num) (by norm_num)]
  simp [cloR, cloP, amp, witSt, nnGl, gs, dy, Prod.ext_iff]

/-- **`CORall = 0` with all three conditions failing.** -/
theorem nn_corAll_zero : CORall nnGl witSt witE witV witO nnCp 0 = 0 := by
  rw [cor_all_decomp nnGl witSt witE witV witO 2 nnCp 0 (fun t ht => by
    have : t = 0 := by simpa [nnGl] using ht
    subst this; exact nn_completeK)]
  simp only [show nnGl.qs.length = 1 from rfl, sum_range_one, nn_scale, nn_shift, nn_gch]
  norm_num

/-- The scale condition fails: the completion is `CompleteK` at `κ = 2`, not at `κ = 1`. -/
theorem nn_scale_fails : ¬ CompleteK nnGl witSt 1 nnCp 0 := by
  intro h
  have := h 0 (by simp [witSt]) 0 (by simp [witSt])
  simp [witSt, nnGl, nnCp, nbq, dy] at this

/-- The shift-closure condition fails on a weighted pair. -/
theorem nn_not_shiftClosed :
    ¬ ShiftClosed witSt.Gk (witSt.kq.getD 0 default).Gq (1, 0, 0) (1, 0, 0) :=
  wit_not_shiftClosed

theorem nn_weighted : TS ≤ |Iq nnGl witE witV witO 0 1 1| := by
  have hA : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
  simp [Iq, IeS, epsS, witE, nnGl, hA, TS_le_half]
  norm_num [hA, TS_le_half]

/-- The `Gch` coverage condition fails on the same weighted pair. -/
theorem nn_gch_misses :
    gs (nnGl.qs.getD 0 default) 1 - gs (nnGl.qs.getD 0 default) 1 ∉ nnGl.Gch := by
  simp [nnGl]

end Witness

end GW.Bridge

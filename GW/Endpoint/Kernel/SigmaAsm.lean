/-
G2 stage 3, soundness (4c/4): assembly. The per-(state, q-point) enclosures sum to an
enclosure of `Σ_a Σ(E)` at the two energies (`sig_bounds`), and those give an
enclosure of `Eqp1` (`eqp1_bounds`) when the boxes put `Σ(Eo)` below `0` and `dΣ/dE`
below `1` (`hneg`, `hd`); there `Sig.eqp1` equals `Eo + Σ(Eo) / (1 - dΣ/dE)` (at
`dΣ/dE = 1` Lean's totalized division would make the two differ).
-/
import GW.Endpoint.Kernel.SigmaStq

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-- The hint total of one state at energy index `iw` (lower `k = 0` / upper `k = 1`), in
units `1 / (4 N_q Ω 2^SOUT)`. -/
noncomputable def Ltot (ds : ℕ → SQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (iw k : ℕ) : ℝ :=
  ∑ t ∈ range nq, ∑ a ∈ range nb,
    (4 * (if k = 0 then ((ds t).XO.getD a (0, 0)).1 else ((ds t).XO.getD a (0, 0)).2 : ℝ) +
      (if k = 0 then ((ds t).CO.getD a (0, 0)).1 else ((ds t).CO.getD a (0, 0)).2 : ℝ) +
      ∑ n1 ∈ range (nbs t), ((((ds t).O.getD a []).getD n1 []).getD (4 + k) 0 +
        2 * (((ds t).O.getD a []).getD n1 []).getD (2 * iw + k) 0 : ℝ))

/-- `Ltot` over the integers (kernel-evaluable). -/
def LtotZ (ds : ℕ → SQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (iw k : ℕ) : ℤ :=
  ∑ t ∈ range nq, ∑ a ∈ range nb,
    (4 * (if k = 0 then ((ds t).XO.getD a (0, 0)).1 else ((ds t).XO.getD a (0, 0)).2) +
      (if k = 0 then ((ds t).CO.getD a (0, 0)).1 else ((ds t).CO.getD a (0, 0)).2) +
      ∑ n1 ∈ range (nbs t), ((((ds t).O.getD a []).getD n1 []).getD (4 + k) 0 +
        2 * (((ds t).O.getD a []).getD n1 []).getD (2 * iw + k) 0))

theorem Ltot_cast (ds : ℕ → SQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (iw k : ℕ) :
    Ltot ds nq nb nbs iw k = (LtotZ ds nq nb nbs iw k : ℝ) := by
  unfold Ltot LtotZ
  push_cast
  refine sum_congr rfl fun t _ => sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

section asm

variable {gl : Gl} {st : St} {g : EG} {kc : KC} {SQq SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

/-- **The state total**: `Σ_a Σ_a(iw) · 4 N_q Ω 2^SOUT ∈ [Ltot iw 0, Ltot iw 1]`. -/
theorem sig_bounds (ds : ℕ → SQ)
    (h : ∀ t < gl.qs.length, StqOK gl st t (ds t) g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA)
    {E : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ}
    (hE : ∀ t < gl.qs.length, EHyp E (ds t).qd.iq (ds t).SO (ds t).Elo (ds t).Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hNq : 0 < Nq gl * vol gl) (iw : ℕ) (hiw : iw < 2) :
    Ltot ds gl.qs.length st.ck.length (nbq st) iw 0 ≤
        (∑ a ∈ range st.ck.length, SigA gl E vb oq st a iw) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
      (∑ a ∈ range st.ck.length, SigA gl E vb oq st a iw) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤
        Ltot ds gl.qs.length st.ck.length (nbq st) iw 1 := by
  have hS : ∀ a, SigA gl E vb oq st a iw * (Nq gl * vol gl) * 4 * 2 ^ SOUT = ∑ t ∈ range gl.qs.length,
      (4 * (Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT) + CSq gl E vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
        ∑ n1 ∈ range (nbq st t), (ACq gl E vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
          2 * (Pq gl E vb oq st t a n1 iw * (Nq gl * vol gl) * 2 * 2 ^ SOUT))) := by
    intro a
    unfold SigA
    rw [sum_mul, sum_mul, sum_mul]
    refine sum_congr rfl fun t _ => ?_
    rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, sum_mul, sum_mul, sum_mul]
    congr 1
    · ring
    · refine sum_congr rfl fun n1 _ => by ring
  rw [sum_mul, sum_mul, sum_mul]
  simp only [hS]
  rw [sum_comm]
  unfold Ltot
  constructor
  · refine sum_le_sum fun t ht => sum_le_sum fun a ha => ?_
    have ht' := mem_range.mp ht
    have ha' := mem_range.mp ha
    obtain ⟨x1, -⟩ := stq_x (h t ht') hvb hNq a ha'
    obtain ⟨c1, -⟩ := stq_cs (h t ht') (hE t ht') hvb hoq hNq a ha'
    have hn := stq_n (h t ht') (hE t ht') hvb hoq hNq a ha'
    rw [if_pos rfl, if_pos rfl]
    have : ∑ n1 ∈ range (nbq st t), ((((ds t).O.getD a []).getD n1 []).getD (4 + 0) 0 +
          2 * (((ds t).O.getD a []).getD n1 []).getD (2 * iw + 0) 0 : ℝ) ≤
        ∑ n1 ∈ range (nbq st t), (ACq gl E vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
          2 * (Pq gl E vb oq st t a n1 iw * (Nq gl * vol gl) * 2 * 2 ^ SOUT)) := by
      refine sum_le_sum fun n1 hn1 => ?_
      obtain ⟨p0, -, p2, -, a4, -⟩ := hn n1 (mem_range.mp hn1)
      have e4 : (((ds t).O.getD a []).getD n1 []).getD (4 + 0) 0 = (((ds t).O.getD a []).getD n1 []).getD 4 0 := rfl
      rw [e4]
      interval_cases iw
      · have e0 : (((ds t).O.getD a []).getD n1 []).getD (2 * 0 + 0) 0 = (((ds t).O.getD a []).getD n1 []).getD 0 0 := rfl
        rw [e0]; linarith
      · have e0 : (((ds t).O.getD a []).getD n1 []).getD (2 * 1 + 0) 0 = (((ds t).O.getD a []).getD n1 []).getD 2 0 := rfl
        rw [e0]; linarith
    linarith
  · refine sum_le_sum fun t ht => sum_le_sum fun a ha => ?_
    have ht' := mem_range.mp ht
    have ha' := mem_range.mp ha
    obtain ⟨-, x2⟩ := stq_x (h t ht') hvb hNq a ha'
    obtain ⟨-, c2⟩ := stq_cs (h t ht') (hE t ht') hvb hoq hNq a ha'
    have hn := stq_n (h t ht') (hE t ht') hvb hoq hNq a ha'
    rw [if_neg one_ne_zero, if_neg one_ne_zero]
    have : ∑ n1 ∈ range (nbq st t), (ACq gl E vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
          2 * (Pq gl E vb oq st t a n1 iw * (Nq gl * vol gl) * 2 * 2 ^ SOUT)) ≤
        ∑ n1 ∈ range (nbq st t), ((((ds t).O.getD a []).getD n1 []).getD (4 + 1) 0 +
          2 * (((ds t).O.getD a []).getD n1 []).getD (2 * iw + 1) 0 : ℝ) := by
      refine sum_le_sum fun n1 hn1 => ?_
      obtain ⟨-, p1, -, p3, -, a5⟩ := hn n1 (mem_range.mp hn1)
      have e5 : (((ds t).O.getD a []).getD n1 []).getD (4 + 1) 0 = (((ds t).O.getD a []).getD n1 []).getD 5 0 := rfl
      rw [e5]
      interval_cases iw
      · have e0 : (((ds t).O.getD a []).getD n1 []).getD (2 * 0 + 1) 0 = (((ds t).O.getD a []).getD n1 []).getD 1 0 := rfl
        rw [e0]; linarith
      · have e0 : (((ds t).O.getD a []).getD n1 []).getD (2 * 1 + 1) 0 = (((ds t).O.getD a []).getD n1 []).getD 3 0 := rfl
        rw [e0]; linarith
    linarith

end asm

/-- `s / (1 - d)` over a box with `s < 0`, `d < 1`. -/
theorem sd_bounds {s d A0 B0 dl dh : ℝ} (hs1 : A0 ≤ s) (hs2 : s ≤ B0) (hB : B0 < 0) (hd1 : dl ≤ d)
    (hd2 : d ≤ dh) (hdh : dh < 1) :
    A0 / (1 - dh) ≤ s / (1 - d) ∧ s / (1 - d) ≤ B0 / (1 - dl) := by
  have h1 : 0 < 1 - dh := by linarith
  have h2 : 0 < 1 - d := by linarith
  have h3 : 0 < 1 - dl := by linarith
  constructor
  · rw [div_le_div_iff₀ h1 h2]; nlinarith
  · rw [div_le_div_iff₀ h2 h3]; nlinarith

/-- **`Eqp1` enclosure** from the state totals: with `c = RYD / (nb N_q Ω 4 2^SOUT)`,
`Σ(E_iw) ∈ c [Lo_iw, Hi_iw]`, `Σ(Eo) < 0` and `dΣ/dE < 1` on the boxes
(`hneg : c Hi0 < 0`, `hd : c Hi1 - c Lo0 < 1`), `Sig.eqp1` lies in the stated interval;
there `Sig.eqp1` equals `Eo + Σ(Eo) / (1 - dΣ/dE)`. -/
theorem eqp1_bounds (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St) (SOUT : ℕ)
    {Lo0 Hi0 Lo1 Hi1 : ℝ} (hnb : 0 < st.ck.length) (hX : 0 < Nq gl * vol gl)
    (h0 : Lo0 ≤ (∑ a ∈ range st.ck.length, SigA gl E vb oq st a 0) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
      (∑ a ∈ range st.ck.length, SigA gl E vb oq st a 0) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤ Hi0)
    (h1 : Lo1 ≤ (∑ a ∈ range st.ck.length, SigA gl E vb oq st a 1) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
      (∑ a ∈ range st.ck.length, SigA gl E vb oq st a 1) * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤ Hi1)
    (hneg : RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) * Hi0 < 0)
    (hd : RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) * Hi1 -
      RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) * Lo0 < 1) :
    let c := RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT)
    let eo := avg st (fun a => RYD * dy gl.SEn (st.Ek.getD a 0))
    eo + c * Lo0 / (1 - (c * Hi1 - c * Lo0)) ≤ eqp1 gl E vb oq st ∧
      eqp1 gl E vb oq st ≤ eo + c * Hi0 / (1 - (c * Lo1 - c * Hi0)) := by
  intro c eo
  have hRY : (0 : ℝ) < RYD := by unfold RYD; norm_num
  have hnb' : (0 : ℝ) < st.ck.length := by exact_mod_cast hnb
  have hc : 0 < c := by positivity
  set S0 := ∑ a ∈ range st.ck.length, SigA gl E vb oq st a 0
  set S1 := ∑ a ∈ range st.ck.length, SigA gl E vb oq st a 1
  have hs : ∀ S : ℝ, S / st.ck.length * RYD = c * (S * (Nq gl * vol gl) * 4 * 2 ^ SOUT) := fun S => by
    have hne : (Nq gl * vol gl) * 4 * 2 ^ SOUT ≠ 0 := by positivity
    calc S / st.ck.length * RYD = RYD * S * ((Nq gl * vol gl) * 4 * 2 ^ SOUT) /
          (st.ck.length * ((Nq gl * vol gl) * 4 * 2 ^ SOUT)) := by
          rw [mul_div_mul_right _ _ hne]; ring
      _ = c * (S * (Nq gl * vol gl) * 4 * 2 ^ SOUT) := by simp only [c]; ring
  have hs0 : avg st (fun a => SigA gl E vb oq st a 0) * RYD = c * (S0 * (Nq gl * vol gl) * 4 * 2 ^ SOUT) := by
    unfold avg; exact hs S0
  have hs1 : avg st (fun a => SigA gl E vb oq st a 1) * RYD = c * (S1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT) := by
    unfold avg; exact hs S1
  set s0 := avg st (fun a => SigA gl E vb oq st a 0) * RYD
  set s1 := avg st (fun a => SigA gl E vb oq st a 1) * RYD
  have a1 : c * Lo0 ≤ s0 := by rw [hs0]; exact mul_le_mul_of_nonneg_left h0.1 hc.le
  have a2 : s0 ≤ c * Hi0 := by rw [hs0]; exact mul_le_mul_of_nonneg_left h0.2 hc.le
  have b1 : c * Lo1 ≤ s1 := by rw [hs1]; exact mul_le_mul_of_nonneg_left h1.1 hc.le
  have b2 : s1 ≤ c * Hi1 := by rw [hs1]; exact mul_le_mul_of_nonneg_left h1.2 hc.le
  have hdl : c * Lo1 - c * Hi0 ≤ s1 - s0 := by linarith
  have hdh : s1 - s0 ≤ c * Hi1 - c * Lo0 := by linarith
  have hsd := sd_bounds a1 a2 hneg hdl hdh hd
  have hform : eqp1 gl E vb oq st = eo + s0 / (1 - (s1 - s0)) := by
    have e : eqp1 gl E vb oq st = (eo + s0) + (s1 - s0) / 1 / (1 - (s1 - s0) / 1) * ((eo + s0) - eo) := rfl
    have hne : 1 - (s1 - s0) ≠ 0 := by linarith
    rw [e, div_one]
    field_simp
    ring
  rw [hform]
  constructor
  · linarith [hsd.1]
  · linarith [hsd.2]

/-- The eps⁻¹ box of a block from a stage-1/2 enclosure theorem: for the function `E`
equal to the matrix `M` on `Fin c.n` and `0` outside, whose entries are in the
certificate's box; the box lists have `n` rows of length `n`. -/
theorem EHyp_block (c : Cert) (M : Matrix (Fin c.n) (Fin c.n) ℝ)
    (hM : ∀ i j, M i j ∈ Set.Icc (c.mat c.SO c.outLo i j) (c.mat c.SO c.outHi i j))
    (hl1 : c.outLo.length = c.n) (hl2 : c.outHi.length = c.n)
    (hr1 : ∀ r ∈ c.outLo, r.length = c.n) (hr2 : ∀ r ∈ c.outHi, r.length = c.n)
    (E : ℕ → ℕ → ℕ → ℝ) (iq : ℕ) (hE : ∀ a b, E iq a b = if h : a < c.n ∧ b < c.n then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) :
    EHyp E iq c.SO c.outLo c.outHi := by
  intro a b
  rw [hE]
  split_ifs with h
  · exact hM ⟨a, h.1⟩ ⟨b, h.2⟩
  · have e : ∀ L : List (List ℤ), L.length = c.n → (∀ r ∈ L, r.length = c.n) → ent L a b = 0 := by
      intro L hL hr
      unfold ent
      by_cases ha : a < c.n
      · have hb : ¬ b < c.n := fun hb => h ⟨ha, hb⟩
        have hrow : (L.getD a []).length = c.n := hr _ (getD_mem [] (by omega))
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      · rw [List.getD_eq_getElem?_getD (l := L), List.getElem?_eq_none (by omega)]; simp
    rw [e _ hl1 hr1, e _ hl2 hr2]; simp

end GW.Endpoint.Kernel.Sig

/-
G2 roots, soundness (3/3, part 2): assembly of one root bracket of one multiplet.

From the per-(state, q-point) facts of `rq_n`, summed over q-points, bands and inner
bands (the totals `LtZ`, `DtZ` are kernel-evaluated integers):

* `f = fQP cv` is continuous on `[Ea, Eb]` with derivative `f' = dfQP` on `(Ea, Eb)`;
* `f' ∈ [c DLo - 1, c DHi - 1]` on `[Ea, Eb]`, and `c DHi - 1 < 0`;
* `f(Ec) > 0 > f(Ed)` for `Ea ≤ Ec ≤ Ed ≤ Eb`;
* no point of `[Ea, Eb]` is one where the source divides by zero (`SrcDefOn`),

hence (`root_bracket`): for either convention `cv` at `wx = wtilde`, `f` has exactly one
zero in `[Ea, Eb]`, it lies in `[Ec, Ed]`, and `[Ec, Ed]` is an `IsolatingBracket`.
-/
import GW.Endpoint.Kernel.RootStq
import GW.Endpoint.Kernel.SigmaAsm

namespace GW.Endpoint.Kernel.QP

open Finset Set GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-- The point-value total of one state at sign point `iw` (`0`: `Ec`, `1`: `Ed`), lower
(`k = 0`) / upper (`k = 1`), in units `1 / (4 N_q Ω 2^SOUT)`. -/
def LtZ (ds : ℕ → SQ) (rs : ℕ → RQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (iw k : ℕ) : ℤ :=
  ∑ t ∈ range nq, ∑ a ∈ range nb,
    (4 * (if k = 0 then ((ds t).XO.getD a (0, 0)).1 else ((ds t).XO.getD a (0, 0)).2) +
      (if k = 0 then ((ds t).CO.getD a (0, 0)).1 else ((ds t).CO.getD a (0, 0)).2) +
      ∑ n1 ∈ range (nbs t), ((((rs t).PO.getD a []).getD n1 []).getD (4 + k) 0 +
        2 * (((rs t).PO.getD a []).getD n1 []).getD (2 * iw + k) 0))

/-- The derivative total of one state (same units). -/
def DtZ (rs : ℕ → RQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (k : ℕ) : ℤ :=
  ∑ t ∈ range nq, ∑ a ∈ range nb, ∑ n1 ∈ range (nbs t),
    2 * (if k = 0 then (((rs t).DH.getD a []).getD n1 (0, 0)).1 else (((rs t).DH.getD a []).getD n1 (0, 0)).2)

theorem LtZ_cast (ds : ℕ → SQ) (rs : ℕ → RQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (iw k : ℕ) :
    (LtZ ds rs nq nb nbs iw k : ℝ) = ∑ t ∈ range nq, ∑ a ∈ range nb,
    (4 * (if k = 0 then ((ds t).XO.getD a (0, 0)).1 else ((ds t).XO.getD a (0, 0)).2 : ℝ) +
      (if k = 0 then ((ds t).CO.getD a (0, 0)).1 else ((ds t).CO.getD a (0, 0)).2 : ℝ) +
      ∑ n1 ∈ range (nbs t), ((((rs t).PO.getD a []).getD n1 []).getD (4 + k) 0 +
        2 * (((rs t).PO.getD a []).getD n1 []).getD (2 * iw + k) 0 : ℝ)) := by
  unfold LtZ
  push_cast
  refine sum_congr rfl fun t _ => sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

theorem DtZ_cast (rs : ℕ → RQ) (nq nb : ℕ) (nbs : ℕ → ℕ) (k : ℕ) :
    (DtZ rs nq nb nbs k : ℝ) = ∑ t ∈ range nq, ∑ a ∈ range nb, ∑ n1 ∈ range (nbs t),
    2 * (if k = 0 then (((rs t).DH.getD a []).getD n1 (0, 0)).1 else (((rs t).DH.getD a []).getD n1 (0, 0)).2 : ℝ) := by
  unfold DtZ
  push_cast
  refine sum_congr rfl fun t _ => sum_congr rfl fun a _ => sum_congr rfl fun n1 _ => ?_
  split_ifs <;> rfl

section asm

variable {gl : Gl} {st : St} {g : EG} {kc : KC} {SQq SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

theorem avg_eq (st : St) (f : ℕ → ℝ) (X : ℝ) (hX : 0 < X) (hnb : 0 < st.ck.length) :
    avg st f * RYD = RYD / (st.ck.length * X) * (∑ a ∈ range st.ck.length, f a * X) := by
  unfold avg
  rw [← sum_mul]
  have : (0 : ℝ) < st.ck.length := by exact_mod_cast hnb
  field_simp; ring

set_option maxHeartbeats 1000000 in
/-- **One root bracket of one multiplet.** -/
theorem root_bracket (ds : ℕ → SQ) (rs : ℕ → RQ)
    (h : ∀ t < gl.qs.length, StqOK gl st t (ds t) g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA)
    {Ep : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ}
    (hE : ∀ t < gl.qs.length, EHyp Ep (ds t).qd.iq (ds t).SO (ds t).Elo (ds t).Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hNq : 0 < Nq gl * vol gl) (hnb : 0 < st.ck.length) (hq0 : 0 < gl.qs.length) {Ca Cb Cc Cd : ℤ}
    (hr : ∀ t < gl.qs.length, RqOK st (ds t) g kc gl.nocc RN she tz Ca Cb Cc Cd (rs t))
    (hac : Ca ≤ Cc) (hcd : Cc ≤ Cd) (hdb : Cd ≤ Cb)
    (hder : RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) *
      DtZ rs gl.qs.length st.ck.length (nbq st) 1 - 1 < 0)
    (hfc : 0 < emf gl st + RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) *
      LtZ ds rs gl.qs.length st.ck.length (nbq st) 0 0 - (Cc : ℝ) / g.Den)
    (hfd : emf gl st + RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT) *
      LtZ ds rs gl.qs.length st.ck.length (nbq st) 1 1 - (Cd : ℝ) / g.Den < 0) :
    let Ea := (Ca : ℝ) / g.Den
    let Eb := (Cb : ℝ) / g.Den
    let Ec := (Cc : ℝ) / g.Den
    let Ed := (Cd : ℝ) / g.Den
    let c := RYD / (st.ck.length * (Nq gl * vol gl) * 4 * 2 ^ SOUT)
    SrcDefOn gl Ep vb oq st Ea Eb ∧
    (∀ E ∈ Icc Ea Eb, c * DtZ rs gl.qs.length st.ck.length (nbq st) 0 - 1 ≤ dfQP gl Ep vb oq st E ∧
      dfQP gl Ep vb oq st E ≤ c * DtZ rs gl.qs.length st.ck.length (nbq st) 1 - 1) ∧
    ∀ cv : Bool,
      IsolatingBracket (fQP gl Ep vb oq st cv) (dfQP gl Ep vb oq st) Ec Ed ∧
      (∃! E, E ∈ Icc Ea Eb ∧ fQP gl Ep vb oq st cv E = 0) ∧
      ∀ E ∈ Icc Ea Eb, fQP gl Ep vb oq st cv E = 0 → E ∈ Icc Ec Ed := by
  intro Ea Eb Ec Ed c
  have hD : (0 : ℝ) < g.Den := by exact_mod_cast (h 0 hq0).hDen0
  have hRQ := fun t (ht : t < gl.qs.length) => rq_n (h t ht) (hE t ht) hvb hoq hNq (hr t ht) hac hcd hdb
  have hRY : (0 : ℝ) < RYD := by unfold RYD; norm_num
  have hnb' : (0 : ℝ) < st.ck.length := by exact_mod_cast hnb
  have hc : 0 < c := by positivity
  have hK : (0 : ℝ) < (Nq gl * vol gl) * 4 * 2 ^ SOUT := by positivity
  -- f and f' in terms of scaled sums
  have hf : ∀ cv E, fQP gl Ep vb oq st cv E = emf gl st + c * (∑ a ∈ range st.ck.length,
      SigE gl Ep vb oq st cv a E * ((Nq gl * vol gl) * 4 * 2 ^ SOUT)) - E := by
    intro cv E
    unfold fQP
    rw [avg_eq st _ ((Nq gl * vol gl) * 4 * 2 ^ SOUT) hK hnb]
    simp only [c]; ring_nf
  have hdf : ∀ E, dfQP gl Ep vb oq st E = c * (∑ a ∈ range st.ck.length, ∑ t ∈ range gl.qs.length,
      ∑ n1 ∈ range (nbq st t), dPqE gl Ep vb oq st t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT * 2) - 1 := by
    intro E
    unfold dfQP
    rw [avg_eq st _ ((Nq gl * vol gl) * 4 * 2 ^ SOUT) hK hnb]
    simp only [c, sum_mul]
    congr 2
    · ring
    · refine sum_congr rfl fun a _ => sum_congr rfl fun t _ => sum_congr rfl fun n1 _ => by ring
  have hS : ∀ cv a E, SigE gl Ep vb oq st cv a E * ((Nq gl * vol gl) * 4 * 2 ^ SOUT) = ∑ t ∈ range gl.qs.length,
      (4 * (Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT) + CSq gl Ep vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
        ∑ n1 ∈ range (nbq st t), (ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
          2 * (PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT))) := by
    intro cv a E
    unfold SigE
    rw [sum_mul]
    refine sum_congr rfl fun t _ => ?_
    rw [add_mul, add_mul, sum_mul]
    congr 1
    · ring
    · refine sum_congr rfl fun n1 _ => by ring
  -- continuity and derivative
  have hfix : ∀ cv, FixedOn (fQP gl Ep vb oq st cv) (dfQP gl Ep vb oq st) Ea Eb := by
    intro cv
    have hP : FixedOn (fun E => ∑ a ∈ range st.ck.length, ∑ t ∈ range gl.qs.length,
        ∑ n1 ∈ range (nbq st t), PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT * 2)
        (fun E => ∑ a ∈ range st.ck.length, ∑ t ∈ range gl.qs.length,
        ∑ n1 ∈ range (nbq st t), dPqE gl Ep vb oq st t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT * 2) Ea Eb := by
      refine FixedOn.sum _ fun a ha => FixedOn.sum _ fun t ht => FixedOn.sum _ fun n1 hn1 => ?_
      have := ((hRQ t (mem_range.mp ht) a (mem_range.mp ha) n1 (mem_range.mp hn1)).1 cv).mul_const
        ((Nq gl * vol gl) * 2 * 2 ^ SOUT * 2)
      exact this.congr (fun E _ => by ring) (fun E _ => by ring)
    set K0 := ∑ a ∈ range st.ck.length, ∑ t ∈ range gl.qs.length,
      (4 * (Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT) + CSq gl Ep vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
        ∑ n1 ∈ range (nbq st t), ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT)
    have hall := ((FixedOn.const (emf gl st + c * K0) Ea Eb).add (hP.const_mul c)).sub (FixedOn.id' Ea Eb)
    refine hall.congr (fun E _ => ?_) (fun E _ => ?_)
    · rw [hf cv E]
      have e : ∑ a ∈ range st.ck.length, SigE gl Ep vb oq st cv a E * ((Nq gl * vol gl) * 4 * 2 ^ SOUT) = K0 +
          ∑ a ∈ range st.ck.length, ∑ t ∈ range gl.qs.length,
            ∑ n1 ∈ range (nbq st t), PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT * 2 := by
        simp only [hS, K0]
        rw [← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun t _ => ?_
        rw [sum_add_distrib]
        have e2 : ∑ n1 ∈ range (nbq st t), 2 * (PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT) =
            ∑ n1 ∈ range (nbq st t), PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT * 2 :=
          sum_congr rfl fun _ _ => by ring
        rw [e2]; ring
      rw [e]; ring
    · rw [hdf E]; ring
  -- derivative bounds
  have hdb' : ∀ E ∈ Icc Ea Eb, c * DtZ rs gl.qs.length st.ck.length (nbq st) 0 - 1 ≤ dfQP gl Ep vb oq st E ∧
      dfQP gl Ep vb oq st E ≤ c * DtZ rs gl.qs.length st.ck.length (nbq st) 1 - 1 := by
    intro E hE
    rw [hdf E, DtZ_cast, DtZ_cast, sum_comm (s := range gl.qs.length)]
    constructor
    · refine sub_le_sub_right (mul_le_mul_of_nonneg_left (sum_le_sum fun a ha => sum_le_sum fun t ht =>
        sum_le_sum fun n1 hn1 => ?_) hc.le) _
      obtain ⟨-, hd, -⟩ := hRQ t (mem_range.mp ht) a (mem_range.mp ha) n1 (mem_range.mp hn1)
      have := (hd E hE).1
      simp only [if_true]; linarith
    · rw [sum_comm (s := range gl.qs.length)]
      refine sub_le_sub_right (mul_le_mul_of_nonneg_left (sum_le_sum fun a ha => sum_le_sum fun t ht =>
        sum_le_sum fun n1 hn1 => ?_) hc.le) _
      obtain ⟨-, hd, -⟩ := hRQ t (mem_range.mp ht) a (mem_range.mp ha) n1 (mem_range.mp hn1)
      have := (hd E hE).2
      simp only [one_ne_zero, if_false]; linarith
  have hneg : ∀ E ∈ Icc Ea Eb, dfQP gl Ep vb oq st E < 0 := fun E hE => lt_of_le_of_lt (hdb' E hE).2 hder
  -- point values
  have hPb : ∀ cv (iw : ℕ), iw < 2 → ∀ t < gl.qs.length, ∀ a < st.ck.length, ∀ n1 < nbq st t,
      ((((rs t).PO.getD a []).getD n1 []).getD (2 * iw + 0) 0 : ℝ) ≤
        PqE gl Ep vb oq st cv t a n1 (if iw = 0 then Ec else Ed) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
      PqE gl Ep vb oq st cv t a n1 (if iw = 0 then Ec else Ed) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤
        ((((rs t).PO.getD a []).getD n1 []).getD (2 * iw + 1) 0 : ℝ) := by
    intro cv iw hiw t ht a ha n1 hn1
    obtain ⟨-, -, hp, -⟩ := hRQ t ht a ha n1 hn1
    obtain ⟨⟨p0, p1⟩, ⟨p2, p3⟩⟩ := hp cv
    interval_cases iw
    · exact ⟨p0, p1⟩
    · exact ⟨p2, p3⟩
  have hval : ∀ cv (iw : ℕ), iw < 2 →
      c * LtZ ds rs gl.qs.length st.ck.length (nbq st) iw 0 ≤ c * (∑ a ∈ range st.ck.length,
        SigE gl Ep vb oq st cv a (if iw = 0 then Ec else Ed) * ((Nq gl * vol gl) * 4 * 2 ^ SOUT)) ∧
      c * (∑ a ∈ range st.ck.length, SigE gl Ep vb oq st cv a (if iw = 0 then Ec else Ed) * ((Nq gl * vol gl) * 4 * 2 ^ SOUT)) ≤
        c * LtZ ds rs gl.qs.length st.ck.length (nbq st) iw 1 := by
    intro cv iw hiw
    simp only [hS]
    rw [sum_comm (s := range st.ck.length), LtZ_cast, LtZ_cast]
    constructor
    · refine mul_le_mul_of_nonneg_left (sum_le_sum fun t ht => sum_le_sum fun a ha => ?_) hc.le
      have ht' := mem_range.mp ht
      have ha' := mem_range.mp ha
      obtain ⟨x1, -⟩ := stq_x (h t ht') hvb hNq a ha'
      obtain ⟨c1, -⟩ := stq_cs (h t ht') (hE t ht') hvb hoq hNq a ha'
      rw [if_pos rfl, if_pos rfl]
      have : ∑ n1 ∈ range (nbq st t), ((((rs t).PO.getD a []).getD n1 []).getD (4 + 0) 0 +
            2 * (((rs t).PO.getD a []).getD n1 []).getD (2 * iw + 0) 0 : ℝ) ≤
          ∑ n1 ∈ range (nbq st t), (ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
            2 * (PqE gl Ep vb oq st cv t a n1 (if iw = 0 then Ec else Ed) * (Nq gl * vol gl) * 2 * 2 ^ SOUT)) := by
        refine sum_le_sum fun n1 hn1 => ?_
        obtain ⟨-, -, -, ha4, -⟩ := hRQ t ht' a ha' n1 (mem_range.mp hn1)
        have := (hPb cv iw hiw t ht' a ha' n1 (mem_range.mp hn1)).1
        linarith [ha4.1]
      linarith
    · refine mul_le_mul_of_nonneg_left (sum_le_sum fun t ht => sum_le_sum fun a ha => ?_) hc.le
      have ht' := mem_range.mp ht
      have ha' := mem_range.mp ha
      obtain ⟨-, x2⟩ := stq_x (h t ht') hvb hNq a ha'
      obtain ⟨-, c2⟩ := stq_cs (h t ht') (hE t ht') hvb hoq hNq a ha'
      rw [if_neg one_ne_zero, if_neg one_ne_zero]
      have : ∑ n1 ∈ range (nbq st t), (ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT +
            2 * (PqE gl Ep vb oq st cv t a n1 (if iw = 0 then Ec else Ed) * (Nq gl * vol gl) * 2 * 2 ^ SOUT)) ≤
          ∑ n1 ∈ range (nbq st t), ((((rs t).PO.getD a []).getD n1 []).getD (4 + 1) 0 +
            2 * (((rs t).PO.getD a []).getD n1 []).getD (2 * iw + 1) 0 : ℝ) := by
        refine sum_le_sum fun n1 hn1 => ?_
        obtain ⟨-, -, -, ha4, -⟩ := hRQ t ht' a ha' n1 (mem_range.mp hn1)
        have := (hPb cv iw hiw t ht' a ha' n1 (mem_range.mp hn1)).2
        linarith [ha4.2]
      linarith
  have hfc' : ∀ cv, 0 < fQP gl Ep vb oq st cv Ec := fun cv => by
    rw [hf cv Ec]; have := (hval cv 0 (by norm_num)).1; simp only [c, Ec, ↓reduceIte] at this ⊢; linarith
  have hfd' : ∀ cv, fQP gl Ep vb oq st cv Ed < 0 := fun cv => by
    rw [hf cv Ed]; have := (hval cv 1 (by norm_num)).2; simp only [c, Ed, one_ne_zero, ↓reduceIte] at this ⊢; linarith
  -- non-singularity
  have hsrc : SrcDefOn gl Ep vb oq st Ea Eb := by
    intro E hE t ht n1 hn1 i hi j hj hk
    exact (hRQ t ht 0 hnb n1 hn1).2.2.2.2 E hE i hi j hj hk
  refine ⟨hsrc, hdb', fun cv => ?_⟩
  have hEa : Ea ≤ Ec := div_le_div_of_nonneg_right (by exact_mod_cast hac) hD.le
  have hEcd : Ec ≤ Ed := div_le_div_of_nonneg_right (by exact_mod_cast hcd) hD.le
  have hEb : Ed ≤ Eb := div_le_div_of_nonneg_right (by exact_mod_cast hdb) hD.le
  have hanti := strictAntiOn_Icc_of_hasDerivAt_neg (hfix cv).1
    (fun x hx => ⟨(hfix cv).2 x hx, hneg x (Ioo_subset_Icc_self hx)⟩)
  have hsub : Icc Ec Ed ⊆ Icc Ea Eb := Icc_subset_Icc hEa hEb
  have hIB : IsolatingBracket (fQP gl Ep vb oq st cv) (dfQP gl Ep vb oq st) Ec Ed := by
    refine ⟨hEcd, (hfix cv).1.mono hsub, Or.inl fun x hx => ?_, ?_⟩
    · have hx' : x ∈ Ioo Ea Eb := ⟨lt_of_le_of_lt hEa hx.1, lt_of_lt_of_le hx.2 hEb⟩
      exact ⟨(hfix cv).2 x hx', hneg x (Ioo_subset_Icc_self hx')⟩
    · have := hfc' cv; have := hfd' cv; nlinarith
  have hin : ∀ E ∈ Icc Ea Eb, fQP gl Ep vb oq st cv E = 0 → E ∈ Icc Ec Ed := by
    intro E hE hz
    have hcI : Ec ∈ Icc Ea Eb := ⟨hEa, le_trans hEcd hEb⟩
    have hdI : Ed ∈ Icc Ea Eb := ⟨le_trans hEa hEcd, hEb⟩
    constructor
    · rcases lt_or_le E Ec with hlt | hlt
      · have := hanti hE hcI hlt; linarith [hfc' cv]
      · exact hlt
    · rcases lt_or_le Ed E with hlt | hlt
      · have := hanti hdI hE hlt; linarith [hfd' cv]
      · exact hlt
  obtain ⟨r, ⟨hr1, hr2⟩, -⟩ := hIB.existsUnique
  refine ⟨hIB, ⟨r, ⟨hsub hr1, hr2⟩, fun E ⟨hE, hz⟩ => ?_⟩, hin⟩
  exact hanti.injOn hE (hsub hr1) (hz.trans hr2.symm)

end asm

end GW.Endpoint.Kernel.QP

/-
G2 roots, soundness (3/3, part 1): one (state, q-point). From stage 3's kernel-checked
facts `StqOK` and the new checks of a root bracket (the derivative check `dOK` over
`[Ea, Eb]` and stage 3's `nOK` at two point energies `Ec`, `Ed`) the E-dependent part
`PqE` of every (band, inner band) is continuous on `[Ea, Eb]` with derivative `dPqE`,
`dPqE` is in the claimed enclosure there, no point of `[Ea, Eb]` is one where the
source divides by zero, and `PqE(Ec)`, `PqE(Ed)`, `ACq` are in their claimed enclosures
(`rq_n`).
-/
import GW.Endpoint.Kernel.RootHot
import GW.Endpoint.Kernel.SigmaStq

namespace GW.Endpoint.Kernel.QP

open Finset Set GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### Energies -/

theorem mkEnP_spec {RN sh tz SEn : ℕ} {D1 : ℕ} (C eq : ℤ)
    (hRN : (RN : ℝ) / 10 ^ 8 = RYD) (hD1 : (D1 : ℝ) = 10 ^ 8 * 2 ^ (SEn + sh)) (htz : (tz : ℝ) = TZ * D1) :
    Enok (mkEnP RN sh tz C eq) D1
      (let w := (C : ℝ) / D1 - RYD * dy SEn eq; if |w| < TZ then TZ else w) := by
  have hD : (0 : ℝ) < D1 := by rw [hD1]; positivity
  set x : ℤ := C - (RN : ℤ) * eq * 2 ^ sh with hx
  have hw : ((C : ℝ) / D1 - RYD * dy SEn eq) * D1 = x := by
    rw [hx, ← hRN]; unfold dy; push_cast
    rw [hD1, pow_add]; field_simp; ring
  have hxabs : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  unfold mkEnP
  dsimp only
  rw [← hx]
  by_cases hs : x.natAbs < tz
  · have hb : Nat.blt x.natAbs tz = true := Nat.blt_eq.mpr hs
    rw [hb, cond_true]
    have hlt : |(C : ℝ) / D1 - RYD * dy SEn eq| < TZ := by
      have : |(x : ℝ)| < tz := by rw [← hxabs]; exact_mod_cast hs
      rw [← hw, abs_mul, abs_of_pos hD, htz] at this
      exact lt_of_mul_lt_mul_right this hD.le
    rw [if_pos hlt]
    exact ⟨by rw [htz]; simp, rfl, fun h => absurd h (by simp)⟩
  · have hb : Nat.blt x.natAbs tz = false := by rw [blt_d]; simpa using hs
    rw [hb, cond_false]
    have hge : ¬ |(C : ℝ) / D1 - RYD * dy SEn eq| < TZ := by
      intro hlt
      apply hs
      have : |(x : ℝ)| < tz := by
        rw [← hw, abs_mul, abs_of_pos hD, htz]; exact mul_lt_mul_of_pos_right hlt hD
      rw [← hxabs] at this; exact_mod_cast this
    rw [if_neg hge]
    refine ⟨?_, rfl, fun h => ?_⟩
    · simp only
      rw [hw]
      rcases lt_or_le x 0 with hn | hn
      · simp only [hn, decide_true, sg_true]; rw [hxabs, abs_of_neg (by exact_mod_cast hn)]; ring
      · simp only [not_lt.mpr hn, decide_false, sg_false]; rw [hxabs, abs_of_nonneg (by exact_mod_cast hn)]
    · simp only [decide_eq_true_eq] at h; exact Int.natAbs_pos.mpr (by omega)

/-- The interval energy: `wx` has one sign and `|wx| ≥ TOL_Zero` on `[Ca, Cb] / D1`, and
the record encloses it. -/
theorem mkEI_spec {RN sh tz SEn : ℕ} {D1 : ℕ} (Ca Cb eq : ℤ)
    (hRN : (RN : ℝ) / 10 ^ 8 = RYD) (hD1 : (D1 : ℝ) = 10 ^ 8 * 2 ^ (SEn + sh)) (htz : (tz : ℝ) = TZ * D1)
    (h : (mkEI RN sh tz Ca Cb eq).2 = true) :
    EIok (mkEI RN sh tz Ca Cb eq).1 D1 ((Ca : ℝ) / D1 - RYD * dy SEn eq) ((Cb : ℝ) / D1 - RYD * dy SEn eq) ∧
      ∀ E ∈ Icc ((Ca : ℝ) / D1) ((Cb : ℝ) / D1), TZ ≤ |E - RYD * dy SEn eq| := by
  have hD : (0 : ℝ) < D1 := by rw [hD1]; positivity
  have htz0 : (0 : ℝ) < tz := by rw [htz]; unfold TZ; positivity
  set xa : ℤ := Ca - (RN : ℤ) * eq * 2 ^ sh with hxa
  set xb : ℤ := Cb - (RN : ℤ) * eq * 2 ^ sh with hxb
  have hw : ∀ C : ℤ, ((C : ℝ) / D1 - RYD * dy SEn eq) * D1 = ((C - (RN : ℤ) * eq * 2 ^ sh : ℤ) : ℝ) := by
    intro C; rw [← hRN]; unfold dy; push_cast
    rw [hD1, pow_add]; field_simp; ring
  -- a point E of the interval, scaled
  have hmem : ∀ E ∈ Icc ((Ca : ℝ) / D1) ((Cb : ℝ) / D1),
      (xa : ℝ) ≤ (E - RYD * dy SEn eq) * D1 ∧ (E - RYD * dy SEn eq) * D1 ≤ xb := by
    intro E hE
    have e1 : (E - RYD * dy SEn eq) * D1 = E * D1 - RN * eq * 2 ^ sh := by
      rw [← hRN]; unfold dy; rw [hD1, pow_add]; field_simp; ring
    have ha := hw Ca
    have hb := hw Cb
    rw [← hxa] at ha; rw [← hxb] at hb
    have c1 : (Ca : ℝ) ≤ E * D1 := by have := mul_le_mul_of_nonneg_right hE.1 hD.le; rwa [div_mul_cancel₀ _ hD.ne'] at this
    have c2 : E * D1 ≤ Cb := by have := mul_le_mul_of_nonneg_right hE.2 hD.le; rwa [div_mul_cancel₀ _ hD.ne'] at this
    constructor
    · rw [← ha, e1]; have : ((Ca : ℝ) / D1 - RYD * dy SEn eq) * D1 = Ca - RN * eq * 2 ^ sh := by
        rw [← hRN]; unfold dy; rw [hD1, pow_add]; field_simp; ring
      rw [this]; linarith
    · rw [← hb, e1]; have : ((Cb : ℝ) / D1 - RYD * dy SEn eq) * D1 = Cb - RN * eq * 2 ^ sh := by
        rw [← hRN]; unfold dy; rw [hD1, pow_add]; field_simp; ring
      rw [this]; linarith
  have hxabs : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := fun z => by rw [Nat.cast_natAbs, Int.cast_abs]
  unfold mkEI at h ⊢
  dsimp only at h ⊢
  rw [← hxa, ← hxb] at h ⊢
  by_cases c1 : (tz : ℤ) ≤ xa ∧ xa ≤ xb
  · rw [if_pos c1]
    have ha0 : (0 : ℤ) ≤ xa := le_trans (by positivity) c1.1
    have hb0 : (0 : ℤ) ≤ xb := le_trans ha0 c1.2
    have ea : ((xa.natAbs : ℕ) : ℝ) = xa := by rw [hxabs, abs_of_nonneg (by exact_mod_cast ha0)]
    have eb : ((xb.natAbs : ℕ) : ℝ) = xb := by rw [hxabs, abs_of_nonneg (by exact_mod_cast hb0)]
    have htza : (tz : ℝ) ≤ xa := by exact_mod_cast c1.1
    refine ⟨⟨?_, rfl, rfl, fun y hy => ?_⟩, fun E hE => ?_⟩
    · have : (0 : ℝ) < xa.natAbs := by rw [ea]; linarith
      exact_mod_cast this
    · -- y = E - e with E ∈ [Ca, Cb] / D1
      have hE : y + RYD * dy SEn eq ∈ Icc ((Ca : ℝ) / D1) ((Cb : ℝ) / D1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := hmem _ hE
      simp only [add_sub_cancel_right] at this
      simp only [sg_false, ea, eb]; exact this
    · have := (hmem E hE).1
      have h2 : TZ * D1 ≤ (E - RYD * dy SEn eq) * D1 := by rw [← htz]; linarith
      have h3 := le_of_mul_le_mul_right h2 hD
      exact le_trans h3 (le_abs_self _)
  · rw [if_neg c1] at h ⊢
    by_cases c2 : xb ≤ -(tz : ℤ) ∧ xa ≤ xb
    · rw [if_pos c2]
      have hb0 : xb ≤ 0 := le_trans c2.1 (by simp)
      have ha0 : xa ≤ 0 := le_trans c2.2 hb0
      have ea : ((xa.natAbs : ℕ) : ℝ) = -xa := by rw [hxabs, abs_of_nonpos (by exact_mod_cast ha0)]
      have eb : ((xb.natAbs : ℕ) : ℝ) = -xb := by rw [hxabs, abs_of_nonpos (by exact_mod_cast hb0)]
      have htzb : (xb : ℝ) ≤ -tz := by exact_mod_cast c2.1
      refine ⟨⟨?_, rfl, rfl, fun y hy => ?_⟩, fun E hE => ?_⟩
      · have : (0 : ℝ) < xb.natAbs := by rw [eb]; linarith
        exact_mod_cast this
      · have hE : y + RYD * dy SEn eq ∈ Icc ((Ca : ℝ) / D1) ((Cb : ℝ) / D1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have := hmem _ hE
        simp only [add_sub_cancel_right] at this
        simp only [sg_true, ea, eb]; constructor <;> linarith [this.1, this.2]
      · have := (hmem E hE).2
        have h2 : TZ * D1 ≤ -((E - RYD * dy SEn eq) * D1) := by rw [← htz]; linarith
        have h3 : TZ * D1 ≤ -(E - RYD * dy SEn eq) * D1 := by linarith
        have h4 := le_of_mul_le_mul_right h3 hD
        exact le_trans h4 (neg_le_abs _)
    · rw [if_neg c2] at h; exact absurd h (by simp)


/-! ### The quadratic forms of one (band, inner band), scaled -/

section rq

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQq SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

/-- The weights of the hot path of `(a, n1)`. -/
noncomputable def Wq (d : SQ) (a n1 : ℕ) (k : ℕ) : ℝ :=
  wv ((xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).getD k (false, 0))

/-- The check's form `Σ_i Σ_j W_i V_i W_j F(j, i)`. -/
noncomputable def Qc (d : SQ) (g : EG) (vb : V3 → ℝ) (a n1 : ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ range d.qd.Gs.length, ∑ j ∈ range d.qd.Gs.length,
    Wq d a n1 i * (vb (key d.qd (gs d.qd i)) * 2 ^ g.SV) * Wq d a n1 j * F j i

theorem quad_scaled (h : StqOK gl st t d g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA) {vb : V3 → ℝ}
    (hNq : 0 < Nq gl * vol gl) {a n1 : ℕ} (ha : a < st.ck.length) (hn1 : n1 < d.kq.cq.length) :
    (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).length = d.qd.Gs.length ∧
    ∀ F : ℕ → ℕ → ℝ, quad gl vb st t a n1 F * (Nq gl * vol gl) * 2 ^ SOUT =
      Qc d g vb a n1 (fun j i => 2 ^ g.SI * F j i) / 2 ^ ((d.sh.getD a []).getD n1 0) := by
  set Tx := (d.Tx.getD a []).getD n1 0 with hTx
  set hr := (d.H.getD a []).getD n1 [] with hhr
  set xs := xsOf Tx hr with hxsd
  obtain ⟨hrl, hxS⟩ := stq_xS h ha hn1
  have hxl : xs.length = d.qd.Gs.length := by rw [hxsd, xsOf_length, hrl]
  refine ⟨hxl, fun F => ?_⟩
  set W := fun k => wv (xs.getD k (false, 0))
  set V := fun i => vb (key d.qd (gs d.qd i)) * 2 ^ g.SV
  set c := (2 : ℝ) ^ Tx / 2 ^ (2 * gl.SC)
  set u := 1 / (2 ^ g.SV * (Nq gl * vol gl))
  have hq := h.hq
  have hxk : ∀ k < (gl.qs.getD t default).Gs.length, xS gl st t a n1 (gs (gl.qs.getD t default) k) = W k * c := by
    intro k hk; rw [hq] at hk; exact hxS k hk
  have hvk : ∀ k < (gl.qs.getD t default).Gs.length, vS gl vb (gl.qs.getD t default) k = V k * u := by
    intro k _; rw [hq]; unfold vS; simp only [V, u]
    have hS : (0 : ℝ) < 2 ^ g.SV := by positivity
    rw [mul_one_div, mul_comm ((2 : ℝ) ^ g.SV) (Nq gl * vol gl), mul_div_mul_right _ _ hS.ne']
  have hQ := quad_eq gl vb st t a n1 F W V c u hxk hvk
  rw [hq] at hQ
  have hsh := h.hsh
  obtain ⟨-, hs1⟩ := all2_spec _ [] [] _ _ hsh
  obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkok
  have hlenT : a < d.sh.length := by
    obtain ⟨hl1, -⟩ := all2_spec _ [] [] _ _ hsh
    obtain ⟨hl3, -⟩ := all2_spec _ [] [] _ _ h.hxs
    rw [hl1, ← hl3, hHl]; exact ha
  have hs2 := hs1 a hlenT
  obtain ⟨hl4, hs3⟩ := all2_spec _ 0 0 _ _ hs2
  have hn1T : n1 < (d.sh.getD a []).length := by
    obtain ⟨hl3, hl3'⟩ := all2_spec _ [] [] _ _ h.hxs
    obtain ⟨hl5, -⟩ := all2_spec _ [] 0 _ _ (hl3' a (by rw [hHl]; exact ha))
    rw [hl4, ← hl5, (hH a ha).1]; exact hn1
  have hs4 := hs3 n1 hn1T
  simp only [Bool.and_eq_true, ble_d, beq_d, decide_eq_true_eq] at hs4
  obtain ⟨hTx2, hshe⟩ := hs4
  set shv := (d.sh.getD a []).getD n1 0
  have hscale : c ^ 2 * u * (Nq gl * vol gl) / 2 ^ g.SI * 2 ^ SOUT = 1 / 2 ^ shv := by
    have e : (2 : ℝ) ^ shv * 2 ^ SOUT = 2 ^ g.SI * 2 ^ (2 * (2 * gl.SC - Tx)) * 2 ^ g.SV := by
      rw [← pow_add, hshe, pow_add, pow_add]
    have e2 : ((2 : ℝ) ^ (2 * gl.SC)) ^ 2 = 2 ^ (2 * (2 * gl.SC - Tx)) * ((2 : ℝ) ^ Tx) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
    have hX := hNq.ne'
    simp only [c, u]
    rw [div_pow, e2]
    have h1 : (0 : ℝ) < 2 ^ Tx := by positivity
    have h2 : (0 : ℝ) < 2 ^ (2 * (2 * gl.SC - Tx)) := by positivity
    have h3 : (0 : ℝ) < 2 ^ g.SV := by positivity
    have h4 : (0 : ℝ) < 2 ^ g.SI := by positivity
    have h5 : (0 : ℝ) < 2 ^ shv := by positivity
    have h6 : (0 : ℝ) < 2 ^ SOUT := by positivity
    field_simp
    linear_combination ((2 : ℝ) ^ Tx) ^ 2 * (Nq gl * vol gl) * e
  have hQS : Qc d g vb a n1 (fun j i => 2 ^ g.SI * F j i) = 2 ^ g.SI *
      ∑ i ∈ range d.qd.Gs.length, ∑ j ∈ range d.qd.Gs.length, W i * V i * W j * F j i := by
    simp only [Qc, Wq, mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [W, V, xs]; ring
  rw [hQ, hQS]
  have : c ^ 2 * u * (Nq gl * vol gl) / 2 ^ g.SI * 2 ^ SOUT = 1 / 2 ^ shv := hscale
  have h5 : (0 : ℝ) < 2 ^ shv := by positivity
  have h4 : (0 : ℝ) < 2 ^ g.SI := by positivity
  field_simp
  field_simp at this
  linear_combination (∑ i ∈ range d.qd.Gs.length, ∑ j ∈ range d.qd.Gs.length, W i * V i * W j * F j i) * this

theorem Qc_lin (d : SQ) (g : EG) (vb : V3 → ℝ) (a n1 : ℕ) (A B : ℕ → ℕ → ℝ) (p r : ℝ) :
    Qc d g vb a n1 (fun j i => p * A j i - r * B j i) =
      p * Qc d g vb a n1 A - r * Qc d g vb a n1 B := by
  unfold Qc
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- The `CH/2 - [occ] SX` combination in terms of the check's form. -/
theorem P_scaled (h : StqOK gl st t d g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA) {vb : V3 → ℝ}
    (hNq : 0 < Nq gl * vol gl) {a n1 : ℕ} (ha : a < st.ck.length) (hn1 : n1 < d.kq.cq.length)
    (A B : ℕ → ℕ → ℝ) :
    (1 / 2 * quad gl vb st t a n1 A - (if n1 < gl.nocc then quad gl vb st t a n1 B else 0)) *
        (Nq gl * vol gl) * 2 * 2 ^ SOUT =
      Qc d g vb a n1 (fun j i => 2 ^ g.SI * A j i - (if decide (n1 < gl.nocc) = true then
        2 * (2 ^ g.SI * B j i) else 0)) / 2 ^ ((d.sh.getD a []).getD n1 0) := by
  obtain ⟨-, hk⟩ := quad_scaled h hNq (vb := vb) ha hn1
  have k1 := hk A
  have k2 := hk B
  by_cases ho : n1 < gl.nocc
  · simp only [ho, if_true, decide_true]
    have := Qc_lin d g vb a n1 A B (2 ^ g.SI) (2 * 2 ^ g.SI)
    have e3 : Qc d g vb a n1 (fun j i => 2 ^ g.SI * A j i - 2 * (2 ^ g.SI * B j i)) =
        Qc d g vb a n1 (fun j i => 2 ^ g.SI * A j i) - 2 * Qc d g vb a n1 (fun j i => 2 ^ g.SI * B j i) := by
      simp only [Qc, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [e3, sub_div, ← k1, mul_div_assoc, ← k2]; ring
  · simp only [ho, if_false, decide_false, Bool.false_eq_true, sub_zero]
    rw [← k1]; ring


/-- The new claims of one (state, q-point) for a root bracket: the derivative enclosures
`DH a n1` and the point claims `PO a n1` (`nOK` at `Ec`, `Ed`: `2 P(Ec)`, `2 P(Ed)`, `4 AC`). -/
structure RQ where
  DH : List (List (ℤ × ℤ))
  PO : List (List (List ℤ))

instance : Inhabited RQ := ⟨⟨[], []⟩⟩

/-- The checks of one (state, q-point) for the bracket `[Ca, Cb]` with sign points `Cc`, `Cd`
(all energies in units `1 / Den` eV). -/
def RqOK (st : St) (d : SQ) (g : EG) (kc : KC) (nocc RN she tz : ℕ) (Ca Cb Cc Cd : ℤ) (r : RQ) : Prop :=
  (∀ a < st.ck.length, ∀ n1 < d.kq.cq.length,
    dOK kc g.Den RN she tz (decide (n1 < nocc)) Ca Cb (d.kq.Eq.getD n1 0)
      (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])) d.vbS d.cols
      ((d.sh.getD a []).getD n1 0) ((r.DH.getD a []).getD n1 (0, 0)).1 ((r.DH.getD a []).getD n1 (0, 0)).2 = true) ∧
  (∀ a < st.ck.length, ∀ n1 < d.kq.cq.length,
    nOK kc (decide (n1 < nocc)) (mkEnP RN she tz Cc (d.kq.Eq.getD n1 0)) (mkEnP RN she tz Cd (d.kq.Eq.getD n1 0))
      (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])) d.vbS d.cols
      ((d.sh.getD a []).getD n1 0) ((r.PO.getD a []).getD n1 []) = true)

theorem tPc_eq {cv occ : Bool} {S I O x : ℝ} (h : keepM I O → x ≠ wtM I O) :
    tPc cv occ S I O x = tP occ S I O x := by
  have e : ssxMc cv I O x = ssxM I O x := by
    unfold ssxMc
    by_cases hk : keepM I O
    · rw [if_neg (fun c => h hk c.2.2)]
    · rw [if_neg (fun c => hk c.2.1)]
  unfold tPc tP; rw [e]

theorem wxE_eq (h : StqOK gl st t d g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA) (n1 : ℕ) (E : ℝ) :
    wxE gl st t n1 E = (let w := E - RYD * dy gl.SEn (d.kq.Eq.getD n1 0); if |w| < TZ then TZ else w) := by
  unfold wxE eKQ; rw [h.hkq]

theorem dwx_eq (h : StqOK gl st t d g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA) (n1 : ℕ) (E : ℝ) :
    dwx gl st t n1 E = if |E - RYD * dy gl.SEn (d.kq.Eq.getD n1 0)| < TZ then 0 else 1 := by
  unfold dwx eKQ; rw [h.hkq]

set_option maxHeartbeats 1000000 in
/-- **One (state, q-point) on a root bracket.** -/
theorem rq_n (h : StqOK gl st t d g kc SQq SOUT RN she tz Wv bv vbT oqT HA cfA)
    {Ep : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ} (hE : EHyp Ep d.qd.iq d.SO d.Elo d.Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hNq : 0 < Nq gl * vol gl) {Ca Cb Cc Cd : ℤ} {r : RQ}
    (hr : RqOK st d g kc gl.nocc RN she tz Ca Cb Cc Cd r) (hac : Ca ≤ Cc) (hcd : Cc ≤ Cd) (hdb : Cd ≤ Cb) :
    ∀ a < st.ck.length, ∀ n1 < nbq st t,
      (∀ cv, FixedOn (PqE gl Ep vb oq st cv t a n1) (dPqE gl Ep vb oq st t a n1)
        ((Ca : ℝ) / g.Den) ((Cb : ℝ) / g.Den)) ∧
      (∀ E ∈ Icc ((Ca : ℝ) / g.Den) ((Cb : ℝ) / g.Den),
        (((r.DH.getD a []).getD n1 (0, 0)).1 : ℝ) ≤ dPqE gl Ep vb oq st t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
        dPqE gl Ep vb oq st t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤ ((r.DH.getD a []).getD n1 (0, 0)).2) ∧
      (∀ cv, ((((r.PO.getD a []).getD n1 []).getD 0 0 : ℝ) ≤
          PqE gl Ep vb oq st cv t a n1 ((Cc : ℝ) / g.Den) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
        PqE gl Ep vb oq st cv t a n1 ((Cc : ℝ) / g.Den) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤
          (((r.PO.getD a []).getD n1 []).getD 1 0 : ℝ)) ∧
        ((((r.PO.getD a []).getD n1 []).getD 2 0 : ℝ) ≤
          PqE gl Ep vb oq st cv t a n1 ((Cd : ℝ) / g.Den) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
        PqE gl Ep vb oq st cv t a n1 ((Cd : ℝ) / g.Den) * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤
          (((r.PO.getD a []).getD n1 []).getD 3 0 : ℝ))) ∧
      ((((r.PO.getD a []).getD n1 []).getD 4 0 : ℝ) ≤ ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
        ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤ (((r.PO.getD a []).getD n1 []).getD 5 0 : ℝ)) ∧
      (∀ E ∈ Icc ((Ca : ℝ) / g.Den) ((Cb : ℝ) / g.Den), ∀ i < (gl.qs.getD t default).Gs.length,
        ∀ j < (gl.qs.getD t default).Gs.length, keepM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) →
          wxE gl st t n1 E ≠ wtM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) ∧
          (n1 < gl.nocc → wxE gl st t n1 E ≠ -wtM (Iq gl Ep vb oq t j i) (Oq gl vb t j i))) := by
  intro a ha n1 hn1
  have hn1' : n1 < d.kq.cq.length := by unfold nbq at hn1; rw [h.hkq] at hn1; exact hn1
  obtain ⟨hxl, -⟩ := quad_scaled h hNq (vb := vb) ha hn1'
  obtain ⟨-, hvS⟩ := stq_vbS h hvb
  have hent := stq_ent h hE hvb hoq
  have hD : (0 : ℝ) < g.Den := by exact_mod_cast h.hDen0
  set Den : ℝ := (g.Den : ℝ)
  set e := RYD * dy gl.SEn (d.kq.Eq.getD n1 0) with he
  set Ea := (Ca : ℝ) / Den
  set Eb := (Cb : ℝ) / Den
  set Ec := (Cc : ℝ) / Den
  set Ed := (Cd : ℝ) / Den
  have hq := h.hq
  set occ := decide (n1 < gl.nocc)
  set sh := (d.sh.getD a []).getD n1 0
  set I := fun j i => IeS gl Ep vb oq d.qd j i
  set O := fun j i => Om2S gl vb d.qd j i
  set V := fun i => vb (key d.qd (gs d.qd i)) * 2 ^ g.SV
  have hV : ∀ i < (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).length,
      ((d.vbS.getD i (0, 0)).1 : ℝ) ≤ V i ∧ V i ≤ (d.vbS.getD i (0, 0)).2 :=
    fun i hi => hvS i (by rw [← hxl]; exact hi)
  have hEnt : ∀ i < (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).length,
      ∀ j < (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).length,
      EntOK (2 ^ g.SI) g.Den ((d.cols.getD i []).getD j default) (I j i) (O j i) :=
    fun i hi j hj => hent i (by rw [← hxl]; exact hi) j (by rw [← hxl]; exact hj)
  -- the interval
  have hDN : ((g.Den : ℕ) : ℝ) = Den := rfl
  have hdk := hr.1 a ha n1 hn1'
  have hxi : (mkEI RN she tz Ca Cb (d.kq.Eq.getD n1 0)).2 = true := by
    unfold dOK at hdk; simp only [Bool.and_eq_true] at hdk; exact hdk.1.1.1.1.1
  obtain ⟨hEI, hTZ⟩ := mkEI_spec Ca Cb (d.kq.Eq.getD n1 0) h.hRNe h.hD1 h.htz' hxi
  obtain ⟨-, hFix, hDb⟩ := dOK_sound (S := 2 ^ g.SI) hD h.hk2 h.hl h.htz hDN (fun _ => hEI) hdk hV hEnt
  rw [hxl] at hFix hDb
  -- wx on the bracket
  have hwx : ∀ E ∈ Icc Ea Eb, wxE gl st t n1 E = E - e := by
    intro E hE
    rw [wxE_eq h]; dsimp only
    rw [if_neg (not_lt.mpr (hTZ E hE))]
  have hdw : ∀ E ∈ Icc Ea Eb, dwx gl st t n1 E = 1 := by
    intro E hE; rw [dwx_eq h, if_neg (not_lt.mpr (hTZ E hE))]
  have hmem : ∀ E ∈ Icc Ea Eb, E - e ∈ Icc (Ea - e) (Eb - e) := fun E hE => ⟨by linarith [hE.1], by linarith [hE.2]⟩
  -- the scaled forms
  have hPs : ∀ cv (E : ℝ), PqE gl Ep vb oq st cv t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT =
      Qc d g vb a n1 (fun j i => tPc cv occ (2 ^ g.SI) (I j i) (O j i) (wxE gl st t n1 E)) / 2 ^ sh := by
    intro cv E
    unfold PqE
    have eI : ∀ j i, Iq gl Ep vb oq t j i = I j i := fun j i => by unfold Iq; rw [hq]
    have eO : ∀ j i, Oq gl vb t j i = O j i := fun j i => by unfold Oq; rw [hq]
    simp only [eI, eO]
    rw [P_scaled h hNq ha hn1']
    rfl
  have hDs : ∀ E ∈ Icc Ea Eb, dPqE gl Ep vb oq st t a n1 E * (Nq gl * vol gl) * 2 * 2 ^ SOUT =
      Qc d g vb a n1 (fun j i => tD occ (2 ^ g.SI) (I j i) (O j i) (wxE gl st t n1 E)) / 2 ^ sh := by
    intro E hE
    unfold dPqE
    rw [hdw E hE, one_mul]
    have eI : ∀ j i, Iq gl Ep vb oq t j i = I j i := fun j i => by unfold Iq; rw [hq]
    have eO : ∀ j i, Oq gl vb t j i = O j i := fun j i => by unfold Oq; rw [hq]
    simp only [eI, eO]
    rw [P_scaled h hNq ha hn1']
    rfl
  have hSh : (0 : ℝ) < 2 ^ sh := by positivity
  have hK : (0 : ℝ) < (Nq gl * vol gl) * 2 * 2 ^ SOUT := by positivity
  -- non-singularity
  have hns : ∀ E ∈ Icc Ea Eb, ∀ i < d.qd.Gs.length, ∀ j < d.qd.Gs.length, keepM (I j i) (O j i) →
      wxE gl st t n1 E ≠ wtM (I j i) (O j i) ∧ (n1 < gl.nocc → wxE gl st t n1 E ≠ -wtM (I j i) (O j i)) := by
    intro E hE i hi j hj hk
    obtain ⟨-, hs⟩ := hFix i hi j hj
    obtain ⟨h1, h2⟩ := hs hk (E - e) (hmem E hE)
    rw [hwx E hE]
    refine ⟨h1, fun ho => fun c => h2 (by simp [occ, ho]) (by linarith)⟩
  -- the point claims
  have hpk := hr.2 a ha n1 hn1'
  have hcI : Ec ∈ Icc Ea Eb := by
    have hc1 : (Ca : ℝ) ≤ Cc := by exact_mod_cast hac
    have hc2 : (Cc : ℝ) ≤ Cb := by exact_mod_cast le_trans hcd hdb
    exact ⟨div_le_div_of_nonneg_right hc1 hD.le, div_le_div_of_nonneg_right hc2 hD.le⟩
  have hdI : Ed ∈ Icc Ea Eb := by
    have hc1 : (Ca : ℝ) ≤ Cd := by exact_mod_cast le_trans hac hcd
    have hc2 : (Cd : ℝ) ≤ Cb := by exact_mod_cast hdb
    exact ⟨div_le_div_of_nonneg_right hc1 hD.le, div_le_div_of_nonneg_right hc2 hD.le⟩
  have e0 := mkEnP_spec Cc (d.kq.Eq.getD n1 0) h.hRNe h.hD1 h.htz'
  have e1 := mkEnP_spec Cd (d.kq.Eq.getD n1 0) h.hRNe h.hD1 h.htz'
  rw [← wxE_eq h] at e0 e1
  have hN := nOK_sound (S := 2 ^ g.SI) hD h.hk2 h.hl h.htz e0 e1 hpk (I := I) (O := O) (V := V) hV hEnt
  simp only at hN
  rw [hxl] at hN
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩, ⟨r0, r1⟩⟩ := hN
  have hpt : ∀ cv, ∀ E ∈ Icc Ea Eb, Qc d g vb a n1 (fun j i => tPc cv occ (2 ^ g.SI) (I j i) (O j i) (wxE gl st t n1 E)) =
      ∑ i ∈ range d.qd.Gs.length, ∑ j ∈ range d.qd.Gs.length,
        Wq d a n1 i * V i * Wq d a n1 j * tP occ (2 ^ g.SI) (I j i) (O j i) (wxE gl st t n1 E) := by
    intro cv E hE
    unfold Qc
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    dsimp only
    rw [tPc_eq (fun hk => (hns E hE i (mem_range.mp hi) j (mem_range.mp hj) hk).1)]
  refine ⟨fun cv => ?_, fun E hE => ?_, fun cv => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- continuity and derivative
    have hsum : FixedOn (fun y => Qc d g vb a n1 (fun j i => tPc cv occ (2 ^ g.SI) (I j i) (O j i) y))
        (fun y => Qc d g vb a n1 (fun j i => tD occ (2 ^ g.SI) (I j i) (O j i) y)) (Ea - e) (Eb - e) := by
      unfold Qc
      refine FixedOn.sum _ fun i hi => FixedOn.sum _ fun j hj => ?_
      exact ((hFix i (mem_range.mp hi) j (mem_range.mp hj)).1 cv).const_mul _
    have ht := (hsum.comp_sub e).mul_const (1 / (2 ^ sh * ((Nq gl * vol gl) * 2 * 2 ^ SOUT)))
    refine ht.congr (fun E hE => ?_) (fun E hE => ?_)
    · have h1 := hPs cv E
      rw [hwx E hE] at h1
      field_simp; field_simp at h1; linarith
    · have hE' := Ioo_subset_Icc_self hE
      have h1 := hDs E hE'
      rw [hwx E hE'] at h1
      field_simp; field_simp at h1; linarith
  · have h1 := hDs E hE
    rw [h1, hwx E hE, le_div_iff₀ hSh, div_le_iff₀ hSh]
    exact hDb (E - e) (hmem E hE)
  · rw [hPs cv, hpt cv Ec hcI, le_div_iff₀ hSh, div_le_iff₀ hSh]
    exact ⟨p0, p1⟩
  · rw [hPs cv, hpt cv Ed hdI, le_div_iff₀ hSh, div_le_iff₀ hSh]
    exact ⟨q0, q1⟩
  · have hA : ACq gl Ep vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT =
        Qc d g vb a n1 (fun j i => 2 ^ g.SI * IeU (I j i)) / 2 ^ sh := by
      unfold ACq
      have eI : ∀ j i, Iq gl Ep vb oq t j i = I j i := fun j i => by unfold Iq; rw [hq]
      simp only [eI]
      obtain ⟨-, hk⟩ := quad_scaled h hNq (vb := vb) ha hn1'
      have k1 := hk (fun j i => IeU (I j i))
      have k2 := hk (fun j i => -IeU (I j i))
      have : Qc d g vb a n1 (fun j i => 2 ^ g.SI * -IeU (I j i)) = -Qc d g vb a n1 (fun j i => 2 ^ g.SI * IeU (I j i)) := by
        unfold Qc; simp only [mul_neg, sum_neg_distrib]
      rw [this, neg_div] at k2
      linear_combination (-1 : ℝ) * k2
    rw [hA, le_div_iff₀ hSh, div_le_iff₀ hSh]
    exact ⟨r0, r1⟩
  · intro E hE i hi j hj hk
    rw [hq] at hi hj
    have eI : Iq gl Ep vb oq t j i = I j i := by unfold Iq; rw [hq]
    have eO : Oq gl vb t j i = O j i := by unfold Oq; rw [hq]
    rw [eI, eO] at hk ⊢
    exact hns E hE i hi j hj hk

end rq

end GW.Endpoint.Kernel.QP

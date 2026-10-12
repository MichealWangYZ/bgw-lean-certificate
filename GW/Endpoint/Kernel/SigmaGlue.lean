/-
G2 stage 3, soundness (4a/4): the smaller checks -- energies (`mkEn`), weights
(`xsOf`, `xsExact`), Coulomb alignment (`vbOK`), wing factors (`wingOK`), RHO
lookups, exchange (`exOK`) and the static remainder (`csOK`).
-/
import GW.Endpoint.Kernel.SigmaEnt

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### Energies -/

/-- `mkEn` encodes the energy `x = RYD (e_k - e_q) + iw` with the `TOL_Zero`
replacement in units `1/D1`. -/
theorem mkEn_spec {RN D1 sh tz : ℕ} {SEn : ℕ} (ek eq : ℤ) (iw : ℕ)
    (hRN : (RN : ℝ) / 10 ^ 8 = RYD) (hD1 : (D1 : ℝ) = 10 ^ 8 * 2 ^ (SEn + sh)) (htz : (tz : ℝ) = TZ * D1) :
    Enok (mkEn RN D1 sh tz ek eq iw) D1
      (let w := RYD * (dy SEn ek - dy SEn eq) + iw; if |w| < TZ then TZ else w) := by
  have hD : (0 : ℝ) < D1 := by rw [hD1]; positivity
  set x : ℤ := (RN : ℤ) * (ek - eq) * 2 ^ sh + iw * D1 with hx
  have hw : (RYD * (dy SEn ek - dy SEn eq) + iw) * D1 = x := by
    rw [hx, ← hRN]; unfold dy; push_cast
    rw [hD1, pow_add]; field_simp; ring
  have hxabs : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  unfold mkEn
  dsimp only
  rw [← hx]
  by_cases hs : x.natAbs < tz
  · have hb : Nat.blt x.natAbs tz = true := Nat.blt_eq.mpr hs
    rw [hb, cond_true]
    have hlt : |RYD * (dy SEn ek - dy SEn eq) + iw| < TZ := by
      have : |(x : ℝ)| < tz := by rw [← hxabs]; exact_mod_cast hs
      rw [← hw, abs_mul, abs_of_pos hD, htz] at this
      exact lt_of_mul_lt_mul_right this hD.le
    rw [if_pos hlt]
    exact ⟨by rw [htz]; simp, rfl, fun h => absurd h (by simp)⟩
  · have hb : Nat.blt x.natAbs tz = false := by rw [blt_d]; simpa using hs
    rw [hb, cond_false]
    have hge : ¬ |RYD * (dy SEn ek - dy SEn eq) + iw| < TZ := by
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

/-! ### Weights -/

theorem xsOf_length (T : ℕ) (l : List ℤ) : (xsOf T l).length = l.length := mapL_length _ _

theorem xsOf_wv {T : ℕ} {l : List ℤ} (hx : xsExact T l = true) (j : ℕ) (hj : j < l.length) :
    wv ((xsOf T l).getD j (false, 0)) * 2 ^ T = (l.getD j 0 : ℝ) := by
  unfold xsOf
  rw [mapL_getD _ _ _ 0 hj]
  have hm := List.all_eq_true.mp hx _ (getD_mem 0 hj)
  simp only [beq_d, decide_eq_true_eq] at hm
  set h := l.getD j 0
  have e : ((h.natAbs >>> T : ℕ) : ℝ) * 2 ^ T = h.natAbs := by
    have : ((h.natAbs >>> T) <<< T : ℕ) = h.natAbs := hm
    rw [Nat.shiftLeft_eq] at this
    exact_mod_cast this
  unfold wv
  simp only
  rcases lt_or_le h 0 with hn | hn
  · simp only [hn, decide_true, sg_true]
    rw [neg_mul, e, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hn)]; ring
  · simp only [not_lt.mpr hn, decide_false, sg_false]
    rw [e, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hn)]

/-! ### Coulomb alignment -/

/-- **`vbOK`**: every box `vs_k` is the table box of `key qd (Gl_k)`; with the table
hypothesis, `vb(key) · 2^SV ∈ vs_k`. -/
theorem vbOK_sound {W h b : ℕ} {vbT : List (V3 × ℤ × ℤ)} {qd : QD} {Gl : List V3} {vs : List (ℕ × ℕ)}
    (hk : keysOK h (vbT.map Prod.fst) = true)
    (hvlo : valsOK W b (vbT.map (fun p => p.2.1)) = true) (hvhi : valsOK W b (vbT.map (fun p => p.2.2)) = true)
    (hv : vbOK W h b (tpackS W (tslots h b (mapL (fun p => (p.1, p.2.1)) vbT)))
      (tpackS W (tslots h b (mapL (fun p => (p.1, p.2.2)) vbT))) qd Gl vs = true)
    {SV : ℕ} {vb : V3 → ℝ} (hvb : ∀ p ∈ vbT, (p.2.1 : ℝ) ≤ vb p.1 * 2 ^ SV ∧ vb p.1 * 2 ^ SV ≤ p.2.2) :
    Gl.length = vs.length ∧ ∀ k < Gl.length, ((vs.getD k (0, 0)).1 : ℝ) ≤ vb (key qd (Gl.getD k 0)) * 2 ^ SV ∧
      vb (key qd (Gl.getD k 0)) * 2 ^ SV ≤ (vs.getD k (0, 0)).2 ∧ 0 < (vs.getD k (0, 0)).1 := by
  unfold vbOK at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨hb0, hall⟩ := hv
  have hb0' : 0 < b := by simpa [blt_d] using hb0
  obtain ⟨hlen, hk'⟩ := all2_spec _ 0 (0, 0) _ _ hall
  refine ⟨hlen, fun k hkk => ?_⟩
  have := hk' k hkk
  simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq, blt_d] at this
  obtain ⟨⟨⟨hbox, hlo⟩, hhi⟩, hpos⟩ := this
  set G := Gl.getD k 0
  have mlo : mapL (fun p : V3 × ℤ × ℤ => (p.1, p.2.1)) vbT = vbT.map (fun p => (p.1, p.2.1)) := mapL_eq _ _
  have mhi : mapL (fun p : V3 × ℤ × ℤ => (p.1, p.2.2)) vbT = vbT.map (fun p => (p.1, p.2.2)) := mapL_eq _ _
  rw [mlo] at hlo; rw [mhi] at hhi
  have kl : keysOK h ((vbT.map (fun p => (p.1, p.2.1))).map Prod.fst) = true := by
    rw [List.map_map]; exact hk
  have kh : keysOK h ((vbT.map (fun p => (p.1, p.2.2))).map Prod.fst) = true := by
    rw [List.map_map]; exact hk
  have vl : valsOK W b ((vbT.map (fun p => (p.1, p.2.1))).map Prod.snd) = true := by
    rw [List.map_map]; exact hvlo
  have vh : valsOK W b ((vbT.map (fun p => (p.1, p.2.2))).map Prod.snd) = true := by
    rw [List.map_map]; exact hvhi
  obtain ⟨fl1, fl2⟩ := tget_find kl vl hbox
  obtain ⟨fh1, -⟩ := tget_find kh vh hbox
  -- a key exists (else the digit would be 0 < b + v)
  have hex : ∃ p ∈ vbT, p.1 = key qd G := by
    by_contra hne
    push_neg at hne
    have := fl2 (fun p hp => by
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
      exact hne p' hp')
    rw [hlo] at this; omega
  obtain ⟨p, hp, hpk⟩ := hex
  have e1 := fl1 (p.1, p.2.1) (List.mem_map_of_mem hp) hpk
  have e2 := fh1 (p.1, p.2.2) (List.mem_map_of_mem hp) hpk
  rw [hlo] at e1; rw [hhi] at e2
  push_cast at e1 e2
  have q1 : ((vs.getD k (0, 0)).1 : ℤ) = p.2.1 := by linarith
  have q2 : ((vs.getD k (0, 0)).2 : ℤ) = p.2.2 := by linarith
  obtain ⟨b1, b2⟩ := hvb p hp
  rw [hpk] at b1 b2
  refine ⟨?_, ?_, hpos⟩
  · have : ((vs.getD k (0, 0)).1 : ℝ) = (p.2.1 : ℝ) := by exact_mod_cast q1
    rw [this]; exact b1
  · have : ((vs.getD k (0, 0)).2 : ℝ) = (p.2.2 : ℝ) := by exact_mod_cast q2
    rw [this]; exact b2

/-! ### Wing factors -/

theorem ar_frlo {frl ol ql A B C p O Q π : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hπ : 0 < π)
    (hπp : π ≤ p) (hk : frl * A * B * 8 * p ≤ ol * ql * C) (hO : ol / A ≤ O) (hQ : ql / B ≤ Q)
    (hol : 0 ≤ ol) (hql : 0 ≤ ql) : frl ≤ O * Q / (8 * π) * C := by
  have hp : 0 < p := lt_of_lt_of_le hπ hπp
  have h1 : ol / A * (ql / B) ≤ O * Q := mul_le_mul hO hQ (by positivity) (le_trans (by positivity) hO)
  have h2 : frl ≤ (ol / A * (ql / B)) / (8 * p) * C := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : ol / A * (ql / B) * C = ol * ql * C / (A * B) := by field_simp
    rw [this, le_div_iff₀ (by positivity)]; linarith
  calc frl ≤ (ol / A * (ql / B)) / (8 * p) * C := h2
    _ ≤ (O * Q) / (8 * π) * C := by
      apply mul_le_mul_of_nonneg_right _ hC.le
      exact div_le_div₀ (le_trans (by positivity) h1) h1 (by positivity) (by linarith)

theorem ar_frhi {frh oh qu A B C p O Q π : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hπ : 0 < π)
    (hπp : p ≤ π) (hp : 0 < p) (hk : oh * qu * C ≤ frh * A * B * 8 * p) (hO : O ≤ oh / A) (hQ : Q ≤ qu / B)
    (hO0 : 0 ≤ O) (hQ0 : 0 ≤ Q) : O * Q / (8 * π) * C ≤ frh := by
  have h1 : O * Q ≤ oh / A * (qu / B) := mul_le_mul hO hQ hQ0 (le_trans hO0 hO)
  have h2 : (oh / A * (qu / B)) / (8 * p) * C ≤ frh := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : oh / A * (qu / B) * C = oh * qu * C / (A * B) := by field_simp
    rw [this, div_le_iff₀ (by positivity)]; linarith
  calc O * Q / (8 * π) * C ≤ (oh / A * (qu / B)) / (8 * p) * C := by
        apply mul_le_mul_of_nonneg_right _ hC.le
        exact div_le_div₀ (le_trans (by positivity) h1) h1 (by positivity) (by linarith)
    _ ≤ frh := h2

theorem ar_fclo {fcl ol vh qu A B C O V Q : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hk : fcl * vh * qu ≤ ol * B * C) (hO : ol / A ≤ O) (hV : V ≤ vh / A) (hQ : Q ≤ qu / B)
    (hV0 : 0 < V) (hQ0 : 0 < Q) (hol : 0 ≤ ol) : fcl ≤ O / (V * Q) * C := by
  have hvh : 0 < vh / A := lt_of_lt_of_le hV0 hV
  have hqu : 0 < qu / B := lt_of_lt_of_le hQ0 hQ
  have h1 : V * Q ≤ vh / A * (qu / B) := mul_le_mul hV hQ hQ0.le hvh.le
  have h2 : fcl ≤ (ol / A) / (vh / A * (qu / B)) * C := by
    have hvh' : 0 < vh := by have := hvh; rwa [div_pos_iff_of_pos_right hA] at this
    have hqu' : 0 < qu := by have := hqu; rwa [div_pos_iff_of_pos_right hB] at this
    have : (ol / A) / (vh / A * (qu / B)) * C = ol * B * C / (vh * qu) := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith
  calc fcl ≤ (ol / A) / (vh / A * (qu / B)) * C := h2
    _ ≤ O / (V * Q) * C := by
      apply mul_le_mul_of_nonneg_right _ hC.le
      exact div_le_div₀ (le_trans (by positivity) hO) hO (by positivity) h1

theorem ar_fchi {fch oh vl ql A B C O V Q : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hk : oh * B * C ≤ fch * vl * ql) (hO : O ≤ oh / A) (hV : vl / A ≤ V) (hQ : ql / B ≤ Q)
    (hvl : 0 < vl) (hql : 0 < ql) (hO0 : 0 ≤ O) : O / (V * Q) * C ≤ fch := by
  have h1 : vl / A * (ql / B) ≤ V * Q := mul_le_mul hV hQ (by positivity) (le_trans (by positivity) hV)
  have h2 : (oh / A) / (vl / A * (ql / B)) * C ≤ fch := by
    have : (oh / A) / (vl / A * (ql / B)) * C = oh * B * C / (vl * ql) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]; linarith
  calc O / (V * Q) * C ≤ (oh / A) / (vl / A * (ql / B)) * C := by
        apply mul_le_mul_of_nonneg_right _ hC.le
        exact div_le_div₀ (le_trans hO0 hO) hO (by positivity) h1
    _ ≤ fch := h2


theorem qlen_eq (gl : Gl) (qd : QD) : qlen gl qd = √((dotN gl.B qd.qh 0 0 : ℝ) / (4 * 2 ^ gl.SB)) := by
  unfold qlen; rw [dotB_eq]

/-- **`wingOK`** gives the certified wing factors `WingOK` (for `oneoverq` and the Coulomb
average of `Gs₀` in their boxes). -/
theorem wingOK_sound {g : EG} {SQ : ℕ} {w : Wing} {qd : QD} {oqT : List (V3 × ℤ × ℤ)}
    {ol oh : ℕ} {vbS : List (ℕ × ℕ)} (hw : wingOK g SQ w qd oqT ol oh vbS = true)
    {gl : Gl} (hSB : gl.SB = g.SB) (hB : gl.B = g.B) {vb oq : V3 → ℝ}
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hv0 : ((vbS.getD 0 (0, 0)).1 : ℝ) ≤ vb (key qd (gs qd 0)) * 2 ^ g.SV ∧
      vb (key qd (gs qd 0)) * 2 ^ g.SV ≤ (vbS.getD 0 (0, 0)).2) :
    WingOK gl vb oq g.SF w qd := by
  intro _
  unfold wingOK at hw
  dsimp only at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, blt_d, ble_d] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hel, hql⟩, hvl⟩, hol⟩, hq1⟩, hq2⟩, hf1⟩, hf2⟩, hf3⟩, hf4⟩ := hw
  have hmem : (qd.qh, (ol : ℤ), (oh : ℤ)) ∈ oqT := by simpa using hel
  obtain ⟨o1, o2⟩ := hoq _ hmem
  simp only at o1 o2
  set vl := (vbS.getD 0 (0, 0)).1
  set vh := (vbS.getD 0 (0, 0)).2
  set O := oq qd.qh
  set Vb := vb (key qd (gs qd 0))
  set q2 := (dotN g.B qd.qh 0 0 : ℤ)
  have hSV : (0 : ℝ) < 2 ^ g.SV := by positivity
  have hSQ : (0 : ℝ) < 2 ^ SQ := by positivity
  have hSF : (0 : ℝ) < 2 ^ g.SF := by positivity
  have hS4 : (0 : ℝ) < 4 * 2 ^ g.SB := by positivity
  have hpi := Real.pi_gt_d20
  have hpi' := Real.pi_lt_d20
  have hpi0 : 0 < Real.pi := Real.pi_pos
  -- |q| bounds
  set Q := qlen gl qd with hQ
  rw [qlen_eq, hB, hSB] at hQ
  have hql' : (0 : ℝ) < w.ql := by exact_mod_cast hql
  have hq1' : ((w.ql : ℤ) : ℝ) ^ 2 * (4 * 2 ^ g.SB) ≤ (q2 : ℝ) * 2 ^ (2 * SQ) := by exact_mod_cast hq1
  have hq2' : (q2 : ℝ) * 2 ^ (2 * SQ) ≤ ((w.qu : ℤ) : ℝ) ^ 2 * (4 * 2 ^ g.SB) := by exact_mod_cast hq2
  push_cast at hq1' hq2'
  have hpow : (2 : ℝ) ^ (2 * SQ) = (2 ^ SQ) ^ 2 := by rw [pow_mul']
  rw [hpow] at hq1' hq2'
  have hQlo : (w.ql : ℝ) / 2 ^ SQ ≤ Q := by
    rw [hQ]; apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_div_iff₀ (by positivity) hS4]; nlinarith
  have hQhi : Q ≤ (w.qu : ℝ) / 2 ^ SQ := by
    rw [hQ]
    have h0 : (0 : ℝ) ≤ (w.qu : ℝ) / 2 ^ SQ := by positivity
    have : (q2 : ℝ) / (4 * 2 ^ g.SB) ≤ ((w.qu : ℝ) / 2 ^ SQ) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ hS4 (by positivity)]; nlinarith
    calc √((q2 : ℝ) / (4 * 2 ^ g.SB)) ≤ √(((w.qu : ℝ) / 2 ^ SQ) ^ 2) := Real.sqrt_le_sqrt this
      _ = (w.qu : ℝ) / 2 ^ SQ := Real.sqrt_sq h0
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQlo
  have hol' : (0 : ℝ) < ol := by exact_mod_cast hol
  have hvl' : (0 : ℝ) < vl := by exact_mod_cast hvl
  have hO0 : 0 < O := by
    have : (0 : ℝ) < O * 2 ^ g.SV := lt_of_lt_of_le hol' o1
    exact pos_of_mul_pos_left this hSV.le
  have hV0 : 0 < Vb := by
    have : (0 : ℝ) < Vb * 2 ^ g.SV := lt_of_lt_of_le hvl' hv0.1
    exact pos_of_mul_pos_left this hSV.le
  have hf1' : (w.frl : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * piHi ≤ ol * w.ql * 2 ^ g.SF * 10 ^ 20 := by exact_mod_cast hf1
  have hf2' : (oh : ℝ) * w.qu * 2 ^ g.SF * 10 ^ 20 ≤ w.frh * 2 ^ g.SV * 2 ^ SQ * 8 * piLo := by exact_mod_cast hf2
  have hf3' : (w.fcl : ℝ) * vh * w.qu ≤ ol * 2 ^ SQ * 2 ^ g.SF := by exact_mod_cast hf3
  have hf4' : (oh : ℝ) * 2 ^ SQ * 2 ^ g.SF ≤ w.fch * vl * w.ql := by exact_mod_cast hf4
  unfold piHi at hf1'; unfold piLo at hf2'
  push_cast at hf1' hf2'
  have hOl : (ol : ℝ) / 2 ^ g.SV ≤ O := by rw [div_le_iff₀ hSV]; exact o1
  have hOh : O ≤ (oh : ℝ) / 2 ^ g.SV := by rw [le_div_iff₀ hSV]; exact o2
  have hVl : (vl : ℝ) / 2 ^ g.SV ≤ Vb := by rw [div_le_iff₀ hSV]; exact hv0.1
  have hVh : Vb ≤ (vh : ℝ) / 2 ^ g.SV := by rw [le_div_iff₀ hSV]; exact hv0.2
  have e10 : (0 : ℝ) < 10 ^ 20 := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ar_frlo hSV hSQ hSF hpi0 hpi'.le ?_ hOl hQlo (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have : (w.frl : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * (314159265358979323847 / 10 ^ 20) * 10 ^ 20 ≤
        ol * w.ql * 2 ^ g.SF * 10 ^ 20 := by
      rw [show (w.frl : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * (314159265358979323847 / 10 ^ 20) * 10 ^ 20 =
        (w.frl : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * 314159265358979323847 by field_simp]
      exact hf1'
    have hd : (3.14159265358979323847 : ℝ) = 314159265358979323847 / 10 ^ 20 := by norm_num
    rw [hd]; exact le_of_mul_le_mul_right this e10
  · refine ar_frhi hSV hSQ hSF hpi0 hpi.le (by positivity) ?_ hOh hQhi hO0.le hQ0.le
    have : (oh : ℝ) * w.qu * 2 ^ g.SF * 10 ^ 20 ≤
        w.frh * 2 ^ g.SV * 2 ^ SQ * 8 * (314159265358979323846 / 10 ^ 20) * 10 ^ 20 := by
      rw [show (w.frh : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * (314159265358979323846 / 10 ^ 20) * 10 ^ 20 =
        (w.frh : ℝ) * 2 ^ g.SV * 2 ^ SQ * 8 * 314159265358979323846 by field_simp]
      exact hf2'
    have hd : (3.14159265358979323846 : ℝ) = 314159265358979323846 / 10 ^ 20 := by norm_num
    rw [hd]; exact le_of_mul_le_mul_right this e10
  · exact ar_fclo hSV hSQ hSF hf3' hOl hVh hQhi hV0 hQ0 (Nat.cast_nonneg _)
  · exact ar_fchi hSV hSQ hSF hf4' hOh hVl hQlo hvl' hql' hO0.le

/-! ### RHO lookups -/

theorem find_some {l : List (V3 × ℤ)} {d : V3} {p : V3 × ℤ} (h : l.find? (fun p => p.1 == d) = some p) :
    p ∈ l ∧ p.1 = d := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem find_none {l : List (V3 × ℤ)} {d : V3} (h : l.find? (fun p => p.1 == d) = none) :
    ∀ p ∈ l, p.1 ≠ d := fun p hp he => by
  have := List.find?_eq_none.mp h p hp
  simp [he] at this

/-- RHO through its table: the digit at `d` is `0` exactly when `d` is not in RHO, else
`b + rho(d)`. -/
theorem rho_dig {W b : ℕ} {gl : Gl} (hk : keysOK 7 (gl.rho.map Prod.fst) = true)
    (hv : valsOK W b (gl.rho.map Prod.snd) = true) {d : V3} (hd : inBox (-(7 : ℕ) : ℤ) (7 : ℕ) d = true) :
    RhoDig gl b d (tget W 7 (tpackS W (tslots 7 b gl.rho)) d) := by
  obtain ⟨f1, f2⟩ := tget_find hk hv hd
  unfold RhoDig rhoF
  cases hf : gl.rho.find? (fun p => p.1 == d) with
  | none => left; exact ⟨rfl, f2 (find_none hf)⟩
  | some p =>
    right
    obtain ⟨hp, hpd⟩ := find_some hf
    refine ⟨p.2, rfl, f1 p hp hpd, fun h0 => ?_⟩
    have e := f1 p hp hpd
    rw [h0] at e
    unfold valsOK at hv
    have hb := List.all_eq_true.mp hv p.2 (List.mem_map_of_mem hp)
    simp only [Bool.and_eq_true, blt_d, decide_eq_true_eq] at hb
    have := ipos_sub_ineg p.2
    push_cast at e
    omega

/-- The G-vectors of a sphere in `[-3, 3]³` have differences in the table box. -/
theorem diff_box {g g' : V3} (hg : inBox (-3) 3 g = true) (hg' : inBox (-3) 3 g' = true) :
    inBox (-(7 : ℕ) : ℤ) (7 : ℕ) (g - g') = true := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
  obtain ⟨a1', a2', b1', b2', c1', c2'⟩ := inBox_spec hg'
  simp only [inBox, Prod.fst_sub, Prod.snd_sub, Bool.and_eq_true, decide_eq_true_eq]
  push_cast
  omega

/-- `nelec ≠ 0` from the RHO digit at `G = 0`. -/
theorem nelec_ne {gl : Gl} {b tg : ℕ} (hr : RhoDig gl b 0 tg) (h0 : tg ≠ 0) (hb : tg ≠ b) :
    nelec gl ≠ 0 := by
  unfold nelec
  rcases hr with ⟨-, ht⟩ | ⟨rN, hs, ht, -⟩
  · exact absurd ht h0
  · rw [hs]; simp only [Option.getD_some]
    unfold dy
    have : rN ≠ 0 := by
      intro hz; rw [hz] at ht; apply hb; exact_mod_cast (by simpa using ht)
    exact div_ne_zero (by exact_mod_cast this) (by positivity)

/-! ### Exchange -/

theorem sumL_real (l : List ℕ) : ((sumL l 0 : ℕ) : ℝ) = ∑ j ∈ range l.length, (l.getD j 0 : ℝ) := by
  rw [sumL_nat_eq]; push_cast; rfl

/-- **`exOK`**: `lo 2^sh ≤ -Σ_r Σ_g H_rg² V_g ≤ hi 2^sh` for `V_g ∈ vbB_g`. -/
theorem exOK_sound {Hb : List (List ℤ)} {vbB : List (ℕ × ℕ)} {sh : ℕ} {lo hi : ℤ}
    (h : exOK Hb vbB sh lo hi = true) {V : ℕ → ℝ}
    (hV : ∀ g < vbB.length, ((vbB.getD g (0, 0)).1 : ℝ) ≤ V g ∧ V g ≤ (vbB.getD g (0, 0)).2) :
    (lo : ℝ) * 2 ^ sh ≤ -∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length, (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * V g ∧
      -∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length, (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * V g ≤ (hi : ℝ) * 2 ^ sh := by
  unfold exOK at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, h1⟩, h2⟩ := h
  have hrow : ∀ r < Hb.length, (Hb.getD r []).length = vbB.length := fun r hr => by
    have := List.all_eq_true.mp hlen _ (getD_mem [] hr); simpa [beq_d] using this
  -- the row sums
  have hS : ∀ (sel : ℕ × ℕ → ℕ), ((sumL (mapL (fun row => sumL (zipW (fun (hh : ℤ) (v : ℕ × ℕ) =>
      hh.natAbs * hh.natAbs * sel v) row vbB) 0) Hb) 0 : ℕ) : ℝ) =
      ∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length,
        (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * (sel (vbB.getD g (0, 0)) : ℝ) := by
    intro sel
    rw [sumL_real, mapL_length]
    refine sum_congr rfl fun r hr => ?_
    rw [mapL_getD _ _ _ [] (mem_range.mp hr), sumL_real, zipW_length, hrow r (mem_range.mp hr), min_self]
    refine sum_congr rfl fun g hg => ?_
    rw [zipW_getD _ 0 0 (0, 0) _ _ g (by rw [hrow r (mem_range.mp hr)]; exact mem_range.mp hg) (mem_range.mp hg)]
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs, ← sq, sq_abs]
  have hA1 := hS Prod.fst
  have hA2 := hS Prod.snd
  have h1' : (lo : ℝ) * 2 ^ sh ≤ -(((sumL (mapL (fun row => sumL (zipW (fun (hh : ℤ) (v : ℕ × ℕ) =>
      hh.natAbs * hh.natAbs * v.2) row vbB) 0) Hb) 0 : ℕ) : ℝ)) := by exact_mod_cast h1
  have h2' : -(((sumL (mapL (fun row => sumL (zipW (fun (hh : ℤ) (v : ℕ × ℕ) =>
      hh.natAbs * hh.natAbs * v.1) row vbB) 0) Hb) 0 : ℕ) : ℝ)) ≤ (hi : ℝ) * 2 ^ sh := by exact_mod_cast h2
  rw [hA2] at h1'
  rw [hA1] at h2'
  have b1 : ∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length, (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * V g ≤
      ∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length,
        (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * ((vbB.getD g (0, 0)).2 : ℝ) :=
    sum_le_sum fun r _ => sum_le_sum fun g hg =>
      mul_le_mul_of_nonneg_left (hV g (mem_range.mp hg)).2 (sq_nonneg _)
  have b2 : ∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length,
        (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * ((vbB.getD g (0, 0)).1 : ℝ) ≤
      ∑ r ∈ range Hb.length, ∑ g ∈ range vbB.length, (((Hb.getD r []).getD g 0 : ℤ) : ℝ) ^ 2 * V g :=
    sum_le_sum fun r _ => sum_le_sum fun g hg =>
      mul_le_mul_of_nonneg_left (hV g (mem_range.mp hg)).1 (sq_nonneg _)
  exact ⟨by linarith, by linarith⟩

/-! ### The static remainder -/

theorem sumCS_all_ok : ∀ (l : List CS) (s : CS), (∀ c ∈ l, c.ok = true) → s.ok = true → (sumCS l s).ok = true
  | [], _, _, hs => hs
  | c :: l, s, h, hs => sumCS_all_ok l (addCS s c) (fun c' hc' => h c' (by simp [hc']))
      (by simp [addCS, hs, h c (by simp)])

theorem zipW_mem {α β γ : Type} {g : α → β → γ} {P : γ → Prop} (hP : ∀ a b, P (g a b)) :
    ∀ (l1 : List α) (l2 : List β), ∀ c ∈ zipW g l1 l2, P c
  | [], _, c, hc => by simp at hc
  | _ :: _, [], c, hc => by simp at hc
  | a :: as, b :: bs, c, hc => by
      simp only [zipW_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hP a b
      · exact zipW_mem hP as bs c hc

/-- The value of key `d` in a table (`0` if absent). -/
noncomputable def tv (tab : List (V3 × ℤ)) (d : V3) : ℝ :=
  ((tab.find? (fun p => p.1 == d)).map (fun p => (p.2 : ℝ))).getD 0

theorem csTerm_spec {W b : ℕ} {tab : List (V3 × ℤ)} (hk : keysOK 7 (tab.map Prod.fst) = true)
    (hv : valsOK W b (tab.map Prod.snd) = true) {qd : QD} {j i : ℕ} {r : Ent}
    (hd : inBox (-(7 : ℕ) : ℤ) (7 : ℕ) (gs qd i - gs qd j) = true) {S Den I O : ℝ}
    (hr : EntOK S Den r I O) :
    AccS (csTerm W 7 b (tpackS W (tslots 7 b tab)) qd j i r)
      (if TS ≤ |I| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then tv tab (gs qd i - gs qd j) * (-(S * I)) else 0) := by
  obtain ⟨f1, f2⟩ := tget_find hk hv hd
  set d := gs qd i - gs qd j
  set tg := tget W 7 (tpackS W (tslots 7 b tab)) d with htg
  unfold csTerm
  dsimp only
  rw [← htg]
  by_cases hc1 : 1 ≤ r.cls
  · have hTI := hr.t1 hc1
    obtain ⟨-, hI1, hI2⟩ := hr.c1 hc1
    by_cases hmem : d ∈ tab.map Prod.fst
    · obtain ⟨p, hp, hpd⟩ := List.mem_map.mp hmem
      have e := f1 p hp hpd
      have hb := List.all_eq_true.mp hv p.2 (List.mem_map_of_mem hp)
      simp only [Bool.and_eq_true, blt_d, decide_eq_true_eq] at hb
      have hpos := ipos_sub_ineg p.2
      have htg0 : tg ≠ 0 := by intro h0; rw [h0] at e; push_cast at e; omega
      have hb1 : (Nat.ble 1 r.cls && !(Nat.beq tg 0)) = true := by
        simp [ble_d, beq_d, hc1, htg0]
      rw [hb1, cond_true, if_pos ⟨hTI, hmem⟩]
      -- the table value
      cases hf : tab.find? (fun p => p.1 == d) with
      | none => exact absurd (find_none hf p hp) (by simpa using hpd)
      | some p' =>
        obtain ⟨hp', hpd'⟩ := find_some hf
        have e' := f1 p' hp' hpd'
        have hA : ((tg : ℤ) - b) = p'.2 := by linarith
        unfold tv; rw [hf]; simp only [Option.map_some', Option.getD_some]
        rw [hA]
        have := ivA_spec (s := decide (0 < p'.2)) (c := p'.2.natAbs) hI1 hI2
        convert this using 1
        rcases lt_or_le 0 p'.2 with hl | hl
        · simp only [hl, decide_true, sg_true]; rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hl)]; ring
        · simp only [not_lt.mpr hl, decide_false, sg_false]
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonpos (by exact_mod_cast hl)]; ring
    · have htg0 : tg = 0 := f2 (fun p hp hpd => hmem (List.mem_map.mpr ⟨p, hp, hpd⟩))
      have hb1 : (Nat.ble 1 r.cls && !(Nat.beq tg 0)) = false := by simp [beq_d, htg0]
      rw [hb1, cond_false, if_neg (fun h => hmem h.2)]; exact AccS_zero
  · have hc0 : r.cls = 0 := by omega
    have hb1 : (Nat.ble 1 r.cls && !(Nat.beq tg 0)) = false := by simp [ble_d, hc0]
    rw [hb1, cond_false, if_neg (fun h => absurd h.1 (not_le.mpr (hr.t0 hc0)))]; exact AccS_zero

/-- **`csOK`**: the static term's box. -/
theorem csOK_sound {W b : ℕ} {tab : List (V3 × ℤ)} {qd : QD} {vbS : List (ℕ × ℕ)}
    {cols : List (List Ent)} {sh : ℕ} {lo hi : ℤ} (hc : csOK W 7 b tab qd vbS cols sh lo hi = true)
    (hk : keysOK 7 (tab.map Prod.fst) = true) (hgs : qd.Gs.all (inBox (-3) 3) = true)
    {S Den : ℝ} {I O : ℕ → ℕ → ℝ}
    (hE : ∀ j < qd.Gs.length, ∀ i < qd.Gs.length, EntOK S Den ((cols.getD j []).getD i default) (I i j) (O i j))
    {V : ℕ → ℝ} (hV : ∀ j < qd.Gs.length, ((vbS.getD j (0, 0)).1 : ℝ) ≤ V j ∧ V j ≤ (vbS.getD j (0, 0)).2) :
    (lo : ℝ) * 2 ^ sh ≤ ∑ j ∈ range qd.Gs.length, V j * ∑ i ∈ range qd.Gs.length,
        (if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0) ∧
      ∑ j ∈ range qd.Gs.length, V j * ∑ i ∈ range qd.Gs.length,
        (if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0)
        ≤ (hi : ℝ) * 2 ^ sh := by
  unfold csOK at hc
  dsimp only at hc
  simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hvals, hl1⟩, hl2⟩, hl3⟩, hin⟩ := hc
  have hvals' : valsOK W b (tab.map Prod.snd) = true := by rwa [mapL_eq] at hvals
  set n := qd.Gs.length
  have hcl : ∀ j < n, (cols.getD j []).length = n := fun j hj => by
    have := List.all_eq_true.mp hl3 _ (getD_mem (l := cols) (i := j) [] (by omega)); simpa [beq_d] using this
  have hbox : ∀ k < n, inBox (-3) 3 (gs qd k) = true := fun k hk =>
    List.all_eq_true.mp hgs _ (getD_mem 0 hk)
  -- one column
  have hcol : ∀ j < n, AccS (sumCS (zipW (fun i r => (⟨true, acc0, acc0,
        csTerm W 7 b (tpackS W (tslots 7 b tab)) qd j i r⟩ : CS)) (List.range (cols.getD j []).length)
        (cols.getD j [])) cs0).ac
      (∑ i ∈ range n, (if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then
        tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0)) := by
    intro j hj
    have hlen : (zipW (fun i r => (⟨true, acc0, acc0, csTerm W 7 b (tpackS W (tslots 7 b tab)) qd j i r⟩ : CS))
        (List.range (cols.getD j []).length) (cols.getD j [])).length = n := by
      rw [zipW_length, List.length_range, min_self, hcl j hj]
    have := sumCS_spec _ (fun _ => 0) (fun _ => 0)
      (fun i => if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then
        tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0)
      (fun i hi => by
        rw [hlen] at hi
        rw [zipW_getD _ cs0 0 default _ _ i (by rw [List.length_range, hcl j hj]; exact hi) (by rw [hcl j hj]; exact hi),
          getD_range (by rw [hcl j hj]; exact hi)]
        intro _
        exact ⟨AccS_zero, AccS_zero, csTerm_spec hk hvals' (diff_box (hbox i hi) (hbox j hj)) (hE j hj i hi)⟩)
      cs0 0 0 0 CSS_zero
    rw [hlen] at this
    have hok : (sumCS (zipW (fun i r => (⟨true, acc0, acc0, csTerm W 7 b (tpackS W (tslots 7 b tab)) qd j i r⟩ : CS))
        (List.range (cols.getD j []).length) (cols.getD j [])) cs0).ok = true :=
      sumCS_all_ok _ _ (zipW_mem (P := fun c : CS => c.ok = true) (fun _ _ => rfl) _ _) rfl
    simpa using (this hok).2.2
  -- all columns
  have hzl1 : (zipW Prod.mk (List.range cols.length) vbS).length = n := by
    rw [zipW_length, List.length_range, hl1, hl2, min_self]
  have hzl : (zipW (fun (jv : ℕ × (ℕ × ℕ)) rs => colFin (false, 1) jv.2 ⟨true, acc0, acc0,
      (sumCS (zipW (fun i r => (⟨true, acc0, acc0, csTerm W 7 b (tpackS W (tslots 7 b tab)) qd jv.1 i r⟩ : CS))
        (List.range rs.length) rs) cs0).ac⟩) (zipW Prod.mk (List.range cols.length) vbS) cols).length = n := by
    rw [zipW_length, hzl1, hl1, min_self]
  have hsum := sumCS_spec _ (fun _ => 0) (fun _ => 0)
    (fun j => V j * ∑ i ∈ range n, (if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then
        tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0))
    (fun j hj => by
      rw [hzl] at hj
      rw [zipW_getD _ cs0 (0, (0, 0)) [] _ _ j (by rw [hzl1]; exact hj) (by omega),
        zipW_getD _ (0, (0, 0)) 0 (0, 0) _ _ j (by rw [List.length_range]; omega) (by omega),
        getD_range (by omega)]
      have h1 : CSS (⟨true, acc0, acc0, (sumCS (zipW (fun i r => (⟨true, acc0, acc0,
          csTerm W 7 b (tpackS W (tslots 7 b tab)) qd j i r⟩ : CS)) (List.range (cols.getD j []).length)
          (cols.getD j [])) cs0).ac⟩ : CS) 0 0
          (∑ i ∈ range n, (if TS ≤ |I i j| ∧ gs qd i - gs qd j ∈ tab.map Prod.fst then
            tv tab (gs qd i - gs qd j) * (-(S * I i j)) else 0)) :=
        fun _ => ⟨AccS_zero, AccS_zero, hcol j hj⟩
      have := colFin_spec (x := (false, 1)) h1 (hV j hj).1 (hV j hj).2
      simpa [wv] using this) cs0 0 0 0 CSS_zero
  rw [hzl] at hsum
  have hok : (sumCS (zipW (fun (jv : ℕ × (ℕ × ℕ)) rs => colFin (false, 1) jv.2 ⟨true, acc0, acc0,
      (sumCS (zipW (fun i r => (⟨true, acc0, acc0, csTerm W 7 b (tpackS W (tslots 7 b tab)) qd jv.1 i r⟩ : CS))
        (List.range rs.length) rs) cs0).ac⟩) (zipW Prod.mk (List.range cols.length) vbS) cols) cs0).ok = true :=
    sumCS_all_ok _ _ (zipW_mem (P := fun c : CS => c.ok = true) (fun _ _ => rfl) _ _) rfl
  have := accIn_spec (hsum hok).2.2 hin
  simpa using this

end GW.Endpoint.Kernel.Sig

/-
G2 stage 3, soundness (4b/4): one (state, q-point). From the kernel-checked facts
of the data modules (entries, pair densities, Coulomb alignment, wings, hot path,
exchange, static remainder) the per-band parts `Xq`, `CSq`, `ACq`, `Pq` of spec A lie
in the claimed enclosures (`stq_x`, `stq_cs`, `stq_n`; the entries `stq_ent`).
-/
import GW.Endpoint.Kernel.SigmaGlue

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### Pair densities -/

theorem pd_Mint (gl : Gl) (kp : KPair) (v c : ℕ) (G : V3) :
    pd gl kp.Gv (kp.cv.getD v []) kp.Gc (kp.cc.getD c []) G = (Mint kp v c G : ℝ) / 2 ^ (2 * gl.SC) := by
  simp only [pd, Mint, dy]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [two_mul, pow_add]; field_simp
  · simp

/-- The quadratic form of the spec in terms of the check's `Q`. -/
theorem quad_eq (gl : Gl) (vb : V3 → ℝ) (st : St) (t a n1 : ℕ) (F : ℕ → ℕ → ℝ) (W V : ℕ → ℝ) (c u : ℝ)
    (hx : ∀ k < (gl.qs.getD t default).Gs.length, xS gl st t a n1 (gs (gl.qs.getD t default) k) = W k * c)
    (hv : ∀ k < (gl.qs.getD t default).Gs.length, vS gl vb (gl.qs.getD t default) k = V k * u) :
    quad gl vb st t a n1 F = c ^ 2 * u * ∑ i ∈ range (gl.qs.getD t default).Gs.length,
      ∑ j ∈ range (gl.qs.getD t default).Gs.length, W i * V i * W j * F j i := by
  unfold quad
  dsimp only
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [hx i (mem_range.mp hi), hv i (mem_range.mp hi), hx j (mem_range.mp hj)]
  ring

/-! ### One (state, q-point) -/

/-- The data of one (state, q-point) instance of the checks. -/
structure SQ where
  qd : QD
  kq : KQ
  cols : List (List Ent)
  vbS : List (ℕ × ℕ)
  vbB : List (ℕ × ℕ)
  w : Wing
  SO : ℕ
  Elo : List (List ℤ)
  Ehi : List (List ℤ)
  H : List (List (List ℤ))
  Hb : List (List (List ℤ))
  cf : Cfg
  cfb : Cfg
  Tx : List (List ℕ)
  sh : List (List ℕ)
  O : List (List (List ℤ))
  XO : List (ℤ × ℤ)
  CO : List (ℤ × ℤ)
  WA : List ℕ
  bA : List ℕ
  shx : ℕ
  shc : ℕ

/-- Everything the data modules certify about one (state, q-point). -/
structure StqOK (gl : Gl) (st : St) (t : ℕ) (d : SQ) (g : EG) (kc : KC) (SQ SOUT RN she tz Wv bv : ℕ)
    (vbT oqT : List (V3 × ℤ × ℤ)) (HA : List (List (List ℤ))) (cfA : Cfg) : Prop where
  hq : gl.qs.getD t default = d.qd
  hkq : st.kq.getD t default = d.kq
  hSB : gl.SB = g.SB
  hB : gl.B = g.B
  hSR : gl.SR = g.SR
  hSOm : gl.SOm = g.SOm
  hOm : gl.Om = g.OmN
  hOm0 : 0 < g.OmN
  hRN : g.RN = 1360569253
  hts : TS = (g.tsn : ℝ) / 2 ^ g.tse
  htsn : 0 < g.tsn
  hwinv : g.winv = 10 ^ 12
  hDen0 : 0 < g.Den
  hh : g.h = 7
  hk2 : (kc.Den2 : ℝ) = (g.Den : ℝ) ^ 2
  hl : kc.lim1 = 250000
  htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze
  hRNe : (RN : ℝ) / 10 ^ 8 = RYD
  hD1 : (g.Den : ℝ) = 10 ^ 8 * 2 ^ (gl.SEn + she)
  htz' : (tz : ℝ) = TZ * g.Den
  hrk : keysOK 7 (gl.rho.map Prod.fst) = true
  hrv : valsOK g.W g.bias (gl.rho.map Prod.snd) = true
  hnel : nelec gl ≠ 0
  hvk : keysOK 7 (vbT.map Prod.fst) = true
  hvl : valsOK Wv bv (vbT.map (fun p => p.2.1)) = true
  hvh : valsOK Wv bv (vbT.map (fun p => p.2.2)) = true
  hvbS : vbOK Wv 7 bv (tpackS Wv (tslots 7 bv (mapL (fun p => (p.1, p.2.1)) vbT)))
    (tpackS Wv (tslots 7 bv (mapL (fun p => (p.1, p.2.2)) vbT))) d.qd d.qd.Gs d.vbS = true
  hvbB : vbOK Wv 7 bv (tpackS Wv (tslots 7 bv (mapL (fun p => (p.1, p.2.1)) vbT)))
    (tpackS Wv (tslots 7 bv (mapL (fun p => (p.1, p.2.2)) vbT))) d.qd d.qd.Gb d.vbB = true
  hwing : d.qd.qh ≠ 0 → ∃ ol oh : ℕ, wingOK g SQ d.w d.qd oqT ol oh d.vbS = true
  hgs : d.qd.Gs.all (inBox (-3) 3) = true
  hent : ∀ i < d.qd.Gs.length, entCol g d.SO d.w d.qd d.Elo d.Ehi d.vbS
    (tpackS g.W (tslots 7 g.bias gl.rho)) i (d.cols.getD i []) = true
  hkok : kOK d.cf d.qd.Gs ⟨st.Gk, st.ck, st.Ek, d.kq.Gq, d.kq.cq, d.kq.Eq⟩ d.H = true
  hkokb : kOK d.cfb d.qd.Gb ⟨st.Gk, st.ck, st.Ek, d.kq.Gq, d.kq.cq.take gl.nocc, d.kq.Eq.take gl.nocc⟩ d.Hb = true
  hkokA : kOK cfA gl.Gch ⟨st.Gk, st.ck, st.Ek, st.Gk, st.ck, st.Ek⟩ HA = true
  hxs : all2 (fun hs txs => all2 (fun h tx => xsExact tx h) hs txs) d.H d.Tx = true
  hsh : shOK SOUT g.SI gl.SC g.SV d.sh d.Tx = true
  hn : ∀ a < st.ck.length, ∀ n1 < d.kq.cq.length, nOK kc (decide (n1 < gl.nocc))
    (mkEn RN g.Den she tz (st.Ek.getD a 0) (d.kq.Eq.getD n1 0) 0)
    (mkEn RN g.Den she tz (st.Ek.getD a 0) (d.kq.Eq.getD n1 0) 1)
    (xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])) d.vbS d.cols
    ((d.sh.getD a []).getD n1 0) ((d.O.getD a []).getD n1 []) = true
  hex : ∀ a < st.ck.length, exOK (d.Hb.getD a []) d.vbB d.shx (d.XO.getD a (0, 0)).1 (d.XO.getD a (0, 0)).2 = true
  hshx : d.shx + SOUT = 4 * gl.SC + g.SV
  hcs : ∀ a < st.ck.length, csOK (d.WA.getD a 0) 7 (d.bA.getD a 0) (zipW Prod.mk gl.Gch ((HA.getD a []).getD a []))
    d.qd d.vbS d.cols d.shc (d.CO.getD a (0, 0)).1 (d.CO.getD a (0, 0)).2 = true
  hshc : d.shc + SOUT = g.SI + 2 * gl.SC + g.SV
  hgk : keysOK 7 gl.Gch = true
  hnocc : gl.nocc ≤ d.kq.cq.length

/-- The Coulomb hypothesis at scale `2^SV`. -/
def VbHyp (vbT : List (V3 × ℤ × ℤ)) (SV : ℕ) (vb : V3 → ℝ) : Prop :=
  ∀ p ∈ vbT, (p.2.1 : ℝ) / 2 ^ SV ≤ vb p.1 ∧ vb p.1 ≤ (p.2.2 : ℝ) / 2 ^ SV

theorem VbHyp.scaled {vbT : List (V3 × ℤ × ℤ)} {SV : ℕ} {vb : V3 → ℝ} (h : VbHyp vbT SV vb) :
    ∀ p ∈ vbT, (p.2.1 : ℝ) ≤ vb p.1 * 2 ^ SV ∧ vb p.1 * 2 ^ SV ≤ p.2.2 := fun p hp => by
  have hS : (0 : ℝ) < 2 ^ SV := by positivity
  obtain ⟨a, b⟩ := h p hp
  exact ⟨by rwa [div_le_iff₀ hS] at a, by rwa [le_div_iff₀ hS] at b⟩

/-- The eps⁻¹ box hypothesis of a block. -/
def EHyp (E : ℕ → ℕ → ℕ → ℝ) (iq SO : ℕ) (Elo Ehi : List (List ℤ)) : Prop :=
  ∀ a b, ((ent Elo a b : ℤ) : ℝ) / 2 ^ SO ≤ E iq a b ∧ E iq a b ≤ ((ent Ehi a b : ℤ) : ℝ) / 2 ^ SO

section stq

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQ SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

theorem stq_vbS (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA) {vb : V3 → ℝ}
    (hvb : VbHyp vbT g.SV vb) :
    d.qd.Gs.length = d.vbS.length ∧ ∀ k < d.qd.Gs.length, ((d.vbS.getD k (0, 0)).1 : ℝ) ≤
      vb (key d.qd (gs d.qd k)) * 2 ^ g.SV ∧ vb (key d.qd (gs d.qd k)) * 2 ^ g.SV ≤ (d.vbS.getD k (0, 0)).2 := by
  obtain ⟨hl, hk⟩ := vbOK_sound h.hvk h.hvl h.hvh h.hvbS hvb.scaled
  exact ⟨hl, fun k hk' => ⟨(hk k hk').1, (hk k hk').2.1⟩⟩

theorem stq_vbB (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA) {vb : V3 → ℝ}
    (hvb : VbHyp vbT g.SV vb) :
    d.qd.Gb.length = d.vbB.length ∧ ∀ k < d.qd.Gb.length, ((d.vbB.getD k (0, 0)).1 : ℝ) ≤
      vb (key d.qd (d.qd.Gb.getD k 0)) * 2 ^ g.SV ∧ vb (key d.qd (d.qd.Gb.getD k 0)) * 2 ^ g.SV ≤ (d.vbB.getD k (0, 0)).2 := by
  obtain ⟨hl, hk⟩ := vbOK_sound h.hvk h.hvl h.hvh h.hvbB hvb.scaled
  exact ⟨hl, fun k hk' => ⟨(hk k hk').1, (hk k hk').2.1⟩⟩

/-- **All entries** of the q-point satisfy `EntOK`. -/
theorem stq_ent (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA)
    {E : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ} (hE : EHyp E d.qd.iq d.SO d.Elo d.Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2) :
    ∀ i < d.qd.Gs.length, ∀ j < d.qd.Gs.length,
      EntOK (2 ^ g.SI) g.Den ((d.cols.getD i []).getD j default) (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) := by
  intro i hi j hj
  obtain ⟨-, hvS⟩ := stq_vbS h hvb
  have hw : WingOK gl vb oq g.SF d.w d.qd := by
    intro hq
    obtain ⟨ol, oh, hw⟩ := h.hwing hq
    exact wingOK_sound hw h.hSB h.hB hoq (hvS 0 (by omega)) hq
  have hbox : ∀ k < d.qd.Gs.length, inBox (-3) 3 (gs d.qd k) = true := fun k hk =>
    List.all_eq_true.mp h.hgs _ (getD_mem 0 hk)
  have hrho : RhoDig gl g.bias (gs d.qd j - gs d.qd i)
      (tget g.W g.h (tpackS g.W (tslots 7 g.bias gl.rho)) (gs d.qd j - gs d.qd i)) := by
    rw [h.hh]; exact rho_dig h.hrk h.hrv (diff_box (hbox j hj) (hbox i hi))
  have hc := h.hent i hi
  unfold entCol at hc
  simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at hc
  obtain ⟨hlen, hall⟩ := hc
  obtain ⟨-, hj'⟩ := all2_spec _ 0 default _ _ hall
  have hchk := hj' j (by rw [List.length_range]; exact hj)
  rw [getD_range hj] at hchk
  obtain ⟨e1, e2⟩ := hE (d.qd.idx.getD j 0) (d.qd.idx.getD i 0)
  exact entChk_sound hchk (h.hSB.symm ▸ rfl) h.hB h.hSR h.hSOm h.hOm h.hOm0 h.hRN h.hnel h.hts h.htsn h.hwinv
    h.hDen0 e1 e2 hw hrho (hvS j hj)

end stq

section stq2

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQ SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

/-- The weights: `xS(G_k) = W_k 2^Tx / 2^(2 SC)`. -/
theorem stq_xS (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA) {a n1 : ℕ}
    (ha : a < st.ck.length) (hn1 : n1 < d.kq.cq.length) :
    ((d.H.getD a []).getD n1 []).length = d.qd.Gs.length ∧
    ∀ k < d.qd.Gs.length, xS gl st t a n1 (gs (gl.qs.getD t default) k) =
      wv ((xsOf ((d.Tx.getD a []).getD n1 0) ((d.H.getD a []).getD n1 [])).getD k (false, 0)) *
        (2 ^ ((d.Tx.getD a []).getD n1 0) / 2 ^ (2 * gl.SC)) := by
  obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkok
  obtain ⟨hHa, hHc⟩ := hH a ha
  obtain ⟨hrow, hval⟩ := hHc n1 hn1
  refine ⟨hrow, fun k hk => ?_⟩
  -- the exactness of the shift
  have hxs := h.hxs
  obtain ⟨hl1, hl2⟩ := all2_spec _ [] [] _ _ hxs
  have hr1 := hl2 a (by rw [hHl]; exact ha)
  obtain ⟨-, hr2⟩ := all2_spec _ [] 0 _ _ hr1
  have hx := hr2 n1 (by rw [hHa]; exact hn1)
  have hw := xsOf_wv hx k (by rw [hrow]; exact hk)
  rw [h.hq]
  unfold xS
  rw [h.hkq]
  have e := pd_Mint gl ⟨st.Gk, st.ck, st.Ek, d.kq.Gq, d.kq.cq, d.kq.Eq⟩ a n1 (gs d.qd k)
  simp only at e
  rw [e]
  have hv := hval k hk
  unfold gs
  rw [← hv]
  have hT : (0 : ℝ) < 2 ^ (2 * gl.SC) := by positivity
  rw [mul_div_assoc', eq_div_iff hT.ne', div_mul_cancel₀ _ hT.ne', hw]

end stq2

section stq3

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQ SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

theorem Qlin (n : ℕ) (W V : ℕ → ℝ) (A B : ℕ → ℕ → ℝ) (p r : ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, W i * V i * W j * (p * A j i - r * B j i) =
      p * ∑ i ∈ range n, ∑ j ∈ range n, W i * V i * W j * A j i -
        r * ∑ i ∈ range n, ∑ j ∈ range n, W i * V i * W j * B j i := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem wxS_eq (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA) (a n1 iw : ℕ) :
    wxS gl st t a n1 iw = (let w := RYD * (dy gl.SEn (st.Ek.getD a 0) - dy gl.SEn (d.kq.Eq.getD n1 0)) + iw
      if |w| < TZ then TZ else w) := by
  unfold wxS; rw [h.hkq]

/-- **The hot-path parts** `Pq`, `ACq` of every (band, inner band) are in the claimed
enclosures (scaled by `N_q Ω 2^SOUT`, with factors `2` and `4`). -/
theorem stq_n (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA)
    {E : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ} (hE : EHyp E d.qd.iq d.SO d.Elo d.Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hNq : 0 < Nq gl * vol gl) :
    ∀ a < st.ck.length, ∀ n1 < nbq st t,
      (((d.O.getD a []).getD n1 []).getD 0 0 : ℝ) ≤ Pq gl E vb oq st t a n1 0 * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
      Pq gl E vb oq st t a n1 0 * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤ (((d.O.getD a []).getD n1 []).getD 1 0 : ℝ) ∧
      (((d.O.getD a []).getD n1 []).getD 2 0 : ℝ) ≤ Pq gl E vb oq st t a n1 1 * (Nq gl * vol gl) * 2 * 2 ^ SOUT ∧
      Pq gl E vb oq st t a n1 1 * (Nq gl * vol gl) * 2 * 2 ^ SOUT ≤ (((d.O.getD a []).getD n1 []).getD 3 0 : ℝ) ∧
      (((d.O.getD a []).getD n1 []).getD 4 0 : ℝ) ≤ ACq gl E vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
      ACq gl E vb oq st t a n1 * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤ (((d.O.getD a []).getD n1 []).getD 5 0 : ℝ) := by
  intro a ha n1 hn1
  have hn1' : n1 < d.kq.cq.length := by unfold nbq at hn1; rw [h.hkq] at hn1; exact hn1
  set Tx := (d.Tx.getD a []).getD n1 0 with hTx
  set hr := (d.H.getD a []).getD n1 [] with hhr
  set xs := xsOf Tx hr with hxsd
  obtain ⟨hrl, hxS⟩ := stq_xS h ha hn1'
  have hxl : xs.length = d.qd.Gs.length := by rw [hxsd, xsOf_length, hrl]
  obtain ⟨hvl, hvS⟩ := stq_vbS h hvb
  have hent := stq_ent h hE hvb hoq
  have hD : (0 : ℝ) < g.Den := by exact_mod_cast h.hDen0
  have e0 := mkEn_spec (st.Ek.getD a 0) (d.kq.Eq.getD n1 0) 0 h.hRNe h.hD1 h.htz'
  have e1 := mkEn_spec (st.Ek.getD a 0) (d.kq.Eq.getD n1 0) 1 h.hRNe h.hD1 h.htz'
  rw [← wxS_eq h] at e0 e1
  have hN := nOK_sound (S := 2 ^ g.SI) hD h.hk2 h.hl h.htz e0 e1 (h.hn a ha n1 hn1')
    (I := fun j i => IeS gl E vb oq d.qd j i) (O := fun j i => Om2S gl vb d.qd j i)
    (V := fun i => vb (key d.qd (gs d.qd i)) * 2 ^ g.SV)
    (fun i hi => hvS i (by rw [← hxl]; exact hi))
    (fun i hi j hj => hent i (by rw [← hxl]; exact hi) j (by rw [← hxl]; exact hj))
  simp only at hN
  rw [hxl] at hN
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩, ⟨r0, r1⟩⟩ := hN
  -- the spec's quadratic forms
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
  have hQ := fun F => quad_eq gl vb st t a n1 F W V c u hxk hvk
  rw [hq] at hQ
  -- the scale: c² u N_q Ω / 2^SI = 1 / 2^(sh + SOUT)
  have hsh := h.hsh
  obtain ⟨-, hs1⟩ := all2_spec _ [] [] _ _ hsh
  have hlenT : a < d.sh.length := by
    obtain ⟨hl1, -⟩ := all2_spec _ [] [] _ _ hsh
    obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkok
    obtain ⟨hl3, -⟩ := all2_spec _ [] [] _ _ h.hxs
    rw [hl1, ← hl3, hHl]; exact ha
  have hs2 := hs1 a hlenT
  obtain ⟨hl4, hs3⟩ := all2_spec _ 0 0 _ _ hs2
  have hn1T : n1 < (d.sh.getD a []).length := by
    obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkok
    obtain ⟨hl3, hl3'⟩ := all2_spec _ [] [] _ _ h.hxs
    obtain ⟨hl5, -⟩ := all2_spec _ [] 0 _ _ (hl3' a (by rw [hHl]; exact ha))
    rw [hl4, ← hl5, (hH a ha).1]; exact hn1'
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
  set X := Nq gl * vol gl with hXd
  set Sh := (2 : ℝ) ^ shv
  have hSh : 0 < Sh := by positivity
  have hSI : (0 : ℝ) < 2 ^ g.SI := by positivity
  set Qf := fun F : ℕ → ℕ → ℝ => ∑ i ∈ range d.qd.Gs.length, ∑ j ∈ range d.qd.Gs.length, W i * V i * W j * F j i
  have hQS : ∀ F : ℕ → ℕ → ℝ, Qf (fun j i => 2 ^ g.SI * F j i) = 2 ^ g.SI * Qf F := fun F => by
    simp only [Qf, mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have key : ∀ F : ℕ → ℕ → ℝ, quad gl vb st t a n1 F * X * 2 ^ SOUT = Qf (fun j i => 2 ^ g.SI * F j i) / Sh := by
    intro F
    rw [hQ F, hQS]
    have : c ^ 2 * u * X / 2 ^ g.SI * 2 ^ SOUT = 1 / Sh := hscale
    field_simp
    field_simp at this
    linear_combination Qf F * this
  -- the targets in terms of `Qf`
  have hocc : (decide (n1 < gl.nocc) = true) ↔ n1 < gl.nocc := decide_eq_true_iff
  have hP : ∀ (x : ℝ), (1 / 2 * quad gl vb st t a n1 (fun j i => schM (Iq gl E vb oq t j i) (Oq gl vb t j i) x) -
      (if n1 < gl.nocc then quad gl vb st t a n1
        (fun j i => ssxM (Iq gl E vb oq t j i) (Oq gl vb t j i) x) else 0)) * X * 2 * 2 ^ SOUT =
      Qf (fun j i => tP (decide (n1 < gl.nocc)) (2 ^ g.SI) (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x) / Sh := by
    intro x
    have eI : ∀ j i, Iq gl E vb oq t j i = IeS gl E vb oq d.qd j i := fun j i => by unfold Iq; rw [hq]
    have eO : ∀ j i, Oq gl vb t j i = Om2S gl vb d.qd j i := fun j i => by unfold Oq; rw [hq]
    simp only [eI, eO]
    have k1 := key (fun j i => schM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x)
    have k2 := key (fun j i => ssxM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x)
    unfold tP
    by_cases ho : n1 < gl.nocc
    · simp only [ho, if_true, decide_true]
      have hl := Qlin d.qd.Gs.length W V (fun j i => schM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x)
        (fun j i => ssxM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x) (2 ^ g.SI) (2 * 2 ^ g.SI)
      have e3 : Qf (fun j i => 2 ^ g.SI * schM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x -
          2 * (2 ^ g.SI * ssxM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x)) =
          Qf (fun j i => 2 ^ g.SI * schM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x) -
            2 * Qf (fun j i => 2 ^ g.SI * ssxM (IeS gl E vb oq d.qd j i) (Om2S gl vb d.qd j i) x) := by
        simp only [Qf, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
      rw [e3, sub_div, ← k1, mul_div_assoc, ← k2]; ring
    · simp only [ho, if_false, decide_false, Bool.false_eq_true, sub_zero]
      rw [← k1]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Pq; rw [hP]; rw [le_div_iff₀ hSh]; exact p0
  · unfold Pq; rw [hP]; rw [div_le_iff₀ hSh]; exact p1
  · unfold Pq; rw [hP]; rw [le_div_iff₀ hSh]; exact q0
  · unfold Pq; rw [hP]; rw [div_le_iff₀ hSh]; exact q1
  · have hA : ACq gl E vb oq st t a n1 * X * 4 * 2 ^ SOUT =
        Qf (fun j i => 2 ^ g.SI * IeU (IeS gl E vb oq d.qd j i)) / Sh := by
      unfold ACq
      have eI : ∀ j i, Iq gl E vb oq t j i = IeS gl E vb oq d.qd j i := fun j i => by unfold Iq; rw [hq]
      simp only [eI]
      have k1 := key (fun j i => IeU (IeS gl E vb oq d.qd j i))
      have hneg := hQ (fun j i => -IeU (IeS gl E vb oq d.qd j i))
      have hpos := hQ (fun j i => IeU (IeS gl E vb oq d.qd j i))
      have : quad gl vb st t a n1 (fun j i => -IeU (IeS gl E vb oq d.qd j i)) =
          -quad gl vb st t a n1 (fun j i => IeU (IeS gl E vb oq d.qd j i)) := by
        rw [hneg, hpos]
        simp only [mul_neg, sum_neg_distrib]
      rw [this, ← k1]; ring
    rw [hA, le_div_iff₀ hSh]; exact r0
  · have hA : ACq gl E vb oq st t a n1 * X * 4 * 2 ^ SOUT =
        Qf (fun j i => 2 ^ g.SI * IeU (IeS gl E vb oq d.qd j i)) / Sh := by
      unfold ACq
      have eI : ∀ j i, Iq gl E vb oq t j i = IeS gl E vb oq d.qd j i := fun j i => by unfold Iq; rw [hq]
      simp only [eI]
      have k1 := key (fun j i => IeU (IeS gl E vb oq d.qd j i))
      have hneg := hQ (fun j i => -IeU (IeS gl E vb oq d.qd j i))
      have hpos := hQ (fun j i => IeU (IeS gl E vb oq d.qd j i))
      have : quad gl vb st t a n1 (fun j i => -IeU (IeS gl E vb oq d.qd j i)) =
          -quad gl vb st t a n1 (fun j i => IeU (IeS gl E vb oq d.qd j i)) := by
        rw [hneg, hpos]
        simp only [mul_neg, sum_neg_distrib]
      rw [this, ← k1]; ring
    rw [hA, div_le_iff₀ hSh]; exact r1

end stq3

section stq4

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQ SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

theorem xterm {H v X S2 SV So Sx : ℝ} (hX : X ≠ 0) (h2 : S2 ≠ 0) (hSx : Sx ≠ 0)
    (hsx : Sx * So = S2 ^ 2 * SV) : (H / S2) ^ 2 * (v / X) * X * So = H ^ 2 * (v * SV) / Sx := by
  field_simp
  linear_combination H ^ 2 * v * X * hsx

theorem take_getD {α : Type} (l : List α) (m k : ℕ) (d : α) (hk : k < m) : (l.take m).getD k d = l.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- **The bare exchange** of every band is in its claimed enclosure. -/
theorem stq_x (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA) {vb : V3 → ℝ}
    (hvb : VbHyp vbT g.SV vb) (hNq : 0 < Nq gl * vol gl) :
    ∀ a < st.ck.length, ((d.XO.getD a (0, 0)).1 : ℝ) ≤ Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT ∧
      Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT ≤ (d.XO.getD a (0, 0)).2 := by
  intro a ha
  obtain ⟨hvl, hvB⟩ := stq_vbB h hvb
  obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkokb
  simp only at hHl hH
  obtain ⟨hHa, hHc⟩ := hH a ha
  have hta : (d.kq.cq.take gl.nocc).length = gl.nocc := by rw [List.length_take]; exact min_eq_left h.hnocc
  rw [hta] at hHa
  have hX := exOK_sound (h.hex a ha) (V := fun g' => vb (key d.qd (d.qd.Gb.getD g' 0)) * 2 ^ g.SV)
    (fun g' hg => hvB g' (by rw [hvl]; exact hg))
  rw [hHa, ← hvl] at hX
  -- the spec
  have hS : (0 : ℝ) < 2 ^ (4 * gl.SC + g.SV) := by positivity
  have hsc : (2 : ℝ) ^ d.shx * 2 ^ SOUT = 2 ^ (4 * gl.SC + g.SV) := by rw [← pow_add, h.hshx]
  have hsc' : (2 : ℝ) ^ d.shx * 2 ^ SOUT = ((2 : ℝ) ^ (2 * gl.SC)) ^ 2 * 2 ^ g.SV := by
    rw [hsc, ← pow_mul, ← pow_add]; congr 1; ring
  have term : ∀ r < gl.nocc, ∀ g' < d.qd.Gb.length,
      pd gl st.Gk (st.ck.getD a []) d.kq.Gq (d.kq.cq.getD r []) (d.qd.Gb.getD g' 0) ^ 2 *
        (vb (key d.qd (d.qd.Gb.getD g' 0)) / (Nq gl * vol gl)) * (Nq gl * vol gl) * 2 ^ SOUT =
      (((d.Hb.getD a []).getD r []).getD g' 0 : ℝ) ^ 2 * (vb (key d.qd (d.qd.Gb.getD g' 0)) * 2 ^ g.SV) /
        2 ^ d.shx := by
    intro r hr' g' hg'
    have e := pd_Mint gl ⟨st.Gk, st.ck, st.Ek, d.kq.Gq, d.kq.cq.take gl.nocc, d.kq.Eq.take gl.nocc⟩ a r
      (d.qd.Gb.getD g' 0)
    simp only at e
    rw [take_getD _ _ _ _ hr'] at e
    rw [e]
    obtain ⟨hrow, hval⟩ := hHc r (by rw [hta]; exact hr')
    rw [hval g' hg']
    exact xterm hNq.ne' (by positivity) (by positivity) hsc'
  have eX : Xq gl vb st t a * (Nq gl * vol gl) * 2 ^ SOUT =
      (-∑ r ∈ range gl.nocc, ∑ g' ∈ range d.qd.Gb.length,
        (((d.Hb.getD a []).getD r []).getD g' 0 : ℝ) ^ 2 * (vb (key d.qd (d.qd.Gb.getD g' 0)) * 2 ^ g.SV)) /
        2 ^ d.shx := by
    unfold Xq
    dsimp only
    rw [h.hq, h.hkq, neg_div, neg_mul, neg_mul, neg_inj, sum_mul, sum_mul, sum_div]
    refine sum_congr rfl fun r hr => ?_
    rw [sum_mul, sum_mul, sum_div]
    refine sum_congr rfl fun g' hg => ?_
    exact term r (mem_range.mp hr) g' (mem_range.mp hg)
  rw [eX, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  exact hX

end stq4

section stq5

variable {gl : Gl} {st : St} {t : ℕ} {d : SQ} {g : EG} {kc : KC} {SQ SOUT RN she tz Wv bv : ℕ}
  {vbT oqT : List (V3 × ℤ × ℤ)} {HA : List (List (List ℤ))} {cfA : Cfg}

theorem zipW_fst {α β : Type} : ∀ (ks : List α) (vs : List β), ks.length = vs.length →
    (zipW Prod.mk ks vs).map Prod.fst = ks
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | k :: ks, v :: vs, h => by simp only [zipW_cons_cons, List.map_cons]; rw [zipW_fst ks vs (by simpa using h)]

theorem mem_zipW {α β : Type} {ks : List α} {vs : List β} {p : α × β} (dk : α) (dv : β)
    (hp : p ∈ zipW Prod.mk ks vs) : ∃ k < ks.length, ks.getD k dk = p.1 ∧ vs.getD k dv = p.2 := by
  induction ks generalizing vs with
  | nil => simp at hp
  | cons k ks ih =>
    cases vs with
    | nil => simp at hp
    | cons v vs =>
      simp only [zipW_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨0, by simp, rfl, rfl⟩
      · obtain ⟨j, hj, e1, e2⟩ := ih hp
        exact ⟨j + 1, by simp; omega, by simpa using e1, by simpa using e2⟩

/-- **The exact static remainder** of every band is in its claimed enclosure. -/
theorem stq_cs (h : StqOK gl st t d g kc SQ SOUT RN she tz Wv bv vbT oqT HA cfA)
    {E : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ} (hE : EHyp E d.qd.iq d.SO d.Elo d.Ehi)
    (hvb : VbHyp vbT g.SV vb)
    (hoq : ∀ p ∈ oqT, (p.2.1 : ℝ) ≤ oq p.1 * 2 ^ g.SV ∧ oq p.1 * 2 ^ g.SV ≤ p.2.2)
    (hNq : 0 < Nq gl * vol gl) :
    ∀ a < st.ck.length, ((d.CO.getD a (0, 0)).1 : ℝ) ≤ CSq gl E vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT ∧
      CSq gl E vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT ≤ (d.CO.getD a (0, 0)).2 := by
  intro a ha
  obtain ⟨hvl, hvS⟩ := stq_vbS h hvb
  have hent := stq_ent h hE hvb hoq
  obtain ⟨hHl, -, -, hH⟩ := kOK_sound h.hkokA
  obtain ⟨hHa, hHc⟩ := hH a ha
  obtain ⟨hrow, hval⟩ := hHc a ha
  set row := (HA.getD a []).getD a []
  set tab := zipW Prod.mk gl.Gch row with htab
  have hkeys : tab.map Prod.fst = gl.Gch := zipW_fst _ _ hrow.symm
  have hk : keysOK 7 (tab.map Prod.fst) = true := by rw [hkeys]; exact h.hgk
  have hC := csOK_sound (h.hcs a ha) hk h.hgs (S := 2 ^ g.SI) (Den := g.Den)
    (I := fun i j => IeS gl E vb oq d.qd i j) (O := fun i j => Om2S gl vb d.qd i j)
    (fun j hj i hi => hent j hj i hi) (V := fun j => vb (key d.qd (gs d.qd j)) * 2 ^ g.SV) (fun j hj => hvS j hj)
  simp only at hC
  rw [hkeys] at hC
  -- the table value is the pair density
  have htv : ∀ dd ∈ gl.Gch, tv tab dd = pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a []) dd * 2 ^ (2 * gl.SC) := by
    intro dd hdd
    unfold tv
    have hmem : dd ∈ tab.map Prod.fst := by rw [hkeys]; exact hdd
    cases hf : tab.find? (fun p => p.1 == dd) with
    | none =>
      exfalso
      obtain ⟨p, hp, hpd⟩ := List.mem_map.mp hmem
      have := List.find?_eq_none.mp hf p hp
      simp [hpd] at this
    | some p =>
      obtain ⟨hp, hpd⟩ := find_some hf
      obtain ⟨k, hk', e1, e2⟩ := mem_zipW (0 : V3) (0 : ℤ) hp
      simp only [Option.map_some', Option.getD_some]
      rw [← e2, hval k hk', e1, hpd]
      have e := pd_Mint gl ⟨st.Gk, st.ck, st.Ek, st.Gk, st.ck, st.Ek⟩ a a dd
      simp only at e
      rw [e]; field_simp
  have hS : (0 : ℝ) < 2 ^ d.shc := by positivity
  have hsc : (2 : ℝ) ^ d.shc * 2 ^ SOUT = 2 ^ g.SI * 2 ^ (2 * gl.SC) * 2 ^ g.SV := by
    rw [← pow_add, h.hshc, pow_add, pow_add]
  have eC : CSq gl E vb oq st t a * (Nq gl * vol gl) * 4 * 2 ^ SOUT =
      (∑ j ∈ range d.qd.Gs.length, vb (key d.qd (gs d.qd j)) * 2 ^ g.SV * ∑ i ∈ range d.qd.Gs.length,
        (if TS ≤ |IeS gl E vb oq d.qd i j| ∧ gs d.qd i - gs d.qd j ∈ gl.Gch then
          tv tab (gs d.qd i - gs d.qd j) * (-(2 ^ g.SI * IeS gl E vb oq d.qd i j)) else 0)) / 2 ^ d.shc := by
    unfold CSq
    dsimp only
    rw [h.hq, eq_div_iff hS.ne']
    rw [show ∀ A : ℝ, 1 / 4 * A * (Nq gl * vol gl) * 4 * 2 ^ SOUT * 2 ^ d.shc =
      A * ((Nq gl * vol gl) * (2 ^ SOUT * 2 ^ d.shc)) from fun A => by ring, sum_mul]
    refine sum_congr rfl fun j hj => ?_
    have hv : vS gl vb d.qd j * ((Nq gl * vol gl) * (2 ^ SOUT * 2 ^ d.shc)) =
        vb (key d.qd (gs d.qd j)) * 2 ^ g.SV * (2 ^ g.SI * 2 ^ (2 * gl.SC)) := by
      unfold vS
      rw [mul_comm ((2 : ℝ) ^ SOUT), hsc]
      field_simp
      ring
    have hre : ∀ Z : ℝ, (vS gl vb d.qd j * Z) * ((Nq gl * vol gl) * (2 ^ SOUT * 2 ^ d.shc)) =
        vS gl vb d.qd j * ((Nq gl * vol gl) * (2 ^ SOUT * 2 ^ d.shc)) * Z := fun Z => by ring
    rw [hre, hv, mul_assoc]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    by_cases hc : TS ≤ |IeS gl E vb oq d.qd i j| ∧ gs d.qd i - gs d.qd j ∈ gl.Gch
    · rw [if_pos hc, if_pos hc, htv _ hc.2]
      unfold IeS
      ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [eC, le_div_iff₀ hS, div_le_iff₀ hS]
  exact hC

end stq5

end GW.Endpoint.Kernel.Sig

/-
G2 stage 3, soundness (3b/4): the entry check `entChk` certifies `EntOK` for the
real `I_eps(j, i) = IeS …` and `Omega²(j, i) = Om2S …` of spec A, for every eps⁻¹
block `E` inside the stage-1 box, every Coulomb average in its box and the
certified wing factors (`entChk_sound`).
-/
import GW.Endpoint.Kernel.SigmaTab

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### The `I_eps` box -/

theorem pmul_spec {el eh : ℤ} {fl fh : ℕ} {e f : ℝ} (he1 : (el : ℝ) ≤ e) (he2 : e ≤ eh)
    (hf1 : (fl : ℝ) ≤ f) (hf2 : f ≤ fh) :
    ((pmul el eh fl fh).1 : ℝ) ≤ e * f ∧ e * f ≤ (pmul el eh fl fh).2 := by
  have hfl : (0 : ℝ) ≤ fl := Nat.cast_nonneg _
  have hf0 : 0 ≤ f := le_trans hfl hf1
  have e1 : (pmul el eh fl fh).1 = if 0 ≤ el then el * fl else el * fh := rfl
  have e2 : (pmul el eh fl fh).2 = if 0 ≤ eh then eh * fh else eh * fl := rfl
  rw [e1, e2]
  constructor
  · by_cases h : 0 ≤ el
    · rw [if_pos h]; have h' : (0 : ℝ) ≤ el := by exact_mod_cast h
      push_cast; nlinarith
    · rw [if_neg h]; have h' : (el : ℝ) < 0 := by push_neg at h; exact_mod_cast h
      push_cast; nlinarith
  · by_cases h : 0 ≤ eh
    · rw [if_pos h]; have h' : (0 : ℝ) ≤ eh := by exact_mod_cast h
      push_cast; nlinarith
    · rw [if_neg h]; have h' : (eh : ℝ) < 0 := by push_neg at h; exact_mod_cast h
      push_cast; nlinarith

/-- The certified wing factors of a q-point (from `wingOK`), scaled by `2^SF`. -/
def WingOK (gl : Gl) (vb oq : V3 → ℝ) (SF : ℕ) (w : Wing) (qd : QD) : Prop :=
  qd.qh ≠ 0 →
    ((w.frl : ℝ) ≤ oq qd.qh * qlen gl qd / (8 * Real.pi) * 2 ^ SF ∧
      oq qd.qh * qlen gl qd / (8 * Real.pi) * 2 ^ SF ≤ w.frh) ∧
    ((w.fcl : ℝ) ≤ oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) * 2 ^ SF ∧
      oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) * 2 ^ SF ≤ w.fch)

/-- **The `I_eps` box**: `ieBox` encloses `I_eps(j, i) · 2^(SO + SF)` for every block `E`
in the stage-1 box (scale `2^-SO`). -/
theorem ieBox_spec (g : EG) (SO : ℕ) (w : Wing) (qd : QD) (Elo Ehi : List (List ℤ)) (j i : ℕ)
    (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)
    (hE1 : (((Elo.getD (qd.idx.getD j 0) []).getD (qd.idx.getD i 0) 0 : ℤ) : ℝ) / 2 ^ SO ≤
      E qd.iq (qd.idx.getD j 0) (qd.idx.getD i 0))
    (hE2 : E qd.iq (qd.idx.getD j 0) (qd.idx.getD i 0) ≤
      (((Ehi.getD (qd.idx.getD j 0) []).getD (qd.idx.getD i 0) 0 : ℤ) : ℝ) / 2 ^ SO)
    (hw : WingOK gl vb oq g.SF w qd) :
    ((ieBox g SO w qd Elo Ehi j i).1 : ℝ) ≤ IeS gl E vb oq qd j i * 2 ^ (SO + g.SF) ∧
      IeS gl E vb oq qd j i * 2 ^ (SO + g.SF) ≤ (ieBox g SO w qd Elo Ehi j i).2 := by
  set a := qd.idx.getD j 0
  set b := qd.idx.getD i 0
  set lo := (Elo.getD a []).getD b 0
  set hi := (Ehi.getD a []).getD b 0
  set s := xor (qd.neg.getD j false) (qd.neg.getD i false) with hs
  set e := (if qd.neg.getD j false = qd.neg.getD i false then (1 : ℝ) else -1) * E qd.iq a b with he
  have hS0 : (0 : ℝ) < 2 ^ SO := by positivity
  -- the signed block entry, scale 2^SO
  have hsg : ((if s then -hi else lo : ℤ) : ℝ) ≤ e * 2 ^ SO ∧ e * 2 ^ SO ≤ ((if s then -lo else hi : ℤ) : ℝ) := by
    have h1 : (lo : ℝ) ≤ E qd.iq a b * 2 ^ SO := by rw [div_le_iff₀ hS0] at hE1; exact hE1
    have h2 : E qd.iq a b * 2 ^ SO ≤ hi := by rw [le_div_iff₀ hS0] at hE2; exact hE2
    rw [he]
    cases hj : qd.neg.getD j false <;> cases hi' : qd.neg.getD i false <;>
      simp only [hs, hj, hi', Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
        if_true, if_false, Bool.false_eq_true, one_mul, neg_one_mul, Int.cast_neg,
        if_pos rfl, reduceCtorEq, neg_mul] <;> constructor <;> linarith
  set el : ℤ := if s then -hi else lo
  set eh : ℤ := if s then -lo else hi
  have hF : (0 : ℝ) < 2 ^ g.SF := by positivity
  have hSS : (2 : ℝ) ^ (SO + g.SF) = 2 ^ SO * 2 ^ g.SF := pow_add _ _ _
  unfold ieBox IeS epsS
  simp only
  rw [← he]
  have hd : ((if j = i then 1 else 0 : ℝ)) * 2 ^ (SO + g.SF) = ((if j = i then 2 ^ (SO + g.SF) else 0 : ℤ) : ℝ) := by
    split_ifs <;> push_cast <;> ring
  rw [sub_mul, hd]
  -- the eps entry times 2^(SO+SF) in the box `ebx`
  suffices H : ∀ (ebx : ℤ × ℤ) (ev : ℝ), (ebx.1 : ℝ) ≤ ev * 2 ^ (SO + g.SF) →
      ev * 2 ^ (SO + g.SF) ≤ ebx.2 →
      (((if j = i then 2 ^ (SO + g.SF) else 0 : ℤ) - ebx.2 : ℤ) : ℝ) ≤
        ((if j = i then 2 ^ (SO + g.SF) else 0 : ℤ) : ℝ) - ev * 2 ^ (SO + g.SF) ∧
      ((if j = i then 2 ^ (SO + g.SF) else 0 : ℤ) : ℝ) - ev * 2 ^ (SO + g.SF) ≤
        (((if j = i then 2 ^ (SO + g.SF) else 0 : ℤ) - ebx.1 : ℤ) : ℝ) by
    have hplain : ((el * 2 ^ g.SF : ℤ) : ℝ) ≤ e * 2 ^ (SO + g.SF) ∧
        e * 2 ^ (SO + g.SF) ≤ ((eh * 2 ^ g.SF : ℤ) : ℝ) := by
      rw [hSS]; push_cast
      constructor
      · have := mul_le_mul_of_nonneg_right hsg.1 hF.le; linarith
      · have := mul_le_mul_of_nonneg_right hsg.2 hF.le; linarith
    by_cases hq : qd.qh = 0
    · simp only [if_pos hq]
      by_cases hwc : (j = qd.z ∧ i ≠ qd.z) ∨ (i = qd.z ∧ j ≠ qd.z)
      · simp only [if_pos hwc]
        exact H (0, 0) 0 (by simp) (by simp)
      · simp only [if_neg hwc]
        exact H (el * 2 ^ g.SF, eh * 2 ^ g.SF) e hplain.1 hplain.2
    · simp only [if_neg hq]
      obtain ⟨⟨fr1, fr2⟩, ⟨fc1, fc2⟩⟩ := hw hq
      have hel : (el : ℝ) ≤ e * 2 ^ SO := hsg.1
      have heh : e * 2 ^ SO ≤ eh := hsg.2
      by_cases hr : j = qd.z ∧ i ≠ qd.z
      · simp only [if_pos hr]
        have := pmul_spec hel heh fr1 fr2
        have e2 : e * (oq qd.qh * qlen gl qd / (8 * Real.pi)) * (2 ^ SO * 2 ^ g.SF) =
            e * 2 ^ SO * (oq qd.qh * qlen gl qd / (8 * Real.pi) * 2 ^ g.SF) := by ring
        refine H (pmul el eh w.frl w.frh) (e * (oq qd.qh * qlen gl qd / (8 * Real.pi))) ?_ ?_ <;>
          rw [hSS, e2]
        · exact this.1
        · exact this.2
      · simp only [if_neg hr]
        by_cases hc : i = qd.z ∧ j ≠ qd.z
        · simp only [if_pos hc]
          have := pmul_spec hel heh fc1 fc2
          have e2 : e * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd)) * (2 ^ SO * 2 ^ g.SF) =
              e * 2 ^ SO * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) * 2 ^ g.SF) := by ring
          refine H (pmul el eh w.fcl w.fch) (e * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd))) ?_ ?_ <;>
            rw [hSS, e2]
          · exact this.1
          · exact this.2
        · simp only [if_neg hc]
          exact H (el * 2 ^ g.SF, eh * 2 ^ g.SF) e hplain.1 hplain.2
  intro ebx ev h1 h2
  push_cast
  constructor <;> linarith

/-! ### `Omega²` -/

theorem dotB_eq (gl : Gl) (qd : QD) (G G' : V3) :
    dotB gl (vec qd G) (vec qd G') = (dotN gl.B qd.qh G G' : ℝ) / (4 * 2 ^ gl.SB) := by
  unfold dotB vec dotN bd dy
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  field_simp
  ring

/-- `fact = wpsq / nelec = 16 π RYD² / celvol` when `nelec ≠ 0`. -/
theorem factW_eq (gl : Gl) (hn : nelec gl ≠ 0) : factW gl = 16 * Real.pi * RYD ^ 2 / vol gl := by
  unfold factW wpsq
  calc RYD * RYD * 16 * Real.pi * nelec gl / vol gl / nelec gl
      = (16 * Real.pi * RYD ^ 2 / vol gl) * (nelec gl / nelec gl) := by ring
    _ = 16 * Real.pi * RYD ^ 2 / vol gl := by rw [div_self hn, mul_one]

/-- The RHO lookup at `d` as the table digit `tg` (bias `b`). -/
def RhoDig (gl : Gl) (b : ℕ) (d : V3) (tg : ℕ) : Prop :=
  (rhoF gl d = none ∧ tg = 0) ∨ ∃ rN : ℤ, rhoF gl d = some (dy gl.SR rN) ∧ (tg : ℤ) = b + rN ∧ tg ≠ 0

/-- **`Omega²` enclosure**: `sg neg Omega² ∈ [lo, hi] / D_O` for a nonzero enclosure, and
`Omega² = 0` otherwise. -/
theorem om2_spec (g : EG) (qd : QD) (vbS : List (ℕ × ℕ)) (P : ℕ) (j i : ℕ) (gl : Gl) (vb : V3 → ℝ)
    (hSB : gl.SB = g.SB) (hB : gl.B = g.B) (hSR : gl.SR = g.SR) (hSOm : gl.SOm = g.SOm)
    (hOm : gl.Om = g.OmN) (hOm0 : 0 < g.OmN) (hRN : g.RN = 1360569253)
    (hn : nelec gl ≠ 0)
    (hrho : RhoDig gl g.bias (gs qd j - gs qd i) (tget g.W g.h P (gs qd j - gs qd i)))
    (hvb : ((vbS.getD j (0, 0)).1 : ℝ) ≤ vb (key qd (gs qd j)) * 2 ^ g.SV ∧
      vb (key qd (gs qd j)) * 2 ^ g.SV ≤ (vbS.getD j (0, 0)).2) :
    ((om2 g qd vbS P j i).nz = false → Om2S gl vb qd j i = 0) ∧
    ((om2 g qd vbS P j i).nz = true →
      ((om2 g qd vbS P j i).lo : ℝ) ≤ sg (om2 g qd vbS P j i).neg (Om2S gl vb qd j i) * DO g ∧
      sg (om2 g qd vbS P j i).neg (Om2S gl vb qd j i) * DO g ≤ (om2 g qd vbS P j i).hi) := by
  have hvol : vol gl = (g.OmN : ℝ) / 2 ^ g.SOm := by unfold vol dy; rw [hOm, hSOm]; push_cast; rfl
  have hRY : RYD = (g.RN : ℝ) / 10 ^ 8 := by rw [hRN]; unfold RYD; norm_num
  have hDO : (DO g : ℝ) = 10 ^ 36 * 4 * 2 ^ (g.SB + g.SR + g.SV) * g.OmN := by unfold DO; push_cast; ring
  have hOm0' : (0 : ℝ) < g.OmN := by exact_mod_cast hOm0
  unfold om2 Om2S
  simp only
  rcases hrho with ⟨hnone, htg⟩ | ⟨rN, hsome, htg, htg0⟩
  · rw [hnone, htg]; simp
  · rw [hsome, if_neg htg0]
    dsimp only
    have hrv : ((tget g.W g.h P (gs qd j - gs qd i) : ℤ) - g.bias) = rN := by rw [htg]; ring
    rw [hrv]
    by_cases hq : qd.qh = 0 ∧ gs qd j = 0
    · rw [if_pos hq, if_pos hq]
      by_cases hi0 : gs qd i = 0
      · rw [if_pos hi0, if_pos hi0]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not]
        refine ⟨fun h => by rw [h]; unfold dy; simp, fun h => ?_⟩
        rw [factW_eq gl hn, hvol, hRY]
        unfold dy
        rw [hSR, hDO]
        have hpi1 := Real.pi_gt_d20
        have hpi2 := Real.pi_lt_d20
        have hne : (rN : ℝ) ≠ 0 := by exact_mod_cast h
        have key : sg (decide (rN < 0)) (16 * Real.pi * ((g.RN : ℝ) / 10 ^ 8) ^ 2 / ((g.OmN : ℝ) / 2 ^ g.SOm) *
            ((rN : ℝ) / 2 ^ g.SR)) * (10 ^ 36 * 4 * 2 ^ (g.SB + g.SR + g.SV) * g.OmN) =
            Real.pi * 10 ^ 20 * (16 * (g.RN : ℝ) ^ 2 * (rN.natAbs : ℝ) * 2 ^ g.SOm * 4 * 2 ^ (g.SB + g.SV)) := by
          have hab : sg (decide (rN < 0)) (rN : ℝ) = (rN.natAbs : ℝ) := by
            rcases lt_or_le rN 0 with hl | hl
            · simp only [hl, decide_true, sg_true]; rw [Nat.cast_natAbs]; push_cast
              rw [abs_of_neg (by exact_mod_cast hl)]
            · simp only [not_lt.mpr hl, decide_false, sg_false]; rw [Nat.cast_natAbs]; push_cast
              rw [abs_of_nonneg (by exact_mod_cast hl)]
          rw [show 16 * Real.pi * ((g.RN : ℝ) / 10 ^ 8) ^ 2 / ((g.OmN : ℝ) / 2 ^ g.SOm) * ((rN : ℝ) / 2 ^ g.SR) =
            (16 * Real.pi * ((g.RN : ℝ) / 10 ^ 8) ^ 2 / ((g.OmN : ℝ) / 2 ^ g.SOm) / 2 ^ g.SR) * (rN : ℝ) by ring,
            sg_mul, hab]
          field_simp
          ring
        rw [key]
        have hc : (0 : ℝ) ≤ 16 * (g.RN : ℝ) ^ 2 * (rN.natAbs : ℝ) * 2 ^ g.SOm * 4 * 2 ^ (g.SB + g.SV) := by
          positivity
        unfold piLo piHi
        push_cast
        constructor <;> nlinarith
      · rw [if_neg hi0, if_neg hi0]; simp
    · rw [if_neg hq, if_neg hq]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not]
      set pr := dotN g.B qd.qh (gs qd i) (gs qd j) * rN with hpr
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [dotB_eq, hB]
        have : dotN g.B qd.qh (gs qd i) (gs qd j) = 0 ∨ rN = 0 := by
          rcases mul_eq_zero.mp h with h | h
          · exact Or.inl h
          · exact Or.inr h
        rcases this with h | h <;> simp [h, dy]
      · rw [factW_eq gl hn, hvol, hRY, dotB_eq, hB, hSB]
        unfold dy
        rw [hSR, hDO]
        set V := vb (key qd (gs qd j)) * 2 ^ g.SV with hV
        have hvbV : vb (key qd (gs qd j)) = V / 2 ^ g.SV := by rw [hV]; field_simp
        rw [hvbV]
        have hab : sg (decide (pr < 0)) (pr : ℝ) = (pr.natAbs : ℝ) := by
          rcases lt_or_le pr 0 with hl | hl
          · simp only [hl, decide_true, sg_true]; rw [Nat.cast_natAbs]; push_cast
            rw [abs_of_neg (by exact_mod_cast hl)]
          · simp only [not_lt.mpr hl, decide_false, sg_false]; rw [Nat.cast_natAbs]; push_cast
            rw [abs_of_nonneg (by exact_mod_cast hl)]
        have key : sg (decide (pr < 0)) (16 * Real.pi * ((g.RN : ℝ) / 10 ^ 8) ^ 2 / ((g.OmN : ℝ) / 2 ^ g.SOm) *
            (V / 2 ^ g.SV) / (8 * Real.pi) *
            ((dotN g.B qd.qh (gs qd i) (gs qd j) : ℝ) / (4 * 2 ^ g.SB)) * ((rN : ℝ) / 2 ^ g.SR)) *
            (10 ^ 36 * 4 * 2 ^ (g.SB + g.SR + g.SV) * g.OmN) =
            V * (2 * (g.RN : ℝ) ^ 2 * (pr.natAbs : ℝ) * 2 ^ g.SOm * 10 ^ 20) := by
          rw [← hab, hpr]
          have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
          cases decide ((dotN g.B qd.qh (gs qd i) (gs qd j) * rN) < 0) <;> simp only [sg] <;>
            push_cast <;> field_simp <;> ring
        rw [key]
        set C := 2 * (g.RN : ℝ) ^ 2 * (pr.natAbs : ℝ) * 2 ^ g.SOm * 10 ^ 20 with hCdef
        have hc : (0 : ℝ) ≤ C := by positivity
        have e1 : ((2 * g.RN ^ 2 * (vbS.getD j (0, 0)).1 * pr.natAbs * 2 ^ g.SOm * 10 ^ 20 : ℕ) : ℝ) =
            (vbS.getD j (0, 0)).1 * C := by rw [hCdef]; push_cast; ring
        have e2 : ((2 * g.RN ^ 2 * (vbS.getD j (0, 0)).2 * pr.natAbs * 2 ^ g.SOm * 10 ^ 20 : ℕ) : ℝ) =
            (vbS.getD j (0, 0)).2 * C := by rw [hCdef]; push_cast; ring
        rw [e1, e2]
        exact ⟨mul_le_mul_of_nonneg_right hvb.1 hc, mul_le_mul_of_nonneg_right hvb.2 hc⟩

/-! ### The entry decisions -/

section decisions

variable {tsn tse SI : ℕ} {IL IH : ℤ} {I : ℝ}

theorem thr_u (hts : TS = (tsn : ℝ) / 2 ^ tse) (h1 : (IL : ℝ) ≤ 2 ^ SI * I) (h2 : 2 ^ SI * I ≤ IH)
    (hu : ((tsn : ℤ) * 2 ^ SI ≤ IL * 2 ^ tse ∨ IH * 2 ^ tse ≤ -((tsn : ℤ) * 2 ^ SI))) : TS ≤ |I| := by
  have hS : (0 : ℝ) < 2 ^ SI := by positivity
  have hT : (0 : ℝ) < 2 ^ tse := by positivity
  rw [hts]
  rcases hu with h | h
  · have h' : (tsn : ℝ) * 2 ^ SI ≤ IL * 2 ^ tse := by exact_mod_cast h
    have : (tsn : ℝ) / 2 ^ tse ≤ I := by
      rw [div_le_iff₀ hT]; nlinarith
    exact le_trans this (le_abs_self I)
  · have h' : (IH : ℝ) * 2 ^ tse ≤ -((tsn : ℝ) * 2 ^ SI) := by exact_mod_cast h
    have : (tsn : ℝ) / 2 ^ tse ≤ -I := by
      rw [div_le_iff₀ hT]; nlinarith
    exact le_trans this (neg_le_abs I)

theorem thr_uf (hts : TS = (tsn : ℝ) / 2 ^ tse) (h1 : (IL : ℝ) ≤ 2 ^ SI * I) (h2 : 2 ^ SI * I ≤ IH)
    (hu : -((tsn : ℤ) * 2 ^ SI) < IL * 2 ^ tse ∧ IH * 2 ^ tse < (tsn : ℤ) * 2 ^ SI) : |I| < TS := by
  have hS : (0 : ℝ) < 2 ^ SI := by positivity
  have hT : (0 : ℝ) < 2 ^ tse := by positivity
  have a1 : -((tsn : ℝ) * 2 ^ SI) < IL * 2 ^ tse := by exact_mod_cast hu.1
  have a2 : (IH : ℝ) * 2 ^ tse < (tsn : ℝ) * 2 ^ SI := by exact_mod_cast hu.2
  rw [hts, abs_lt]
  constructor
  · rw [neg_lt, lt_div_iff₀ hT]
    nlinarith
  · rw [lt_div_iff₀ hT]; nlinarith

/-- `|I| · 2^SI ∈ [al, ah]` under the `u` decision. -/
theorem abs_box (hts : TS = (tsn : ℝ) / 2 ^ tse) (h1 : (IL : ℝ) ≤ 2 ^ SI * I) (h2 : 2 ^ SI * I ≤ IH)
    (hu : ((tsn : ℤ) * 2 ^ SI ≤ IL * 2 ^ tse ∨ IH * 2 ^ tse ≤ -((tsn : ℤ) * 2 ^ SI))) (htsn : 0 < tsn) :
    (((if 0 < IL then IL.natAbs else IH.natAbs : ℕ)) : ℝ) ≤ 2 ^ SI * |I| ∧
      2 ^ SI * |I| ≤ ((if 0 < IL then IH.natAbs else IL.natAbs : ℕ) : ℝ) ∧
      0 < (if 0 < IL then IL.natAbs else IH.natAbs : ℕ) ∧ (0 ≤ IL ∨ IH < 0) ∧ (IL < 0 ↔ I < 0) := by
  have hS : (0 : ℝ) < 2 ^ SI := by positivity
  have hpos : (0 : ℤ) < (tsn : ℤ) * 2 ^ SI := by positivity
  have hT : (0 : ℤ) < 2 ^ tse := by positivity
  by_cases hL : 0 < IL
  · simp only [hL, if_true]
    have hH : 0 < IH := by
      have : (IL : ℝ) ≤ IH := le_trans h1 h2
      have : IL ≤ IH := by exact_mod_cast this
      omega
    have hI : 0 < I := by
      have : (0 : ℝ) < IL := by exact_mod_cast hL
      nlinarith
    rw [abs_of_pos hI, Nat.cast_natAbs, Nat.cast_natAbs]; push_cast
    rw [abs_of_pos (by exact_mod_cast hL), abs_of_pos (by exact_mod_cast hH)]
    refine ⟨h1, h2, by omega, Or.inl hL.le, ⟨fun h => absurd h (by omega), fun h => absurd h (by linarith)⟩⟩
  · simp only [hL, if_false]
    have hH : IH < 0 := by
      rcases hu with h | h
      · exfalso; have : IL * 2 ^ tse ≤ 0 := by nlinarith
        omega
      · nlinarith
    have hI : I < 0 := by
      have : (IH : ℝ) < 0 := by exact_mod_cast hH
      nlinarith
    rw [abs_of_neg hI, Nat.cast_natAbs, Nat.cast_natAbs]; push_cast
    rw [abs_of_neg (by exact_mod_cast hH), abs_of_nonpos (by exact_mod_cast (not_lt.mp hL))]
    have hIL : IL < 0 := by
      have : (IL : ℝ) ≤ IH := le_trans h1 h2
      have : IL ≤ IH := by exact_mod_cast this
      omega
    refine ⟨by linarith, by linarith, by omega, Or.inr hH, ⟨fun _ => hI, fun _ => hIL⟩⟩

end decisions

/-! ### Arithmetic of the decisions -/

theorem ar_wtt {t D S e ah lo x y : ℝ} (ht : 0 ≤ t) (hD : 0 < D) (hS : 0 < S) (he : 0 < e)
    (hk : t * D * ah ≤ lo * S * e) (a1 : lo ≤ y * D) (ha2 : S * x ≤ ah) (hx : 0 < x) :
    t / e ≤ y / x := by
  rw [div_le_div_iff₀ he hx]
  have c1 : t * D * (S * x) ≤ t * D * ah := mul_le_mul_of_nonneg_left ha2 (by positivity)
  have c2 : lo * S * e ≤ y * D * S * e := by
    have := mul_le_mul_of_nonneg_right a1 (show (0 : ℝ) ≤ S * e by positivity); linarith
  have c3 : (t * x) * (D * S) ≤ (y * e) * (D * S) := by linarith
  exact le_of_mul_le_mul_right c3 (by positivity)

theorem ar_wtf {t D S e al hi x y : ℝ} (ht : 0 ≤ t) (hD : 0 < D) (hS : 0 < S) (he : 0 < e)
    (hk : hi * S * e < t * D * al) (a2 : y * D ≤ hi) (ha1 : al ≤ S * x) (hx : 0 < x) :
    y / x < t / e := by
  rw [div_lt_div_iff₀ hx he]
  have c1 : t * D * al ≤ t * D * (S * x) := mul_le_mul_of_nonneg_left ha1 (by positivity)
  have c2 : y * D * S * e ≤ hi * S * e := by
    have := mul_le_mul_of_nonneg_right a2 (show (0 : ℝ) ≤ S * e by positivity); linarith
  have c3 : (y * e) * (D * S) < (t * x) * (D * S) := by linarith
  exact lt_of_mul_lt_mul_right c3 (by positivity)

theorem ar_sqlo {tl Dn D S ah lo x y : ℝ} (htl : 0 ≤ tl) (hDn : 0 < Dn) (hD : 0 < D) (hS : 0 < S)
    (hk : tl * tl * D * ah ≤ Dn * Dn * lo * S) (a1 : lo ≤ y * D) (ha2 : S * x ≤ ah) (hx : 0 < x) :
    (tl / Dn) ^ 2 ≤ y / x := by
  rw [div_pow, div_le_div_iff₀ (by positivity) hx]
  have c1 : tl ^ 2 * D * (S * x) ≤ tl ^ 2 * D * ah := mul_le_mul_of_nonneg_left ha2 (by positivity)
  have c2 : Dn ^ 2 * lo * S ≤ Dn ^ 2 * (y * D) * S := by
    have := mul_le_mul_of_nonneg_left a1 (show (0 : ℝ) ≤ Dn ^ 2 by positivity)
    nlinarith
  have c3 : (tl ^ 2 * x) * (D * S) ≤ (y * Dn ^ 2) * (D * S) := by nlinarith
  exact le_of_mul_le_mul_right c3 (by positivity)

theorem ar_sqhi {th Dn D S al hi x y : ℝ} (hth : 0 ≤ th) (hDn : 0 < Dn) (hD : 0 < D) (hS : 0 < S)
    (hk : Dn * Dn * hi * S ≤ th * th * D * al) (a2 : y * D ≤ hi) (ha1 : al ≤ S * x) (hx : 0 < x) :
    y / x ≤ (th / Dn) ^ 2 := by
  rw [div_pow, div_le_div_iff₀ hx (by positivity)]
  have c1 : th * th * D * al ≤ th * th * D * (S * x) := mul_le_mul_of_nonneg_left ha1 (by positivity)
  have c2 : Dn ^ 2 * (y * D) * S ≤ Dn ^ 2 * hi * S := by
    have := mul_le_mul_of_nonneg_left a2 (show (0 : ℝ) ≤ Dn ^ 2 by positivity)
    nlinarith
  have c3 : (y * Dn ^ 2) * (D * S) ≤ (th ^ 2 * x) * (D * S) := by nlinarith
  exact le_of_mul_le_mul_right c3 (by positivity)

/-! ### The entry check -/

theorem keepM_iff {I O : ℝ} : keepM I O ↔ (TS ≤ |I| ∧ TS ≤ |O|) ∧ TS ≤ |O / I| := by
  unfold keepM wt2
  constructor
  · rintro ⟨h1, h2⟩; rw [if_pos h1] at h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; rw [if_pos h1]; exact ⟨h1, h2⟩

theorem wtM_keep {I O : ℝ} (hk : keepM I O) :
    wtM I O = if 0 < O / I then √(O / I) else WINV := by
  unfold wtM; rw [if_pos hk]
  have h1 := (keepM_iff.mp hk).1
  unfold wt2; rw [if_pos h1]

theorem TS_pos : (0 : ℝ) < TS := by unfold TS; positivity

/-- **The entry check is sound.** -/
theorem entChk_sound {g : EG} {SO : ℕ} {w : Wing} {qd : QD} {Elo Ehi : List (List ℤ)}
    {vbS : List (ℕ × ℕ)} {P j i : ℕ} {r : Ent} (h : entChk g SO w qd Elo Ehi vbS P j i r = true)
    {gl : Gl} {E : ℕ → ℕ → ℕ → ℝ} {vb oq : V3 → ℝ}
    (hSB : gl.SB = g.SB) (hB : gl.B = g.B) (hSR : gl.SR = g.SR) (hSOm : gl.SOm = g.SOm)
    (hOm : gl.Om = g.OmN) (hOm0 : 0 < g.OmN) (hRN : g.RN = 1360569253) (hn : nelec gl ≠ 0)
    (hts : TS = (g.tsn : ℝ) / 2 ^ g.tse) (htsn : 0 < g.tsn) (hwinv : g.winv = 10 ^ 12)
    (hDen0 : 0 < g.Den) (hE1 : (((Elo.getD (qd.idx.getD j 0) []).getD (qd.idx.getD i 0) 0 : ℤ) : ℝ) / 2 ^ SO ≤
      E qd.iq (qd.idx.getD j 0) (qd.idx.getD i 0))
    (hE2 : E qd.iq (qd.idx.getD j 0) (qd.idx.getD i 0) ≤
      (((Ehi.getD (qd.idx.getD j 0) []).getD (qd.idx.getD i 0) 0 : ℤ) : ℝ) / 2 ^ SO)
    (hw : WingOK gl vb oq g.SF w qd)
    (hrho : RhoDig gl g.bias (gs qd j - gs qd i) (tget g.W g.h P (gs qd j - gs qd i)))
    (hvb : ((vbS.getD j (0, 0)).1 : ℝ) ≤ vb (key qd (gs qd j)) * 2 ^ g.SV ∧
      vb (key qd (gs qd j)) * 2 ^ g.SV ≤ (vbS.getD j (0, 0)).2) :
    EntOK (2 ^ g.SI) g.Den r (IeS gl E vb oq qd j i) (Om2S gl vb qd j i) := by
  have hS : (0 : ℝ) < 2 ^ g.SI := by positivity
  have hT : (0 : ℝ) < 2 ^ g.tse := by positivity
  have hDO : (0 : ℝ) < DO g := Nat.cast_pos.mpr (by unfold DO; exact Nat.mul_pos (by positivity) hOm0)
  obtain ⟨bx1, bx2⟩ := ieBox_spec g SO w qd Elo Ehi j i gl E vb oq hE1 hE2 hw
  obtain ⟨om0, om1⟩ := om2_spec g qd vbS P j i gl vb hSB hB hSR hSOm hOm hOm0 hRN hn hrho hvb
  unfold entChk at h
  dsimp only at h
  generalize ieBox g SO w qd Elo Ehi j i = bx at h bx1 bx2
  generalize om2 g qd vbS P j i = o at h om0 om1
  generalize IeS gl E vb oq qd j i = I at bx1 bx2 ⊢
  generalize Om2S gl vb qd j i = O at om0 om1 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hie1, hie2⟩, hLH⟩, hcl⟩ := h
  -- the `I` box
  have hS1 : (0 : ℝ) < 2 ^ (SO + g.SF) := by positivity
  have hI1 : (r.IL : ℝ) ≤ 2 ^ g.SI * I := by
    have a : (r.IL : ℝ) * 2 ^ (SO + g.SF) ≤ bx.1 * 2 ^ g.SI := by exact_mod_cast hie1
    have : (r.IL : ℝ) * 2 ^ (SO + g.SF) ≤ 2 ^ g.SI * I * 2 ^ (SO + g.SF) := by nlinarith
    exact le_of_mul_le_mul_right this hS1
  have hI2 : 2 ^ g.SI * I ≤ r.IH := by
    have a : bx.2 * 2 ^ g.SI ≤ (r.IH : ℝ) * 2 ^ (SO + g.SF) := by exact_mod_cast hie2
    have : 2 ^ g.SI * I * 2 ^ (SO + g.SF) ≤ (r.IH : ℝ) * 2 ^ (SO + g.SF) := by nlinarith
    exact le_of_mul_le_mul_right this hS1
  -- `|O|` facts
  have hOabs : o.nz = true → (o.lo : ℝ) ≤ |O| * DO g ∧ |O| * DO g ≤ o.hi := fun hz => by
    obtain ⟨a1, a2⟩ := om1 hz
    have hsg0 : 0 ≤ sg o.neg O := by
      have : (0 : ℝ) ≤ sg o.neg O * DO g := le_trans (Nat.cast_nonneg _) a1
      exact nonneg_of_mul_nonneg_left this hDO
    rw [← abs_sg o.neg O, abs_of_nonneg hsg0]; exact ⟨a1, a2⟩
  have k1_spec : (o.nz && Nat.ble (g.tsn * DO g) (o.lo * 2 ^ g.tse)) = true → TS ≤ |O| := fun hk => by
    simp only [Bool.and_eq_true, ble_d, decide_eq_true_eq] at hk
    obtain ⟨a1, -⟩ := hOabs hk.1
    have hk' : (g.tsn : ℝ) * DO g ≤ o.lo * 2 ^ g.tse := by exact_mod_cast hk.2
    rw [hts, div_le_iff₀ hT]
    have b1 : (o.lo : ℝ) * 2 ^ g.tse ≤ |O| * DO g * 2 ^ g.tse := mul_le_mul_of_nonneg_right a1 hT.le
    have b2 : (g.tsn : ℝ) * DO g ≤ (|O| * 2 ^ g.tse) * DO g := by linarith
    exact le_of_mul_le_mul_right b2 hDO
  have k1f_spec : (!o.nz || Nat.blt (o.hi * 2 ^ g.tse) (g.tsn * DO g)) = true → |O| < TS := fun hk => by
    by_cases hz : o.nz = true
    · simp only [hz, Bool.not_true, Bool.false_or, blt_d, decide_eq_true_eq] at hk
      obtain ⟨-, a2⟩ := hOabs hz
      have hk' : (o.hi : ℝ) * 2 ^ g.tse < g.tsn * DO g := by exact_mod_cast hk
      rw [hts, lt_div_iff₀ hT]
      have b1 : |O| * DO g * 2 ^ g.tse ≤ (o.hi : ℝ) * 2 ^ g.tse := mul_le_mul_of_nonneg_right a2 hT.le
      have b2 : (|O| * 2 ^ g.tse) * DO g < (g.tsn : ℝ) * DO g := by linarith
      exact lt_of_mul_lt_mul_right b2 hDO.le
    · have hz' : o.nz = false := by simpa using hz
      rw [om0 hz', abs_zero]; exact TS_pos
  -- the `u` / `uf` decisions
  have hu_spec : decide ((g.tsn : ℤ) * 2 ^ g.SI ≤ r.IL * 2 ^ g.tse ∨ r.IH * 2 ^ g.tse ≤ -((g.tsn : ℤ) * 2 ^ g.SI)) = true →
      TS ≤ |I| ∧ (((if 0 < r.IL then r.IL.natAbs else r.IH.natAbs : ℕ)) : ℝ) ≤ 2 ^ g.SI * |I| ∧
      2 ^ g.SI * |I| ≤ ((if 0 < r.IL then r.IH.natAbs else r.IL.natAbs : ℕ) : ℝ) ∧
      0 < (if 0 < r.IL then r.IL.natAbs else r.IH.natAbs : ℕ) ∧ (0 ≤ r.IL ∨ r.IH < 0) ∧
      (r.IL < 0 ↔ I < 0) := fun hu => by
    rw [decide_eq_true_eq] at hu
    exact ⟨thr_u hts hI1 hI2 hu, abs_box hts hI1 hI2 hu htsn⟩
  have huf_spec : decide (-((g.tsn : ℤ) * 2 ^ g.SI) < r.IL * 2 ^ g.tse ∧ r.IH * 2 ^ g.tse < (g.tsn : ℤ) * 2 ^ g.SI) = true →
      |I| < TS := fun hu => by
    rw [decide_eq_true_eq] at hu; exact thr_uf hts hI1 hI2 hu
  set al := (if 0 < r.IL then r.IL.natAbs else r.IH.natAbs : ℕ) with hal
  set ah := (if 0 < r.IL then r.IH.natAbs else r.IL.natAbs : ℕ) with hah
  -- `|wt2|` decisions (under `u` and `nz`)
  have wtt_spec : TS ≤ |I| → (al : ℝ) ≤ 2 ^ g.SI * |I| → 2 ^ g.SI * |I| ≤ ah → o.nz = true →
      Nat.ble (g.tsn * DO g * ah) (o.lo * 2 ^ g.SI * 2 ^ g.tse) = true → TS ≤ |O / I| := by
    intro hTI ha1 ha2 hz hk
    have hk' : (g.tsn : ℝ) * DO g * ah ≤ o.lo * 2 ^ g.SI * 2 ^ g.tse := by exact_mod_cast bt (ble_d _ _) hk
    rw [abs_div, hts]
    exact ar_wtt (Nat.cast_nonneg _) hDO hS hT hk' (hOabs hz).1 ha2 (lt_of_lt_of_le TS_pos hTI)
  have wtf_spec : TS ≤ |I| → (al : ℝ) ≤ 2 ^ g.SI * |I| → o.nz = true →
      Nat.blt (o.hi * 2 ^ g.SI * 2 ^ g.tse) (g.tsn * DO g * al) = true → |O / I| < TS := by
    intro hTI ha1 hz hk
    have hk' : (o.hi : ℝ) * 2 ^ g.SI * 2 ^ g.tse < g.tsn * DO g * al := by exact_mod_cast bt (blt_d _ _) hk
    rw [abs_div, hts]
    exact ar_wtf (Nat.cast_nonneg _) hDO hS hT hk' (hOabs hz).2 ha1 (lt_of_lt_of_le TS_pos hTI)
  -- the sign of `O`
  have hOsgn : o.nz = true → TS ≤ |O| → (o.neg = true ↔ O < 0) := fun hz hTO => by
    obtain ⟨a1, -⟩ := om1 hz
    have hDO' := hDO
    have hsg0 : 0 ≤ sg o.neg O := nonneg_of_mul_nonneg_left (le_trans (Nat.cast_nonneg _) a1) hDO
    have hO0 : O ≠ 0 := fun h0 => by rw [h0, abs_zero] at hTO; exact absurd hTO (not_le.mpr TS_pos)
    cases hn' : o.neg
    · rw [hn', sg_false] at hsg0
      simp only [Bool.false_eq_true, false_iff, not_lt]; exact hsg0
    · rw [hn', sg_true] at hsg0
      simp only [true_iff]; exact lt_of_le_of_ne (by linarith) hO0
  -- assemble by class
  have hDen' : (0 : ℝ) < g.Den := by exact_mod_cast hDen0
  by_cases c0 : r.cls = 0
  · simp only [c0, if_true] at hcl
    have hlt := huf_spec hcl
    have hnot : ¬ TS ≤ |I| := not_le.mpr hlt
    refine ⟨fun _ => ⟨by unfold IeU; rw [if_neg hnot], fun hk => hnot (keepM_iff.mp hk).1.1⟩,
      fun h1 => absurd h1 (by omega), fun h1 => absurd h1 (by omega), fun h1 => absurd h1 (by omega),
      fun _ => hlt, fun h1 => absurd h1 (by omega)⟩
  simp only [c0, if_false] at hcl
  by_cases c1 : r.cls = 1
  · simp only [c1, if_true, Bool.and_eq_true] at hcl
    obtain ⟨hTI, ha1, ha2, ha0, hsgn, hIneg⟩ := hu_spec hcl.1
    have hnk : ¬keepM I O := by
      intro hk
      rcases (Bool.or_eq_true _ _).mp hcl.2 with hk1 | hw
      · exact absurd (keepM_iff.mp hk).1.2 (not_le.mpr (k1f_spec hk1))
      · by_cases hz : o.nz = true
        · exact absurd (keepM_iff.mp hk).2 (not_le.mpr (wtf_spec hTI ha1 hz hw))
        · have hz' : o.nz = false := by simpa using hz
          exact absurd (keepM_iff.mp hk).1.2 (not_le.mpr (k1f_spec (by simp [hz'])))
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨by unfold IeU; rw [if_pos hTI], hI1, hI2⟩,
      fun _ => hnk, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => hTI⟩
  simp only [c1, if_false] at hcl
  by_cases c2 : r.cls = 2
  · simp only [c2, if_true, Bool.and_eq_true] at hcl
    obtain ⟨⟨⟨⟨⟨⟨hu, hk1⟩, hwt⟩, hsq⟩, htl⟩, hlo⟩, hhi⟩ := hcl
    obtain ⟨hTI, ha1, ha2, ha0, hsgn, hIneg⟩ := hu_spec hu
    have hz : o.nz = true := hk1.1
    have hTO := k1_spec (by rw [Bool.and_eq_true]; exact hk1)
    have hTW := wtt_spec hTI ha1 ha2 hz hwt
    have hk : keepM I O := keepM_iff.mpr ⟨⟨hTI, hTO⟩, hTW⟩
    have hpos : 0 < O / I := by
      have hs := (hOsgn hz hTO)
      simp only [beq_iff_eq] at hsq
      have hsq' : (o.neg = true ↔ r.IL < 0) := by rw [hsq]; simp
      have hIO : (O < 0 ↔ I < 0) := by rw [← hs, hsq', hIneg]
      have hI0 : I ≠ 0 := fun h0 => by rw [h0, abs_zero] at hTI; exact absurd hTI (not_le.mpr TS_pos)
      have hO0 : O ≠ 0 := fun h0 => by rw [h0, abs_zero] at hTO; exact absurd hTO (not_le.mpr TS_pos)
      rcases lt_or_gt_of_ne hI0 with hI | hI
      · exact div_pos_of_neg_of_neg (hIO.mpr hI) hI
      · have : 0 < O := lt_of_le_of_ne (not_lt.mp (fun h => absurd (hIO.mp h) (not_lt.mpr hI.le))) hO0.symm
        exact div_pos this hI
    have hwt' : wtM I O = √(O / I) := by rw [wtM_keep hk, if_pos hpos]
    have hOI : O / I = |O| / |I| := by rw [← abs_div, abs_of_pos hpos]
    have htl' : 0 < r.tl := by simpa [blt_d] using htl
    have hlo' : (r.tl : ℝ) * r.tl * DO g * ah ≤ (g.Den : ℝ) * g.Den * o.lo * 2 ^ g.SI := by
      exact_mod_cast bt (ble_d _ _) hlo
    have hhi' : (g.Den : ℝ) * g.Den * o.hi * 2 ^ g.SI ≤ (r.th : ℝ) * r.th * DO g * al := by
      exact_mod_cast bt (ble_d _ _) hhi
    obtain ⟨a1, a2⟩ := hOabs hz
    have hIp : 0 < |I| := lt_of_lt_of_le TS_pos hTI
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨by unfold IeU; rw [if_pos hTI], hI1, hI2⟩,
      fun h => absurd h (by omega), fun _ => ⟨hk, htl', ?_, ?_, hsgn⟩, fun h => absurd h (by omega),
      fun _ => hTI⟩
    · -- tl ≤ √(O/I) Den
      rw [hwt']
      have hsq2 : ((r.tl : ℝ) / g.Den) ^ 2 ≤ O / I := by
        rw [hOI]
        exact ar_sqlo (Nat.cast_nonneg _) hDen' hDO hS hlo' a1 ha2 hIp
      have := Real.le_sqrt_of_sq_le hsq2
      rw [div_le_iff₀ hDen'] at this; exact this
    · rw [hwt']
      have hsq3 : O / I ≤ ((r.th : ℝ) / g.Den) ^ 2 := by
        rw [hOI]
        exact ar_sqhi (Nat.cast_nonneg _) hDen' hDO hS hhi' a2 ha1 hIp
      have hth0 : (0 : ℝ) ≤ r.th / g.Den := by positivity
      have := Real.sqrt_le_sqrt hsq3
      rw [Real.sqrt_sq hth0, le_div_iff₀ hDen'] at this; exact this
  simp only [c2, if_false] at hcl
  by_cases c3 : r.cls = 3
  · simp only [c3, if_true, Bool.and_eq_true] at hcl
    obtain ⟨⟨⟨⟨⟨⟨hu, hk1⟩, hwt⟩, hsq⟩, htl⟩, hlo⟩, hhi⟩ := hcl
    obtain ⟨hTI, ha1, ha2, ha0, hsgn, hIneg⟩ := hu_spec hu
    have hz : o.nz = true := hk1.1
    have hTO := k1_spec (by rw [Bool.and_eq_true]; exact hk1)
    have hTW := wtt_spec hTI ha1 ha2 hz hwt
    have hk : keepM I O := keepM_iff.mpr ⟨⟨hTI, hTO⟩, hTW⟩
    have hneg : ¬ 0 < O / I := by
      have hs := (hOsgn hz hTO)
      have hsq' : ¬(o.neg = decide (r.IL < 0)) := by simpa using hsq
      have hIO : ¬(O < 0 ↔ I < 0) := by
        intro hh; apply hsq'; rw [Bool.eq_iff_iff, hs, hh, decide_eq_true_iff, hIneg]
      intro hp
      rcases lt_or_gt_of_ne (show I ≠ 0 from fun h0 => by rw [h0, abs_zero] at hTI; exact absurd hTI (not_le.mpr TS_pos)) with hI | hI
      · have : O < 0 := by
          by_contra hO; push_neg at hO
          have := div_nonpos_of_nonneg_of_nonpos hO hI.le; linarith
        exact hIO ⟨fun _ => hI, fun _ => this⟩
      · have : 0 < O := by
          by_contra hO; push_neg at hO
          have := div_nonpos_of_nonpos_of_nonneg hO hI.le; linarith
        exact hIO ⟨fun h => absurd h (not_lt.mpr this.le), fun h => absurd h (not_lt.mpr hI.le)⟩
    have hwt' : wtM I O = WINV := by rw [wtM_keep hk, if_neg hneg]
    have htl' : 0 < r.tl := by simpa [blt_d] using htl
    have hlo' : (r.tl : ℝ) ≤ g.winv * g.Den := by exact_mod_cast bt (ble_d _ _) hlo
    have hhi' : (g.winv : ℝ) * g.Den ≤ r.th := by exact_mod_cast bt (ble_d _ _) hhi
    rw [hwinv] at hlo' hhi'
    have hW : WINV = ((10 ^ 12 : ℕ) : ℝ) := by unfold WINV; push_cast; ring
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨by unfold IeU; rw [if_pos hTI], hI1, hI2⟩,
      fun h => absurd h (by omega), fun _ => ⟨hk, htl', ?_, ?_, hsgn⟩, fun h => absurd h (by omega),
      fun _ => hTI⟩
    · rw [hwt', hW]; exact hlo'
    · rw [hwt', hW]; exact hhi'
  · simp only [c3, if_false] at hcl
    exact absurd hcl (by simp)

end GW.Endpoint.Kernel.Sig

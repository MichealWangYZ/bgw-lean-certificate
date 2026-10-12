/-
G2 stage 3, soundness (1/4): the GPP kernel checkers `schK`, `ssxK` of
`SigmaCheck.lean` enclose the real kernel values `schM`, `ssxM` of `SigmaSpec.lean`.

All quantities are scaled: an energy `x` (eV) is `x' = x · Den`, `wtilde` is
`w' = w · Den`, `I_eps` is `I · 2^SI`; the kernel values are then scale-free ratios,
e.g. `sch = w I / (x - w) = w' I / (x' - w')`.
-/
import GW.Endpoint.Kernel.SigmaCheck
import GW.Endpoint.Kernel.EpsSound

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### Signs and floor division -/

/-- `(-1)^b v`. -/
def sg (b : Bool) (v : ℝ) : ℝ := if b then -v else v

@[simp] theorem sg_false (v : ℝ) : sg false v = v := rfl
@[simp] theorem sg_true (v : ℝ) : sg true v = -v := rfl

theorem sg_sg (b : Bool) (v : ℝ) : sg b (sg b v) = v := by cases b <;> simp

theorem sg_xor (a b : Bool) (v : ℝ) : sg (xor a b) v = sg a (sg b v) := by
  cases a <;> cases b <;> simp

theorem sg_mul (b : Bool) (u v : ℝ) : sg b (u * v) = u * sg b v := by cases b <;> simp

theorem sg_div (b : Bool) (u v : ℝ) : sg b (u / v) = sg b u / v := by cases b <;> simp [neg_div]

theorem sg_zero (b : Bool) : sg b 0 = 0 := by cases b <;> simp

theorem ndiv_le (a d : ℕ) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := Nat.cast_div_le

theorem lt_ndiv_succ (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
  have hpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hpos]
  have h : ((a : ℕ) : ℝ) < ((d * (a / d + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.lt_mul_div_succ a hd
  push_cast at h; linarith

/-- Quotient bounds from bounds of numerator and denominator, with the floor divisions
of the checker: `⌊al / dh⌋ ≤ A / D ≤ ⌊ah / dl⌋ + 1`. -/
theorem qbounds {al ah dl dh : ℕ} {A D : ℝ} (h1 : (al : ℝ) ≤ A) (h2 : A ≤ ah) (hdl : 0 < dl)
    (h3 : (dl : ℝ) ≤ D) (h4 : D ≤ dh) :
    ((al / dh : ℕ) : ℝ) ≤ A / D ∧ A / D ≤ ((ah / dl : ℕ) : ℝ) + 1 := by
  have hdl' : (0 : ℝ) < dl := by exact_mod_cast hdl
  have hD : 0 < D := lt_of_lt_of_le hdl' h3
  have hdh : (0 : ℝ) < dh := lt_of_lt_of_le hD h4
  have hdh' : 0 < dh := by exact_mod_cast hdh
  have hA : (0 : ℝ) ≤ A := le_trans (Nat.cast_nonneg _) h1
  constructor
  · calc ((al / dh : ℕ) : ℝ) ≤ (al : ℝ) / dh := ndiv_le _ _
      _ ≤ A / dh := div_le_div_of_nonneg_right h1 hdh.le
      _ ≤ A / D := div_le_div_of_nonneg_left hA hD h4
  · calc A / D ≤ (ah : ℝ) / D := div_le_div_of_nonneg_right h2 hD.le
      _ ≤ (ah : ℝ) / dl := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdl' h3
      _ ≤ ((ah / dl : ℕ) : ℝ) + 1 := (lt_ndiv_succ _ _ hdl).le

/-! ### `x - t`, `x + t`, `x² - t²` -/

/-- The semantics of an `ok` signed-magnitude enclosure of `y`: `lo ≤ (-1)^neg y ≤ hi`. -/
def SMs (r : SM) (y : ℝ) : Prop := (r.lo : ℝ) ≤ sg r.neg y ∧ sg r.neg y ≤ r.hi

theorem blt_d (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])

theorem ble_d (a b : ℕ) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

theorem beq_d (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

theorem subT_spec {sx : Bool} {X tl th : ℕ} {w : ℝ} (htl : 0 < tl) (hw1 : (tl : ℝ) ≤ w)
    (hw2 : w ≤ th) (h : (subT sx X tl th).ok = true) :
    0 < (subT sx X tl th).lo ∧ SMs (subT sx X tl th) (sg sx X - w) := by
  have hth : tl ≤ th := by exact_mod_cast le_trans hw1 hw2
  unfold subT SMs at *
  cases sx
  · simp only [Bool.false_eq_true, cond_false, blt_d, Bool.cond_decide] at h ⊢
    by_cases h1 : th < X
    · simp only [h1, if_true] at h ⊢
      have h1' : tl ≤ X := by omega
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_false] <;>
        push_cast [Nat.cast_sub h1.le, Nat.cast_sub h1'] <;> linarith
    · simp only [h1, if_false] at h ⊢
      by_cases h2 : X < tl
      · simp only [h2, if_true] at h ⊢
        refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_true, sg_false] <;>
          push_cast [Nat.cast_sub h2.le, Nat.cast_sub (le_trans h2.le hth)] <;> linarith
      · simp [h2, smFail] at h
  · simp only [cond_true] at h ⊢
    refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_true] <;> push_cast <;> linarith

theorem abs_sg (b : Bool) (v : ℝ) : |sg b v| = |v| := by cases b <;> simp

theorem SMs_abs {r : SM} {y : ℝ} (h : SMs r y) : (r.lo : ℝ) ≤ |y| ∧ |y| ≤ r.hi := by
  have hpos : (0 : ℝ) ≤ sg r.neg y := le_trans (Nat.cast_nonneg _) h.1
  rw [← abs_sg r.neg y, abs_of_nonneg hpos]; exact h

/-- `subT` also bounds `|x - t|`. -/
theorem subT_abs {sx : Bool} {X tl th : ℕ} {w : ℝ} (htl : 0 < tl) (hw1 : (tl : ℝ) ≤ w)
    (hw2 : w ≤ th) (h : (subT sx X tl th).ok = true) :
    ((subT sx X tl th).lo : ℝ) ≤ |sg sx X - w| ∧ |sg sx X - w| ≤ (subT sx X tl th).hi :=
  SMs_abs (subT_spec htl hw1 hw2 h).2

theorem addT_spec {sx : Bool} {X tl th : ℕ} {w : ℝ} (htl : 0 < tl) (hw1 : (tl : ℝ) ≤ w)
    (hw2 : w ≤ th) :
    ((addT sx X tl th).lo : ℝ) ≤ |sg sx X + w| ∧ |sg sx X + w| ≤ (addT sx X tl th).hi ∧
      ((addT sx X tl th).ok = true → 0 < (addT sx X tl th).lo ∧ SMs (addT sx X tl th) (sg sx X + w)) := by
  have hth : tl ≤ th := by exact_mod_cast le_trans hw1 hw2
  have htl' : (0 : ℝ) < tl := by exact_mod_cast htl
  unfold addT SMs
  cases sx
  · simp only [Bool.not_false, cond_true, sg_false]
    have : 0 ≤ (X : ℝ) + w := by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _
                                 linarith
    rw [abs_of_nonneg this]; push_cast
    refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by simp; linarith, by simp; linarith⟩⟩
  · simp only [Bool.not_true, cond_false, blt_d, Bool.cond_decide, sg_true]
    by_cases h1 : X < tl
    · simp only [h1, if_true]
      have : 0 ≤ -(X : ℝ) + w := by have : (X : ℝ) < tl := by exact_mod_cast h1
                                    linarith
      rw [abs_of_nonneg this]
      push_cast [Nat.cast_sub h1.le, Nat.cast_sub (le_trans h1.le hth)]
      refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by simp; linarith, by simp; linarith⟩⟩
    · simp only [h1, if_false]
      by_cases h2 : th < X
      · simp only [h2, if_true]
        have : -(X : ℝ) + w ≤ 0 := by have : (th : ℝ) < X := by exact_mod_cast h2
                                      linarith
        rw [abs_of_nonpos this]
        have h1' : tl ≤ X := by omega
        push_cast [Nat.cast_sub h2.le, Nat.cast_sub h1']
        refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by simp; linarith, by simp; linarith⟩⟩
      · simp only [h2, if_false]
        have h1' : tl ≤ X := by omega
        have h2' : X ≤ th := by omega
        refine ⟨by simp, ?_, fun h => by simp at h⟩
        have e : (((max (th - X) (X - tl) : ℕ)) : ℝ) = max ((th : ℝ) - X) ((X : ℝ) - tl) := by
          push_cast [Nat.cast_sub h1', Nat.cast_sub h2']; rfl
        rw [e, abs_le]
        constructor
        · have := le_max_right ((th : ℝ) - X) ((X : ℝ) - tl); linarith
        · have := le_max_left ((th : ℝ) - X) ((X : ℝ) - tl); linarith

theorem sq2_spec {X2 tl2 th2 : ℕ} {W : ℝ} (hw1 : (tl2 : ℝ) ≤ W) (hw2 : W ≤ th2) :
    ((sq2 X2 tl2 th2).lo : ℝ) ≤ |(X2 : ℝ) - W| ∧ |(X2 : ℝ) - W| ≤ (sq2 X2 tl2 th2).hi ∧
      ((sq2 X2 tl2 th2).ok = true → 0 < (sq2 X2 tl2 th2).lo ∧ SMs (sq2 X2 tl2 th2) ((X2 : ℝ) - W)) := by
  have hth : tl2 ≤ th2 := by exact_mod_cast le_trans hw1 hw2
  unfold sq2 SMs
  simp only [blt_d, Bool.cond_decide]
  by_cases h1 : th2 < X2
  · simp only [h1, if_true, sg_false]
    have : 0 ≤ (X2 : ℝ) - W := by have : (th2 : ℝ) < X2 := by exact_mod_cast h1
                                  linarith
    rw [abs_of_nonneg this]
    have h1' : tl2 ≤ X2 := by omega
    push_cast [Nat.cast_sub h1.le, Nat.cast_sub h1']
    refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by linarith, by linarith⟩⟩
  · simp only [h1, if_false]
    by_cases h2 : X2 < tl2
    · simp only [h2, if_true, sg_true]
      have : (X2 : ℝ) - W ≤ 0 := by have : (X2 : ℝ) < tl2 := by exact_mod_cast h2
                                    linarith
      rw [abs_of_nonpos this]
      push_cast [Nat.cast_sub h2.le, Nat.cast_sub (le_trans h2.le hth)]
      refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by linarith, by linarith⟩⟩
    · simp only [h2, if_false]
      have h1' : tl2 ≤ X2 := by omega
      have h2' : X2 ≤ th2 := by omega
      refine ⟨by simp, ?_, fun h => by simp at h⟩
      have e : (((max (th2 - X2) (X2 - tl2) : ℕ)) : ℝ) = max ((th2 : ℝ) - X2) ((X2 : ℝ) - tl2) := by
        push_cast [Nat.cast_sub h1', Nat.cast_sub h2']; rfl
      rw [e, abs_le]
      constructor
      · have := le_max_left ((th2 : ℝ) - X2) ((X2 : ℝ) - tl2); linarith
      · have := le_max_right ((th2 : ℝ) - X2) ((X2 : ℝ) - tl2); linarith

/-! ### The generic-branch test -/

theorem genT_eq (kc : KC) (dl dh tl2 th2 : ℕ) : genT kc dl dh tl2 th2 =
    if kc.Den2 < 4 * (dl * dl) ∧ th2 < dl * dl * kc.lim1 then (true, true)
    else if 4 * (dh * dh) ≤ kc.Den2 ∨ dh * dh * kc.lim1 ≤ tl2 then (true, false) else (false, false) := by
  unfold genT
  simp only [blt_d, ble_d, ← Bool.decide_and, ← Bool.decide_or, Bool.cond_decide]

/-- `genT` decides the generic condition `(x - w)² > 1/4 ∧ w² < (x - w)² LIM1` over the
box, in scaled form `d = (x - w) Den`, `w' = w Den`. -/
theorem genT_spec {Den : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) {dl dh tl2 th2 : ℕ} {x w : ℝ}
    (hd1 : (dl : ℝ) ≤ |(x - w) * Den|) (hd2 : |(x - w) * Den| ≤ dh)
    (hw1 : (tl2 : ℝ) ≤ (w * Den) ^ 2) (hw2 : (w * Den) ^ 2 ≤ th2) :
    ((genT kc dl dh tl2 th2).1 = true → (genT kc dl dh tl2 th2).2 = true →
      (x - w) ^ 2 > GAM2 ∧ w ^ 2 < (x - w) ^ 2 * LIM1) ∧
    ((genT kc dl dh tl2 th2).1 = true → (genT kc dl dh tl2 th2).2 = false →
      ¬((x - w) ^ 2 > GAM2 ∧ w ^ 2 < (x - w) ^ 2 * LIM1)) := by
  have hsq : ((x - w) * Den) ^ 2 = (x - w) ^ 2 * Den ^ 2 := by ring
  have hwsq : (w * Den) ^ 2 = w ^ 2 * Den ^ 2 := by ring
  have hD2 : 0 < Den ^ 2 := by positivity
  have hdl0 : (0 : ℝ) ≤ dl := Nat.cast_nonneg _
  have e1 : (dl : ℝ) ^ 2 ≤ (x - w) ^ 2 * Den ^ 2 := by
    have := pow_le_pow_left₀ hdl0 hd1 2; rwa [sq_abs, hsq] at this
  have e2 : (x - w) ^ 2 * Den ^ 2 ≤ (dh : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hd2 2; rwa [sq_abs, hsq] at this
  rw [hwsq] at hw1 hw2
  rw [genT_eq]
  unfold GAM2 LIM1
  by_cases hA : kc.Den2 < 4 * (dl * dl) ∧ th2 < dl * dl * kc.lim1
  · simp only [hA, and_self, if_true]
    refine ⟨fun _ _ => ?_, fun _ h => absurd h (by simp)⟩
    obtain ⟨a1, a2⟩ := hA
    have a1' : (kc.Den2 : ℝ) < 4 * (dl * dl) := by exact_mod_cast a1
    have a2' : (th2 : ℝ) < dl * dl * kc.lim1 := by exact_mod_cast a2
    rw [hk2] at a1'; rw [hl] at a2'; push_cast at a2'
    constructor
    · have : Den ^ 2 * 1 < Den ^ 2 * (4 * (x - w) ^ 2) := by nlinarith
      have := lt_of_mul_lt_mul_left this hD2.le
      show (1 : ℝ) / 4 < (x - w) ^ 2; linarith
    · have : w ^ 2 * Den ^ 2 < (x - w) ^ 2 * 250000 * Den ^ 2 := by nlinarith
      exact lt_of_mul_lt_mul_right this hD2.le
  · simp only [hA, if_false]
    by_cases hB : 4 * (dh * dh) ≤ kc.Den2 ∨ dh * dh * kc.lim1 ≤ tl2
    · simp only [hB, if_true]
      refine ⟨fun _ h => absurd h (by simp), fun _ _ => ?_⟩
      rintro ⟨c1, c2⟩
      rcases hB with b | b
      · have b' : 4 * ((dh : ℝ) * dh) ≤ kc.Den2 := by exact_mod_cast b
        rw [hk2] at b'
        have c1' : (1 : ℝ) / 4 < (x - w) ^ 2 := c1
        nlinarith
      · have b' : (dh : ℝ) * dh * kc.lim1 ≤ tl2 := by exact_mod_cast b
        rw [hl] at b'; push_cast at b'
        have : (x - w) ^ 2 * 250000 * Den ^ 2 ≤ w ^ 2 * Den ^ 2 := by nlinarith
        nlinarith
    · simp only [hB, if_false]; simp

/-! ### The kernel values -/

/-- The scaled data of one kept mode: `w' = w Den ∈ [tl, th]`, `tl > 0`, `t2 = t²`, and
`I` (scaled) with `(-1)^sI I ∈ [al, ah]`. -/
structure EDok (e : ED) (Den w I : ℝ) : Prop where
  tl_pos : 0 < e.tl
  w_lo : (e.tl : ℝ) ≤ w * Den
  w_hi : w * Den ≤ e.th
  tl2 : e.tl2 = e.tl * e.tl
  th2 : e.th2 = e.th * e.th
  I_lo : (e.al : ℝ) ≤ sg e.sI I
  I_hi : sg e.sI I ≤ e.ah

/-- One energy: `x Den = (-1)^sx X`, `X2 = X²`, and `sx → X > 0`. -/
structure Enok (x : En) (Den xr : ℝ) : Prop where
  val : xr * Den = sg x.sx x.X
  sq : x.X2 = x.X * x.X
  neg : x.sx = true → 0 < x.X

theorem EDok.w_nonneg {e : ED} {Den w I : ℝ} (h : EDok e Den w I) : 0 ≤ w * Den :=
  le_trans (Nat.cast_nonneg _) h.w_lo

theorem EDok.wsq {e : ED} {Den w I : ℝ} (h : EDok e Den w I) :
    (e.tl2 : ℝ) ≤ (w * Den) ^ 2 ∧ (w * Den) ^ 2 ≤ e.th2 := by
  rw [h.tl2, h.th2]; push_cast
  exact ⟨by nlinarith [h.w_lo, h.w_nonneg], by nlinarith [h.w_hi, h.w_nonneg]⟩

theorem sg_div' (b : Bool) (u v : ℝ) : sg b (u / v) = u / sg b v := by cases b <;> simp [div_neg]

/-- The magnitude of `t I / d` from the boxes of `t`, `(-1)^sI I` and `(-1)^dn d`. -/
theorem quot_SM {tl th al ah dl dh : ℕ} {sI dn : Bool} {t I d : ℝ}
    (ht1 : (tl : ℝ) ≤ t) (ht2 : t ≤ th) (hI1 : (al : ℝ) ≤ sg sI I) (hI2 : sg sI I ≤ ah)
    (hdl : 0 < dl) (hd1 : (dl : ℝ) ≤ sg dn d) (hd2 : sg dn d ≤ dh) :
    ((tl * al / dh : ℕ) : ℝ) ≤ sg (xor sI dn) (t * I / d) ∧
      sg (xor sI dn) (t * I / d) ≤ ((th * ah / dl : ℕ) : ℝ) + 1 := by
  have e : sg (xor sI dn) (t * I / d) = (t * sg sI I) / sg dn d := by
    cases sI <;> cases dn <;> simp [div_neg, neg_div, mul_neg]
  rw [e]
  have h0 : (0 : ℝ) ≤ tl := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ al := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := le_trans h0 ht1
  have hI0 : 0 ≤ sg sI I := le_trans h0' hI1
  exact qbounds (by push_cast; exact mul_le_mul ht1 hI1 h0' ht0)
    (by push_cast; exact mul_le_mul ht2 hI2 hI0 (le_trans ht0 ht2)) hdl hd1 hd2

/-- The generic condition of the source. -/
def Gen (x w : ℝ) : Prop := (x - w) ^ 2 > GAM2 ∧ w ^ 2 < (x - w) ^ 2 * LIM1

noncomputable instance (x w : ℝ) : Decidable (Gen x w) := Classical.dec _

/-- **`schK` encloses the CH kernel** `[generic] w I / (x - w)` of a kept mode (scaled `I`). -/
theorem schK_spec {Den : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) {e : ED} {x : En} {xr w I : ℝ} (he : EDok e Den w I)
    (hx : Enok x Den xr) (hok : (schK kc e x).ok = true) :
    SMs (schK kc e x) (if Gen xr w then w * I / (xr - w) else 0) := by
  have hd' : sg x.sx x.X - w * Den = (xr - w) * Den := by rw [← hx.val]; ring
  unfold schK at hok ⊢
  cases hdo : (subT x.sx x.X e.tl e.th).ok
  · simp [hdo, smFail] at hok
  simp only [hdo, cond_true] at hok ⊢
  obtain ⟨hlo, hsm⟩ := subT_spec he.tl_pos he.w_lo he.w_hi hdo
  have habs := subT_abs he.tl_pos he.w_lo he.w_hi hdo
  rw [hd'] at hsm habs
  obtain ⟨g1, g2⟩ := genT_spec hD hk2 hl habs.1 habs.2 he.wsq.1 he.wsq.2
  cases hg1 : (genT kc (subT x.sx x.X e.tl e.th).lo (subT x.sx x.X e.tl e.th).hi e.tl2 e.th2).1
  · simp [hg1, smFail] at hok
  simp only [hg1, cond_true] at hok ⊢
  cases hg2 : (genT kc (subT x.sx x.X e.tl e.th).lo (subT x.sx x.X e.tl e.th).hi e.tl2 e.th2).2
  · have hG := g2 hg1 hg2
    simp only [hg2, cond_false, Gen, hG, if_false, SMs, smZero, sg_zero]; simp
  · have hG := g1 hg1 hg2
    simp only [hg2, cond_true, Gen, hG, and_self, if_true, SMs]
    have ev : w * I / (xr - w) = (w * Den) * I / ((xr - w) * Den) := by
      have : Den ≠ 0 := hD.ne'
      rw [mul_comm (xr - w) Den, mul_comm w Den, mul_assoc, mul_div_mul_left _ _ this]
    rw [ev]
    simp only [Nat.cast_add, Nat.cast_one]
    exact quot_SM he.w_lo he.w_hi he.I_lo he.I_hi hlo hsm.1 hsm.2

/-- The source's SX kernel of a kept mode, with `I` scaled. -/
noncomputable def ssxV (I w x : ℝ) : ℝ := GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w x

theorem shr_le_iff (A e b : ℕ) : b ≤ A >>> e ↔ b * 2 ^ e ≤ A := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.le_div_iff_mul_le (by positivity)

theorem shr_lt_iff (A e b : ℕ) : A >>> e < b ↔ A < b * 2 ^ e := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_iff_lt_mul (by positivity)

theorem bt {b : Bool} {p : Prop} [Decidable p] (hb : b = decide p) (h : b = true) : p := by
  subst hb; simpa using h

theorem bf {b : Bool} {p : Prop} [Decidable p] (hb : b = decide p) (h : b = false) : ¬p := by
  subst hb; simpa using h

theorem sq_bounds {lo hi : ℕ} {y : ℝ} (h1 : (lo : ℝ) ≤ |y|) (h2 : |y| ≤ hi) :
    (lo : ℝ) ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ (hi : ℝ) ^ 2 := by
  constructor
  · have := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2; rwa [sq_abs] at this
  · have := pow_le_pow_left₀ (abs_nonneg _) h2 2; rwa [sq_abs] at this

/-- Common facts of an energy. -/
theorem Enok.xneg {x : En} {Den xr : ℝ} (hD : 0 < Den) (hx : Enok x Den xr) :
    x.sx = true → xr < 0 := fun h => by
  have := hx.val; rw [h, sg_true] at this
  have hX : (0 : ℝ) < x.X := by exact_mod_cast hx.neg h
  nlinarith

theorem Enok.xpos {x : En} {Den xr : ℝ} (hD : 0 < Den) (hx : Enok x Den xr) :
    x.sx = false → 0 ≤ xr := fun h => by
  have := hx.val; rw [h, sg_false] at this
  have : 0 ≤ xr * Den := by rw [this]; exact Nat.cast_nonneg _
  nlinarith

/-- The generic SX value with its `sexcut` clamp. -/
theorem ssx_gen {Den : ℝ} (hD : 0 < Den) {e : ED} {x : En} {xr w I : ℝ} (he : EDok e Den w I)
    (hx : Enok x Den xr)
    (hok : (bif x.sx && Nat.blt (4 * (sq2 x.X2 e.tl2 e.th2).hi) e.tl2 then smZero
      else bif (sq2 x.X2 e.tl2 e.th2).ok && (!x.sx || Nat.ble e.th2 (4 * (sq2 x.X2 e.tl2 e.th2).lo)) then
        (⟨true, xor e.sI (sq2 x.X2 e.tl2 e.th2).neg, e.tl2 * e.al / (sq2 x.X2 e.tl2 e.th2).hi,
          e.th2 * e.ah / (sq2 x.X2 e.tl2 e.th2).lo + 1⟩ : SM)
      else smFail).ok = true) :
    SMs (bif x.sx && Nat.blt (4 * (sq2 x.X2 e.tl2 e.th2).hi) e.tl2 then smZero
      else bif (sq2 x.X2 e.tl2 e.th2).ok && (!x.sx || Nat.ble e.th2 (4 * (sq2 x.X2 e.tl2 e.th2).lo)) then
        (⟨true, xor e.sI (sq2 x.X2 e.tl2 e.th2).neg, e.tl2 * e.al / (sq2 x.X2 e.tl2 e.th2).hi,
          e.th2 * e.ah / (sq2 x.X2 e.tl2 e.th2).lo + 1⟩ : SM)
      else smFail)
      (if |xr ^ 2 - w ^ 2| < w ^ 2 * (1 / SEXC) ∧ xr < 0 then 0 else w ^ 2 * I / (xr ^ 2 - w ^ 2)) := by
  have hD2 : 0 < Den ^ 2 := by positivity
  have e3 : (w * Den) ^ 2 = w ^ 2 * Den ^ 2 := by ring
  have hwsq := he.wsq
  rw [e3] at hwsq
  obtain ⟨qa1, qa2, qa3⟩ := sq2_spec (X2 := x.X2) he.wsq.1 he.wsq.2
  have hq' : (x.X2 : ℝ) - (w * Den) ^ 2 = (xr ^ 2 - w ^ 2) * Den ^ 2 := by
    rw [hx.sq]; push_cast
    have : (x.X : ℝ) * x.X = (xr * Den) ^ 2 := by
      rw [hx.val]; cases x.sx <;> simp <;> ring
    rw [this]; ring
  rw [hq'] at qa1 qa2 qa3
  have hab : |xr ^ 2 - w ^ 2| * Den ^ 2 = |(xr ^ 2 - w ^ 2) * Den ^ 2| := by
    rw [abs_mul, abs_of_pos hD2]
  generalize sq2 x.X2 e.tl2 e.th2 = q at *
  cases hC : (x.sx && Nat.blt (4 * q.hi) e.tl2)
  · simp only [hC, cond_false] at hok ⊢
    cases hqo : q.ok
    · simp [hqo, smFail] at hok
    cases hql : (!x.sx || Nat.ble e.th2 (4 * q.lo))
    · simp [hqo, hql, smFail] at hok
    simp only [hqo, hql, Bool.and_self, cond_true]
    obtain ⟨qlo, qsm⟩ := qa3 hqo
    have hncl : ¬(|xr ^ 2 - w ^ 2| < w ^ 2 * (1 / SEXC) ∧ xr < 0) := by
      rintro ⟨c1, c2⟩
      cases hsx : x.sx
      · have := hx.xpos hD hsx; linarith
      · rw [hsx] at hql
        simp only [Bool.not_true, Bool.false_or] at hql
        have h' : (e.th2 : ℝ) ≤ 4 * q.lo := by exact_mod_cast bt (ble_d _ _) hql
        unfold SEXC at c1
        have : |xr ^ 2 - w ^ 2| * Den ^ 2 < w ^ 2 * (1 / 4) * Den ^ 2 := mul_lt_mul_of_pos_right c1 hD2
        rw [hab] at this; nlinarith
    rw [if_neg hncl]
    unfold SMs
    have ev : w ^ 2 * I / (xr ^ 2 - w ^ 2) = (w * Den) ^ 2 * I / ((xr ^ 2 - w ^ 2) * Den ^ 2) := by
      have : Den ^ 2 ≠ 0 := hD2.ne'
      rw [mul_pow, mul_comm (w ^ 2) (Den ^ 2), mul_comm (xr ^ 2 - w ^ 2) (Den ^ 2), mul_assoc,
        mul_div_mul_left _ _ this]
    rw [ev]
    simp only [Nat.cast_add, Nat.cast_one]
    exact quot_SM he.wsq.1 he.wsq.2 he.I_lo he.I_hi qlo qsm.1 qsm.2
  · simp only [hC, cond_true]
    simp only [Bool.and_eq_true] at hC
    have c4 : (4 : ℝ) * q.hi < e.tl2 := by exact_mod_cast bt (blt_d _ _) hC.2
    have hcl : |xr ^ 2 - w ^ 2| < w ^ 2 * (1 / SEXC) ∧ xr < 0 := by
      refine ⟨?_, hx.xneg hD hC.1⟩
      unfold SEXC
      have : |xr ^ 2 - w ^ 2| * Den ^ 2 < w ^ 2 * (1 / 4) * Den ^ 2 := by
        rw [hab]; nlinarith
      exact lt_of_mul_lt_mul_right this hD2.le
    rw [if_pos hcl]; simp [SMs, smZero]

/-- The near-pole SX value with its `sexcut` clamp. -/
theorem ssx_near {Den : ℝ} (hD : 0 < Den) {e : ED} {x : En} {xr w I : ℝ} (he : EDok e Den w I)
    (hx : Enok x Den xr)
    (hok : (bif x.sx && Nat.blt (8 * (addT x.sx x.X e.tl e.th).hi) e.tl then smZero
      else bif (addT x.sx x.X e.tl e.th).ok && (!x.sx || Nat.ble e.th (8 * (addT x.sx x.X e.tl e.th).lo)) then
        (⟨true, !(xor e.sI (addT x.sx x.X e.tl e.th).neg), e.tl * e.al / (2 * (addT x.sx x.X e.tl e.th).hi),
          e.th * e.ah / (2 * (addT x.sx x.X e.tl e.th).lo) + 1⟩ : SM)
      else smFail).ok = true) :
    SMs (bif x.sx && Nat.blt (8 * (addT x.sx x.X e.tl e.th).hi) e.tl then smZero
      else bif (addT x.sx x.X e.tl e.th).ok && (!x.sx || Nat.ble e.th (8 * (addT x.sx x.X e.tl e.th).lo)) then
        (⟨true, !(xor e.sI (addT x.sx x.X e.tl e.th).neg), e.tl * e.al / (2 * (addT x.sx x.X e.tl e.th).hi),
          e.th * e.ah / (2 * (addT x.sx x.X e.tl e.th).lo) + 1⟩ : SM)
      else smFail)
      (if |2 * (xr + w)| < w * (1 / SEXC) ∧ xr < 0 then 0 else -(I * w) / (2 * (xr + w))) := by
  have hs' : sg x.sx x.X + w * Den = (xr + w) * Den := by rw [← hx.val]; ring
  obtain ⟨sa1, sa2, sa3⟩ := addT_spec (sx := x.sx) (X := x.X) he.tl_pos he.w_lo he.w_hi
  rw [hs'] at sa1 sa2 sa3
  have hab : |2 * (xr + w)| * Den = 2 * |(xr + w) * Den| := by
    rw [abs_mul, abs_mul, abs_of_pos hD, abs_two]; ring
  generalize addT x.sx x.X e.tl e.th = sv at *
  cases hC : (x.sx && Nat.blt (8 * sv.hi) e.tl)
  · simp only [hC, cond_false] at hok ⊢
    cases hso : sv.ok
    · simp [hso, smFail] at hok
    cases hsl : (!x.sx || Nat.ble e.th (8 * sv.lo))
    · simp [hso, hsl, smFail] at hok
    simp only [hso, hsl, Bool.and_self, cond_true]
    obtain ⟨slo, ssm⟩ := sa3 hso
    have hncl : ¬(|2 * (xr + w)| < w * (1 / SEXC) ∧ xr < 0) := by
      rintro ⟨c1, c2⟩
      cases hsx : x.sx
      · have := hx.xpos hD hsx; linarith
      · rw [hsx] at hsl
        simp only [Bool.not_true, Bool.false_or] at hsl
        have h' : (e.th : ℝ) ≤ 8 * sv.lo := by exact_mod_cast bt (ble_d _ _) hsl
        unfold SEXC at c1
        have : |2 * (xr + w)| * Den < w * (1 / 4) * Den := mul_lt_mul_of_pos_right c1 hD
        rw [hab] at this; nlinarith [he.w_hi]
    rw [if_neg hncl]
    unfold SMs
    have ev : -(I * w) / (2 * (xr + w)) = -((w * Den) * I / (2 * ((xr + w) * Den))) := by
      have : Den ≠ 0 := hD.ne'
      rw [show (w * Den) * I = (w * I) * Den by ring, show 2 * ((xr + w) * Den) = (2 * (xr + w)) * Den by ring,
        mul_div_mul_right _ _ this, mul_comm I w, neg_div]
    rw [ev]
    have e2 : sg (!(xor e.sI sv.neg)) (-((w * Den) * I / (2 * ((xr + w) * Den)))) =
        sg (xor e.sI sv.neg) ((w * Den) * I / (2 * ((xr + w) * Den))) := by
      cases (xor e.sI sv.neg) <;> simp
    rw [e2]
    have hs2 : ((2 * sv.lo : ℕ) : ℝ) ≤ sg sv.neg (2 * ((xr + w) * Den)) ∧
        sg sv.neg (2 * ((xr + w) * Den)) ≤ ((2 * sv.hi : ℕ) : ℝ) := by
      rw [sg_mul]; push_cast; constructor <;> linarith [ssm.1, ssm.2]
    simp only [Nat.cast_add, Nat.cast_one]
    exact quot_SM he.w_lo he.w_hi he.I_lo he.I_hi (by omega) hs2.1 hs2.2
  · simp only [hC, cond_true]
    simp only [Bool.and_eq_true] at hC
    have c8 : (8 : ℝ) * sv.hi < e.tl := by exact_mod_cast bt (blt_d _ _) hC.2
    have hcl : |2 * (xr + w)| < w * (1 / SEXC) ∧ xr < 0 := by
      refine ⟨?_, hx.xneg hD hC.1⟩
      unfold SEXC
      have : |2 * (xr + w)| * Den < w * (1 / 4) * Den := by
        rw [hab]; nlinarith [he.w_lo]
      exact lt_of_mul_lt_mul_right this hD.le
    rw [if_pos hcl]; simp [SMs, smZero]

/-- **`ssxK` encloses the SX kernel** `Cert.certSsx` of a kept mode (scaled `I`). -/
theorem ssxK_spec {Den : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze)
    {e : ED} {x : En} {xr w I : ℝ} (he : EDok e Den w I)
    (hx : Enok x Den xr) (hok : (ssxK kc e x).ok = true) :
    SMs (ssxK kc e x) (ssxV I w xr) := by
  have hD2 : 0 < Den ^ 2 := by positivity
  have hd' : sg x.sx x.X - w * Den = (xr - w) * Den := by rw [← hx.val]; ring
  have htz0 : (0 : ℝ) < 2 ^ kc.tze := by positivity
  unfold ssxK at hok ⊢
  unfold ssxV GW.Endpoint.Cert.certSsx
  cases hdo : (subT x.sx x.X e.tl e.th).ok
  · simp [hdo, smFail] at hok
  simp only [hdo, cond_true] at hok ⊢
  obtain ⟨hlo, hsm⟩ := subT_spec he.tl_pos he.w_lo he.w_hi hdo
  have habs := subT_abs he.tl_pos he.w_lo he.w_hi hdo
  rw [hd'] at hsm habs
  obtain ⟨g1, g2⟩ := genT_spec hD hk2 hl habs.1 habs.2 he.wsq.1 he.wsq.2
  have hsqd := sq_bounds habs.1 habs.2
  have hsq : ((xr - w) * Den) ^ 2 = (xr - w) ^ 2 * Den ^ 2 := by ring
  rw [hsq] at hsqd
  have e3 : (w * Den) ^ 2 = w ^ 2 * Den ^ 2 := by ring
  have hwsq := he.wsq
  rw [e3] at hwsq
  generalize hdl : (subT x.sx x.X e.tl e.th).lo = dl at *
  generalize hdh : (subT x.sx x.X e.tl e.th).hi = dh at *
  cases hg1 : (genT kc dl dh e.tl2 e.th2).1
  · simp [hg1, smFail] at hok
  simp only [hg1, cond_true] at hok ⊢
  cases hg2 : (genT kc dl dh e.tl2 e.th2).2
  · have hG := g2 hg1 hg2
    simp only [hg2, cond_false] at hok ⊢
    rw [if_neg hG]
    cases hN1 : Nat.ble e.th2 ((dl * dl * kc.tzn) >>> kc.tze)
    · simp only [hN1, cond_false] at hok ⊢
      cases hN2 : Nat.blt ((dh * dh * kc.tzn) >>> kc.tze) e.tl2
      · simp [hN2, smFail] at hok
      simp only [hN2, cond_true] at hok ⊢
      have h2 := (shr_lt_iff _ _ _).mp (bt (blt_d _ _) hN2)
      have h2' : (dh : ℝ) * dh * kc.tzn < e.tl2 * 2 ^ kc.tze := by exact_mod_cast h2
      have hdne : xr - w ≠ 0 := by
        intro h0
        have : (dl : ℝ) ≤ 0 := by simpa [h0] using habs.1
        have : (0 : ℝ) < dl := by exact_mod_cast hlo
        linarith
      have hn : w ^ 2 > (xr - w) ^ 2 * TZ ∧ xr - w ≠ 0 := by
        refine ⟨?_, hdne⟩
        rw [htz]
        have c1 : (xr - w) ^ 2 * Den ^ 2 * kc.tzn ≤ (dh : ℝ) ^ 2 * kc.tzn :=
          mul_le_mul_of_nonneg_right hsqd.2 (Nat.cast_nonneg _)
        have c2 : (xr - w) ^ 2 * kc.tzn * Den ^ 2 < w ^ 2 * 2 ^ kc.tze * Den ^ 2 := by nlinarith
        have c3 := lt_of_mul_lt_mul_right c2 hD2.le
        show (xr - w) ^ 2 * (kc.tzn / 2 ^ kc.tze) < w ^ 2
        rw [mul_div_assoc', div_lt_iff₀ htz0]; linarith
      rw [if_pos hn]
      exact ssx_near hD he hx hok
    · simp only [hN1, cond_true]
      have h1 := (shr_le_iff _ _ _).mp (bt (ble_d _ _) hN1)
      have h1' : (e.th2 : ℝ) * 2 ^ kc.tze ≤ dl * dl * kc.tzn := by exact_mod_cast h1
      have hn : ¬(w ^ 2 > (xr - w) ^ 2 * TZ ∧ xr - w ≠ 0) := by
        rintro ⟨c, -⟩
        rw [htz] at c
        have c' : (xr - w) ^ 2 * kc.tzn < w ^ 2 * 2 ^ kc.tze := by
          have : (xr - w) ^ 2 * (kc.tzn / 2 ^ kc.tze) < w ^ 2 := c
          rw [mul_div_assoc', div_lt_iff₀ htz0] at this; linarith
        have c1 : (dl : ℝ) ^ 2 * kc.tzn ≤ (xr - w) ^ 2 * Den ^ 2 * kc.tzn :=
          mul_le_mul_of_nonneg_right hsqd.1 (Nat.cast_nonneg _)
        have c2 : (xr - w) ^ 2 * kc.tzn * Den ^ 2 < w ^ 2 * 2 ^ kc.tze * Den ^ 2 :=
          mul_lt_mul_of_pos_right c' hD2
        nlinarith
      rw [if_neg hn]; simp [SMs, smZero]
  · have hG := g1 hg1 hg2
    simp only [hg2, cond_true] at hok ⊢
    rw [if_pos hG]
    exact ssx_gen hD he hx hok

end GW.Endpoint.Kernel.Sig

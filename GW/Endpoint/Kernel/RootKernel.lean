/-
G2 roots, soundness (1/3): the derivative kernel checkers `dschK`, `dssxK` of
`RootCheck.lean` over an energy INTERVAL.

When a check succeeds, on the whole interval `[xa, xb]` of `x = wx`:
* every branch condition of the kernel has one truth value, so the kernel equals one
  fixed rational function there: it is continuous on `[xa, xb]` and has the formal
  derivative (`dschM`, `dcertSsx`) on `(xa, xb)` (`FixedOn`);
* `x ≠ w`, and for the SX kernel `x ≠ -w` (no point where the source divides by zero);
* the formal derivative lies in the enclosure (scaled: `x' = x Den`, `w' = w Den`, `I`
  scaled by `2^SI`; the derivative values are per eV).
-/
import GW.Endpoint.Kernel.RootCheck
import GW.Endpoint.Kernel.RootSpec
import GW.Endpoint.Kernel.SigmaKernel

namespace GW.Endpoint.Kernel.QP

open Set GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### Interval energies -/

/-- The semantics of an interval record: `0 < XL`, the squares, and every `x ∈ [xa, xb]`
has `(-1)^sx x Den ∈ [XL, XH]`. -/
structure EIok (x : EI) (Den xa xb : ℝ) : Prop where
  pos : 0 < x.XL
  sq1 : x.XL2 = x.XL * x.XL
  sq2 : x.XH2 = x.XH * x.XH
  mem : ∀ y ∈ Icc xa xb, (x.XL : ℝ) ≤ sg x.sx (y * Den) ∧ sg x.sx (y * Den) ≤ x.XH

theorem sg_sg' (b : Bool) (v : ℝ) : v = sg b (sg b v) := (sg_sg b v).symm

/-! ### Differences over an interval -/

theorem subI_spec {sx : Bool} {XL XH tl th : ℕ} {Y w : ℝ} (htl : 0 < tl) (hw1 : (tl : ℝ) ≤ w)
    (hw2 : w ≤ th) (hY1 : (XL : ℝ) ≤ Y) (hY2 : Y ≤ XH) (h : (subI sx XL XH tl th).ok = true) :
    0 < (subI sx XL XH tl th).lo ∧ SMs (subI sx XL XH tl th) (sg sx Y - w) := by
  have hth : tl ≤ th := by exact_mod_cast le_trans hw1 hw2
  have hXX : XL ≤ XH := by exact_mod_cast le_trans hY1 hY2
  unfold subI SMs at *
  cases sx
  · simp only [Bool.false_eq_true, cond_false, blt_d, Bool.cond_decide] at h ⊢
    by_cases h1 : th < XL
    · simp only [h1, if_true] at h ⊢
      have h1' : tl ≤ XH := by omega
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_false] <;>
        push_cast [Nat.cast_sub h1.le, Nat.cast_sub h1'] <;> linarith
    · simp only [h1, if_false] at h ⊢
      by_cases h2 : XH < tl
      · simp only [h2, if_true] at h ⊢
        have h2' : XL ≤ th := by omega
        refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_true, sg_false] <;>
          push_cast [Nat.cast_sub h2.le, Nat.cast_sub h2'] <;> linarith
      · simp [h2, smFail] at h
  · simp only [cond_true] at h ⊢
    refine ⟨by omega, ?_, ?_⟩ <;> simp only [sg_true] <;> push_cast <;> linarith

theorem addI_spec {sx : Bool} {XL XH tl th : ℕ} {Y w : ℝ} (htl : 0 < tl) (hw1 : (tl : ℝ) ≤ w)
    (hw2 : w ≤ th) (hY1 : (XL : ℝ) ≤ Y) (hY2 : Y ≤ XH) :
    ((addI sx XL XH tl th).lo : ℝ) ≤ |sg sx Y + w| ∧ |sg sx Y + w| ≤ (addI sx XL XH tl th).hi ∧
      ((addI sx XL XH tl th).ok = true → 0 < (addI sx XL XH tl th).lo ∧
        SMs (addI sx XL XH tl th) (sg sx Y + w)) := by
  have hth : tl ≤ th := by exact_mod_cast le_trans hw1 hw2
  have hXX : XL ≤ XH := by exact_mod_cast le_trans hY1 hY2
  have htl' : (0 : ℝ) < tl := by exact_mod_cast htl
  have hXL0 : (0 : ℝ) ≤ XL := Nat.cast_nonneg _
  unfold addI SMs
  cases sx
  · simp only [Bool.not_false, cond_true, sg_false]
    have : 0 ≤ Y + w := by linarith
    rw [abs_of_nonneg this]; push_cast
    refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by (try simp only [sg_false, sg_true]); push_cast; linarith,
        by (try simp only [sg_false, sg_true]); push_cast; linarith⟩⟩
  · simp only [Bool.not_true, cond_false, blt_d, Bool.cond_decide, sg_true]
    by_cases h1 : XH < tl
    · simp only [h1, if_true]
      have h1' : (XH : ℝ) < tl := by exact_mod_cast h1
      have : 0 ≤ -Y + w := by linarith
      rw [abs_of_nonneg this]
      have h1'' : XL ≤ th := by omega
      push_cast [Nat.cast_sub h1.le, Nat.cast_sub h1'']
      refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by (try simp only [sg_false, sg_true]); push_cast; linarith,
        by (try simp only [sg_false, sg_true]); push_cast; linarith⟩⟩
    · simp only [h1, if_false]
      by_cases h2 : th < XL
      · simp only [h2, if_true]
        have h2' : (th : ℝ) < XL := by exact_mod_cast h2
        have : -Y + w ≤ 0 := by linarith
        rw [abs_of_nonpos this]
        have h2'' : tl ≤ XH := by omega
        push_cast [Nat.cast_sub h2.le, Nat.cast_sub h2'']
        refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by (try simp only [sg_false, sg_true]); push_cast; linarith,
        by (try simp only [sg_false, sg_true]); push_cast; linarith⟩⟩
      · simp only [h2, if_false]
        refine ⟨by simp, ?_, fun h => by simp at h⟩
        have e1 : ((th - XL : ℕ) : ℝ) = th - XL := by
          have : XL ≤ th := by omega
          push_cast [Nat.cast_sub this]; rfl
        have e2 : ((XH - tl : ℕ) : ℝ) = XH - tl := by
          have : tl ≤ XH := by omega
          push_cast [Nat.cast_sub this]; rfl
        rw [Nat.cast_max, e1, e2, abs_le]
        constructor
        · have := le_max_right ((th : ℝ) - XL) ((XH : ℝ) - tl); linarith
        · have := le_max_left ((th : ℝ) - XL) ((XH : ℝ) - tl); linarith

theorem sq2I_spec {XL2 XH2 tl2 th2 : ℕ} {X2 W : ℝ} (hw1 : (tl2 : ℝ) ≤ W) (hw2 : W ≤ th2)
    (hx1 : (XL2 : ℝ) ≤ X2) (hx2 : X2 ≤ XH2) :
    ((sq2I XL2 XH2 tl2 th2).lo : ℝ) ≤ |X2 - W| ∧ |X2 - W| ≤ (sq2I XL2 XH2 tl2 th2).hi ∧
      ((sq2I XL2 XH2 tl2 th2).ok = true → 0 < (sq2I XL2 XH2 tl2 th2).lo ∧
        SMs (sq2I XL2 XH2 tl2 th2) (X2 - W)) := by
  have hth : tl2 ≤ th2 := by exact_mod_cast le_trans hw1 hw2
  have hXX : XL2 ≤ XH2 := by exact_mod_cast le_trans hx1 hx2
  unfold sq2I SMs
  simp only [blt_d, Bool.cond_decide]
  by_cases h1 : th2 < XL2
  · simp only [h1, if_true, sg_false]
    have h1' : (th2 : ℝ) < XL2 := by exact_mod_cast h1
    have : 0 ≤ X2 - W := by linarith
    rw [abs_of_nonneg this]
    have h1'' : tl2 ≤ XH2 := by omega
    push_cast [Nat.cast_sub h1.le, Nat.cast_sub h1'']
    refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by linarith, by linarith⟩⟩
  · simp only [h1, if_false]
    by_cases h2 : XH2 < tl2
    · simp only [h2, if_true, sg_true]
      have h2' : (XH2 : ℝ) < tl2 := by exact_mod_cast h2
      have : X2 - W ≤ 0 := by linarith
      rw [abs_of_nonpos this]
      have h2'' : XL2 ≤ th2 := by omega
      push_cast [Nat.cast_sub h2.le, Nat.cast_sub h2'']
      refine ⟨by linarith, by linarith, fun _ => ⟨by omega, by linarith, by linarith⟩⟩
    · simp only [h2, if_false]
      refine ⟨by simp, ?_, fun h => by simp at h⟩
      have e1 : ((th2 - XL2 : ℕ) : ℝ) = th2 - XL2 := by
        have : XL2 ≤ th2 := by omega
        push_cast [Nat.cast_sub this]; rfl
      have e2 : ((XH2 - tl2 : ℕ) : ℝ) = XH2 - tl2 := by
        have : tl2 ≤ XH2 := by omega
        push_cast [Nat.cast_sub this]; rfl
      rw [Nat.cast_max, e1, e2, abs_le]
      constructor
      · have := le_max_left ((th2 : ℝ) - XL2) ((XH2 : ℝ) - tl2); linarith
      · have := le_max_right ((th2 : ℝ) - XL2) ((XH2 : ℝ) - tl2); linarith


/-! ### One point of the interval -/

theorem EIok.pt {x : EI} {Den xa xb y : ℝ} (hD : 0 < Den) (hx : EIok x Den xa xb) (hy : y ∈ Icc xa xb) :
    (x.XL : ℝ) ≤ sg x.sx (y * Den) ∧ sg x.sx (y * Den) ≤ x.XH ∧ y * Den = sg x.sx (sg x.sx (y * Den)) ∧
      (0 : ℝ) < sg x.sx (y * Den) ∧ (x.XL2 : ℝ) ≤ (sg x.sx (y * Den)) ^ 2 ∧ (sg x.sx (y * Den)) ^ 2 ≤ x.XH2 ∧
      (x.sx = true → y < 0) ∧ (x.sx = false → 0 < y) := by
  obtain ⟨h1, h2⟩ := hx.mem y hy
  have hp : (0 : ℝ) < x.XL := by exact_mod_cast hx.pos
  have hY : (0 : ℝ) < sg x.sx (y * Den) := lt_of_lt_of_le hp h1
  refine ⟨h1, h2, (sg_sg _ _).symm, hY, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · rw [hx.sq1]; push_cast; nlinarith
  · rw [hx.sq2]; push_cast; nlinarith
  · rw [h, sg_true] at hY; nlinarith
  · rw [h, sg_false] at hY; nlinarith

/-- The value of `y Den - w Den` as `sg sx Y - w'`. -/
theorem sub_scaled {sx : Bool} {Den y w : ℝ} : sg sx (sg sx (y * Den)) - w * Den = (y - w) * Den := by
  rw [sg_sg]; ring

theorem add_scaled {sx : Bool} {Den y w : ℝ} : sg sx (sg sx (y * Den)) + w * Den = (y + w) * Den := by
  rw [sg_sg]; ring

/-! ### The CH kernel -/

/-- The branch function of the CH kernel is fixed where `Gen` has one truth value and `y ≠ w`. -/
theorem sch_fixed {w c xa xb : ℝ} (hne : ∀ y ∈ Icc xa xb, y ≠ w)
    (hG : (∀ y ∈ Icc xa xb, Gen y w) ∨ (∀ y ∈ Icc xa xb, ¬Gen y w)) :
    FixedOn (fun y => if Gen y w then c / (y - w) else 0) (fun y => if Gen y w then -c / (y - w) ^ 2 else 0)
      xa xb :=
  FixedOn.ite (fixed_div_sub c w fun y hy => sub_ne_zero.mpr (hne y hy)) (FixedOn.const 0 _ _) hG

/-- The quotient bounds of the derivative checkers. -/
theorem qb {nl nh dl dh : ℕ} {A D : ℝ} (h1 : (nl : ℝ) ≤ A) (h2 : A ≤ nh) (hdl : 0 < dl) (h3 : (dl : ℝ) ≤ D)
    (h4 : D ≤ dh) : ((nl / dh : ℕ) : ℝ) ≤ A / D ∧ A / D ≤ ((nh / dl : ℕ) : ℝ) + 1 :=
  qbounds h1 h2 hdl h3 h4

theorem mul3_bounds {a1 a2 b1 b2 c : ℕ} {A B : ℝ} (ha1 : (a1 : ℝ) ≤ A) (ha2 : A ≤ a2) (hb1 : (b1 : ℝ) ≤ B)
    (hb2 : B ≤ b2) : ((a1 * b1 * c : ℕ) : ℝ) ≤ A * B * c ∧ A * B * c ≤ ((a2 * b2 * c : ℕ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ a1 := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ b1 := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hA : 0 ≤ A := le_trans h0 ha1
  have hB : 0 ≤ B := le_trans h0' hb1
  push_cast
  constructor
  · exact mul_le_mul_of_nonneg_right (mul_le_mul ha1 hb1 h0' hA) hc
  · exact mul_le_mul_of_nonneg_right (mul_le_mul ha2 hb2 hB (le_trans hA ha2)) hc

theorem sq_le_sq_of {lo hi : ℕ} {d : ℝ} (h1 : (lo : ℝ) ≤ |d|) (h2 : |d| ≤ hi) :
    ((lo * lo : ℕ) : ℝ) ≤ d ^ 2 ∧ d ^ 2 ≤ ((hi * hi : ℕ) : ℝ) := by
  obtain ⟨a, b⟩ := sq_bounds h1 h2
  push_cast; constructor <;> nlinarith

/-- **`dschK` is sound** on the interval: `y ≠ w`, `Gen` decided, derivative enclosed. -/
theorem dschK_spec {Den : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) {DN : ℕ} (hDN : (DN : ℝ) = Den) {e : ED} {x : EI} {xa xb w I : ℝ}
    (he : EDok e Den w I) (hx : EIok x Den xa xb) (hok : (dschK kc DN e x).ok = true) :
    (∀ y ∈ Icc xa xb, y ≠ w) ∧ ((∀ y ∈ Icc xa xb, Gen y w) ∨ (∀ y ∈ Icc xa xb, ¬Gen y w)) ∧
      ∀ y ∈ Icc xa xb, SMs (dschK kc DN e x) (if Gen y w then -(w * I) / (y - w) ^ 2 else 0) := by
  unfold dschK at hok ⊢
  cases hdo : (subI x.sx x.XL x.XH e.tl e.th).ok
  · simp [hdo, smFail] at hok
  simp only [hdo, cond_true] at hok ⊢
  generalize hdd : subI x.sx x.XL x.XH e.tl e.th = d at *
  -- per point
  have P : ∀ y ∈ Icc xa xb, 0 < d.lo ∧ SMs d ((y - w) * Den) ∧ (d.lo : ℝ) ≤ |(y - w) * Den| ∧
      |(y - w) * Den| ≤ d.hi := by
    intro y hy
    obtain ⟨h1, h2, -, -, -, -, -, -⟩ := hx.pt hD hy
    have := subI_spec (sx := x.sx) he.tl_pos he.w_lo he.w_hi h1 h2 (by rw [hdd]; exact hdo)
    rw [hdd, sub_scaled] at this
    exact ⟨this.1, this.2, SMs_abs this.2⟩
  have hne : ∀ y ∈ Icc xa xb, y ≠ w := by
    intro y hy h
    obtain ⟨h0, -, h1, -⟩ := P y hy
    rw [h, sub_self, zero_mul, abs_zero] at h1
    have : (0 : ℝ) < d.lo := by exact_mod_cast h0
    linarith
  have G : ∀ y ∈ Icc xa xb, ((genT kc d.lo d.hi e.tl2 e.th2).1 = true → (genT kc d.lo d.hi e.tl2 e.th2).2 = true →
      Gen y w) ∧ ((genT kc d.lo d.hi e.tl2 e.th2).1 = true → (genT kc d.lo d.hi e.tl2 e.th2).2 = false → ¬Gen y w) :=
    fun y hy => genT_spec hD hk2 hl (P y hy).2.2.1 (P y hy).2.2.2 he.wsq.1 he.wsq.2
  cases hg1 : (genT kc d.lo d.hi e.tl2 e.th2).1
  · simp [hg1, smFail] at hok
  simp only [hg1, cond_true] at hok ⊢
  cases hg2 : (genT kc d.lo d.hi e.tl2 e.th2).2
  · have hG : ∀ y ∈ Icc xa xb, ¬Gen y w := fun y hy => (G y hy).2 hg1 hg2
    simp only [hg2, cond_false]
    refine ⟨hne, Or.inr hG, fun y hy => ?_⟩
    rw [if_neg (hG y hy)]; simp [SMs, smZero]
  · have hG : ∀ y ∈ Icc xa xb, Gen y w := fun y hy => (G y hy).1 hg1 hg2
    simp only [hg2, cond_true]
    refine ⟨hne, Or.inl hG, fun y hy => ?_⟩
    rw [if_pos (hG y hy)]
    obtain ⟨h0, hsm, ha1, ha2⟩ := P y hy
    unfold SMs
    have ev : sg (!e.sI) (-(w * I) / (y - w) ^ 2) =
        (w * Den) * sg e.sI I * DN / ((y - w) * Den) ^ 2 := by
      have hD0 : Den ≠ 0 := hD.ne'
      have hyw : y - w ≠ 0 := sub_ne_zero.mpr (hne y hy)
      rw [hDN]
      cases e.sI <;> simp only [Bool.not_false, Bool.not_true, sg_true, sg_false] <;> field_simp <;> ring
    rw [ev]
    have hq := qb (mul3_bounds (c := DN) he.w_lo he.w_hi he.I_lo he.I_hi).1
      (mul3_bounds (c := DN) he.w_lo he.w_hi he.I_lo he.I_hi).2 (Nat.mul_pos h0 h0)
      (sq_le_sq_of ha1 ha2).1 (sq_le_sq_of ha1 ha2).2
    simp only [Nat.cast_add, Nat.cast_one]
    exact hq


/-! ### The SX kernel -/

/-- The x-derivative of the SX kernel of a kept mode (scaled `I`). -/
noncomputable def dssxV (I w x : ℝ) : ℝ := dcertSsx GAM2 LIM1 TZ SEXC I w x

theorem mul4_bounds {a1 a2 b1 b2 c1 c2 k : ℕ} {A B C : ℝ} (ha1 : (a1 : ℝ) ≤ A) (ha2 : A ≤ a2)
    (hb1 : (b1 : ℝ) ≤ B) (hb2 : B ≤ b2) (hc1 : (c1 : ℝ) ≤ C) (hc2 : C ≤ c2) :
    ((2 * a1 * b1 * c1 * k : ℕ) : ℝ) ≤ 2 * A * B * C * k ∧ 2 * A * B * C * k ≤ ((2 * a2 * b2 * c2 * k : ℕ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ a1 := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ b1 := Nat.cast_nonneg _
  have h0'' : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hA : 0 ≤ A := le_trans h0 ha1
  have hB : 0 ≤ B := le_trans h0' hb1
  have hC : 0 ≤ C := le_trans h0'' hc1
  push_cast
  constructor
  · have := mul_le_mul (mul_le_mul ha1 hb1 h0' hA) hc1 h0'' (mul_nonneg hA hB)
    nlinarith
  · have := mul_le_mul (mul_le_mul ha2 hb2 hB (le_trans hA ha2)) hc2 hC (mul_nonneg (le_trans hA ha2) (le_trans hB hb2))
    nlinarith

theorem TZ_lt : 4 * TZ < 1 := by unfold TZ; norm_num

set_option maxHeartbeats 2000000 in
/-- **`dssxK` is sound** on the interval: `y ≠ w`, `y ≠ -w`, the SX kernel fixed, and its
derivative enclosed. -/
theorem dssxK_spec {Den : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {DN : ℕ} (hDN : (DN : ℝ) = Den)
    {e : ED} {x : EI} {xa xb w I : ℝ}
    (he : EDok e Den w I) (hx : EIok x Den xa xb) (hok : (dssxK kc DN e x).ok = true) :
    (∀ y ∈ Icc xa xb, y ≠ w ∧ y + w ≠ 0) ∧ FixedOn (ssxV I w) (dssxV I w) xa xb ∧
      ∀ y ∈ Icc xa xb, SMs (dssxK kc DN e x) (dssxV I w y) := by
  have hD2 : 0 < Den ^ 2 := by positivity
  have htz0 : (0 : ℝ) < 2 ^ kc.tze := by positivity
  have hw0 : 0 < w := by
    have := he.w_lo
    have h : (0 : ℝ) < e.tl := by exact_mod_cast he.tl_pos
    have : 0 < w * Den := by linarith
    exact pos_of_mul_pos_left this hD.le
  unfold dssxK at hok ⊢
  unfold ssxV dssxV
  cases hdo : (subI x.sx x.XL x.XH e.tl e.th).ok
  · simp [hdo, smFail] at hok
  simp only [hdo, cond_true] at hok ⊢
  generalize hdd : subI x.sx x.XL x.XH e.tl e.th = d at *
  have P : ∀ y ∈ Icc xa xb, 0 < d.lo ∧ SMs d ((y - w) * Den) ∧ (d.lo : ℝ) ≤ |(y - w) * Den| ∧
      |(y - w) * Den| ≤ d.hi := by
    intro y hy
    obtain ⟨h1, h2, -, -, -, -, -, -⟩ := hx.pt hD hy
    have := subI_spec (sx := x.sx) he.tl_pos he.w_lo he.w_hi h1 h2 (by rw [hdd]; exact hdo)
    rw [hdd, sub_scaled] at this
    exact ⟨this.1, this.2, SMs_abs this.2⟩
  have hne : ∀ y ∈ Icc xa xb, y ≠ w := by
    intro y hy h
    obtain ⟨h0, -, h1, -⟩ := P y hy
    rw [h, sub_self, zero_mul, abs_zero] at h1
    have : (0 : ℝ) < d.lo := by exact_mod_cast h0
    linarith
  have hsq : ∀ y ∈ Icc xa xb, (d.lo : ℝ) ^ 2 ≤ (y - w) ^ 2 * Den ^ 2 ∧ (y - w) ^ 2 * Den ^ 2 ≤ (d.hi : ℝ) ^ 2 := by
    intro y hy
    have := sq_bounds (P y hy).2.2.1 (P y hy).2.2.2
    rwa [mul_pow] at this
  have e3 : (w * Den) ^ 2 = w ^ 2 * Den ^ 2 := by ring
  have hwsq := he.wsq
  rw [e3] at hwsq
  have G : ∀ y ∈ Icc xa xb, ((genT kc d.lo d.hi e.tl2 e.th2).1 = true → (genT kc d.lo d.hi e.tl2 e.th2).2 = true →
      Gen y w) ∧ ((genT kc d.lo d.hi e.tl2 e.th2).1 = true → (genT kc d.lo d.hi e.tl2 e.th2).2 = false → ¬Gen y w) :=
    fun y hy => genT_spec hD hk2 hl (P y hy).2.2.1 (P y hy).2.2.2 he.wsq.1 he.wsq.2
  cases hg1 : (genT kc d.lo d.hi e.tl2 e.th2).1
  · simp [hg1, smFail] at hok
  simp only [hg1, cond_true] at hok ⊢
  cases hg2 : (genT kc d.lo d.hi e.tl2 e.th2).2
  · -- not generic on the whole interval
    have hG : ∀ y ∈ Icc xa xb, ¬Gen y w := fun y hy => (G y hy).2 hg1 hg2
    have hG' : ∀ y ∈ Icc xa xb, ¬((y - w) ^ 2 > GAM2 ∧ w ^ 2 < (y - w) ^ 2 * LIM1) := hG
    simp only [hg2, cond_false] at hok ⊢
    cases hN1 : Nat.ble e.th2 ((d.lo * d.lo * kc.tzn) >>> kc.tze)
    · simp only [hN1, cond_false] at hok ⊢
      cases hN2 : Nat.blt ((d.hi * d.hi * kc.tzn) >>> kc.tze) e.tl2
      · simp [hN2, smFail] at hok
      simp only [hN2, cond_true] at hok ⊢
      have h2 := (shr_lt_iff _ _ _).mp (bt (blt_d _ _) hN2)
      have h2' : (d.hi : ℝ) * d.hi * kc.tzn < e.tl2 * 2 ^ kc.tze := by exact_mod_cast h2
      have hn : ∀ y ∈ Icc xa xb, w ^ 2 > (y - w) ^ 2 * TZ ∧ y - w ≠ 0 := by
        intro y hy
        refine ⟨?_, sub_ne_zero.mpr (hne y hy)⟩
        rw [htz]
        have c1 : (y - w) ^ 2 * Den ^ 2 * kc.tzn ≤ (d.hi : ℝ) ^ 2 * kc.tzn :=
          mul_le_mul_of_nonneg_right (hsq y hy).2 (Nat.cast_nonneg _)
        have c2 : (y - w) ^ 2 * kc.tzn * Den ^ 2 < w ^ 2 * 2 ^ kc.tze * Den ^ 2 := by nlinarith
        have c3 := lt_of_mul_lt_mul_right c2 hD2.le
        show (y - w) ^ 2 * (kc.tzn / 2 ^ kc.tze) < w ^ 2
        rw [mul_div_assoc', div_lt_iff₀ htz0]; linarith
      cases hso : (addI x.sx x.XL x.XH e.tl e.th).ok
      · simp [hso, smFail] at hok
      simp only [hso, cond_true] at hok ⊢
      generalize hss : addI x.sx x.XL x.XH e.tl e.th = sv at *
      have S : ∀ y ∈ Icc xa xb, 0 < sv.lo ∧ SMs sv ((y + w) * Den) ∧ (sv.lo : ℝ) ≤ |(y + w) * Den| ∧
          |(y + w) * Den| ≤ sv.hi := by
        intro y hy
        obtain ⟨h1, h2', -, -, -, -, -, -⟩ := hx.pt hD hy
        obtain ⟨a1, a2, a3⟩ := addI_spec (sx := x.sx) he.tl_pos he.w_lo he.w_hi h1 h2'
        rw [hss, add_scaled] at a1 a2 a3
        obtain ⟨b1, b2⟩ := a3 hso
        exact ⟨b1, b2, a1, a2⟩
      have hne' : ∀ y ∈ Icc xa xb, y + w ≠ 0 := by
        intro y hy h
        obtain ⟨h0, -, h1, -⟩ := S y hy
        rw [h, zero_mul, abs_zero] at h1
        have : (0 : ℝ) < sv.lo := by exact_mod_cast h0
        linarith
      have hab : ∀ y : ℝ, |2 * (y + w)| * Den = 2 * |(y + w) * Den| := fun y => by
        rw [abs_mul, abs_mul, abs_of_pos hD, abs_two]; ring
      cases hC : (x.sx && Nat.blt (8 * sv.hi) e.tl)
      · simp only [hC, cond_false] at hok ⊢
        cases hsl : (!x.sx || Nat.ble e.th (8 * sv.lo))
        · simp [hsl, smFail] at hok
        simp only [hsl, cond_true]
        have hncl : ∀ y ∈ Icc xa xb, ¬(|2 * (y + w)| < w * (1 / SEXC) ∧ y < 0) := by
          rintro y hy ⟨c1, c2⟩
          obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hx.pt hD hy
          cases hsx : x.sx
          · have := hpos hsx; linarith
          · rw [hsx] at hsl
            simp only [Bool.not_true, Bool.false_or] at hsl
            have h' : (e.th : ℝ) ≤ 8 * sv.lo := by exact_mod_cast bt (ble_d _ _) hsl
            unfold SEXC at c1
            have : |2 * (y + w)| * Den < w * (1 / 4) * Den := mul_lt_mul_of_pos_right c1 hD
            rw [hab] at this; nlinarith [he.w_hi, (S y hy).2.2.1]
        have hval : ∀ y ∈ Icc xa xb, GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w y = -(I * w) / (2 * (y + w)) ∧
            dcertSsx GAM2 LIM1 TZ SEXC I w y = (I * w) / (2 * (y + w) ^ 2) := by
          intro y hy
          unfold GW.Endpoint.Cert.certSsx dcertSsx
          rw [if_neg (hG' y hy), if_pos (hn y hy), if_neg (hncl y hy), if_neg (hG' y hy), if_pos (hn y hy),
            if_neg (hncl y hy)]
          exact ⟨rfl, rfl⟩
        refine ⟨fun y hy => ⟨hne y hy, hne' y hy⟩, ?_, fun y hy => ?_⟩
        · exact (fixed_div_add (-(I * w)) w hne').congr (fun y hy => (hval y hy).1.symm)
            (fun y hy => by rw [(hval y (Ioo_subset_Icc_self hy)).2, neg_neg])
        · rw [(hval y hy).2]
          obtain ⟨h0, hsm, ha1, ha2⟩ := S y hy
          unfold SMs
          have ev : sg e.sI (I * w / (2 * (y + w) ^ 2)) = (w * Den) * sg e.sI I * DN / (2 * ((y + w) * Den) ^ 2) := by
            have hD0 : Den ≠ 0 := hD.ne'
            have hyw : y + w ≠ 0 := hne' y hy
            rw [hDN]
            cases e.sI <;> simp only [sg_true, sg_false] <;> field_simp <;> ring
          rw [ev]
          have hs2 := sq_le_sq_of ha1 ha2
          have hq := qb (dl := 2 * (sv.lo * sv.lo)) (dh := 2 * (sv.hi * sv.hi))
            (mul3_bounds (c := DN) he.w_lo he.w_hi he.I_lo he.I_hi).1
            (mul3_bounds (c := DN) he.w_lo he.w_hi he.I_lo he.I_hi).2 (by positivity)
            (D := 2 * ((y + w) * Den) ^ 2) (by push_cast at hs2 ⊢; linarith [hs2.1])
            (by push_cast at hs2 ⊢; linarith [hs2.2])
          simp only [Nat.cast_add, Nat.cast_one]
          exact hq
      · simp only [hC, cond_true]
        simp only [Bool.and_eq_true] at hC
        have c8 : (8 : ℝ) * sv.hi < e.tl := by exact_mod_cast bt (blt_d _ _) hC.2
        have hcl : ∀ y ∈ Icc xa xb, |2 * (y + w)| < w * (1 / SEXC) ∧ y < 0 := by
          intro y hy
          obtain ⟨-, -, -, -, -, -, hneg, -⟩ := hx.pt hD hy
          refine ⟨?_, hneg hC.1⟩
          unfold SEXC
          have : |2 * (y + w)| * Den < w * (1 / 4) * Den := by
            rw [hab]; nlinarith [he.w_lo, (S y hy).2.2.2]
          exact lt_of_mul_lt_mul_right this hD.le
        have hval : ∀ y ∈ Icc xa xb, GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w y = 0 ∧
            dcertSsx GAM2 LIM1 TZ SEXC I w y = 0 := by
          intro y hy
          unfold GW.Endpoint.Cert.certSsx dcertSsx
          rw [if_neg (hG' y hy), if_pos (hn y hy), if_pos (hcl y hy), if_neg (hG' y hy), if_pos (hn y hy),
            if_pos (hcl y hy)]
          exact ⟨rfl, rfl⟩
        refine ⟨fun y hy => ⟨hne y hy, hne' y hy⟩, ?_, fun y hy => ?_⟩
        · exact (FixedOn.const 0 xa xb).congr (fun y hy => (hval y hy).1.symm)
            (fun y hy => (hval y (Ioo_subset_Icc_self hy)).2.symm)
        · rw [(hval y hy).2]; simp [SMs, smZero]
    · simp only [hN1, cond_true]
      have h1 := (shr_le_iff _ _ _).mp (bt (ble_d _ _) hN1)
      have h1' : (e.th2 : ℝ) * 2 ^ kc.tze ≤ d.lo * d.lo * kc.tzn := by exact_mod_cast h1
      have hn : ∀ y ∈ Icc xa xb, ¬(w ^ 2 > (y - w) ^ 2 * TZ ∧ y - w ≠ 0) := by
        rintro y hy ⟨c, -⟩
        rw [htz] at c
        have c' : (y - w) ^ 2 * kc.tzn < w ^ 2 * 2 ^ kc.tze := by
          have : (y - w) ^ 2 * (kc.tzn / 2 ^ kc.tze) < w ^ 2 := c
          rw [mul_div_assoc', div_lt_iff₀ htz0] at this; linarith
        have c1 : (d.lo : ℝ) ^ 2 * kc.tzn ≤ (y - w) ^ 2 * Den ^ 2 * kc.tzn :=
          mul_le_mul_of_nonneg_right (hsq y hy).1 (Nat.cast_nonneg _)
        have c2 : (y - w) ^ 2 * kc.tzn * Den ^ 2 < w ^ 2 * 2 ^ kc.tze * Den ^ 2 :=
          mul_lt_mul_of_pos_right c' hD2
        nlinarith
      have hne' : ∀ y ∈ Icc xa xb, y + w ≠ 0 := by
        intro y hy h
        have hy' : y = -w := by linarith
        have hs : (y - w) ^ 2 * TZ < w ^ 2 := by
          have hw2 : 0 < w ^ 2 := by positivity
          calc (y - w) ^ 2 * TZ = w ^ 2 * (4 * TZ) := by rw [hy']; ring
            _ < w ^ 2 * 1 := mul_lt_mul_of_pos_left TZ_lt hw2
            _ = w ^ 2 := mul_one _
        exact hn y hy ⟨hs, sub_ne_zero.mpr (hne y hy)⟩
      have hval : ∀ y ∈ Icc xa xb, GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w y = 0 ∧
          dcertSsx GAM2 LIM1 TZ SEXC I w y = 0 := by
        intro y hy
        unfold GW.Endpoint.Cert.certSsx dcertSsx
        rw [if_neg (hG' y hy), if_neg (hn y hy), if_neg (hG' y hy), if_neg (hn y hy)]
        exact ⟨rfl, rfl⟩
      refine ⟨fun y hy => ⟨hne y hy, hne' y hy⟩, ?_, fun y hy => ?_⟩
      · exact (FixedOn.const 0 xa xb).congr (fun y hy => (hval y hy).1.symm)
          (fun y hy => (hval y (Ioo_subset_Icc_self hy)).2.symm)
      · rw [(hval y hy).2]; simp [SMs, smZero]
  · -- generic on the whole interval
    have hG : ∀ y ∈ Icc xa xb, Gen y w := fun y hy => (G y hy).1 hg1 hg2
    have hG' : ∀ y ∈ Icc xa xb, (y - w) ^ 2 > GAM2 ∧ w ^ 2 < (y - w) ^ 2 * LIM1 := hG
    simp only [hg2, cond_true] at hok ⊢
    cases hqo : (sq2I x.XL2 x.XH2 e.tl2 e.th2).ok
    · simp [hqo, smFail] at hok
    simp only [hqo, cond_true] at hok ⊢
    generalize hqq : sq2I x.XL2 x.XH2 e.tl2 e.th2 = q at *
    have Qp : ∀ y ∈ Icc xa xb, 0 < q.lo ∧ SMs q ((y ^ 2 - w ^ 2) * Den ^ 2) ∧
        (q.lo : ℝ) ≤ |(y ^ 2 - w ^ 2) * Den ^ 2| ∧ |(y ^ 2 - w ^ 2) * Den ^ 2| ≤ q.hi := by
      intro y hy
      obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hx.pt hD hy
      obtain ⟨a1, a2, a3⟩ := sq2I_spec (XL2 := x.XL2) (XH2 := x.XH2) he.wsq.1 he.wsq.2 h5 h6
      have ey : (sg x.sx (y * Den)) ^ 2 - (w * Den) ^ 2 = (y ^ 2 - w ^ 2) * Den ^ 2 := by
        cases x.sx <;> simp only [sg_true, sg_false] <;> ring
      rw [hqq, ey] at a1 a2 a3
      obtain ⟨b1, b2⟩ := a3 hqo
      exact ⟨b1, b2, a1, a2⟩
    have hq0 : ∀ y ∈ Icc xa xb, y ^ 2 - w ^ 2 ≠ 0 := by
      intro y hy h
      obtain ⟨h0, -, h1, -⟩ := Qp y hy
      rw [h, zero_mul, abs_zero] at h1
      have : (0 : ℝ) < q.lo := by exact_mod_cast h0
      linarith
    have hne' : ∀ y ∈ Icc xa xb, y + w ≠ 0 := by
      intro y hy h
      apply hq0 y hy
      have : y = -w := by linarith
      rw [this]; ring
    have hab : ∀ y : ℝ, |y ^ 2 - w ^ 2| * Den ^ 2 = |(y ^ 2 - w ^ 2) * Den ^ 2| := fun y => by
      rw [abs_mul, abs_of_pos hD2]
    cases hC : (x.sx && Nat.blt (4 * q.hi) e.tl2)
    · simp only [hC, cond_false] at hok ⊢
      cases hql : (!x.sx || Nat.ble e.th2 (4 * q.lo))
      · simp [hql, smFail] at hok
      simp only [hql, cond_true]
      have hncl : ∀ y ∈ Icc xa xb, ¬(|y ^ 2 - w ^ 2| < w ^ 2 * (1 / SEXC) ∧ y < 0) := by
        rintro y hy ⟨c1, c2⟩
        obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hx.pt hD hy
        cases hsx : x.sx
        · have := hpos hsx; linarith
        · rw [hsx] at hql
          simp only [Bool.not_true, Bool.false_or] at hql
          have h' : (e.th2 : ℝ) ≤ 4 * q.lo := by exact_mod_cast bt (ble_d _ _) hql
          unfold SEXC at c1
          have : |y ^ 2 - w ^ 2| * Den ^ 2 < w ^ 2 * (1 / 4) * Den ^ 2 := mul_lt_mul_of_pos_right c1 hD2
          rw [hab] at this; nlinarith [(Qp y hy).2.2.1]
      have hval : ∀ y ∈ Icc xa xb, GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w y = w ^ 2 * I / (y ^ 2 - w ^ 2) ∧
          dcertSsx GAM2 LIM1 TZ SEXC I w y = -(2 * y * w ^ 2 * I) / (y ^ 2 - w ^ 2) ^ 2 := by
        intro y hy
        unfold GW.Endpoint.Cert.certSsx dcertSsx
        rw [if_pos (hG' y hy), if_neg (hncl y hy), if_pos (hG' y hy), if_neg (hncl y hy)]
        exact ⟨rfl, rfl⟩
      refine ⟨fun y hy => ⟨hne y hy, hne' y hy⟩, ?_, fun y hy => ?_⟩
      · exact (fixed_div_sq (w ^ 2 * I) w hq0).congr (fun y hy => (hval y hy).1.symm)
          (fun y hy => by rw [(hval y (Ioo_subset_Icc_self hy)).2]; ring)
      · rw [(hval y hy).2]
        obtain ⟨h0, hsm, ha1, ha2⟩ := Qp y hy
        obtain ⟨hY1, hY2, hY3, hY4, -, -, -, -⟩ := hx.pt hD hy
        unfold SMs
        have ev : sg (!(xor x.sx e.sI)) (-(2 * y * w ^ 2 * I) / (y ^ 2 - w ^ 2) ^ 2) =
            2 * sg x.sx (y * Den) * (w * Den) ^ 2 * sg e.sI I * DN / ((y ^ 2 - w ^ 2) * Den ^ 2) ^ 2 := by
          have hD0 : Den ≠ 0 := hD.ne'
          have hyw : y ^ 2 - w ^ 2 ≠ 0 := hq0 y hy
          rw [hDN]
          cases x.sx <;> cases e.sI <;> simp only [Bool.xor_false, Bool.xor_true, Bool.true_xor,
            Bool.false_xor, Bool.not_false, Bool.not_true, sg_true, sg_false] <;> field_simp <;> ring
        rw [ev]
        have hs2 := sq_le_sq_of ha1 ha2
        have hm := mul4_bounds (k := DN) hY1 hY2 he.wsq.1 he.wsq.2 he.I_lo he.I_hi
        have hq := qb hm.1 hm.2 (Nat.mul_pos h0 h0) hs2.1 hs2.2
        simp only [Nat.cast_add, Nat.cast_one]
        exact hq
    · simp only [hC, cond_true]
      simp only [Bool.and_eq_true] at hC
      have c4 : (4 : ℝ) * q.hi < e.tl2 := by exact_mod_cast bt (blt_d _ _) hC.2
      have hcl : ∀ y ∈ Icc xa xb, |y ^ 2 - w ^ 2| < w ^ 2 * (1 / SEXC) ∧ y < 0 := by
        intro y hy
        obtain ⟨-, -, -, -, -, -, hneg, -⟩ := hx.pt hD hy
        refine ⟨?_, hneg hC.1⟩
        unfold SEXC
        have : |y ^ 2 - w ^ 2| * Den ^ 2 < w ^ 2 * (1 / 4) * Den ^ 2 := by
          rw [hab]; nlinarith [(Qp y hy).2.2.2]
        exact lt_of_mul_lt_mul_right this hD2.le
      have hval : ∀ y ∈ Icc xa xb, GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w y = 0 ∧
          dcertSsx GAM2 LIM1 TZ SEXC I w y = 0 := by
        intro y hy
        unfold GW.Endpoint.Cert.certSsx dcertSsx
        rw [if_pos (hG' y hy), if_pos (hcl y hy), if_pos (hG' y hy), if_pos (hcl y hy)]
        exact ⟨rfl, rfl⟩
      refine ⟨fun y hy => ⟨hne y hy, hne' y hy⟩, ?_, fun y hy => ?_⟩
      · exact (FixedOn.const 0 xa xb).congr (fun y hy => (hval y hy).1.symm)
          (fun y hy => (hval y (Ioo_subset_Icc_self hy)).2.symm)
      · rw [(hval y hy).2]; simp [SMs, smZero]

end GW.Endpoint.Kernel.QP

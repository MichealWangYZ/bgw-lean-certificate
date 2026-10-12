/-
G2-coulomb (5/n): soundness of the kernel checker `treeChk` (`CheckDefs.lean`).

For a triangle `y(s) = a₀ + s₁ d₁ + s₂ d₂` whose Gram numerators are `qc` (`GramOK`, scale
`s2 = sD²`), `treeChk_sound`: if `treeChk qc k t 0 0 0 false = some (lo, hi)` and every rule
degree used is certified (`degOK`), then

  lo ≤ 2^K · WCc · sD^{-k} · ∫_{T2} |y(s)|_B^{-k} ds ≤ hi       (K = KB for k = 2, KB1 for k = 1),

and `|y(s)|_B > 0` on `T2`.
-/
import GW.Endpoint.Coulomb.Leaf

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset

/-- The six Gram numerators of `(a, D, E)` at scale `S` (`S ⟨·,·⟩ = numerator`). -/
structure GramOK (Q : QF) (a D E : E3) (S : ℝ) (g00 g01 g02 g11 g12 g22 : ℤ) : Prop where
  h00 : Q.q a * S = g00
  h01 : Q.bil a D * S = g01
  h02 : Q.bil a E * S = g02
  h11 : Q.q D * S = g11
  h12 : Q.bil D E * S = g12
  h22 : Q.q E * S = g22

/-- `±1`. -/
noncomputable def epsR (e : Bool) : ℝ := if e then -1 else 1

theorem epsR_sq (e : Bool) : epsR e ^ 2 = 1 := by cases e <;> simp [epsR]

/-- The leaf point map `s ↦ (p + ε s) / 2^j`. -/
noncomputable def lpt (j : ℕ) (p1 p2 : ℤ) (e : Bool) (s : ℝ × ℝ) : ℝ × ℝ :=
  ((p1 + epsR e * s.1) / 2 ^ j, (p2 + epsR e * s.2) / 2 ^ j)

theorem aff_apply (a D E : E3) (s : ℝ × ℝ) : aff a D E s = a + s.1 • D + s.2 • E := rfl

/-- The leaf as an affine map. -/
theorem aff_leaf (a0 d1 d2 : E3) (j : ℕ) (p1 p2 : ℤ) (e : Bool) (s : ℝ × ℝ) :
    aff (aff a0 d1 d2 ((p1 : ℝ) / 2 ^ j, (p2 : ℝ) / 2 ^ j)) ((epsR e / 2 ^ j) • d1) ((epsR e / 2 ^ j) • d2) s =
      aff a0 d1 d2 (lpt j p1 p2 e s) := by
  ext i; simp only [aff, lpt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The Gram numerators of a leaf are `leafLQ`. -/
theorem gram_leaf (Q : QF) {a0 d1 d2 : E3} {s2 : ℝ} {qc : QC}
    (h : GramOK Q a0 d1 d2 s2 qc.q00 qc.q01 qc.q02 qc.q11 qc.q12 qc.q22) (j : ℕ) (p1 p2 : ℤ) (e : Bool) :
    GramOK Q (aff a0 d1 d2 ((p1 : ℝ) / 2 ^ j, (p2 : ℝ) / 2 ^ j)) ((epsR e / 2 ^ j) • d1)
      ((epsR e / 2 ^ j) • d2) ((2 : ℝ) ^ j * 2 ^ j * s2)
      (leafLQ qc j p1 p2 e).l00 (leafLQ qc j p1 p2 e).l01 (leafLQ qc j p1 p2 e).l02
      (leafLQ qc j p1 p2 e).l11 (leafLQ qc j p1 p2 e).l12 (leafLQ qc j p1 p2 e).l22 := by
  obtain ⟨h00, h01, h02, h11, h12, h22⟩ := h
  have hH : (2 : ℝ) ^ j ≠ 0 := by positivity
  cases e <;>
  · simp only [leafLQ, epsR, Bool.false_eq_true, if_true, if_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast
    · rw [aff_apply, QF.q_aff]
      rw [← h00, ← h01, ← h02, ← h11, ← h12, ← h22]; field_simp; ring
    · rw [aff_apply, QF.bil_add_left, QF.bil_add_left, QF.bil_smul_left, QF.bil_smul_left,
        QF.bil_smul_right, QF.bil_smul_right, QF.bil_smul_right, Q.bil_comm d2 d1]
      rw [← h01, ← h11, ← h12]; simp only [QF.q]; field_simp; ring
    · rw [aff_apply, QF.bil_add_left, QF.bil_add_left, QF.bil_smul_left, QF.bil_smul_left,
        QF.bil_smul_right, QF.bil_smul_right, QF.bil_smul_right]
      rw [← h02, ← h12, ← h22]; simp only [QF.q]; field_simp; ring
    · rw [QF.q_smul, ← h11]; field_simp; ring
    · rw [QF.bil_smul_left, QF.bil_smul_right, ← h12]; field_simp; ring
    · rw [QF.q_smul, ← h22]; field_simp; ring

/-- `m² S |y(a/m, b/m)|² = nodeN`. -/
theorem node_q (Q : QF) {a D E : E3} {S : ℝ} {L : LQ} (h : GramOK Q a D E S L.l00 L.l01 L.l02 L.l11 L.l12 L.l22)
    (x y m : ℤ) (hm : (m : ℝ) ≠ 0) :
    Q.q (aff a D E ((x : ℝ) / m, (y : ℝ) / m)) * ((m : ℝ) ^ 2 * S) = nodeN L x y m := by
  obtain ⟨h00, h01, h02, h11, h12, h22⟩ := h
  rw [aff_apply, QF.q_aff]; simp only [nodeN]; push_cast
  rw [← h00, ← h01, ← h02, ← h11, ← h12, ← h22]; field_simp; ring

/-- `9 S |v - c|² = offR` for a vertex `v` (offsets `(u,v)/3`). -/
theorem off_q (Q : QF) {a D E : E3} {S : ℝ} {L : LQ} (h : GramOK Q a D E S L.l00 L.l01 L.l02 L.l11 L.l12 L.l22)
    (u v : ℤ) (s : ℝ × ℝ) (hs : s = ((u : ℝ) / 3 + 1 / 3, (v : ℝ) / 3 + 1 / 3)) :
    Q.q (aff a D E s - aff a D E (1 / 3, 1 / 3)) * (9 * S) = offR L u v := by
  obtain ⟨-, -, -, h11, h12, h22⟩ := h
  have e : aff a D E s - aff a D E (1 / 3, 1 / 3) = 0 + ((u : ℝ) / 3) • D + ((v : ℝ) / 3) • E := by
    subst hs; ext i; simp [aff]; ring
  rw [e, QF.q_aff]; simp only [offR]; push_cast
  rw [← h11, ← h12, ← h22]
  have h0 : Q.q 0 = 0 := by simp [QF.q, QF.bil]
  have h0D : Q.bil 0 D = 0 := by simp [QF.bil]
  have h0E : Q.bil 0 E = 0 := by simp [QF.bil]
  rw [h0, h0D, h0E]; ring

/-! ### Integer helpers -/

theorem nat_div_bounds (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b < (a / b : ℕ) + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  have e : (a : ℝ) = b * (a / b : ℕ) + (a % b : ℕ) := by exact_mod_cast h1.symm
  constructor
  · rw [le_div_iff₀ hb', e]; have : (0:ℝ) ≤ (a % b : ℕ) := by positivity
    nlinarith
  · rw [div_lt_iff₀ hb', e]; have : ((a % b : ℕ) : ℝ) < b := by exact_mod_cast h2
    nlinarith

/-- The Nat parts reconstruct `nodeN`. -/
theorem node_parts (L : LQ) (h00 : 0 ≤ L.l00) (h11 : 0 ≤ L.l11) (h22 : 0 ≤ L.l22) (n : GNode) :
    ((nodeP (toLN L) (toFN n) : ℕ) : ℤ) - (nodeM (toLN L) (toFN n) : ℕ) = nodeN L n.a n.b n.m := by
  simp only [nodeP, nodeM, toLN, toFN, nodeN]
  have e1 := Int.toNat_sub_toNat_neg L.l01
  have e2 := Int.toNat_sub_toNat_neg L.l02
  have e3 := Int.toNat_sub_toNat_neg L.l12
  have f0 : (L.l00.toNat : ℤ) = L.l00 := Int.toNat_of_nonneg h00
  have f1 : (L.l11.toNat : ℤ) = L.l11 := Int.toNat_of_nonneg h11
  have f2 : (L.l22.toNat : ℤ) = L.l22 := Int.toNat_of_nonneg h22
  push_cast
  rw [f0, f1, f2]
  linear_combination (2 * (n.m : ℤ) * n.a) * e1 + (2 * (n.m : ℤ) * n.b) * e2 + (2 * (n.a : ℤ) * n.b) * e3

/-- The real value of one node term (`k = 2`, before rounding). -/
noncomputable def nt2 (L : LQ) (n : GNode) : ℝ :=
  (n.W : ℝ) * (n.m : ℝ) ^ 2 * 2 ^ KB / (nodeN L n.a n.b n.m : ℝ)

theorem sum2_spec (L : LQ) (h00 : 0 ≤ L.l00) (h11 : 0 ≤ L.l11) (h22 : 0 ≤ L.l22) :
    ∀ (xs : List GNode) (p0 n0 p n : ℕ), sum2 (toLN L) (xs.map toFN) p0 n0 = some (p, n) →
      (∀ x ∈ xs, 0 < nodeN L x.a x.b x.m) ∧
      ((p : ℝ) - p0) - ((n : ℝ) - n0) - (xs.filter fun x => decide (x.W < 0)).length ≤ (xs.map (nt2 L)).sum ∧
      (xs.map (nt2 L)).sum ≤ ((p : ℝ) - p0) + (xs.filter fun x => decide (0 ≤ x.W)).length - ((n : ℝ) - n0)
  | [], p0, n0, p, n, h => by
    simp only [List.map_nil, sum2, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | x :: xs, p0, n0, p, n, h => by
    simp only [List.map_cons, sum2] at h
    set P := nodeP (toLN L) (toFN x)
    set M := nodeM (toLN L) (toFN x)
    cases hc : (Nat.blt M P && !(Nat.beq p0 1) && !(Nat.beq n0 1))
    · rw [hc] at h; simp at h
    rw [hc] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hc
    have hMP : M < P := hc.1.1
    have hN := node_parts L h00 h11 h22 x
    have hNpos : 0 < nodeN L x.a x.b x.m := by rw [← hN]; omega
    have hNr : ((P - M : ℕ) : ℝ) = (nodeN L x.a x.b x.m : ℝ) := by
      rw [← hN]; push_cast [Nat.cast_sub (le_of_lt hMP)]; ring
    have hPM : 0 < P - M := by omega
    obtain ⟨b1, b2⟩ := nat_div_bounds (toFN x).w2 (P - M) hPM
    have hw2 : ((toFN x).w2 : ℝ) = (x.W.natAbs : ℝ) * (x.m : ℝ) ^ 2 * 2 ^ KB := by
      simp only [toFN, Nat.shiftLeft_eq]; push_cast; ring
    rw [hNr, hw2] at b1 b2
    have hnt : nt2 L x = (if x.W < 0 then -1 else 1) * ((x.W.natAbs : ℝ) * (x.m : ℝ) ^ 2 * 2 ^ KB /
        (nodeN L x.a x.b x.m : ℝ)) := by
      simp only [nt2]
      split_ifs with hw
      · have h1 := Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hw))
        rw [Int.natAbs_neg] at h1
        have : (x.W : ℝ) = -((x.W.natAbs : ℤ) : ℝ) := by
          rw [show ((x.W.natAbs : ℤ) : ℝ) = ((-x.W : ℤ) : ℝ) by rw [h1]]; push_cast; ring
        rw [this, Int.cast_natCast]; ring
      · have h1 := Int.natAbs_of_nonneg (not_lt.mp hw)
        have : (x.W : ℝ) = ((x.W.natAbs : ℤ) : ℝ) := by rw [h1]
        rw [this, Int.cast_natCast]; ring
    by_cases hneg : x.W < 0
    · have hx : (toFN x).neg = true := by simp [toFN, hneg]
      rw [hx, cond_true] at h
      obtain ⟨ih1, ih2, ih3⟩ := sum2_spec L h00 h11 h22 xs _ _ _ _ h
      refine ⟨fun y hy => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy; exact hNpos; exact ih1 y hy
      · simp only [List.map_cons, List.sum_cons, List.filter_cons, hneg, decide_true, if_true,
          List.length_cons, hnt]
        push_cast at ih2 ⊢; nlinarith
      · simp only [List.map_cons, List.sum_cons, List.filter_cons, hneg, decide_true, if_true,
          show ¬ (0 ≤ x.W) by omega, decide_false, if_false, hnt]
        push_cast at ih3 ⊢; nlinarith
    · have hx : (toFN x).neg = false := by simp [toFN, hneg]
      rw [hx, cond_false] at h
      obtain ⟨ih1, ih2, ih3⟩ := sum2_spec L h00 h11 h22 xs _ _ _ _ h
      refine ⟨fun y hy => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy; exact hNpos; exact ih1 y hy
      · simp only [List.map_cons, List.sum_cons, List.filter_cons, hneg, decide_false, if_false, hnt]
        push_cast at ih2 ⊢; nlinarith
      · simp only [List.map_cons, List.sum_cons, List.filter_cons, show (0 ≤ x.W) by omega, decide_true,
          if_true, List.length_cons, hneg, if_false, hnt]
        push_cast at ih3 ⊢; nlinarith

/-- `⌈a/b⌉` as `(a + b - 1) / b`. -/
theorem nat_ceil_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [div_le_iff₀ hb']
  have : a ≤ b * ((a + b - 1) / b) := by omega
  have : (a : ℝ) ≤ b * (((a + b - 1) / b : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem nat_ceil_ge' (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (((a + (b - 1)) / b : ℕ) : ℝ) := by
  rw [← Nat.add_sub_assoc hb]; exact nat_ceil_ge a b hb

/-- From the verified square root: `r ≤ 2^K / √N < r + 1`. -/
theorem isqrt_bounds (K N r : ℕ) (hN : 0 < N) (h1 : r * r ≤ 2 ^ (2 * K) / N)
    (h2 : 2 ^ (2 * K) / N < (r + 1) * (r + 1)) :
    (r : ℝ) ≤ 2 ^ K / Real.sqrt N ∧ 2 ^ K / Real.sqrt N < r + 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN'
  obtain ⟨b1, b2⟩ := nat_div_bounds (2 ^ (2 * K)) N hN
  have e : (2 : ℝ) ^ K / Real.sqrt N = Real.sqrt ((2 : ℝ) ^ (2 * K) / N) := by
    rw [Real.sqrt_div (by positivity), show (2:ℝ) ^ (2 * K) = (2 ^ K) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [e]
  push_cast at b1 b2
  constructor
  · rw [show (r : ℝ) = Real.sqrt ((r : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : ((r * r : ℕ) : ℝ) ≤ ((2 ^ (2 * K) / N : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; nlinarith
  · rw [show (r : ℝ) + 1 = Real.sqrt (((r : ℝ) + 1) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : ((2 ^ (2 * K) / N : ℕ) : ℝ) + 1 ≤ (((r + 1) * (r + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; nlinarith

/-- The real value of one node term (`k = 1`, before rounding). -/
noncomputable def nt1 (L : LQ) (j : ℕ) (n : GNode) : ℝ :=
  (n.W : ℝ) * n.m * 2 ^ KB1 / (2 ^ j * Real.sqrt (nodeN L n.a n.b n.m : ℝ))

theorem W_real (W : ℤ) : (W : ℝ) = (if W < 0 then -1 else 1) * (W.natAbs : ℝ) := by
  split_ifs with hw
  · have h1 := Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hw))
    rw [Int.natAbs_neg] at h1
    rw [← Int.cast_natCast, h1]
    push_cast; ring
  · have h1 := Int.natAbs_of_nonneg (not_lt.mp hw)
    rw [← Int.cast_natCast, h1]
    ring

theorem sum1_spec (L : LQ) (h00 : 0 ≤ L.l00) (h11 : 0 ≤ L.l11) (h22 : 0 ≤ L.l22) (j g0 : ℕ) :
    ∀ (xs : List GNode) (p0 n0 cp0 cn0 p n cp cn : ℕ),
      sum1 (toLN L) j g0 (xs.map toFN) p0 n0 cp0 cn0 = some (p, n, cp, cn) →
      (∀ x ∈ xs, 0 < nodeN L x.a x.b x.m) ∧
      ((p : ℝ) - p0) - ((cn : ℝ) - cn0) ≤ (xs.map (nt1 L j)).sum ∧
      (xs.map (nt1 L j)).sum ≤ ((cp : ℝ) - cp0) - ((n : ℝ) - n0)
  | [], p0, n0, cp0, cn0, p, n, cp, cn, h => by
    simp only [List.map_nil, sum1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp
  | x :: xs, p0, n0, cp0, cn0, p, n, cp, cn, h => by
    simp only [List.map_cons, sum1] at h
    set P := nodeP (toLN L) (toFN x)
    set M := nodeM (toLN L) (toFN x)
    set Mv := 2 ^ (2 * KB1) / (P - M)
    set r := isqrtN 64 Mv (g0 * 3 / (toFN x).m + 1)
    cases hc : (Nat.blt M P && Nat.ble (r * r) Mv && Nat.blt Mv ((r + 1) * (r + 1)) &&
        !(Nat.beq p0 1) && !(Nat.beq n0 1))
    · rw [hc] at h; simp at h
    rw [hc] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨hMP, hr1⟩, hr2⟩, -⟩, -⟩ := hc
    have hN := node_parts L h00 h11 h22 x
    have hNpos : 0 < nodeN L x.a x.b x.m := by rw [← hN]; omega
    have hNr : ((P - M : ℕ) : ℝ) = (nodeN L x.a x.b x.m : ℝ) := by
      rw [← hN]; push_cast [Nat.cast_sub (le_of_lt hMP)]; ring
    have hPM : 0 < P - M := by omega
    obtain ⟨s1, s2⟩ := isqrt_bounds KB1 (P - M) r hPM hr1 hr2
    rw [hNr] at s1 s2
    have hH : (0 : ℝ) < 2 ^ j := by positivity
    have hw1 : ((toFN x).w1 : ℝ) = (x.W.natAbs : ℝ) * x.m := by simp [toFN]
    -- v = |W| m 2^K / (2^j √N)
    set v := (x.W.natAbs : ℝ) * x.m * (2 ^ KB1 / Real.sqrt (nodeN L x.a x.b x.m : ℝ)) / 2 ^ j
    have hv : nt1 L j x = (if x.W < 0 then -1 else 1) * v := by
      simp only [nt1, v]; rw [W_real x.W]; ring
    have hA0 : (0 : ℝ) ≤ (x.W.natAbs : ℝ) * x.m := by positivity
    have hfl : ((((toFN x).w1 * r) >>> j : ℕ) : ℝ) ≤ v := by
      rw [Nat.shiftRight_eq_div_pow]
      obtain ⟨c1, -⟩ := nat_div_bounds ((toFN x).w1 * r) (2 ^ j) (by positivity)
      push_cast at c1; rw [hw1] at c1
      calc _ ≤ (x.W.natAbs : ℝ) * x.m * r / 2 ^ j := c1
        _ ≤ v := by
          simp only [v]; apply div_le_div_of_nonneg_right _ (le_of_lt hH)
          exact mul_le_mul_of_nonneg_left s1 hA0
    have hce : v ≤ ((((toFN x).w1 * (r + 1) + 2 ^ j - 1) >>> j : ℕ) : ℝ) := by
      rw [Nat.shiftRight_eq_div_pow]
      have c2 := nat_ceil_ge ((toFN x).w1 * (r + 1)) (2 ^ j) (by positivity)
      push_cast at c2; rw [hw1] at c2
      calc v ≤ (x.W.natAbs : ℝ) * x.m * (r + 1) / 2 ^ j := by
            simp only [v]; apply div_le_div_of_nonneg_right _ (le_of_lt hH)
            exact mul_le_mul_of_nonneg_left (le_of_lt s2) hA0
        _ ≤ _ := c2
    by_cases hneg : x.W < 0
    · have hx : (toFN x).neg = true := by simp [toFN, hneg]
      rw [hx, cond_true] at h
      obtain ⟨ih1, ih2, ih3⟩ := sum1_spec L h00 h11 h22 j g0 xs _ _ _ _ _ _ _ _ h
      refine ⟨fun y hy => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy; exact hNpos; exact ih1 y hy
      · simp only [List.map_cons, List.sum_cons, hv, hneg, if_true]
        push_cast at ih2 ⊢; linarith
      · simp only [List.map_cons, List.sum_cons, hv, hneg, if_true]
        push_cast at ih3 ⊢; linarith
    · have hx : (toFN x).neg = false := by simp [toFN, hneg]
      rw [hx, cond_false] at h
      obtain ⟨ih1, ih2, ih3⟩ := sum1_spec L h00 h11 h22 j g0 xs _ _ _ _ _ _ _ _ h
      refine ⟨fun y hy => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy; exact hNpos; exact ih1 y hy
      · simp only [List.map_cons, List.sum_cons, hv, hneg, if_false]
        push_cast at ih2 ⊢; linarith
      · simp only [List.map_cons, List.sum_cons, hv, hneg, if_false]
        push_cast at ih3 ⊢; linarith

/-! ### One leaf -/

theorem cond_some {α : Type*} {b : Bool} {x : Option α} {v : α} (h : (bif b then x else none) = some v) :
    b = true ∧ x = some v := by
  cases b <;> simp_all

/-- The output scale `2^K WCc / sD^k`. -/
noncomputable def SK (k : ℕ) (sD : ℝ) : ℝ := 2 ^ (if k = 2 then KB else KB1) * WCc / sD ^ k

theorem gAbs_real (r : List GNode) :
    (r.map fun n => |(n.W : ℝ) / WCc|).sum = (gAbs r : ℝ) / WCc := by
  simp only [gAbs]
  induction r with
  | nil => simp
  | cons n r ih =>
    simp only [List.map_cons, List.sum_cons, ih]; push_cast
    rw [abs_div, Nat.abs_cast, add_div, Int.cast_natAbs]; simp [WCc]

theorem phiB_eq (d tn : ℕ) (h : tn < 2 ^ TB) :
    phiB d ((tn : ℝ) / 2 ^ TB) = (phiN d tn : ℝ) / phiD d tn := by
  have hT : (0 : ℝ) < 2 ^ TB := by positivity
  have htn : (tn : ℝ) < 2 ^ TB := by exact_mod_cast h
  have h1 : (2 : ℝ) ^ TB - tn ≠ 0 := by linarith
  have h2 : ((2 ^ TB - tn : ℕ) : ℝ) = 2 ^ TB - tn := by push_cast [Nat.cast_sub (le_of_lt h)]; ring
  simp only [phiB, phiN, phiD]
  push_cast [h2]
  have h3 : (1 : ℝ) - tn / 2 ^ TB = (2 ^ TB - tn) / 2 ^ TB := by field_simp
  rw [h3, div_pow, div_pow, div_pow, pow_mul]
  field_simp
  ring

theorem ruleSum_map (WC : ℕ) (r : List GNode) (g : ℝ × ℝ → ℝ) (c : ℝ) :
    c * ruleSum WC r g = (r.map fun n => c * (((n.W : ℝ) / WC) * g n.pt)).sum := by
  simp only [ruleSum]; rw [← List.sum_map_mul_left]

theorem fk2_eq (Q : QF) (x : E3) (h : 0 < Q.q x) : Q.fk 2 x = 1 / Q.q x := by
  unfold QF.fk; rw [inv_pow, Real.sq_sqrt (le_of_lt h), one_div]

theorem fk1_eq (Q : QF) (x : E3) : Q.fk 1 x = 1 / Real.sqrt (Q.q x) := by
  unfold QF.fk; rw [pow_one, one_div]

theorem leafCond_spec {L : LQ} {tn : ℕ} (h : leafCond L tn = true) :
    tn < 2 ^ TB ∧ 0 < nodeN L 1 1 3 ∧ 0 ≤ L.l00 ∧ 0 ≤ L.l11 ∧ 0 ≤ L.l22 ∧
      Rmax L * ((2 ^ (2 * TB) : ℕ) : ℤ) ≤ ((tn * tn : ℕ) : ℤ) * nodeN L 1 1 3 := by
  simp only [leafCond, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The geometric content of `leafCond`: positivity on the leaf and the leaf bound. -/
theorem leaf_geom (Q : QF) {a D E : E3} {S : ℝ} (hS0 : 0 < S) {L : LQ}
    (hGL : GramOK Q a D E S L.l00 L.l01 L.l02 L.l11 L.l12 L.l22) {tn : ℕ} (hc : leafCond L tn = true) :
    Q.q (aff a D E (1 / 3, 1 / 3)) * (9 * S) = nodeN L 1 1 3 ∧
    (∀ s ∈ T2, 0 < Q.q (aff a D E s)) ∧
    ∀ {k d M : ℕ} {r : List GNode}, (k = 1 ∨ k = 2) → ruleOK d WCc M r = true →
      |(∫ s in T2, Q.fk k (aff a D E s)) - ruleSum WCc r (fun s => Q.fk k (aff a D E s))| ≤
        (1 / 2 + (gAbs r : ℝ) / WCc) *
          ((phiN d tn : ℝ) / phiD d tn * (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ k) := by
  obtain ⟨htn, hNc, h00, h11, h22, hRt⟩ := leafCond_spec hc
  set c := aff a D E (1 / 3, 1 / 3)
  have hcq : Q.q c * (9 * S) = nodeN L 1 1 3 := by
    have := node_q Q hGL 1 1 3 (by norm_num)
    simp only [Int.cast_one, Int.cast_ofNat] at this
    rw [show (3 : ℝ) ^ 2 * S = 9 * S by ring] at this; exact this
  have hNcR : (0 : ℝ) < nodeN L 1 1 3 := by exact_mod_cast hNc
  have hcpos : 0 < Q.q c := by
    have : 0 < Q.q c * (9 * S) := by rw [hcq]; exact hNcR
    exact pos_of_mul_pos_left this (by positivity)
  set t : ℝ := (tn : ℝ) / 2 ^ TB
  have ht0 : 0 ≤ t := by positivity
  have htn' : (tn : ℝ) < 2 ^ TB := by exact_mod_cast htn
  have ht1 : t < 1 := by rw [div_lt_one (by positivity)]; exact htn'
  have hR'' : ((Rmax L : ℤ) : ℝ) * 2 ^ (2 * TB) ≤ (tn : ℝ) ^ 2 * (nodeN L 1 1 3 : ℝ) := by
    have : ((Rmax L : ℤ) : ℝ) * ((2 ^ (2 * TB) : ℕ) : ℝ) ≤ ((tn * tn : ℕ) : ℝ) * (nodeN L 1 1 3 : ℝ) := by
      exact_mod_cast hRt
    push_cast at this; rw [sq]; linarith
  have hvert : ∀ u v : ℤ, offR L u v ≤ Rmax L → ∀ s, s = ((u : ℝ) / 3 + 1 / 3, (v : ℝ) / 3 + 1 / 3) →
      Q.q (aff a D E s - c) ≤ t ^ 2 * Q.q c := by
    intro u v hle s hs
    have ho := off_q Q hGL u v s hs
    have hle' : (offR L u v : ℝ) ≤ ((Rmax L : ℤ) : ℝ) := by exact_mod_cast hle
    have key : Q.q (aff a D E s - c) * (9 * S) * 2 ^ (2 * TB) ≤ (tn : ℝ) ^ 2 * (Q.q c * (9 * S)) := by
      rw [ho, hcq]
      exact le_trans (mul_le_mul_of_nonneg_right hle' (by positivity)) hR''
    have key' : (Q.q (aff a D E s - c) * (2 ^ TB) ^ 2) * (9 * S) ≤ ((tn : ℝ) ^ 2 * Q.q c) * (9 * S) := by
      have e1 : Q.q (aff a D E s - c) * (9 * S) * 2 ^ (2 * TB) =
          (Q.q (aff a D E s - c) * (2 ^ TB) ^ 2) * (9 * S) := by ring
      have e2 : (tn : ℝ) ^ 2 * (Q.q c * (9 * S)) = ((tn : ℝ) ^ 2 * Q.q c) * (9 * S) := by ring
      rw [← e1, ← e2]; exact key
    have key'' := le_of_mul_le_mul_right key' (by positivity)
    simp only [t, div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact key''
  have hv0 := hvert (-1) (-1) (le_max_left _ _) (0, 0) (by norm_num)
  have hv1 := hvert 2 (-1) (le_trans (le_max_left _ _) (le_max_right _ _)) (1, 0) (by norm_num)
  have hv2 := hvert (-1) 2 (le_trans (le_max_right _ _) (le_max_right _ _)) (0, 1) (by norm_num)
  have hy := leaf_near Q a D E hv0 hv1 hv2
  refine ⟨hcq, leaf_pos Q a D E ht0 ht1 hcpos hy, ?_⟩
  intro k d M r hk hR
  have hB := leaf_bound Q hk hR a D E ht0 ht1 hcpos hv0 hv1 hv2
  rwa [gAbs_real, phiB_eq d tn htn] at hB

theorem hm_rule {d : ℕ} (hR : ruleOK d WCc (gmM d) (gmRule d) = true) : ∀ n ∈ gmRule d, (0 : ℝ) < n.m := by
  intro n hn
  simp only [ruleOK, nodesOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
  exact_mod_cast (hR.1.1.1 n hn).1.1

theorem hq_rule (Q : QF) {a D E : E3} {S : ℝ} {L : LQ} (hGL : GramOK Q a D E S L.l00 L.l01 L.l02 L.l11 L.l12 L.l22)
    {d : ℕ} (hR : ruleOK d WCc (gmM d) (gmRule d) = true) :
    ∀ n ∈ gmRule d, Q.q (aff a D E n.pt) * ((n.m : ℝ) ^ 2 * S) = nodeN L n.a n.b n.m := by
  intro n hn
  have := node_q Q hGL n.a n.b n.m (by push_cast; exact ne_of_gt (hm_rule hR n hn))
  simp only [Int.cast_natCast] at this
  exact this

theorem phiD_pos {d tn : ℕ} (h : tn < 2 ^ TB) : 0 < phiD d tn := by
  simp only [phiD]
  exact Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (Nat.sub_pos_of_lt h) _)

theorem WCc_pos : (0 : ℝ) < WCc := by norm_num [WCc]

theorem err2_ge (d tn Nc : ℕ) (hNc : 0 < Nc) (htn : tn < 2 ^ TB) :
    ((9 * (WCc + 2 * gAbs (gmRule d)) * phiN d tn * 2 ^ KB : ℕ) : ℝ) / ((2 * phiD d tn * Nc : ℕ) : ℝ) ≤
      (err2 d tn Nc : ℝ) := by
  unfold err2
  exact nat_ceil_ge' _ _ (Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) (phiD_pos (d := d) htn)) hNc)

theorem err1_ge (d tn rc j : ℕ) (htn : tn < 2 ^ TB) :
    ((3 * (WCc + 2 * gAbs (gmRule d)) * phiN d tn * (rc + 1) : ℕ) : ℝ) / ((2 * phiD d tn * 2 ^ j : ℕ) : ℝ) ≤
      (err1 d tn rc j : ℝ) := by
  unfold err1
  exact nat_ceil_ge' _ _ (Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) (phiD_pos (d := d) htn))
    (pow_pos (by norm_num : (0:ℕ) < 2) j))

/-- **Leaf, `k = 2`.** -/
theorem leaf2_sound (Q : QF) {a D E : E3} {S : ℝ} (hS0 : 0 < S) {L : LQ}
    (hGL : GramOK Q a D E S L.l00 L.l01 L.l02 L.l11 L.l12 L.l22) {tn d : ℕ} (hc : leafCond L tn = true)
    (hR : ruleOK d WCc (gmM d) (gmRule d) = true) {lo hi : ℤ} (h : leaf2 L d tn = some (lo, hi)) :
    (lo : ℝ) ≤ 2 ^ KB * WCc / S * ∫ s in T2, Q.fk 2 (aff a D E s) ∧
      2 ^ KB * WCc / S * (∫ s in T2, Q.fk 2 (aff a D E s)) ≤ hi := by
  obtain ⟨htn, hNc, h00, h11, h22, -⟩ := leafCond_spec hc
  obtain ⟨hcq, hpos, hB⟩ := leaf_geom Q hS0 hGL hc
  have hB2 := abs_sub_le_iff.mp (hB (k := 2) (Or.inr rfl) hR)
  simp only [leaf2] at h
  split at h
  · rename_i p n hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hNp, hlo, hhi⟩ := sum2_spec L h00 h11 h22 (gmRule d) 0 0 p n hs
    set C : ℝ := 2 ^ KB * WCc / S
    have hC0 : 0 ≤ C := by positivity
    have hRS : C * ruleSum WCc (gmRule d) (fun s => Q.fk 2 (aff a D E s)) = ((gmRule d).map (nt2 L)).sum := by
      rw [ruleSum_map]; congr 1
      apply List.map_congr_left
      intro n hn
      have hq := hq_rule Q hGL hR n hn
      have hNr : (0 : ℝ) < nodeN L n.a n.b n.m := by exact_mod_cast hNp n hn
      have hmn := hm_rule hR n hn
      have hqp : 0 < Q.q (aff a D E n.pt) := by
        have : 0 < Q.q (aff a D E n.pt) * ((n.m : ℝ) ^ 2 * S) := by rw [hq]; exact hNr
        exact pos_of_mul_pos_left this (by positivity)
      rw [fk2_eq Q _ hqp]
      have hqv : Q.q (aff a D E n.pt) = nodeN L n.a n.b n.m / ((n.m : ℝ) ^ 2 * S) := by
        rw [← hq]; field_simp
      rw [hqv]; simp only [C, nt2]
      have := WCc_pos
      field_simp; ring
    have hNcR : (0 : ℝ) < nodeN L 1 1 3 := by exact_mod_cast hNc
    have hNcn : (((nodeN L 1 1 3).toNat : ℕ) : ℝ) = (nodeN L 1 1 3 : ℝ) := by
      have : (((nodeN L 1 1 3).toNat : ℤ)) = nodeN L 1 1 3 := Int.toNat_of_nonneg (le_of_lt hNc)
      exact_mod_cast this
    have hNc0 : 0 < (nodeN L 1 1 3).toNat := by exact_mod_cast (show (0:ℝ) < ((nodeN L 1 1 3).toNat : ℕ) by rw [hNcn]; exact hNcR)
    have hErr : C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
        (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 2)) ≤ (err2 d tn (nodeN L 1 1 3).toNat : ℝ) := by
      have hpd : (0 : ℝ) < phiD d tn := by exact_mod_cast phiD_pos htn
      have hcp : 0 < Q.q (aff a D E (1 / 3, 1 / 3)) := by
        have : 0 < Q.q (aff a D E (1 / 3, 1 / 3)) * (9 * S) := by rw [hcq]; exact hNcR
        exact pos_of_mul_pos_left this (by positivity)
      rw [inv_pow, Real.sq_sqrt (le_of_lt hcp)]
      have hqc : Q.q (aff a D E (1 / 3, 1 / 3)) = nodeN L 1 1 3 / (9 * S) := by rw [← hcq]; field_simp
      rw [hqc]
      refine le_trans (le_of_eq ?_) (err2_ge d tn _ hNc0 htn)
      push_cast; rw [hNcn]
      simp only [C]
      have := WCc_pos
      field_simp; ring
    have hW := WCc_pos
    unfold cntNeg cntPos
    constructor
    · have : C * ((∫ s in T2, Q.fk 2 (aff a D E s)) - ruleSum WCc (gmRule d) (fun s => Q.fk 2 (aff a D E s))) ≥
          -(C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
          (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 2))) := by
        rw [ge_iff_le, neg_le, ← mul_neg]
        exact mul_le_mul_of_nonneg_left (by linarith [hB2.2]) hC0
      rw [mul_sub, hRS] at this
      push_cast at hlo ⊢
      linarith
    · have : C * ((∫ s in T2, Q.fk 2 (aff a D E s)) - ruleSum WCc (gmRule d) (fun s => Q.fk 2 (aff a D E s))) ≤
          C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
          (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 2)) :=
        mul_le_mul_of_nonneg_left hB2.1 hC0
      rw [mul_sub, hRS] at this
      push_cast at hhi ⊢
      linarith
  · simp at h

/-- **Leaf, `k = 1`.** -/
theorem leaf1_sound (Q : QF) {a D E : E3} {sD : ℝ} (hsD : 0 < sD) {j : ℕ} {L : LQ}
    (hGL : GramOK Q a D E ((2 : ℝ) ^ j * 2 ^ j * sD ^ 2) L.l00 L.l01 L.l02 L.l11 L.l12 L.l22) {tn d : ℕ}
    (hc : leafCond L tn = true) (hR : ruleOK d WCc (gmM d) (gmRule d) = true) {lo hi : ℤ}
    (h : leaf1 L d tn j = some (lo, hi)) :
    (lo : ℝ) ≤ 2 ^ KB1 * WCc / (sD * (2 ^ j * 2 ^ j)) * ∫ s in T2, Q.fk 1 (aff a D E s) ∧
      2 ^ KB1 * WCc / (sD * (2 ^ j * 2 ^ j)) * (∫ s in T2, Q.fk 1 (aff a D E s)) ≤ hi := by
  set S : ℝ := (2 : ℝ) ^ j * 2 ^ j * sD ^ 2 with hS
  have hS0 : 0 < S := by positivity
  obtain ⟨htn, hNc, h00, h11, h22, -⟩ := leafCond_spec hc
  obtain ⟨hcq, hpos, hB⟩ := leaf_geom Q hS0 hGL hc
  have hB1 := abs_sub_le_iff.mp (hB (k := 1) (Or.inl rfl) hR)
  simp only [leaf1] at h
  obtain ⟨hcr, h'⟩ := cond_some h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hcr
  split at h'
  · rename_i p n cp cn hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨hNp, hlo, hhi⟩ := sum1_spec L h00 h11 h22 j _ (gmRule d) 0 0 0 0 p n cp cn hs
    set rc := rcOf (nodeN L 1 1 3).toNat
    have hNcR : (0 : ℝ) < nodeN L 1 1 3 := by exact_mod_cast hNc
    have hNcn : (((nodeN L 1 1 3).toNat : ℕ) : ℝ) = (nodeN L 1 1 3 : ℝ) := by
      have : (((nodeN L 1 1 3).toNat : ℤ)) = nodeN L 1 1 3 := Int.toNat_of_nonneg (le_of_lt hNc)
      exact_mod_cast this
    have hNc0 : 0 < (nodeN L 1 1 3).toNat := by
      exact_mod_cast (show (0:ℝ) < ((nodeN L 1 1 3).toNat : ℕ) by rw [hNcn]; exact hNcR)
    obtain ⟨rc1, rc2⟩ := isqrt_bounds KB1 _ rc hNc0 hcr.1 hcr.2
    rw [hNcn] at rc1 rc2
    set C : ℝ := 2 ^ KB1 * WCc / (sD * (2 ^ j * 2 ^ j))
    have hC0 : 0 ≤ C := div_nonneg (mul_nonneg (by positivity) (le_of_lt WCc_pos))
      (mul_nonneg (le_of_lt hsD) (by positivity))
    have hW := WCc_pos
    have hH : (0 : ℝ) < 2 ^ j := by positivity
    have hRS : C * ruleSum WCc (gmRule d) (fun s => Q.fk 1 (aff a D E s)) = ((gmRule d).map (nt1 L j)).sum := by
      rw [ruleSum_map]; congr 1
      apply List.map_congr_left
      intro n hn
      have hq := hq_rule Q hGL hR n hn
      have hNr : (0 : ℝ) < nodeN L n.a n.b n.m := by exact_mod_cast hNp n hn
      have hmn := hm_rule hR n hn
      have hqv : Q.q (aff a D E n.pt) = nodeN L n.a n.b n.m / ((n.m : ℝ) ^ 2 * S) := by
        rw [← hq]; field_simp
      rw [fk1_eq, hqv, hS, show (n.m : ℝ) ^ 2 * (2 ^ j * 2 ^ j * sD ^ 2) = ((n.m : ℝ) * 2 ^ j * sD) ^ 2 by ring,
        Real.sqrt_div (le_of_lt hNr), Real.sqrt_sq (by positivity)]
      simp only [C, nt1]
      have : Real.sqrt (nodeN L n.a n.b n.m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNr)
      field_simp; ring
    have hErr : C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
        (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 1)) ≤ (err1 d tn rc j : ℝ) := by
      have hpd : (0 : ℝ) < phiD d tn := by exact_mod_cast phiD_pos htn
      have hqc : Q.q (aff a D E (1 / 3, 1 / 3)) = nodeN L 1 1 3 / (9 * S) := by rw [← hcq]; field_simp
      rw [hqc, hS, show (9 : ℝ) * (2 ^ j * 2 ^ j * sD ^ 2) = (3 * 2 ^ j * sD) ^ 2 by ring,
        Real.sqrt_div (le_of_lt hNcR), Real.sqrt_sq (by positivity), pow_one]
      refine le_trans ?_ (err1_ge d tn rc j htn)
      have hsN : 0 < Real.sqrt (nodeN L 1 1 3 : ℝ) := Real.sqrt_pos.mpr hNcR
      push_cast
      have key : (2 : ℝ) ^ KB1 / Real.sqrt (nodeN L 1 1 3) ≤ rc + 1 := le_of_lt rc2
      have e : C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
          (Real.sqrt (nodeN L 1 1 3) / (3 * 2 ^ j * sD))⁻¹)) =
          3 * (WCc + 2 * gAbs (gmRule d)) * phiN d tn * (2 ^ KB1 / Real.sqrt (nodeN L 1 1 3)) /
            (2 * phiD d tn * 2 ^ j) := by
        simp only [C]; field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left key; positivity
    constructor
    · have : C * ((∫ s in T2, Q.fk 1 (aff a D E s)) - ruleSum WCc (gmRule d) (fun s => Q.fk 1 (aff a D E s))) ≥
          -(C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
          (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 1))) := by
        rw [ge_iff_le, neg_le, ← mul_neg]
        exact mul_le_mul_of_nonneg_left (by linarith [hB1.2]) hC0
      rw [mul_sub, hRS] at this
      push_cast at hlo ⊢
      linarith
    · have : C * ((∫ s in T2, Q.fk 1 (aff a D E s)) - ruleSum WCc (gmRule d) (fun s => Q.fk 1 (aff a D E s))) ≤
          C * ((1 / 2 + (gAbs (gmRule d) : ℝ) / WCc) * ((phiN d tn : ℝ) / phiD d tn *
          (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ 1)) :=
        mul_le_mul_of_nonneg_left hB1.1 hC0
      rw [mul_sub, hRS] at this
      push_cast at hhi ⊢
      linarith
  · simp at h'

/-- **Soundness of one leaf of the quadtree.** -/
theorem leafChk_sound (Q : QF) {a0 d1 d2 : E3} {sD : ℝ} (hsD : 0 < sD) {qc : QC}
    (hG : GramOK Q a0 d1 d2 (sD ^ 2) qc.q00 qc.q01 qc.q02 qc.q11 qc.q12 qc.q22)
    {k d tn j : ℕ} {p1 p2 : ℤ} {e : Bool} (hk : k = 1 ∨ k = 2)
    (hR : ruleOK d WCc (gmM d) (gmRule d) = true) {lo hi : ℤ}
    (h : leafChk qc k d tn j p1 p2 e = some (lo, hi)) :
    (∀ s ∈ T2, 0 < Q.q (aff a0 d1 d2 (lpt j p1 p2 e s))) ∧
    (lo : ℝ) ≤ SK k sD / 4 ^ j * ∫ s in T2, Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s)) ∧
    SK k sD / 4 ^ j * (∫ s in T2, Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s))) ≤ hi := by
  have hGL := gram_leaf Q hG j p1 p2 e
  have haff := aff_leaf a0 d1 d2 j p1 p2 e
  set L := leafLQ qc j p1 p2 e
  set a := aff a0 d1 d2 ((p1 : ℝ) / 2 ^ j, (p2 : ℝ) / 2 ^ j)
  set D := (epsR e / 2 ^ j) • d1
  set E := (epsR e / 2 ^ j) • d2
  have hS0 : (0 : ℝ) < 2 ^ j * 2 ^ j * sD ^ 2 := by positivity
  simp only [leafChk] at h
  obtain ⟨hc, h'⟩ := cond_some h
  have hc := ((Bool.and_eq_true _ _).mp hc).2
  obtain ⟨-, hpos, -⟩ := leaf_geom Q hS0 hGL hc
  refine ⟨fun s hs => by rw [← haff]; exact hpos s hs, ?_⟩
  have hint : (∫ s in T2, Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s))) = ∫ s in T2, Q.fk k (aff a D E s) := by
    congr 1; funext s; rw [haff]
  rw [hint]
  have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  rcases hk with rfl | rfl
  · simp only [show Nat.beq 1 2 = false from rfl, cond_false] at h'
    have := leaf1_sound Q hsD hGL hc hR h'
    have e : SK 1 sD / 4 ^ j = 2 ^ KB1 * WCc / (sD * (2 ^ j * 2 ^ j)) := by
      simp only [SK, show (1 : ℕ) ≠ 2 by norm_num, if_false, pow_one, h4]; field_simp
    rw [e]; exact this
  · simp only [show Nat.beq 2 2 = true from rfl, cond_true] at h'
    have := leaf2_sound Q hS0 hGL hc hR h'
    have e : SK 2 sD / 4 ^ j = 2 ^ KB * WCc / (2 ^ j * 2 ^ j * sD ^ 2) := by
      simp only [SK, if_true, h4]; field_simp; left; ring
    rw [e]; exact this

/-- The child parameters of the quadtree (`CheckDefs.treeChk`). -/
theorem lpt_child (j : ℕ) (p1 p2 : ℤ) (e : Bool) (s : ℝ × ℝ) :
    lpt j p1 p2 e (phiC 0 s) = lpt (j + 1) (2 * p1) (2 * p2) e s ∧
    lpt j p1 p2 e (phiC 1 s) = lpt (j + 1) (2 * p1 + (if e then -1 else 1)) (2 * p2) e s ∧
    lpt j p1 p2 e (phiC 2 s) = lpt (j + 1) (2 * p1) (2 * p2 + (if e then -1 else 1)) e s ∧
    lpt j p1 p2 e (phiC 3 s) = lpt (j + 1) (2 * p1 + (if e then -1 else 1)) (2 * p2 + (if e then -1 else 1)) (!e) s := by
  have h2 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  cases e <;> simp only [lpt, phiC, epsR, h2, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_true, if_false,
    Prod.mk.injEq] <;> push_cast <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> field_simp <;> ring

/-- **Soundness of the quadtree check.** -/
theorem treeChk_sound (Q : QF) {a0 d1 d2 : E3} {sD : ℝ} (hsD : 0 < sD) {qc : QC}
    (hG : GramOK Q a0 d1 d2 (sD ^ 2) qc.q00 qc.q01 qc.q02 qc.q11 qc.q12 qc.q22) {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hDeg : ∀ d ∈ degList, ruleOK d WCc (gmM d) (gmRule d) = true) :
    ∀ (t : QT) (j : ℕ) (p1 p2 : ℤ) (e : Bool) (lo hi : ℤ), treeChk qc k t j p1 p2 e = some (lo, hi) →
      (∀ s ∈ T2, 0 < Q.q (aff a0 d1 d2 (lpt j p1 p2 e s))) ∧
      (lo : ℝ) ≤ SK k sD / 4 ^ j * ∫ s in T2, Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s)) ∧
      SK k sD / 4 ^ j * (∫ s in T2, Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s))) ≤ hi := by
  intro t
  induction t with
  | leaf d tn =>
    intro j p1 p2 e lo hi h
    simp only [treeChk] at h
    have hd : degList.elem d = true := by
      simp only [leafChk] at h
      cases hb : degList.elem d
      · rw [hb] at h; simp at h
      · rfl
    have hR := hDeg d (by simpa using hd)
    exact leafChk_sound Q hsD hG hk hR (by simpa [leafChk, hd] using h)
  | node c0 c1 c2 c3 ih0 ih1 ih2 ih3 =>
    intro j p1 p2 e lo hi h
    simp only [treeChk] at h
    split at h
    · rename_i r0 r1 r2 r3 h0 h1 h2 h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨q0, l0, u0⟩ := ih0 _ _ _ _ _ _ h0
      obtain ⟨q1, l1, u1⟩ := ih1 _ _ _ _ _ _ h1
      obtain ⟨q2, l2, u2⟩ := ih2 _ _ _ _ _ _ h2
      obtain ⟨q3, l3, u3⟩ := ih3 _ _ _ _ _ _ h3
      have hc := fun s => lpt_child j p1 p2 e s
      have hpos : ∀ s ∈ T2, 0 < Q.q (aff a0 d1 d2 (lpt j p1 p2 e s)) := by
        intro s hs
        obtain ⟨c, hc'⟩ := T2_cover s hs
        obtain ⟨s', hs', rfl⟩ := SC_surj c s hc'
        have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by fin_cases c <;> simp
        rcases hc4 with rfl | rfl | rfl | rfl
        · rw [(hc s').1]; exact q0 s' hs'
        · rw [(hc s').2.1]; exact q1 s' hs'
        · rw [(hc s').2.2.1]; exact q2 s' hs'
        · rw [(hc s').2.2.2]; exact q3 s' hs'
      refine ⟨hpos, ?_⟩
      -- continuity on T2, then the split
      have hGL := gram_leaf Q hG j p1 p2 e
      have haff := aff_leaf a0 d1 d2 j p1 p2 e
      have hcont : ContinuousOn (fun s => Q.fk k (aff a0 d1 d2 (lpt j p1 p2 e s))) T2 := by
        have := leaf_cont Q k (aff a0 d1 d2 ((p1 : ℝ) / 2 ^ j, (p2 : ℝ) / 2 ^ j)) ((epsR e / 2 ^ j) • d1)
          ((epsR e / 2 ^ j) • d2) (fun s hs => by rw [haff]; exact hpos s hs)
        simpa only [haff] using this
      rw [integral_T2_split (integrableOn_T2 hcont), Fin.sum_univ_four]
      simp only [(hc _).1, (hc _).2.1, (hc _).2.2.1, (hc _).2.2.2]
      have h4 : SK k sD / (4 : ℝ) ^ (j + 1) = SK k sD / 4 ^ j * (1 / 4) := by ring
      rw [h4] at l0 l1 l2 l3 u0 u1 u2 u3
      push_cast
      constructor
      · have := add_le_add (add_le_add (add_le_add l0 l1) l2) l3
        exact le_trans this (le_of_eq (by ring))
      · have := add_le_add (add_le_add (add_le_add u0 u1) u2) u3
        exact le_trans (le_of_eq (by ring)) this
    · simp at h

end GW.Endpoint.Coulomb

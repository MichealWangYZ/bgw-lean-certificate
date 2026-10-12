/-
G2-coulomb (3/n): one quadtree leaf.

`QF` is a positive definite quadratic form on `E3 = Fin 3 → ℝ` (the metric `B`); `fk Q k x =
|x|_B^{-k}`. For an affine map `y s = a + s₁ D + s₂ E` of the triangle `T2`, centre
`c = y(1/3,1/3)`, and `t ∈ [0,1)` with `|y v - c|² ≤ t² |c|²` at the three vertices,
`leaf_bound` gives, for a cubature rule exact to degree `d` (`ruleOK`):

  |∫_{T2} fk (y s) ds - Σ_i w_i fk (y s_i)| ≤ (1/2 + Σ|w_i|) φ_d(t) |c|^{-k}    (k = 1, 2).

The proof: `|y s - c| ≤ t |c|` on `T2` (convexity), the Taylor polynomial of degree `d`
about `c` (`cW` for `k = 2`, `lV` for `k = 1`) is a polynomial in `s` of degree `≤ d`, the rule
integrates it exactly, and the remainder is `≤ φ_d(t) |c|^{-k}` pointwise.
-/
import GW.Endpoint.Coulomb.Series
import GW.Endpoint.Coulomb.Simplex

namespace GW.Endpoint.Coulomb

open MeasureTheory Set Finset

abbrev E3 := Fin 3 → ℝ

/-- A positive definite quadratic form on `E3`. -/
structure QF where
  M : Matrix (Fin 3) (Fin 3) ℝ
  symm : ∀ i j, M i j = M j i
  pos : ∀ x : E3, x ≠ 0 → 0 < ∑ i, ∑ j, M i j * x i * x j

namespace QF

variable (Q : QF)

/-- The bilinear form. -/
def bil (x y : E3) : ℝ := ∑ i, ∑ j, Q.M i j * x i * y j

/-- The quadratic form. -/
def q (x : E3) : ℝ := Q.bil x x

theorem bil_comm (x y : E3) : Q.bil x y = Q.bil y x := by
  simp only [bil]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Q.symm]; ring

theorem bil_add_left (x y z : E3) : Q.bil (x + y) z = Q.bil x z + Q.bil y z := by
  simp only [bil, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem bil_add_right (x y z : E3) : Q.bil x (y + z) = Q.bil x y + Q.bil x z := by
  rw [bil_comm, bil_add_left, bil_comm, Q.bil_comm z]

theorem bil_smul_left (r : ℝ) (x y : E3) : Q.bil (r • x) y = r * Q.bil x y := by
  simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem bil_smul_right (r : ℝ) (x y : E3) : Q.bil x (r • y) = r * Q.bil x y := by
  rw [bil_comm, bil_smul_left, bil_comm]

theorem bil_neg_left (x y : E3) : Q.bil (-x) y = - Q.bil x y := by
  rw [show -x = (-1 : ℝ) • x by simp, bil_smul_left]; ring

theorem bil_sub_left (x y z : E3) : Q.bil (x - y) z = Q.bil x z - Q.bil y z := by
  rw [sub_eq_add_neg, bil_add_left, bil_neg_left]; ring

theorem bil_sub_right (x y z : E3) : Q.bil x (y - z) = Q.bil x y - Q.bil x z := by
  rw [bil_comm, bil_sub_left, bil_comm, Q.bil_comm z]

theorem q_nonneg (x : E3) : 0 ≤ Q.q x := by
  by_cases h : x = 0
  · subst h; simp [q, bil]
  · exact le_of_lt (Q.pos x h)

theorem q_pos {x : E3} (h : x ≠ 0) : 0 < Q.q x := Q.pos x h

theorem q_add (x y : E3) : Q.q (x + y) = Q.q x + 2 * Q.bil x y + Q.q y := by
  simp only [q, bil_add_left, bil_add_right, Q.bil_comm y x]; ring

theorem q_smul (r : ℝ) (x : E3) : Q.q (r • x) = r ^ 2 * Q.q x := by
  simp only [q, bil_smul_left, bil_smul_right]; ring

theorem q_sub (x y : E3) : Q.q (x - y) = Q.q x - 2 * Q.bil x y + Q.q y := by
  rw [sub_eq_add_neg, q_add, show -y = (-1 : ℝ) • y by simp, bil_smul_right, q_smul]; ring

/-- Cauchy–Schwarz. -/
theorem cs (x y : E3) : Q.bil x y ^ 2 ≤ Q.q x * Q.q y := by
  by_cases hy : Q.q y = 0
  · have : y = 0 := by
      by_contra h; exact absurd hy (ne_of_gt (Q.q_pos h))
    subst this; simp [q, bil]
  · have hy' : 0 < Q.q y := lt_of_le_of_ne (Q.q_nonneg y) (Ne.symm hy)
    have h := Q.q_nonneg (x - (Q.bil x y / Q.q y) • y)
    rw [q_sub, bil_smul_right, q_smul] at h
    have e : Q.q x - 2 * (Q.bil x y / Q.q y * Q.bil x y) + (Q.bil x y / Q.q y) ^ 2 * Q.q y =
        Q.q x - Q.bil x y ^ 2 / Q.q y := by field_simp; ring
    have : Q.bil x y ^ 2 / Q.q y ≤ Q.q x := by linarith
    rw [div_le_iff₀ hy'] at this; linarith

/-- The norm `√q` is subadditive. -/
theorem sqrt_q_add (x y : E3) : Real.sqrt (Q.q (x + y)) ≤ Real.sqrt (Q.q x) + Real.sqrt (Q.q y) := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt (Q.q_nonneg x)
  have h2 := Real.sq_sqrt (Q.q_nonneg y)
  have hc := Q.cs x y
  have hb : Q.bil x y ≤ Real.sqrt (Q.q x) * Real.sqrt (Q.q y) := by
    have : |Q.bil x y| ≤ Real.sqrt (Q.q x) * Real.sqrt (Q.q y) := by
      rw [← Real.sqrt_mul (Q.q_nonneg x), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hc
    exact le_trans (le_abs_self _) this
  rw [q_add]; nlinarith

/-- Convexity along a segment. -/
theorem q_convex (u v : E3) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    Q.q (l • u + (1 - l) • v) ≤ l * Q.q u + (1 - l) * Q.q v := by
  have h := Q.q_nonneg (u - v)
  rw [q_add, q_smul, q_smul, bil_smul_left, bil_smul_right, q_sub] at *
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- Convexity over a triangle: `q` of a convex combination of three points. -/
theorem q_convex3 (u v w : E3) {l1 l2 : ℝ} (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : l1 + l2 ≤ 1) :
    Q.q ((1 - l1 - l2) • u + l1 • v + l2 • w) ≤ max (Q.q u) (max (Q.q v) (Q.q w)) := by
  set M := max (Q.q u) (max (Q.q v) (Q.q w))
  have hu : Q.q u ≤ M := le_max_left _ _
  have hv : Q.q v ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw : Q.q w ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases hs : l1 + l2 = 0
  · have e1 : l1 = 0 := by linarith
    have e2 : l2 = 0 := by linarith
    subst e1 e2; simpa using hu
  have hs' : 0 < l1 + l2 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
  -- (1-s) u + s ((l1/s) v + (l2/s) w)
  set s := l1 + l2
  have e : (1 - l1 - l2) • u + l1 • v + l2 • w = (1 - s) • u + s • ((l1 / s) • v + (1 - l1 / s) • w) := by
    have : 1 - l1 / s = l2 / s := by field_simp; ring
    rw [this, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ (ne_of_gt hs'),
      mul_div_cancel₀ _ (ne_of_gt hs')]
    simp only [s]; abel_nf
  rw [e]
  have hl : 0 ≤ l1 / s := div_nonneg h1 (le_of_lt hs')
  have hl' : l1 / s ≤ 1 := by rw [div_le_one hs']; simp only [s]; linarith
  have i1 := Q.q_convex v w hl hl'
  have i2 := Q.q_convex ((l1 / s) • v + (1 - l1 / s) • w) u (le_of_lt hs') h3
  rw [show (1 - s) • u + s • ((l1 / s) • v + (1 - l1 / s) • w) =
    s • ((l1 / s) • v + (1 - l1 / s) • w) + (1 - s) • u by abel]
  calc _ ≤ s * Q.q ((l1 / s) • v + (1 - l1 / s) • w) + (1 - s) * Q.q u := i2
    _ ≤ s * M + (1 - s) * M := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (le_of_lt hs')
          calc _ ≤ l1 / s * Q.q v + (1 - l1 / s) * Q.q w := i1
            _ ≤ l1 / s * M + (1 - l1 / s) * M := by
                apply add_le_add (mul_le_mul_of_nonneg_left hv hl)
                  (mul_le_mul_of_nonneg_left hw (by linarith))
            _ = M := by ring
        · exact mul_le_mul_of_nonneg_left hu (by linarith)
    _ = M := by ring

/-- `|x|_B^{-k}`. -/
noncomputable def fk (k : ℕ) (x : E3) : ℝ := (Real.sqrt (Q.q x))⁻¹ ^ k

theorem fk_nonneg (k : ℕ) (x : E3) : 0 ≤ Q.fk k x := by unfold fk; positivity

end QF

/-- The degree-`N` Taylor polynomial in terms of `α, β`: `k = 2` Chebyshev, `k = 1` Legendre. -/
noncomputable def tay (k N : ℕ) (α β : ℝ) : ℝ :=
  if k = 1 then ∑ n ∈ range (N + 1), lV α β n else ∑ n ∈ range (N + 1), cW α β n

/-- **Taylor bound in `E3`**: for `|y| ≤ t |c|`, `t < 1`,
`|fk (c + y) - |c|^{-k} tay(α, β)| ≤ φ_N(t) |c|^{-k}` with `α = 2⟨c,y⟩/|c|²`, `β = |y|²/|c|²`. -/
theorem QF.taylor (Q : QF) {k : ℕ} (hk : k = 1 ∨ k = 2) (N : ℕ) {c y : E3} {t : ℝ} (hc : 0 < Q.q c)
    (ht : 0 ≤ t) (ht1 : t < 1) (hy : Q.q y ≤ t ^ 2 * Q.q c) :
    |Q.fk k (c + y) - (Real.sqrt (Q.q c))⁻¹ ^ k * tay k N (2 * Q.bil c y / Q.q c) (Q.q y / Q.q c)| ≤
      phiB N t * (Real.sqrt (Q.q c))⁻¹ ^ k := by
  set α := 2 * Q.bil c y / Q.q c
  set β := Q.q y / Q.q c
  have hβt : β ≤ t ^ 2 := by simp only [β]; rw [div_le_iff₀ hc]; exact hy
  have hα : α ^ 2 ≤ 4 * β := by
    have hcs := Q.cs c y
    simp only [α, β]
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc (2 * Q.bil c y) ^ 2 = 4 * Q.bil c y ^ 2 := by ring
      _ ≤ 4 * (Q.q c * Q.q y) := by linarith
      _ = 4 * (Q.q y / Q.q c) * Q.q c ^ 2 := by field_simp; ring
  have hz : Q.q (c + y) = Q.q c * (1 + α + β) := by
    rw [QF.q_add]; simp only [α, β]; field_simp
  have hzl := z_lower ht hβt hα
  have hβ0 : 0 ≤ β := by nlinarith [sq_nonneg α]
  have hs1 : Real.sqrt β < 1 := by
    have : Real.sqrt β ≤ t := by
      rw [show t = Real.sqrt (t ^ 2) by rw [Real.sqrt_sq ht]]; exact Real.sqrt_le_sqrt hβt
    linarith
  have hz0 : 0 < 1 + α + β := lt_of_lt_of_le (by nlinarith [Real.sqrt_nonneg β]) hzl
  have hsc : 0 < Real.sqrt (Q.q c) := Real.sqrt_pos.mpr hc
  have hfk : Q.fk k (c + y) = (Real.sqrt (Q.q c))⁻¹ ^ k * (Real.sqrt (1 + α + β))⁻¹ ^ k := by
    unfold QF.fk; rw [hz, Real.sqrt_mul (le_of_lt hc), mul_inv, mul_pow]
  rw [hfk, ← mul_sub, abs_mul, abs_of_pos (by positivity), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rcases hk with rfl | rfl
  · simp only [tay, if_true, pow_one]
    have := lV_taylor ht ht1 hβt hα N
    rwa [one_div] at this
  · simp only [tay, show (2 : ℕ) ≠ 1 by norm_num, if_false]
    have := cW_taylor ht ht1 hβt hα N
    rwa [inv_pow, Real.sq_sqrt (le_of_lt hz0), ← one_div]

/-! ### Polynomiality of the Taylor polynomial along an affine map -/

theorem IsPoly.congr {d : ℕ} {f g : ℝ × ℝ → ℝ} (h : IsPoly d f) (e : ∀ s, f s = g s) : IsPoly d g := by
  obtain ⟨p, hp, hf⟩ := h; exact ⟨p, hp, fun s => by rw [← e, hf]⟩

theorem isPoly_cW {α β : ℝ × ℝ → ℝ} (ha : IsPoly 1 α) (hb : IsPoly 2 β) :
    ∀ n, IsPoly n fun s => cW (α s) (β s) n
  | 0 => by simpa [cW] using IsPoly.const 0 1
  | 1 => by simpa [cW] using ha.neg
  | (n + 2) => by
    have h1 := (ha.neg.mul (isPoly_cW ha hb (n + 1)))
    have h2 := (hb.mul (isPoly_cW ha hb n))
    have := (h1.mono (by omega : 1 + (n + 1) ≤ n + 2)).sub (h2.mono (by omega : 2 + n ≤ n + 2))
    simpa [cW, neg_mul] using this

theorem isPoly_lV {α β : ℝ × ℝ → ℝ} (ha : IsPoly 1 α) (hb : IsPoly 2 β) :
    ∀ n, IsPoly n fun s => lV (α s) (β s) n
  | 0 => by simpa [lV] using IsPoly.const 0 1
  | 1 => (ha.const_mul (-1 / 2)).congr fun s => by simp [lV]; ring
  | (n + 2) => by
    have h1 := (ha.mul (isPoly_lV ha hb (n + 1))).const_mul (-(2 * n + 3) / (2 * (n + 2)))
    have h2 := (hb.mul (isPoly_lV ha hb n)).const_mul (-(n + 1) / (n + 2))
    refine ((h1.mono (by omega : 1 + (n + 1) ≤ n + 2)).add (h2.mono (by omega : 2 + n ≤ n + 2))).congr ?_
    intro s
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    show _ = (-(2 * (n : ℝ) + 3) * (α s / 2) * lV (α s) (β s) (n + 1) - (n + 1) * β s * lV (α s) (β s) n) / (n + 2)
    field_simp; ring

/-! ### The leaf bound -/

/-- The affine map `s ↦ a + s₁ D + s₂ E`. -/
def aff (a D E : E3) (s : ℝ × ℝ) : E3 := a + s.1 • D + s.2 • E

theorem QF.continuous_q (Q : QF) : Continuous Q.q := by
  unfold QF.q QF.bil; fun_prop

theorem QF.q_aff (Q : QF) (u D E : E3) (x y : ℝ) :
    Q.q (u + x • D + y • E) = Q.q u + 2 * x * Q.bil u D + 2 * y * Q.bil u E +
      x ^ 2 * Q.q D + 2 * x * y * Q.bil D E + y ^ 2 * Q.q E := by
  rw [QF.q_add, QF.q_add, QF.q_smul, QF.q_smul, QF.bil_add_left, QF.bil_smul_right, QF.bil_smul_right,
    QF.bil_smul_left, QF.bil_smul_right]
  ring

theorem QF.bil_aff (Q : QF) (c u D E : E3) (s : ℝ × ℝ) :
    Q.bil c (u + s.1 • D + s.2 • E) = Q.bil c u + s.1 * Q.bil c D + s.2 * Q.bil c E := by
  rw [QF.bil_add_right, QF.bil_add_right, QF.bil_smul_right, QF.bil_smul_right]

theorem ruleSum_sub (WC : ℕ) (r : List GNode) (f g : ℝ × ℝ → ℝ) :
    ruleSum WC r (fun s => f s - g s) = ruleSum WC r f - ruleSum WC r g := by
  have := ruleSum_add WC r f (fun s => (-1) * g s)
  rw [ruleSum_const_mul] at this
  simp only [neg_one_mul, ← sub_eq_add_neg] at this
  linarith

/-- On the leaf, `|y s - c| ≤ t |c|` (convexity of `q`). -/
theorem leaf_near (Q : QF) (a D E : E3) {t : ℝ}
    (hv0 : Q.q (aff a D E (0, 0) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3)))
    (hv1 : Q.q (aff a D E (1, 0) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3)))
    (hv2 : Q.q (aff a D E (0, 1) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3))) :
    ∀ s ∈ T2, Q.q (aff a D E s - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3)) := by
  set c := aff a D E (1 / 3, 1 / 3)
  have hoff : ∀ s : ℝ × ℝ, aff a D E s - c = (1 - s.1 - s.2) • (aff a D E (0, 0) - c) +
      s.1 • (aff a D E (1, 0) - c) + s.2 • (aff a D E (0, 1) - c) := by
    intro s; ext i; simp [aff]; ring
  intro s ⟨h1, h2, h3⟩
  rw [hoff]
  exact le_trans (Q.q_convex3 _ _ _ h1 h2 h3) (max_le hv0 (max_le hv1 hv2))

/-- On the leaf, `|y s| ≥ (1 - t) |c| > 0`. -/
theorem leaf_pos (Q : QF) (a D E : E3) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hc : 0 < Q.q (aff a D E (1 / 3, 1 / 3)))
    (hy : ∀ s ∈ T2, Q.q (aff a D E s - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3))) :
    ∀ s ∈ T2, 0 < Q.q (aff a D E s) := by
  set c := aff a D E (1 / 3, 1 / 3)
  have hsc : 0 < Real.sqrt (Q.q c) := Real.sqrt_pos.mpr hc
  intro s hs
  have h1 := Q.sqrt_q_add (aff a D E s) (c - aff a D E s)
  rw [add_sub_cancel] at h1
  have h2 : Real.sqrt (Q.q (c - aff a D E s)) ≤ t * Real.sqrt (Q.q c) := by
    rw [show c - aff a D E s = (-1 : ℝ) • (aff a D E s - c) by simp, QF.q_smul]
    rw [show t * Real.sqrt (Q.q c) = Real.sqrt (t ^ 2 * Q.q c) by
      rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]]
    apply Real.sqrt_le_sqrt; have := hy s hs; linarith
  have h3 : 0 < Real.sqrt (Q.q (aff a D E s)) := by nlinarith
  exact Real.sqrt_pos.mp h3

theorem leaf_cont (Q : QF) (k : ℕ) (a D E : E3) (hpos : ∀ s ∈ T2, 0 < Q.q (aff a D E s)) :
    ContinuousOn (fun s => Q.fk k (aff a D E s)) T2 := by
  unfold QF.fk
  apply ContinuousOn.pow
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sqrt.comp (Q.continuous_q.comp (by unfold aff; fun_prop))).continuousOn
  · intro s hs; exact ne_of_gt (Real.sqrt_pos.mpr (hpos s hs))

/-- **One leaf.** -/
theorem leaf_bound (Q : QF) {k : ℕ} (hk : k = 1 ∨ k = 2) {d WC M : ℕ} {r : List GNode}
    (hr : ruleOK d WC M r = true) (a D E : E3) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hc : 0 < Q.q (aff a D E (1 / 3, 1 / 3)))
    (hv0 : Q.q (aff a D E (0, 0) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3)))
    (hv1 : Q.q (aff a D E (1, 0) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3)))
    (hv2 : Q.q (aff a D E (0, 1) - aff a D E (1 / 3, 1 / 3)) ≤ t ^ 2 * Q.q (aff a D E (1 / 3, 1 / 3))) :
    |(∫ s in T2, Q.fk k (aff a D E s)) - ruleSum WC r (fun s => Q.fk k (aff a D E s))| ≤
      (1 / 2 + (r.map fun n => |(n.W : ℝ) / WC|).sum) *
        (phiB d t * (Real.sqrt (Q.q (aff a D E (1 / 3, 1 / 3))))⁻¹ ^ k) := by
  set c := aff a D E (1 / 3, 1 / 3)
  set Eb := phiB d t * (Real.sqrt (Q.q c))⁻¹ ^ k
  have hy := leaf_near Q a D E hv0 hv1 hv2
  have hsc : 0 < Real.sqrt (Q.q c) := Real.sqrt_pos.mpr hc
  have hpos := leaf_pos Q a D E ht ht1 hc hy
  -- the Taylor polynomial
  set P : ℝ × ℝ → ℝ := fun s => (Real.sqrt (Q.q c))⁻¹ ^ k *
    tay k d (2 * Q.bil c (aff a D E s - c) / Q.q c) (Q.q (aff a D E s - c) / Q.q c)
  have hP : IsPoly d P := by
    have hu : ∀ s : ℝ × ℝ, aff a D E s - c = (a - c) + s.1 • D + s.2 • E := by
      intro s; ext i; simp [aff]; ring
    have ha : IsPoly 1 fun s => 2 * Q.bil c (aff a D E s - c) / Q.q c := by
      refine (IsPoly.affine (2 * Q.bil c (a - c) / Q.q c) (2 * Q.bil c D / Q.q c)
        (2 * Q.bil c E / Q.q c)).congr fun s => ?_
      rw [hu, QF.bil_aff]; field_simp; ring
    have hb : IsPoly 2 fun s => Q.q (aff a D E s - c) / Q.q c := by
      have h00 := IsPoly.const 2 (Q.q (a - c) / Q.q c)
      have h1 := (IsPoly.fst.const_mul (2 * Q.bil (a - c) D / Q.q c)).mono (by norm_num : 1 ≤ 2)
      have h2 := (IsPoly.snd.const_mul (2 * Q.bil (a - c) E / Q.q c)).mono (by norm_num : 1 ≤ 2)
      have h11 := (IsPoly.fst.mul IsPoly.fst).const_mul (Q.q D / Q.q c)
      have h12 := (IsPoly.fst.mul IsPoly.snd).const_mul (2 * Q.bil D E / Q.q c)
      have h22 := (IsPoly.snd.mul IsPoly.snd).const_mul (Q.q E / Q.q c)
      refine (((((h00.add h1).add h2).add h11).add h12).add h22).congr fun s => ?_
      rw [hu, QF.q_aff]; field_simp; ring
    refine IsPoly.const_mul _ ?_
    unfold tay
    split_ifs
    · exact IsPoly.sum _ fun n hn => (isPoly_lV ha hb n).mono (by simp at hn; omega)
    · exact IsPoly.sum _ fun n hn => (isPoly_cW ha hb n).mono (by simp at hn; omega)
  -- the pointwise remainder
  have hrem : ∀ s ∈ T2, |Q.fk k (aff a D E s) - P s| ≤ Eb := by
    intro s hs
    have := Q.taylor hk d hc ht ht1 (hy s hs)
    rwa [add_sub_cancel] at this
  have hcont := leaf_cont Q k a D E hpos
  have hPc : Continuous P := by
    obtain ⟨p, _, hp⟩ := hP
    have : P = fun s => MvPolynomial.eval ![s.1, s.2] p := funext hp
    rw [this]
    have hv : Continuous fun s : ℝ × ℝ => ![s.1, s.2] :=
      continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
    exact (MvPolynomial.continuous_eval p).comp hv
  have hexact := rule_exact hr hP
  have hi1 : IntegrableOn (fun s => Q.fk k (aff a D E s)) T2 := integrableOn_T2 hcont
  have hi2 : IntegrableOn P T2 := integrableOn_T2 hPc.continuousOn
  have e1 : (∫ s in T2, Q.fk k (aff a D E s)) =
      (∫ s in T2, (Q.fk k (aff a D E s) - P s)) + ∫ s in T2, P s := by
    rw [integral_sub hi1 hi2]; ring
  have e2 : ruleSum WC r (fun s => Q.fk k (aff a D E s)) =
      ruleSum WC r (fun s => Q.fk k (aff a D E s) - P s) + ruleSum WC r P := by
    rw [ruleSum_sub]; ring
  rw [e1, e2, hexact]
  have b1 : |∫ s in T2, (Q.fk k (aff a D E s) - P s)| ≤ Eb * (1 / 2) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) volume_T2_lt
      (f := fun s => Q.fk k (aff a D E s) - P s) (C := Eb) (fun s hs => by
        rw [Real.norm_eq_abs]; exact hrem s hs)
    rwa [volume_T2, Real.norm_eq_abs] at this
  have b2 := ruleSum_abs_le WC r (fun s => Q.fk k (aff a D E s) - P s) Eb
    (fun n hn => hrem n.pt (ruleOK_nodes hr n hn))
  calc _ = |(∫ s in T2, (Q.fk k (aff a D E s) - P s)) - ruleSum WC r (fun s => Q.fk k (aff a D E s) - P s)| := by
        ring_nf
    _ ≤ |∫ s in T2, (Q.fk k (aff a D E s) - P s)| + |ruleSum WC r (fun s => Q.fk k (aff a D E s) - P s)| :=
        abs_sub _ _
    _ ≤ Eb * (1 / 2) + ((r.map fun n => |(n.W : ℝ) / WC|).sum) * Eb := add_le_add b1 b2
    _ = _ := by ring

end GW.Endpoint.Coulomb

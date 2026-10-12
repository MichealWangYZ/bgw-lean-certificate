/-
Endpoint E1.4, certificate soundness (1/3): outward-rounded interval arithmetic.

`bgw/endpoint/iv.py` represents an interval by float endpoints `[lo, hi]` and
says it *encloses* a real `x` when `lo ≤ x ≤ hi`; here that is
`x ∈ Set.Icc lo hi`. Each theorem below is the real-number fact that makes one
operation of `iv.py` sound, with the endpoints written exactly as the code
computes them.

## The rounding model and the named gap

An endpoint the code computes as `_down(expr)` (resp. `_up(expr)`) is modelled
as `ρ.down r` (resp. `ρ.up r`), where `r` is the *exact real* value of `expr`
on the float operands, and `ρ : Rounding` only promises `down r ≤ r ≤ up r`.
The link to the Python is the following hypothesis, which is **not proved
here and is a named gap of the certificate**:

  (IEEE) numpy's float64 `+ - * / sqrt` are IEEE-754 binary64 operations rounded
  to nearest with gradual underflow, so for the exact result `r` of one such
  operation, `pred (fl r) ≤ r ≤ succ (fl r)` with `pred/succ = numpy.nextafter`;
  and `fl` is monotone, so `min_k fl(p_k) = fl(min_k p_k)` (this is what lets
  `_down(p.min(axis=0))` in `I.__mul__` be read as `down (min …)` of the exact
  products).

Also a gap: that the Python code implements these formulas (the
Python-to-Lean correspondence), and that `I.exact` of a float is that float as
a real. Negation, `abs`, `min`, `max` and `np.where` are exact in binary64 and
are modelled exactly.

Rounding directions audited against `iv.py` (all outward): `__add__` (line
110), `__mul__` (124), `recip` (131), `sqr` (142-143; the straddling lower
endpoint is the exact `0`), `sqrt` (148), `sum` (178-179), `_row_sum_up` (246),
`_matmul_up` (255). `__neg__`, `abs`, `mag`, `hull`, `select` do no rounding.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Sqrt

namespace GW.Endpoint.Cert.IV

open Set Finset

/-- A rounding model: `down r ≤ r ≤ up r`. The existence of such functions
matching numpy's `nextafter ∘ fl` is the IEEE hypothesis of the module
docstring, a named gap; nothing here depends on how they are implemented. -/
structure Rounding where
  down : ℝ → ℝ
  up : ℝ → ℝ
  down_le : ∀ r, down r ≤ r
  le_up : ∀ r, r ≤ up r

variable (ρ : Rounding) {lo hi lo' hi' x y : ℝ}

/-- `I.__neg__`: `[-hi, -lo]`, exact. -/
theorem neg_mem (hx : x ∈ Icc lo hi) : -x ∈ Icc (-hi) (-lo) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

/-- `I.__add__`: `[down (lo + lo'), up (hi + hi')]`. -/
theorem add_mem (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x + y ∈ Icc (ρ.down (lo + lo')) (ρ.up (hi + hi')) :=
  ⟨(ρ.down_le _).trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans (ρ.le_up _)⟩

/-- `I.__sub__` is `self + (-o)`: `[down (lo + -hi'), up (hi + -lo')]`. -/
theorem sub_mem (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x - y ∈ Icc (ρ.down (lo + -hi')) (ρ.up (hi + -lo')) := by
  rw [sub_eq_add_neg]; exact add_mem ρ hx (neg_mem hy)

/-- Some one of the four endpoint products is `≤ x * y`. -/
theorem min4_le_mul (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    min (min (lo * lo') (lo * hi')) (min (hi * lo') (hi * hi')) ≤ x * y := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  rcases le_total 0 y with hy0 | hy0
  · rcases le_total 0 lo with ha | ha
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by nlinarith))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by nlinarith))
  · rcases le_total 0 hi with hb | hb
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by nlinarith))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by nlinarith))

/-- `x * y` is `≤` some one of the four endpoint products. -/
theorem mul_le_max4 (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x * y ≤ max (max (lo * lo') (lo * hi')) (max (hi * lo') (hi * hi')) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  rcases le_total 0 y with hy0 | hy0
  · rcases le_total 0 hi with hb | hb
    · exact (by nlinarith : x * y ≤ hi * hi').trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (by nlinarith : x * y ≤ hi * lo').trans ((le_max_left _ _).trans (le_max_right _ _))
  · rcases le_total 0 lo with ha | ha
    · exact (by nlinarith : x * y ≤ lo * hi').trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (by nlinarith : x * y ≤ lo * lo').trans ((le_max_left _ _).trans (le_max_left _ _))

/-- `I.__mul__`: the four-product rule, `[down (min of the four products),
up (max of the four products)]` (products in the order of `iv.py:122-123`). -/
theorem mul_mem (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x * y ∈ Icc (ρ.down (min (min (lo * lo') (lo * hi')) (min (hi * lo') (hi * hi'))))
      (ρ.up (max (max (lo * lo') (lo * hi')) (max (hi * lo') (hi * hi')))) :=
  ⟨(ρ.down_le _).trans (min4_le_mul hx hy), (mul_le_max4 hx hy).trans (ρ.le_up _)⟩

/-- `I.sqr`: with `a = lo*lo`, `b = hi*hi`, the lower endpoint is the exact
`0` if the interval straddles `0` and `down (min a b)` otherwise; the upper
endpoint is `up (max a b)`. -/
theorem sqr_mem (hx : x ∈ Icc lo hi) :
    x * x ∈ Icc (if lo ≤ 0 ∧ 0 ≤ hi then 0 else ρ.down (min (lo * lo) (hi * hi)))
      (ρ.up (max (lo * lo) (hi * hi))) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · exact mul_self_nonneg x
    · refine (ρ.down_le _).trans ?_
      rcases not_and_or.mp h with h | h
      · push_neg at h; exact (min_le_left _ _).trans (by nlinarith)
      · push_neg at h; exact (min_le_right _ _).trans (by nlinarith)
  · refine le_trans ?_ (ρ.le_up _)
    rcases le_total 0 x with h0 | h0
    · exact (by nlinarith : x * x ≤ hi * hi).trans (le_max_right _ _)
    · exact (by nlinarith : x * x ≤ lo * lo).trans (le_max_left _ _)

/-- `I.recip`, which raises unless `0 ∉ [lo, hi]`: `[down (1/hi), up (1/lo)]`. -/
theorem recip_mem (h0 : ¬(lo ≤ 0 ∧ 0 ≤ hi)) (hx : x ∈ Icc lo hi) :
    1 / x ∈ Icc (ρ.down (1 / hi)) (ρ.up (1 / lo)) := by
  obtain ⟨h1, h2⟩ := hx
  rw [not_and_or] at h0; push_neg at h0
  refine ⟨(ρ.down_le _).trans ?_, le_trans ?_ (ρ.le_up _)⟩
  · rcases h0 with h | h
    · exact one_div_le_one_div_of_le (by linarith) h2
    · exact (one_div_le_one_div_of_neg h (by linarith)).mpr h2
  · rcases h0 with h | h
    · exact one_div_le_one_div_of_le h h1
    · exact (one_div_le_one_div_of_neg (by linarith) (by linarith)).mpr h1

/-- The endpoints of `iv.I.recip` of `[lo, hi]`, which `I.__truediv__` then
multiplies by (`self * o.recip()`). -/
theorem div_mem (h0 : ¬(lo' ≤ 0 ∧ 0 ≤ hi')) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x / y ∈ Icc
      (ρ.down (min (min (lo * ρ.down (1 / hi')) (lo * ρ.up (1 / lo')))
        (min (hi * ρ.down (1 / hi')) (hi * ρ.up (1 / lo')))))
      (ρ.up (max (max (lo * ρ.down (1 / hi')) (lo * ρ.up (1 / lo')))
        (max (hi * ρ.down (1 / hi')) (hi * ρ.up (1 / lo'))))) := by
  have := mul_mem ρ hx (recip_mem ρ h0 hy)
  rwa [← div_eq_mul_one_div] at this

/-- `I.sqrt`, which raises unless `0 ≤ lo`: `[max (down √lo) 0, up √hi]`. -/
theorem sqrt_mem (hx : x ∈ Icc lo hi) :
    Real.sqrt x ∈ Icc (max (ρ.down (Real.sqrt lo)) 0) (ρ.up (Real.sqrt hi)) :=
  ⟨max_le ((ρ.down_le _).trans (Real.sqrt_le_sqrt hx.1)) (Real.sqrt_nonneg _),
    (Real.sqrt_le_sqrt hx.2).trans (ρ.le_up _)⟩

/-- `I.mag`: `|x| ≤ max |lo| |hi|`. -/
theorem abs_le_mag (hx : x ∈ Icc lo hi) : |x| ≤ max |lo| |hi| :=
  abs_le_max_abs_abs hx.1 hx.2

/-- `I.abs`: lower endpoint `0` when straddling `0`, else `min |lo| |hi|`;
upper endpoint `mag`. Exact (no rounding). -/
theorem abs_mem (hx : x ∈ Icc lo hi) :
    |x| ∈ Icc (if lo ≤ 0 ∧ 0 ≤ hi then 0 else min |lo| |hi|) (max |lo| |hi|) := by
  refine ⟨?_, abs_le_mag hx⟩
  split_ifs with h
  · exact abs_nonneg x
  · rcases not_and_or.mp h with h | h
    · push_neg at h
      rw [abs_of_pos (h.trans_le hx.1), abs_of_pos h]
      exact (min_le_left _ _).trans hx.1
    · push_neg at h
      rw [abs_of_neg (hx.2.trans_lt h), abs_of_neg h]
      exact (min_le_right _ _).trans (neg_le_neg hx.2)

/-- `hull`: `[min lo lo', max hi hi']` encloses anything either operand encloses. -/
theorem hull_mem (h : x ∈ Icc lo hi ∨ x ∈ Icc lo' hi') :
    x ∈ Icc (min lo lo') (max hi hi') := by
  rcases h with h | h
  · exact ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩

/-- `select(cond_true, cond_false, a, b)` (`iv.py:192-200`): if the real
condition `c` is certainly true (`ct`) take `a`, if certainly false (`cf`) take
`b`, otherwise the hull. The result encloses `if c then xa else xb`, i.e.
whichever branch the real computation takes. -/
theorem select_mem (c : Prop) [Decidable c] (ct cf : Bool) (hct : ct = true → c)
    (hcf : cf = true → ¬c) {xa xb : ℝ} (ha : xa ∈ Icc lo hi) (hb : xb ∈ Icc lo' hi') :
    (if c then xa else xb) ∈
      Icc (if ct then lo else if cf then lo' else min lo lo')
        (if ct then hi else if cf then hi' else max hi hi') := by
  cases ct
  · cases cf
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact hull_mem (Or.inl ha)
      · exact hull_mem (Or.inr hb)
    · simp only [Bool.false_eq_true, ↓reduceIte, if_neg (hcf rfl)]; exact hb
  · simp only [↓reduceIte, if_pos (hct rfl)]; exact ha

/-- `certainly_lt`: `hi < lo'` decides `x < y` for all enclosed `x`, `y`. -/
theorem certainly_lt_sound (h : hi < lo') (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x < y := hx.2.trans_lt (h.trans_le hy.1)

/-- `certainly_le`: `hi ≤ lo'`. -/
theorem certainly_le_sound (h : hi ≤ lo') (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x ≤ y := hx.2.trans (h.trans hy.1)

/-- `certainly_gt`: `lo > hi'`. -/
theorem certainly_gt_sound (h : lo > hi') (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x > y := hy.2.trans_lt (h.trans_le hx.1)

/-- `certainly_ge`: `lo ≥ hi'`. -/
theorem certainly_ge_sound (h : lo ≥ hi') (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo' hi') :
    x ≥ y := hy.2.trans (h.trans hx.1)

/-- `contains_zero` false (the guard before every division) excludes `x = 0`. -/
theorem ne_zero_of_not_contains_zero (h : ¬(lo ≤ 0 ∧ 0 ≤ hi)) (hx : x ∈ Icc lo hi) :
    x ≠ 0 := by
  rintro rfl; exact h ⟨hx.1, hx.2⟩

/-- The sequential lower sum of `I.sum`: `s₀ = lo 0`, `s_{j+1} = down (s_j + lo (j+1))`. -/
def sumDown (l : ℕ → ℝ) : ℕ → ℝ
  | 0 => l 0
  | j + 1 => ρ.down (sumDown l j + l (j + 1))

/-- The sequential upper sum of `I.sum` and `_row_sum_up`:
`s₀ = hi 0`, `s_{j+1} = up (s_j + hi (j+1))`. -/
def sumUp (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => h 0
  | j + 1 => ρ.up (sumUp h j + h (j + 1))

theorem sum_le_sumUp (x h : ℕ → ℝ) (N : ℕ) (hx : ∀ j ≤ N, x j ≤ h j) :
    ∑ j ∈ range (N + 1), x j ≤ sumUp ρ h N := by
  induction N with
  | zero => simpa [sumUp] using hx 0 le_rfl
  | succ N ih =>
    rw [sum_range_succ, sumUp]
    exact (add_le_add (ih fun j hj => hx j (by omega)) (hx _ le_rfl)).trans (ρ.le_up _)

theorem sumDown_le_sum (x l : ℕ → ℝ) (N : ℕ) (hx : ∀ j ≤ N, l j ≤ x j) :
    sumDown ρ l N ≤ ∑ j ∈ range (N + 1), x j := by
  induction N with
  | zero => simpa [sumDown] using hx 0 le_rfl
  | succ N ih =>
    rw [sum_range_succ, sumDown]
    exact (ρ.down_le _).trans (add_le_add (ih fun j hj => hx j (by omega)) (hx _ le_rfl))

/-- `I.sum` (`iv.py:172-180`): the sequential outward sum of `N + 1` intervals
encloses the exact sum of any enclosed family. -/
theorem sum_mem (x l h : ℕ → ℝ) (N : ℕ) (hx : ∀ j ≤ N, x j ∈ Icc (l j) (h j)) :
    ∑ j ∈ range (N + 1), x j ∈ Icc (sumDown ρ l N) (sumUp ρ h N) :=
  ⟨sumDown_le_sum ρ x l N fun j hj => (hx j hj).1, sum_le_sumUp ρ x h N fun j hj => (hx j hj).2⟩

/-- `_matmul_up` (`iv.py:250-256`) accumulates `out = up (out + up (t_j))` from
`out = 0`; the result bounds the exact sum `∑_{j<N} t_j` from above. -/
def matmulUpAcc (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => ρ.up (matmulUpAcc t j + ρ.up (t j))

theorem sum_le_matmulUpAcc (t : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, t j ≤ matmulUpAcc ρ t N := by
  induction N with
  | zero => simp [matmulUpAcc]
  | succ N ih =>
    rw [sum_range_succ, matmulUpAcc]
    exact (add_le_add ih (ρ.le_up _)).trans (ρ.le_up _)

end GW.Endpoint.Cert.IV

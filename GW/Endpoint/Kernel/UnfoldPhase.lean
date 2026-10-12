/-
G2 unfolding: what the integer sign rules of `Unfold.lean` mean.

* `phase_half`: `exp(-2πi n/2) = ±1` by the parity of `n`. With `t = t2 / 2`
  (`Unf.Op.t2`), the per-G factor of a rotated state, `exp(-2πi (M G)·t)`, is exactly
  the sign `Unf.flipG` applies (`flipG_phase`), and the relative eps phase
  `exp(-2πi M(G_i - G_0)·t)` of `Screening.mapping` is the sign `QD.neg` records.
* `rot_coef`: the coefficients of a rotated state are the irreducible ones times these
  signs (`c'(M G - g) = exp(-2πi (M G)·t) c(G)`; the global factor `exp(-2πi (M k)·t)`
  of the textbook formula is dropped, as in `cert.real_coeffs`).
* `tOK1_sound`: the header check `tOK` means `|tnp - π t2| ≤ 10^-15 + 10^-20`, i.e. the
  exported `t = t2/2` is `tnp / 2π` up to `2·10^-16`.
-/
import GW.Endpoint.Kernel.Unfold
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Real.Pi.Bounds

namespace GW.Endpoint.Kernel.Unf

open Complex GW.Endpoint.Kernel.Eps

/-- `exp(-2πi n/2) = (-1)^n`. -/
theorem phase_half (n : ℤ) :
    Complex.exp (-(2 * Real.pi * I) * ((n : ℂ) / 2)) = if n % 2 = 1 then -1 else 1 := by
  have h : -(2 * (Real.pi : ℂ) * I) * ((n : ℂ) / 2) = n * (-(Real.pi * I)) := by ring
  rw [h, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [inv_neg_one]
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · rw [if_neg (by omega), hk, zpow_mul]; norm_num
  · rw [if_pos (by omega), hk, zpow_add₀ (by norm_num), zpow_mul]; norm_num

/-- The sign `flipG op G` is the phase `exp(-2πi (M G)·t)`, `t = t2 / 2`. -/
theorem flipG_phase (op : Op) (G : V3) :
    ((if flipG op G then -1 else 1 : ℤ) : ℂ) =
      Complex.exp (-(2 * Real.pi * I) * (((dot (mulMV op.M G) op.t2 : ℤ) : ℂ) / 2)) := by
  rw [phase_half]; unfold flipG
  by_cases h : dot (mulMV op.M G) op.t2 % 2 = 1 <;> simp [h]

theorem getD_zipWith {α β γ : Type} [Inhabited γ] (f : α → β → γ) (l1 : List α) (l2 : List β)
    (i : ℕ) (d1 : α) (d2 : β) (h1 : i < l1.length) (h2 : i < l2.length) :
    (List.zipWith f l1 l2).getD i default = f (l1.getD i d1) (l2.getD i d2) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

/-- The coefficients of a rotated state: entry `i` of band row `b` is the irreducible
coefficient times the phase sign of `G_i` (`cert.real_coeffs`). -/
theorem rot_coef (w : Wfn) (ik iop : ℕ) (g : V3) (b i : ℕ)
    (hi : i < ((w.coef.getD ik []).getD b []).length) (hG : i < (w.kg.getD ik []).length) :
    (((rot w ik iop g).c.getD b []).getD i default).val =
      (if flipG (w.ops.getD iop default) ((w.kg.getD ik []).getD i 0) then -1 else 1) *
        (((w.coef.getD ik []).getD b []).getD i default).val := by
  have hc : (rot w ik iop g).c.getD b [] = List.zipWith Dy.flip
      ((w.kg.getD ik []).map (flipG (w.ops.getD iop default))) ((w.coef.getD ik []).getD b []) := by
    unfold rot
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    generalize (w.coef[ik]?.getD [])[b]? = o
    cases o <;> simp
  rw [hc, getD_zipWith _ _ _ i false default (by simpa using hG) hi, Dy.flip_val]
  congr 2
  generalize w.kg.getD ik [] = G at hG ⊢
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hG]

/-- `±t` give the same signs (`spec.atom_mapping_sign` only chooses the sign of `t`). -/
theorem flipG_neg (M : M3) (t2 G : V3) : flipG ⟨M, -t2⟩ G = flipG ⟨M, t2⟩ G := by
  unfold flipG dot
  simp only [Prod.fst_neg, Prod.snd_neg]
  have : ∀ x : ℤ, (-x % 2 = 1) ↔ (x % 2 = 1) := fun x => by omega
  rw [decide_eq_decide]
  convert this _ using 2 <;> ring_nf

/-- The header check of the fractional translations: `|tnp - π t2| ≤ 10^-15 + 10^-20`. -/
theorem tOK1_sound (d : Dy) (t : ℤ) (h : tOK1 d t = true) :
    |d.val - t * Real.pi| ≤ 1 / 10 ^ 15 + 1 / 10 ^ 20 := by
  unfold tOK1 at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hn, ht⟩, hc⟩ := h
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  set X : ℤ := ((d.m * 10 ^ 20 : ℕ) : ℤ) - t * ((PIL * 2 ^ d.e : ℕ) : ℤ) with hX
  have hX' : |(X : ℝ)| ≤ 2 ^ d.e * 10 ^ 5 := by
    have h1 : |X| ≤ ((2 ^ d.e * 10 ^ 5 : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hc
    have h2 := (Int.cast_le (R := ℝ)).mpr h1
    rw [Int.cast_abs] at h2; push_cast at h2; norm_num at h2 ⊢; exact h2
  have hPIL : ((PIL : ℕ) : ℝ) = 314159265358979323846 := by norm_num [PIL]
  have hXr : (X : ℝ) = (d.m : ℝ) * 10 ^ 20 - t * (314159265358979323846 * 2 ^ d.e) := by
    rw [hX]; push_cast; rw [hPIL]; norm_num
  have ht' : |(t : ℝ)| ≤ 1 := by
    have : |t| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht
    exact_mod_cast this
  unfold Dy.val; rw [hn]; simp only [Bool.false_eq_true, if_false, one_mul]
  have e1 : |(d.m : ℝ) / 2 ^ d.e - t * (314159265358979323846 / 10 ^ 20)| ≤ 1 / 10 ^ 15 := by
    have : (d.m : ℝ) / 2 ^ d.e - t * (314159265358979323846 / 10 ^ 20) =
        (X : ℝ) / (2 ^ d.e * 10 ^ 20) := by
      rw [hXr]; field_simp; ring
    rw [this, abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ d.e * 10 ^ 20 by positivity),
      div_le_iff₀ (by positivity)]
    calc _ ≤ 2 ^ d.e * 10 ^ 5 := hX'
      _ = 1 / 10 ^ 15 * (2 ^ d.e * 10 ^ 20) := by ring
  have e2 : |(t : ℝ) * (314159265358979323846 / 10 ^ 20) - t * Real.pi| ≤ 1 / 10 ^ 20 := by
    rw [← mul_sub, abs_mul]
    have : |(314159265358979323846 / 10 ^ 20 : ℝ) - Real.pi| ≤ 1 / 10 ^ 20 := by
      rw [abs_le]; constructor <;> norm_num at hpi1 hpi2 ⊢ <;> linarith
    calc |(t : ℝ)| * _ ≤ 1 * (1 / 10 ^ 20) :=
          mul_le_mul ht' this (abs_nonneg _) (by norm_num)
      _ = 1 / 10 ^ 20 := by ring
  calc |(d.m : ℝ) / 2 ^ d.e - t * Real.pi|
      = |((d.m : ℝ) / 2 ^ d.e - t * (314159265358979323846 / 10 ^ 20)) +
          ((t : ℝ) * (314159265358979323846 / 10 ^ 20) - t * Real.pi)| := by ring_nf
    _ ≤ _ := abs_add _ _
    _ ≤ 1 / 10 ^ 15 + 1 / 10 ^ 20 := add_le_add e1 e2

end GW.Endpoint.Kernel.Unf

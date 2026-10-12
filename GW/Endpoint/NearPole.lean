/-
Endpoint E1.4: the one algebraic rewrite the certified evaluator makes.

In the near-pole branch for an occupied band, BerkeleyGW 4.0
(`Sigma/mtxel_cor.f90:1834-1839`, real flavour) computes

    delw = wtilde / (wx - wtilde)
    ssx  = -Omega2 * delw / (4 * wtilde^2 * (delw + 1/2)),   Omega2 = wtilde^2 * I.

`bgw/endpoint/cert.py` encloses instead the closed form

    ssx  = -I * wtilde / (2 * (wx + wtilde)),

which has no removable singularity at `wx = wtilde`. This file proves the two
agree wherever the source expression is defined, so the certified number is
the source's formula and not a look-alike.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace GW.Endpoint

/-- The source's `delw` for a real mode. -/
noncomputable def delw (w x : ℝ) : ℝ := w / (x - w)

/-- The source's near-pole screened-exchange term, as written. -/
noncomputable def ssxNearSource (I w x : ℝ) : ℝ :=
  -(w ^ 2 * I) * delw w x / (4 * w ^ 2 * (delw w x + 1 / 2))

/-- The closed form enclosed by the certified evaluator. -/
noncomputable def ssxNearClosed (I w x : ℝ) : ℝ :=
  -I * w / (2 * (x + w))

/-- Wherever the source expression is defined (`x ≠ w`, `w ≠ 0`, and the
denominator `delw + 1/2 ≠ 0`, i.e. `x + w ≠ 0`), the two forms are equal. -/
theorem ssxNear_eq (I w x : ℝ) (hxw : x - w ≠ 0) (hw : w ≠ 0) (hs : x + w ≠ 0) :
    ssxNearSource I w x = ssxNearClosed I w x := by
  have hd : delw w x + 1 / 2 = (x + w) / (2 * (x - w)) := by
    unfold delw
    field_simp
    ring
  unfold ssxNearSource ssxNearClosed
  rw [hd]
  unfold delw
  field_simp
  ring

/-- The source's denominator condition is exactly `x + w ≠ 0` (given `x ≠ w`):
so the closed form is defined on the whole domain of the source's formula. -/
theorem delw_half_ne_zero_iff (w x : ℝ) (hxw : x - w ≠ 0) :
    w / (x - w) + 1 / 2 ≠ 0 ↔ x + w ≠ 0 := by
  rw [div_add_div _ _ hxw two_ne_zero]
  constructor
  · intro h hs
    apply h
    rw [div_eq_zero_iff]
    left
    linarith
  · intro hs h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact hs (by linarith)
    · exact (mul_ne_zero hxw two_ne_zero) h

end GW.Endpoint

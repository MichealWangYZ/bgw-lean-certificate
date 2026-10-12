/-
Endpoint E1.4, certificate soundness (3/3): BerkeleyGW's `sexcut` clamp and
the division-free test that `bgw/endpoint/cert.py` (`SigmaIV.kernel`,
lines 278-353) uses in its place.

Source (BerkeleyGW 4.0 `Sigma/mtxel_cor.f90:1817-1848`, real flavour, one
mode with `w = wtilde > 0`, `I = I_eps`, `x = wx`, `Omega2 = w^2 I`):

    delw  = w / (x - w),   delwr = delw^2,   wdiffr = (x - w)^2
    if (wdiffr > limittwo .and. delwr < limitone)   ssx = Omega2 / (x^2 - w^2)
    else if (delwr > TOL_Zero)   ssx = -Omega2 delw / (4 w^2 (delw + 1/2))
    else                         ssx = 0
    if (abs(ssx) > sexcut * abs(I) .and. x < 0)   ssx = 0

cert.py decides the same branches without dividing:
`delwr < limitone ⟺ w^2 < (x-w)^2 limitone`, `delwr > TOL_Zero ⟺
w^2 > (x-w)^2 TOL_Zero`, and the clamp by
generic `|x^2 - w^2| < w^2 / sexcut`, near-pole `|2 (x + w)| < w / sexcut`,
then uses the closed near-pole value `-(I w) / (2 (x + w))`
(`GW.Endpoint.ssxNear_eq`).

Main results:

* `sexcut_generic_iff`, `sexcut_near_iff`, `sexcut_nearSource_iff`: the clamp
  conditions are equivalent (for `I ≠ 0` and nonzero denominators).
* `certSsx_eq_srcSsx`: for every branch outcome the value cert.py selects
  (as modelled by `certSsx`) equals the source's value as a real number, whenever `x ≠ w` and
  `x + w ≠ 0`. These are exactly the points where the source's real-number
  formula is defined: `x^2 - w^2 = (x - w)(x + w)` and `delw` need both.
* The two excluded points, stated honestly (Lean's `/` is totalized; the Lean
  value of a zero-denominator expression is NOT the physical one and is never
  used below as such):
  - `x = -w` (`certSsx_at_neg`): the source divides by zero (in IEEE binary64
    `1/0 = Inf`, then `0 * Inf = NaN`, and `abs(NaN) > cutoff` is false, so the
    Fortran `ssx` is NaN); cert.py's division-free test certainly clamps and
    gives `0`.
  - `x = w` (`certSsx_at_w`): the IEEE Fortran gives `ssx = 0` there:
    `delw = w * 0 * Inf = NaN`, so `delwr = NaN`, both branch tests are false
    and the `else` branch sets `ssx = 0`. cert.py originally returned the
    continuous extension `-I / 4` (LEAN-CERT finding 1). `certSsx` models the
    decided branches (near-pole only when `x - w ≠ 0`, value `0` at `x = w`);
    cert.py itself leaves the near-pole condition undecided wherever `x - w`
    may be `0`, so its interval is the hull of both `0` and `-I / 4`
    (`CertInterval.select_mem`) and the certificate holds under either
    convention. The NaN behaviour is an IEEE-arithmetic fact about the
    Fortran, argued here, not modelled in Lean.
  - `I = 0`: both values are `0` (included in `certSsx_eq_srcSsx`).

Named gap: that cert.py and the Fortran implement these real-number formulas
(the Python/Fortran-to-Lean correspondence), and interval enclosure of the
decisions (`CertInterval`).
-/
import GW.Endpoint.NearPole
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity

namespace GW.Endpoint.Cert

variable {I w x s : ℝ}

/-- The source's generic screened-exchange value, `Omega2 / (x^2 - w^2)` with
`Omega2 = w^2 I` (real flavour; `Omega2 * conj(cden) * (1 / |cden|^2)` in the
source). Meaningful only for `x^2 ≠ w^2`. -/
noncomputable def ssxGen (I w x : ℝ) : ℝ := w ^ 2 * I / (x ^ 2 - w ^ 2)

/-- **Generic clamp.** For `I ≠ 0`, `x^2 ≠ w^2`:
`sexcut |I| < |ssx| ⟺ |x^2 - w^2| < w^2 / sexcut` (cert.py:311-312, `lim_g`, `cg_t`). -/
theorem sexcut_generic_iff (hw : 0 < w) (hs : 0 < s) (hI : I ≠ 0)
    (hD : x ^ 2 - w ^ 2 ≠ 0) :
    s * |I| < |ssxGen I w x| ↔ |x ^ 2 - w ^ 2| < w ^ 2 / s := by
  have hIp : 0 < |I| := abs_pos.mpr hI
  have hDp : 0 < |x ^ 2 - w ^ 2| := abs_pos.mpr hD
  unfold ssxGen
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hw 2), lt_div_iff₀ hDp, lt_div_iff₀ hs,
    show s * |I| * |x ^ 2 - w ^ 2| = |x ^ 2 - w ^ 2| * s * |I| by ring,
    mul_lt_mul_right hIp]

/-- **Near-pole clamp**, on the closed form `-I w / (2 (x + w))`: for `I ≠ 0`,
`x + w ≠ 0`: `sexcut |I| < |ssx| ⟺ |2 (x + w)| < w / sexcut`
(cert.py:332-333, `lim_n`, `cn_t`; the threshold `w / sexcut`, fixed in commit 7a4b7a5). -/
theorem sexcut_near_iff (hw : 0 < w) (hs : 0 < s) (hI : I ≠ 0) (hxw : x + w ≠ 0) :
    s * |I| < |ssxNearClosed I w x| ↔ |2 * (x + w)| < w / s := by
  have hIp : 0 < |I| := abs_pos.mpr hI
  have hDp : 0 < |2 * (x + w)| := abs_pos.mpr (mul_ne_zero two_ne_zero hxw)
  unfold ssxNearClosed
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hw, lt_div_iff₀ hDp, lt_div_iff₀ hs,
    show s * |I| * |2 * (x + w)| = |2 * (x + w)| * s * |I| by ring,
    show |I| * w = w * |I| by ring, mul_lt_mul_right hIp]

/-- The same, on the source's own near-pole expression
`-Omega2 delw / (4 w^2 (delw + 1/2))` (via `GW.Endpoint.ssxNear_eq`). -/
theorem sexcut_nearSource_iff (hw : 0 < w) (hs : 0 < s) (hI : I ≠ 0) (hxw' : x - w ≠ 0)
    (hxw : x + w ≠ 0) :
    s * |I| < |ssxNearSource I w x| ↔ |2 * (x + w)| < w / s := by
  rw [ssxNear_eq I w x hxw' hw.ne' hxw]; exact sexcut_near_iff hw hs hI hxw

/-- The source's value for one mode, real flavour, read over the reals:
branch on `wdiffr = (x-w)^2`, `delwr = (w/(x-w))^2`, then the `sexcut` clamp.
Meaningful only for `x ≠ w` and `x + w ≠ 0` (see the module docstring). -/
noncomputable def srcSsx (γ2 lim1 tolZ s I w x : ℝ) : ℝ :=
  let v := if (x - w) ^ 2 > γ2 ∧ delw w x ^ 2 < lim1 then ssxGen I w x
    else if delw w x ^ 2 > tolZ then ssxNearSource I w x else 0
  if |v| > s * |I| ∧ x < 0 then 0 else v

/-- The decided-branch model of cert.py's value for one kept mode (`SigmaIV.kernel`,
occupied): the division-free branch and clamp tests, the generic value `wt2 * Ie / den` and the
near-pole value `-(Ie * wt) / den_n`. -/
noncomputable def certSsx (γ2 lim1 tolZ s I w x : ℝ) : ℝ :=
  if (x - w) ^ 2 > γ2 ∧ w ^ 2 < (x - w) ^ 2 * lim1 then
    (if |x ^ 2 - w ^ 2| < w ^ 2 * (1 / s) ∧ x < 0 then 0 else w ^ 2 * I / (x ^ 2 - w ^ 2))
  else if w ^ 2 > (x - w) ^ 2 * tolZ ∧ x - w ≠ 0 then
    (if |2 * (x + w)| < w * (1 / s) ∧ x < 0 then 0 else -(I * w) / (2 * (x + w)))
  else 0

/-- Replacing a clamp condition by an equivalent one (for `I ≠ 0`) does not
change the clamped value; for `I = 0` the value is `0` either way. -/
theorem clamp_congr {v : ℝ} (C : Prop) [Decidable C] (h0 : I = 0 → v = 0)
    (hiff : I ≠ 0 → (s * |I| < |v| ↔ C)) :
    (if |v| > s * |I| ∧ x < 0 then 0 else v) = (if C ∧ x < 0 then 0 else v) := by
  by_cases hI : I = 0
  · rw [h0 hI]; simp
  · simp only [gt_iff_lt, hiff hI]

/-- **The certified value is the source's value** for every branch outcome,
whenever the source's real-number formula is defined (`x ≠ w`, `x + w ≠ 0`),
for `w > 0`, `sexcut > 0` and any thresholds. -/
theorem certSsx_eq_srcSsx (γ2 lim1 tolZ : ℝ) (hw : 0 < w) (hs : 0 < s) (hxw' : x ≠ w)
    (hxw : x + w ≠ 0) : certSsx γ2 lim1 tolZ s I w x = srcSsx γ2 lim1 tolZ s I w x := by
  have hd : x - w ≠ 0 := sub_ne_zero.mpr hxw'
  have hd2 : 0 < (x - w) ^ 2 := by positivity
  have hD : x ^ 2 - w ^ 2 ≠ 0 := by
    rw [show x ^ 2 - w ^ 2 = (x - w) * (x + w) by ring]; exact mul_ne_zero hd hxw
  have hdelw : delw w x ^ 2 = w ^ 2 / (x - w) ^ 2 := by unfold delw; rw [div_pow]
  have c1 : delw w x ^ 2 < lim1 ↔ w ^ 2 < (x - w) ^ 2 * lim1 := by
    rw [hdelw, div_lt_iff₀ hd2, mul_comm]
  have c2 : delw w x ^ 2 > tolZ ↔ w ^ 2 > (x - w) ^ 2 * tolZ := by
    rw [hdelw, gt_iff_lt, gt_iff_lt, lt_div_iff₀ hd2, mul_comm]
  have hs1 : ∀ a : ℝ, a * (1 / s) = a / s := fun a => by rw [mul_one_div]
  unfold srcSsx certSsx
  simp only [c1, c2, hs1, ne_eq, hd, not_false_eq_true, and_true]
  by_cases hg : (x - w) ^ 2 > γ2 ∧ w ^ 2 < (x - w) ^ 2 * lim1
  · simp only [if_pos hg]
    exact (clamp_congr (v := ssxGen I w x) _ (fun h => by simp [ssxGen, h])
      (fun hI => sexcut_generic_iff hw hs hI hD)).symm
  · simp only [if_neg hg]
    by_cases hn : w ^ 2 > (x - w) ^ 2 * tolZ
    · have he : ssxNearSource I w x = -(I * w) / (2 * (x + w)) := by
        rw [ssxNear_eq I w x hd hw.ne' hxw, ssxNearClosed, neg_mul]
      simp only [if_pos hn, he]
      exact (clamp_congr (v := -(I * w) / (2 * (x + w))) _ (fun h => by simp [h])
        (fun hI => by
          rw [← neg_mul, ← ssxNearClosed]; exact sexcut_near_iff hw hs hI hxw)).symm
    · simp [if_neg hn]

/-- At `x = -w` (the hole-branch SX pole) cert.py's value is `0`: its
division-free test certainly clamps (generic and near-pole alike). The source
divides by zero there (Fortran IEEE: NaN), so no real-number equality is
claimed. -/
theorem certSsx_at_neg (γ2 lim1 tolZ : ℝ) (hw : 0 < w) (hs : 0 < s) :
    certSsx γ2 lim1 tolZ s I w (-w) = 0 := by
  have h1 : |(-w) ^ 2 - w ^ 2| < w ^ 2 * (1 / s) := by
    rw [show (-w) ^ 2 - w ^ 2 = 0 by ring, abs_zero]; positivity
  have h2 : |2 * (-w + w)| < w * (1 / s) := by
    rw [show 2 * (-w + w) = 0 by ring, abs_zero]; positivity
  have h3 : -w < 0 := neg_neg_of_pos hw
  unfold certSsx
  simp [h1, h2, h3]

/-- At `x = w` `certSsx` (the decided-branch model, for `0 ≤ γ2`) takes neither the
generic nor the near-pole branch and returns `0`, the IEEE Fortran's value there (NaN
`delwr` fails both branch tests; argued in the module docstring, not modelled). cert.py
itself leaves the near-pole condition undecided where `x - w` may be `0`, so its
interval there is the hull of `0` and `-I / 4` (module docstring). -/
theorem certSsx_at_w (γ2 lim1 tolZ : ℝ) (hγ : 0 ≤ γ2) :
    certSsx γ2 lim1 tolZ s I w w = 0 := by
  have hg : ¬((w - w) ^ 2 > γ2 ∧ w ^ 2 < (w - w) ^ 2 * lim1) := by
    rintro ⟨h, -⟩; simp at h; linarith
  have hn : ¬(w ^ 2 > (w - w) ^ 2 * tolZ ∧ w - w ≠ 0) := fun h => h.2 (sub_self w)
  unfold certSsx
  rw [if_neg hg, if_neg hn]

end GW.Endpoint.Cert

/-
G2 roots (A1 in Lean): spec A's GPP self-energy `Σ(E)` as a FUNCTION of the energy
`E` (eV), the quasiparticle function `f(E) = Emf + Σ(E) - E` of a multiplet, and the
formal derivative `f'` (the derivative of the branch that is active at `E`).

This is `bgw/endpoint/qp_cert.py` (`QPEquation.sigma`, `f`) and
`bgw/endpoint/qp_unique.py` (`kernel_d`, `dsigma`) read over the reals, on stage 3's
inputs (`SigmaSpec.lean`): the E-independent parts (bare exchange `Xq`, static CH `CSq`,
static remainder `ACq`) are stage 3's; the E-dependent part replaces stage 3's
`wx = e_a(k) + iw - e_n1(k - q)` by

    wx(E) = E - e_n1(k - q)      (with the |wx| < TOL_Zero -> TOL_Zero replacement),

common to all bands of the multiplet (qp_cert.py: `wx = E - e1`).

**Points where the source divides by zero.** At `wx = w` (a mode's `wtilde`) the
source's near-pole SX value is `0 / 0`: under IEEE the Fortran gives `ssx = 0`
(`CertSexcut.lean`), the continuous extension of the closed form is `-I/4`. The
spec does not choose: `ssxMc cv` takes `0` (`cv = false`, the IEEE value, `certSsx`)
or `-I/4` (`cv = true`) there, and every theorem of the root enumeration is stated for
both. At `wx = -w` (occupied bands) the source's SX denominator is `0` (IEEE: NaN);
the spec's value there is the sexcut clamp value `0`, the limit from both sides; the
certified brackets contain no such point (`SrcDefOn`), so no claim depends on it.

The second part is a small calculus: `FixedOn F F' a b` (continuous on `[a, b]`,
derivative `F'` on `(a, b)`), closed under sums, scalar multiples, translations and
agreement on `[a, b]`, and the per-mode facts: on an interval where a kernel's branch
conditions have constant truth values, the kernel is `FixedOn` with its formal derivative.
-/
import GW.Endpoint.Kernel.SigmaSpec
import GW.Endpoint.QPUnique
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace GW.Endpoint.Kernel.QP

open Finset Set GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### The spec as a function of `E` -/

section defs

variable (gl : Gl) (Ep : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)

/-- `e_n1(k - q)` in eV. -/
noncomputable def eKQ (t n1 : ℕ) : ℝ := RYD * dy gl.SEn ((st.kq.getD t default).Eq.getD n1 0)

/-- `wx(E) = E - e_n1(k - q)` (eV) with the `|wx| < TOL_Zero` replacement. -/
noncomputable def wxE (t n1 : ℕ) (E : ℝ) : ℝ :=
  let w := E - eKQ gl st t n1
  if |w| < TZ then TZ else w

/-- The SX kernel with the convention `cv` at `wx = wtilde` (where the source divides by
zero): `cv = false` is `ssxM` (value `0`, IEEE), `cv = true` the continuous extension
`-I/4` of the near-pole closed form. -/
noncomputable def ssxMc (cv : Bool) (I O x : ℝ) : ℝ :=
  if cv = true ∧ keepM I O ∧ x = wtM I O then -(IeU I) / 4 else ssxM I O x

/-- The GPP part of inner band `n1` at energy `E`: `CH/2 - [occ] SX`. -/
noncomputable def PqE (cv : Bool) (t a n1 : ℕ) (E : ℝ) : ℝ :=
  (1 / 2) * quad gl vb st t a n1 (fun j i => schM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) (wxE gl st t n1 E)) -
  (if n1 < gl.nocc then
    quad gl vb st t a n1 (fun j i => ssxMc cv (Iq gl Ep vb oq t j i) (Oq gl vb t j i) (wxE gl st t n1 E))
   else 0)

/-- Band `a`'s `Σ(E) - Vxc` summed over q (Ry): `X + SX(E) + CH(E) + COR`. -/
noncomputable def SigE (cv : Bool) (a : ℕ) (E : ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (Xq gl vb st t a + CSq gl Ep vb oq st t a +
    ∑ n1 ∈ range (nbq st t), (ACq gl Ep vb oq st t a n1 + PqE gl Ep vb oq st cv t a n1 E))

/-- The mean-field energy of the multiplet (eV). -/
noncomputable def emf : ℝ := avg st (fun a => RYD * dy gl.SEn (st.Ek.getD a 0))

/-- **The quasiparticle function** `f(E) = Emf + Σ(E) - E` (eV; Vxc = 0), multiplet-averaged. -/
noncomputable def fQP (cv : Bool) (E : ℝ) : ℝ :=
  emf gl st + avg st (fun a => SigE gl Ep vb oq st cv a E) * RYD - E

/-! #### The formal derivative -/

/-- The E-derivative of the CH kernel (the active branch's derivative). -/
noncomputable def dschM (I O x : ℝ) : ℝ :=
  if keepM I O then
    (let w := wtM I O
     if (x - w) ^ 2 > GAM2 ∧ w ^ 2 < (x - w) ^ 2 * LIM1 then -(w * IeU I) / (x - w) ^ 2 else 0)
  else 0

/-- The x-derivative of `Cert.certSsx` (branch by branch). -/
noncomputable def dcertSsx (γ2 lim1 tolZ s I w x : ℝ) : ℝ :=
  if (x - w) ^ 2 > γ2 ∧ w ^ 2 < (x - w) ^ 2 * lim1 then
    (if |x ^ 2 - w ^ 2| < w ^ 2 * (1 / s) ∧ x < 0 then 0 else -(2 * x * w ^ 2 * I) / (x ^ 2 - w ^ 2) ^ 2)
  else if w ^ 2 > (x - w) ^ 2 * tolZ ∧ x - w ≠ 0 then
    (if |2 * (x + w)| < w * (1 / s) ∧ x < 0 then 0 else (I * w) / (2 * (x + w) ^ 2))
  else 0

/-- The E-derivative of the SX kernel. -/
noncomputable def dssxM (I O x : ℝ) : ℝ :=
  if keepM I O then dcertSsx GAM2 LIM1 TZ SEXC (IeU I) (wtM I O) x else 0

/-- `d wx / dE`: `0` where the `TOL_Zero` replacement is active, else `1`. -/
noncomputable def dwx (t n1 : ℕ) (E : ℝ) : ℝ := if |E - eKQ gl st t n1| < TZ then 0 else 1

/-- The E-derivative of `PqE`. -/
noncomputable def dPqE (t a n1 : ℕ) (E : ℝ) : ℝ :=
  dwx gl st t n1 E * ((1 / 2) * quad gl vb st t a n1
      (fun j i => dschM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) (wxE gl st t n1 E)) -
    (if n1 < gl.nocc then
      quad gl vb st t a n1 (fun j i => dssxM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) (wxE gl st t n1 E))
     else 0))

/-- **The formal derivative** `f'(E) = Σ'(E) - 1`. -/
noncomputable def dfQP (E : ℝ) : ℝ :=
  avg st (fun a => ∑ t ∈ range gl.qs.length, ∑ n1 ∈ range (nbq st t), dPqE gl Ep vb oq st t a n1 E) * RYD - 1

/-- No point of `[a, b]` is one where the source divides by zero: for every q-point,
inner band and kept mode, `wx(E) ≠ wtilde`, and for occupied bands `wx(E) ≠ -wtilde`. -/
def SrcDefOn (lo hi : ℝ) : Prop :=
  ∀ E ∈ Icc lo hi, ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ i < (gl.qs.getD t default).Gs.length,
    ∀ j < (gl.qs.getD t default).Gs.length,
      keepM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) →
        wxE gl st t n1 E ≠ wtM (Iq gl Ep vb oq t j i) (Oq gl vb t j i) ∧
        (n1 < gl.nocc → wxE gl st t n1 E ≠ -wtM (Iq gl Ep vb oq t j i) (Oq gl vb t j i))

end defs

/-! ### `FixedOn`: continuity on `[a, b]` and a derivative on `(a, b)` -/

/-- `F` is continuous on `[a, b]` and has derivative `F' x` at every `x ∈ (a, b)`. -/
def FixedOn (F F' : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn F (Icc a b) ∧ ∀ x ∈ Ioo a b, HasDerivAt F (F' x) x

theorem FixedOn.const (c a b : ℝ) : FixedOn (fun _ => c) (fun _ => 0) a b :=
  ⟨continuousOn_const, fun _ _ => hasDerivAt_const _ _⟩

theorem FixedOn.id' (a b : ℝ) : FixedOn (fun x => x) (fun _ => 1) a b :=
  ⟨continuousOn_id, fun _ _ => hasDerivAt_id _⟩

theorem FixedOn.add {F G F' G' : ℝ → ℝ} {a b : ℝ} (hF : FixedOn F F' a b) (hG : FixedOn G G' a b) :
    FixedOn (fun x => F x + G x) (fun x => F' x + G' x) a b :=
  ⟨hF.1.add hG.1, fun x hx => (hF.2 x hx).add (hG.2 x hx)⟩

theorem FixedOn.sub {F G F' G' : ℝ → ℝ} {a b : ℝ} (hF : FixedOn F F' a b) (hG : FixedOn G G' a b) :
    FixedOn (fun x => F x - G x) (fun x => F' x - G' x) a b :=
  ⟨hF.1.sub hG.1, fun x hx => (hF.2 x hx).sub (hG.2 x hx)⟩

theorem FixedOn.const_mul {F F' : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hF : FixedOn F F' a b) :
    FixedOn (fun x => c * F x) (fun x => c * F' x) a b :=
  ⟨continuousOn_const.mul hF.1, fun x hx => (hF.2 x hx).const_mul c⟩

theorem FixedOn.mul_const {F F' : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hF : FixedOn F F' a b) :
    FixedOn (fun x => F x * c) (fun x => F' x * c) a b :=
  ⟨hF.1.mul continuousOn_const, fun x hx => (hF.2 x hx).mul_const c⟩

theorem FixedOn.sum {ι : Type} (s : Finset ι) {F F' : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, FixedOn (F i) (F' i) a b) :
    FixedOn (fun x => ∑ i ∈ s, F i x) (fun x => ∑ i ∈ s, F' i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FixedOn.const 0 a b
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Agreement on `[a, b]` (values) and on `(a, b)` (derivatives). -/
theorem FixedOn.congr {F G F' G' : ℝ → ℝ} {a b : ℝ} (hF : FixedOn F F' a b)
    (h1 : ∀ x ∈ Icc a b, F x = G x) (h2 : ∀ x ∈ Ioo a b, F' x = G' x) : FixedOn G G' a b := by
  refine ⟨hF.1.congr fun x hx => (h1 x hx).symm, fun x hx => ?_⟩
  have hn : Icc a b ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have := (hF.2 x hx).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hn fun y hy => (h1 y hy).symm)
  rw [h2 x hx] at this; exact this

/-- Translation: `F` fixed on `[a - e, b - e]` gives `x ↦ F (x - e)` fixed on `[a, b]`. -/
theorem FixedOn.comp_sub {F F' : ℝ → ℝ} {a b : ℝ} (e : ℝ) (hF : FixedOn F F' (a - e) (b - e)) :
    FixedOn (fun x => F (x - e)) (fun x => F' (x - e)) a b := by
  refine ⟨?_, fun x hx => ?_⟩
  · refine hF.1.comp (continuousOn_id.sub continuousOn_const) fun x hx => ?_
    exact ⟨by show a - e ≤ x - e; linarith [hx.1], by show x - e ≤ b - e; linarith [hx.2]⟩
  · have hx' : x - e ∈ Ioo (a - e) (b - e) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have := (hF.2 (x - e) hx').comp x ((hasDerivAt_id x).sub_const e)
    simpa using this

/-- A function equal on `[a, b]` to one of two fixed functions, the choice being the
same at every point, is fixed. -/
theorem FixedOn.ite {P : ℝ → Prop} [DecidablePred P] {F G F' G' : ℝ → ℝ} {a b : ℝ}
    (hF : FixedOn F F' a b) (hG : FixedOn G G' a b)
    (hP : (∀ x ∈ Icc a b, P x) ∨ ∀ x ∈ Icc a b, ¬P x) :
    FixedOn (fun x => if P x then F x else G x) (fun x => if P x then F' x else G' x) a b := by
  rcases hP with h | h
  · exact hF.congr (fun x hx => by rw [if_pos (h x hx)]) (fun x hx => by rw [if_pos (h x (Ioo_subset_Icc_self hx))])
  · exact hG.congr (fun x hx => by rw [if_neg (h x hx)]) (fun x hx => by rw [if_neg (h x (Ioo_subset_Icc_self hx))])

/-! ### The branch functions -/

/-- `c / (x - w)` is fixed on an interval where `x ≠ w`. -/
theorem fixed_div_sub (c w : ℝ) {a b : ℝ} (h : ∀ x ∈ Icc a b, x - w ≠ 0) :
    FixedOn (fun x => c / (x - w)) (fun x => -c / (x - w) ^ 2) a b := by
  refine ⟨?_, fun x hx => ?_⟩
  · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const) h
  · have hne := h x (Ioo_subset_Icc_self hx)
    have h2 := (hasDerivAt_const x c).div ((hasDerivAt_id x).sub_const w) hne
    convert h2 using 1
    simp only [id]; field_simp

/-- `c / (x^2 - w^2)` is fixed on an interval where `x^2 ≠ w^2`. -/
theorem fixed_div_sq (c w : ℝ) {a b : ℝ} (h : ∀ x ∈ Icc a b, x ^ 2 - w ^ 2 ≠ 0) :
    FixedOn (fun x => c / (x ^ 2 - w ^ 2)) (fun x => -(2 * x * c) / (x ^ 2 - w ^ 2) ^ 2) a b := by
  refine ⟨?_, fun x hx => ?_⟩
  · exact continuousOn_const.div ((continuousOn_id.pow 2).sub continuousOn_const) h
  · have hne := h x (Ioo_subset_Icc_self hx)
    have hd : HasDerivAt (fun y : ℝ => y ^ 2 - w ^ 2) (2 * x) x := by
      have := (hasDerivAt_pow 2 x).sub_const (w ^ 2)
      simpa using this
    have := (hasDerivAt_const x c).div hd hne
    convert this using 1
    field_simp; ring

/-- `c / (2 (x + w))` is fixed on an interval where `x ≠ -w`. -/
theorem fixed_div_add (c w : ℝ) {a b : ℝ} (h : ∀ x ∈ Icc a b, x + w ≠ 0) :
    FixedOn (fun x => c / (2 * (x + w))) (fun x => -c / (2 * (x + w) ^ 2)) a b := by
  refine ⟨?_, fun x hx => ?_⟩
  · exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.add continuousOn_const))
      fun x hx => mul_ne_zero two_ne_zero (h x hx)
  · have hne := h x (Ioo_subset_Icc_self hx)
    have hd : HasDerivAt (fun y : ℝ => 2 * (y + w)) 2 x := by
      have := ((hasDerivAt_id x).add_const w).const_mul 2
      simpa using this
    have := (hasDerivAt_const x c).div hd (mul_ne_zero two_ne_zero hne)
    convert this using 1
    field_simp; ring

end GW.Endpoint.Kernel.QP

/-
A3(a), analytic bridge, part 1: second-order jets at `λ = 0`.

`Jet f F` says that the real function `f` agrees with the degree-2 truncation of the
formal power series `F` up to `O(λ³)` as `λ → 0`:

  f λ - (F₀ + F₁ λ + F₂ λ²) = O(λ³).

The pairs `(f, F)` with `Jet f F` form a subring of `(ℝ → ℝ) × ℝ⟦λ⟧` (`jetRing`).
Consequently every ring-theoretic expression (matrix products, determinants,
adjugates, dot products) built from jet-related inputs is jet-related to the same
expression over `ℝ⟦λ⟧` (`JetM.mul`, `jet_det`, `JetM.adjugate`, ...), and inverses
are handled separately (`jet_inv`, `JetM.inv`): if the constant term of the formal
determinant is nonzero, the real matrix inverse `(M λ)⁻¹` (Lean's total inverse) is
jet-related to the formal inverse.

This is what connects the formal-series theorems of `Sigma.lean` to the actual
function `λ ↦ Σ(ω; λ)`: only coefficients `0, 1, 2` of the formal series enter.

Reuse decision: mathlib's `Asymptotics.IsBigO` is used for the remainder, and
`RingHom.map_det`, `RingHom.map_adjugate`, `Matrix.map_mul` transport the ring
operations. No Taylor theorem or analyticity (`HasFPowerSeriesAt`) is needed: every
function involved is built from the exact eigenvector by ring operations and
inverses, and its jet is obtained algebraically.
-/
import GW.Endpoint.ManyBody.Series
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.Order.Field

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries Asymptotics Filter Topology

/-- The degree-2 truncation of a formal series, evaluated at `x`. -/
noncomputable def tr2 (F : T) (x : ℝ) : ℝ :=
  coeff ℝ 0 F + coeff ℝ 1 F * x + coeff ℝ 2 F * x ^ 2

/-- `f λ = F₀ + F₁ λ + F₂ λ² + O(λ³)` as `λ → 0`. -/
def Jet (f : ℝ → ℝ) (F : T) : Prop :=
  (fun x => f x - tr2 F x) =O[𝓝 0] fun x => x ^ 3

theorem tr2_continuous (F : T) : Continuous (tr2 F) := by
  unfold tr2; fun_prop

theorem tr2_zero (F : T) : tr2 F 0 = coeff ℝ 0 F := by simp [tr2]

theorem cube_tendsto : Tendsto (fun x : ℝ => x ^ 3) (𝓝 0) (𝓝 0) := by
  have : Continuous fun x : ℝ => x ^ 3 := by fun_prop
  simpa using this.tendsto 0

theorem cube_isBigO_one : (fun x : ℝ => x ^ 3) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
  cube_tendsto.isBigO_one ℝ

theorem tr2_isBigO_one (F : T) : tr2 F =O[𝓝 0] (fun _ => (1 : ℝ)) :=
  ((tr2_continuous F).tendsto 0).isBigO_one ℝ

/-- A polynomial remainder `x³ h(x)` with `h` bounded is `O(x³)`. -/
theorem cube_mul_isBigO {h : ℝ → ℝ} (hh : h =O[𝓝 0] (fun _ => (1 : ℝ))) :
    (fun x => x ^ 3 * h x) =O[𝓝 0] fun x => x ^ 3 := by
  simpa using (isBigO_refl (fun x : ℝ => x ^ 3) (𝓝 0)).mul hh

theorem Jet.tendsto {f : ℝ → ℝ} {F : T} (h : Jet f F) :
    Tendsto f (𝓝 0) (𝓝 (coeff ℝ 0 F)) := by
  have h1 : Tendsto (fun x => f x - tr2 F x) (𝓝 0) (𝓝 0) := h.trans_tendsto cube_tendsto
  have h2 : Tendsto (tr2 F) (𝓝 0) (𝓝 (coeff ℝ 0 F)) := by
    rw [← tr2_zero]; exact (tr2_continuous F).tendsto 0
  simpa using h1.add h2

theorem Jet.isBigO_one {f : ℝ → ℝ} {F : T} (h : Jet f F) : f =O[𝓝 0] (fun _ => (1 : ℝ)) :=
  h.tendsto.isBigO_one ℝ

/-! ### Ring operations -/

theorem jet_const (a : ℝ) : Jet (fun _ => a) (C ℝ a) := by
  have : (fun x : ℝ => a - tr2 (C ℝ a) x) = fun _ => 0 := by
    funext x; simp [tr2, coeff_C]
  unfold Jet; rw [this]; exact isBigO_zero _ _

theorem jet_X : Jet (fun x => x) X := by
  have : (fun x : ℝ => x - tr2 X x) = fun _ => 0 := by
    funext x; simp [tr2, coeff_X]
  unfold Jet; rw [this]; exact isBigO_zero _ _

theorem jet_zero : Jet (fun _ => 0) 0 := by simpa using jet_const 0

theorem jet_one : Jet (fun _ => 1) 1 := by simpa using jet_const 1

theorem jet_add {f g : ℝ → ℝ} {F G : T} (hf : Jet f F) (hg : Jet g G) :
    Jet (fun x => f x + g x) (F + G) := by
  unfold Jet at *
  convert hf.add hg using 1
  funext x; simp only [tr2, map_add, Pi.add_apply]; ring

theorem jet_neg {f : ℝ → ℝ} {F : T} (hf : Jet f F) : Jet (fun x => -f x) (-F) := by
  unfold Jet at *
  convert hf.neg_left using 1
  funext x; simp only [tr2, map_neg]; ring

theorem jet_sub {f g : ℝ → ℝ} {F G : T} (hf : Jet f F) (hg : Jet g G) :
    Jet (fun x => f x - g x) (F - G) := by
  simpa [sub_eq_add_neg] using jet_add hf (jet_neg hg)

theorem jet_mul {f g : ℝ → ℝ} {F G : T} (hf : Jet f F) (hg : Jet g G) :
    Jet (fun x => f x * g x) (F * G) := by
  unfold Jet at *
  have e : (fun x => f x * g x - tr2 (F * G) x) = fun x =>
      (f x - tr2 F x) * g x + tr2 F x * (g x - tr2 G x) +
        x ^ 3 * (coeff ℝ 1 F * coeff ℝ 2 G + coeff ℝ 2 F * coeff ℝ 1 G +
          coeff ℝ 2 F * coeff ℝ 2 G * x) := by
    funext x; simp only [tr2, coeff0_mul, coeff1_mul, coeff2_mul]; ring
  rw [e]
  have h1 : (fun x => (f x - tr2 F x) * g x) =O[𝓝 0] fun x => x ^ 3 := by
    simpa using hf.mul (Jet.isBigO_one hg)
  have h2 : (fun x => tr2 F x * (g x - tr2 G x)) =O[𝓝 0] fun x => x ^ 3 := by
    simpa using (tr2_isBigO_one F).mul hg
  have h3 : (fun x : ℝ => coeff ℝ 1 F * coeff ℝ 2 G + coeff ℝ 2 F * coeff ℝ 1 G +
      coeff ℝ 2 F * coeff ℝ 2 G * x) =O[𝓝 0] (fun _ => (1 : ℝ)) := by
    have : Continuous fun x : ℝ => coeff ℝ 1 F * coeff ℝ 2 G + coeff ℝ 2 F * coeff ℝ 1 G +
        coeff ℝ 2 F * coeff ℝ 2 G * x := by fun_prop
    exact (this.tendsto 0).isBigO_one ℝ
  exact (h1.add h2).add (cube_mul_isBigO h3)

/-- Inverses: if the constant term is nonzero, `f⁻¹` is jet-related to `F⁻¹`. -/
theorem jet_inv {f : ℝ → ℝ} {F : T} (hf : Jet f F) (h0 : coeff ℝ 0 F ≠ 0) :
    Jet (fun x => (f x)⁻¹) F⁻¹ := by
  have hc : constantCoeff ℝ F ≠ 0 := by rwa [← coeff_zero_eq_constantCoeff_apply]
  have hFG : F * F⁻¹ = 1 := PowerSeries.mul_inv_cancel F hc
  -- `1 - f · tr2 F⁻¹ = O(x³)`
  have htr : Jet (tr2 F⁻¹) F⁻¹ := by
    unfold Jet; simp only [sub_self]; exact isBigO_zero _ _
  have hprod := jet_mul hf htr
  rw [hFG] at hprod
  have hr : (fun x => 1 - f x * tr2 F⁻¹ x) =O[𝓝 0] fun x => x ^ 3 := by
    have e : (fun x => 1 - f x * tr2 F⁻¹ x) = fun x => -(f x * tr2 F⁻¹ x - tr2 1 x) := by
      funext x; simp [tr2, coeff_one]
    rw [e]; exact hprod.neg_left
  have hinv : Tendsto (fun x => (f x)⁻¹) (𝓝 0) (𝓝 (coeff ℝ 0 F)⁻¹) := hf.tendsto.inv₀ h0
  have hne : ∀ᶠ x in 𝓝 0, f x ≠ 0 := hf.tendsto.eventually_ne h0
  have hb := (hinv.isBigO_one ℝ).mul hr
  unfold Jet
  refine (by simpa using hb : (fun x => (f x)⁻¹ * (1 - f x * tr2 F⁻¹ x)) =O[𝓝 0] _).congr' ?_
    EventuallyEq.rfl
  filter_upwards [hne] with x hx
  field_simp

/-- Finite sums. -/
theorem jet_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {F : ι → T}
    (h : ∀ i ∈ s, Jet (f i) (F i)) : Jet (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jet_zero
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    exact jet_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Extracting explicit constants. -/
theorem Jet.bound {f : ℝ → ℝ} {F : T} (h : Jet f F) :
    ∃ δ > 0, ∃ K : ℝ, ∀ x : ℝ, |x| < δ → |f x - tr2 F x| ≤ K * |x| ^ 3 := by
  obtain ⟨K, hK⟩ := IsBigO.bound h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hK
  refine ⟨δ, hδ, K, fun x hx => ?_⟩
  have := hball (y := x) (by simpa [Real.dist_eq] using hx)
  simpa [Real.norm_eq_abs, abs_pow] using this

/-! ### The subring of jet-related pairs -/

/-- Pairs `(f, F)` with `Jet f F`. -/
noncomputable def jetRing : Subring ((ℝ → ℝ) × T) where
  carrier := {p | Jet p.1 p.2}
  mul_mem' ha hb := jet_mul ha hb
  one_mem' := jet_one
  add_mem' ha hb := jet_add ha hb
  zero_mem' := jet_zero
  neg_mem' ha := jet_neg ha

/-- Evaluation of the function component at `x`. -/
noncomputable def evJ (x : ℝ) : jetRing →+* ℝ :=
  (Pi.evalRingHom (fun _ : ℝ => ℝ) x).comp ((RingHom.fst _ _).comp jetRing.subtype)

/-- The formal component. -/
noncomputable def sndJ : jetRing →+* T := (RingHom.snd _ _).comp jetRing.subtype

theorem jet_of_mem (a : jetRing) : Jet (fun x => evJ x a) (sndJ a) := a.2

/-! ### Matrices and vectors -/

section Mat
variable {ι κ ρ : Type*}

/-- Entrywise jets of matrix-valued functions. -/
def JetM (M : ℝ → Matrix ι κ ℝ) (Mf : Matrix ι κ T) : Prop :=
  ∀ i j, Jet (fun x => M x i j) (Mf i j)

/-- Entrywise jets of vector-valued functions. -/
def JetV (u : ℝ → ι → ℝ) (uf : ι → T) : Prop := ∀ i, Jet (fun x => u x i) (uf i)

/-- Packing a jet-related pair of matrices into a matrix over `jetRing`. -/
def liftJ (M : ℝ → Matrix ι κ ℝ) (Mf : Matrix ι κ T) (h : JetM M Mf) : Matrix ι κ jetRing :=
  Matrix.of fun i j => ⟨(fun x => M x i j, Mf i j), h i j⟩

theorem liftJ_map_evJ (M : ℝ → Matrix ι κ ℝ) (Mf : Matrix ι κ T) (h : JetM M Mf) (x : ℝ) :
    (liftJ M Mf h).map (evJ x) = M x := by ext; rfl

theorem liftJ_map_sndJ (M : ℝ → Matrix ι κ ℝ) (Mf : Matrix ι κ T) (h : JetM M Mf) :
    (liftJ M Mf h).map sndJ = Mf := by ext; rfl

theorem jetM_of (MS : Matrix ι κ jetRing) : JetM (fun x => MS.map (evJ x)) (MS.map sndJ) :=
  fun i j => (MS i j).2

theorem jetM_const (M : Matrix ι κ ℝ) : JetM (fun _ => M) (lift M) :=
  fun i j => jet_const (M i j)

theorem jetM_one [DecidableEq ι] : JetM (fun _ => (1 : Matrix ι ι ℝ)) 1 := by
  intro i j; by_cases h : i = j
  · subst h; simpa using jet_one
  · simpa [one_apply, h] using jet_zero

theorem JetM.add {A B : ℝ → Matrix ι κ ℝ} {Af Bf : Matrix ι κ T} (hA : JetM A Af)
    (hB : JetM B Bf) : JetM (fun x => A x + B x) (Af + Bf) :=
  fun i j => jet_add (hA i j) (hB i j)

theorem JetM.sub {A B : ℝ → Matrix ι κ ℝ} {Af Bf : Matrix ι κ T} (hA : JetM A Af)
    (hB : JetM B Bf) : JetM (fun x => A x - B x) (Af - Bf) :=
  fun i j => jet_sub (hA i j) (hB i j)

theorem JetM.smul {c : ℝ → ℝ} {cf : T} {A : ℝ → Matrix ι κ ℝ} {Af : Matrix ι κ T}
    (hc : Jet c cf) (hA : JetM A Af) : JetM (fun x => c x • A x) (cf • Af) :=
  fun i j => jet_mul hc (hA i j)

theorem JetM.mul [Fintype κ] {A : ℝ → Matrix ι κ ℝ} {B : ℝ → Matrix κ ρ ℝ} {Af : Matrix ι κ T}
    {Bf : Matrix κ ρ T} (hA : JetM A Af) (hB : JetM B Bf) :
    JetM (fun x => A x * B x) (Af * Bf) := by
  have := jetM_of (liftJ A Af hA * liftJ B Bf hB)
  simpa only [Matrix.map_mul, liftJ_map_evJ, liftJ_map_sndJ] using this

theorem JetV.mulVec [Fintype κ] {A : ℝ → Matrix ι κ ℝ} {u : ℝ → κ → ℝ} {Af : Matrix ι κ T}
    {uf : κ → T} (hA : JetM A Af) (hu : JetV u uf) :
    JetV (fun x => A x *ᵥ u x) (Af *ᵥ uf) :=
  fun i => jet_sum univ fun j _ => jet_mul (hA i j) (hu j)

theorem JetV.dot [Fintype ι] {u w : ℝ → ι → ℝ} {uf wf : ι → T} (hu : JetV u uf)
    (hw : JetV w wf) : Jet (fun x => u x ⬝ᵥ w x) (uf ⬝ᵥ wf) :=
  jet_sum univ fun j _ => jet_mul (hu j) (hw j)

variable [Fintype ι] [DecidableEq ι]

theorem jet_det {M : ℝ → Matrix ι ι ℝ} {Mf : Matrix ι ι T} (hM : JetM M Mf) :
    Jet (fun x => (M x).det) Mf.det := by
  have h := jet_of_mem (liftJ M Mf hM).det
  simp only [RingHom.map_det, RingHom.mapMatrix_apply, liftJ_map_evJ, liftJ_map_sndJ] at h
  exact h

theorem JetM.adjugate {M : ℝ → Matrix ι ι ℝ} {Mf : Matrix ι ι T} (hM : JetM M Mf) :
    JetM (fun x => (M x).adjugate) Mf.adjugate := by
  have h := jetM_of (liftJ M Mf hM).adjugate
  have e1 : ∀ x, ((liftJ M Mf hM).adjugate).map (evJ x) = (M x).adjugate := fun x => by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, liftJ_map_evJ]
  have e2 : ((liftJ M Mf hM).adjugate).map sndJ = Mf.adjugate := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, liftJ_map_sndJ]
  simpa only [e1, e2] using h

/-- The formal inverse through the power-series inverse of the determinant. -/
theorem inv_eq_inv_det_smul_adjugate (Mf : Matrix ι ι T) (h0 : coeff ℝ 0 Mf.det ≠ 0) :
    Mf⁻¹ = (Mf.det)⁻¹ • Mf.adjugate := by
  apply inv_eq_left_inv
  have hc : constantCoeff ℝ Mf.det ≠ 0 := by rwa [← coeff_zero_eq_constantCoeff_apply]
  rw [smul_mul, adjugate_mul, smul_smul, PowerSeries.inv_mul_cancel _ hc, one_smul]

theorem coeff0_det_ne_zero {Mf : Matrix ι ι T} (hu : IsUnit Mf.det) : coeff ℝ 0 Mf.det ≠ 0 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  exact (isUnit_iff_constantCoeff.mp hu).ne_zero

/-- **Matrix inverses.** If the formal determinant is a unit (equivalently its constant
term is nonzero), the real inverse `(M λ)⁻¹` is jet-related to the formal inverse. -/
theorem JetM.inv {M : ℝ → Matrix ι ι ℝ} {Mf : Matrix ι ι T} (hM : JetM M Mf)
    (hu : IsUnit Mf.det) : JetM (fun x => (M x)⁻¹) Mf⁻¹ := by
  have h0 := coeff0_det_ne_zero hu
  have e : (fun x => (M x)⁻¹) = fun x => ((M x).det)⁻¹ • (M x).adjugate := by
    funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e, inv_eq_inv_det_smul_adjugate Mf h0]
  exact JetM.smul (jet_inv (jet_det hM) h0) hM.adjugate

/-- Near `0`, the real determinant is nonzero when the formal one is a unit. -/
theorem JetM.eventually_det_ne {M : ℝ → Matrix ι ι ℝ} {Mf : Matrix ι ι T} (hM : JetM M Mf)
    (hu : IsUnit Mf.det) : ∀ᶠ x in 𝓝 0, (M x).det ≠ 0 :=
  (jet_det hM).tendsto.eventually_ne (coeff0_det_ne_zero hu)

end Mat

end GW.Endpoint.ManyBody

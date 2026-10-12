/-
A3(a), analytic bridge, part 2: the TRUE ground state of `H(λ) = H0 + λ V` in the
`|O|`-particle sector, for small real `λ`.

Hypothesis `IsGround ε O`: the Slater determinant `Φ = phi O` is the strict ground
state of `H0` in its particle-number sector (every other `|O|`-particle basis state
has strictly larger energy). This implies `NonDeg ε O`.

Construction (no spectral theorem, no implicit function theorem): the intermediate
normalization `ψ = Φ + χ`, `⟨Φ|χ⟩ = 0`, turns the eigenvalue problem into the
fixed-point equation

  χ = λ F(χ),   F(χ) = Rs (V(Φ + χ) - ⟨Φ|V(Φ + χ)⟩ χ),

with `Rs = diag((E0 - E_S)⁻¹)` restricted to the sector (`Rs`). For `|λ| · 4‖Rs‖‖V‖ ≤ ½`
the map is a `½`-contraction of the closed unit ball (sup norm), so mathlib's Banach
fixed-point theorem (`ContractingWith.exists_fixedPoint'`) gives `χ(λ)`, and

  ψ(λ) = Φ + χ(λ),  E(λ) = E0 + λ ⟨Φ|V ψ(λ)⟩

solve `H(λ) ψ = E ψ` exactly (`eig_exact`). Iterating the fixed-point equation gives
the explicit bounds (`chi_bound1/2/3`, `E_bound`)

  ‖χ‖ ≤ a|λ|,  ‖χ - λψ1‖ ≤ a²λ²,  ‖χ - λψ1 - λ²ψ2‖ ≤ b|λ|³,  |E - (E0+λE1+λ²E2)| ≤ c|λ|³

with `ψ1, ψ2, E1, E2` the Rayleigh–Schrödinger quantities of `Perturb.lean`.

Ground state and simplicity (`groundPair_psiR`, `groundPair_unique`): for small `|λ|`,
every sector eigenvector with eigenvalue `μ ≤ E(λ)` is a multiple of `ψ(λ)` and has
`μ = E(λ)` (a gap argument in the sup norm). Hence `E(λ)` is the lowest eigenvalue of
`H(λ)` in the sector and its eigenspace there is the line through `ψ(λ)`.

Norms: the sup norm on `Fock n → ℝ` (mathlib's `Pi` norm) and the crude matrix bound
`‖M x‖ ≤ (Σ_{ij} |M_ij|) ‖x‖` (`norm_mulVec_le`); no matrix-norm instance is used.
-/
import GW.Endpoint.ManyBody.Perturb
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module

namespace GW.Endpoint.ManyBody

open Matrix Finset Metric Function

variable {n : ℕ}

/-! ### Norm bounds -/

section Norms
variable {ι : Type*} [Fintype ι]

/-- A crude matrix norm: the sum of the absolute values of the entries. -/
def mnorm (M : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |M i j|

theorem mnorm_nonneg (M : Matrix ι ι ℝ) : 0 ≤ mnorm M :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_norm (x : ι → ℝ) (i : ι) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm x i

theorem norm_mulVec_le (M : Matrix ι ι ℝ) (x : ι → ℝ) : ‖M *ᵥ x‖ ≤ mnorm M * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mnorm_nonneg M) (norm_nonneg x))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(M *ᵥ x) i| = |∑ j, M i j * x j| := rfl
    _ ≤ ∑ j, |M i j * x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖x‖ := sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le_norm x j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖x‖ := by rw [sum_mul]
    _ ≤ mnorm M * ‖x‖ := mul_le_mul_of_nonneg_right
        (single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => sum_nonneg fun j _ => abs_nonneg _) (mem_univ i)) (norm_nonneg _)

theorem abs_mulVec_le (M : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) : |(M *ᵥ x) i| ≤ mnorm M * ‖x‖ :=
  (abs_le_norm _ i).trans (norm_mulVec_le M x)

theorem norm_le_of_abs_le {x : ι → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖x‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun i => by rw [Real.norm_eq_abs]; exact h i

end Norms

theorem norm_phi_le (O : Fock n) : ‖phi O‖ ≤ 1 :=
  norm_le_of_abs_le zero_le_one fun S => by
    by_cases h : S = O <;> simp [phi, Pi.single_apply, h]

variable (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n)

/-! ### Sector, ground-state hypothesis, reduced resolvent -/

/-- `x` lies in the `|O|`-particle sector. -/
def InSec (O : Fock n) (x : Fock n → ℝ) : Prop := ∀ S : Fock n, S.card ≠ O.card → x S = 0

/-- `Φ` is the strict ground state of `H0` in its particle-number sector. -/
def IsGround : Prop := ∀ S : Fock n, S.card = O.card → S ≠ O → energy ε O < energy ε S

/-- The sector-reduced resolvent `Q (E0 - H0)⁻¹ Q` (zero outside the sector and on `Φ`). -/
noncomputable def Rs : Matrix (Fock n) (Fock n) ℝ :=
  diagonal fun S => if S.card = O.card then (energy ε O - energy ε S)⁻¹ else 0

/-- The Hamiltonian `H(λ) = H0 + λ V` as a real matrix. -/
noncomputable def Hl (x : ℝ) : Matrix (Fock n) (Fock n) ℝ := H0 ε + x • vop v

/-- The fixed-point map `F(χ) = Rs (V(Φ+χ) - ⟨Φ|V(Φ+χ)⟩ χ)`. -/
noncomputable def Fm (χ : Fock n → ℝ) : Fock n → ℝ :=
  Rs ε O *ᵥ (vop v *ᵥ (phi O + χ) - (vop v *ᵥ (phi O + χ)) O • χ)

/-- The contraction constant `4 ‖Rs‖ ‖V‖`. -/
noncomputable def aC : ℝ := 4 * mnorm (Rs ε O) * mnorm (vop v)

variable {ε v O}

theorem aC_nonneg : 0 ≤ aC ε v O := by
  unfold aC; have := mnorm_nonneg (Rs ε O); have := mnorm_nonneg (vop v); positivity

theorem IsGround.nonDeg (h : IsGround ε O) : NonDeg ε O :=
  fun S hS hne => (h S hS hne).ne'

theorem inSec_iff (x : Fock n → ℝ) : InSec O x ↔ IsEig (fun _ => 1) (O.card : ℝ) x := by
  unfold InSec IsEig
  rw [H0_eq_diagonal]
  constructor
  · intro h; funext S
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, energy, sum_const, nsmul_eq_mul,
      mul_one]
    by_cases hS : S.card = O.card
    · rw [hS]
    · rw [h S hS]; ring
  · intro h S hS
    have := congrFun h S
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul, energy, sum_const, nsmul_eq_mul,
      mul_one] at this
    have hne : (S.card : ℝ) ≠ O.card := by exact_mod_cast hS
    have : ((S.card : ℝ) - O.card) * x S = 0 := by rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem inSec_phi : InSec O (phi O) := (inSec_iff _).2 (phi_isEig_num O)

theorem InSec.vop {x : Fock n → ℝ} (h : InSec O x) : InSec O (vop v *ᵥ x) :=
  (inSec_iff _).2 (vop_isEig_num v ((inSec_iff _).1 h))

theorem InSec.add {x y : Fock n → ℝ} (hx : InSec O x) (hy : InSec O y) : InSec O (x + y) :=
  fun S hS => by simp [hx S hS, hy S hS]

theorem InSec.sub {x y : Fock n → ℝ} (hx : InSec O x) (hy : InSec O y) : InSec O (x - y) :=
  fun S hS => by simp [hx S hS, hy S hS]

theorem InSec.smul {x : Fock n → ℝ} (hx : InSec O x) (c : ℝ) : InSec O (c • x) :=
  fun S hS => by simp [hx S hS]

theorem inSec_Rs (y : Fock n → ℝ) : InSec O (Rs ε O *ᵥ y) := fun S hS => by
  simp [Rs, mulVec_diagonal, hS]

theorem Rs_apply_self (y : Fock n → ℝ) : (Rs ε O *ᵥ y) O = 0 := by
  simp [Rs, mulVec_diagonal]

theorem Rs_eq_Rr {y : Fock n → ℝ} (hy : InSec O y) : Rs ε O *ᵥ y = Rr ε O *ᵥ y := by
  funext S
  simp only [Rs, Rr, mulVec_diagonal]
  by_cases hS : S.card = O.card
  · rw [if_pos hS]
  · rw [if_neg hS, hy S hS]; ring

/-- `(H0 - E0) Rs y = y_O Φ - y` for `y` in the sector. -/
theorem H0_Rs (hnd : NonDeg ε O) {y : Fock n → ℝ} (hy : InSec O y) :
    H0 ε *ᵥ (Rs ε O *ᵥ y) - energy ε O • (Rs ε O *ᵥ y) = y O • phi O - y := by
  rw [Rs_eq_Rr hy, H0_Rr hnd ((inSec_iff y).1 hy), phi_dot]

theorem phi_dot_eq (x : Fock n → ℝ) : phi O ⬝ᵥ x = x O := phi_dot x

/-! ### The contraction -/

theorem abs_vop_apply_le {p : Fock n → ℝ} (hp : ‖p‖ ≤ 1) :
    |(vop v *ᵥ (phi O + p)) O| ≤ 2 * mnorm (vop v) := by
  have h1 := abs_mulVec_le (vop v) (phi O + p) O
  have h2 : ‖phi O + p‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [norm_phi_le O])
  nlinarith [mnorm_nonneg (vop v)]

theorem norm_Fm_le {p : Fock n → ℝ} (hp : ‖p‖ ≤ 1) : ‖Fm ε v O p‖ ≤ aC ε v O := by
  have hV := mnorm_nonneg (vop v)
  have hR := mnorm_nonneg (Rs ε O)
  have h1 := norm_mulVec_le (Rs ε O)
    (vop v *ᵥ (phi O + p) - (vop v *ᵥ (phi O + p)) O • p)
  have h2 : ‖phi O + p‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [norm_phi_le O])
  have h3 := norm_mulVec_le (vop v) (phi O + p)
  have h4 : ‖(vop v *ᵥ (phi O + p)) O • p‖ ≤ 2 * mnorm (vop v) := by
    rw [norm_smul, Real.norm_eq_abs]
    have := abs_vop_apply_le (v := v) (O := O) hp
    have := norm_nonneg p
    nlinarith [abs_nonneg ((vop v *ᵥ (phi O + p)) O)]
  have h5 : ‖vop v *ᵥ (phi O + p) - (vop v *ᵥ (phi O + p)) O • p‖ ≤ 4 * mnorm (vop v) :=
    (norm_sub_le _ _).trans (by nlinarith)
  unfold Fm aC
  calc _ ≤ _ := h1
    _ ≤ mnorm (Rs ε O) * (4 * mnorm (vop v)) := mul_le_mul_of_nonneg_left h5 hR
    _ = _ := by ring

theorem Fm_sub (p q : Fock n → ℝ) :
    Fm ε v O p - Fm ε v O q = Rs ε O *ᵥ (vop v *ᵥ (p - q) -
      (vop v *ᵥ (phi O + p)) O • (p - q) - (vop v *ᵥ (p - q)) O • q) := by
  have e : vop v *ᵥ (phi O + p) - (vop v *ᵥ (phi O + p)) O • p -
      (vop v *ᵥ (phi O + q) - (vop v *ᵥ (phi O + q)) O • q) = vop v *ᵥ (p - q) -
      (vop v *ᵥ (phi O + p)) O • (p - q) - (vop v *ᵥ (p - q)) O • q := by
    funext S
    simp only [mulVec_sub, mulVec_add, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Fm, Fm, ← mulVec_sub, e]

theorem norm_Fm_sub_le {p q : Fock n → ℝ} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖Fm ε v O p - Fm ε v O q‖ ≤ aC ε v O * ‖p - q‖ := by
  have hV := mnorm_nonneg (vop v)
  have hR := mnorm_nonneg (Rs ε O)
  have hd := norm_nonneg (p - q)
  rw [Fm_sub]
  refine (norm_mulVec_le _ _).trans ?_
  have h1 := norm_mulVec_le (vop v) (p - q)
  have h2 : ‖(vop v *ᵥ (phi O + p)) O • (p - q)‖ ≤ 2 * mnorm (vop v) * ‖p - q‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_vop_apply_le hp) hd
  have h3 : ‖(vop v *ᵥ (p - q)) O • q‖ ≤ mnorm (vop v) * ‖p - q‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have := abs_mulVec_le (vop v) (p - q) O
    have := norm_nonneg q
    nlinarith [abs_nonneg ((vop v *ᵥ (p - q)) O)]
  have h4 : ‖vop v *ᵥ (p - q) - (vop v *ᵥ (phi O + p)) O • (p - q) - (vop v *ᵥ (p - q)) O • q‖
      ≤ 4 * mnorm (vop v) * ‖p - q‖ := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (vop v *ᵥ (p - q)) ((vop v *ᵥ (phi O + p)) O • (p - q))
    linarith
  unfold aC
  calc _ ≤ mnorm (Rs ε O) * (4 * mnorm (vop v) * ‖p - q‖) := mul_le_mul_of_nonneg_left h4 hR
    _ = _ := by ring

/-- **Existence** of the normalized eigenvector: a fixed point `χ = λ F(χ)` in the unit ball. -/
theorem exists_fix {x : ℝ} (hx : |x| * aC ε v O ≤ 1 / 2) :
    ∃ χ : Fock n → ℝ, ‖χ‖ ≤ 1 ∧ x • Fm ε v O χ = χ := by
  set s := closedBall (0 : Fock n → ℝ) 1
  have hsc : IsComplete s := isClosed_closedBall.isComplete
  have hmaps : Set.MapsTo (fun χ => x • Fm ε v O χ) s s := fun χ hχ => by
    simp only [s, mem_closedBall, dist_zero_right] at hχ ⊢
    rw [norm_smul, Real.norm_eq_abs]
    have := norm_Fm_le (ε := ε) (v := v) (O := O) hχ
    nlinarith [abs_nonneg x]
  have hK : ContractingWith (1 / 2) (hmaps.restrict _ s s) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
    have hp : ‖(p : Fock n → ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2
    have hq : ‖(q : Fock n → ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.mp q.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [Set.MapsTo.val_restrict_apply]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    have h := norm_Fm_sub_le (ε := ε) (v := v) (O := O) hp hq
    have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    rw [this]
    have hd := norm_nonneg ((p : Fock n → ℝ) - q)
    calc |x| * ‖Fm ε v O p - Fm ε v O q‖ ≤ |x| * (aC ε v O * ‖(p : Fock n → ℝ) - q‖) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg x)
      _ = (|x| * aC ε v O) * ‖(p : Fock n → ℝ) - q‖ := by ring
      _ ≤ 1 / 2 * ‖(p : Fock n → ℝ) - q‖ := mul_le_mul_of_nonneg_right hx hd
  obtain ⟨y, hy, hfix, -⟩ := hK.exists_fixedPoint' hsc hmaps (x := 0) (by simp [s])
    (edist_ne_top _ _)
  exact ⟨y, by simpa [s] using hy, hfix⟩

/-! ### The exact ground state -/

variable (ε v O) in
/-- Radius of the contraction regime. -/
noncomputable def δ0 : ℝ := 1 / (2 * aC ε v O + 1)

theorem δ0_pos : 0 < δ0 ε v O := by unfold δ0; have := aC_nonneg (ε := ε) (v := v) (O := O); positivity

theorem small_of_le_δ0 {x : ℝ} (hx : |x| ≤ δ0 ε v O) : |x| * aC ε v O ≤ 1 / 2 := by
  have ha := aC_nonneg (ε := ε) (v := v) (O := O)
  unfold δ0 at hx
  rw [le_div_iff₀ (by positivity)] at hx
  nlinarith [abs_nonneg x]

variable (ε v O) in
/-- The correction `χ(λ)` (defined as `0` outside the contraction regime). -/
noncomputable def chi (x : ℝ) : Fock n → ℝ :=
  if h : |x| ≤ δ0 ε v O then Classical.choose (exists_fix (small_of_le_δ0 h)) else 0

variable (ε v O) in
/-- The exact eigenvector in intermediate normalization, `ψ(λ) = Φ + χ(λ)`. -/
noncomputable def psiR (x : ℝ) : Fock n → ℝ := phi O + chi ε v O x

variable (ε v O) in
/-- The exact eigenvalue `E(λ) = E0 + λ ⟨Φ|V ψ(λ)⟩`. -/
noncomputable def ER (x : ℝ) : ℝ := energy ε O + x * (vop v *ᵥ psiR ε v O x) O

theorem chi_spec {x : ℝ} (hx : |x| ≤ δ0 ε v O) :
    ‖chi ε v O x‖ ≤ 1 ∧ x • Fm ε v O (chi ε v O x) = chi ε v O x := by
  unfold chi; rw [dif_pos hx]; exact Classical.choose_spec (exists_fix (small_of_le_δ0 hx))

theorem chi_inSec {x : ℝ} (hx : |x| ≤ δ0 ε v O) : InSec O (chi ε v O x) := by
  rw [← (chi_spec hx).2]; exact (inSec_Rs _).smul x

theorem chi_self {x : ℝ} (hx : |x| ≤ δ0 ε v O) : chi ε v O x O = 0 := by
  rw [← (chi_spec hx).2]; simp [Fm, Rs_apply_self]

theorem psiR_inSec {x : ℝ} (hx : |x| ≤ δ0 ε v O) : InSec O (psiR ε v O x) :=
  inSec_phi.add (chi_inSec hx)

theorem psiR_self {x : ℝ} (hx : |x| ≤ δ0 ε v O) : psiR ε v O x O = 1 := by
  simp [psiR, chi_self hx, phi]

theorem psiR_ne_zero {x : ℝ} (hx : |x| ≤ δ0 ε v O) : psiR ε v O x ≠ 0 := fun h => by
  have := psiR_self (ε := ε) (v := v) hx; rw [h] at this; simp at this

/-- **The exact eigenvalue equation** `H(λ) ψ(λ) = E(λ) ψ(λ)`. -/
theorem eig_exact (hnd : NonDeg ε O) {x : ℝ} (hx : |x| ≤ δ0 ε v O) :
    Hl ε v x *ᵥ psiR ε v O x = ER ε v O x • psiR ε v O x := by
  set χ := chi ε v O x
  set ψ := psiR ε v O x
  set e := (vop v *ᵥ ψ) O
  have hfix : x • Fm ε v O χ = χ := (chi_spec hx).2
  set y := x • (vop v *ᵥ ψ - e • χ)
  have hy : InSec O y := ((psiR_inSec hx).vop.sub ((chi_inSec hx).smul e)).smul x
  have hχ : χ = Rs ε O *ᵥ y := by
    rw [← hfix, Fm, mulVec_smul]; rfl
  have hχO : χ O = 0 := chi_self hx
  have hyO : y O = x * e := by
    simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hχO, mul_zero, sub_zero]; rfl
  have hH0 := H0_Rs hnd hy
  rw [← hχ, hyO] at hH0
  have hpsi : ψ = phi O + χ := rfl
  have hphi : H0 ε *ᵥ phi O = energy ε O • phi O := phi_isEig ε O
  unfold Hl ER
  rw [add_mulVec, smul_mulVec_assoc]
  change H0 ε *ᵥ ψ + x • (vop v *ᵥ ψ) = (energy ε O + x * e) • ψ
  have hH0' : H0 ε *ᵥ χ = energy ε O • χ + (x * e) • phi O - y := by
    rw [add_sub_assoc, ← hH0]; abel
  rw [hpsi, mulVec_add, hphi, hH0']
  simp only [y, ← hpsi]
  rw [hpsi]
  module

/-! ### Expansion of the exact ground state -/

theorem Fm_zero : Fm ε v O 0 = psi1 ε v O := by
  simp only [Fm, add_zero, smul_zero, sub_zero, psi1]
  exact Rs_eq_Rr inSec_phi.vop

theorem chi_bound1 {x : ℝ} (hx : |x| ≤ δ0 ε v O) : ‖chi ε v O x‖ ≤ aC ε v O * |x| := by
  have h := chi_spec (ε := ε) (v := v) (O := O) hx
  rw [← h.2, norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_Fm_le h.1) (abs_nonneg x)

theorem chi_bound2 {x : ℝ} (hx : |x| ≤ δ0 ε v O) :
    ‖chi ε v O x - x • psi1 ε v O‖ ≤ aC ε v O ^ 2 * |x| ^ 2 := by
  have h := chi_spec (ε := ε) (v := v) (O := O) hx
  have ha := aC_nonneg (ε := ε) (v := v) (O := O)
  have e : chi ε v O x - x • psi1 ε v O = x • (Fm ε v O (chi ε v O x) - Fm ε v O 0) := by
    rw [smul_sub, h.2, Fm_zero]
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := norm_Fm_sub_le (ε := ε) (v := v) (O := O) h.1 (by rw [norm_zero]; exact zero_le_one)
  rw [sub_zero] at h1
  have h2 := chi_bound1 (ε := ε) (v := v) (O := O) hx
  calc |x| * ‖Fm ε v O (chi ε v O x) - Fm ε v O 0‖ ≤ |x| * (aC ε v O * (aC ε v O * |x|)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 ha)) (abs_nonneg x)
    _ = _ := by ring

variable (ε v O) in
/-- The linear part `A = Rs (V - E1)` of the fixed-point map. -/
noncomputable def Am : Matrix (Fock n) (Fock n) ℝ := Rs ε O * (vop v - E1 v O • 1)

theorem Am_psi1 : Am ε v O *ᵥ psi1 ε v O = psi2 ε v O := by
  rw [Am, ← mulVec_mulVec, sub_mulVec, smul_mulVec_assoc, one_mulVec, psi2]
  apply Rs_eq_Rr
  have h1 : InSec O (psi1 ε v O) := (inSec_iff _).2 psi1_num
  exact h1.vop.sub (h1.smul _)

theorem E1_eq : E1 v O = (vop v *ᵥ phi O) O := phi_dot _

theorem E2_eq : E2 ε v O = (vop v *ᵥ psi1 ε v O) O := phi_dot _

theorem Fm_expand (χ : Fock n → ℝ) :
    Fm ε v O χ = psi1 ε v O + Am ε v O *ᵥ χ - (vop v *ᵥ χ) O • (Rs ε O *ᵥ χ) := by
  rw [← Fm_zero]
  simp only [Fm, Am, ← mulVec_mulVec, sub_mulVec, smul_mulVec_assoc, one_mulVec, Rs,
    mulVec_diagonal, E1_eq]
  funext S
  simp only [mulVec_diagonal, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_add,
    add_zero, mulVec_zero, Pi.zero_apply, mul_zero, sub_zero, smul_zero]
  ring

variable (ε v O) in
/-- The third-order constant. -/
noncomputable def bC : ℝ :=
  mnorm (Am ε v O) * aC ε v O ^ 2 + mnorm (vop v) * mnorm (Rs ε O) * aC ε v O ^ 2

theorem chi_bound3 {x : ℝ} (hx : |x| ≤ δ0 ε v O) :
    ‖chi ε v O x - x • psi1 ε v O - x ^ 2 • psi2 ε v O‖ ≤ bC ε v O * |x| ^ 3 := by
  have h := chi_spec (ε := ε) (v := v) (O := O) hx
  have h1 := chi_bound1 (ε := ε) (v := v) (O := O) hx
  have h2 := chi_bound2 (ε := ε) (v := v) (O := O) hx
  set χ := chi ε v O x
  have ha := aC_nonneg (ε := ε) (v := v) (O := O)
  have hV := mnorm_nonneg (vop v)
  have hR := mnorm_nonneg (Rs ε O)
  have hA := mnorm_nonneg (Am ε v O)
  have e : χ - x • psi1 ε v O - x ^ 2 • psi2 ε v O =
      x • (Am ε v O *ᵥ (χ - x • psi1 ε v O)) - (x * (vop v *ᵥ χ) O) • (Rs ε O *ᵥ χ) := by
    conv_lhs => rw [← h.2]
    rw [Fm_expand, ← Am_psi1, mulVec_sub, mulVec_smul]
    module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hax := abs_nonneg x
  have t1 : ‖x • (Am ε v O *ᵥ (χ - x • psi1 ε v O))‖ ≤ mnorm (Am ε v O) * aC ε v O ^ 2 * |x| ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |x| * ‖Am ε v O *ᵥ (χ - x • psi1 ε v O)‖
        ≤ |x| * (mnorm (Am ε v O) * (aC ε v O ^ 2 * |x| ^ 2)) :=
          mul_le_mul_of_nonneg_left ((norm_mulVec_le _ _).trans
            (mul_le_mul_of_nonneg_left h2 hA)) hax
      _ = _ := by ring
  have t2 : ‖(x * (vop v *ᵥ χ) O) • (Rs ε O *ᵥ χ)‖ ≤
      mnorm (vop v) * mnorm (Rs ε O) * aC ε v O ^ 2 * |x| ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have hc1 : |(vop v *ᵥ χ) O| ≤ mnorm (vop v) * (aC ε v O * |x|) :=
      (abs_mulVec_le _ _ _).trans (mul_le_mul_of_nonneg_left h1 hV)
    have hc2 : ‖Rs ε O *ᵥ χ‖ ≤ mnorm (Rs ε O) * (aC ε v O * |x|) :=
      (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left h1 hR)
    calc |x| * |(vop v *ᵥ χ) O| * ‖Rs ε O *ᵥ χ‖
        ≤ |x| * (mnorm (vop v) * (aC ε v O * |x|)) * (mnorm (Rs ε O) * (aC ε v O * |x|)) := by
          gcongr
      _ = _ := by ring
  unfold bC; nlinarith

variable (ε v O) in
/-- The constant of the energy bound. -/
noncomputable def cC : ℝ := mnorm (vop v) * aC ε v O ^ 2

theorem E_bound {x : ℝ} (hx : |x| ≤ δ0 ε v O) :
    |ER ε v O x - (energy ε O + x * E1 v O + x ^ 2 * E2 ε v O)| ≤ cC ε v O * |x| ^ 3 := by
  have e : ER ε v O x - (energy ε O + x * E1 v O + x ^ 2 * E2 ε v O) =
      x * (vop v *ᵥ (chi ε v O x - x • psi1 ε v O)) O := by
    rw [ER, E1_eq, E2_eq, psiR, mulVec_add, mulVec_sub, mulVec_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, abs_mul]
  have h2 := chi_bound2 (ε := ε) (v := v) (O := O) hx
  have hV := mnorm_nonneg (vop v)
  calc |x| * |(vop v *ᵥ (chi ε v O x - x • psi1 ε v O)) O|
      ≤ |x| * (mnorm (vop v) * (aC ε v O ^ 2 * |x| ^ 2)) :=
        mul_le_mul_of_nonneg_left ((abs_mulVec_le _ _ _).trans
          (mul_le_mul_of_nonneg_left h2 hV)) (abs_nonneg x)
    _ = _ := by unfold cC; ring

/-! ### Ground state and simplicity -/

theorem exists_gap (hg : IsGround ε O) : ∃ g > 0, ∀ S : Fock n, S.card = O.card → S ≠ O →
    g ≤ energy ε S - energy ε O := by
  classical
  set s := univ.filter (fun S : Fock n => S.card = O.card ∧ S ≠ O)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun S hS hne => ?_⟩
    have : S ∈ s := by simp [s, hS, hne]
    rw [h] at this; simp at this
  · obtain ⟨S0, hS0, hmin⟩ := s.exists_min_image (fun S => energy ε S - energy ε O) h
    simp only [s, mem_filter, mem_univ, true_and] at hS0
    exact ⟨energy ε S0 - energy ε O, sub_pos.mpr (hg S0 hS0.1 hS0.2),
      fun S hS hne => hmin S (by simp [s, hS, hne])⟩

variable (ε v O) in
/-- Radius of the ground-state regime, for a gap `g`. -/
noncomputable def δ1 (g : ℝ) : ℝ := min (δ0 ε v O) (g / (8 * mnorm (vop v) + 1))

theorem δ1_pos {g : ℝ} (hg : 0 < g) : 0 < δ1 ε v O g := by
  unfold δ1; have := mnorm_nonneg (vop v)
  exact lt_min δ0_pos (by positivity)

theorem abs_psiR_apply_le {x : ℝ} (hx : |x| ≤ δ0 ε v O) {S : Fock n} (hS : S ≠ O) :
    |psiR ε v O x S| ≤ 1 := by
  have : psiR ε v O x S = chi ε v O x S := by simp [psiR, phi, Pi.single_apply, hS]
  rw [this]; exact (abs_le_norm _ S).trans (chi_spec hx).1

/-- **Gap argument.** For small `|λ|`, a sector eigenvector with eigenvalue `μ ≤ E(λ)` is a
multiple of `ψ(λ)`. -/
theorem eq_smul_psiR {g : ℝ} (hg0 : 0 < g)
    (hgap : ∀ S : Fock n, S.card = O.card → S ≠ O → g ≤ energy ε S - energy ε O)
    (hnd : NonDeg ε O) {x : ℝ} (hx : |x| ≤ δ1 ε v O g) {μ : ℝ} {φ : Fock n → ℝ}
    (hφ : InSec O φ) (heig : Hl ε v x *ᵥ φ = μ • φ) (hμ : μ ≤ ER ε v O x) :
    φ = φ O • psiR ε v O x := by
  have hx0 : |x| ≤ δ0 ε v O := hx.trans (min_le_left _ _)
  have hxg : |x| ≤ g / (8 * mnorm (vop v) + 1) := hx.trans (min_le_right _ _)
  have hV := mnorm_nonneg (vop v)
  have hax := abs_nonneg x
  have hxg' : |x| * (8 * mnorm (vop v) + 1) ≤ g := by
    rwa [le_div_iff₀ (by positivity)] at hxg
  have hs1 : |x| * mnorm (vop v) ≤ g / 8 := by nlinarith
  have hψ := eig_exact (v := v) hnd hx0
  have hψO := psiR_self (ε := ε) (v := v) hx0
  set ψ := psiR ε v O x
  set E := ER ε v O x
  set α := φ O
  set d := φ - α • ψ with hd
  have hdsec : InSec O d := hφ.sub ((psiR_inSec hx0).smul α)
  have hdO : d O = 0 := by simp [d, hψO, α]
  have key : Hl ε v x *ᵥ d - μ • d = (α * (μ - E)) • ψ := by
    rw [hd, mulVec_sub, mulVec_smul, heig, hψ]; module
  have hcomp : ∀ S, energy ε S * d S + x * (vop v *ᵥ d) S - μ * d S = α * (μ - E) * ψ S := by
    intro S
    have := congrFun key S
    simp only [Hl, add_mulVec, smul_mulVec_assoc, H0_eq_diagonal, mulVec_diagonal, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hVd : ∀ S, |(vop v *ᵥ d) S| ≤ mnorm (vop v) * ‖d‖ := fun S => abs_mulVec_le _ _ S
  have hD := norm_nonneg d
  have hαE : |α * (μ - E)| ≤ |x| * (mnorm (vop v) * ‖d‖) := by
    have h := hcomp O
    rw [hdO, hψO, mul_zero, mul_zero, zero_add, sub_zero, mul_one] at h
    rw [← h, abs_mul]; exact mul_le_mul_of_nonneg_left (hVd O) hax
  have hE : E - energy ε O ≤ g / 4 := by
    have h1 : E - energy ε O = x * (vop v *ᵥ ψ) O := by simp only [E, ER, ψ]; ring
    have h2 : |(vop v *ᵥ ψ) O| ≤ 2 * mnorm (vop v) := abs_vop_apply_le (chi_spec hx0).1
    rw [h1]
    calc x * (vop v *ᵥ ψ) O ≤ |x * (vop v *ᵥ ψ) O| := le_abs_self _
      _ = |x| * |(vop v *ᵥ ψ) O| := abs_mul _ _
      _ ≤ |x| * (2 * mnorm (vop v)) := mul_le_mul_of_nonneg_left h2 hax
      _ ≤ g / 4 := by nlinarith
  have hall : ∀ S, |d S| ≤ ‖d‖ / 2 := by
    intro S
    by_cases hSO : S = O
    · rw [hSO, hdO, abs_zero]; positivity
    by_cases hcard : S.card = O.card
    · have hES : g / 2 ≤ energy ε S - μ := by
        have := hgap S hcard hSO; linarith
      have h := hcomp S
      have e : (energy ε S - μ) * d S = α * (μ - E) * ψ S - x * (vop v *ᵥ d) S := by
        linarith
      have hb : |(energy ε S - μ) * d S| ≤ 2 * (|x| * (mnorm (vop v) * ‖d‖)) := by
        rw [e]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul (x)]
        have hψS := abs_psiR_apply_le (ε := ε) (v := v) hx0 hSO
        have t1 : |α * (μ - E)| * |ψ S| ≤ |x| * (mnorm (vop v) * ‖d‖) :=
          (mul_le_mul hαE hψS (abs_nonneg _) (by positivity)).trans (by rw [mul_one])
        have t2 : |x| * |(vop v *ᵥ d) S| ≤ |x| * (mnorm (vop v) * ‖d‖) :=
          mul_le_mul_of_nonneg_left (hVd S) hax
        linarith
      rw [abs_mul, abs_of_pos (by linarith : 0 < energy ε S - μ)] at hb
      have hdS := abs_nonneg (d S)
      have : g / 2 * |d S| ≤ g / 4 * ‖d‖ := by nlinarith
      nlinarith
    · rw [hdsec S hcard, abs_zero]; positivity
  have hle : ‖d‖ ≤ ‖d‖ / 2 := norm_le_of_abs_le (by positivity) hall
  have hd0 : d = 0 := norm_le_zero_iff.mp (by linarith)
  exact sub_eq_zero.mp hd0

variable (ε v O) in
/-- `(μ, φ)` is a ground pair of `H(λ)` in the `|O|`-particle sector: `φ` is a nonzero
sector eigenvector with eigenvalue `μ`, and no sector eigenvalue is below `μ`. -/
def IsGroundPair (x μ : ℝ) (φ : Fock n → ℝ) : Prop :=
  InSec O φ ∧ φ ≠ 0 ∧ Hl ε v x *ᵥ φ = μ • φ ∧
    ∀ (μ' : ℝ) (φ' : Fock n → ℝ), InSec O φ' → φ' ≠ 0 → Hl ε v x *ᵥ φ' = μ' • φ' → μ ≤ μ'

theorem eigval_eq_of_smul {x μ E α : ℝ} {φ ψ : Fock n → ℝ} (hφ0 : φ ≠ 0)
    (hφ : Hl ε v x *ᵥ φ = μ • φ) (hψ : Hl ε v x *ᵥ ψ = E • ψ) (he : φ = α • ψ) : μ = E := by
  have h1 : Hl ε v x *ᵥ φ = E • φ := by rw [he, mulVec_smul, hψ, smul_comm]
  rw [hφ] at h1
  have : (μ - E) • φ = 0 := by rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hφ0)

/-- **Existence.** `(E(λ), ψ(λ))` is a ground pair. -/
theorem groundPair_psiR {g : ℝ} (hg0 : 0 < g)
    (hgap : ∀ S : Fock n, S.card = O.card → S ≠ O → g ≤ energy ε S - energy ε O)
    (hnd : NonDeg ε O) {x : ℝ} (hx : |x| ≤ δ1 ε v O g) :
    IsGroundPair ε v O x (ER ε v O x) (psiR ε v O x) := by
  have hx0 : |x| ≤ δ0 ε v O := hx.trans (min_le_left _ _)
  refine ⟨psiR_inSec hx0, psiR_ne_zero hx0, eig_exact hnd hx0, fun μ' φ' hs hne he => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h := eq_smul_psiR hg0 hgap hnd hx hs he hlt.le
  have := eigval_eq_of_smul hne he (eig_exact hnd hx0) h
  linarith

/-- **Uniqueness (simplicity).** Every ground pair is `(E(λ), α ψ(λ))` with `α ≠ 0`. -/
theorem groundPair_unique {g : ℝ} (hg0 : 0 < g)
    (hgap : ∀ S : Fock n, S.card = O.card → S ≠ O → g ≤ energy ε S - energy ε O)
    (hnd : NonDeg ε O) {x μ : ℝ} {φ : Fock n → ℝ} (hx : |x| ≤ δ1 ε v O g)
    (h : IsGroundPair ε v O x μ φ) :
    μ = ER ε v O x ∧ φ = φ O • psiR ε v O x ∧ φ O ≠ 0 := by
  have hx0 : |x| ≤ δ0 ε v O := hx.trans (min_le_left _ _)
  have hle : μ ≤ ER ε v O x :=
    h.2.2.2 _ _ (psiR_inSec hx0) (psiR_ne_zero hx0) (eig_exact hnd hx0)
  have he := eq_smul_psiR hg0 hgap hnd hx h.1 h.2.2.1 hle
  refine ⟨eigval_eq_of_smul h.2.1 h.2.2.1 (eig_exact hnd hx0) he, he, fun h0 => h.2.1 ?_⟩
  rw [he, h0, zero_smul]

end GW.Endpoint.ManyBody

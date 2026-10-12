/-
A3(a), analytic bridge, part 3: the ACTUAL self-energy `λ ↦ Σ(ω; λ)` of the true
ground state, and its expansion to `O(λ³)`.

Real (not formal) definitions, literally the formulas of `Exact.lean` with the exact
ground pair `(E, ψ)` of `H(λ) = H0 + λ V` in place of the Rayleigh–Schrödinger series:

  G(ω; λ)_pq = [⟨ψ|c_p (ω - (H - E))⁻¹ c_q†|ψ⟩ + ⟨ψ|c_q† (ω + (H - E))⁻¹ c_p|ψ⟩] / ⟨ψ|ψ⟩,
  G0(ω) = diag (ω - ε_p)⁻¹,   Σ(ω; λ) = G0(ω)⁻¹ - G(ω; λ)⁻¹,

with real matrix inverses (`greenR`, `green0R`, `sigmaR`). `G` does not depend on the
normalization of `ψ` (`greenR_smul`).

Main theorem (`sigma_exact_expansion`). Assume `hv1`, `hv2` (the standing symmetries),
`IsGround ε O` (Φ is the strict ground state of `H0` in the `|O|`-particle sector) and
`OffPoles ε O ω`. Then there are `δ > 0` and `K` such that for all real `|λ| < δ`:

* `H(λ)` has a ground pair in the sector, `(E(λ), ψ(λ))`, and every ground pair is
  `(E(λ), α ψ(λ))` with `α ≠ 0` (the ground state is nondegenerate);
* `det(ω - (H - E)) ≠ 0`, `det(ω + (H - E)) ≠ 0` and `det G ≠ 0` (ω stays off the
  poles, and `Σ` is a genuine inverse);
* for every ground pair `(μ, φ)` and all `p, q`:

    |Σ(ω; λ)_pq - (λ Σ1_pq + λ² Σ2_pq(ω))| ≤ K |λ|³,

  with `Σ1_pq = Σ_{a∈O} ⟨pa||qa⟩` (Hartree–Fock) and
  `Σ2 = dir2 + sox2 + relax`: exactly the formal coefficients of `sigma1_eq_HF` and
  `sigma2_eq_direct_add_sox_add_relax` (they are imported, not re-derived).

Proof: `GroundState.lean` gives `ψ(λ) = Φ + λψ1 + λ²ψ2 + O(λ³)` and
`E(λ) = E0 + λE1 + λ²E2 + O(λ³)`; `Jet.lean` transports these through products,
dot products and inverses to `Σ(ω; λ) - trunc₂(sigmaT) = O(λ³)`.

GW side. In this repository the G0W0 self-energy is defined only through second order,
and no full RPA function of `λ` is defined. `sigmaGW2` is the polynomial
`Σ_GW^{≤2}(λ) = λ (Σ_H + Σ_x) + λ² dir2`, with `dir2` a sum of fractions under Lean's
totalized division (`x / 0 = 0`). It is identified with the G0W0 self-energy through
second order when `GWOffPoles ε O ω` holds: there `gw2_limit` proves that `dir2` is the
`η → 0⁺` limit of the damped transform of `Σ⁽²⁾_GW`. `OffPoles ε O ω` does not imply `GWOffPoles ε O ω`:
for `n = 2`, `ε = ![0, 1]`, `O = {0}`, `ω = 2`, `OffPoles` holds but
`ω + ε 0 - ε 1 - ε 1 = 0`, so `GWOffPoles` fails; with `v = 1` on `(0,0,1,1)` and
`(1,1,0,0)` and `0` elsewhere (which satisfies `hv1`, `hv2`; `IsGround` also holds), the
`(0, 0)` entry of the damped transform is `-I / η` for every `η > 0` and has no limit,
while `dir2` there is `0` (the totalized `1/0`). `sigma_exact_minus_gw` assumes
`OffPoles` (with `hv1`, `hv2`, `IsGround`) but not `GWOffPoles`: `|Σ(ω; λ) - Σ_GW^{≤2}(λ) - λ² (sox2 + relax)| ≤ K|λ|³`, and `relax = 0` under the
Brillouin condition (`sigma_exact_minus_gw_brillouin`). Where `GWOffPoles` fails, these
are statements about that polynomial at a frequency where the G0W0 second-order
self-energy itself may not exist (the theorems still hold there because Lean sets the
same `1/0` terms of `dir2` and `sox2` to `0`).

What is NOT claimed: analyticity in `λ` (only the `O(λ³)` bound), complex `λ`, anything
about the full RPA `W(λ)`, uniformity in `ω`.
-/
import GW.Endpoint.ManyBody.Jet
import GW.Endpoint.ManyBody.GroundState
import GW.Endpoint.ManyBody.GWError

namespace GW.Endpoint.ManyBody

open Matrix Finset PowerSeries Asymptotics Filter Topology

variable {n : ℕ} (ε : Fin n → ℝ) (v : Fin n → Fin n → Fin n → Fin n → ℝ) (O : Fock n) (ω : ℝ)

/-! ### The actual Green's function and self-energy -/

/-- `ω - (H(λ) - E)`. -/
noncomputable def MpR (x E : ℝ) : Matrix (Fock n) (Fock n) ℝ := ω • 1 - (Hl ε v x - E • 1)

/-- `ω + (H(λ) - E)`. -/
noncomputable def MmR (x E : ℝ) : Matrix (Fock n) (Fock n) ℝ := ω • 1 + (Hl ε v x - E • 1)

/-- **The actual Green's function** of `H(λ)` built from a state `ψ` with energy `E`. -/
noncomputable def greenR (x E : ℝ) (ψ : Fock n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q =>
    (ψ ⬝ᵥ ((ann p * (MpR ε v ω x E)⁻¹ * cre q) *ᵥ ψ) +
      ψ ⬝ᵥ ((cre q * (MmR ε v ω x E)⁻¹ * ann p) *ᵥ ψ)) * (ψ ⬝ᵥ ψ)⁻¹

/-- `G0(ω) = diag (ω - ε_p)⁻¹`. -/
noncomputable def green0R : Matrix (Fin n) (Fin n) ℝ := diagonal fun p => (ω - ε p)⁻¹

/-- **The actual self-energy** `Σ = G0⁻¹ - G⁻¹`. -/
noncomputable def sigmaR (x E : ℝ) (ψ : Fock n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (green0R ε ω)⁻¹ - (greenR ε v ω x E ψ)⁻¹

/-- The second-order coefficient `Σ2 = dir2 + sox2 + relax`. -/
noncomputable def sig2 (p q : Fin n) : ℝ := dir2 ε v O ω p q + sox2 ε v O ω p q + relax ε v O p q

variable {ε v O ω}

/-- `G` does not depend on the normalization of `ψ`. -/
theorem greenR_smul (x E : ℝ) (ψ : Fock n → ℝ) {α : ℝ} (hα : α ≠ 0) :
    greenR ε v ω x E (α • ψ) = greenR ε v ω x E ψ := by
  ext p q
  simp only [greenR, of_apply, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have h2 : α * α ≠ 0 := mul_ne_zero hα hα
  rw [show α * (α * ψ ⬝ᵥ ((ann p * (MpR ε v ω x E)⁻¹ * cre q) *ᵥ ψ)) +
      α * (α * ψ ⬝ᵥ ((cre q * (MmR ε v ω x E)⁻¹ * ann p) *ᵥ ψ)) =
      (α * α) * (ψ ⬝ᵥ ((ann p * (MpR ε v ω x E)⁻¹ * cre q) *ᵥ ψ) +
        ψ ⬝ᵥ ((cre q * (MmR ε v ω x E)⁻¹ * ann p) *ᵥ ψ)) by ring,
    show α * (α * ψ ⬝ᵥ ψ) = (α * α) * (ψ ⬝ᵥ ψ) by ring, mul_inv, mul_mul_mul_comm,
    mul_inv_cancel₀ h2, one_mul]

theorem sigmaR_smul (x E : ℝ) (ψ : Fock n → ℝ) {α : ℝ} (hα : α ≠ 0) :
    sigmaR ε v ω x E (α • ψ) = sigmaR ε v ω x E ψ := by
  rw [sigmaR, sigmaR, greenR_smul x E ψ hα]

/-! ### Jets of the ingredients -/

theorem eventually_le_δ0 : ∀ᶠ x in 𝓝 (0 : ℝ), |x| ≤ δ0 ε v O :=
  Metric.eventually_nhds_iff.2 ⟨δ0 ε v O, δ0_pos, fun y hy => by
    rw [Real.dist_eq, sub_zero] at hy; exact hy.le⟩

theorem jetV_psiR : JetV (psiR ε v O) (psiT ε v O) := by
  intro S
  unfold Jet
  refine IsBigO.of_bound (bC ε v O) ?_
  filter_upwards [eventually_le_δ0 (ε := ε) (v := v) (O := O)] with x hx
  have h0 : coeff ℝ 0 (psiT ε v O S) = phi O S := congrFun (cfv0_psiT (ε := ε) (v := v)) S
  have h1 : coeff ℝ 1 (psiT ε v O S) = psi1 ε v O S := congrFun (cfv1_psiT (ε := ε) (v := v)) S
  have h2 : coeff ℝ 2 (psiT ε v O S) = psi2 ε v O S := congrFun (cfv2_psiT (ε := ε) (v := v)) S
  have e : psiR ε v O x S - tr2 (psiT ε v O S) x =
      (chi ε v O x - x • psi1 ε v O - x ^ 2 • psi2 ε v O) S := by
    simp only [tr2, h0, h1, h2, psiR, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
  exact (abs_le_norm _ S).trans (chi_bound3 hx)

theorem jet_ER : Jet (ER ε v O) (ET ε v O) := by
  unfold Jet
  refine IsBigO.of_bound (cC ε v O) ?_
  filter_upwards [eventually_le_δ0 (ε := ε) (v := v) (O := O)] with x hx
  have e : tr2 (ET ε v O) x = energy ε O + x * E1 v O + x ^ 2 * E2 ε v O := by
    simp only [tr2, coeff_ET]; simp [E0]; ring
  rw [e, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
  exact E_bound hx

theorem jetM_Hl : JetM (Hl ε v) (HT ε v) := fun S S' =>
  jet_add (jet_const (H0 ε S S')) (jet_mul jet_X (jet_const (vop v S S')))

theorem jetM_K :
    JetM (fun x => Hl ε v x - ER ε v O x • (1 : Matrix (Fock n) (Fock n) ℝ)) (KT ε v O) :=
  jetM_Hl.sub (JetM.smul jet_ER jetM_one)

theorem jetM_Mp : JetM (fun x => MpR ε v ω x (ER ε v O x)) (MpT ε v O ω) :=
  (JetM.smul (jet_const ω) jetM_one).sub jetM_K

theorem jetM_Mm : JetM (fun x => MmR ε v ω x (ER ε v O x)) (MmT ε v O ω) :=
  (JetM.smul (jet_const ω) jetM_one).add jetM_K

theorem jetM_greenR (hω : OffPoles ε O ω) :
    JetM (fun x => greenR ε v ω x (ER ε v O x) (psiR ε v O x)) (greenT ε v O ω) := by
  intro p q
  have hψ := jetV_psiR (ε := ε) (v := v) (O := O)
  have hp := jetM_Mp.inv (MpT_det (v := v) hω)
  have hm := jetM_Mm.inv (MmT_det (v := v) hω)
  have hd : coeff ℝ 0 (dT ε v O) ≠ 0 := by rw [coeff0_dT]; exact one_ne_zero
  exact jet_mul (jet_add
    (hψ.dot (JetV.mulVec (((jetM_const (ann p)).mul hp).mul (jetM_const (cre q))) hψ))
    (hψ.dot (JetV.mulVec (((jetM_const (cre q)).mul hm).mul (jetM_const (ann p))) hψ)))
    (jet_inv (hψ.dot hψ) hd)

theorem isUnit_det_greenT (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω) :
    IsUnit (greenT ε v O ω).det := by
  have hL : (C ℝ ω • 1 - (dT ε v O)⁻¹ • KKT ε v O ω) * greenT ε v O ω = 1 := by
    rw [greenT_eq hv2]
    exact feshbach (HHT ε v O) (AT ε v O) (dT ε v O) (dT ε v O)⁻¹ (C ℝ ω) dT_inv_mul AT_gram
      (XT ε v O ω) (resolvent_XT hω) (NT ε v O ω)⁻¹ (nonsing_inv_mul _ (NT_det hω))
  exact isUnit_det_of_left_inverse hL

theorem jetM_green0 : JetM (fun _ => green0R ε ω) (green0 ε ω) := by
  intro p q
  by_cases h : p = q
  · subst h; simpa [green0R, green0] using jet_const (ω - ε p)⁻¹
  · simpa [green0R, green0, diagonal_apply_ne _ h] using jet_zero

theorem isUnit_det_green0 (hω : OffPoles ε O ω) : IsUnit (green0 ε ω).det := by
  refine isUnit_det_of_cf0 _ (diagonal fun p => ω - ε p) ?_
  have : cf 0 (green0 ε ω) = diagonal fun p => (ω - ε p)⁻¹ := by
    rw [green0, cf_diag_C, if_pos rfl]
  rw [this, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun p => mul_inv_cancel₀ (omega_ne_eps hω p))

/-- **Jet of the actual self-energy**: `Σ(ω; λ)` agrees with `sigmaT` to `O(λ³)`. -/
theorem jetM_sigmaR (hv2 : ∀ p q r s, v p q r s = v r s p q) (hω : OffPoles ε O ω) :
    JetM (fun x => sigmaR ε v ω x (ER ε v O x) (psiR ε v O x)) (sigmaT ε v O ω) :=
  (jetM_green0.inv (isUnit_det_green0 hω)).sub
    ((jetM_greenR hω).inv (isUnit_det_greenT hv2 hω))

theorem tr2_sigmaT (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hnd : NonDeg ε O) (hω : OffPoles ε O ω)
    (p q : Fin n) (x : ℝ) :
    tr2 (sigmaT ε v O ω p q) x = x * sig1 v O p q + x ^ 2 * sig2 ε v O ω p q := by
  have h0 := congrFun (congrFun (sigma_coeff0 hv1 hv2 hnd hω) p) q
  have h1 := congrFun (congrFun (sigma1_eq_HF hv1 hv2 hnd hω) p) q
  have h2 := congrFun (congrFun (sigma2_eq_direct_add_sox_add_relax hv1 hv2 hnd hω) p) q
  simp only [cf_apply, of_apply, zero_apply] at h0 h1 h2
  rw [tr2, h0, h1, h2, sig2, sig1]; ring

/-! ### The main theorem -/

/-- **The analytic statement.** For small real `λ` the true ground state of `H(λ)` in
the `|O|`-particle sector is nondegenerate, the Green's function is well defined
(`ω` stays off the poles), and for every ground pair
`|Σ(ω; λ)_pq - (λ Σ1_pq + λ² Σ2_pq(ω))| ≤ K |λ|³`. -/
theorem sigma_exact_expansion (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hg : IsGround ε O) (hω : OffPoles ε O ω) :
    ∃ δ > 0, ∃ K : ℝ, ∀ x : ℝ, |x| < δ →
      IsGroundPair ε v O x (ER ε v O x) (psiR ε v O x) ∧
      (∀ μ φ, IsGroundPair ε v O x μ φ → μ = ER ε v O x ∧ ∃ α : ℝ, α ≠ 0 ∧ φ = α • psiR ε v O x) ∧
      (MpR ε v ω x (ER ε v O x)).det ≠ 0 ∧ (MmR ε v ω x (ER ε v O x)).det ≠ 0 ∧
      (greenR ε v ω x (ER ε v O x) (psiR ε v O x)).det ≠ 0 ∧
      ∀ μ φ, IsGroundPair ε v O x μ φ → ∀ p q : Fin n,
        |sigmaR ε v ω x μ φ p q - (x * sig1 v O p q + x ^ 2 * sig2 ε v O ω p q)| ≤
          K * |x| ^ 3 := by
  have hnd := hg.nonDeg
  obtain ⟨g, hg0, hgap⟩ := exists_gap hg
  -- the remainder, summed over all entries
  set rem : ℝ → ℝ := fun x => ∑ p : Fin n, ∑ q : Fin n,
    |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p q - tr2 (sigmaT ε v O ω p q) x|
  have hrem : rem =O[𝓝 0] fun x => x ^ 3 :=
    IsBigO.sum fun p _ => IsBigO.sum fun q _ => (jetM_sigmaR hv2 hω p q).abs_left
  obtain ⟨K, hK⟩ := IsBigO.bound hrem
  have hball : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < δ1 ε v O g :=
    Metric.eventually_nhds_iff.2 ⟨δ1 ε v O g, δ1_pos hg0, fun y hy => by
      rwa [Real.dist_eq, sub_zero] at hy⟩
  have hev := hball.and ((jetM_Mp (ε := ε) (v := v) (O := O) (ω := ω)).eventually_det_ne
    (MpT_det hω) |>.and ((jetM_Mm (ε := ε) (v := v) (O := O) (ω := ω)).eventually_det_ne
    (MmT_det hω) |>.and (((jetM_greenR hω).eventually_det_ne (isUnit_det_greenT hv2 hω)).and
    hK)))
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, K, fun x hx => ?_⟩
  obtain ⟨hx1, hdp, hdm, hdg, hb⟩ := hall (y := x) (by rwa [Real.dist_eq, sub_zero])
  have hxle : |x| ≤ δ1 ε v O g := hx1.le
  refine ⟨groundPair_psiR hg0 hgap hnd hxle, fun μ φ h => ?_, hdp, hdm, hdg, fun μ φ h p q => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := groundPair_unique hg0 hgap hnd hxle h
    exact ⟨h1, φ O, h3, h2⟩
  · obtain ⟨h1, h2, h3⟩ := groundPair_unique hg0 hgap hnd hxle h
    rw [h1, h2, sigmaR_smul _ _ _ h3, ← tr2_sigmaT hv1 hv2 hnd hω p q x]
    have hle : |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p q - tr2 (sigmaT ε v O ω p q) x| ≤
        rem x := by
      have hnn : ∀ p' q', 0 ≤ |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p' q' -
          tr2 (sigmaT ε v O ω p' q') x| := fun _ _ => abs_nonneg _
      calc _ ≤ ∑ q' : Fin n, |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p q' -
            tr2 (sigmaT ε v O ω p q') x| :=
            single_le_sum (f := fun q' => |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p q' -
              tr2 (sigmaT ε v O ω p q') x|) (fun q' _ => hnn p q') (mem_univ q)
        _ ≤ rem x := single_le_sum (f := fun p' => ∑ q' : Fin n,
              |sigmaR ε v ω x (ER ε v O x) (psiR ε v O x) p' q' - tr2 (sigmaT ε v O ω p' q') x|)
            (fun p' _ => sum_nonneg fun q' _ => hnn p' q') (mem_univ p)
    have hrn : ‖rem x‖ = rem x := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
        abs_nonneg _)]
    rw [hrn, Real.norm_eq_abs, abs_pow] at hb
    exact hle.trans hb

/-! ### The GW side -/

variable (ε v O ω) in
/-- The polynomial `λ (Σ_H + Σ_x) + λ² dir2` in `λ`, with `dir2` under Lean's totalized
division. It is identified with the G0W0 self-energy through second order (`gw1_eq_HF`,
`gw2_limit`) when `GWOffPoles ε O ω` holds, which `OffPoles ε O ω` does not imply (module
docstring).
No higher order is defined. -/
noncomputable def sigmaGW2 (x : ℝ) (p q : Fin n) : ℝ :=
  x * (sigH v O p q + sigX v O p q) + x ^ 2 * dir2 ε v O ω p q

/-- **Exact minus the second-order GW polynomial** for the actual self-energy:
`Σ - Σ_GW^{≤2} = λ² (SOX + relax) + O(λ³)`, uniformly over the ground pairs. `Σ_GW^{≤2}`
(`sigmaGW2`) is identified with G0W0 through second order (`gw2_limit`) when
`GWOffPoles ε O ω` holds, which is not assumed here; elsewhere this is a statement about that polynomial at a frequency where
G0W0 itself may not exist. -/
theorem sigma_exact_minus_gw (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hg : IsGround ε O) (hω : OffPoles ε O ω) :
    ∃ δ > 0, ∃ K : ℝ, ∀ x : ℝ, |x| < δ → ∀ μ φ, IsGroundPair ε v O x μ φ → ∀ p q : Fin n,
      |sigmaR ε v ω x μ φ p q - sigmaGW2 ε v O ω x p q -
          x ^ 2 * (sox2 ε v O ω p q + relax ε v O p q)| ≤ K * |x| ^ 3 := by
  obtain ⟨δ, hδ, K, h⟩ := sigma_exact_expansion hv1 hv2 hg hω
  refine ⟨δ, hδ, K, fun x hx μ φ hp p q => ?_⟩
  have := (h x hx).2.2.2.2.2 μ φ hp p q
  convert this using 2
  simp only [sigmaGW2, gw1_eq_HF, sig2]; ring

/-- Under the Brillouin condition `Σ - Σ_GW^{≤2} = λ² SOX + O(λ³)`. It is the actual
error of G0W0 when `GWOffPoles ε O ω` holds (not assumed here; see
`sigma_exact_minus_gw`). -/
theorem sigma_exact_minus_gw_brillouin (hv1 : ∀ p q r s, v p q r s = v q p s r)
    (hv2 : ∀ p q r s, v p q r s = v r s p q) (hg : IsGround ε O) (hω : OffPoles ε O ω)
    (hB : ∀ a ∈ O, ∀ r ∉ O, sig1 v O r a = 0) :
    ∃ δ > 0, ∃ K : ℝ, ∀ x : ℝ, |x| < δ → ∀ μ φ, IsGroundPair ε v O x μ φ → ∀ p q : Fin n,
      |sigmaR ε v ω x μ φ p q - sigmaGW2 ε v O ω x p q - x ^ 2 * sox2 ε v O ω p q| ≤
        K * |x| ^ 3 := by
  obtain ⟨δ, hδ, K, h⟩ := sigma_exact_minus_gw hv1 hv2 hg hω
  refine ⟨δ, hδ, K, fun x hx μ φ hp p q => ?_⟩
  simpa [relax_eq_zero_of_brillouin hB] using h x hx μ φ hp p q

end GW.Endpoint.ManyBody

/-
BRIDGE B1: the G0W0 correlation self-energy with a pole-sum screened interaction,
derived by the damped Fourier transform of the time-domain product `i G0 W_c`,
and the Hybertsen-Louie SX/CH rewriting that BerkeleyGW uses.

Setting (finite basis, T = 0, time-ordered, one fixed matrix element `(p, q)`):

* orbitals `n ∈ S` (any finite set), energies `ε n`, occupied set `O`,
  occupation `f n = [n ∈ O]`;
* for every orbital `n` a finite set of poles `P n` of the screened interaction
  in the orbital-pair channel `(p n), (n q)`, with frequencies `w n k` and
  residues `R n k` (`R n k` is `B_k` of the task for this channel):

    W_c,(pn)(nq)(τ) = Σ_{k ∈ P n} -i R n k e^{-i w n k |τ|}        (`wct`)

  Its damped transform tends to the GPP frequency form
  `Σ_k R n k · 2 w / (ω² - w²)` (`wct_limit`), so this IS the time-ordered
  version of `W_c(ω) = Σ_k B_k 2 w_k / (ω² - w_k²)`.
* `G0_n(τ) = -i [θ(τ)(1 - f_n) - θ(-τ) f_n] e^{-i ε_n τ}` (`g0`, equal to
  `ManyBody.G0t` on `Fin N`: `g0_eq_G0t`);
* `Σ_c,pq(τ) = i Σ_n G0_n(τ) W_c,(pn)(nq)(τ)` (`sigt`, the orbital projection
  of `Σ(1,2) = i G0(1,2) W_c(1,2)`, as in `ManyBody.sigGW2t`).

Proved:

* `sigt_limit` (**B1 core**): for real `E` off the poles, the damped transform
  `ftDamped η sigt E` tends as `η → 0⁺` to

    Σ_c(E) = Σ_{n ∈ S} Σ_{k ∈ P n} R n k [ f_n / (E - ε_n + w) + (1 - f_n) / (E - ε_n - w) ]

  i.e. occupied orbitals give `B_k / (E - e_n + w_k)`, empty ones
  `B_k / (E - e_n - w_k)`, coefficient exactly `+1` each. The signs are derived
  (`ftDamped_twoSided_limit`), not assumed.
* `sigc_eq_terms`: for `w ≠ 0`, with `A = 2 w R` this is `Σ occupiedTerm A x w` over
  occupied and `Σ emptyTerm A x w` over empty orbitals (`x = E - ε_n`), the scalar
  branches of `GW.GPP.PoleCancellation`.
* `sigc_eq_sx_ch` (**HL rewriting**): for `w ≠ 0` and `x ≠ ±w` on occupied
  orbitals, `Σ_c = SX_c + CH` with

    SX_c(E) = Σ_{n ∈ S ∩ O} Σ_k -A / (x² - w²)    (screened exchange minus bare exchange)
    CH(E)   = Σ_{n ∈ S} Σ_k  A / (2 w (x - w))    (Coulomb hole, all orbitals)

  by `GW.GPP.rawOccupied_eq_occupiedTerm`, orbital by orbital.

Not claimed: finite temperature, non-time-ordered objects, a distributional
limit at the poles; the damping is put on the product (as in `GWSecond.lean`).
-/
import GW.Endpoint.ManyBody.GWSecond
import GW.GPP.PoleCancellation

namespace GW.Bridge

open Complex Finset Filter Topology MeasureTheory
open GW.Endpoint.HubbardDimer (ftDamped twoSided expSum ftDamped_twoSided_limit)

variable {ι κ : Type*} [DecidableEq ι]

/-- The data of B1: orbitals, energies, occupied set, and per orbital the poles of the
screened interaction in the channel `(p n), (n q)`. -/
structure PoleSys (ι κ : Type*) where
  S : Finset ι
  O : Finset ι
  ε : ι → ℝ
  P : ι → Finset κ
  w : ι → κ → ℝ
  R : ι → κ → ℝ

variable (D : PoleSys ι κ)

/-- Occupation `f_n ∈ {0, 1}`. -/
def PoleSys.f (n : ι) : ℝ := if n ∈ D.O then 1 else 0

/-- Time-ordered `G0_n(τ)`. -/
noncomputable def g0 (n : ι) (τ : ℝ) : ℂ :=
  -I * ((if 0 < τ then 1 - D.f n else -D.f n : ℝ) : ℂ) * Complex.exp (-(I * D.ε n * τ))

/-- Time-ordered pole-sum screened interaction in the channel of orbital `n`. -/
noncomputable def wct (n : ι) (τ : ℝ) : ℂ :=
  ∑ k ∈ D.P n, -I * (D.R n k : ℂ) * Complex.exp (-(I * D.w n k * ((|τ| : ℝ) : ℂ)))

/-- `Σ_c(τ) = i Σ_n G0_n(τ) W_c(τ)`. -/
noncomputable def sigt (τ : ℝ) : ℂ := I * ∑ n ∈ D.S, g0 D n τ * wct D n τ

/-- The closed form of B1. -/
noncomputable def sigc (E : ℝ) : ℝ :=
  ∑ n ∈ D.S, ∑ k ∈ D.P n,
    D.R n k * (D.f n / (E - D.ε n + D.w n k) + (1 - D.f n) / (E - D.ε n - D.w n k))

/-- The GPP frequency form of the screened interaction of channel `n`. -/
noncomputable def wcFreq (n : ι) (ω : ℝ) : ℝ :=
  ∑ k ∈ D.P n, D.R n k * (2 * D.w n k / (ω ^ 2 - D.w n k ^ 2))

/-! ### `g0` is the many-body `G0t` -/

theorem g0_eq_G0t {N : ℕ} (ε : Fin N → ℝ) (O : Finset (Fin N)) (P : Fin N → Finset κ)
    (w R : Fin N → κ → ℝ) (m : Fin N) (τ : ℝ) :
    g0 ⟨univ, O, ε, P, w, R⟩ m τ = GW.Endpoint.ManyBody.G0t ε O m τ := by
  simp only [g0, PoleSys.f, GW.Endpoint.ManyBody.G0t, GW.Endpoint.ManyBody.occ]

/-! ### Two-sided exponential form -/

/-- Forward (particle) list: `(-i R (1 - f), ε + w)`. -/
noncomputable def lp : List (ℂ × ℝ) :=
  (D.S.sigma D.P).toList.map fun x =>
    (-I * ((D.R x.1 x.2 * (1 - D.f x.1) : ℝ) : ℂ), D.ε x.1 + D.w x.1 x.2)

/-- Backward (hole) list: `(i R f, ε - w)`. -/
noncomputable def ln : List (ℂ × ℝ) :=
  (D.S.sigma D.P).toList.map fun x =>
    (I * ((D.R x.1 x.2 * D.f x.1 : ℝ) : ℂ), D.ε x.1 - D.w x.1 x.2)

omit [DecidableEq ι] in
theorem sum_sigma_toList {M : Type*} [AddCommMonoid M] (g : (Σ _ : ι, κ) → M) :
    ((D.S.sigma D.P).toList.map g).sum = ∑ n ∈ D.S, ∑ k ∈ D.P n, g ⟨n, k⟩ := by
  rw [Finset.sum_map_toList, Finset.sum_sigma]

theorem sigt_eq {τ : ℝ} (hτ : τ ≠ 0) : sigt D τ = twoSided (lp D) (ln D) τ := by
  unfold sigt twoSided expSum lp ln
  rw [List.map_map, List.map_map]
  split_ifs with h
  · rw [sum_sigma_toList, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [wct, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [g0, Function.comp, if_pos h, abs_of_pos h]
    push_cast
    rw [show -(I * ((D.ε n : ℂ) + (D.w n k : ℂ)) * (τ : ℂ)) =
      -(I * D.ε n * τ) + -(I * D.w n k * τ) by ring, Complex.exp_add]
    ring_nf; simp only [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring
  · have h' : τ < 0 := lt_of_le_of_ne (not_lt.mp h) hτ
    rw [sum_sigma_toList, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [wct, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [g0, Function.comp, if_neg h, abs_of_neg h']
    push_cast
    rw [show -(I * ((D.ε n : ℂ) - (D.w n k : ℂ)) * (τ : ℂ)) =
      -(I * D.ε n * τ) + -(I * D.w n k * -(τ : ℂ)) by ring, Complex.exp_add]
    ring_nf; simp only [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring

/-- The pole conditions: `E ≠ ε_n - w` on occupied, `E ≠ ε_n + w` on empty orbitals. -/
def OffPoles (E : ℝ) : Prop :=
  ∀ n ∈ D.S, ∀ k ∈ D.P n,
    (n ∈ D.O → E - D.ε n + D.w n k ≠ 0) ∧ (n ∉ D.O → E - D.ε n - D.w n k ≠ 0)

/-- **B1 core.** The damped Fourier transform of `Σ_c(τ) = i G0(τ) W_c(τ)` tends, as
`η → 0⁺`, to the closed form `sigc`, for real `E` off the poles. -/
theorem sigt_limit {E : ℝ} (hE : OffPoles D E) :
    Tendsto (fun η => ftDamped η (sigt D) E) (𝓝[>] 0) (𝓝 ((sigc D E : ℝ) : ℂ)) := by
  have hc : ∀ η, ftDamped η (sigt D) E = ftDamped η (twoSided (lp D) (ln D)) E :=
    fun η => GW.Endpoint.ManyBody.ftDamped_congr_ne_zero (fun τ hτ => sigt_eq D hτ) η E
  simp only [hc]
  convert ftDamped_twoSided_limit _ _ E ?_ ?_ using 2
  · unfold lp ln
    rw [List.map_map, List.map_map, sum_sigma_toList, sum_sigma_toList, ← sum_add_distrib]
    unfold sigc
    push_cast
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [Function.comp]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    ring_nf; rw [I_sq]; ring_nf
  · unfold lp
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_sigma]
    rintro _ ⟨⟨n, k⟩, ⟨hn, hk⟩, rfl⟩ hz
    have hO : n ∉ D.O := by
      intro h; apply hz; simp [PoleSys.f, h]
    have := (hE n hn k hk).2 hO
    intro h0; apply this; dsimp only at h0; linarith
  · unfold ln
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_sigma]
    rintro _ ⟨⟨n, k⟩, ⟨hn, hk⟩, rfl⟩ hz
    have hO : n ∈ D.O := by
      by_contra h; apply hz; simp [PoleSys.f, h]
    have := (hE n hn k hk).1 hO
    intro h0; apply this; dsimp only at h0; linarith

omit [DecidableEq ι] in
/-- The screened interaction `wct` is the time-ordered form of the GPP frequency form:
its damped transform tends to `Σ_k R · 2w/(ω² - w²)` for `ω ≠ ± w`. -/
theorem wct_limit (n : ι) {ω : ℝ} (hω : ∀ k ∈ D.P n, ω - D.w n k ≠ 0 ∧ ω + D.w n k ≠ 0) :
    Tendsto (fun η => ftDamped η (wct D n) ω) (𝓝[>] 0) (𝓝 ((wcFreq D n ω : ℝ) : ℂ)) := by
  have he : wct D n = twoSided ((D.P n).toList.map fun k => (-I * (D.R n k : ℂ), D.w n k))
      ((D.P n).toList.map fun k => (-I * (D.R n k : ℂ), -D.w n k)) := by
    funext τ
    unfold wct twoSided expSum
    rw [List.map_map, List.map_map]
    split_ifs with h
    · rw [Finset.sum_map_toList]
      refine sum_congr rfl fun k _ => ?_
      simp only [Function.comp, abs_of_pos h]
    · rw [Finset.sum_map_toList]
      refine sum_congr rfl fun k _ => ?_
      simp only [Function.comp, abs_of_nonpos (not_lt.mp h)]
      push_cast; ring_nf
  rw [he]
  convert ftDamped_twoSided_limit _ _ ω ?_ ?_ using 2
  · rw [List.map_map, List.map_map, Finset.sum_map_toList, Finset.sum_map_toList,
      ← sum_add_distrib, wcFreq]
    push_cast
    refine sum_congr rfl fun k hk => ?_
    simp only [Function.comp]
    have h1 : ((ω : ℂ) - D.w n k) ≠ 0 := by exact_mod_cast (hω k hk).1
    have h2 : ((ω : ℂ) + D.w n k) ≠ 0 := by exact_mod_cast (hω k hk).2
    have h3 : ((ω : ℂ) ^ 2 - (D.w n k : ℂ) ^ 2) ≠ 0 := by
      rw [show (ω : ℂ) ^ 2 - (D.w n k : ℂ) ^ 2 = (ω - D.w n k) * (ω + D.w n k) by ring]
      exact mul_ne_zero h1 h2
    rw [show (ω : ℂ) - ((-D.w n k : ℝ) : ℂ) = ω + D.w n k by push_cast; ring]
    field_simp
    ring_nf; rw [I_sq]; ring
  · simp only [List.mem_map, Finset.mem_toList]
    rintro _ ⟨k, hk, rfl⟩ _; exact (hω k hk).1
  · simp only [List.mem_map, Finset.mem_toList]
    rintro _ ⟨k, hk, rfl⟩ _
    intro h; apply (hω k hk).2; dsimp only at h; linarith

/-! ### The scalar branches and the Hybertsen-Louie SX/CH rewriting -/

/-- The GPP numerator `A = 2 w R` (`= Ω² · M v M` in the Bloch specialisation). -/
noncomputable def PoleSys.A (n : ι) (k : κ) : ℝ := 2 * D.w n k * D.R n k

theorem term_occ {R w x : ℝ} (hw : w ≠ 0) :
    R / (x + w) = GW.GPP.occupiedTerm (2 * w * R) x w := by
  unfold GW.GPP.occupiedTerm
  by_cases hx : x + w = 0
  · simp [hx]
  · field_simp; ring

theorem term_emp {R w x : ℝ} (hw : w ≠ 0) :
    R / (x - w) = GW.GPP.emptyTerm (2 * w * R) x w := by
  unfold GW.GPP.emptyTerm
  by_cases hx : x - w = 0
  · simp [hx]
  · field_simp; ring

/-- `sigc` as the occupied / empty scalar branches of `GW.GPP.PoleCancellation`. -/
theorem sigc_eq_terms (hw : ∀ n ∈ D.S, ∀ k ∈ D.P n, D.w n k ≠ 0) (E : ℝ) :
    sigc D E = ∑ n ∈ D.S, ∑ k ∈ D.P n,
      (if n ∈ D.O then GW.GPP.occupiedTerm (D.A n k) (E - D.ε n) (D.w n k)
       else GW.GPP.emptyTerm (D.A n k) (E - D.ε n) (D.w n k)) := by
  unfold sigc
  refine sum_congr rfl fun n hn => sum_congr rfl fun k hk => ?_
  have hw' := hw n hn k hk
  unfold PoleSys.f PoleSys.A
  split_ifs with h
  · rw [← term_occ hw', sub_self, zero_div, add_zero, mul_one_div]
  · rw [← term_emp hw', sub_zero, zero_div, zero_add, mul_one_div]

/-- Screened exchange minus bare exchange (occupied orbitals only). -/
noncomputable def sxc (E : ℝ) : ℝ :=
  ∑ n ∈ D.S, if n ∈ D.O then ∑ k ∈ D.P n,
    -D.A n k / ((E - D.ε n) ^ 2 - D.w n k ^ 2) else 0

/-- Coulomb hole (all orbitals). -/
noncomputable def ch (E : ℝ) : ℝ :=
  ∑ n ∈ D.S, ∑ k ∈ D.P n, D.A n k / (2 * D.w n k * ((E - D.ε n) - D.w n k))

/-- **Hybertsen-Louie rewriting.** Off the occupied poles `x = ± w` (and `w ≠ 0`),
the closed form is screened exchange on the occupied orbitals plus the Coulomb hole
over all orbitals. -/
theorem sigc_eq_sx_ch {E : ℝ} (hw : ∀ n ∈ D.S, ∀ k ∈ D.P n, D.w n k ≠ 0)
    (hocc : ∀ n ∈ D.S, n ∈ D.O → ∀ k ∈ D.P n,
      E - D.ε n ≠ D.w n k ∧ E - D.ε n ≠ -D.w n k) :
    sigc D E = sxc D E + ch D E := by
  rw [sigc_eq_terms D hw, sxc, ch, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h
  · rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := hocc n hn h k hk
    rw [← GW.GPP.rawOccupied_eq_occupiedTerm _ _ _ (hw n hn k hk) h1 h2, GW.GPP.rawOccupied]
  · rw [zero_add]
    refine sum_congr rfl fun k _ => ?_
    rfl

end GW.Bridge

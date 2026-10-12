/-
A3(b): a kernel-checked bound on the error of one-shot G0W0 for the fundamental
gap of the half-filled two-site Hubbard model.

    H = -t sum_sigma (c†_{1s} c_{2s} + h.c.) + U sum_i n_{i up} n_{i dn},  t > 0, U >= 0.

GW variant (named, and used consistently): **G0W0@HF** in the setup of
Romaniello, Guyot, Reining, J. Chem. Phys. 131, 154111 (2009):
* G0 = restricted Hartree-Fock Green's function: bonding orbital doubly
  occupied, HF eigenvalues `epsB = -t + U/2`, `epsA = t + U/2` (the U = 0 G
  shifted by Hartree + exchange = U/2; `fock_eq`, `hf_selfconsistent`);
* W = RPA screened interaction from the spin-summed chi0 of that G0 (one
  bonding-to-antibonding transition), with the spin-independent contact
  interaction `v_ij = U δ_ij` (`two_dbl_eq_normal_ordered` in the Fock file shows
  this is the Hubbard interaction); single pole at `h = sqrt(4t^2 + 4tU)`;
* Sigma_c = i G0 W_c, frequency integral by residues (single-pole W);
* QP energies from the FULL QP equation `E = eps_HF + Sigma_c(E)` (no
  linearisation, no Z factor), root selected as the unique root on the
  physical side of the self-energy pole.

Results (all for t > 0):
* `exact_gap` (HubbardDimerExact.lean): E0(3)+E0(1)-2E0(2) = sqrt(U^2+16t^2) - 2t.
* `gw_gap_of_qp`: any solutions of the two QP equations on the physical sides
  of the poles have difference `gapGW t U = sqrt((2t+h)^2 + 4tU^2/h) - h`.
* `gw_error_bounds`: for 0 <= U <= t,
     U^2/(8t) - 3U^3/(16t^2) <= gapGW - gapExact <= U^2/(8t) - U^3/(16t^2),
  hence `gw_error_abs`: |gapGW - gapExact| <= (1/8) U^2 / t.
* `hf_error_bounds`: -U^2/(8t) <= gapHF - gapExact <= -U^2/(8t) + U^4/(512 t^3).
* `gw_error_leading`, `hf_error_leading`: error / U^2 -> +1/(8t) and -1/(8t)
  as U -> 0+. Both errors START AT ORDER U^2, with equal magnitude and
  opposite sign: at leading order G0W0@HF is not better than HF in this model
  (it doubles the second-order correction, because the second-order exchange
  diagram is missing). `no_cubic_bound` proves the power 2 cannot be improved.
* `gw_beats_hf`: for 0 < U <= t, |GW error| < |HF error| (by a U^3 margin).

What this does NOT say:
* It is a result about a two-site model with an exactly known spectrum. It is
  NOT a bound for silicon, for Si-EPM, or for the BerkeleyGW run (no GPP, no
  plane waves, no frequency grid, no convergence parameters are involved).
* It is about G0W0@HF as specified above; other starting points (e.g. a
  Hartree-only G0 with poles at ∓t + U), self-consistent GW, or GW with a
  vertex give different numbers and are not covered.
* `sigmaSinglePole` is the T = 0 closed form of `i ∫ G0 W_c`. It is DERIVED
  in `GW/Endpoint/HubbardDimerSigma.lean` (`sigmaSinglePole_eq_limit`,
  `sigmaC_eq_limit`): the damped Fourier transform of the time-domain
  `Σ_c(τ) = i G0(τ) W_c(τ)` tends to it as η → 0⁺, for real ω off the poles.
  What remains a definition there is the time-domain product itself (T = 0,
  entrywise in the site indices, damping applied to the product).
* Real division is totalized in Lean; the QP statements carry explicit side
  conditions so that no zero-denominator value is used.
-/
import GW.Endpoint.HubbardDimerExact
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Basic

namespace GW.Endpoint.HubbardDimer

open Matrix Filter Topology

/-! ### One-body problem and restricted Hartree-Fock -/

/-- `1/sqrt 2`. -/
noncomputable def s2 : ℝ := Real.sqrt 2 / 2

theorem s2_sq : s2 ^ 2 = 1 / 2 := by
  unfold s2; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem s2_mul : s2 * s2 = 1 / 2 := by rw [← sq]; exact s2_sq

/-- Bonding and antibonding orbitals (site basis), and the site sign vector. -/
noncomputable def phiB : Fin 2 → ℝ := ![s2, s2]
noncomputable def phiA : Fin 2 → ℝ := ![s2, -s2]
def sgn : Fin 2 → ℝ := ![1, -1]

/-- One-body hopping matrix. -/
def h0 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -t; -t, 0]

theorem orbitals_orthonormal : phiB ⬝ᵥ phiB = 1 ∧ phiA ⬝ᵥ phiA = 1 ∧ phiB ⬝ᵥ phiA = 0 := by
  simp only [phiB, phiA, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> nlinarith [s2_sq]

theorem h0_orbitals (t : ℝ) : h0 t *ᵥ phiB = (-t) • phiB ∧ h0 t *ᵥ phiA = t • phiA := by
  constructor <;> funext i <;> fin_cases i <;> simp [h0, phiB, phiA, Matrix.mulVec, dotProduct]

/-- HF eigenvalues. -/
noncomputable def epsB (t U : ℝ) : ℝ := -t + U / 2
noncomputable def epsA (t U : ℝ) : ℝ := t + U / 2

/-- Per-spin density matrix of the bonding orbital. -/
noncomputable def rhoSpin : Matrix (Fin 2) (Fin 2) ℝ := Matrix.vecMulVec phiB phiB

/-- Fock matrix with `v_ij = U δ_ij`: Hartree `U n_i` (n_i = both spins) minus
local exchange `U rho_sigma(i,i)`. -/
noncomputable def fock (t U : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  h0 t + U • Matrix.diagonal (fun i => 2 * rhoSpin i i) - U • Matrix.diagonal (fun i => rhoSpin i i)

theorem fock_eq (t U : ℝ) : fock t U = h0 t + (U / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fock, rhoSpin, Matrix.vecMulVec_apply, phiB, h0, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, s2_mul] <;> ring

/-- Restricted HF is self-consistent: the Fock matrix built from the bonding
orbital has the same orbitals, with eigenvalues `epsB < epsA`, so the aufbau
occupation is again the bonding orbital. -/
theorem hf_selfconsistent {t : ℝ} (U : ℝ) (ht : 0 < t) :
    fock t U *ᵥ phiB = epsB t U • phiB ∧ fock t U *ᵥ phiA = epsA t U • phiA ∧
      epsB t U < epsA t U := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fock_eq]; funext i; fin_cases i <;>
      simp [h0, phiB, epsB, Matrix.mulVec, dotProduct, Matrix.add_apply] <;> ring
  · rw [fock_eq]; funext i; fin_cases i <;>
      simp [h0, phiA, epsA, Matrix.mulVec, dotProduct, Matrix.add_apply] <;> ring
  · unfold epsB epsA; linarith

/-! ### RPA screened interaction -/

/-- Spin-summed independent-particle response of `G0 = G_HF` (time-ordered,
real frequency, off the poles): one transition `phiB -> phiA`, energy
`epsA - epsB`, factor 2 for spin. -/
noncomputable def chi0 (t U ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => 2 * (phiB i * phiA i) * (phiA j * phiB j) *
    (1 / (ω - (epsA t U - epsB t U)) - 1 / (ω + (epsA t U - epsB t U)))

/-- Bare contact interaction `v_ij = U δ_ij`. -/
noncomputable def vC (U : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := U • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The RPA pole. -/
noncomputable def hRPA (t U : ℝ) : ℝ := Real.sqrt (4 * t ^ 2 + 4 * t * U)

theorem hRPA_sq {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) : hRPA t U ^ 2 = 4 * t ^ 2 + 4 * t * U :=
  Real.sq_sqrt (by positivity)

theorem hRPA_pos {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) : 0 < hRPA t U :=
  Real.sqrt_pos.mpr (by positivity)

/-- Correlation part of the screened interaction, `W - v`. -/
noncomputable def Wc (t U ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => sgn i * sgn j * (2 * t * U ^ 2 / (ω ^ 2 - hRPA t U ^ 2))

noncomputable def W (t U ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := vC U + Wc t U ω

theorem chi0_eq {t U ω : ℝ} (h1 : ω ^ 2 ≠ 4 * t ^ 2) :
    chi0 t U ω = Matrix.of fun i j => sgn i * sgn j * (2 * t / (ω ^ 2 - 4 * t ^ 2)) := by
  have hp : ∀ i, phiB i * phiA i = sgn i / 2 := by
    intro i; fin_cases i <;> simp [phiB, phiA, sgn] <;> nlinarith [s2_sq]
  have hp' : ∀ i, phiA i * phiB i = sgn i / 2 := fun i => by rw [mul_comm]; exact hp i
  have hd : epsA t U - epsB t U = 2 * t := by unfold epsA epsB; ring
  have hm : ω - 2 * t ≠ 0 := by
    intro h; apply h1; have e : ω = 2 * t := by linarith
    rw [e]; ring
  have hq : ω + 2 * t ≠ 0 := by
    intro h; apply h1; have e : ω = -(2 * t) := by linarith
    rw [e]; ring
  have hs : ω ^ 2 - 4 * t ^ 2 ≠ 0 := sub_ne_zero.mpr h1
  ext i j
  simp only [chi0, Matrix.of_apply, hp, hp', hd]
  field_simp
  ring

/-- **RPA.** Off the poles, `W` solves the Dyson equation `(1 - v chi0) W = v`. -/
theorem rpa_solves {t U ω : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ^ 2 ≠ 4 * t ^ 2)
    (h2 : ω ^ 2 ≠ hRPA t U ^ 2) : (1 - vC U * chi0 t U ω) * W t U ω = vC U := by
  rw [chi0_eq h1]
  have hs : ω ^ 2 - 4 * t ^ 2 ≠ 0 := sub_ne_zero.mpr h1
  have hh : ω ^ 2 - hRPA t U ^ 2 ≠ 0 := sub_ne_zero.mpr h2
  have hsq := hRPA_sq ht hU
  set k := 2 * t / (ω ^ 2 - 4 * t ^ 2) with hk
  set w := 2 * t * U ^ 2 / (ω ^ 2 - hRPA t U ^ 2) with hw
  have key : w * (1 - 2 * U * k) = U ^ 2 * k := by
    rw [hk, hw]; field_simp; rw [hsq]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, Wc, vC, sgn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.one_apply, ← hw] <;>
    first | linear_combination key | linear_combination (-1 : ℝ) * key

theorem rpa_det {t U ω : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ^ 2 ≠ 4 * t ^ 2) :
    (1 - vC U * chi0 t U ω).det = (ω ^ 2 - hRPA t U ^ 2) / (ω ^ 2 - 4 * t ^ 2) := by
  rw [chi0_eq h1, Matrix.det_fin_two, hRPA_sq ht hU]
  have hs : ω ^ 2 - 4 * t ^ 2 ≠ 0 := sub_ne_zero.mpr h1
  simp [vC, sgn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  field_simp
  ring

/-- `W` is THE RPA screened interaction: `W = (1 - v chi0)^{-1} v`. -/
theorem W_eq_inv {t U ω : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ^ 2 ≠ 4 * t ^ 2)
    (h2 : ω ^ 2 ≠ hRPA t U ^ 2) : W t U ω = (1 - vC U * chi0 t U ω)⁻¹ * vC U := by
  have hdet : IsUnit (1 - vC U * chi0 t U ω).det := by
    rw [rpa_det ht hU h1, isUnit_iff_ne_zero]
    exact div_ne_zero (sub_ne_zero.mpr h2) (sub_ne_zero.mpr h1)
  calc W t U ω = (1 - vC U * chi0 t U ω)⁻¹ * ((1 - vC U * chi0 t U ω) * W t U ω) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ hdet).symm
    _ = (1 - vC U * chi0 t U ω)⁻¹ * vC U := by rw [rpa_solves ht hU h1 h2]

/-- Residue matrix of the single RPA pole. -/
noncomputable def resW (t U : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => sgn i * sgn j * (t * U ^ 2 / hRPA t U)

/-- Single-pole form of the (time-ordered) screened interaction:
`W_c(ω) = R (1/(ω - h) - 1/(ω + h))`. -/
theorem Wc_single_pole {t U ω : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (h1 : ω ≠ hRPA t U)
    (h2 : ω ≠ -hRPA t U) :
    Wc t U ω = Matrix.of fun i j => resW t U i j * (1 / (ω - hRPA t U) - 1 / (ω + hRPA t U)) := by
  have hp := hRPA_pos ht hU
  have e1 : ω - hRPA t U ≠ 0 := sub_ne_zero.mpr h1
  have e2 : ω + hRPA t U ≠ 0 := by
    intro h; apply h2; linarith
  have e3 : ω ^ 2 - hRPA t U ^ 2 ≠ 0 := by
    have : ω ^ 2 - hRPA t U ^ 2 = (ω - hRPA t U) * (ω + hRPA t U) := by ring
    rw [this]; exact mul_ne_zero e1 e2
  ext i j
  simp only [Wc, resW, Matrix.of_apply]
  field_simp
  ring

/-! ### The G0W0 self-energy -/

/-- The T = 0 residue evaluation of `Sigma_c(ω) = i ∫ dω'/2π G0(ω+ω') W_c(ω')`
for `G0 = sum_k phi_k phi_k^T / (ω - eps_k ± i0)` (occupation `f_k`) and a
single-pole `W_c(ω') = R (1/(ω' - Ω + i0) - 1/(ω' + Ω - i0))`:

    Sigma_c,ij(ω) = sum_k phi_k(i) phi_k(j) R_ij [ f_k/(ω - eps_k + Ω) + (1 - f_k)/(ω - eps_k - Ω) ].

This closed form is used as the definition here; it is derived from the
time-domain `i G0(τ) W_c(τ)` in `GW/Endpoint/HubbardDimerSigma.lean`
(`sigmaSinglePole_eq_limit`), and `bgw/endpoint/a3_dimer/dimer.py` checks it
against a numerical imaginary-axis quadrature. -/
noncomputable def sigmaSinglePole (R : Matrix (Fin 2) (Fin 2) ℝ) (Ω : ℝ)
    (orbs : List ((Fin 2 → ℝ) × ℝ × Bool)) (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (orbs.map fun o => o.1 i * o.1 j * R i j *
    (if o.2.2 then 1 / (ω - o.2.1 + Ω) else 1 / (ω - o.2.1 - Ω))).sum

/-- G0W0@HF correlation self-energy of the dimer (per spin; site basis). -/
noncomputable def sigmaC (t U ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  sigmaSinglePole (resW t U) (hRPA t U) [(phiB, epsB t U, true), (phiA, epsA t U, false)] ω

/-- Orbital matrix elements of `Sigma_c`. -/
noncomputable def sigBB (t U E : ℝ) : ℝ := t * U ^ 2 / hRPA t U / (E - epsA t U - hRPA t U)
noncomputable def sigAA (t U E : ℝ) : ℝ := t * U ^ 2 / hRPA t U / (E - epsB t U + hRPA t U)

theorem s2_pow4 : s2 ^ 4 = 1 / 4 := by
  have : s2 ^ 4 = (s2 ^ 2) ^ 2 := by ring
  rw [this, s2_sq]; norm_num

/-- `Sigma_c` is diagonal in the orbital basis, with the bonding (removal)
element having its only pole at `epsA + h` and the antibonding (addition)
element its only pole at `epsB - h`. -/
theorem sigmaC_orbital (t U ω : ℝ) :
    phiB ⬝ᵥ (sigmaC t U ω *ᵥ phiB) = sigBB t U ω ∧
      phiA ⬝ᵥ (sigmaC t U ω *ᵥ phiA) = sigAA t U ω ∧
      phiA ⬝ᵥ (sigmaC t U ω *ᵥ phiB) = 0 ∧ phiB ⬝ᵥ (sigmaC t U ω *ᵥ phiA) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [sigmaC, sigmaSinglePole, resW, sigBB, sigAA, phiB, phiA, sgn, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] <;> ring_nf <;> simp only [s2_pow4] <;> ring_nf

/-! ### Full QP equations and the G0W0@HF gap -/

/-- `D = sqrt((2t + h)^2 + 4 t U^2 / h)`, the discriminant root of the QP quadratics. -/
noncomputable def Dgw (t U : ℝ) : ℝ :=
  Real.sqrt ((2 * t + hRPA t U) ^ 2 + 4 * t * U ^ 2 / hRPA t U)

/-- Removal (bonding) and addition (antibonding) QP energies. -/
noncomputable def Erem (t U : ℝ) : ℝ := epsB t U + ((2 * t + hRPA t U) - Dgw t U) / 2
noncomputable def Eadd (t U : ℝ) : ℝ := epsA t U - ((2 * t + hRPA t U) - Dgw t U) / 2

/-- The G0W0@HF gap. -/
noncomputable def gapGW (t U : ℝ) : ℝ := Dgw t U - hRPA t U

section QP
variable {t U : ℝ}

theorem Dgw_sq (ht : 0 < t) (hU : 0 ≤ U) :
    Dgw t U ^ 2 = (2 * t + hRPA t U) ^ 2 + 4 * (t * U ^ 2 / hRPA t U) := by
  have hp := hRPA_pos ht hU
  unfold Dgw; rw [Real.sq_sqrt (by positivity)]; ring

theorem Dgw_ge (ht : 0 < t) (hU : 0 ≤ U) : 2 * t + hRPA t U ≤ Dgw t U := by
  have hp := hRPA_pos ht hU
  unfold Dgw
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have : 0 ≤ 4 * t * U ^ 2 / hRPA t U := by positivity
  linarith

/-- **Removal QP equation.** On the physical side of the self-energy pole
(`E < epsA + h`, the side containing the HF level `epsB`), the full QP
equation `E = epsB + Sigma_bb(E)` has exactly one solution, `Erem`. -/
theorem qp_removal (ht : 0 < t) (hU : 0 ≤ U) (E : ℝ) (hE : E < epsA t U + hRPA t U) :
    E = epsB t U + sigBB t U E ↔ E = Erem t U := by
  have hp := hRPA_pos ht hU
  have hD := Dgw_sq ht hU
  have hDge := Dgw_ge ht hU
  have hAB : epsA t U = epsB t U + 2 * t := by unfold epsA epsB; ring
  unfold sigBB Erem
  set c := t * U ^ 2 / hRPA t U
  set D := Dgw t U
  set P := 2 * t + hRPA t U
  have hden : E - epsA t U - hRPA t U = (E - epsB t U) - P := by rw [hAB]; ring
  rw [hden]
  have hden' : (E - epsB t U) - P ≠ 0 := by rw [← hden]; linarith
  constructor
  · intro h
    have h2 : (E - epsB t U) * ((E - epsB t U) - P) = c := by
      have e : E - epsB t U = c / ((E - epsB t U) - P) := by linarith
      rw [eq_div_iff hden'] at e; exact e
    have hq : (E - epsB t U - (P - D) / 2) * (E - epsB t U - (P + D) / 2) = 0 := by
      linear_combination h2 - hD / 4
    rcases mul_eq_zero.mp hq with h3 | h3
    · linarith
    · exfalso; rw [hAB] at hE; linarith
  · intro h
    have hy : E - epsB t U = (P - D) / 2 := by rw [h]; ring
    have hPD : P + D ≠ 0 := by linarith
    have : c / ((E - epsB t U) - P) = (P - D) / 2 := by
      rw [hy, div_eq_iff (by intro h0; apply hPD; linarith)]
      linear_combination (-1 / 4 : ℝ) * hD
    rw [this, h]

theorem Erem_side (ht : 0 < t) (hU : 0 ≤ U) : Erem t U < epsA t U + hRPA t U := by
  have hDge := Dgw_ge ht hU
  have hp := hRPA_pos ht hU
  unfold Erem epsA epsB; linarith

/-- **Addition QP equation.** On the physical side of the pole (`epsB - h < E`),
`E = epsA + Sigma_aa(E)` has exactly one solution, `Eadd`. -/
theorem qp_addition (ht : 0 < t) (hU : 0 ≤ U) (E : ℝ) (hE : epsB t U - hRPA t U < E) :
    E = epsA t U + sigAA t U E ↔ E = Eadd t U := by
  have hp := hRPA_pos ht hU
  have hD := Dgw_sq ht hU
  have hDge := Dgw_ge ht hU
  have hAB : epsA t U = epsB t U + 2 * t := by unfold epsA epsB; ring
  unfold sigAA Eadd
  set c := t * U ^ 2 / hRPA t U
  set D := Dgw t U
  set P := 2 * t + hRPA t U
  have hden : E - epsB t U + hRPA t U = (E - epsA t U) + P := by rw [hAB]; ring
  rw [hden]
  have hden' : (E - epsA t U) + P ≠ 0 := by rw [← hden]; linarith
  constructor
  · intro h
    have h2 : (E - epsA t U) * ((E - epsA t U) + P) = c := by
      have e : E - epsA t U = c / ((E - epsA t U) + P) := by linarith
      rw [eq_div_iff hden'] at e; exact e
    have hq : (E - epsA t U + (P - D) / 2) * (E - epsA t U + (P + D) / 2) = 0 := by
      linear_combination h2 - hD / 4
    rcases mul_eq_zero.mp hq with h3 | h3
    · linarith
    · exfalso
      have hP : P = 2 * t + hRPA t U := rfl
      rw [hAB] at h3; linarith
  · intro h
    have hy : E - epsA t U = -(P - D) / 2 := by rw [h]; ring
    have hPD : P + D ≠ 0 := by linarith
    have : c / ((E - epsA t U) + P) = -(P - D) / 2 := by
      rw [hy, div_eq_iff (by intro h0; apply hPD; linarith)]
      linear_combination (-1 / 4 : ℝ) * hD
    rw [this, h]; ring

theorem Eadd_side (ht : 0 < t) (hU : 0 ≤ U) : epsB t U - hRPA t U < Eadd t U := by
  have hDge := Dgw_ge ht hU
  have hp := hRPA_pos ht hU
  unfold Eadd epsA epsB; linarith

/-- **G0W0@HF gap from the full QP equations.** QP solutions exist on the
physical sides of the poles, and ANY such pair has
`E_add - E_rem = gapGW t U = sqrt((2t + h)^2 + 4tU^2/h) - h`. -/
theorem gw_gap_of_qp (ht : 0 < t) (hU : 0 ≤ U) :
    (Erem t U < epsA t U + hRPA t U ∧ Erem t U = epsB t U + sigBB t U (Erem t U)) ∧
    (epsB t U - hRPA t U < Eadd t U ∧ Eadd t U = epsA t U + sigAA t U (Eadd t U)) ∧
    ∀ Er Ea : ℝ, Er < epsA t U + hRPA t U → Er = epsB t U + sigBB t U Er →
      epsB t U - hRPA t U < Ea → Ea = epsA t U + sigAA t U Ea → Ea - Er = gapGW t U := by
  refine ⟨⟨Erem_side ht hU, (qp_removal ht hU _ (Erem_side ht hU)).mpr rfl⟩,
    ⟨Eadd_side ht hU, (qp_addition ht hU _ (Eadd_side ht hU)).mpr rfl⟩, ?_⟩
  intro Er Ea hr hr' ha ha'
  rw [(qp_removal ht hU Er hr).mp hr', (qp_addition ht hU Ea ha).mp ha']
  unfold Eadd Erem gapGW epsA epsB; ring

/-- At `U = 0` everything reduces to the noninteracting gap `2t`. -/
theorem gapGW_zero (ht : 0 < t) : gapGW t 0 = 2 * t := by
  have h2 : hRPA t 0 = 2 * t := by
    unfold hRPA; rw [show 4 * t ^ 2 + 4 * t * 0 = (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  unfold gapGW Dgw; rw [h2]
  rw [show (2 * t + 2 * t) ^ 2 + 4 * t * 0 ^ 2 / (2 * t) = (4 * t) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]
  ring

end QP

/-! ### Hartree-Fock baseline -/

/-- Koopmans HF gap `epsA - epsB`. -/
noncomputable def gapHF (t U : ℝ) : ℝ := epsA t U - epsB t U

theorem gapHF_eq (t U : ℝ) : gapHF t U = 2 * t := by unfold gapHF epsA epsB; ring

/-! ### The error bounds -/

section Bounds

theorem pw_pos {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 2) :
    0 < 524288 - 212992 * w - 303104 * w ^ 2 - 172032 * w ^ 3 - 106496 * w ^ 4 - 9152 * w ^ 5
      + 26880 * w ^ 6 + 15024 * w ^ 7 + 4368 * w ^ 8 + 924 * w ^ 9 + 136 * w ^ 10
      + 13 * w ^ 11 + w ^ 12 := by
  have e2 : w ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have e3 : w ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have e4 : w ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ h0 h1 4
  have e5 : w ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ h0 h1 5
  have hpos : 0 ≤ 26880 * w ^ 6 + 15024 * w ^ 7 + 4368 * w ^ 8 + 924 * w ^ 9 + 136 * w ^ 10
      + 13 * w ^ 11 + w ^ 12 := by positivity
  norm_num at e2 e3 e4 e5
  linarith

theorem qw_pos {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 2) :
    0 < 1216 + 1024 * w + 448 * w ^ 2 - 16 * w ^ 3 - 336 * w ^ 4 - 264 * w ^ 5 - 81 * w ^ 6
      - 9 * w ^ 7 := by
  have e3 : w ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have e4 : w ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ h0 h1 4
  have e5 : w ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ h0 h1 5
  have e6 : w ^ 6 ≤ (1 / 2) ^ 6 := pow_le_pow_left₀ h0 h1 6
  have e7 : w ^ 7 ≤ (1 / 2) ^ 7 := pow_le_pow_left₀ h0 h1 7
  have hpos : 0 ≤ 1024 * w + 448 * w ^ 2 := by positivity
  norm_num at e3 e4 e5 e6 e7
  linarith

/-- Upper polynomial for the scaled QP discriminant (`a = h / 2t`, `u = a^2 - 1 = U/t`). -/
noncomputable def Xup (a : ℝ) : ℝ :=
  2 * a + 2 + (a ^ 2 - 1) ^ 2 / 4 - (a ^ 2 - 1) ^ 3 / 16 - (a ^ 2 - 1) ^ 4 / 512
/-- Lower polynomial. -/
noncomputable def Ylo (a : ℝ) : ℝ := 2 * a + 2 + (a ^ 2 - 1) ^ 2 / 4 - 3 * (a ^ 2 - 1) ^ 3 / 16

theorem polyX {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 3 / 2) :
    a * (2 + 2 * a) ^ 2 + 2 * (a ^ 2 - 1) ^ 2 ≤ a * Xup a ^ 2 := by
  set w := a - 1 with hw
  have ha : a = 1 + w := by rw [hw]; ring
  have hw0 : 0 ≤ w := by linarith
  have hw1 : w ≤ 1 / 2 := by linarith
  have hp := pw_pos hw0 hw1
  have hid : a * Xup a ^ 2 - (a * (2 + 2 * a) ^ 2 + 2 * (a ^ 2 - 1) ^ 2) =
      w ^ 3 * (w + 2) ^ 2 * (524288 - 212992 * w - 303104 * w ^ 2 - 172032 * w ^ 3
        - 106496 * w ^ 4 - 9152 * w ^ 5 + 26880 * w ^ 6 + 15024 * w ^ 7 + 4368 * w ^ 8
        + 924 * w ^ 9 + 136 * w ^ 10 + 13 * w ^ 11 + w ^ 12) / 262144 := by
    rw [ha]; unfold Xup; ring
  have : 0 ≤ w ^ 3 * (w + 2) ^ 2 * (524288 - 212992 * w - 303104 * w ^ 2 - 172032 * w ^ 3
        - 106496 * w ^ 4 - 9152 * w ^ 5 + 26880 * w ^ 6 + 15024 * w ^ 7 + 4368 * w ^ 8
        + 924 * w ^ 9 + 136 * w ^ 10 + 13 * w ^ 11 + w ^ 12) / 262144 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (mul_nonneg (pow_nonneg hw0 3) (sq_nonneg _)) hp.le
  linarith

theorem polyY {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 3 / 2) :
    a * Ylo a ^ 2 ≤ a * (2 + 2 * a) ^ 2 + 2 * (a ^ 2 - 1) ^ 2 := by
  set w := a - 1 with hw
  have ha : a = 1 + w := by rw [hw]; ring
  have hw0 : 0 ≤ w := by linarith
  have hw1 : w ≤ 1 / 2 := by linarith
  have hq := qw_pos hw0 hw1
  have hid : a * (2 + 2 * a) ^ 2 + 2 * (a ^ 2 - 1) ^ 2 - a * Ylo a ^ 2 =
      w ^ 4 * (w + 2) ^ 2 * (1216 + 1024 * w + 448 * w ^ 2 - 16 * w ^ 3 - 336 * w ^ 4
        - 264 * w ^ 5 - 81 * w ^ 6 - 9 * w ^ 7) / 256 := by
    rw [ha]; unfold Ylo; ring
  have : 0 ≤ w ^ 4 * (w + 2) ^ 2 * (1216 + 1024 * w + 448 * w ^ 2 - 16 * w ^ 3 - 336 * w ^ 4
        - 264 * w ^ 5 - 81 * w ^ 6 - 9 * w ^ 7) / 256 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (mul_nonneg (pow_nonneg hw0 4) (sq_nonneg _)) hq.le
  linarith

theorem Xup_Ylo_nonneg {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 3 / 2) : 0 ≤ Xup a ∧ 0 ≤ Ylo a := by
  set u := a ^ 2 - 1 with hu
  have hu0 : 0 ≤ u := by nlinarith
  have hu1 : u ≤ 5 / 4 := by nlinarith
  have e3 : u ^ 3 ≤ (5 / 4) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have e4 : u ^ 4 ≤ (5 / 4) ^ 4 := pow_le_pow_left₀ hu0 hu1 4
  have e2 : 0 ≤ u ^ 2 := sq_nonneg u
  unfold Xup Ylo
  rw [← hu]
  norm_num at e3 e4
  constructor <;> nlinarith

/-- The dimensionless core: with `h = 2 t a`, `U = t (a^2 - 1)`, `1 <= a <= 3/2`. -/
theorem core_bounds {t a : ℝ} (ht : 0 < t) (h1 : 1 ≤ a) (h2 : a ≤ 3 / 2) :
    t * Ylo a ≤ Real.sqrt ((2 * t + 2 * t * a) ^ 2 + 4 * t * (t * (a ^ 2 - 1)) ^ 2 / (2 * t * a)) ∧
    Real.sqrt ((2 * t + 2 * t * a) ^ 2 + 4 * t * (t * (a ^ 2 - 1)) ^ 2 / (2 * t * a)) ≤ t * Xup a := by
  have ha : 0 < a := by linarith
  obtain ⟨hX, hY⟩ := Xup_Ylo_nonneg h1 h2
  have harg : (2 * t + 2 * t * a) ^ 2 + 4 * t * (t * (a ^ 2 - 1)) ^ 2 / (2 * t * a) =
      t ^ 2 * (a * (2 + 2 * a) ^ 2 + 2 * (a ^ 2 - 1) ^ 2) / a := by
    field_simp; ring
  rw [harg]
  constructor
  · rw [Real.le_sqrt (by positivity) (by positivity), le_div_iff₀ ha]
    have := polyY h1 h2
    nlinarith [sq_nonneg t]
  · rw [Real.sqrt_le_left (by positivity), div_le_iff₀ ha]
    have := polyX h1 h2
    nlinarith [sq_nonneg t]

/-- Two-sided bounds on the exact gap's square root, `u = U/t`. -/
theorem exact_sqrt_bounds {t u : ℝ} (ht : 0 < t) (hu0 : 0 ≤ u) (hu1 : u ≤ 2) :
    t * (4 + u ^ 2 / 8 - u ^ 4 / 512) ≤ Real.sqrt ((t * u) ^ 2 + 16 * t ^ 2) ∧
    Real.sqrt ((t * u) ^ 2 + 16 * t ^ 2) ≤ t * (4 + u ^ 2 / 8) := by
  have e2 : u ^ 2 ≤ 4 := by nlinarith
  have e4 : u ^ 4 ≤ 16 := by nlinarith
  constructor
  · rw [Real.le_sqrt (by nlinarith) (by positivity)]
    have : (t * (4 + u ^ 2 / 8 - u ^ 4 / 512)) ^ 2 =
        t ^ 2 * (16 + u ^ 2) - t ^ 2 * u ^ 6 * (128 - u ^ 2) / 262144 := by ring
    rw [this]
    have : 0 ≤ t ^ 2 * u ^ 6 * (128 - u ^ 2) / 262144 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (by positivity) (by linarith)
    nlinarith
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (t * u ^ 2)]

theorem exists_scale {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t) :
    ∃ a : ℝ, 1 ≤ a ∧ a ≤ 3 / 2 ∧ hRPA t U = 2 * t * a ∧ U = t * (a ^ 2 - 1) := by
  have hp := hRPA_pos ht hU
  have hsq := hRPA_sq ht hU
  refine ⟨hRPA t U / (2 * t), ?_, ?_, by field_simp, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · field_simp; rw [hsq]; ring

/-- **Main result (G0W0@HF vs exact).** For `t > 0` and `0 <= U <= t`,

    U^2/(8t) - 3 U^3/(16 t^2) <= gapGW - gapExact <= U^2/(8t) - U^3/(16 t^2). -/
theorem gw_error_bounds {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t) :
    U ^ 2 / (8 * t) - 3 * U ^ 3 / (16 * t ^ 2) ≤ gapGW t U - gapExact t U ∧
      gapGW t U - gapExact t U ≤ U ^ 2 / (8 * t) - U ^ 3 / (16 * t ^ 2) := by
  obtain ⟨a, h1, h2, hh, hUa⟩ := exists_scale ht hU hUt
  have hcore := core_bounds ht h1 h2
  set u := a ^ 2 - 1 with hu
  have hu0 : 0 ≤ u := by nlinarith
  have hu1 : u ≤ 2 := by nlinarith
  have hex := exact_sqrt_bounds ht hu0 hu1
  unfold gapGW Dgw gapExact
  rw [hh, hUa]
  rw [hUa] at hU
  have e1 : (t * u) ^ 2 / (8 * t) - 3 * (t * u) ^ 3 / (16 * t ^ 2) = t * (u ^ 2 / 8 - 3 * u ^ 3 / 16) := by
    field_simp; ring
  have e2 : (t * u) ^ 2 / (8 * t) - (t * u) ^ 3 / (16 * t ^ 2) = t * (u ^ 2 / 8 - u ^ 3 / 16) := by
    field_simp; ring
  rw [e1, e2]
  have hX : Xup a = 2 * a + 2 + u ^ 2 / 4 - u ^ 3 / 16 - u ^ 4 / 512 := by unfold Xup; rw [hu]
  have hY : Ylo a = 2 * a + 2 + u ^ 2 / 4 - 3 * u ^ 3 / 16 := by unfold Ylo; rw [hu]
  rw [hX] at hcore; rw [hY] at hcore
  constructor <;> nlinarith [hcore.1, hcore.2, hex.1, hex.2]

/-- **Headline bound.** `|gapGW - gapExact| <= (1/8) U^2 / t` for `0 <= U <= t`. -/
theorem gw_error_abs {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t) :
    |gapGW t U - gapExact t U| ≤ (1 / 8) * U ^ 2 / t := by
  obtain ⟨hl, hu⟩ := gw_error_bounds ht hU hUt
  have k1 : U ^ 3 / (16 * t ^ 2) ≥ 0 := by positivity
  have k2 : 3 * U ^ 3 / (16 * t ^ 2) ≤ 2 * (U ^ 2 / (8 * t)) := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (U ^ 2 / (8 * t)) * (16 * t ^ 2) = 4 * U ^ 2 * t := by field_simp; ring
    rw [this]; nlinarith [sq_nonneg U, mul_nonneg (sq_nonneg U) hU]
  have e : (1 / 8) * U ^ 2 / t = U ^ 2 / (8 * t) := by field_simp
  rw [abs_le, e]; constructor <;> linarith

/-- **HF baseline.** For `t > 0`, `0 <= U <= 2t`:
`-U^2/(8t) <= gapHF - gapExact <= -U^2/(8t) + U^4/(512 t^3)`. -/
theorem hf_error_bounds {t U : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ 2 * t) :
    -(U ^ 2 / (8 * t)) ≤ gapHF t U - gapExact t U ∧
      gapHF t U - gapExact t U ≤ -(U ^ 2 / (8 * t)) + U ^ 4 / (512 * t ^ 3) := by
  set u := U / t with hu
  have hUu : U = t * u := by rw [hu]; field_simp
  have hu0 : 0 ≤ u := div_nonneg hU ht.le
  have hu1 : u ≤ 2 := by rw [hu, div_le_iff₀ ht]; linarith
  have hex := exact_sqrt_bounds ht hu0 hu1
  rw [gapHF_eq]; unfold gapExact; rw [hUu]
  have e1 : (t * u) ^ 2 / (8 * t) = t * (u ^ 2 / 8) := by field_simp; ring
  have e2 : (t * u) ^ 4 / (512 * t ^ 3) = t * (u ^ 4 / 512) := by field_simp; ring
  rw [e1, e2]
  constructor <;> nlinarith [hex.1, hex.2]

/-- **G0W0@HF beats HF, but only beyond leading order.** For `0 < U <= t`. -/
theorem gw_beats_hf {t U : ℝ} (ht : 0 < t) (hU : 0 < U) (hUt : U ≤ t) :
    |gapGW t U - gapExact t U| < |gapHF t U - gapExact t U| := by
  obtain ⟨gl, gu⟩ := gw_error_bounds ht hU.le hUt
  obtain ⟨fl, fu⟩ := hf_error_bounds ht hU.le (by linarith)
  set u := U / t with hu
  have hUu : U = t * u := by rw [hu]; field_simp
  have hu0 : 0 < u := div_pos hU ht
  have hu1 : u ≤ 1 := by rw [hu, div_le_iff₀ ht]; linarith
  rw [hUu] at gl gu fl fu
  have e1 : (t * u) ^ 2 / (8 * t) = t * (u ^ 2 / 8) := by field_simp; ring
  have e2 : (t * u) ^ 3 / (16 * t ^ 2) = t * (u ^ 3 / 16) := by field_simp; ring
  have e3 : 3 * (t * u) ^ 3 / (16 * t ^ 2) = t * (3 * u ^ 3 / 16) := by field_simp; ring
  have e4 : (t * u) ^ 4 / (512 * t ^ 3) = t * (u ^ 4 / 512) := by field_simp; ring
  rw [e1, e3] at gl; rw [e1, e2] at gu; rw [e1] at fl; rw [e1, e4] at fu
  have hHF : gapHF t (t * u) - gapExact t (t * u) < 0 := by
    have : u ^ 4 / 512 < u ^ 2 / 8 := by nlinarith [pow_pos hu0 2, pow_pos hu0 4]
    nlinarith
  rw [hUu, abs_of_neg hHF, abs_lt]
  have p3 : 0 < u ^ 3 := pow_pos hu0 3
  have p4 : u ^ 4 ≤ u ^ 3 := by nlinarith [pow_pos hu0 3]
  have p34 : u ^ 3 ≤ u ^ 2 := by nlinarith [pow_pos hu0 2]
  constructor <;> nlinarith [mul_pos ht p3]

/-- **The power 2 is sharp for G0W0@HF**: no bound `C U^3 / t^2` holds on `(0, t]`. -/
theorem no_cubic_bound {t : ℝ} (ht : 0 < t) :
    ¬ ∃ C : ℝ, ∀ U : ℝ, 0 < U → U ≤ t → |gapGW t U - gapExact t U| ≤ C * U ^ 3 / t ^ 2 := by
  rintro ⟨C, hC⟩
  set d := 1 / (16 * (|C| + 1)) with hd
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hdpos : 0 < d := by positivity
  have hd16 : d * (|C| + 1) = 1 / 16 := by rw [hd]; field_simp; ring
  have hdle : d ≤ 1 / 16 := by nlinarith
  have hU : 0 < t * d := mul_pos ht hdpos
  have hUt : t * d ≤ t := by nlinarith
  have h1 := hC (t * d) hU hUt
  have h2 := (gw_error_bounds ht hU.le hUt).1
  have e1 : (t * d) ^ 2 / (8 * t) - 3 * (t * d) ^ 3 / (16 * t ^ 2) = t * d ^ 2 * (1 / 8 - 3 * d / 16) := by
    field_simp; ring
  have e2 : C * (t * d) ^ 3 / t ^ 2 = t * d ^ 2 * (C * d) := by field_simp; ring
  rw [e1] at h2; rw [e2] at h1
  have h3 := le_trans h2 (le_trans (le_abs_self _) h1)
  have hpos : 0 < t * d ^ 2 := by positivity
  have h4 : 1 / 8 - 3 * d / 16 ≤ C * d := le_of_mul_le_mul_left h3 hpos
  have h5 : C * d ≤ |C| * d := mul_le_mul_of_nonneg_right (le_abs_self C) hdpos.le
  nlinarith

/-- **Leading order, G0W0@HF:** `(gapGW - gapExact) / U^2 -> 1/(8t)` as `U -> 0+`. -/
theorem gw_error_leading {t : ℝ} (ht : 0 < t) :
    Tendsto (fun U => (gapGW t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by
  have hlo : Tendsto (fun U : ℝ => 1 / (8 * t) - 3 * U / (16 * t ^ 2)) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun U : ℝ => 1 / (8 * t) - 3 * U / (16 * t ^ 2)) := by continuity
    simpa using this.tendsto 0
  have hhi : Tendsto (fun U : ℝ => 1 / (8 * t) - U / (16 * t ^ 2)) (𝓝[>] 0) (𝓝 (1 / (8 * t))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun U : ℝ => 1 / (8 * t) - U / (16 * t ^ 2)) := by continuity
    simpa using this.tendsto 0
  have hev : ∀ᶠ U in 𝓝[>] (0 : ℝ), U ∈ Set.Ioo 0 t := Ioo_mem_nhdsGT ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with U hU
    obtain ⟨l, _⟩ := gw_error_bounds ht hU.1.le hU.2.le
    have hU2 : 0 < U ^ 2 := pow_pos hU.1 2
    rw [le_div_iff₀ hU2]
    have : (1 / (8 * t) - 3 * U / (16 * t ^ 2)) * U ^ 2 = U ^ 2 / (8 * t) - 3 * U ^ 3 / (16 * t ^ 2) := by
      field_simp; ring
    linarith
  · filter_upwards [hev] with U hU
    obtain ⟨_, r⟩ := gw_error_bounds ht hU.1.le hU.2.le
    have hU2 : 0 < U ^ 2 := pow_pos hU.1 2
    rw [div_le_iff₀ hU2]
    have : (1 / (8 * t) - U / (16 * t ^ 2)) * U ^ 2 = U ^ 2 / (8 * t) - U ^ 3 / (16 * t ^ 2) := by
      field_simp; ring
    linarith

/-- **Leading order, HF:** `(gapHF - gapExact) / U^2 -> -1/(8t)` as `U -> 0+`. -/
theorem hf_error_leading {t : ℝ} (ht : 0 < t) :
    Tendsto (fun U => (gapHF t U - gapExact t U) / U ^ 2) (𝓝[>] 0) (𝓝 (-(1 / (8 * t)))) := by
  have hlo : Tendsto (fun _ : ℝ => -(1 / (8 * t))) (𝓝[>] 0) (𝓝 (-(1 / (8 * t)))) :=
    tendsto_const_nhds
  have hhi : Tendsto (fun U : ℝ => -(1 / (8 * t)) + U ^ 2 / (512 * t ^ 3)) (𝓝[>] 0)
      (𝓝 (-(1 / (8 * t)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun U : ℝ => -(1 / (8 * t)) + U ^ 2 / (512 * t ^ 3)) := by continuity
    simpa using this.tendsto 0
  have hev : ∀ᶠ U in 𝓝[>] (0 : ℝ), U ∈ Set.Ioo 0 t := Ioo_mem_nhdsGT ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with U hU
    obtain ⟨l, _⟩ := hf_error_bounds ht hU.1.le (by linarith [hU.2])
    have hU2 : 0 < U ^ 2 := pow_pos hU.1 2
    rw [le_div_iff₀ hU2]
    have : -(1 / (8 * t)) * U ^ 2 = -(U ^ 2 / (8 * t)) := by field_simp
    linarith
  · filter_upwards [hev] with U hU
    obtain ⟨_, r⟩ := hf_error_bounds ht hU.1.le (by linarith [hU.2])
    have hU2 : 0 < U ^ 2 := pow_pos hU.1 2
    rw [div_le_iff₀ hU2]
    have : (-(1 / (8 * t)) + U ^ 2 / (512 * t ^ 3)) * U ^ 2 =
        -(U ^ 2 / (8 * t)) + U ^ 4 / (512 * t ^ 3) := by
      field_simp; ring
    linarith

/-- **The whole chain in one statement.** For `t > 0`, `0 <= U <= t`: take ANY
ground energies `E1, E2, E3` of the 1-, 2-, 3-electron sectors of the Fock-space
Hamiltonian, and ANY solutions `Er, Ea` of the full G0W0@HF QP equations on the
physical sides of their self-energy poles. Then

    |(Ea - Er) - (E3 + E1 - 2 E2)| <= (1/8) U^2 / t. -/
theorem gw_gap_error_main {t U E1 E2 E3 Er Ea : ℝ} (ht : 0 < t) (hU : 0 ≤ U) (hUt : U ≤ t)
    (h1 : IsSectorGround t U 1 E1) (h2 : IsSectorGround t U 2 E2) (h3 : IsSectorGround t U 3 E3)
    (hr : Er < epsA t U + hRPA t U) (hr' : Er = epsB t U + sigBB t U Er)
    (ha : epsB t U - hRPA t U < Ea) (ha' : Ea = epsA t U + sigAA t U Ea) :
    |(Ea - Er) - (E3 + E1 - 2 * E2)| ≤ (1 / 8) * U ^ 2 / t := by
  rw [exact_gap ht h1 h2 h3, (gw_gap_of_qp ht hU).2.2 Er Ea hr hr' ha ha']
  exact gw_error_abs ht hU hUt

end Bounds

end GW.Endpoint.HubbardDimer

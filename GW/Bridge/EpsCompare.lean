/-
BRIDGE-EPS E4: `Kernel/EpsSpec.lean` (transcribed from BerkeleyGW's Epsilon) against the
theory RPA dielectric matrix of E1-E3, and the composition with BRIDGE's
`sigA_eq_theory`.

Main theorems:

* `epsSpec_eq_theory_rem`: on the eps sphere `Gs` of one Input (one `q ≠ 0` point),
  EpsSpec's matrix `eps_ij = δ_ij - v(q+G_i) chi(G_i, G_j)` equals the theory
  `epsM v (χ0_theory - remainder)`: `χ0_theory = chiS (spinSys B)` is E1's static
  `χ0` of the spin-orbital Bloch system, and `v(q+G) = 8π/|q+G|²` (Rydberg), under
  the named hypotheses `V = N_k Ω`, `0 < V`, `ResOK` (unfolding trust), `TROK` (time
  reversal);
* `epsSpec_eq_theory`: with `Bands` as well (momentum conservation and complete band
  sums), EpsSpec's eps IS the theory eps;
* `epsTheory_entry_limit`: each theory entry is `δ_ij - v_i lim_{η→0⁺} ftDamped η
  ⟨G_i| -i G0 G0 |G_j⟩ 0`, i.e. built from the time-ordered `G0` alone (gapped system);
* `sigA_eps_eq_theory` (**the composition**): with `eps⁻¹` of SigmaSpec taken to be the
  matrix inverse of EpsSpec's eps on every block outside a set `Z` of `q = 0` blocks
  (whose `eps⁻¹` `E0` is an input), BerkeleyGW's `SigA` equals the theory `SigT` built
  with the inverse of the THEORY eps, plus `COR`, under the union of BRIDGE's named
  hypotheses (`hC`, `hW`, `hX`, `hM`) and this file's (`EpsBlock.OK` per block).
  "Inverse" in this file is Mathlib's totalized `Matrix.inv` (`0` for a singular
  matrix); it is a genuine inverse only when `det eps ≠ 0`, which `EpsBlock.OK` does not
  assume and which is not established for these blocks.

Named departures of this layer (see `docs/BRIDGE.md`, rows E-*):

* `q = 0` blocks: the head/wings of `eps(q → 0)` are not EpsSpec (which is `q ≠ 0`;
  at `q + G = 0` Lean's totalised `8π/0 = 0` is not a physical value); BerkeleyGW
  computes them at a small `q0`. Here they are the input `E0`; `EpsBlock.OK.qne` excludes
  `q + G_i = 0` from the compared blocks.
* finite band sum: `Bands` (remainder `remR + remA` otherwise, `epsSpec_eq_theory_rem`);
* G-sphere: the theory eps is the `Gs × Gs` block and its inverse the inverse of the
  truncated matrix (shared convergence parameter, same on both sides);
* symmetry unfolding trust: `ResOK` (the Input's states are the Bloch states);
* time reversal: `TROK` (the factor `4 = 2 × 2`).

REVIEW-28 F1: the composed theorem below takes the screening blocks `bs` independently of the
Sigma data `gl`, `st`; it is a conditional identity, not a statement about one system. The
one-system version is `GW.Bridge.Common.sigA_compat` (`GW/Bridge/Common.lean`). On the
Si-EPM run the Epsilon and Sigma k-grids are disjoint, so with any screening block off `Z`
its compatibility hypothesis `Compat` fails whenever a block the Σ q-list reads is derived
(`Compat` requires `k0` and every `k0 - q_t`
to be grid points). Its time-reversal hypothesis `MF.TR` cannot hold at a self-paired
point with a nonzero sphere vector, such as X or L (`MF.tr_fixed`). For O1 its hypotheses
are unsatisfiable if every block outside `Z` has a `neg` that fixes `k0`
(`hyps_unsat_of_selfpaired`; this follows from the trusted premise that `neg` encodes
`-k`, on a grid that stores X/L once), or, for arbitrary plans, if no grid index stores
the negated sphere list of `k0` (`hnp`, `hyps_unsat_of_unpaired`); storing X/L once does
not by itself give either premise (`docs/reviews/R28-F1.md`).
-/
import GW.Bridge.EpsRPA
import GW.Bridge.Compare

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Matrix Finset Filter Topology GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig
open GW.Endpoint.HubbardDimer (ftDamped)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section block

variable (inp : Input)

/-- The sphere entry `G_i`. -/
def gsI (i : Fin inp.Gs.length) : V3 := inp.Gs.getD i 0

/-- EpsSpec's eps on its sphere, as a matrix. -/
noncomputable def epsMatR : Matrix (Fin inp.Gs.length) (Fin inp.Gs.length) ℝ :=
  of fun i j => epsR inp i j

/-- The theory bare interaction `v(q + G_i) = 8π/|q + G_i|²` (Rydberg, `e² = 2`): EpsSpec's
`vC`, shared by definition, not derived. -/
noncomputable def vT (i : Fin inp.Gs.length) : ℝ := vC inp (gsI inp i)

/-- The remainder matrix `2/V (remR + remA)` on the sphere. -/
noncomputable def remMat (B : SpData κ V3) (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ) :
    Matrix (Fin inp.Gs.length) (Fin inp.Gs.length) ℝ :=
  of fun i j => 2 / B.Vol * (remR B (pairsOf inp vR cR vA cA) (gsI inp i) (gsI inp j) +
    remA B (pairsOf inp vR cR vA cA) (gsI inp i) (gsI inp j))

theorem one_fin_apply {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℝ) i j = if (i : ℕ) = j then 1 else 0 := by
  rw [one_apply]; simp only [Fin.ext_iff]

/-- **E4 (one block, with remainder).** -/
theorem epsSpec_eq_theory_rem (B : SpData κ V3) (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ)
    (hV : B.Vol = inpVol inp) (hVp : 0 < B.Vol)
    (hR : ResOK B (pairsOf inp vR cR vA cA)) (hA : TROK B (pairsOf inp vR cR vA cA)) :
    epsMatR inp = epsM (vT inp) (chiMat (spinSys B) (gsI inp) - remMat inp B vR cR vA cA) := by
  ext i j
  rw [epsMatR, of_apply, epsR, epsM, sub_apply, one_fin_apply, diagonal_mul, sub_apply,
    chiMat, remMat, of_apply, of_apply, epsSpec_chi_eq_theory inp B vR cR vA cA hV hVp hR hA]
  rfl

/-- **E4 (one block).** EpsSpec's eps is the theory RPA eps `1 - v χ0` of the spin-orbital
Bloch system, under `V = N_k Ω`, `0 < V`, `ResOK`, `TROK`, `Bands`. -/
theorem epsSpec_eq_theory (B : SpData κ V3) (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ)
    (hV : B.Vol = inpVol inp) (hVp : 0 < B.Vol)
    (hR : ResOK B (pairsOf inp vR cR vA cA)) (hA : TROK B (pairsOf inp vR cR vA cA))
    (hB : Bands B (pairsOf inp vR cR vA cA)) :
    epsMatR inp = epsM (vT inp) (chiMat (spinSys B) (gsI inp)) := by
  ext i j
  rw [epsMatR, of_apply, epsR, epsM, sub_apply, one_fin_apply, diagonal_mul,
    chiMat, of_apply, epsSpec_chi_eq_theory_bands inp B vR cR vA cA hV hVp hR hA hB]
  rfl

/-- The spin system of a gapped spatial system is off the excitations at `ω = 0`. -/
theorem spin_excOff (B : SpData κ V3) (hgap : ∀ v ∈ B.Oc, ∀ c ∈ B.Ocᶜ, B.e v < B.e c) :
    ExcOff (spinSys B) 0 := by
  apply excOff_zero
  intro v hv c hc
  simp only [spinSys, mem_product, mem_univ, true_and, mem_compl] at hv hc ⊢
  exact hgap v.2 hv c.2 (mem_compl.mpr hc)

/-- **The theory eps from `G0` alone.** Each theory entry is
`δ_ij - v_i lim_{η → 0⁺} ftDamped η ⟨G_i| -i G0 G0 |G_j⟩ 0`. -/
theorem epsTheory_entry_limit (B : SpData κ V3)
    (hgap : ∀ v ∈ B.Oc, ∀ c ∈ B.Ocᶜ, B.e v < B.e c) (i j : Fin inp.Gs.length) :
    Tendsto (fun η => (((1 : Matrix (Fin inp.Gs.length) (Fin inp.Gs.length) ℝ) i j : ℝ) : ℂ) -
        (vT inp i : ℂ) * ftDamped η (chiF (spinSys B) (gsI inp i) (gsI inp j)) 0) (𝓝[>] 0)
      (𝓝 ((epsM (vT inp) (chiMat (spinSys B) (gsI inp)) i j : ℝ) : ℂ)) := by
  have h := chiF_limit (spinSys B) (gsI inp i) (gsI inp j) (spin_excOff B hgap)
  rw [chiW_zero] at h
  have e : epsM (vT inp) (chiMat (spinSys B) (gsI inp)) i j =
      (1 : Matrix (Fin inp.Gs.length) (Fin inp.Gs.length) ℝ) i j -
        vT inp i * chiS (spinSys B) (gsI inp i) (gsI inp j) := by
    rw [epsM, sub_apply, diagonal_mul, chiMat, of_apply]
  rw [e]
  push_cast
  exact tendsto_const_nhds.sub (tendsto_const_nhds.mul h)

end block

/-! ### The composition with `sigA_eq_theory` -/

/-- One `q ≠ 0` block: EpsSpec's Input and the theory Bloch system with its pairing. -/
structure EpsBlock (κ : Type*) where
  inp : Input
  B : SpData κ V3
  vR : (Σ _ : ℕ, ℕ × ℕ) → κ
  cR : (Σ _ : ℕ, ℕ × ℕ) → κ
  vA : (Σ _ : ℕ, ℕ × ℕ) → κ
  cA : (Σ _ : ℕ, ℕ × ℕ) → κ

/-- The named hypotheses of one block. -/
structure EpsBlock.OK (b : EpsBlock κ) : Prop where
  /-- `q + G_i ≠ 0` on the sphere: a `q ≠ 0` block, `v` physically defined. -/
  qne : ∀ i : Fin b.inp.Gs.length, qG2 b.inp (gsI b.inp i) ≠ 0
  /-- The BvK supercell volume is `N_k Ω`. -/
  vol : b.B.Vol = inpVol b.inp
  volpos : 0 < b.B.Vol
  /-- Unfolding trust. -/
  res : ResOK b.B (pairsOf b.inp b.vR b.cR b.vA b.cA)
  /-- Time reversal. -/
  tr : TROK b.B (pairsOf b.inp b.vR b.cR b.vA b.cA)
  /-- Complete bands / momentum conservation. -/
  bands : Bands b.B (pairsOf b.inp b.vR b.cR b.vA b.cA)

/-- The `ℕ`-indexed `eps⁻¹` block of a matrix (entries outside the sphere are `0`). -/
noncomputable def blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r c : ℕ) : ℝ :=
  if h : r < n ∧ c < n then A⁻¹ ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

/-- SigmaSpec's `eps⁻¹` input from EpsSpec: the (totalized, `Matrix.inv`) inverse of
EpsSpec's eps on every block outside `Z`, and `E0` on the `q = 0` blocks `Z`. -/
noncomputable def Espec (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ) :
    ℕ → ℕ → ℕ → ℝ :=
  fun iq => if iq ∈ Z then E0 iq else blk (epsMatR (bs iq).inp)

/-- The theory `eps⁻¹`: the inverse of the theory RPA eps `1 - v χ0` built from E1's
static `χ0`, and `E0` on `Z`. The inverse is Mathlib's totalized `Matrix.inv` (`0` for a
singular matrix); it is a genuine inverse only when `det eps ≠ 0`, which is not
established for these blocks. -/
noncomputable def Etheory (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ) :
    ℕ → ℕ → ℕ → ℝ :=
  fun iq => if iq ∈ Z then E0 iq else
    blk (epsM (vT (bs iq).inp) (chiMat (spinSys (bs iq).B) (gsI (bs iq).inp)))

theorem Espec_eq_Etheory (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ)
    (hOK : ∀ iq ∉ Z, (bs iq).OK) : Espec Z E0 bs = Etheory Z E0 bs := by
  funext iq
  unfold Espec Etheory
  split_ifs with h
  · rfl
  · have ok := hOK iq h
    rw [epsSpec_eq_theory (bs iq).inp (bs iq).B _ _ _ _ ok.vol ok.volpos ok.res ok.tr ok.bands]

/-- **The theory block in BRIDGE's convention.** On a block outside `Z` the theory
`eps⁻¹` entry times `v_c` is the entry of `W = eps⁻¹ diag(v)` (`WM`), and the theory eps
is `GW.LL.dielectric (diag v)` of an explicit transition list, the object of BRIDGE's
`screened_entry`. Here `W` denotes the totalized inverse expression `eps⁻¹ diag(v)`;
`eps W = diag(v)` follows only under the nonsingularity hypothesis of `rpa_solve`. -/
theorem etheory_W (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ) {iq : ℕ}
    (hZ : iq ∉ Z) (r c : Fin (bs iq).inp.Gs.length) :
    Etheory Z E0 bs iq r c * vT (bs iq).inp c =
        WM (vT (bs iq).inp) (chiMat (spinSys (bs iq).B) (gsI (bs iq).inp)) r c ∧
      epsM (vT (bs iq).inp) (chiMat (spinSys (bs iq).B) (gsI (bs iq).inp)) =
        GW.LL.dielectric (diagonal (vT (bs iq).inp)) (tsOf (spinSys (bs iq).B) (gsI (bs iq).inp)) := by
  refine ⟨?_, theory_eps_eq_dielectric _ _ _⟩
  rw [WM_entry]
  simp only [Etheory, if_neg hZ, blk, dif_pos (And.intro r.2 c.2)]

/-- **The composition.** BerkeleyGW's `SigA`, with SigmaSpec's `eps⁻¹` taken to be the
inverse of EpsSpec's eps (outside the `q = 0` blocks `Z`), equals the theory `SigT` built
with the inverse of the theory RPA eps (from theory `χ0`), plus `COR`, under the union
of the named hypotheses of BRIDGE (`hC`, `hW`, `hX`, `hM`) and BRIDGE-EPS (`hOK`). Both
inverses are the totalized `Matrix.inv`; they are genuine inverses only when
`det eps ≠ 0`, which `hOK` does not give. -/
theorem sigA_eps_eq_theory (gl : Gl) (vb oq : V3 → ℝ) (st : St) (vc : V3 → ℝ) (a iw : ℕ)
    (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ)
    (hOK : ∀ iq ∉ Z, (bs iq).OK)
    (hC : ∀ k, vb k = vc k)
    (hW : ∀ t < gl.qs.length, WingFree gl (Etheory Z E0 bs) vb oq (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ModeOK (decide (n1 < gl.nocc)) (ITq gl (Etheory Z E0 bs) t j i) (OTq gl vb t j i)
        (xT gl st t a n1 iw)) :
    SigA gl (Espec Z E0 bs) vb oq st a iw =
      SigT gl (Etheory Z E0 bs) vc st a iw + COR gl (Etheory Z E0 bs) vb oq st a := by
  rw [Espec_eq_Etheory Z E0 bs hOK]
  exact sigA_eq_theory gl _ vb oq st vc a iw hC hW hX hM

/-- **The composition, complete bands in Sigma too.** Under BRIDGE's closure hypotheses
(complete bands at `k - q`, shift-closed spheres, `Gch` covering; then `COR = 0`), the
spec with EpsSpec's eps IS the theory: `SigA = SigT`. -/
theorem sigA_eps_eq_theory_complete (gl : Gl) (vb oq : V3 → ℝ) (st : St) (vc : V3 → ℝ)
    (a iw : ℕ) (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ)
    (hOK : ∀ iq ∉ Z, (bs iq).OK)
    (hC : ∀ k, vb k = vc k)
    (hW : ∀ t < gl.qs.length, WingFree gl (Etheory Z E0 bs) vb oq (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ModeOK (decide (n1 < gl.nocc)) (ITq gl (Etheory Z E0 bs) t j i) (OTq gl vb t j i)
        (xT gl st t a n1 iw))
    (hc : ∀ t < gl.qs.length,
      Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t))
    (hs : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t, ShiftClosed st.Gk
      (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j))
    (hch : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t,
      TS ≤ |IeS gl (Etheory Z E0 bs) vb oq (gl.qs.getD t default) j i| →
        gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    SigA gl (Espec Z E0 bs) vb oq st a iw = SigT gl (Etheory Z E0 bs) vc st a iw := by
  rw [Espec_eq_Etheory Z E0 bs hOK]
  exact sigA_eq_theory_complete gl _ vb oq st vc a iw hC hW hX hM hc hs hch

end GW.Bridge

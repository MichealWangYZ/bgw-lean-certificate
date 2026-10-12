/-
BRIDGE B3: the Bloch / plane-wave specialisation of B1 on SigmaSpec's own data.

Objects (on `Sig.Gl`, `Sig.St`, `Sig.QD`; the THEORY side, no BerkeleyGW rule applied):

* orbitals `(t, n1)`: band `n1` at `k - q_t`, energy `ε = RYD e_{n1}(k - q_t)` (eV),
  occupied iff `n1 < nocc`; the state `a` at `k`, energy `E = RYD e_a(k) + iw` (eV);
* pair densities `M_{a n1}(q_t, G) = Sig.xS` (the plane-wave convolution `Sig.pd`);
* the Coulomb interaction `v_i = vc(2(q+G_i)) / (N_q Ω)` for a Coulomb function `vc`;
  the bare point value is `vBareK`, `vBareK (key q G) = 8π / |q + G|²_B`
  (`vBareK_key`), i.e. `v(q+G) = 8π/(Ω |q+G|²)` per q-point in Ry;
* the static `eps⁻¹_{ij}(q)`: `epsT`, the symmetry-mapped entry of the input block
  WITHOUT the wing rule; `IT = δ - epsT`;
* the HL `Ω²_{ij}` (`OmT`): `ω_p² ρ(G_i - G_j)/ρ(0) · (q+G_i)·(q+G_j)/|q+G_i|²`, with
  `1/|q+G_i|² = vc/(8π)`; at `q = 0` the `G_i = 0` row is set by convention (BerkeleyGW's):
  head `ω_p²`, its direction-independent `q → 0` limit (`omT_head`); row wings `0`. The
  row wing in general (`ρ(-G_j) ≠ 0`) has no `q → 0` limit: its leading odd `O(1/|q|)`
  part averages to `0` over inversion-symmetric directions, and its even `O(1)` part
  `ω_p² ρ(-G_j)/ρ(0)` is dropped (a named approximation, EpsQ0Sigma);
* per mode `(j, i)` the GPP of B2 with `w̃ = √(Ω²/I)` and, per unit weight
  `M_i v_i M_j`, the B1 kernel `thK`: `occupiedTerm Ω² x w̃` (occupied) or
  `emptyTerm Ω² x w̃` (empty), `x = E - ε` (`xT`);
* `PT` the theory correlation of band `n1` at `q_t`, `SigT` the theory Σ = bare
  exchange `Xq` + correlation, summed over `q`.

Shared with SigmaSpec by definition, not derived here: the bare exchange `Sig.Xq` (`SigT`
contains it literally) and the plane-wave projection `Sig.quad` (the pair densities
`xS`/`pd`, the normalisation `vS = v/(N_q Ω)` and the `(j, i)` contraction). Only the
per-mode kernel `thK` is the theory's; its HL `Ω²` (`OmT`) is the supplied ansatz, built
from the spec's helpers `factW`, `rhoF`, `dotB`, `vec` (REVIEW-28 F2).

Proved:

* `bloch_sigc_eq` / `bloch_limit` (**B3**): the B1 system `blochSys` whose channel
  residues are `R = M_i v_i M_j Ω²_{ji}/(2 w̃_{ji})` has closed form
  `Σ_t Σ_{n1} PT` -- the sum over `q, n, G, G'` BerkeleyGW writes -- and hence, for `E`
  off the poles (`OffPoles`), the damped transform of `i G0 W_c` tends to it.
* `bloch_wcFreq` : in this basis the channel `W_c(ω)` of `blochSys` is
  `Σ_{i,j} M_i v_i M_j (eps⁻¹_GPP(ω) - δ)_{ji}` (valid modes), i.e. `W_c` is built from
  the B2 GPP `eps⁻¹` and `v` with `W_{ji} = eps⁻¹_{ji} v_i` (`= (eps⁻¹ · diag v)_{ji}`).
  `screened_entry` is a separate identity about `GW.LL.dielectric`: there `W` solves
  `eps W = diag v` when `det eps` is a unit. No theorem identifies the GPP `eps⁻¹_GPP(ω)`
  of `bloch_wcFreq` with the inverse of a `GW.LL.dielectric`.
* `pd_closure`: completeness of the bands at `k - q` (orthonormal coefficient matrix)
  and shift-closure of the `k - q` sphere give `Σ_n M_n(G) M_n(G') = ρ_aa(G - G')`,
  the identity behind the exact static COH term; `pd_neg`: `ρ_aa(-G) = ρ_aa(G)`.
-/
import GW.Bridge.FreqIntegral
import GW.Bridge.GPPModel

namespace GW.Bridge

open Finset Filter Topology GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps
open GW.Endpoint.HubbardDimer (ftDamped)

section defs

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St)

/-- The bare Coulomb function keyed like `vb`: `vBareK k = 8π / |k/2|²_B`. -/
noncomputable def vBareK (k : V3) : ℝ :=
  8 * Real.pi / dotB gl ![(k.1 : ℝ) / 2, (k.2.1 : ℝ) / 2, (k.2.2 : ℝ) / 2]
    ![(k.1 : ℝ) / 2, (k.2.1 : ℝ) / 2, (k.2.2 : ℝ) / 2]

/-- The symmetry-mapped static `eps⁻¹` entry, without the wing rule. -/
noncomputable def epsT (qd : QD) (i j : ℕ) : ℝ :=
  (if qd.neg.getD i false = qd.neg.getD j false then 1 else -1) *
    E qd.iq (qd.idx.getD i 0) (qd.idx.getD j 0)

/-- `I = δ - eps⁻¹(0)` (theory). -/
noncomputable def IT (qd : QD) (i j : ℕ) : ℝ := (if i = j then 1 else 0) - epsT E qd i j

/-- The HL oscillator-strength prescription `Ω²_{ij}` (supplied ansatz, not derived from the
system's response; REVIEW-28 F2) (theory). At `q = 0` the `G_i = 0` row is set by
convention: the head is its `q → 0` limit; the row wings, which in general
(`ρ(-G_j) ≠ 0`) have no `q → 0` limit, are `0` (their odd `O(1/|q|)` part averages to
`0`, their even `O(1)` part is dropped). -/
noncomputable def OmT (qd : QD) (i j : ℕ) : ℝ :=
  factW gl * (rhoF gl (gs qd i - gs qd j)).getD 0 *
    (if qd.qh = 0 ∧ gs qd i = 0 then (if gs qd j = 0 then 1 else 0)
     else vc (key qd (gs qd i)) / (8 * Real.pi) * dotB gl (vec qd (gs qd j)) (vec qd (gs qd i)))

/-- The B1 kernel per unit weight `M_i v_i M_j` of one GPP mode. -/
noncomputable def thK (occ : Bool) (I O x : ℝ) : ℝ :=
  if occ then GW.GPP.occupiedTerm O x (wTilde I O) else GW.GPP.emptyTerm O x (wTilde I O)

/-- `x = E - ε_{n1}(k - q)` in eV, exactly. -/
noncomputable def xT (t a n1 iw : ℕ) : ℝ :=
  RYD * (dy gl.SEn (st.Ek.getD a 0) - dy gl.SEn ((st.kq.getD t default).Eq.getD n1 0)) + iw

noncomputable def ITq (t j i : ℕ) : ℝ := IT E (gl.qs.getD t default) j i
noncomputable def OTq (t j i : ℕ) : ℝ := OmT gl vc (gl.qs.getD t default) j i

/-- The theory GPP correlation of band `n1` at `q_t`. -/
noncomputable def PT (t a n1 iw : ℕ) : ℝ :=
  quad gl vc st t a n1 (fun j i =>
    thK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OTq gl vc t j i) (xT gl st t a n1 iw))

/-- **The theory Σ** of band `a` at `E = RYD e_a + iw` (Ry): bare exchange plus the
GPP correlation, summed over the q-grid and the bands. -/
noncomputable def SigT (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (Xq gl vc st t a + ∑ n1 ∈ range (nbq st t), PT gl E vc st t a n1 iw)

/-- The weight `M_i v_i M_j` of mode `(j, i)`. -/
noncomputable def wgt (t a n1 j i : ℕ) : ℝ :=
  xS gl st t a n1 (gs (gl.qs.getD t default) i) * vS gl vc (gl.qs.getD t default) i *
    xS gl st t a n1 (gs (gl.qs.getD t default) j)

/-- The number of sphere vectors at `q_t`. -/
def nG (t : ℕ) : ℕ := (gl.qs.getD t default).Gs.length

/-- **The B1 system of the Bloch problem** for state `a`. -/
noncomputable def blochSys (a : ℕ) : PoleSys (Σ _ : ℕ, ℕ) (ℕ × ℕ) where
  S := (range gl.qs.length).sigma fun t => range (nbq st t)
  O := ((range gl.qs.length).sigma fun t => range (nbq st t)).filter fun x => x.2 < gl.nocc
  ε x := RYD * dy gl.SEn ((st.kq.getD x.1 default).Eq.getD x.2 0)
  P x := range (nG gl x.1) ×ˢ range (nG gl x.1)
  w x k := wTilde (ITq gl E x.1 k.1 k.2) (OTq gl vc x.1 k.1 k.2)
  R x k := wgt gl vc st x.1 a x.2 k.1 k.2 * (OTq gl vc x.1 k.1 k.2 /
    (2 * wTilde (ITq gl E x.1 k.1 k.2) (OTq gl vc x.1 k.1 k.2)))

end defs

/-! ### The bare Coulomb point value -/

theorem vBareK_key (gl : Gl) (qd : QD) (G : V3) :
    vBareK gl (key qd G) = 8 * Real.pi / dotB gl (vec qd G) (vec qd G) := by
  have : (![((key qd G).1 : ℝ) / 2, ((key qd G).2.1 : ℝ) / 2, ((key qd G).2.2 : ℝ) / 2] :
      Fin 3 → ℝ) = vec qd G := by
    funext c; fin_cases c <;> simp [key, vec] <;> ring
  rw [vBareK, this]

/-- The HL head `(q·q)/|q|²` is `1` for every `q ≠ 0`, so `OmT`'s `q = 0` head value is
the (direction-independent) `q → 0` limit. -/
theorem omT_head (gl : Gl) (qd : QD) (i j : ℕ) (hq : qd.qh ≠ 0) (hi : gs qd i = 0)
    (hj : gs qd j = 0) (hd : dotB gl (vec qd 0) (vec qd 0) ≠ 0) :
    OmT gl (vBareK gl) qd i j = factW gl * (rhoF gl 0).getD 0 := by
  unfold OmT
  rw [if_neg (fun h => hq h.1), hi, hj, sub_zero, vBareK_key]
  have : 8 * Real.pi / dotB gl (vec qd 0) (vec qd 0) / (8 * Real.pi) *
      dotB gl (vec qd 0) (vec qd 0) = 1 := by field_simp; ring
  rw [this, mul_one]

/-! ### `quad` is linear in the kernel -/

theorem quad_sub (gl : Gl) (vb : V3 → ℝ) (st : St) (t a n1 : ℕ) (F G : ℕ → ℕ → ℝ) :
    quad gl vb st t a n1 (fun j i => F j i - G j i) =
      quad gl vb st t a n1 F - quad gl vb st t a n1 G := by
  simp only [quad, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem quad_smul (gl : Gl) (vb : V3 → ℝ) (st : St) (t a n1 : ℕ) (c : ℝ) (F : ℕ → ℕ → ℝ) :
    quad gl vb st t a n1 (fun j i => c * F j i) = c * quad gl vb st t a n1 F := by
  simp only [quad, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem quad_congr (gl : Gl) (vb : V3 → ℝ) (st : St) (t a n1 : ℕ) {F G : ℕ → ℕ → ℝ}
    (h : ∀ j < nG gl t, ∀ i < nG gl t, F j i = G j i) :
    quad gl vb st t a n1 F = quad gl vb st t a n1 G := by
  simp only [quad]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [h j (mem_range.mp hj) i (mem_range.mp hi)]

theorem quad_eq_wgt (gl : Gl) (vc : V3 → ℝ) (st : St) (t a n1 : ℕ) (F : ℕ → ℕ → ℝ) :
    quad gl vc st t a n1 F =
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t), wgt gl vc st t a n1 j i * F j i := by
  rfl

/-! ### B3: the Bloch B1 closed form is BerkeleyGW's sum over `q, n, G, G'` -/

/-- **B3.** The B1 closed form of the Bloch system is `Σ_t Σ_{n1} PT`. -/
theorem bloch_sigc_eq (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St) (a iw : ℕ) :
    sigc (blochSys gl E vc st a) (RYD * dy gl.SEn (st.Ek.getD a 0) + iw) =
      ∑ t ∈ range gl.qs.length, ∑ n1 ∈ range (nbq st t), PT gl E vc st t a n1 iw := by
  unfold sigc
  simp only [blochSys]
  rw [sum_sigma]
  refine sum_congr rfl fun t _ => sum_congr rfl fun n1 hn1 => ?_
  rw [PT, quad_eq_wgt, sum_product, sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hx : RYD * dy gl.SEn (st.Ek.getD a 0) + iw -
      RYD * dy gl.SEn ((st.kq.getD t default).Eq.getD n1 0) = xT gl st t a n1 iw := by
    unfold xT; ring
  simp only [PoleSys.f, mem_filter, mem_sigma, mem_range, hn1, and_true]
  have hn1' : n1 < nbq st t := mem_range.mp hn1
  simp only [mem_range] at *
  unfold thK
  by_cases ho : n1 < gl.nocc
  · have hl : t < gl.qs.length := by assumption
    simp only [hl, ho, and_self, if_true, decide_true, sub_self, zero_div, add_zero, hx, one_div]
    unfold GW.GPP.occupiedTerm
    simp only [div_eq_mul_inv, mul_inv]; ring
  · simp only [ho, and_false, if_false, decide_false, sub_zero, zero_div, zero_add, hx,
      Bool.false_eq_true, one_div]
    unfold GW.GPP.emptyTerm
    simp only [div_eq_mul_inv, mul_inv]; ring

/-- **B1 + B3.** For `E` off the poles, the damped transform of `i G0 W_c` of the Bloch
system tends to the theory correlation `Σ_t Σ_{n1} PT`. -/
theorem bloch_limit (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St) (a iw : ℕ)
    (hE : OffPoles (blochSys gl E vc st a) (RYD * dy gl.SEn (st.Ek.getD a 0) + iw)) :
    Tendsto (fun η => ftDamped η (sigt (blochSys gl E vc st a))
        (RYD * dy gl.SEn (st.Ek.getD a 0) + iw)) (𝓝[>] 0)
      (𝓝 (((∑ t ∈ range gl.qs.length, ∑ n1 ∈ range (nbq st t), PT gl E vc st t a n1 iw : ℝ)) : ℂ)) := by
  rw [← bloch_sigc_eq]; exact sigt_limit _ hE

/-- **`W_c` from the GPP `eps⁻¹` and `v`.** For valid modes (`0 < Ω²/I`), the channel
screened interaction of the Bloch system is `Σ_{i,j} M_i v_i M_j (eps⁻¹_GPP(ω) - δ)_{ji}`. -/
theorem bloch_wcFreq (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ) (st : St) (a t n1 : ℕ)
    (hv : ∀ j < nG gl t, ∀ i < nG gl t, 0 < OTq gl vc t j i / ITq gl E t j i) (ω : ℝ) :
    wcFreq (blochSys gl E vc st a) ⟨t, n1⟩ ω =
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
        wgt gl vc st t a n1 j i * gppC (ITq gl E t j i) (OTq gl vc t j i) ω := by
  unfold wcFreq
  simp only [blochSys]
  rw [sum_product, sum_comm]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [gppC_pole_form (hv j (mem_range.mp hj) i (mem_range.mp hi)), singlePole]
  ring

/-- `W_{ji} = eps⁻¹_{ji} v_i` is the entry of `eps⁻¹ · diag v`, and for the dielectric
`eps = 1 - diag(v) chi0` of `GW.LL.Electronic`, when `det eps` is a unit (hypothesis `h`),
it solves `eps W = diag v`. (Lean's inverse is totalized: without `h` it can fail.) -/
theorem screened_entry {N : ℕ} (v : Fin N → ℝ) (ts : List (GW.LL.Transition ℝ N))
    (h : IsUnit (GW.LL.dielectric (Matrix.diagonal v) ts).det) (j i : Fin N) :
    ((GW.LL.dielectric (Matrix.diagonal v) ts)⁻¹ * Matrix.diagonal v) j i =
        (GW.LL.dielectric (Matrix.diagonal v) ts)⁻¹ j i * v i ∧
      GW.LL.dielectric (Matrix.diagonal v) ts *
        ((GW.LL.dielectric (Matrix.diagonal v) ts)⁻¹ * Matrix.diagonal v) = Matrix.diagonal v := by
  refine ⟨Matrix.mul_diagonal _ _ _ _, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.one_mul]

/-! ### Closure of the pair densities -/

theorem pd_neg (gl : Gl) (Gk : List V3) (ca : List ℤ) (G : V3) :
    pd gl Gk ca Gk ca (-G) = pd gl Gk ca Gk ca G := by
  unfold pd
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have : (Gk.getD j 0 - Gk.getD i 0 = -G) ↔ (Gk.getD i 0 - Gk.getD j 0 = G) := by
    constructor <;> intro h
    · rw [← neg_sub, h, neg_neg]
    · rw [← neg_sub, h]
  simp only [this]
  split_ifs <;> ring

/-- Completeness of the band coefficients at `k - q` (orthonormal columns). -/
def Complete (gl : Gl) (Gq : List V3) (cs : List (List ℤ)) (nb : ℕ) : Prop :=
  ∀ v < Gq.length, ∀ v' < Gq.length,
    ∑ n ∈ range nb, dy gl.SC ((cs.getD n []).getD v 0) * dy gl.SC ((cs.getD n []).getD v' 0) =
      if v = v' then 1 else 0

/-- Shift-closure of the `k - q` sphere for the pair `(G, G')`: for every pair of `k`
coefficients the number of `k - q` vectors realising both shifts is `[G_u - G_u' = G - G']`. -/
def ShiftClosed (Gk Gq : List V3) (G G' : V3) : Prop :=
  ∀ u < Gk.length, ∀ u' < Gk.length,
    ∑ v ∈ range Gq.length,
      (if Gk.getD u 0 - Gq.getD v 0 = G ∧ Gk.getD u' 0 - Gq.getD v 0 = G' then (1 : ℝ) else 0) =
      if Gk.getD u 0 - Gk.getD u' 0 = G - G' then 1 else 0

/-- **Closure.** `Σ_n M_{an}(G) M_{an}(G') = ρ_aa(G - G')`. -/
theorem pd_closure (gl : Gl) (Gk : List V3) (ca : List ℤ) (Gq : List V3) (cs : List (List ℤ))
    (nb : ℕ) (G G' : V3) (hc : Complete gl Gq cs nb) (hs : ShiftClosed Gk Gq G G') :
    ∑ n ∈ range nb, pd gl Gk ca Gq (cs.getD n []) G * pd gl Gk ca Gq (cs.getD n []) G' =
      pd gl Gk ca Gk ca (G - G') := by
  set A : ℕ → ℝ := fun u => dy gl.SC (ca.getD u 0) with hA
  set C : ℕ → ℕ → ℝ := fun n v => dy gl.SC ((cs.getD n []).getD v 0) with hC
  have ind : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  have hprod : ∀ n ∈ range nb, pd gl Gk ca Gq (cs.getD n []) G * pd gl Gk ca Gq (cs.getD n []) G' =
      ∑ u ∈ range Gk.length, ∑ u' ∈ range Gk.length, ∑ v ∈ range Gq.length,
        ∑ v' ∈ range Gq.length,
          (if Gk.getD u 0 - Gq.getD v 0 = G then (1 : ℝ) else 0) *
            (if Gk.getD u' 0 - Gq.getD v' 0 = G' then 1 else 0) * (A u * A u') *
              (C n v * C n v') := by
    intro n _
    unfold pd
    rw [sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => ?_
    rw [sum_mul_sum]
    refine sum_congr rfl fun v _ => sum_congr rfl fun v' _ => ?_
    rw [ind, ind (Gk.getD u' 0 - _ = _)]; ring
  have hrhs : pd gl Gk ca Gk ca (G - G') = ∑ u ∈ range Gk.length, ∑ u' ∈ range Gk.length,
      (if Gk.getD u 0 - Gk.getD u' 0 = G - G' then (1 : ℝ) else 0) * (A u * A u') := by
    unfold pd
    refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => ?_
    rw [ind]
  rw [sum_congr rfl hprod, hrhs]
  refine sum_comm.trans (sum_congr rfl fun u hu => ?_)
  refine sum_comm.trans (sum_congr rfl fun u' hu' => ?_)
  refine sum_comm.trans ?_
  rw [← hs u (mem_range.mp hu) u' (mem_range.mp hu'), sum_mul]
  refine sum_congr rfl fun v hv => ?_
  rw [sum_comm]
  have e : ∀ v' ∈ range Gq.length, ∑ n ∈ range nb,
      (if Gk.getD u 0 - Gq.getD v 0 = G then (1 : ℝ) else 0) *
        (if Gk.getD u' 0 - Gq.getD v' 0 = G' then 1 else 0) * (A u * A u') * (C n v * C n v') =
      (if Gk.getD u 0 - Gq.getD v 0 = G then (1 : ℝ) else 0) *
        (if Gk.getD u' 0 - Gq.getD v' 0 = G' then 1 else 0) * (A u * A u') *
          (if v = v' then 1 else 0) := by
    intro v' hv'
    rw [← mul_sum, hC, hc v (mem_range.mp hv) v' (mem_range.mp hv')]
  rw [sum_congr rfl e]
  rw [sum_eq_single v (fun v' _ h => by rw [if_neg (Ne.symm h), mul_zero])
    (fun h => absurd hv h), if_pos rfl, mul_one]
  by_cases h1 : Gk.getD u 0 - Gq.getD v 0 = G <;> by_cases h2 : Gk.getD u' 0 - Gq.getD v 0 = G' <;>
    simp only [h1, h2, if_true, if_false, and_true, true_and, and_false, false_and,
      mul_one, mul_zero, one_mul, zero_mul]

end GW.Bridge

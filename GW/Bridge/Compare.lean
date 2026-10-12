/-
BRIDGE B4: `Kernel/SigmaSpec.lean` (transcribed from BerkeleyGW) against the theory
formula `SigT` of B3 (its correlation kernel derived from `i G0 W_c` in B1 with the GPP of
B2; the exchange `Xq` and the plane-wave projection `quad` are SigmaSpec's own, shared by
definition: Bloch.lean).

Main theorem (`sigA_eq_theory`):

    Sig.SigA gl E vb oq st a iw  =  SigT gl E vc st a iw  +  COR

for the spec's inputs, under the explicit, named departure hypotheses

* `hC`  (Coulomb): the Coulomb function the spec uses (`vb`, the mini-BZ average) is
  the theory's `vc`. It is met trivially by `vc := vb`, the theory then using the
  averages. With the point value `vc = vBareK` it fails, since `vb` are averages: an
  approximation (and at `q + G = 0` the point value does not exist; the theory's q-sum needs a
  regularised value there, which `vb` is);
* `hW`  (wings, `WingFree`): at `q = 0` the raw `eps⁻¹` wings vanish (the spec zeroes
  them); at `q ≠ 0` the wing factors `oq |q|/(8π)` and `oq/(vb(q+G₀)|q|)` are `1`
  (`wing_factors_point`: this holds for point values of the averages);
* `hX`  (`TOL_Zero` replacement of `wx`): no `|x| < TOL_Zero`. When the `q = 0` states
  are those at `k`, as in every standard run, it fails at `iw = 0` for `n1 = a` (and its
  degenerate partners), where `x = 0` exactly; `wxS_close` bounds the replacement,
  `|Δx| < 2 TOL_Zero`, but that is not propagated to Σ here;
* `hM`  (every mode, `ModeOK`): the mode is kept (drop thresholds), valid
  (`wt2 > 0`, i.e. not the invalid-mode rule), and either in the generic branch without
  the `sexcut` clamp, or occupied in the near-pole branch without the clamp and off
  `x = w̃`, or a zero mode `I = Ω² = 0`;

and with ONE explicit correction term `COR = Σ_q (CSq + Σ_n ACq)`, the static
remainder, for which

* `cor_eq`: `COR_q = ½ (CH_exact,q - Σ_n CH_static,q,n)`, the Deslippe et al. (2013)
  static remainder with its empirical factor `½`;
* `chpart_sum_eq_exact`: `Σ_n CH_static = CH_exact` when the bands at `k - q` are
  complete, the `k - q` sphere is shift-closed and `Gch` covers the kept differences,
  so then `COR = 0` (`sigA_eq_theory_complete`); completeness alone leaves
  `COR = corShift + corGch` (`CorResidual.cor_decomp_complete`). `Complete` (exact orthonormality of the
  stored dyadic rows) cannot hold on the stored data, so that corollary does not apply there.

Every excluded case is characterised (`emp_near_zero`, `occ_generic_clamp`,
`occ_near_clamp`, `GPPModel.bgw_invalid_mode`, `GPPModel.bgw_dropped`, `wxS_eq`), and
the one departure that is NOT a documented BerkeleyGW approximation is witnessed
(`occ_pole_point`, `discrepancy_witness`): at exactly `x = w̃` on an occupied band the
spec gives `0` where the theory gives the finite value `I/4` per unit weight (the
removable singularity at `x = w̃` of the SX+CH split `GW.GPP.rawOccupied`, whose extension
is `GW.GPP.occupiedTerm`); arbitrarily close to it the spec agrees with the theory
(`ModeOK`'s near-pole case). `eqp1_linear`: the formula of `Sig.eqp1` is the linearised
QP equation when `1 - dΣ/dE ≠ 0` (an identity on that formula, not a rewrite of
`Sig.eqp1` itself; not part of Σ).
-/
import GW.Bridge.Bloch

namespace GW.Bridge

open Finset GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

/-! ### One mode -/

/-- The spec's contribution of one mode per unit weight: `CH/2 - [occ] SX`. -/
noncomputable def specMode (occ : Bool) (I O x : ℝ) : ℝ :=
  (1 / 2) * schM I O x - (if occ then ssxM I O x else 0)

/-- The spec's pole `√wt2`. -/
noncomputable def wG (I O : ℝ) : ℝ := √(wt2 I O)

/-- BerkeleyGW's generic-branch test. -/
def Generic (I O x : ℝ) : Prop := (x - wG I O) ^ 2 > GAM2 ∧ wG I O ^ 2 < (x - wG I O) ^ 2 * LIM1

/-- The generic `sexcut` clamp. -/
def ClampG (I O x : ℝ) : Prop := |x ^ 2 - wG I O ^ 2| < wG I O ^ 2 * (1 / SEXC) ∧ x < 0

/-- The near-pole `sexcut` clamp. -/
def ClampN (I O x : ℝ) : Prop := |2 * (x + wG I O)| < wG I O * (1 / SEXC) ∧ x < 0

/-- A mode on which the spec is the theory. -/
def ModeOK (occ : Bool) (I O x : ℝ) : Prop :=
  (keepM I O ∧ 0 < wt2 I O ∧ Generic I O x ∧ (occ = true → ¬ ClampG I O x)) ∨
  (occ = true ∧ keepM I O ∧ 0 < wt2 I O ∧ ¬ Generic I O x ∧
    wG I O ^ 2 > (x - wG I O) ^ 2 * TZ ∧ x - wG I O ≠ 0 ∧ ¬ ClampN I O x) ∨
  (I = 0 ∧ O = 0)

theorem TS_pos : (0 : ℝ) < TS := by unfold TS; positivity

theorem keep_facts {I O : ℝ} (hk : keepM I O) (hp : 0 < wt2 I O) :
    IeU I = I ∧ wt2 I O = O / I ∧ wtM I O = wG I O ∧ wG I O = wTilde I O ∧ I ≠ 0 ∧
      0 < wG I O ∧ O = wG I O ^ 2 * I := by
  have hI : I ≠ 0 := fun h => by
    have := hk.1.1; rw [h, abs_zero] at this; linarith [TS_pos]
  have h2 : wt2 I O = O / I := by simp [wt2, hk.1]
  have hw : 0 < wG I O := Real.sqrt_pos.mpr hp
  refine ⟨by simp [IeU, hk.1.1], h2, by simp [wtM, hk, hp, wG], by rw [wG, wTilde, h2], hI, hw, ?_⟩
  rw [wG, Real.sq_sqrt hp.le, h2]; field_simp

/-- **Per-mode comparison.** On a `ModeOK` mode the spec's kernel is the theory's. -/
theorem mode_eq {occ : Bool} {I O x : ℝ} (h : ModeOK occ I O x) :
    specMode occ I O x = thK occ I O x := by
  rcases h with ⟨hk, hp, hg, hcl⟩ | ⟨rfl, hk, hp, hg, hn, hxw, hcl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hU, -, hW, hT, hI, hw, hO⟩ := keep_facts hk hp
    have hd : x - wG I O ≠ 0 := by
      intro h0; have := hg.1; rw [h0] at this; unfold GAM2 at this; norm_num at this
    have hsch : schM I O x = wG I O * I / (x - wG I O) := by
      simp only [schM, if_pos hk, hW, hU]; rw [if_pos (by exact ⟨hg.1, hg.2⟩)]
    unfold specMode thK
    cases occ
    · simp only [Bool.false_eq_true, if_false, sub_zero, hsch]
      unfold GW.GPP.emptyTerm
      rw [← hT]
      generalize wG I O = w at hO hw hd ⊢
      subst hO; field_simp; ring
    · have hc := hcl rfl
      have hs : x + wG I O ≠ 0 := by
        intro h0; apply hc
        have hx : x = -wG I O := by linarith
        refine ⟨?_, by linarith⟩
        rw [hx, show (-wG I O) ^ 2 - wG I O ^ 2 = 0 by ring, abs_zero]
        unfold SEXC; positivity
      have hssx : ssxM I O x = wG I O ^ 2 * I / (x ^ 2 - wG I O ^ 2) := by
        simp only [ssxM, if_pos hk, hW, hU, GW.Endpoint.Cert.certSsx]
        rw [if_pos (by exact ⟨hg.1, hg.2⟩), if_neg (by exact hc)]
      simp only [if_true, hsch, hssx]
      unfold GW.GPP.occupiedTerm
      have hq : x ^ 2 - wG I O ^ 2 ≠ 0 := by
        rw [show x ^ 2 - wG I O ^ 2 = (x - wG I O) * (x + wG I O) by ring]
        exact mul_ne_zero hd hs
      rw [← hT]
      generalize wG I O = w at hO hw hd hs hq ⊢
      subst hO; field_simp; ring
  · obtain ⟨hU, -, hW, hT, hI, hw, hO⟩ := keep_facts hk hp
    have hs : x + wG I O ≠ 0 := by
      intro h0; apply hcl
      have hx : x = -wG I O := by linarith
      refine ⟨?_, by linarith⟩
      rw [hx, show 2 * (-wG I O + wG I O) = 0 by ring, abs_zero]
      unfold SEXC; positivity
    have hsch : schM I O x = 0 := by
      simp only [schM, if_pos hk, hW]; rw [if_neg (by exact hg)]
    have hssx : ssxM I O x = -(I * wG I O) / (2 * (x + wG I O)) := by
      simp only [ssxM, if_pos hk, hW, hU, GW.Endpoint.Cert.certSsx]
      rw [if_neg (by exact hg), if_pos ⟨hn, hxw⟩, if_neg (by exact hcl)]
    unfold specMode thK
    simp only [if_true, hsch, hssx]
    unfold GW.GPP.occupiedTerm
    rw [← hT]
    generalize wG I O = w at hO hw hs ⊢
    subst hO; field_simp; ring
  · have hk : ¬ keepM 0 0 := fun h => by
      have := h.1.1; rw [abs_zero] at this; linarith [TS_pos]
    obtain ⟨-, h1, h2⟩ := bgw_dropped (x := x) hk
    unfold specMode thK GW.GPP.occupiedTerm GW.GPP.emptyTerm
    rw [h1, h2]; cases occ <;> simp

/-! ### The excluded mode cases (named departures) -/

/-- Empty band, outside the generic branch: the spec drops the CH pole term. -/
theorem emp_near_zero {I O x : ℝ} (hk : keepM I O) (hp : 0 < wt2 I O) (hg : ¬ Generic I O x) :
    specMode false I O x = 0 := by
  obtain ⟨-, -, hW, -⟩ := keep_facts hk hp
  unfold specMode
  simp only [schM, if_pos hk, hW, Bool.false_eq_true, if_false, sub_zero]
  rw [if_neg (by exact hg)]; ring

/-- Occupied band, generic branch with the `sexcut` clamp: SX is zeroed, CH kept. -/
theorem occ_generic_clamp {I O x : ℝ} (hk : keepM I O) (hp : 0 < wt2 I O) (hg : Generic I O x)
    (hc : ClampG I O x) : specMode true I O x = (1 / 2) * (wG I O * I / (x - wG I O)) := by
  obtain ⟨hU, -, hW, -⟩ := keep_facts hk hp
  unfold specMode
  simp only [schM, ssxM, if_pos hk, hW, hU, GW.Endpoint.Cert.certSsx, if_true]
  rw [if_pos (by exact ⟨hg.1, hg.2⟩), if_pos (by exact ⟨hg.1, hg.2⟩), if_pos (by exact hc)]; ring

/-- Occupied band, near-pole branch with the clamp: both SX and CH are zero. -/
theorem occ_near_clamp {I O x : ℝ} (hk : keepM I O) (hp : 0 < wt2 I O) (hg : ¬ Generic I O x)
    (hn : wG I O ^ 2 > (x - wG I O) ^ 2 * TZ) (hxw : x - wG I O ≠ 0) (hc : ClampN I O x) :
    specMode true I O x = 0 := by
  obtain ⟨hU, -, hW, -⟩ := keep_facts hk hp
  unfold specMode
  simp only [schM, ssxM, if_pos hk, hW, hU, GW.Endpoint.Cert.certSsx, if_true]
  rw [if_neg (by exact hg), if_neg (by exact hg), if_pos ⟨hn, hxw⟩, if_pos (by exact hc)]; ring

/-- **The discrepancy.** At exactly `x = w̃` on an occupied band the spec gives `0`,
the theory the finite removable-singularity value `I/4` (per unit weight). -/
theorem occ_pole_point {I O : ℝ} (hk : keepM I O) (hp : 0 < wt2 I O) :
    specMode true I O (wTilde I O) = 0 ∧ thK true I O (wTilde I O) = I / 4 := by
  obtain ⟨hU, -, hW, hT, hI, hw, hO⟩ := keep_facts hk hp
  refine ⟨?_, ?_⟩
  · have hg : ¬ ((wTilde I O - wtM I O) ^ 2 > GAM2 ∧ wtM I O ^ 2 < (wTilde I O - wtM I O) ^ 2 * LIM1) := by
      rw [hW, hT, sub_self]; unfold GAM2; norm_num
    unfold specMode
    simp only [schM, ssxM, if_pos hk, if_true]
    rw [if_neg hg, hW, hT, GW.Endpoint.Cert.certSsx_at_w _ _ _ (by unfold GAM2; norm_num)]; ring
  · unfold thK
    simp only [if_true]
    rw [GW.GPP.occupiedTerm_at_pole _ _ (hT ▸ hw.ne'), ← hT]
    generalize wG I O = w at hO hw ⊢
    subst hO; field_simp; ring

/-- A minimal instance: `I = Ω² = 1` (`w̃ = 1`), `x = 1`: spec `0`, theory `1/4`. -/
theorem discrepancy_witness : specMode true 1 1 1 = 0 ∧ thK true 1 1 1 = 1 / 4 := by
  have hTS : TS ≤ 1 := by unfold TS; norm_num
  have hk : keepM 1 1 := ⟨⟨by simpa using hTS, by simpa using hTS⟩, by
    simp only [wt2, abs_one, hTS, and_self, if_true, div_one]⟩
  have hp : 0 < wt2 1 1 := by simp [wt2, hTS]
  have hw : wTilde 1 1 = 1 := by simp [wTilde]
  have := occ_pole_point hk hp
  rw [hw] at this; exact this

/-- The `TOL_Zero` replacement of `wx`. -/
theorem wxS_eq (gl : Gl) (st : St) (t a n1 iw : ℕ) :
    wxS gl st t a n1 iw = if |xT gl st t a n1 iw| < TZ then TZ else xT gl st t a n1 iw := rfl

/-- ... which moves `x` by less than `2 TOL_Zero` (≈ 2e-12 eV) when active. -/
theorem wxS_close (gl : Gl) (st : St) (t a n1 iw : ℕ) :
    |wxS gl st t a n1 iw - xT gl st t a n1 iw| < 2 * TZ := by
  have hT : (0 : ℝ) < TZ := by unfold TZ; positivity
  rw [wxS_eq]
  split_ifs with h
  · calc |TZ - xT gl st t a n1 iw| ≤ |TZ| + |xT gl st t a n1 iw| := abs_sub _ _
      _ < 2 * TZ := by rw [abs_of_pos hT]; linarith
  · rw [sub_self, abs_zero]; linarith

/-! ### Wings, Ω², the whole Σ -/

variable (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)

/-- The wing rule is inactive at `qd`. -/
def WingFree (qd : QD) : Prop :=
  (qd.qh = 0 → ∀ i j, ((i = qd.z ∧ j ≠ qd.z) ∨ (j = qd.z ∧ i ≠ qd.z)) → epsT E qd i j = 0) ∧
  (qd.qh ≠ 0 → oq qd.qh * qlen gl qd / (8 * Real.pi) = 1 ∧
    oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) = 1)

theorem epsS_eq {qd : QD} (h : WingFree gl E vb oq qd) (i j : ℕ) :
    epsS gl E vb oq qd i j = epsT E qd i j := by
  have e : epsS gl E vb oq qd i j =
      if qd.qh = 0 then
        (if (i = qd.z ∧ j ≠ qd.z) ∨ (j = qd.z ∧ i ≠ qd.z) then 0 else epsT E qd i j)
      else if i = qd.z ∧ j ≠ qd.z then epsT E qd i j * (oq qd.qh * qlen gl qd / (8 * Real.pi))
      else if j = qd.z ∧ i ≠ qd.z then
        epsT E qd i j * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd))
      else epsT E qd i j := rfl
  rw [e]
  by_cases h0 : qd.qh = 0
  · rw [if_pos h0]
    by_cases hw : (i = qd.z ∧ j ≠ qd.z) ∨ (j = qd.z ∧ i ≠ qd.z)
    · rw [if_pos hw, h.1 h0 i j hw]
    · rw [if_neg hw]
  · rw [if_neg h0, (h.2 h0).1, (h.2 h0).2, mul_one]
    split_ifs <;> rfl

/-- With the point values `oq = 8π/|q|` and `vb(q + G₀) = 8π/|q|²` (`G₀ = 0`) the q ≠ 0
wing factors are `1`. -/
theorem wing_factors_point (qd : QD) (hq : qlen gl qd ≠ 0)
    (hoq : oq qd.qh = 8 * Real.pi / qlen gl qd)
    (hvb : vb (key qd (gs qd 0)) = 8 * Real.pi / qlen gl qd ^ 2) :
    oq qd.qh * qlen gl qd / (8 * Real.pi) = 1 ∧
      oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd) = 1 := by
  rw [hoq, hvb]
  refine ⟨by field_simp, by field_simp; ring⟩

theorem om2S_eq (qd : QD) (i j : ℕ) : Om2S gl vb qd i j = OmT gl vb qd i j := by
  unfold Om2S OmT
  cases rhoF gl (gs qd i - gs qd j) with
  | none => simp
  | some r =>
    simp only [Option.getD_some]
    split_ifs <;> ring

/-- The static-remainder correction. -/
noncomputable def COR (a : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (CSq gl E vb oq st t a + ∑ n1 ∈ range (nbq st t), ACq gl E vb oq st t a n1)

theorem Pq_eq_quad (t a n1 iw : ℕ) :
    Pq gl E vb oq st t a n1 iw = quad gl vb st t a n1 (fun j i =>
      specMode (decide (n1 < gl.nocc)) (Iq gl E vb oq t j i) (Oq gl vb t j i) (wxS gl st t a n1 iw)) := by
  unfold Pq specMode
  by_cases ho : n1 < gl.nocc
  · simp only [ho, if_true, decide_true]
    rw [quad_sub, quad_smul]
  · simp only [ho, if_false, decide_false, Bool.false_eq_true, sub_zero]
    rw [quad_smul]

/-- **B4.** The spec's Σ is the theory's Σ plus the static remainder, under the named
departure hypotheses. -/
theorem sigA_eq_theory (vc : V3 → ℝ) (a iw : ℕ) (hC : ∀ k, vb k = vc k)
    (hW : ∀ t < gl.qs.length, WingFree gl E vb oq (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ModeOK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OTq gl vb t j i) (xT gl st t a n1 iw)) :
    SigA gl E vb oq st a iw = SigT gl E vc st a iw + COR gl E vb oq st a := by
  have hv : vb = vc := funext hC
  subst hv
  unfold SigA SigT COR
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hP : ∀ n1 ∈ range (nbq st t), Pq gl E vb oq st t a n1 iw = PT gl E vb st t a n1 iw := by
    intro n1 hn1
    have hn1' := mem_range.mp hn1
    rw [Pq_eq_quad, PT]
    apply quad_congr
    intro j hj i hi
    have hI : Iq gl E vb oq t j i = ITq gl E t j i := by
      simp only [Iq, ITq, IeS, IT, epsS_eq gl E vb oq (hW t ht') j i]
    have hO : Oq gl vb t j i = OTq gl vb t j i := by simp only [Oq, OTq, om2S_eq]
    have hx : wxS gl st t a n1 iw = xT gl st t a n1 iw := by
      rw [wxS_eq, if_neg (not_lt.mpr (hX t ht' n1 hn1'))]
    rw [hI, hO, hx]
    exact mode_eq (hM t ht' n1 hn1' j hj i hi)
  rw [sum_congr rfl fun n1 hn1 => by rw [hP n1 hn1], sum_add_distrib]
  ring

/-! ### The static remainder -/

/-- The static COH term of band `n1` in the band sum (with the spec's `|I| ≥ TOL_Small`). -/
noncomputable def CHpart (t a n1 : ℕ) : ℝ :=
  (1 / 2) * quad gl vb st t a n1 (fun j i => -IeU (Iq gl E vb oq t j i))

/-- The exact (closure) static COH term. -/
noncomputable def CHexact (t a : ℕ) : ℝ :=
  let qd := gl.qs.getD t default
  (1 / 2) * ∑ j ∈ range qd.Gs.length, vS gl vb qd j * ∑ i ∈ range qd.Gs.length,
    (if TS ≤ |IeS gl E vb oq qd i j| ∧ gs qd i - gs qd j ∈ gl.Gch then
      pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a []) (gs qd i - gs qd j) *
        (epsS gl E vb oq qd i j - if i = j then 1 else 0)
     else 0)

/-- **The static remainder** is `½ (CH_exact - Σ_n CH_static)`. -/
theorem cor_eq (t a : ℕ) :
    CSq gl E vb oq st t a + ∑ n1 ∈ range (nbq st t), ACq gl E vb oq st t a n1 =
      (1 / 2) * (CHexact gl E vb oq st t a - ∑ n1 ∈ range (nbq st t), CHpart gl E vb oq st t a n1) := by
  have h1 : CSq gl E vb oq st t a = (1 / 2) * CHexact gl E vb oq st t a := by
    simp only [CSq, CHexact]; ring
  have h2 : ∀ n1 ∈ range (nbq st t), ACq gl E vb oq st t a n1 = -(1 / 2) * CHpart gl E vb oq st t a n1 :=
    fun n1 _ => by simp only [ACq, CHpart]
  rw [h1, sum_congr rfl h2, ← mul_sum]; ring

/-- **Closure.** Complete bands at `k - q`, a shift-closed `k - q` sphere and a `Gch` covering
the kept differences make the band sum of the static COH term exact. -/
theorem chpart_sum_eq_exact (t a : ℕ)
    (hc : Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t))
    (hs : ∀ i < nG gl t, ∀ j < nG gl t, ShiftClosed st.Gk (st.kq.getD t default).Gq
      (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j))
    (hch : ∀ i < nG gl t, ∀ j < nG gl t, TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
      gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    ∑ n1 ∈ range (nbq st t), CHpart gl E vb oq st t a n1 = CHexact gl E vb oq st t a := by
  unfold CHpart CHexact
  rw [← mul_sum]
  congr 1
  simp only [quad]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have hcl := pd_closure gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq
    (st.kq.getD t default).cq (nbq st t) _ _ hc (hs i hi' j hj')
  have e : ∀ n1 ∈ range (nbq st t),
      xS gl st t a n1 (gs (gl.qs.getD t default) i) * vS gl vb (gl.qs.getD t default) i *
        xS gl st t a n1 (gs (gl.qs.getD t default) j) * -IeU (Iq gl E vb oq t j i) =
      (pd gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq ((st.kq.getD t default).cq.getD n1 [])
          (gs (gl.qs.getD t default) i) *
        pd gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq ((st.kq.getD t default).cq.getD n1 [])
          (gs (gl.qs.getD t default) j)) *
        (vS gl vb (gl.qs.getD t default) i * -IeU (Iq gl E vb oq t j i)) := by
    intro n1 _; simp only [xS]; ring
  rw [sum_congr rfl e, ← sum_mul, hcl]
  have hneg : gs (gl.qs.getD t default) i - gs (gl.qs.getD t default) j =
      -(gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i) := by rw [neg_sub]
  rw [hneg, pd_neg]
  have hIq : Iq gl E vb oq t j i = IeS gl E vb oq (gl.qs.getD t default) j i := rfl
  have hIe : -IeS gl E vb oq (gl.qs.getD t default) j i =
      epsS gl E vb oq (gl.qs.getD t default) j i - if j = i then 1 else 0 := by unfold IeS; ring
  rw [hIq]
  by_cases h : TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i|
  · simp only [IeU, if_pos h]
    rw [if_pos ⟨h, hch i hi' j hj' h⟩, hIe]; ring
  · simp only [IeU, if_neg h, neg_zero]
    rw [if_neg (fun h' => h h'.1)]; ring

/-- With complete bands (and the closure conditions) the static remainder vanishes and
the spec IS the theory, under the remaining named hypotheses.

Applicability note (comment only): the hypothesis `hc` (`Bloch.Complete`) is unsatisfiable
on the stored dyadic rows of the Si-EPM run: their `‖R‖₂² - 1 ≈ +2e-15`, so `I - R Rᵀ` has
a negative pivot (`bgw/bridge_cor/data/cor.json` `completeness_check`; docs/BRIDGE.md
BRIDGE-COR). This theorem is therefore never instantiated on the run's data. -/
theorem sigA_eq_theory_complete (vc : V3 → ℝ) (a iw : ℕ) (hC : ∀ k, vb k = vc k)
    (hW : ∀ t < gl.qs.length, WingFree gl E vb oq (gl.qs.getD t default))
    (hX : ∀ t < gl.qs.length, ∀ n1 < nbq st t, TZ ≤ |xT gl st t a n1 iw|)
    (hM : ∀ t < gl.qs.length, ∀ n1 < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      ModeOK (decide (n1 < gl.nocc)) (ITq gl E t j i) (OTq gl vb t j i) (xT gl st t a n1 iw))
    (hc : ∀ t < gl.qs.length, Complete gl (st.kq.getD t default).Gq (st.kq.getD t default).cq (nbq st t))
    (hs : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t, ShiftClosed st.Gk
      (st.kq.getD t default).Gq (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j))
    (hch : ∀ t < gl.qs.length, ∀ i < nG gl t, ∀ j < nG gl t,
      TS ≤ |IeS gl E vb oq (gl.qs.getD t default) j i| →
        gs (gl.qs.getD t default) j - gs (gl.qs.getD t default) i ∈ gl.Gch) :
    SigA gl E vb oq st a iw = SigT gl E vc st a iw := by
  rw [sigA_eq_theory gl E vb oq st vc a iw hC hW hX hM, COR]
  have : ∀ t ∈ range gl.qs.length,
      CSq gl E vb oq st t a + ∑ n1 ∈ range (nbq st t), ACq gl E vb oq st t a n1 = 0 := by
    intro t ht
    have ht' := mem_range.mp ht
    rw [cor_eq, chpart_sum_eq_exact gl E vb oq st t a (hc t ht') (hs t ht') (hch t ht'), sub_self,
      mul_zero]
  rw [sum_congr rfl this, sum_const_zero, add_zero]

/-! ### The quasiparticle step (not part of Σ) -/

/-- The formula of `Sig.eqp1` (its `let` body, restated on free reals `s0`, `s1`, `eo`; no
theorem here rewrites `Sig.eqp1` itself) equals the linearised QP equation
`Eo + Σ(Eo) / (1 - dΣ/dE)` with the forward difference `dΣ/dE ≈ Σ(Eo + 1 eV) - Σ(Eo)`,
when `1 - dΣ/dE ≠ 0`. -/
theorem eqp1_linear (s0 s1 eo : ℝ) (h : 1 - (s1 - s0) / 1 ≠ 0) :
    (eo + s0) + (s1 - s0) / 1 / (1 - (s1 - s0) / 1) * ((eo + s0) - eo) =
      eo + s0 / (1 - (s1 - s0)) := by
  rw [div_one] at h ⊢
  field_simp; ring

end GW.Bridge

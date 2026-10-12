/-
BRIDGE-EPS E2: the Bloch / plane-wave specialisation of E1, and EpsSpec's
`chi(G, G') = 4/(N_k Ω) Σ_k Σ_v Σ_c M M / (E_v(k+q) - E_c(k))`.

Setting (the THEORY side, no BerkeleyGW rule applied):

* spatial orbitals `a : κ` (a `Fintype`: band and k-point of a finite BvK grid), energies
  `e a`, occupied set `Oc`; the spin-orbitals are `(σ, a)`, `σ : Bool`, with the same
  energy and occupation for both spins (`spinSys`, a closed-shell, spin-unpolarised
  system without spin-orbit coupling);
* the density channels `g` are the plane waves `|q + G⟩ = V^{-1/2} e^{i(q+G)·r}`,
  orthonormal on the Born-von Karman supercell of volume `V = N_k Ω` (`Vol`);
* `rho a b G = ∫_V φ_b^* e^{-i(q+G)·r} φ_a` the pair density of the spatial Bloch
  orbitals, normalised on the supercell with unit-normalised plane-wave coefficients
  (`φ_{nk} = V^{-1/2} Σ_G c_n(k, G) e^{i(k+G)·r}`). The E1 amplitude of the
  spin-orbital pair is then `⟨q+G| φ_{(σ',b)}^* φ_{(σ,a)}⟩ = [σ = σ'] rho a b G / √V`:
  the density operator is spin-diagonal, and the channel normalisation contributes
  `1/√V` per amplitude, hence `1/V = 1/(N_k Ω)` per term.

Derivation of the pairing (by hand; its conclusions enter as NAMED hypotheses):
with `φ = V^{-1/2} Σ c e^{i(k+G)·r}`,
`rho_{(n,k),(n',k')}(G) = Σ_{G₁ - G₂ = G} c_n(k, G₁) c_{n'}(k', G₂)^*` if `k = k' + q` and
`0` otherwise (momentum conservation). So

* the pair `a = (v, k+q)` occupied, `b = (c, k)` empty has `rho = M_vc(k, G)`, EpsSpec's
  pair density, and enters E1's second (`τ < 0`, hole-first) term: `ResOK`
  (`rhoR`, `eR`: the Input's states ARE these Bloch states -- the unfolding trust);
* the pair `a = (c, k')` empty, `b = (v, k' - q)` occupied enters E1's first (`τ > 0`)
  term. With time reversal (`φ_{n,-k} = φ_{n,k}^*`, `e_n(-k) = e_n(k)`, real
  coefficients) and `k' = -k` it equals the first one: `rho = M_vc(k, G)`, same
  denominator. `TROK` (`rhoA`, `eA`) is this time-reversal hypothesis; it needs the
  grid to be closed under `k ↦ -k`.
* all other occupied/empty pairs, i.e. momentum-mismatched pairs and bands beyond the
  Input's band lists, are collected in the remainder `remR + remA`. It is zero under
  `Bands` (`rem_zero`; momentum conservation plus completeness of the band sums); the
  finite conduction-band sum of EpsSpec is this departure.

Proved:

* `spin_chiS`: for `V > 0`, the spin sum gives exactly `2`:
  `chiS (spinSys B) = 2/V · Σ_{v ∈ Oc} Σ_{c ∉ Oc} [rho_cv rho_cv + rho_vc rho_vc] / (e_v - e_c)`.
* `bloch_chi` (**E2**): under `V > 0`, `ResOK` and `TROK`,
  `chiS = 4/V · Σ_{x ∈ T} M_x(G) M_x(G') / (E_v - E_c) + 2/V · (remR + remA)`.
  The `4` is `2` (spin) times `2` (the two time orderings, equal by time reversal).
* `chi_eq_triples`: EpsSpec's `chi` is `4/(N_k Ω) Σ_{x ∈ T_inp}` over its triples
  `(k, v, c)`.
* `epsSpec_chi_eq_theory`: EpsSpec's `chi` equals the theory `chiS` minus the
  remainder; `epsSpec_chi_eq_theory_bands`: equals `chiS` under `Bands`.
* `factor_two_wrong`: a minimal Lean witness that the factor is `4`, not `2` (the
  spin-only factor): for one occupied/empty pair and `V > 0`,
  `chiS = 4 M²/(V (E_v - E_c))`, which differs from the factor-`2` form whenever
  `M ≠ 0` and `E_v ≠ E_c` (an equality; the inequality is not stated as a theorem).

The `k + q` convention: EpsSpec's valence state at `k + q` and conduction state at `k`
is the one the momentum-conserving pair `a = (v, k+q)`, `b = (c, k)` requires for the
channel `e^{-i(q+G)·r}`, i.e. `chi(q)` and not `chi(-q)`.
-/
import GW.Bridge.EpsChi0
import GW.Endpoint.Kernel.EpsSpec

set_option linter.unusedSectionVars false

namespace GW.Bridge

open Finset GW.Endpoint.Kernel.Eps

variable {κ τ γ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq τ]

/-- Spatial Bloch data at one `q`: energies, occupied set, pair densities, supercell volume. -/
structure SpData (κ γ : Type*) where
  e : κ → ℝ
  Oc : Finset κ
  rho : κ → κ → γ → ℝ
  Vol : ℝ

variable (B : SpData κ γ)

/-- The spin-orbital E1 system: two spins, spin-diagonal density, `1/√V` per amplitude. -/
noncomputable def spinSys : FSys (Bool × κ) γ where
  ε x := B.e x.2
  O := univ ×ˢ B.Oc
  P x y g := if x.1 = y.1 then B.rho x.2 y.2 g / √B.Vol else 0

/-- The spatial static sum (no spin, no volume). -/
noncomputable def chiSp (g g' : γ) : ℝ :=
  ∑ v ∈ B.Oc, ∑ c ∈ B.Ocᶜ,
    (B.rho c v g * B.rho c v g' + B.rho v c g * B.rho v c g') / (B.e v - B.e c)

theorem compl_prod_univ (s : Finset κ) : ((univ : Finset Bool) ×ˢ s)ᶜ = univ ×ˢ sᶜ := by
  ext x; simp

/-- **The spin factor.** For `V > 0`, summing the two spins gives exactly `2`. -/
theorem spin_chiS (hV : 0 < B.Vol) (g g' : γ) :
    chiS (spinSys B) g g' = 2 / B.Vol * chiSp B g g' := by
  have hs : √B.Vol * √B.Vol = B.Vol := Real.mul_self_sqrt hV.le
  have hs0 : √B.Vol ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  have key : ∀ a b : ℝ, a / √B.Vol * (b / √B.Vol) = a * b / B.Vol := by
    intro a b; rw [← hs]; field_simp
  unfold chiS chiSp
  simp only [spinSys]
  rw [compl_prod_univ]
  have inner : ∀ x : Bool × κ, (∑ y ∈ (univ : Finset Bool) ×ˢ B.Ocᶜ,
      ((if y.1 = x.1 then B.rho y.2 x.2 g / √B.Vol else 0) *
          (if y.1 = x.1 then B.rho y.2 x.2 g' / √B.Vol else 0) +
        (if x.1 = y.1 then B.rho x.2 y.2 g / √B.Vol else 0) *
          (if x.1 = y.1 then B.rho x.2 y.2 g' / √B.Vol else 0)) / (B.e x.2 - B.e y.2)) =
      1 / B.Vol * ∑ c ∈ B.Ocᶜ,
        (B.rho c x.2 g * B.rho c x.2 g' + B.rho x.2 c g * B.rho x.2 c g') / (B.e x.2 - B.e c) := by
    rintro ⟨σ, v⟩
    rw [sum_product, Fintype.sum_bool, mul_sum]
    cases σ <;>
    · simp only [if_true, Bool.true_eq_false, Bool.false_eq_true, if_false, mul_zero, zero_add,
        add_zero, sum_const_zero, zero_div]
      refine sum_congr rfl fun c _ => ?_
      rw [key, key]; ring
  rw [sum_congr rfl fun x _ => inner x, sum_product, Fintype.sum_bool, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  ring

/-! ### The pairing with EpsSpec's triples -/

/-- The index set `T` of EpsSpec's terms and, per term, the spatial orbitals of the
resonant pair (`vR` occupied at `k + q`, `cR` empty at `k`) and of its time-reversal
partner (`vA` occupied, `cA` empty), the pair density `M` and the energies. -/
structure Pairs (κ τ γ : Type*) where
  T : Finset τ
  vR : τ → κ
  cR : τ → κ
  vA : τ → κ
  cA : τ → κ
  M : τ → γ → ℝ
  Ev : τ → ℝ
  Ec : τ → ℝ

variable (Q : Pairs κ τ γ)

/-- **Named hypothesis (unfolding trust).** The data's pairs are the Bloch pairs
`(v, k+q), (c, k)` of the theory: distinct, occupied/empty, with EpsSpec's pair density
and energies. -/
structure ResOK : Prop where
  inj : Set.InjOn (fun x => (Q.vR x, Q.cR x)) Q.T
  mem : ∀ x ∈ Q.T, Q.vR x ∈ B.Oc ∧ Q.cR x ∉ B.Oc
  rho : ∀ x ∈ Q.T, ∀ g, B.rho (Q.vR x) (Q.cR x) g = Q.M x g
  ene : ∀ x ∈ Q.T, B.e (Q.vR x) = Q.Ev x ∧ B.e (Q.cR x) = Q.Ec x

/-- **Named hypothesis (time reversal).** The other time ordering's pair
`(c, k'), (v, k' - q)` has, via `k' = -k`, the same pair density and energies. -/
structure TROK : Prop where
  inj : Set.InjOn (fun x => (Q.vA x, Q.cA x)) Q.T
  mem : ∀ x ∈ Q.T, Q.vA x ∈ B.Oc ∧ Q.cA x ∉ B.Oc
  rho : ∀ x ∈ Q.T, ∀ g, B.rho (Q.cA x) (Q.vA x) g = Q.M x g
  ene : ∀ x ∈ Q.T, B.e (Q.vA x) = Q.Ev x ∧ B.e (Q.cA x) = Q.Ec x

/-- The resonant pairs. -/
def imgR : Finset (κ × κ) := Q.T.image fun x => (Q.vR x, Q.cR x)
/-- The time-reversed pairs. -/
def imgA : Finset (κ × κ) := Q.T.image fun x => (Q.vA x, Q.cA x)

/-- The remainder of the hole-first ordering: occupied/empty pairs not in the data. -/
noncomputable def remR (g g' : γ) : ℝ :=
  ∑ p ∈ (B.Oc ×ˢ B.Ocᶜ) \ imgR Q, B.rho p.1 p.2 g * B.rho p.1 p.2 g' / (B.e p.1 - B.e p.2)

/-- The remainder of the particle-first ordering. -/
noncomputable def remA (g g' : γ) : ℝ :=
  ∑ p ∈ (B.Oc ×ˢ B.Ocᶜ) \ imgA Q, B.rho p.2 p.1 g * B.rho p.2 p.1 g' / (B.e p.1 - B.e p.2)

/-- The data sum `Σ_{x ∈ T} M M / (E_v - E_c)`. -/
noncomputable def dataSum (g g' : γ) : ℝ := ∑ x ∈ Q.T, Q.M x g * Q.M x g' / (Q.Ev x - Q.Ec x)

/-- **Named hypothesis (bands / momentum conservation).** Every occupied/empty pair
outside the data has zero pair density. -/
def Bands : Prop :=
  (∀ p ∈ (B.Oc ×ˢ B.Ocᶜ) \ imgR Q, ∀ g, B.rho p.1 p.2 g = 0) ∧
    (∀ p ∈ (B.Oc ×ˢ B.Ocᶜ) \ imgA Q, ∀ g, B.rho p.2 p.1 g = 0)

theorem split_img {s : Finset (κ × κ)} (F : κ × κ → ℝ) (f : τ → κ × κ)
    (hinj : Set.InjOn f Q.T) (hsub : ∀ x ∈ Q.T, f x ∈ s) :
    ∑ p ∈ s, F p = ∑ x ∈ Q.T, F (f x) + ∑ p ∈ s \ Q.T.image f, F p := by
  have hs : Q.T.image f ⊆ s := by
    intro p hp; obtain ⟨x, hx, rfl⟩ := mem_image.mp hp; exact hsub x hx
  rw [← sum_sdiff hs, sum_image (fun x hx y hy h => hinj hx hy h), add_comm]

/-- **E2.** For `V > 0`, under the unfolding and time-reversal hypotheses the theory
static `χ0` is `4/V` times the data sum, plus the remainder. -/
theorem bloch_chi (hV : 0 < B.Vol) (hR : ResOK B Q) (hA : TROK B Q) (g g' : γ) :
    chiS (spinSys B) g g' =
      4 / B.Vol * dataSum Q g g' + 2 / B.Vol * (remR B Q g g' + remA B Q g g') := by
  rw [spin_chiS B hV]
  have h1 : chiSp B g g' =
      (∑ p ∈ B.Oc ×ˢ B.Ocᶜ, B.rho p.2 p.1 g * B.rho p.2 p.1 g' / (B.e p.1 - B.e p.2)) +
        ∑ p ∈ B.Oc ×ˢ B.Ocᶜ, B.rho p.1 p.2 g * B.rho p.1 p.2 g' / (B.e p.1 - B.e p.2) := by
    unfold chiSp
    rw [sum_product, sum_product, ← sum_add_distrib]
    refine sum_congr rfl fun v _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    ring
  have hRs := split_img Q (s := B.Oc ×ˢ B.Ocᶜ)
    (fun p => B.rho p.1 p.2 g * B.rho p.1 p.2 g' / (B.e p.1 - B.e p.2)) _ hR.inj
    (fun x hx => mem_product.mpr ⟨(hR.mem x hx).1, mem_compl.mpr (hR.mem x hx).2⟩)
  have hAs := split_img Q (s := B.Oc ×ˢ B.Ocᶜ)
    (fun p => B.rho p.2 p.1 g * B.rho p.2 p.1 g' / (B.e p.1 - B.e p.2)) _ hA.inj
    (fun x hx => mem_product.mpr ⟨(hA.mem x hx).1, mem_compl.mpr (hA.mem x hx).2⟩)
  have eR : ∑ x ∈ Q.T, B.rho (Q.vR x) (Q.cR x) g * B.rho (Q.vR x) (Q.cR x) g' /
      (B.e (Q.vR x) - B.e (Q.cR x)) = dataSum Q g g' := by
    refine sum_congr rfl fun x hx => ?_
    rw [hR.rho x hx, hR.rho x hx, (hR.ene x hx).1, (hR.ene x hx).2]
  have eA : ∑ x ∈ Q.T, B.rho (Q.cA x) (Q.vA x) g * B.rho (Q.cA x) (Q.vA x) g' /
      (B.e (Q.vA x) - B.e (Q.cA x)) = dataSum Q g g' := by
    refine sum_congr rfl fun x hx => ?_
    rw [hA.rho x hx, hA.rho x hx, (hA.ene x hx).1, (hA.ene x hx).2]
  rw [h1, hRs, hAs]
  simp only at eR eA ⊢
  rw [eR, eA]
  unfold remR remA imgR imgA
  ring

theorem rem_zero (h : Bands B Q) (g g' : γ) : remR B Q g g' = 0 ∧ remA B Q g g' = 0 :=
  ⟨sum_eq_zero fun p hp => by rw [h.1 p hp g]; ring,
   sum_eq_zero fun p hp => by rw [h.2 p hp g]; ring⟩

/-! ### EpsSpec's `chi` as a sum over its triples -/

section inp

variable (inp : Input)

/-- EpsSpec's triples `(k, v, c)`. -/
noncomputable def inpT : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range inp.ks.length).sigma fun t =>
    range (inp.ks.getD t default).cv.length ×ˢ range (inp.ks.getD t default).cc.length

/-- EpsSpec's pair density of a triple. -/
noncomputable def inpM (x : Σ _ : ℕ, ℕ × ℕ) (G : V3) : ℝ :=
  M inp (inp.ks.getD x.1 default) x.2.1 x.2.2 G

/-- `E_v(k + q)` of a triple (Ry). -/
noncomputable def inpEv (x : Σ _ : ℕ, ℕ × ℕ) : ℝ :=
  dy inp.SEn ((inp.ks.getD x.1 default).Ev.getD x.2.1 0)

/-- `E_c(k)` of a triple (Ry). -/
noncomputable def inpEc (x : Σ _ : ℕ, ℕ × ℕ) : ℝ :=
  dy inp.SEn ((inp.ks.getD x.1 default).Ec.getD x.2.2 0)

/-- `N_k Ω`. -/
noncomputable def inpVol : ℝ := inp.ks.length * dy inp.SOm inp.Om

theorem chi_eq_triples (G G' : V3) :
    chi inp G G' = 4 / inpVol inp *
      ∑ x ∈ inpT inp, inpM inp x G * inpM inp x G' / (inpEv inp x - inpEc inp x) := by
  unfold chi inpT inpVol
  rw [sum_sigma]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [sum_product]
  rfl

/-- The pairing of a theory system with EpsSpec's data. -/
noncomputable def pairsOf (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ) : Pairs κ (Σ _ : ℕ, ℕ × ℕ) V3 where
  T := inpT inp
  vR := vR
  cR := cR
  vA := vA
  cA := cA
  M := inpM inp
  Ev := inpEv inp
  Ec := inpEc inp

/-- **E2 for EpsSpec.** EpsSpec's `chi` is the theory static `χ0` of the spin-orbital
Bloch system minus the remainder, under the named hypotheses: supercell volume
`V = N_k Ω` with `0 < V`, unfolding trust `ResOK`, time reversal `TROK`. -/
theorem epsSpec_chi_eq_theory (B : SpData κ V3) (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ)
    (hV : B.Vol = inpVol inp) (hVp : 0 < B.Vol)
    (hR : ResOK B (pairsOf inp vR cR vA cA)) (hA : TROK B (pairsOf inp vR cR vA cA))
    (G G' : V3) :
    chi inp G G' = chiS (spinSys B) G G' -
      2 / B.Vol * (remR B (pairsOf inp vR cR vA cA) G G' + remA B (pairsOf inp vR cR vA cA) G G') := by
  rw [bloch_chi B _ hVp hR hA, chi_eq_triples, ← hV]
  unfold dataSum
  simp only [pairsOf]
  ring

/-- **E2 for EpsSpec, complete bands.** Under `Bands` as well, EpsSpec's `chi` IS the
theory static `χ0`. -/
theorem epsSpec_chi_eq_theory_bands (B : SpData κ V3) (vR cR vA cA : (Σ _ : ℕ, ℕ × ℕ) → κ)
    (hV : B.Vol = inpVol inp) (hVp : 0 < B.Vol)
    (hR : ResOK B (pairsOf inp vR cR vA cA)) (hA : TROK B (pairsOf inp vR cR vA cA))
    (hB : Bands B (pairsOf inp vR cR vA cA)) (G G' : V3) :
    chi inp G G' = chiS (spinSys B) G G' := by
  rw [epsSpec_chi_eq_theory inp B vR cR vA cA hV hVp hR hA, (rem_zero B _ hB G G').1,
    (rem_zero B _ hB G G').2]
  ring

end inp

/-! ### The factor is `4`, not `2` -/

/-- One occupied orbital `true`, one empty `false`, pair density `m` both ways. -/
noncomputable def twoLevel (m ev ec V : ℝ) : SpData Bool Unit where
  e b := if b then ev else ec
  Oc := {true}
  rho _ _ _ := m
  Vol := V

/-- **The factor is not the spin factor alone.** For one occupied/empty pair with pair
density `m` and `V > 0` the theory gives `4 m² / (V (E_v - E_c))`: `2` for spin times `2`
for the two time orderings. A `2 m²/(V(E_v - E_c))` (spin only) would be wrong whenever
`m ≠ 0` and `E_v ≠ E_c` (with `E_v = E_c` Lean's `x/0 = 0` makes both forms `0`). -/
theorem factor_two_wrong (m ev ec V : ℝ) (hV : 0 < V) :
    chiS (spinSys (twoLevel m ev ec V)) () () = 4 / V * (m * m / (ev - ec)) := by
  rw [spin_chiS _ hV]
  unfold chiSp twoLevel
  have hc : ({true} : Finset Bool)ᶜ = {false} := by decide
  simp only [hc, sum_singleton, if_true, Bool.false_eq_true, if_false]
  ring

end GW.Bridge

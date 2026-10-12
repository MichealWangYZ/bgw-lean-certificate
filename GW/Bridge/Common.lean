/-
R28-F1: ONE finite mean-field system as the common source of the screening and the
self-energy data, and the composed theorem stated for it.

REVIEW-28 F1: `sigA_eps_eq_theory_q0` (EpsQ0Sigma.lean) takes the screening blocks
`bs : ℕ → EpsBlock κ` independently of the Σ data `gl`, `st`; nothing identifies the
orbitals, energies, occupations, density, geometry and interaction of the screening
system with the ones in Σ. This file supplies that identification.

* `MF` is a finite, closed-shell, spin-unpolarised mean-field system on a Born-von Karman
  grid of `NK` k-points: the cell (`bdot` `B`, `celvol` `Om`), for each grid point `k` its
  G-sphere `G k`, the coefficient rows `c k` of its `nb` bands and their energies `e k`
  (Ry), the number of occupied bands `nocc`, and the density list `rho` (the RHO file
  format). All bands of the system are used on both sides: the system IS the finite band
  set. `MF` is a DATA RECORD: nothing requires the rows to be orthonormal, and there is no
  Hamiltonian or eigen-equation.
* `EP` (per screening block, a grid `q ≠ 0`) and `SP` (the Σ calculation) are index plans
  only: which grid point is `k + q` (`plus`) and `-k` (`neg`), the eps sphere, which grid
  point is `k0 - q_t` (`minus`), the Σ q-list with its symmetry map, the multiplet. They
  carry no orbital, energy, occupation or cell data.
* The two maps: `MF.inp` / `MF.blk` (to EpsSpec's `Input` and an `EpsBlock` whose theory
  Bloch system `MF.sp` is built from the SAME orbitals), and `MF.gl` / `MF.st` (to
  SigmaSpec's `Gl`, `St`).
* `blk_ok`: for a well-formed system (`MF.WF`) with a consistent grid plan (`EP.WF`) and
  time reversal (`MF.TR`), the block hypotheses `EpsBlock.OK` are THEOREMS except `qne`
  (`q + G ≠ 0` on the sphere): `vol`, `volpos`, `res` (unfolding), `tr` (time reversal,
  only from `MF.TR`) and `bands` (complete bands, momentum conservation) are proved from
  the construction. `res` and `bands` hold by construction: `MF.sp` builds momentum
  conservation in through the plan's index map `plus`.
* `MF.TR` is an exact, ordered list identity (no sphere permutation, no umklapp, no sign or
  multiplet rotation). `MF.tr_fixed`: at a grid point that `neg` fixes (time-reversal
  invariant when `neg` encodes `-k`, e.g. Γ, X, L) it forces every sphere vector to be `0`.
  `compat_selfpaired_no_TR`: a block whose `neg` fixes `k0`, with a nonzero vector in the
  sphere at `k0`, cannot satisfy `TR`. `Z` is a `Finset`, so `hT` covers infinitely many
  blocks, and the hypotheses of `sigA_compat` are unsatisfiable under either of two
  premises: every plan off `Z` has a `neg` that fixes the same grid point, whose sphere
  holds a nonzero vector (`hyps_unsat_of_selfpaired`), or no grid index stores the negated sphere
  list of some grid point (`hnp`, `hyps_unsat_of_unpaired`, for arbitrary plans). Storing
  X or L once implies neither by itself (`MF` carries no k-coordinates). The first follows
  on such a grid from the trusted, unformalised premise that every plan's `neg` encodes
  `-k` (X, L and Γ are time-reversal-invariant); under it `sigA_compat` cannot be applied
  to O1 at all, and Γ-centred grids are excluded too. A generalized `TR` (sphere
  permutation, umklapp, rotation within degenerate multiplets) is not formalized.
* `sigA_common`: SigmaSpec with `eps⁻¹` the inverse of EpsSpec's eps of the system's
  blocks equals the theory `SigT` built from the inverse theory RPA eps of the SAME system
  plus `COR` ("inverse" is Mathlib's totalized matrix inverse, `0` for a singular matrix;
  it is a genuine inverse only when `det eps ≠ 0`, which is not established for these
  blocks), under the remaining named hypotheses (`qne`, `hC`, `hWq`, `hZ`, `hX`,
  `ModeOK` off the `q = 0` wings). The `q = 0` blocks `Z` carry an input `E0`, the same on
  both sides (`Espec`, `Etheory`), so their head and wings are not derived here: a finite
  BvK system has no `q = 0` RPA block (`v(0)` is singular); BerkeleyGW computes it at a
  finite `q0` from auxiliary states `k + q0` (WFNq) that are not grid states. Taking `E0`
  to be EpsSpec's `q0` block recovers BerkeleyGW's input exactly (`Espec_q0_input`).
  `hC` (`vb = vc`) is met trivially by `vc := vb`; with the physical point value
  `vc = vBareK` it fails on the run (`vb` are mini-BZ averages).
* `Compat` is the compatibility predicate between arbitrary data `bs`, `gl`, `st` and a
  system: the eps Inputs off `Z`, the `Gl` and the `St` are the system's images, and `k0`
  and every `k0 - q_t` are grid points (fields `k0`, `minus`; without them an off-grid
  copy of the Σ states met the predicate with any energies: `offgrid_loophole`).
  `sigA_compat` is the composed theorem for such data, with the theory side built from
  the system, the trusted plans and a free Coulomb function `vc`. `compat_st_unique`:
  given the blocks `bs` and `gl` (and one block off `Z` whose `plus` is onto the grid), at
  most ONE `st` is compatible, for EVERY system; `compat_energy_shift` is the reviewer's adversarial case
  (fixed `bs`, `st` energies changed) as a theorem: no system makes it compatible under the
  same plans (`EPs`, `Z`, `P`), given such an onto block and a nonempty multiplet.
* `coulomb_same`: the theory interaction is one function of the shared cell: EpsSpec's
  `v(q + G) = 8π/|q + G|²` equals `vBareK` of the Σ data at the key `2(q + G)`. It is not
  a premise of `sigA_compat`, which does not identify the Σ and eps interactions.
* `DensOK`: the density list is the system's own occupied density, the named
  hypothesis under which the HL `Ω²` of `SigT` is built from the SAME system's density
  (`omT_dens`). It is a hypothesis, not discharged (it FAILS on the Si-EPM run: RHO is
  the unsymmetrised IBZ sum, BRIDGE-FIX; measured in `bgw/r28_f1/`).

Not formalized here (recorded): that the plans' index maps encode the k-point
coordinates (k + q, -k, k0 - q_t) and the symmetry map of Σ's spheres (`Screening.mapping`:
`idx`, `neg`, `iq`); these are the same trust items as in SigmaSpec. Whether the
Si-EPM run's data are images of one system is checked in `bgw/r28_f1/check.py`: they are
NOT (the eps k-set and the Σ k-set are disjoint, so with any block off `Z` no system is
compatible); see `docs/reviews/R28-F1.md`.
-/
import GW.Bridge.EpsQ0Sigma

set_option linter.unusedSectionVars false

namespace GW.Bridge.Common

open Finset GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig GW.Bridge

/-! ### The system and the plans -/

/-- A finite mean-field system on a BvK grid of `NK` k-points with `nb` bands. -/
structure MF where
  SC : ℕ
  SEn : ℕ
  SB : ℕ
  SOm : ℕ
  B : List (List ℤ)
  Om : ℕ
  SR : ℕ
  rho : List (V3 × ℤ)
  nocc : ℕ
  NK : ℕ
  nb : ℕ
  hNK : 0 < NK
  hnb : 0 < nb
  /-- The G-sphere of grid point `k`. -/
  G : ℕ → List V3
  /-- The coefficient rows (one per band) at grid point `k`, scale `2^-SC`. -/
  c : ℕ → List (List ℤ)
  /-- The band energies (Ry, scale `2^-SEn`) at grid point `k`. -/
  e : ℕ → List ℤ

/-- The plan of one screening block (a grid `q ≠ 0`): `q`, the eps sphere, the grid
points `k + q` and `-k`. -/
structure EP where
  SQ : ℕ
  qn : V3
  Gs : List V3
  plus : ℕ → ℕ
  neg : ℕ → ℕ

/-- The plan of the Σ calculation: the static-CH sphere, the q-list (with Σ's symmetry
map), the state's grid point `k0`, its multiplet, and the grid points `k0 - q_t`. -/
structure SP where
  Gch : List V3
  qs : List QD
  k0 : ℕ
  ms : List ℕ
  minus : ℕ → ℕ

namespace MF

variable (S : MF)

/-! ### The map to the screening -/

/-- The k-pair of grid point `t`: valence (bands `< nocc`) at `k + q`, conduction (all
other bands of the system) at `k`. -/
def kpair (P : EP) (t : ℕ) : KPair :=
  ⟨S.G (P.plus t), (S.c (P.plus t)).take S.nocc, (S.e (P.plus t)).take S.nocc,
   S.G t, (S.c t).drop S.nocc, (S.e t).drop S.nocc⟩

/-- **The map to EpsSpec.** The Input of one block: the system's cell and scales, the
k-sum over the WHOLE grid. -/
def inp (P : EP) : Input :=
  ⟨S.SC, S.SEn, S.SB, S.SOm, P.SQ, P.qn, S.B, S.Om, P.Gs, (List.range S.NK).map (S.kpair P)⟩

/-! ### The map to the self-energy -/

/-- **The map to SigmaSpec's `Gl`.** -/
def gl (P : SP) : Gl := ⟨S.SC, S.SEn, S.SB, S.B, S.SOm, S.Om, S.SR, S.rho, P.Gch, P.qs, S.nocc⟩

/-- **The map to SigmaSpec's `St`.** The multiplet at `k0` and, at every `q_t`, all bands
of the system at `k0 - q_t`. -/
def st (P : SP) : St :=
  ⟨S.G P.k0, P.ms.map (fun n => (S.c P.k0).getD n []), P.ms.map (fun n => (S.e P.k0).getD n 0),
   (List.range P.qs.length).map fun t => ⟨S.G (P.minus t), S.c (P.minus t), S.e (P.minus t)⟩⟩

/-! ### The theory Bloch system of the same orbitals -/

/-- The spatial orbitals `(k, n)`. -/
abbrev Orb := Fin S.NK × Fin S.nb

def fk (n : ℕ) : Fin S.NK := ⟨n % S.NK, Nat.mod_lt _ S.hNK⟩
def fb (n : ℕ) : Fin S.nb := ⟨n % S.nb, Nat.mod_lt _ S.hnb⟩

/-- The plane-wave pair density `Σ_{G_i - G'_j = g} c_x(G_i) c_y(G'_j)` of two orbitals. -/
noncomputable def pdO (P : EP) (x y : S.Orb) (g : V3) : ℝ :=
  M (S.inp P) ⟨S.G x.1, S.c x.1, S.e x.1, S.G y.1, S.c y.1, S.e y.1⟩ x.2 y.2 g

/-- **The theory system of block `P`**: the system's orbitals, energies, occupations
(`n < nocc`), the momentum-conserving pair densities (`k_x = k_y + q`, i.e.
`x.k = plus y.k`) and the BvK volume `N_k Ω`. -/
noncomputable def sp (P : EP) : SpData S.Orb V3 where
  e x := dy S.SEn ((S.e x.1).getD x.2 0)
  Oc := univ.filter fun x => (x.2 : ℕ) < S.nocc
  rho x y g := if (x.1 : ℕ) = P.plus y.1 then S.pdO P x y g else 0
  Vol := S.NK * dy S.SOm S.Om

def vR (P : EP) (x : Σ _ : ℕ, ℕ × ℕ) : S.Orb := (S.fk (P.plus x.1), S.fb x.2.1)
def cR (_P : EP) (x : Σ _ : ℕ, ℕ × ℕ) : S.Orb := (S.fk x.1, S.fb (S.nocc + x.2.2))
def vA (P : EP) (x : Σ _ : ℕ, ℕ × ℕ) : S.Orb := (S.fk (P.neg (P.plus x.1)), S.fb x.2.1)
def cA (P : EP) (x : Σ _ : ℕ, ℕ × ℕ) : S.Orb := (S.fk (P.neg x.1), S.fb (S.nocc + x.2.2))

/-- **The screening block of the system**: EpsSpec's Input and the theory Bloch system,
both from the same orbitals. -/
noncomputable def blk (P : EP) : EpsBlock S.Orb :=
  ⟨S.inp P, S.sp P, S.vR P, S.cR P, S.vA P, S.cA P⟩

/-- The blocks of a plan family. -/
noncomputable def bs (EPs : ℕ → EP) : ℕ → EpsBlock S.Orb := fun iq => S.blk (EPs iq)

/-! ### Well-formedness -/

/-- The system is well formed: `nocc ≤ nb`, `nb` coefficient rows at every grid point,
positive cell volume. -/
structure WF : Prop where
  occ : S.nocc ≤ S.nb
  rows : ∀ k < S.NK, (S.c k).length = S.nb
  om : 0 < S.Om

/-- Time reversal of the real-flavour system: `φ_{n,-k}(G) = φ_{n,k}(-G)`, same energy. -/
def TR (P : EP) : Prop :=
  ∀ t < S.NK, S.G (P.neg t) = (S.G t).map (fun g => -g) ∧ S.c (P.neg t) = S.c t ∧
    S.e (P.neg t) = S.e t

end MF

/-- A grid plan is consistent: `plus` and `neg` map the grid into itself, `neg` is an
involution, and `-(k + q) + q = -k`. -/
structure EP.WF (P : EP) (S : MF) : Prop where
  plus_lt : ∀ t < S.NK, P.plus t < S.NK
  neg_lt : ∀ t < S.NK, P.neg t < S.NK
  neg_neg : ∀ t < S.NK, P.neg (P.neg t) = t
  plus_neg : ∀ t < S.NK, P.plus (P.neg (P.plus t)) = P.neg t

namespace MF

variable (S : MF)

/-! ### The block hypotheses are theorems -/

theorem ks_getD (P : EP) {t : ℕ} (ht : t < S.NK) :
    (S.inp P).ks.getD t default = S.kpair P t := by
  simp [inp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, ht]

theorem ks_length (P : EP) : (S.inp P).ks.length = S.NK := by simp [inp]

theorem fk_val {n : ℕ} (h : n < S.NK) : ((S.fk n : Fin S.NK) : ℕ) = n := Nat.mod_eq_of_lt h
theorem fb_val {n : ℕ} (h : n < S.nb) : ((S.fb n : Fin S.nb) : ℕ) = n := Nat.mod_eq_of_lt h

theorem getD_take {α : Type*} (l : List α) (d : α) {n v : ℕ} (h : v < n) :
    (l.take n).getD v d = l.getD v d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_drop {α : Type*} (l : List α) (d : α) (n c : ℕ) :
    (l.drop n).getD c d = l.getD (n + c) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `M` reads only the two spheres and the two selected rows. -/
theorem M_congr (inp inp' : Input) (hSC : inp.SC = inp'.SC) (kp kp' : KPair) (v c v' c' : ℕ)
    (h1 : kp.Gv = kp'.Gv) (h2 : kp.Gc = kp'.Gc) (h3 : kp.cv.getD v [] = kp'.cv.getD v' [])
    (h4 : kp.cc.getD c [] = kp'.cc.getD c' []) (g : V3) :
    M inp kp v c g = M inp' kp' v' c' g := by
  unfold M; rw [h1, h2, h3, h4, hSC]

/-- Membership in EpsSpec's triples of the system's Input. -/
theorem mem_inpT (hS : S.WF) (P : EP) (x : Σ _ : ℕ, ℕ × ℕ) (hp : ∀ t < S.NK, P.plus t < S.NK) :
    x ∈ inpT (S.inp P) ↔ x.1 < S.NK ∧ x.2.1 < S.nocc ∧ x.2.2 < S.nb - S.nocc := by
  rcases x with ⟨t, v, c⟩
  simp only [inpT, mem_sigma, mem_range, mem_product, ks_length]
  constructor
  · rintro ⟨ht, hv, hc⟩
    rw [S.ks_getD P ht] at hv hc
    simp only [kpair, List.length_take, List.length_drop, hS.rows _ (hp t ht),
      hS.rows t ht] at hv hc
    exact ⟨ht, lt_of_lt_of_le hv (min_le_left _ _), hc⟩
  · rintro ⟨ht, hv, hc⟩
    rw [S.ks_getD P ht]
    simp only [kpair, List.length_take, List.length_drop, hS.rows _ (hp t ht), hS.rows t ht]
    exact ⟨ht, lt_min hv (lt_of_lt_of_le hv hS.occ), hc⟩

theorem blk_vol (P : EP) : (S.sp P).Vol = inpVol (S.inp P) := by
  simp [sp, inpVol, ks_length, inp]

theorem blk_volpos (hS : S.WF) (P : EP) : 0 < (S.sp P).Vol := by
  have h1 : (0 : ℝ) < S.NK := by exact_mod_cast S.hNK
  have h2 : (0 : ℝ) < dy S.SOm S.Om := by
    unfold dy; have : (0 : ℝ) < S.Om := by exact_mod_cast hS.om
    positivity
  simp only [sp]; positivity

/-- **Unfolding (`ResOK`) is a theorem** for the system's own block. -/
theorem blk_res (hS : S.WF) (P : EP) (hP : P.WF S) :
    ResOK (S.sp P) (pairsOf (S.inp P) (S.vR P) (S.cR P) (S.vA P) (S.cA P)) := by
  have mem := fun x => S.mem_inpT hS P x hP.plus_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨t, v, c⟩ hx ⟨t', v', c'⟩ hx' h
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    obtain ⟨ht', hv', hc'⟩ := (mem _).mp hx'
    simp only at ht hv hc ht' hv' hc'
    have := hS.occ
    simp only [pairsOf, vR, cR, Prod.mk.injEq] at h
    obtain ⟨⟨-, h2⟩, h3, h4⟩ := h
    have e3 := congrArg Fin.val h3
    have e2 := congrArg Fin.val h2
    have e4 := congrArg Fin.val h4
    rw [S.fk_val ht, S.fk_val ht'] at e3
    rw [S.fb_val (by omega), S.fb_val (by omega)] at e2
    rw [S.fb_val (by omega), S.fb_val (by omega)] at e4
    try simp only at e2 e3 e4
    subst e3 e2
    have : c = c' := by omega
    subst this; rfl
  · rintro ⟨t, v, c⟩ hx
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    simp only [pairsOf, vR, cR, sp, mem_filter, mem_univ, true_and]
    rw [S.fb_val (by omega), S.fb_val (by omega)]
    omega
  · rintro ⟨t, v, c⟩ hx g
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    have hpt := hP.plus_lt t ht
    simp only [pairsOf, vR, cR, sp, S.fk_val hpt, S.fk_val ht, if_true, pdO, inpM]
    rw [S.ks_getD P ht]
    apply M_congr _ _ rfl
    · rfl
    · rfl
    · simp only [kpair, S.fb_val (show v < S.nb by omega)]
      exact (getD_take _ _ hv).symm
    · simp only [kpair, S.fb_val (show S.nocc + c < S.nb by omega)]
      exact (getD_drop _ _ _ _).symm
  · rintro ⟨t, v, c⟩ hx
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    have hpt := hP.plus_lt t ht
    simp only [pairsOf, vR, cR, sp, inpEv, inpEc, S.ks_getD P ht, kpair, S.fk_val hpt,
      S.fk_val ht, S.fb_val (show v < S.nb by omega),
      S.fb_val (show S.nocc + c < S.nb by omega)]
    exact ⟨by rw [getD_take _ _ hv]; rfl, by rw [getD_drop]; rfl⟩

/-- The pair density of the time-reversed pair: real coefficients on the negated sphere. -/
theorem M_neg (inp : Input) (Gv Gc : List V3) (cv cc : List (List ℤ)) (Ev Ec : List ℤ)
    (Ev' Ec' : List ℤ) (v c : ℕ) (g : V3) :
    M inp ⟨Gc.map (fun x => -x), cc, Ec', Gv.map (fun x => -x), cv, Ev'⟩ c v g =
      M inp ⟨Gv, cv, Ev, Gc, cc, Ec⟩ v c g := by
  unfold M
  simp only [List.length_map]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have e1 : (Gc.map (fun x => -x)).getD j 0 = -(Gc.getD j 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj']
  have e2 : (Gv.map (fun x => -x)).getD i 0 = -(Gv.getD i 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hi']
  rw [e1, e2, show -(Gc.getD j 0) - -(Gv.getD i 0) = Gv.getD i 0 - Gc.getD j 0 by abel,
    mul_comm]

/-- **Time reversal (`TROK`) is a theorem** for a time-reversal-symmetric system. -/
theorem blk_tr (hS : S.WF) (P : EP) (hP : P.WF S) (hT : S.TR P) :
    TROK (S.sp P) (pairsOf (S.inp P) (S.vR P) (S.cR P) (S.vA P) (S.cA P)) := by
  have mem := fun x => S.mem_inpT hS P x hP.plus_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨t, v, c⟩ hx ⟨t', v', c'⟩ hx' h
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    obtain ⟨ht', hv', hc'⟩ := (mem _).mp hx'
    simp only at ht hv hc ht' hv' hc'
    have := hS.occ
    simp only [pairsOf, vA, cA, Prod.mk.injEq] at h
    obtain ⟨⟨-, h2⟩, h3, h4⟩ := h
    have e3 := congrArg Fin.val h3
    have e2 := congrArg Fin.val h2
    have e4 := congrArg Fin.val h4
    rw [S.fk_val (hP.neg_lt t ht), S.fk_val (hP.neg_lt t' ht')] at e3
    rw [S.fb_val (by omega), S.fb_val (by omega)] at e2
    rw [S.fb_val (by omega), S.fb_val (by omega)] at e4
    try simp only at e2 e3 e4
    have et : t = t' := by rw [← hP.neg_neg t ht, ← hP.neg_neg t' ht', e3]
    subst et e2
    have : c = c' := by omega
    subst this; rfl
  · rintro ⟨t, v, c⟩ hx
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    simp only [pairsOf, vA, cA, sp, mem_filter, mem_univ, true_and]
    rw [S.fb_val (by omega), S.fb_val (by omega)]
    omega
  · rintro ⟨t, v, c⟩ hx g
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    have hpt := hP.plus_lt t ht
    have hn := hP.neg_lt t ht
    have hnp := hP.neg_lt _ hpt
    have hm : P.neg t = P.plus (P.neg (P.plus t)) := (hP.plus_neg t ht).symm
    obtain ⟨g1, c1, -⟩ := hT t ht
    obtain ⟨g2, c2, -⟩ := hT _ hpt
    simp only [pairsOf, vA, cA, sp, S.fk_val hn, S.fk_val hnp, if_pos hm, pdO, inpM]
    rw [S.ks_getD P ht, g1, c1, g2, c2]
    rw [M_neg (S.inp P) (S.G (P.plus t)) (S.G t) (S.c (P.plus t)) (S.c t)
      (S.e (P.plus t)) (S.e t)]
    apply M_congr _ _ rfl
    · rfl
    · rfl
    · simp only [kpair, S.fb_val (show v < S.nb by omega)]
      exact (getD_take _ _ hv).symm
    · simp only [kpair, S.fb_val (show S.nocc + c < S.nb by omega)]
      exact (getD_drop _ _ _ _).symm
  · rintro ⟨t, v, c⟩ hx
    obtain ⟨ht, hv, hc⟩ := (mem _).mp hx
    simp only at ht hv hc
    have := hS.occ
    have hpt := hP.plus_lt t ht
    obtain ⟨-, -, e1⟩ := hT t ht
    obtain ⟨-, -, e2⟩ := hT _ hpt
    simp only [pairsOf, vA, cA, sp, inpEv, inpEc, S.ks_getD P ht, kpair,
      S.fk_val (hP.neg_lt _ hpt), S.fk_val (hP.neg_lt t ht), e1, e2,
      S.fb_val (show v < S.nb by omega), S.fb_val (show S.nocc + c < S.nb by omega)]
    exact ⟨by rw [getD_take _ _ hv]; rfl, by rw [getD_drop]; rfl⟩

/-- **Complete bands (`Bands`) is a theorem**: the Input sums every momentum-conserving
occupied/empty pair of the system (all its bands, the whole grid). -/
theorem blk_bands (hS : S.WF) (P : EP) (hP : P.WF S) :
    Bands (S.sp P) (pairsOf (S.inp P) (S.vR P) (S.cR P) (S.vA P) (S.cA P)) := by
  have mem := fun x => S.mem_inpT hS P x hP.plus_lt
  have hocc := hS.occ
  constructor
  · rintro ⟨x, y⟩ hp g
    simp only [mem_sdiff, mem_product, sp, mem_filter, mem_univ, true_and, mem_compl,
      not_lt] at hp
    obtain ⟨⟨hx, hy⟩, hni⟩ := hp
    have hy2 := y.2.2
    simp only [sp]
    split_ifs with h
    · exfalso; apply hni
      refine mem_image.mpr ⟨⟨y.1, (x.2, y.2 - S.nocc)⟩,
        (mem _).mpr ⟨y.1.2, hx, show (y.2 : ℕ) - S.nocc < S.nb - S.nocc by omega⟩, ?_⟩
      refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · show ((S.fk (P.plus y.1)) : ℕ) = x.1
        rw [S.fk_val (hP.plus_lt _ y.1.2)]; exact h.symm
      · exact S.fb_val x.2.2
      · exact S.fk_val y.1.2
      · show ((S.fb (S.nocc + (y.2 - S.nocc))) : ℕ) = y.2
        rw [S.fb_val (by omega)]; omega
    · rfl
  · rintro ⟨x, y⟩ hp g
    simp only [mem_sdiff, mem_product, sp, mem_filter, mem_univ, true_and, mem_compl,
      not_lt] at hp
    obtain ⟨⟨hx, hy⟩, hni⟩ := hp
    have hy2 := y.2.2
    simp only [sp]
    split_ifs with h
    · exfalso; apply hni
      have hx1 := x.1.2
      have hpx := hP.plus_lt _ hx1
      have hn := hP.neg_lt _ hpx
      refine mem_image.mpr ⟨⟨P.neg (P.plus x.1), (x.2, y.2 - S.nocc)⟩,
        (mem _).mpr ⟨hn, hx, show (y.2 : ℕ) - S.nocc < S.nb - S.nocc by omega⟩, ?_⟩
      refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · show ((S.fk (P.neg (P.plus (P.neg (P.plus x.1))))) : ℕ) = x.1
        rw [hP.plus_neg _ hx1, hP.neg_neg _ hx1, S.fk_val hx1]
      · exact S.fb_val x.2.2
      · show ((S.fk (P.neg (P.neg (P.plus x.1)))) : ℕ) = y.1
        rw [hP.neg_neg _ hpx, S.fk_val hpx]; exact h.symm
      · show ((S.fb (S.nocc + (y.2 - S.nocc))) : ℕ) = y.2
        rw [S.fb_val (by omega)]; omega
    · rfl

/-- **The block hypotheses of the system's own blocks**: only `qne` (`q + G ≠ 0` on the
sphere) remains a block hypothesis. `tr` (TROK) follows from the system hypothesis
`MF.TR` (`hT`), which cannot hold at a self-paired grid point with a nonzero sphere vector
(`MF.tr_fixed`). `res` and `bands` hold by construction: the theory pair density builds
in momentum conservation through the index map `plus`. -/
theorem blk_ok (hS : S.WF) (P : EP) (hP : P.WF S) (hT : S.TR P)
    (hq : ∀ i : Fin (S.inp P).Gs.length, qG2 (S.inp P) (gsI (S.inp P) i) ≠ 0) :
    (S.blk P).OK :=
  ⟨hq, S.blk_vol P, S.blk_volpos hS P, S.blk_res hS P hP, S.blk_tr hS P hP hT,
    S.blk_bands hS P hP⟩

end MF

/-! ### The composed theorem for one system -/

/-- **R28-F1, the composed theorem for one common system.** SigmaSpec's `SigA` of the
system's Σ data, with `eps⁻¹` the inverse of EpsSpec's eps of the SAME system's blocks
(off the `q = 0` blocks `Z`, whose `eps⁻¹` is the input `E0`), equals the theory `SigT`
built from the inverse theory RPA eps `1 - v χ0` of the SAME system's Bloch orbitals,
plus `COR`. Both inverses are Mathlib's totalized matrix inverse (`0` for a singular
matrix); they are genuine inverses only when `det eps ≠ 0`, which is not established for
these blocks. Unfolding, complete bands and the volume hold for the system's own blocks,
and time reversal follows from `MF.TR` (`blk_ok`). The remaining named hypotheses are
the well-formedness hypotheses `hS` (`MF.WF`) and `hP` (`EP.WF` for every block outside
`Z`), `MF.TR`, `qne`, `hC` (`vb = vc`; `vc` is free, so `vc := vb` meets it trivially, and the
physical case `vc` = bare point values fails for mini-BZ averages), `hWq` (the `q ≠ 0`
wing factors), `hZ`, `hX` and `ModeOK` off the `q = 0` wings. -/
theorem sigA_common (S : MF) (EPs : ℕ → EP) (P : SP) (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ)
    (vb oq vc : V3 → ℝ) (a iw : ℕ) (hS : S.WF) (hP : ∀ iq ∉ Z, (EPs iq).WF S)
    (hT : ∀ iq ∉ Z, S.TR (EPs iq))
    (hq : ∀ iq ∉ Z, ∀ i : Fin (S.inp (EPs iq)).Gs.length,
      qG2 (S.inp (EPs iq)) (gsI (S.inp (EPs iq)) i) ≠ 0)
    (hC : ∀ k, vb k = vc k)
    (hWq : ∀ t < (S.gl P).qs.length, ((S.gl P).qs.getD t default).qh ≠ 0 →
      oq ((S.gl P).qs.getD t default).qh * qlen (S.gl P) ((S.gl P).qs.getD t default) /
          (8 * Real.pi) = 1 ∧
      oq ((S.gl P).qs.getD t default).qh / (vb (key ((S.gl P).qs.getD t default)
        (gs ((S.gl P).qs.getD t default) 0)) * qlen (S.gl P) ((S.gl P).qs.getD t default)) = 1)
    (hZ : ∀ t < (S.gl P).qs.length, ((S.gl P).qs.getD t default).qh = 0 →
      ZeroAt ((S.gl P).qs.getD t default))
    (hX : ∀ t < (S.gl P).qs.length, ∀ n1 < nbq (S.st P) t,
      TZ ≤ |xT (S.gl P) (S.st P) t a n1 iw|)
    (hM : ∀ t < (S.gl P).qs.length, ∀ n1 < nbq (S.st P) t, ∀ j < nG (S.gl P) t,
      ∀ i < nG (S.gl P) t, ¬ Wing ((S.gl P).qs.getD t default) j i →
      ModeOK (decide (n1 < (S.gl P).nocc)) (ITq (S.gl P) (Etheory Z E0 (S.bs EPs)) t j i)
        (OTq (S.gl P) vb t j i) (xT (S.gl P) (S.st P) t a n1 iw)) :
    SigA (S.gl P) (Espec Z E0 (S.bs EPs)) vb oq (S.st P) a iw =
      SigT (S.gl P) (Etheory Z E0 (S.bs EPs)) vc (S.st P) a iw +
        COR (S.gl P) (Etheory Z E0 (S.bs EPs)) vb oq (S.st P) a := by
  rw [Espec_eq_Etheory Z E0 (S.bs EPs)
    (fun iq h => S.blk_ok hS _ (hP iq h) (hT iq h) (hq iq h))]
  exact sigA_eq_theory_q0 (S.gl P) _ vb oq (S.st P) vc a iw hC hWq hZ hX hM

/-- With `E0` EpsSpec's eps of auxiliary Inputs `inp0` (BerkeleyGW: the `q0` block from
WFN/WFNq), the spec side is EpsSpec's eps on EVERY block, as BerkeleyGW computes it. -/
theorem Espec_q0_input {κ : Type*} [Fintype κ] [DecidableEq κ] (Z : Finset ℕ)
    (inp0 : ℕ → Input) (bs : ℕ → EpsBlock κ) (iq : ℕ) :
    Espec Z (fun i => blk (epsMatR (inp0 i))) bs iq =
      blk (epsMatR (if iq ∈ Z then inp0 iq else (bs iq).inp)) := by
  unfold Espec
  by_cases h : iq ∈ Z
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-! ### The compatibility predicate -/

/-- **Compatibility of arbitrary data with a system.** The screening blocks' Inputs
(off the `q = 0` blocks `Z`), the run data `gl` and the state data `st` are the images of
the ONE system `S` under the plans. Field by field this says: the eps Inputs and `gl`
share the scales `SC`, `SEn`, `SB`, `SOm`, the metric `B` and the volume `Om`; every eps
k-pair is (valence of `S` at `k + q`, conduction of `S` at `k`) for every grid point `k`;
`gl.nocc = S.nocc`; `gl.rho = S.rho`; `st` holds `S`'s sphere, rows and energies at `k0`
and, at every `q_t`, ALL bands of `S` at the grid point `k0 - q_t`.

`k0` and every `k0 - q_t` are GRID points (`k0`, `minus`). Without these two fields the
predicate could be met by storing the Σ states at an index outside the grid, which no
screening block reads; the screening would then be unrelated to the Σ states (the
REVIEW-28 F1 case; `offgrid_loophole` records why the fields are needed). -/
structure Compat {κ : Type*} (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP)
    (bs : ℕ → EpsBlock κ) (gl : Gl) (st : St) : Prop where
  eps : ∀ iq ∉ Z, (bs iq).inp = S.inp (EPs iq)
  sig : gl = S.gl P
  sta : st = S.st P
  k0 : P.k0 < S.NK
  minus : ∀ t < P.qs.length, P.minus t < S.NK

/-- The system's own images are compatible when the Σ states are grid states (the
predicate is satisfiable). -/
theorem compat_self (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP) (hk0 : P.k0 < S.NK)
    (hmin : ∀ t < P.qs.length, P.minus t < S.NK) :
    Compat S EPs Z P (S.bs EPs) (S.gl P) (S.st P) :=
  ⟨fun _ _ => rfl, rfl, rfl, hk0, hmin⟩

/-- `Espec` reads only the blocks' Inputs. -/
theorem Espec_inp {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ) (bs' : ℕ → EpsBlock κ')
    (h : ∀ iq ∉ Z, (bs iq).inp = (bs' iq).inp) : Espec Z E0 bs = Espec Z E0 bs' := by
  funext iq
  unfold Espec
  split_ifs with hz
  · rfl
  · rw [h iq hz]

/-- **The composed theorem for compatible data.** For ANY blocks `bs` and Σ data `gl`,
`st` compatible with one system `S`, BerkeleyGW's `SigA` with EpsSpec's screening of `bs`
equals the theory `SigT` of the system `S` (its orbitals, energies, occupations, cell and
theory RPA eps) plus `COR`, under the remaining named hypotheses of `sigA_common`. The
plans' index maps (`k + q`, `-k`, `k0 - q_t`, Σ's symmetry map) are trusted, and the
interaction `vc` is free. A block whose `neg` fixes `k0`, with a nonzero vector in the
sphere at `k0`, does not satisfy `MF.TR` (`compat_selfpaired_no_TR`). Since `Z` is
finite, the hypotheses are unsatisfiable if every block outside `Z` fixes `k0` in this way
(`hyps_unsat_of_selfpaired`), or, for arbitrary plans, if no grid index stores the negated
sphere list of `k0` (`hnp`, `hyps_unsat_of_unpaired`). For X or L of O1 the first premise
follows from the trusted plan semantics (`neg` encodes `-k`) on a grid that stores `k0`
once; storing `k0` once does not by itself give either premise. Under either premise this
theorem cannot be applied for O1. -/
theorem sigA_compat {κ : Type*} [Fintype κ] [DecidableEq κ] (S : MF) (EPs : ℕ → EP)
    (P : SP) (Z : Finset ℕ) (E0 : ℕ → ℕ → ℕ → ℝ) (bs : ℕ → EpsBlock κ) (gl : Gl) (st : St)
    (hc : Compat S EPs Z P bs gl st)
    (vb oq vc : V3 → ℝ) (a iw : ℕ) (hS : S.WF) (hP : ∀ iq ∉ Z, (EPs iq).WF S)
    (hT : ∀ iq ∉ Z, S.TR (EPs iq))
    (hq : ∀ iq ∉ Z, ∀ i : Fin (S.inp (EPs iq)).Gs.length,
      qG2 (S.inp (EPs iq)) (gsI (S.inp (EPs iq)) i) ≠ 0)
    (hC : ∀ k, vb k = vc k)
    (hWq : ∀ t < (S.gl P).qs.length, ((S.gl P).qs.getD t default).qh ≠ 0 →
      oq ((S.gl P).qs.getD t default).qh * qlen (S.gl P) ((S.gl P).qs.getD t default) /
          (8 * Real.pi) = 1 ∧
      oq ((S.gl P).qs.getD t default).qh / (vb (key ((S.gl P).qs.getD t default)
        (gs ((S.gl P).qs.getD t default) 0)) * qlen (S.gl P) ((S.gl P).qs.getD t default)) = 1)
    (hZ : ∀ t < (S.gl P).qs.length, ((S.gl P).qs.getD t default).qh = 0 →
      ZeroAt ((S.gl P).qs.getD t default))
    (hX : ∀ t < (S.gl P).qs.length, ∀ n1 < nbq (S.st P) t,
      TZ ≤ |xT (S.gl P) (S.st P) t a n1 iw|)
    (hM : ∀ t < (S.gl P).qs.length, ∀ n1 < nbq (S.st P) t, ∀ j < nG (S.gl P) t,
      ∀ i < nG (S.gl P) t, ¬ Wing ((S.gl P).qs.getD t default) j i →
      ModeOK (decide (n1 < (S.gl P).nocc)) (ITq (S.gl P) (Etheory Z E0 (S.bs EPs)) t j i)
        (OTq (S.gl P) vb t j i) (xT (S.gl P) (S.st P) t a n1 iw)) :
    SigA gl (Espec Z E0 bs) vb oq st a iw =
      SigT (S.gl P) (Etheory Z E0 (S.bs EPs)) vc (S.st P) a iw +
        COR (S.gl P) (Etheory Z E0 (S.bs EPs)) vb oq (S.st P) a := by
  obtain ⟨he, rfl, rfl, -, -⟩ := hc
  rw [Espec_inp Z E0 bs (S.bs EPs) he]
  exact sigA_common S EPs P Z E0 vb oq vc a iw hS hP hT hq hC hWq hZ hX hM

/-! ### The predicate is not satisfiable by unrelated data -/

/-- The eps Input of one block pins the system's grid: its size, and at every grid point
the sphere, all coefficient rows and all energies (with `plus` onto the grid). -/
theorem inp_pins (S S' : MF) (E : EP) (h : S.inp E = S'.inp E)
    (hsurj : ∀ k < S.NK, ∃ t < S.NK, E.plus t = k) :
    S.NK = S'.NK ∧ ∀ k < S.NK, S.G k = S'.G k ∧ S.c k = S'.c k ∧ S.e k = S'.e k := by
  have hNK : S.NK = S'.NK := by
    have := congrArg (fun i => i.ks.length) h
    simpa only [MF.ks_length] using this
  have hp : ∀ t < S.NK, S.kpair E t = S'.kpair E t := by
    intro t ht
    rw [← S.ks_getD E ht, ← S'.ks_getD E (hNK ▸ ht), h]
  refine ⟨hNK, fun k hk => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hsurj k hk
  have h1 := hp t ht
  have h2 := hp (E.plus t) hk
  simp only [MF.kpair, KPair.mk.injEq] at h1 h2
  obtain ⟨hG, hcv, hev, -, -, -⟩ := h1
  obtain ⟨-, -, -, -, hcc, hec⟩ := h2
  refine ⟨hG, ?_, ?_⟩
  · rw [← List.take_append_drop S.nocc (S.c _), hcv, hcc, List.take_append_drop]
  · rw [← List.take_append_drop S.nocc (S.e _), hev, hec, List.take_append_drop]

/-- **Given the screening blocks, at most one `st` is compatible, for every system.** If
`st` and `st'` are compatible with the same `bs` (through any two systems `S`, `S'` and
the same plans), then `st = st'`: one grid `q ≠ 0` block pins every sphere, coefficient
row and energy of the grid, and `st` reads only those. -/
theorem compat_st_unique {κ : Type*} (S S' : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP)
    (bs : ℕ → EpsBlock κ) (gl : Gl) (st st' : St)
    (h : Compat S EPs Z P bs gl st) (h' : Compat S' EPs Z P bs gl st')
    (iq : ℕ) (hiq : iq ∉ Z) (hsurj : ∀ k < S.NK, ∃ t < S.NK, (EPs iq).plus t = k) :
    st = st' := by
  have hi : S.inp (EPs iq) = S'.inp (EPs iq) := by rw [← h.eps iq hiq, h'.eps iq hiq]
  obtain ⟨-, hk⟩ := inp_pins S S' (EPs iq) hi hsurj
  rw [h.sta, h'.sta]
  obtain ⟨g0, c0, e0⟩ := hk _ h.k0
  simp only [MF.st, g0, c0, e0, St.mk.injEq, true_and]
  apply List.map_congr_left
  intro t ht
  obtain ⟨g1, c1, e1⟩ := hk _ (h.minus t (List.mem_range.mp ht))
  rw [g1, c1, e1]

theorem map_succ_ne {l : List ℤ} (hl : l ≠ []) : l.map (· + 1) ≠ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => intro h; simp only [List.map_cons, List.cons.injEq] at h; omega

/-- **The reviewer's adversarial case, as a theorem.** Keep the screening blocks `bs` and
`gl` of compatible data fixed and change the Σ state energies (`Ek ↦ Ek + 1`, in units
of `2^-SEn` Ry; any change works the same way). Then NO system makes the new data
compatible under the same plans `EPs`, `Z`, `P`, given one block `iq` outside `Z` whose
`plus` is onto the grid (`hsurj`) and a nonempty multiplet (`hms : P.ms ≠ []`). (Under
different plans the shifted data can be compatible.) -/
theorem compat_energy_shift {κ : Type*} (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP)
    (bs : ℕ → EpsBlock κ) (gl : Gl) (st : St) (h : Compat S EPs Z P bs gl st)
    (iq : ℕ) (hiq : iq ∉ Z) (hsurj : ∀ k < S.NK, ∃ t < S.NK, (EPs iq).plus t = k)
    (hms : P.ms ≠ []) :
    ∀ S' : MF, ¬ Compat S' EPs Z P bs gl { st with Ek := st.Ek.map (· + 1) } := by
  intro S' h'
  have e := congrArg St.Ek (compat_st_unique S S' EPs Z P bs gl st _ h h' iq hiq hsurj)
  have hne : st.Ek ≠ [] := by
    rw [h.sta]; simp only [MF.st, ne_eq, List.map_eq_nil_iff]; exact hms
  exact map_succ_ne hne e.symm

/-! ### One interaction, one density -/

/-- **The same Coulomb interaction.** With the two encodings of the same `q`
(`qn / 2^SQ` in EpsSpec, `qh / 2` in SigmaSpec), EpsSpec's `v(q + G) = 8π/|q + G|²` of the
system's block is `vBareK` of the system's Σ data at the key `2(q + G)`: both are the bare
Coulomb interaction of the one cell `B`. -/
theorem coulomb_same (S : MF) (E : EP) (P : SP) (qd : QD)
    (h1 : dy E.SQ E.qn.1 = (qd.qh.1 : ℝ) / 2) (h2 : dy E.SQ E.qn.2.1 = (qd.qh.2.1 : ℝ) / 2)
    (h3 : dy E.SQ E.qn.2.2 = (qd.qh.2.2 : ℝ) / 2) (G : V3) :
    vC (S.inp E) G = vBareK (S.gl P) (key qd G) := by
  rw [vBareK_key]
  unfold vC qG2 dotB bd vec
  congr 2
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have hv : (![G.1 + dy (S.inp E).SQ (S.inp E).qn.1, G.2.1 + dy (S.inp E).SQ (S.inp E).qn.2.1,
      G.2.2 + dy (S.inp E).SQ (S.inp E).qn.2.2] : Fin 3 → ℝ) =
      ![(qd.qh.1 : ℝ) / 2 + G.1, (qd.qh.2.1 : ℝ) / 2 + G.2.1, (qd.qh.2.2 : ℝ) / 2 + G.2.2] := by
    simp only [MF.inp, h1, h2, h3]
    funext c; fin_cases c <;> simp [add_comm]
  rw [hv]
  rfl

/-- The density of the system's occupied orbitals,
`ρ(g) = (2/N_k) Σ_k Σ_{n < nocc} Σ_{G_i - G_j = g} c_n(k, G_i) c_n(k, G_j)` (real flavour,
spin 2; `ρ(0) = 2 nocc` for normalised rows). -/
noncomputable def MF.dens (S : MF) (g : V3) : ℝ :=
  2 / S.NK * ∑ k ∈ range S.NK, ∑ n ∈ range S.nocc,
    ∑ i ∈ range (S.G k).length, ∑ j ∈ range (S.G k).length,
      if (S.G k).getD i 0 - (S.G k).getD j 0 = g then
        dy S.SC (((S.c k).getD n []).getD i 0) * dy S.SC (((S.c k).getD n []).getD j 0)
      else 0

/-- **Named hypothesis (density).** The density list of the system is the density of its
own occupied orbitals (absent entries read `0`). NOT discharged on the Si-EPM run (RHO is
the unsymmetrised IBZ sum; `bgw/r28_f1/check.py`). -/
def MF.DensOK (S : MF) : Prop :=
  ∀ g, ((S.rho.find? (fun p => p.1 == g)).map (fun p => dy S.SR p.2)).getD 0 = S.dens g

/-- Under `DensOK`, the HL `Ω²` of `SigT` is built from the SAME system's density. -/
theorem omT_dens (S : MF) (hD : S.DensOK) (P : SP) (vc : V3 → ℝ) (qd : QD) (i j : ℕ) :
    OmT (S.gl P) vc qd i j = factW (S.gl P) * S.dens (gs qd i - gs qd j) *
      (if qd.qh = 0 ∧ gs qd i = 0 then (if gs qd j = 0 then 1 else 0)
       else vc (key qd (gs qd i)) / (8 * Real.pi) *
         dotB (S.gl P) (vec qd (gs qd j)) (vec qd (gs qd i))) := by
  unfold OmT
  rw [show (rhoF (S.gl P) (gs qd i - gs qd j)).getD 0 = S.dens (gs qd i - gs qd j) from
    hD _]

/-! ### Why `k0` and `minus` are fields of `Compat` (post-review R2) -/

/-- An index beyond the grid and beyond every `minus t`. -/
def kstar (S : MF) (P : SP) : ℕ := S.NK + 1 + ∑ t ∈ range P.qs.length, P.minus t

theorem minus_lt_kstar (S : MF) (P : SP) {t : ℕ} (ht : t < P.qs.length) :
    P.minus t < kstar S P := by
  have := Finset.single_le_sum (f := P.minus) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr ht)
  unfold kstar; omega

/-- `S` with the state at `k0` copied to the off-grid index `kstar`, carrying energies `L`. -/
def offgrid (S : MF) (P : SP) (L : List ℤ) : MF :=
  { S with
    G := fun k => if k = kstar S P then S.G P.k0 else S.G k
    c := fun k => if k = kstar S P then S.c P.k0 else S.c k
    e := fun k => if k = kstar S P then L else S.e k }

theorem offgrid_grid (S : MF) (P : SP) (L : List ℤ) {k : ℕ} (hk : k < S.NK) :
    (offgrid S P L).G k = S.G k ∧ (offgrid S P L).c k = S.c k ∧ (offgrid S P L).e k = S.e k := by
  have : k ≠ kstar S P := by unfold kstar; omega
  simp [offgrid, this]

theorem offgrid_inp (S : MF) (P : SP) (L : List ℤ) (E : EP)
    (hp : ∀ t < S.NK, E.plus t < S.NK) : (offgrid S P L).inp E = S.inp E := by
  simp only [MF.inp]
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht' := List.mem_range.mp ht
  obtain ⟨g1, c1, e1⟩ := offgrid_grid S P L ht'
  obtain ⟨g2, c2, e2⟩ := offgrid_grid S P L (hp t ht')
  simp only [MF.kpair]
  rw [g1, c1, e1, g2, c2, e2]
  rfl

/-- **The loophole the fields `k0`, `minus` close** (found in the post-fix review of
b580e80). Without them, the first three fields of `Compat` hold for the system's OWN
screening blocks and `gl` together with Σ state energies `L` chosen ARBITRARILY: a system
equal to `S` on the whole grid, with the `k0` state stored off the grid, and a plan with
that off-grid `k0`. Every system-side hypothesis (`WF`, `EP.WF`, `TR`) carries over. -/
theorem offgrid_loophole (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP) (L : List ℤ)
    (hS : S.WF) (hP : ∀ iq ∉ Z, (EPs iq).WF S) (hT : ∀ iq ∉ Z, S.TR (EPs iq)) :
    let S' := offgrid S P L
    let P' : SP := { P with k0 := kstar S P }
    (∀ iq ∉ Z, (S.bs EPs iq).inp = S'.inp (EPs iq)) ∧ S.gl P = S'.gl P' ∧
      ({ S.st P with Ek := P.ms.map (fun n => L.getD n 0) } : St) = S'.st P' ∧
      S'.NK = S.NK ∧ S.NK ≤ P'.k0 ∧
      S'.WF ∧ (∀ iq ∉ Z, (EPs iq).WF S') ∧ (∀ iq ∉ Z, S'.TR (EPs iq)) := by
  intro S' P'
  refine ⟨fun iq hiq => (offgrid_inp S P L (EPs iq) (hP iq hiq).plus_lt).symm, rfl, ?_, rfl,
    by simp [P', kstar]; omega, ⟨hS.occ, fun k hk => ?_, hS.om⟩,
    fun iq h => (let w := hP iq h; ⟨w.1, w.2, w.3, w.4⟩), fun iq h t ht => ?_⟩
  · simp only [MF.st, S', P', offgrid, if_pos rfl, St.mk.injEq, true_and, if_true]
    apply List.map_congr_left
    intro t ht
    have := minus_lt_kstar S P (List.mem_range.mp ht)
    simp [this.ne]
  · rw [(offgrid_grid S P L hk).2.1]; exact hS.rows k hk
  · have hn := (hP iq h).neg_lt t ht
    obtain ⟨a1, b1, c1⟩ := offgrid_grid S P L hn
    obtain ⟨a2, b2, c2⟩ := offgrid_grid S P L ht
    rw [a1, b1, c1, a2, b2, c2]; exact hT iq h t ht

/-! ### Where `MF.TR` can hold (post-review R2) -/

theorem v3_self_neg (a : V3) (h : a = -a) : a = 0 := by
  obtain ⟨x, y, z⟩ := a
  simp only [Prod.neg_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Prod.mk_eq_zero]
  exact ⟨by omega, by omega, by omega⟩

theorem list_self_neg (l : List V3) (h : l = l.map (fun x => -x)) : ∀ g ∈ l, g = 0 := by
  induction l with
  | nil => intro g hg; simp at hg
  | cons a as ih =>
    intro g hg
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact v3_self_neg _ h.1
    · exact ih h.2 g hg'

/-- **`MF.TR` at a self-paired grid point.** `TR` is an exact, ordered list identity
(no sphere permutation, no umklapp vector, no sign or multiplet rotation). At a grid
point that `neg` maps to itself, i.e. a time-reversal-invariant point such as Γ, X or L
when `neg` encodes `-k`, it forces every sphere vector to be `0`. -/
theorem MF.tr_fixed (S : MF) (P : EP) (hT : S.TR P) {t : ℕ} (ht : t < S.NK)
    (hfix : P.neg t = t) : ∀ g ∈ S.G t, g = 0 := by
  obtain ⟨hG, -, -⟩ := hT t ht
  rw [hfix] at hG
  exact list_self_neg _ hG

/-- **Consequence for the composed theorem.** If the Σ state's grid point `k0` is
self-paired under a block's `neg` and its sphere holds a nonzero vector (any physical
sphere does), that block cannot satisfy `MF.TR`. This rules out only the blocks whose `neg`
fixes `k0`. Since `hT` must hold for infinitely many blocks (`Z` is finite), `sigA_compat`
cannot be applied at all if every block outside `Z` fixes `k0` (`hyps_unsat_of_selfpaired`),
or, for arbitrary plans, under `hnp` (`hyps_unsat_of_unpaired`). The O1 states X and L are
time-reversal-invariant, so when every plan's `neg` encodes `-k` (a trusted plan premise,
not formalised) on a grid that stores `k0` once, every block fixes `k0` and the
common-system composition derives nothing for O1. A `TR` with a sphere permutation, an
umklapp vector and an orthogonal rotation within degenerate multiplets at self-paired
points would remove this restriction; it is not formalized. -/
theorem compat_selfpaired_no_TR {κ : Type*} (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) (P : SP)
    (bs : ℕ → EpsBlock κ) (gl : Gl) (st : St) (h : Compat S EPs Z P bs gl st) (iq : ℕ)
    (hfix : (EPs iq).neg P.k0 = P.k0) {g : V3} (hg : g ∈ S.G P.k0) (hg0 : g ≠ 0) :
    ¬ S.TR (EPs iq) :=
  fun hT => hg0 (S.tr_fixed (EPs iq) hT h.k0 hfix g hg)

/-- **The hypotheses of `sigA_common` / `sigA_compat` are unsatisfiable on a grid where some
point's negated sphere is stored nowhere.** `Z` is a `Finset`, so `hP` and `hT` cover
infinitely many block indices, and at least one plan must satisfy `MF.TR` at every grid
point. If no grid index stores the negated sphere list of a grid point `k`, no plan does.
The theorem below therefore takes the absence of a stored negated sphere as the explicit
hypothesis `hnp`; it does **not** infer it from uniqueness of a stored k-point, because a
finite cutoff sphere does not determine k modulo the reciprocal lattice. For a concrete
X/L/Γ application, `hnp` must be established from the actual grid/sphere data (or from a
stronger coordinate-aware time-reversal model). Separately, `compat_selfpaired_no_TR`
gives the direct `MF.tr_fixed` obstruction, but only for a block whose `neg` fixes a grid
point with a nonzero sphere vector; a single such block can be put into `Z`. When EVERY
block outside `Z` fixes that point (as when every plan's `neg` encodes `-k` at a
time-reversal-invariant point stored once), `hyps_unsat_of_selfpaired` gives
unsatisfiability without `hnp`. Thus any O1 non-applicability claim must cite one of those
two premises (`hnp`, or every block outside `Z` fixing `k0`), not sphere uniqueness. Under
either premise, putting finitely many blocks into `Z` does not help. (Restricting `hP`,
`hT`, `hq` to the blocks the Σ q-list reads would make "every
read block an input" possible, but nothing would then be derived for O1 either.) -/
theorem hyps_unsat_of_unpaired (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) {k : ℕ}
    (hk : k < S.NK) (hnp : ∀ j < S.NK, S.G j ≠ (S.G k).map (fun g => -g))
    (hP : ∀ iq ∉ Z, (EPs iq).WF S) (hT : ∀ iq ∉ Z, S.TR (EPs iq)) : False := by
  obtain ⟨iq, hiq⟩ := Infinite.exists_not_mem_finset Z
  obtain ⟨hG, -, -⟩ := hT iq hiq k hk
  exact hnp _ ((hP iq hiq).neg_lt k hk) hG

/-- **The hypotheses are unsatisfiable when every block outside `Z` fixes a grid point with
a nonzero sphere vector.** If the `neg` of every plan outside the finite `Z` fixes the grid
point `k` and the sphere at `k` holds a nonzero vector, then `hT` fails: `Z` is a
`Finset`, so some block lies outside it, and `MF.tr_fixed` forces its sphere at `k` to be
`0`. No `hnp` and no `EP.WF` are needed; the premise is about the plans, not the sphere
data. For X or L of O1 it follows from the trusted, unformalised plan semantics (`neg`
encodes `-k`) on a grid that stores `k` once; `MF` carries no k-coordinates, so that step
is not a theorem. -/
theorem hyps_unsat_of_selfpaired (S : MF) (EPs : ℕ → EP) (Z : Finset ℕ) {k : ℕ}
    (hk : k < S.NK) (hfix : ∀ iq ∉ Z, (EPs iq).neg k = k) {g : V3} (hg : g ∈ S.G k)
    (hg0 : g ≠ 0) (hT : ∀ iq ∉ Z, S.TR (EPs iq)) : False := by
  obtain ⟨iq, hiq⟩ := Infinite.exists_not_mem_finset Z
  exact hg0 (S.tr_fixed (EPs iq) (hT iq hiq) hk (hfix iq hiq) g hg)

end GW.Bridge.Common

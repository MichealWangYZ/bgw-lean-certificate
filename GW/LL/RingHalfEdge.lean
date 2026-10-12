/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C2A section 3.3: an explicit half-edge (flag) model for the RING FAMILY
ONLY, and the proof that the compressed automorphism computation of
`GW.LL.Aut (ring k)` is faithful to it on that family.

WHY THIS FILE IS DELIBERATELY NARROW. `GW.LL.selfLoopWitness` shows the
compressed site/edge representation is NOT faithful to half-edge symmetries in
general: a self-loop's two incidences can be exchanged invisibly. This model
therefore covers the ring family and nothing else. It is not a general Feynman
diagram framework, it does not support tadpoles, Wick contractions or skeleton
decomposition, and no general faithfulness is claimed.

WHAT MAKES IT MORE THAN A RESTATEMENT. Each edge here carries TWO flags, one
per endpoint, as separate inhabitants of `RingFlag`. Exchanging the two flags
of a single edge is expressible; it is ruled out by the site-map condition
rather than by the encoding, and that is exactly the freedom the compressed
model cannot express.
-/
import GW.LL.StructuralRing

namespace GW.LL

open FeynDiagram

/-- A half-edge of `ring k`.

* `extProp s` — the external propagator's flag at `extI` (`s = false`) or
  `extJ` (`s = true`);
* `bub m c s` — copy `c` of bubble `m`'s propagator, at `a_m` (`s = false`) or
  `b_m` (`s = true`);
* `int e s` — interaction edge `e`, at its `I`-side (`s = false`) or `J`-side.
-/
inductive RingFlag (k : ℕ) where
  | extProp : Bool → RingFlag k
  | bub : Fin k → Bool → Bool → RingFlag k
  | int : Fin (k + 1) → Bool → RingFlag k
deriving DecidableEq, Fintype

namespace RingFlag

variable {k : ℕ}

/-- The other flag of the same edge. An involution with no fixed point: every
edge really does have two distinct flags. -/
def mate : RingFlag k → RingFlag k
  | .extProp s => .extProp !s
  | .bub m c s => .bub m c !s
  | .int e s => .int e !s

@[simp] theorem mate_mate (f : RingFlag k) : f.mate.mate = f := by
  cases f <;> simp [mate]

theorem mate_ne (f : RingFlag k) : f.mate ≠ f := by
  cases f <;> simp [mate]

/-- Whether the flag belongs to a propagator. -/
def isProp : RingFlag k → Bool
  | .extProp _ => true
  | .bub _ _ _ => true
  | .int _ _ => false

@[simp] theorem isProp_mate (f : RingFlag k) : f.mate.isProp = f.isProp := by
  cases f <;> simp [mate, isProp]

end RingFlag

/-- The endpoints of interaction edge `e`: its `I`-side is `extI` for `e = 0`
and `b_{e-1}` otherwise; its `J`-side is `a_e` for `e < k` and `extJ` for
`e = k`. This is the chain of `ringInts`. -/
def intSite {k : ℕ} (e : Fin (k + 1)) (s : Bool) : Site (2 * k) :=
  if s then (if h : e.val < k then aS ⟨e.val, h⟩ else .extJ)
  else (if h : 0 < e.val then bS ⟨e.val - 1, by omega⟩ else .extI)

/-- The site a flag is attached to. -/
def RingFlag.site {k : ℕ} : RingFlag k → Site (2 * k)
  | .extProp s => if s then .extJ else .extI
  | .bub m _ s => if s then bS m else aS m
  | .int e s => intSite e s

/-- A half-edge automorphism of `ring k`: a permutation of the flags that
preserves edges (commutes with `mate`), preserves edge kind, and induces a site
relabeling fixing both external labels.

Note what is NOT assumed: nothing prevents `ψ` from exchanging the two flags of
one edge. That is excluded by `siteMap` together with the fact that a ring
propagator joins two DISTINCT sites, which is where `ring_no_self_loop` enters. -/
def IsFlagAut (k : ℕ) (ψ : Equiv.Perm (RingFlag k))
    (σ : Equiv.Perm (Site (2 * k))) : Prop :=
  (∀ f, ψ f.mate = (ψ f).mate) ∧ (∀ f, (ψ f).isProp = f.isProp)
    ∧ (∀ f, (ψ f).site = σ f.site)
    ∧ σ .extI = .extI ∧ σ .extJ = .extJ

/-- The half-edge automorphism group of `ring k`. -/
def RingHalfEdgeAut (k : ℕ) : Type :=
  {p : Equiv.Perm (RingFlag k) × Equiv.Perm (Site (2 * k)) // IsFlagAut k p.1 p.2}

/-- Decidability is genuine here, not inherited from the correspondence: the
conditions are finite conjunctions of decidable equalities over finite types.
So `Fintype.card (RingHalfEdgeAut k)` below is an independent count, not a
restatement of the equivalence. -/
instance instDecIsFlagAut (k : ℕ) : DecidablePred
    (fun p : Equiv.Perm (RingFlag k) × Equiv.Perm (Site (2 * k)) =>
      IsFlagAut k p.1 p.2) := fun p => by
  unfold IsFlagAut
  infer_instance

instance instFintypeRingHalfEdgeAut (k : ℕ) : Fintype (RingHalfEdgeAut k) :=
  Subtype.fintype _

/-! ### Which flags sit at which site -/

section Inversion

variable {k : ℕ}

@[simp] theorem site_extProp_false : (RingFlag.extProp false : RingFlag k).site
    = (.extI : Site (2 * k)) := rfl

@[simp] theorem site_extProp_true : (RingFlag.extProp true : RingFlag k).site
    = (.extJ : Site (2 * k)) := rfl

@[simp] theorem site_bub_false (m : Fin k) (c : Bool) :
    (RingFlag.bub m c false).site = aS m := rfl

@[simp] theorem site_bub_true (m : Fin k) (c : Bool) :
    (RingFlag.bub m c true).site = bS m := rfl

theorem site_int_zero_false : (RingFlag.int (0 : Fin (k + 1)) false).site
    = (.extI : Site (2 * k)) := by
  simp [RingFlag.site, intSite]

theorem site_int_true_of_lt (e : Fin (k + 1)) (h : e.val < k) :
    (RingFlag.int e true).site = aS ⟨e.val, h⟩ := by
  simp [RingFlag.site, intSite, dif_pos h]

theorem site_int_false_of_pos (e : Fin (k + 1)) (h : 0 < e.val) :
    (RingFlag.int e false).site = bS ⟨e.val - 1, by omega⟩ := by
  simp [RingFlag.site, intSite, h]

/-- Only the `I`-side of interaction edge 0 sits at `extI`, among interaction
flags. -/
theorem int_at_extI {e : Fin (k + 1)} {s : Bool}
    (h : (RingFlag.int e s).site = (.extI : Site (2 * k))) : e.val = 0 ∧ s = false := by
  cases s
  · by_cases hp : 0 < e.val
    · rw [site_int_false_of_pos e hp] at h
      exact absurd h (bS_ne_extI _)
    · exact ⟨by omega, rfl⟩
  · by_cases hl : e.val < k
    · rw [site_int_true_of_lt e hl] at h
      exact absurd h (aS_ne_extI _)
    · rw [RingFlag.site, intSite, if_pos rfl, dif_neg hl] at h
      exact absurd h extI_ne_extJ.symm

/-- Only the `I`-side of interaction edge `m+1` sits at `b_m`. -/
theorem int_at_bS {e : Fin (k + 1)} {s : Bool} {m : Fin k}
    (h : (RingFlag.int e s).site = bS m) : e.val = m.val + 1 ∧ s = false := by
  cases s
  · by_cases hp : 0 < e.val
    · rw [site_int_false_of_pos e hp] at h
      refine ⟨?_, rfl⟩
      have := bS_inj h
      have : e.val - 1 = m.val := congrArg Fin.val this
      omega
    · rw [RingFlag.site, intSite, if_neg (by simp), dif_neg (by omega)] at h
      exact absurd h.symm (bS_ne_extI m)
  · by_cases hl : e.val < k
    · rw [site_int_true_of_lt e hl] at h
      exact absurd h (aS_ne_bS _ m)
    · rw [RingFlag.site, intSite, if_pos rfl, dif_neg hl] at h
      exact absurd h.symm (bS_ne_extJ m)

/-- Only the `J`-side of interaction edge `m` sits at `a_m`. -/
theorem int_at_aS {e : Fin (k + 1)} {s : Bool} {m : Fin k}
    (h : (RingFlag.int e s).site = aS m) : e.val = m.val ∧ s = true := by
  cases s
  · by_cases hp : 0 < e.val
    · rw [site_int_false_of_pos e hp] at h
      exact absurd h (aS_ne_bS m _).symm
    · rw [RingFlag.site, intSite, if_neg (by simp), dif_neg (by omega)] at h
      exact absurd h.symm (aS_ne_extI m)
  · by_cases hl : e.val < k
    · rw [site_int_true_of_lt e hl] at h
      refine ⟨?_, rfl⟩
      have := aS_inj h
      exact congrArg Fin.val this
    · rw [RingFlag.site, intSite, if_pos rfl, dif_neg hl] at h
      exact absurd h.symm (aS_ne_extJ m)

/-- A propagator flag at `a_m` is a copy of bubble `m`, on its `a` side. -/
theorem prop_at_aS {f : RingFlag k} (hp : f.isProp = true) {m : Fin k}
    (h : f.site = aS m) : ∃ c, f = .bub m c false := by
  cases f with
  | extProp s =>
      cases s
      · exact absurd h.symm (aS_ne_extI m)
      · exact absurd h.symm (aS_ne_extJ m)
  | bub m' c s =>
      cases s
      · obtain rfl := aS_inj h
        exact ⟨c, rfl⟩
      · simp only [site_bub_true] at h
        exact absurd h (aS_ne_bS m m').symm
  | int e s => exact absurd hp (by simp [RingFlag.isProp])

/-- A propagator flag at `extI` is the external propagator's `I`-side. -/
theorem prop_at_extI {f : RingFlag k} (hp : f.isProp = true)
    (h : f.site = (.extI : Site (2 * k))) : f = .extProp false := by
  cases f with
  | extProp s =>
      cases s
      · rfl
      · exact absurd h extI_ne_extJ.symm
  | bub m c s =>
      cases s
      · exact absurd h (aS_ne_extI m)
      · exact absurd h (bS_ne_extI m)
  | int e s => exact absurd hp (by simp [RingFlag.isProp])

end Inversion

/-! ### Rigidity in the half-edge model -/

section Rigid

variable {k : ℕ} {ψ : Equiv.Perm (RingFlag k)} {σ : Equiv.Perm (Site (2 * k))}

theorem isProp_false_iff {f : RingFlag k} :
    f.isProp = false ↔ ∃ e s, f = .int e s := by
  cases f <;> simp [RingFlag.isProp]

/-- Walking the interaction chain: every interaction flag on the `I` side is
fixed. The step alternates between an interaction edge and a bubble, exactly as
in the compressed model. -/
theorem flagAut_chain (h : IsFlagAut k ψ σ) :
    ∀ (t : ℕ) (ht : t < k + 1), ψ (.int ⟨t, ht⟩ false) = .int ⟨t, ht⟩ false := by
  intro t
  induction t with
  | zero =>
      intro ht
      have hk : (ψ (.int ⟨0, ht⟩ false)).isProp = false := by
        rw [h.2.1]; simp [RingFlag.isProp]
      obtain ⟨e, s, hes⟩ := isProp_false_iff.mp hk
      have hsite : (RingFlag.int e s).site = (.extI : Site (2 * k)) := by
        rw [← hes, h.2.2.1]
        have : (RingFlag.int (⟨0, ht⟩ : Fin (k + 1)) false).site
            = (.extI : Site (2 * k)) := by
          simpa using site_int_zero_false (k := k)
        rw [this, h.2.2.2.1]
      obtain ⟨he0, rfl⟩ := int_at_extI hsite
      rw [hes]
      congr 1
      exact Fin.ext (by simp [he0])
  | succ t iht =>
      intro ht
      have htk : t < k := by omega
      have htt : t < k + 1 := by omega
      -- the previous interaction edge is fixed, hence so is its `J` side
      have hprev := iht htt
      have hmate : ψ (.int ⟨t, htt⟩ true) = .int ⟨t, htt⟩ true := by
        have := h.1 (.int ⟨t, htt⟩ false)
        simpa [RingFlag.mate, hprev] using this
      -- so `a_t` is fixed
      have haS : σ (aS ⟨t, htk⟩) = aS ⟨t, htk⟩ := by
        have hs := h.2.2.1 (.int ⟨t, htt⟩ true)
        rw [hmate, site_int_true_of_lt ⟨t, htt⟩ htk] at hs
        simpa using hs.symm
      -- the bubble at `t` maps to itself, so `b_t` is fixed
      have hbub : ∃ c, ψ (.bub ⟨t, htk⟩ false false) = .bub ⟨t, htk⟩ c false := by
        refine prop_at_aS ?_ ?_
        · rw [h.2.1]; simp [RingFlag.isProp]
        · rw [h.2.2.1]; simpa using haS
      obtain ⟨c, hc⟩ := hbub
      have hbS : σ (bS ⟨t, htk⟩) = bS ⟨t, htk⟩ := by
        have hm := h.1 (.bub ⟨t, htk⟩ false false)
        rw [hc] at hm
        have hs := h.2.2.1 (.bub ⟨t, htk⟩ false true)
        rw [show (RingFlag.bub (⟨t, htk⟩ : Fin k) false true)
            = (RingFlag.bub (⟨t, htk⟩ : Fin k) false false).mate from rfl, hm] at hs
        simpa [RingFlag.mate] using hs.symm
      -- hence the next interaction edge is fixed
      have hk2 : (ψ (.int ⟨t + 1, ht⟩ false)).isProp = false := by
        rw [h.2.1]; simp [RingFlag.isProp]
      obtain ⟨e, s, hes⟩ := isProp_false_iff.mp hk2
      have hsite : (RingFlag.int e s).site = bS ⟨t, htk⟩ := by
        rw [← hes, h.2.2.1, site_int_false_of_pos ⟨t + 1, ht⟩ (by simp)]
        have : (⟨(⟨t + 1, ht⟩ : Fin (k + 1)).val - 1, by simp; omega⟩ : Fin k)
            = ⟨t, htk⟩ := Fin.ext (by simp)
        rw [this, hbS]
      obtain ⟨he, rfl⟩ := int_at_bS hsite
      rw [hes]
      congr 1
      exact Fin.ext (by simp [he])

/-- Both sites of every bubble are fixed. -/
theorem flagAut_sites (h : IsFlagAut k ψ σ) (m : Fin k) :
    σ (aS m) = aS m ∧ σ (bS m) = bS m := by
  have htt : m.val < k + 1 := by omega
  have hprev := flagAut_chain h m.val htt
  have hmate : ψ (.int ⟨m.val, htt⟩ true) = .int ⟨m.val, htt⟩ true := by
    have := h.1 (.int ⟨m.val, htt⟩ false)
    simpa [RingFlag.mate, hprev] using this
  have haS : σ (aS m) = aS m := by
    have hs := h.2.2.1 (.int ⟨m.val, htt⟩ true)
    rw [hmate, site_int_true_of_lt ⟨m.val, htt⟩ m.isLt] at hs
    have hfin : (⟨(⟨m.val, htt⟩ : Fin (k + 1)).val, m.isLt⟩ : Fin k) = m := Fin.ext rfl
    rw [hfin] at hs
    exact hs.symm
  refine ⟨haS, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, ψ (.bub m false false) = .bub m c false := by
    refine prop_at_aS ?_ ?_
    · rw [h.2.1]; simp [RingFlag.isProp]
    · rw [h.2.2.1]; simpa using haS
  have hm := h.1 (.bub m false false)
  rw [hc] at hm
  have hs := h.2.2.1 (.bub m false true)
  rw [show (RingFlag.bub m false true) = (RingFlag.bub m false false).mate from rfl,
    hm] at hs
  simpa [RingFlag.mate] using hs.symm

/-- The induced site relabeling of a half-edge automorphism is the identity --
the same conclusion as in the compressed model, proved independently here. -/
theorem flagAut_sigma_eq_one (h : IsFlagAut k ψ σ) : σ = 1 := by
  apply Equiv.ext
  intro s
  match s with
  | .extI => exact h.2.2.2.1
  | .extJ => exact h.2.2.2.2
  | .int q =>
      obtain ⟨m, hm | hm⟩ := site_cases q
      · rw [hm]; exact (flagAut_sites h m).1
      · rw [hm]; exact (flagAut_sites h m).2

/-- Interaction flags are all fixed. -/
theorem flagAut_fixes_int (h : IsFlagAut k ψ σ) (e : Fin (k + 1)) (s : Bool) :
    ψ (.int e s) = .int e s := by
  have h0 : ψ (.int e false) = .int e false := by
    have := flagAut_chain h e.val e.isLt
    have hfin : (⟨e.val, e.isLt⟩ : Fin (k + 1)) = e := Fin.ext rfl
    rwa [hfin] at this
  cases s
  · exact h0
  · have := h.1 (.int e false)
    simpa [RingFlag.mate, h0] using this

/-- The external propagator's flags are fixed. -/
theorem flagAut_fixes_extProp (h : IsFlagAut k ψ σ) (s : Bool) :
    ψ (.extProp s) = .extProp s := by
  have h0 : ψ (.extProp false) = .extProp false := by
    refine prop_at_extI ?_ ?_
    · rw [h.2.1]; simp [RingFlag.isProp]
    · rw [h.2.2.1]
      simpa using h.2.2.2.1
  cases s
  · exact h0
  · have := h.1 (.extProp false)
    simpa [RingFlag.mate, h0] using this

/-- The bit of bubble `m`: does the automorphism exchange its two copies? -/
def flagBits (h : IsFlagAut k ψ σ) : Fin k → Bool :=
  fun m => decide (ψ (.bub m false false) = .bub m true false)

theorem flagAut_bub_false (h : IsFlagAut k ψ σ) (m : Fin k) (c : Bool) :
    ψ (.bub m c false) = .bub m (xor c (flagBits h m)) false := by
  obtain ⟨c0, h0⟩ : ∃ c0, ψ (.bub m false false) = .bub m c0 false := by
    refine prop_at_aS ?_ ?_
    · rw [h.2.1]; simp [RingFlag.isProp]
    · rw [h.2.2.1]
      have := (flagAut_sites h m).1
      simpa using this
  obtain ⟨c1, h1⟩ : ∃ c1, ψ (.bub m true false) = .bub m c1 false := by
    refine prop_at_aS ?_ ?_
    · rw [h.2.1]; simp [RingFlag.isProp]
    · rw [h.2.2.1]
      have := (flagAut_sites h m).1
      simpa using this
  have hne : c1 ≠ c0 := by
    intro hc
    rw [hc] at h1
    have := ψ.injective (h1.trans h0.symm)
    simp at this
  have hbits : flagBits h m = c0 := by
    simp only [flagBits, h0]
    cases c0 <;> simp
  cases c
  · rw [h0, hbits]; cases c0 <;> simp
  · rw [h1, hbits]
    cases c0 <;> cases c1 <;> simp_all

theorem flagAut_bub (h : IsFlagAut k ψ σ) (m : Fin k) (c s : Bool) :
    ψ (.bub m c s) = .bub m (xor c (flagBits h m)) s := by
  cases s
  · exact flagAut_bub_false h m c
  · have := h.1 (.bub m c false)
    rw [flagAut_bub_false h m c] at this
    simpa [RingFlag.mate] using this

end Rigid

/-! ### Both models are the same bubble bits, hence the same group -/

/-- Exchange the two copies of every bubble whose bit is set; fix every other
flag. Written as an explicit involution. -/
def flagFlip {k : ℕ} (bits : Fin k → Bool) : RingFlag k → RingFlag k
  | .extProp s => .extProp s
  | .bub m c s => .bub m (xor c (bits m)) s
  | .int e s => .int e s

theorem flagFlip_involutive {k : ℕ} (bits : Fin k → Bool) :
    Function.Involutive (flagFlip bits) := by
  intro f
  cases f with
  | extProp s => rfl
  | bub m c s => simp [flagFlip, Bool.xor_assoc]
  | int e s => rfl

/-- The half-edge automorphism selected by a bit vector. -/
def flagPerm {k : ℕ} (bits : Fin k → Bool) : Equiv.Perm (RingFlag k) :=
  (flagFlip_involutive bits).toPerm _

@[simp] theorem flagPerm_apply {k : ℕ} (bits : Fin k → Bool) (f : RingFlag k) :
    flagPerm bits f = flagFlip bits f := rfl

/-- Exchanging bubble copies really is a half-edge automorphism: the site of a
flag does not depend on WHICH copy it belongs to, only on the bubble and the
side. -/
theorem isFlagAut_flagPerm {k : ℕ} (bits : Fin k → Bool) :
    IsFlagAut k (flagPerm bits) 1 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro f; cases f with
    | extProp s => rfl
    | bub m c s => rfl
    | int e s => rfl
  · intro f; cases f with
    | extProp s => rfl
    | bub m c s => rfl
    | int e s => rfl
  · intro f; cases f with
    | extProp s => rfl
    | bub m c s => rfl
    | int e s => rfl

/-- **Both models are classified by the same bubble bits.** -/
def ringHalfEdgeEquivBits (k : ℕ) : RingHalfEdgeAut k ≃ (Fin k → Bool) where
  toFun a := flagBits a.2
  invFun bits := ⟨(flagPerm bits, 1), isFlagAut_flagPerm bits⟩
  left_inv a := by
    obtain ⟨⟨ψ, σ⟩, ha⟩ := a
    refine Subtype.ext (Prod.ext ?_ (flagAut_sigma_eq_one ha).symm)
    refine Equiv.ext fun f => ?_
    show flagFlip (flagBits ha) f = ψ f
    cases f with
    | extProp s => rw [flagAut_fixes_extProp ha s]; rfl
    | bub m c s => rw [flagAut_bub ha m c s]; rfl
    | int e s => rw [flagAut_fixes_int ha e s]; rfl
  right_inv bits := by
    funext m
    show decide (flagPerm bits (.bub m false false) = .bub m true false) = bits m
    rw [flagPerm_apply]
    cases hb : bits m <;> simp [flagFlip, hb]

/-- **Ring-specific fidelity.** For the arbitrary finite ring family, the
compressed automorphism computation is faithful to the ring's explicit
half-edge symmetries.

This is asserted for the RING FAMILY only. `GW.LL.selfLoopWitness` shows the
compressed representation is not faithful in general, and this file defines no
half-edge model outside the rings. -/
def ringHalfEdgeEquivAut (k : ℕ) : RingHalfEdgeAut k ≃ Aut (ring k) :=
  (ringHalfEdgeEquivBits k).trans (autEquivBits k).symm

/-- The correspondence really does match bubble swaps to bubble swaps: the bit
read off a half-edge automorphism is the bit read off its compressed image. -/
theorem ringHalfEdgeEquivAut_bits (k : ℕ) (a : RingHalfEdgeAut k) :
    autBits (ringHalfEdgeEquivAut k a) = flagBits a.2 := by
  show autBits ((autEquivBits k).symm (ringHalfEdgeEquivBits k a)) = _
  rw [show autBits = (autEquivBits k).toFun from rfl]
  exact (autEquivBits k).apply_symm_apply _

/-- Consequently the half-edge symmetry factor is also `2 ^ k`. -/
theorem card_ringHalfEdgeAut (k : ℕ) :
    Fintype.card (RingHalfEdgeAut k) = 2 ^ k := by
  rw [Fintype.card_congr (ringHalfEdgeEquivBits k)]
  simp

end GW.LL

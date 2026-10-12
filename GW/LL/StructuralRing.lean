/-
LL-C2A: the arbitrary finite ring family of Lin-Lindsey Part I
(arXiv:1809.02900v1, PDF section 4.7.1, Fig. 4.11), as one structural
definition rather than three examples.

`ring k` has `k` bubbles, `k+1` interaction edges chaining the two fixed
external sites, one external propagator, and no self-loop. Internal sites are
interleaved: bubble `m` uses indices `2m` and `2m+1`. That choice is what makes
the induction work -- peeling the first two indices off an assignment leaves
exactly an assignment for `ring k`.

Nothing here uses `2^k` as an input. The symmetry factor is derived.
-/
import GW.LL.Ring

namespace GW.LL

open FeynDiagram

/-! ### Internal site indexing -/

/-- Site `a` of bubble `m`: internal index `2m`. -/
def aIdx {k : ℕ} (m : Fin k) : Fin (2 * k) := ⟨2 * m.val, by omega⟩

/-- Site `b` of bubble `m`: internal index `2m+1`. -/
def bIdx {k : ℕ} (m : Fin k) : Fin (2 * k) := ⟨2 * m.val + 1, by omega⟩

/-- `a` of bubble `m`, as a site. -/
def aS {k : ℕ} (m : Fin k) : Site (2 * k) := .int (aIdx m)

/-- `b` of bubble `m`, as a site. -/
def bS {k : ℕ} (m : Fin k) : Site (2 * k) := .int (bIdx m)

theorem aIdx_ne_bIdx {k : ℕ} (m m' : Fin k) : aIdx m ≠ bIdx m' := by
  simp only [aIdx, bIdx, Ne, Fin.mk.injEq]
  omega

theorem aIdx_inj {k : ℕ} {m m' : Fin k} (h : aIdx m = aIdx m') : m = m' := by
  simp only [aIdx, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem bIdx_inj {k : ℕ} {m m' : Fin k} (h : bIdx m = bIdx m') : m = m' := by
  simp only [bIdx, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

/-! ### The family, as data -/

/-- Propagators: the external one, then two parallel copies per bubble. -/
def ringProps (k : ℕ) : List (Site (2 * k) × Site (2 * k)) :=
  (.extI, .extJ) :: ((List.finRange k).flatMap fun m => [(aS m, bS m), (aS m, bS m)])

/-- Interaction edges: the chain `I - a₀`, `b₀ - a₁`, ..., `b_{k-1} - J`. -/
def ringInts : (k : ℕ) → List (Site (2 * k) × Site (2 * k))
  | 0 => [(.extI, .extJ)]
  | (k + 1) =>
      (.extI, aS (0 : Fin (k + 1))) ::
        (((List.finRange k).map fun m => (bS m.castSucc, aS m.succ))
          ++ [(bS (Fin.last k), .extJ)])

/-- The `k`-th ring diagram. -/
def ring (k : ℕ) : FeynDiagram where
  numInternal := 2 * k
  propagators := ringProps k
  interactions := ringInts k

/-! ### Agreement with the three C1 examples, as graph data -/

theorem ring_zero : ring 0 = ring0 := by rfl
theorem ring_one : ring 1 = ring1 := by rfl
theorem ring_two : ring 2 = ring2 := by rfl

/-! ### Index shifting: peeling bubble 0 off an assignment

`2 * (k+1)` reduces to `2 * k + 2`, so an assignment for `ring (k+1)` is
literally `Fin.cons a (Fin.cons b g)` for an assignment `g` of `ring k`. Under
that split, bubble `m+1` of `ring (k+1)` is bubble `m` of `ring k`. -/

/-- The general shift: index `t+2` of a two-element `Fin.cons` is index `t` of
the tail. Every specific bubble-shift below is this lemma plus an index
identity discharged by `omega`. -/
theorem cons_cons_at {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N)
    (t : ℕ) (h : t + 2 < 2 * (k + 1)) (h' : t < 2 * k) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) ⟨t + 2, h⟩
      = g ⟨t, h'⟩ := by
  have e1 : (⟨t + 2, h⟩ : Fin (2 * (k + 1)))
      = (⟨t + 1, by omega⟩ : Fin (2 * k + 1)).succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [e1, Fin.cons_succ]
  have e2 : (⟨t + 1, by omega⟩ : Fin (2 * k + 1))
      = (⟨t, h'⟩ : Fin (2 * k)).succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [e2, Fin.cons_succ]

/-- Any index of the big assignment that sits two above an index of the tail
reads the tail there. All bubble shifts are instances. -/
theorem cons_cons_idx {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N)
    (p : Fin (2 * (k + 1))) (q : Fin (2 * k)) (h : p.val = q.val + 2) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) p = g q := by
  have e : p = ⟨q.val + 2, by omega⟩ := Fin.ext h
  rw [e, cons_cons_at a b g q.val (by omega) q.isLt]

theorem cons_cons_aIdx_succ {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N)
    (m : Fin k) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) (aIdx m.succ)
      = g (aIdx m) := by
  have h : (aIdx m.succ : Fin (2 * (k + 1)))
      = (⟨2 * m.val + 1, by omega⟩ : Fin (2 * k + 1)).succ := by
    apply Fin.ext; simp [aIdx, Fin.val_succ]; omega
  rw [h, Fin.cons_succ]
  have h2 : (⟨2 * m.val + 1, by omega⟩ : Fin (2 * k + 1))
      = (⟨2 * m.val, by omega⟩ : Fin (2 * k)).succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [h2, Fin.cons_succ]
  rfl

theorem cons_cons_bIdx_succ {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N)
    (m : Fin k) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) (bIdx m.succ)
      = g (bIdx m) := by
  have h : (bIdx m.succ : Fin (2 * (k + 1)))
      = (⟨2 * m.val + 2, by omega⟩ : Fin (2 * k + 1)).succ := by
    apply Fin.ext; simp [bIdx, Fin.val_succ]; omega
  rw [h, Fin.cons_succ]
  have h2 : (⟨2 * m.val + 2, by omega⟩ : Fin (2 * k + 1))
      = (⟨2 * m.val + 1, by omega⟩ : Fin (2 * k)).succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [h2, Fin.cons_succ]
  rfl

theorem cons_cons_aIdx_zero {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N)
      (aIdx (0 : Fin (k + 1))) = a := by
  have h : (aIdx (0 : Fin (k + 1)) : Fin (2 * (k + 1))) = 0 := by
    apply Fin.ext; simp [aIdx]
  rw [h, Fin.cons_zero]

theorem cons_cons_bIdx_zero {k N : ℕ} (a b : Fin N) (g : Fin (2 * k) → Fin N) :
    (Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N)
      (bIdx (0 : Fin (k + 1))) = b := by
  have h : (bIdx (0 : Fin (k + 1)) : Fin (2 * (k + 1)))
      = (0 : Fin (2 * k + 1)).succ := by
    apply Fin.ext; simp [bIdx, Fin.val_succ]
  rw [h, Fin.cons_succ, Fin.cons_zero]

/-! ### Closed forms for the two edge products -/

section Products

variable {K : Type*} [CommRing K] {N : ℕ}

theorem edgeProd_ringProps (k : ℕ) (G : Matrix (Fin N) (Fin N) K) (i j : Fin N)
    (f : Fin (2 * k) → Fin N) :
    edgeProd G i j f (ringProps k)
      = G i j * ∏ m : Fin k, (G (f (aIdx m)) (f (bIdx m)) * G (f (aIdx m)) (f (bIdx m))) := by
  classical
  simp only [edgeProd, ringProps, List.map_cons, List.prod_cons, siteIndex,
    List.map_flatMap, Fin.prod_univ_def]
  congr 1
  induction (List.finRange k) with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons,
        List.map_nil, List.prod_nil, aS, bS, siteIndex] at *
      rw [ih]
      ring

/-- Closed form for the interaction chain at `k = 0`. -/
theorem edgeProd_ringInts_zero (v : Matrix (Fin N) (Fin N) K) (x y : Fin N)
    (f : Fin (2 * 0) → Fin N) : edgeProd v x y f (ringInts 0) = v x y := by
  simp [edgeProd, ringInts, siteIndex]

/-- Closed form for the interaction chain at `k+1`: head, middle product, tail. -/
theorem edgeProd_ringInts_succ (k : ℕ) (v : Matrix (Fin N) (Fin N) K)
    (x y : Fin N) (f : Fin (2 * (k + 1)) → Fin N) :
    edgeProd v x y f (ringInts (k + 1))
      = v x (f (aIdx (0 : Fin (k + 1))))
        * ((∏ m : Fin k, v (f (bIdx m.castSucc)) (f (aIdx m.succ)))
            * v (f (bIdx (Fin.last k))) y) := by
  classical
  simp only [edgeProd, ringInts, List.map_cons, List.prod_cons, List.map_append,
    List.prod_append, List.map_map, List.map_nil, List.prod_nil, siteIndex,
    aS, bS, Fin.prod_univ_def, Function.comp_def]
  ring

/-- **The peel.** An assignment for `ring (k+1)` splits as bubble 0's two
indices followed by an assignment for `ring k`, and the interaction chain
factors as the first interaction times the chain of `ring k` started at `b`. -/
theorem edgeProd_ringInts_peel (k : ℕ) (v : Matrix (Fin N) (Fin N) K)
    (x y a b : Fin N) (g : Fin (2 * k) → Fin N) :
    edgeProd v x y (Fin.cons a (Fin.cons b g)) (ringInts (k + 1))
      = v x a * edgeProd v b y g (ringInts k) := by
  classical
  rw [edgeProd_ringInts_succ, cons_cons_aIdx_zero]
  cases k with
  | zero =>
      rw [edgeProd_ringInts_zero]
      have hb : (Fin.cons a (Fin.cons b g) : Fin (2 * (0 + 1)) → Fin N)
          (bIdx (Fin.last 0)) = b := by
        rw [show (Fin.last 0 : Fin (0 + 1)) = (0 : Fin (0 + 1)) from rfl]
        exact cons_cons_bIdx_zero a b g
      rw [hb]
      simp
  | succ j =>
      rw [edgeProd_ringInts_succ, Fin.prod_univ_succ]
      -- bubble 0's two sites, then the tail's head
      have h0b : (Fin.cons a (Fin.cons b g) : Fin (2 * (j + 1 + 1)) → Fin N)
          (bIdx ((0 : Fin (j + 1)).castSucc)) = b := by
        rw [show ((0 : Fin (j + 1)).castSucc) = (0 : Fin (j + 1 + 1)) from rfl]
        exact cons_cons_bIdx_zero a b g
      have h0a : (Fin.cons a (Fin.cons b g) : Fin (2 * (j + 1 + 1)) → Fin N)
          (aIdx ((0 : Fin (j + 1)).succ)) = g (aIdx (0 : Fin (j + 1))) :=
        cons_cons_idx a b g _ _ (by simp [aIdx, Fin.val_succ])
      have hlast : (Fin.cons a (Fin.cons b g) : Fin (2 * (j + 1 + 1)) → Fin N)
          (bIdx (Fin.last (j + 1))) = g (bIdx (Fin.last j)) :=
        cons_cons_idx a b g _ _ (by simp [bIdx, Fin.val_last]; omega)
      have hmid : ∀ m : Fin j,
          v ((Fin.cons a (Fin.cons b g) : Fin (2 * (j + 1 + 1)) → Fin N)
                (bIdx m.succ.castSucc))
              ((Fin.cons a (Fin.cons b g) : Fin (2 * (j + 1 + 1)) → Fin N)
                (aIdx m.succ.succ))
            = v (g (bIdx m.castSucc)) (g (aIdx m.succ)) := by
        intro m
        rw [cons_cons_idx a b g _ (bIdx m.castSucc)
              (by simp [bIdx, Fin.val_succ, Fin.coe_castSucc]; omega),
            cons_cons_idx a b g _ (aIdx m.succ)
              (by simp [aIdx, Fin.val_succ]; omega)]
      rw [h0b, h0a, hlast]
      rw [Finset.prod_congr rfl (fun m _ => hmid m)]
      ring

end Products

/-! ### The general contraction theorem

`ringPart` is the contraction with the fixed external propagator stripped and
the two external endpoints made variable, so that it can be peeled one bubble
at a time. -/

section Contraction

variable {K : Type*} [CommRing K] {N : ℕ}

/-- The bubble-chain sum: `k` bubbles, `k+1` interactions, endpoints `x`, `y`. -/
def ringPart (B v : Matrix (Fin N) (Fin N) K) (k : ℕ) (x y : Fin N) : K :=
  ∑ f : Fin (2 * k) → Fin N,
    (∏ m : Fin k, B (f (aIdx m)) (f (bIdx m))) * edgeProd v x y f (ringInts k)

/-- Splitting an assignment for `ring (k+1)` into bubble 0's two indices and an
assignment for `ring k`.

Stated as an explicit `Equiv` rather than by rewriting with `sum_over_pi_succ`:
`Fin (2 * (k+1))` and `Fin (?n + 1)` are definitionally equal but do not unify
syntactically, because the literal `2` is not a successor numeral. -/
def peelEquiv (k N : ℕ) :
    (Fin N × Fin N × (Fin (2 * k) → Fin N)) ≃ (Fin (2 * (k + 1)) → Fin N) where
  toFun p := Fin.cons p.1 (Fin.cons p.2.1 p.2.2)
  invFun f := (f (aIdx (0 : Fin (k + 1))), f (bIdx (0 : Fin (k + 1))),
    fun q => f ⟨q.val + 2, by omega⟩)
  left_inv p := by
    obtain ⟨a, b, g⟩ := p
    dsimp only
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simpa using cons_cons_aIdx_zero a b g
    · simpa using cons_cons_bIdx_zero a b g
    · funext q
      simpa using cons_cons_at a b g q.val (by omega) q.isLt
  right_inv f := by
    funext q
    dsimp only
    refine Fin.cases ?_ (fun q' => ?_) q
    · have h0 : (aIdx (0 : Fin (k + 1)) : Fin (2 * (k + 1))) = 0 := by
        apply Fin.ext; simp [aIdx]
      rw [Fin.cons_zero, h0]
    · refine Fin.cases ?_ (fun q'' => ?_) q'
      · have h1 : (bIdx (0 : Fin (k + 1)) : Fin (2 * (k + 1)))
            = (0 : Fin (2 * k + 1)).succ := by
          apply Fin.ext; simp [bIdx, Fin.val_succ]
        rw [Fin.cons_succ, Fin.cons_zero, h1]
      · rw [Fin.cons_succ, Fin.cons_succ]
        congr 1

theorem sum_peel {K : Type*} [AddCommMonoid K] (k N : ℕ)
    (g : (Fin (2 * (k + 1)) → Fin N) → K) :
    (∑ f : Fin (2 * (k + 1)) → Fin N, g f)
      = ∑ a : Fin N, ∑ b : Fin N, ∑ h : Fin (2 * k) → Fin N,
          g (Fin.cons a (Fin.cons b h)) := by
  rw [← (peelEquiv k N).sum_comp g, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

theorem ringPart_zero (B v : Matrix (Fin N) (Fin N) K) (x y : Fin N) :
    ringPart B v 0 x y = v x y := by
  simp [ringPart, edgeProd_ringInts_zero]

theorem ringPart_succ (B v : Matrix (Fin N) (Fin N) K) (k : ℕ) (x y : Fin N) :
    ringPart B v (k + 1) x y
      = ∑ a : Fin N, ∑ b : Fin N, v x a * B a b * ringPart B v k b y := by
  classical
  rw [ringPart, sum_peel]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ringPart, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fin.prod_univ_succ, cons_cons_aIdx_zero, cons_cons_bIdx_zero,
      edgeProd_ringInts_peel]
  have hp : (∏ m : Fin k,
        B ((Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) (aIdx m.succ))
          ((Fin.cons a (Fin.cons b g) : Fin (2 * (k + 1)) → Fin N) (bIdx m.succ)))
      = ∏ m : Fin k, B (g (aIdx m)) (g (bIdx m)) :=
    Finset.prod_congr rfl fun m _ => by
      rw [cons_cons_aIdx_succ, cons_cons_bIdx_succ]
  rw [hp]
  ring

/-- `ringPart` is the matrix chain `v * (B * v)^k`, for every finite `N`. -/
theorem ringPart_eq_chain (B v : Matrix (Fin N) (Fin N) K) :
    ∀ (k : ℕ) (x y : Fin N), ringPart B v k x y = (v * (B * v) ^ k) x y := by
  intro k
  induction k with
  | zero => intro x y; simp [ringPart_zero]
  | succ k ih =>
      intro x y
      rw [ringPart_succ]
      have : ∀ a b : Fin N, v x a * B a b * ringPart B v k b y
          = v x a * B a b * (v * (B * v) ^ k) b y := by
        intro a b; rw [ih]
      rw [Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => this a b))]
      rw [Finset.sum_comm]
      have step : ∀ b : Fin N,
          (∑ a : Fin N, v x a * B a b * (v * (B * v) ^ k) b y)
            = (v * B) x b * (v * (B * v) ^ k) b y := by
        intro b
        simp [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun b _ => step b)]
      rw [← Matrix.mul_apply]
      have hassoc : (v * B) * (v * (B * v) ^ k) = v * (B * v) ^ (k + 1) := by
        rw [pow_succ']
        simp [mul_assoc]
      rw [hassoc]

/-- **The general contraction theorem.** For every `k` and every finite
dimension `N`, the contraction of the ring graph DATA is the matrix chain.

No positivity, invertibility, symmetry or convergence hypothesis is used; this
is a polynomial identity in the matrix entries over any commutative ring. -/
theorem contraction_ring (k : ℕ) (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    contraction (ring k) G v i j = G i j * (v * (bubble G * v) ^ k) i j := by
  classical
  have key : contraction (ring k) G v i j = G i j * ringPart (bubble G) v k i j := by
    rw [contraction, ringPart, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [show (ring k).propagators = ringProps k from rfl,
        show (ring k).interactions = ringInts k from rfl,
        edgeProd_ringProps]
    simp only [bubble]
    ring
  rw [key, ringPart_eq_chain]

end Contraction

/-! ### Membership characterisations of the two edge lists

Automorphism rigidity is proved through list MEMBERSHIP, not `List.get` index
arithmetic: the automorphism conditions say each edge maps to *some* edge, and
membership is the natural form of that. -/

section Membership

theorem mem_ringProps {k : ℕ} (p : Site (2 * k) × Site (2 * k)) :
    p ∈ ringProps k ↔ p = (.extI, .extJ) ∨ ∃ m : Fin k, p = (aS m, bS m) := by
  simp [ringProps, List.mem_flatMap]

theorem mem_ringInts_succ {k : ℕ} (p : Site (2 * (k + 1)) × Site (2 * (k + 1))) :
    p ∈ ringInts (k + 1) ↔
      p = (.extI, aS (0 : Fin (k + 1)))
        ∨ (∃ m : Fin k, p = (bS m.castSucc, aS m.succ))
        ∨ p = (bS (Fin.last k), .extJ) := by
  simp [ringInts]
  tauto

/-- Every edge maps to some edge: the membership form of the automorphism
conditions. -/
theorem isAut_props_mem {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (p : Site (2 * k) × Site (2 * k)) (hp : p ∈ ringProps k) :
    ∃ q ∈ ringProps k, samePair σ p q := by
  obtain ⟨e, he⟩ := List.mem_iff_get.mp hp
  exact ⟨_, List.get_mem _ _, he ▸ h.2.2.1 e⟩

theorem isAut_ints_mem {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (p : Site (2 * k) × Site (2 * k)) (hp : p ∈ ringInts k) :
    ∃ q ∈ ringInts k, samePair σ p q := by
  obtain ⟨e, he⟩ := List.mem_iff_get.mp hp
  exact ⟨_, List.get_mem _ _, he ▸ h.2.2.2 e⟩

/-! ### Site distinctness -/

@[simp] theorem aS_ne_extI {k : ℕ} (m : Fin k) : aS m ≠ (.extI : Site (2 * k)) := by
  simp [aS]
@[simp] theorem aS_ne_extJ {k : ℕ} (m : Fin k) : aS m ≠ (.extJ : Site (2 * k)) := by
  simp [aS]
@[simp] theorem bS_ne_extI {k : ℕ} (m : Fin k) : bS m ≠ (.extI : Site (2 * k)) := by
  simp [bS]
@[simp] theorem bS_ne_extJ {k : ℕ} (m : Fin k) : bS m ≠ (.extJ : Site (2 * k)) := by
  simp [bS]

@[simp] theorem extI_ne_extJ {n : ℕ} : (Site.extI : Site n) ≠ .extJ := by simp

theorem aS_ne_bS {k : ℕ} (m m' : Fin k) : aS m ≠ bS m' := by
  simp only [aS, bS, Ne, Site.int.injEq]
  exact aIdx_ne_bIdx m m'

theorem aS_inj {k : ℕ} {m m' : Fin k} (h : aS m = aS m') : m = m' :=
  aIdx_inj (by simpa [aS] using h)

theorem bS_inj {k : ℕ} {m m' : Fin k} (h : bS m = bS m') : m = m' :=
  bIdx_inj (by simpa [bS] using h)

/-! ### Rigidity: the external labels plus the interaction chain pin every site -/

/-- The first internal site is fixed: `extI` lies on exactly one interaction
edge, so that edge must map to itself. -/
theorem sigma_fixes_aS_zero {j : ℕ} {σ π ρ} (h : IsAut (ring (j + 1)) σ π ρ) :
    σ (aS (0 : Fin (j + 1))) = aS (0 : Fin (j + 1)) := by
  obtain ⟨q, hq, hs⟩ := isAut_ints_mem h (.extI, aS (0 : Fin (j + 1)))
    (by rw [mem_ringInts_succ]; exact Or.inl rfl)
  rw [mem_ringInts_succ] at hq
  have hI : σ (.extI : Site (2 * (j + 1))) = .extI := h.1
  simp only [samePair] at hs
  rcases hq with rfl | ⟨m, rfl⟩ | rfl
  · rcases hs with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hI.symm.trans h1) (aS_ne_extI _).symm
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd (hI.symm.trans h1) (bS_ne_extI _).symm
    · exact absurd (hI.symm.trans h1) (aS_ne_extI _).symm
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd (hI.symm.trans h1) (bS_ne_extI _).symm
    · exact absurd (hI.symm.trans h1) extI_ne_extJ

/-- Within a bubble: if `a` is fixed then so is `b`, because the only
propagators at `a` are that bubble's two parallel copies. -/
theorem sigma_fixes_bS {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) (m : Fin k)
    (ha : σ (aS m) = aS m) : σ (bS m) = bS m := by
  obtain ⟨q, hq, hs⟩ := isAut_props_mem h (aS m, bS m)
    (by rw [mem_ringProps]; exact Or.inr ⟨m, rfl⟩)
  rw [mem_ringProps] at hq
  simp only [samePair] at hs
  rcases hq with rfl | ⟨m', rfl⟩
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd (ha.symm.trans h1) (aS_ne_extI m)
    · exact absurd (ha.symm.trans h1) (aS_ne_extJ m)
  · rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl := aS_inj (ha.symm.trans h1); exact h2
    · exact absurd (ha.symm.trans h1) (aS_ne_bS m m')

/-- Along the chain: if `b` of bubble `m` is fixed then so is `a` of bubble
`m+1`, because `b_m` lies on exactly one interaction edge whose other end is
`a_{m+1}`. -/
theorem sigma_fixes_aS_succ {j : ℕ} {σ π ρ} (h : IsAut (ring (j + 1)) σ π ρ)
    (m : Fin j) (hb : σ (bS m.castSucc) = bS m.castSucc) :
    σ (aS m.succ) = aS m.succ := by
  obtain ⟨q, hq, hs⟩ := isAut_ints_mem h (bS m.castSucc, aS m.succ)
    (by rw [mem_ringInts_succ]; exact Or.inr (Or.inl ⟨m, rfl⟩))
  rw [mem_ringInts_succ] at hq
  simp only [samePair] at hs
  rcases hq with rfl | ⟨m', rfl⟩ | rfl
  · rcases hs with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd (hb.symm.trans h1) (bS_ne_extI _)
    · exact absurd (hb.symm.trans h1) (aS_ne_bS _ _).symm
  · rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl := Fin.castSucc_inj.mp (bS_inj (hb.symm.trans h1))
      exact h2
    · exact absurd (hb.symm.trans h1) (aS_ne_bS _ _).symm
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · -- `b_m` with `m < j` cannot be `b` of the LAST bubble
      exfalso
      have := bS_inj (hb.symm.trans h1)
      have hm : (m.castSucc : Fin (j + 1)).val = (Fin.last j).val := by
        rw [this]
      simp [Fin.coe_castSucc, Fin.val_last] at hm
      omega
    · exact absurd (hb.symm.trans h1) (bS_ne_extJ _)

/-- Every internal index belongs to exactly one bubble, on one of its two
sides. -/
theorem site_cases {k : ℕ} (q : Fin (2 * k)) :
    ∃ m : Fin k, q = aIdx m ∨ q = bIdx m := by
  rcases Nat.even_or_odd q.val with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨⟨r, by omega⟩, Or.inl (Fin.ext (by simp [aIdx]; omega))⟩
  · exact ⟨⟨r, by omega⟩, Or.inr (Fin.ext (by simp [bIdx]; omega))⟩

/-- **Chain rigidity.** Walking the interaction chain from the fixed external
label pins every internal site, alternating between the two claims above. This
is the structural replacement for enumerating automorphisms per order. -/
theorem sigma_fixes_all {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) :
    ∀ m : Fin k, σ (aS m) = aS m ∧ σ (bS m) = bS m := by
  have key : ∀ (t : ℕ) (ht : t < k),
      σ (aS ⟨t, ht⟩) = aS ⟨t, ht⟩ ∧ σ (bS ⟨t, ht⟩) = bS ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero =>
        intro ht
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have ha : σ (aS (⟨0, ht⟩ : Fin (j + 1))) = aS ⟨0, ht⟩ := by
          have := sigma_fixes_aS_zero h
          simpa using this
        exact ⟨ha, sigma_fixes_bS h _ ha⟩
    | succ t iht =>
        intro ht
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have htj : t < j := by omega
        have hb := (iht (by omega)).2
        have hcast : (⟨t, by omega⟩ : Fin (j + 1)) = (⟨t, htj⟩ : Fin j).castSucc :=
          Fin.ext rfl
        have hsucc : (⟨t + 1, ht⟩ : Fin (j + 1)) = (⟨t, htj⟩ : Fin j).succ :=
          Fin.ext rfl
        rw [hcast] at hb
        have ha : σ (aS (⟨t + 1, ht⟩ : Fin (j + 1))) = aS ⟨t + 1, ht⟩ := by
          rw [hsucc]; exact sigma_fixes_aS_succ h _ hb
        exact ⟨ha, sigma_fixes_bS h _ ha⟩
  intro m
  have := key m.val m.isLt
  simpa using this

/-- The site relabeling of any automorphism of `ring k` is the identity. -/
theorem sigma_eq_one {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) : σ = 1 := by
  apply Equiv.ext
  intro s
  match s with
  | .extI => exact h.1
  | .extJ => exact h.2.1
  | .int q =>
      obtain ⟨m, hm | hm⟩ := site_cases q
      · rw [hm]; exact (sigma_fixes_all h m).1
      · rw [hm]; exact (sigma_fixes_all h m).2

/-! ### The interaction permutation is forced

With `σ = 1`, no stored interaction pair is the reverse of another (left ends
are `extI` or some `b`; right ends are some `a` or `extJ`), so the unordered
condition collapses to equality of stored pairs. The list has no repeats, so
the permutation is the identity. -/

theorem ringInts_nodup (k : ℕ) : (ringInts k).Nodup := by
  -- via the left endpoints, which are `extI, b₀, …, b_{k-1}` and pairwise distinct
  refine List.Nodup.of_map Prod.fst ?_
  cases k with
  | zero => simp [ringInts]
  | succ j =>
      rw [ringInts]
      simp only [List.map_cons, List.map_append, List.map_map, List.map_nil,
        List.map_singleton, Function.comp_def]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton,
          true_and, not_or]
        exact ⟨fun ⟨m, hm⟩ => absurd hm (bS_ne_extI m.castSucc), fun hc =>
          absurd hc.symm (bS_ne_extI (Fin.last j))⟩
      · refine List.Nodup.append ?_ (by simp) ?_
        · refine List.Nodup.map ?_ (List.nodup_finRange j)
          intro m m' hmm
          exact Fin.castSucc_inj.mp (bS_inj hmm)
        · intro x hx hy
          simp only [List.mem_map, List.mem_finRange, true_and] at hx
          simp only [List.mem_singleton] at hy
          obtain ⟨m, rfl⟩ := hx
          have hlast : (m.castSucc : Fin (j + 1)) = Fin.last j := bS_inj hy
          have hv : (m.castSucc : Fin (j + 1)).val = (Fin.last j).val := by rw [hlast]
          simp [Fin.coe_castSucc, Fin.val_last] at hv
          omega

/-- With the site relabeling trivial, an interaction pair can only map to an
identical pair, never a reversed one: left endpoints are `extI` or some `b`,
right endpoints are some `a` or `extJ`, and those sets are disjoint. -/
theorem ints_pair_eq {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (e : Fin (ring k).interactions.length) :
    (ringInts k).get (ρ e) = (ringInts k).get e := by
  have hσ : σ = 1 := sigma_eq_one h
  have hs := h.2.2.2 e
  rw [hσ] at hs
  simp only [samePair, Equiv.Perm.one_apply] at hs
  have hmemE : (ringInts k).get e ∈ ringInts k := List.get_mem _ _
  have hmemR : (ringInts k).get (ρ e) ∈ ringInts k := List.get_mem _ _
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : ((ringInts k).get e).1 = ((ringInts k).get (ρ e)).1 := h1
    have h2' : ((ringInts k).get e).2 = ((ringInts k).get (ρ e)).2 := h2
    exact (Prod.ext h1'.symm h2'.symm)
  · exfalso
    have h1' : ((ringInts k).get e).1 = ((ringInts k).get (ρ e)).2 := h1
    have h2' : ((ringInts k).get e).2 = ((ringInts k).get (ρ e)).1 := h2
    cases k with
    | zero =>
        have hE : (ringInts 0).get e = ((.extI : Site (2 * 0)), (.extJ : Site (2 * 0))) := by
          simp [ringInts]
        have hR : (ringInts 0).get (ρ e) = ((.extI : Site (2 * 0)), (.extJ : Site (2 * 0))) := by
          simp [ringInts]
        rw [hE, hR] at h1'
        exact absurd h1' extI_ne_extJ
    | succ j =>
        rw [mem_ringInts_succ] at hmemE hmemR
        rcases hmemE with hE | ⟨m, hE⟩ | hE <;> rcases hmemR with hR | ⟨m', hR⟩ | hR <;>
          rw [hE] at h1' h2' <;> rw [hR] at h1' h2' <;>
          simp only [aS, bS] at h1' h2' <;>
          simp_all [aIdx, bIdx, Fin.ext_iff] <;> omega

/-- The interaction permutation of any automorphism is the identity. -/
theorem rho_eq_one {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) : ρ = 1 := by
  apply Equiv.ext
  intro e
  exact (List.Nodup.get_inj_iff (ringInts_nodup k)).mp (ints_pair_eq h e)

/-! ### The propagator permutation: only the bubble swaps survive -/

/-- Reading an index of a doubled list: entry `2i` and entry `2i+1` are both
the `i`-th value. Proved once, generically, by induction on the list. -/
theorem length_flatMap_pair {α β : Type*} (f : α → β) (l : List α) :
    (l.flatMap fun x => [f x, f x]).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons x t ih => simp [List.flatMap_cons, ih]; omega

theorem getElem_flatMap_pair {α β : Type*} (f : α → β) :
    ∀ (l : List α) (e : ℕ) (he : e < (l.flatMap fun x => [f x, f x]).length),
      ∃ i : Fin l.length,
        (l.flatMap fun x => [f x, f x])[e] = f (l.get i)
          ∧ (e = 2 * i.val ∨ e = 2 * i.val + 1)
  | [], e, he => absurd he (by simp)
  | (x :: t), 0, he => ⟨⟨0, by simp⟩, by simp [List.flatMap_cons], Or.inl rfl⟩
  | (x :: t), 1, he => ⟨⟨0, by simp⟩, by simp [List.flatMap_cons], Or.inr rfl⟩
  | (x :: t), (e + 2), he => by
      have he' : e < (t.flatMap fun y => [f y, f y]).length := by
        rw [length_flatMap_pair] at he ⊢
        simp at he
        omega
      obtain ⟨i, hget, hidx⟩ := getElem_flatMap_pair f t e he'
      refine ⟨i.succ, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append,
          List.getElem_cons_succ]
        rw [hget]
        simp
      · simp only [Fin.val_succ]
        omega

/-! ### Index structure of the propagator list -/

theorem ringProps_length (k : ℕ) : (ringProps k).length = 1 + 2 * k := by
  simp [ringProps, length_flatMap_pair]
  omega

/-- Index 0 is the external propagator; every other index belongs to a bubble,
and the two indices `1+2m`, `2+2m` are exactly bubble `m`'s two parallel
copies. -/
theorem ringProps_getElem_zero (k : ℕ) :
    (ringProps k)[0]'(by simp [ringProps]) = ((.extI : Site (2 * k)), .extJ) := by
  simp [ringProps]

theorem ringProps_getElem_succ (k : ℕ) (e : ℕ) (he : e + 1 < (ringProps k).length) :
    ∃ m : Fin k, (ringProps k)[e + 1] = (aS m, bS m)
      ∧ (e = 2 * m.val ∨ e = 2 * m.val + 1) := by
  have he' : e < ((List.finRange k).flatMap fun m => [((aS m, bS m)), (aS m, bS m)]).length := by
    rw [length_flatMap_pair]
    rw [ringProps_length] at he
    simp
    omega
  obtain ⟨i, hget, hidx⟩ := getElem_flatMap_pair (fun m : Fin k => ((aS m, bS m))) (List.finRange k) e he'
  refine ⟨(List.finRange k).get i, ?_, ?_⟩
  · simpa [ringProps] using hget
  · simpa [List.get_finRange] using hidx

/-- With the site relabeling trivial, a propagator pair maps to an identical
stored pair: no stored pair is the reverse of another. -/
theorem props_pair_eq {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (e : Fin (ring k).propagators.length) :
    (ringProps k).get (π e) = (ringProps k).get e := by
  have hσ : σ = 1 := sigma_eq_one h
  have hs := h.2.2.1 e
  rw [hσ] at hs
  simp only [samePair, Equiv.Perm.one_apply] at hs
  have hmemE : (ringProps k).get e ∈ ringProps k := List.get_mem _ _
  have hmemR : (ringProps k).get (π e) ∈ ringProps k := List.get_mem _ _
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : ((ringProps k).get e).1 = ((ringProps k).get (π e)).1 := h1
    have h2' : ((ringProps k).get e).2 = ((ringProps k).get (π e)).2 := h2
    exact (Prod.ext h1'.symm h2'.symm)
  · exfalso
    have h1' : ((ringProps k).get e).1 = ((ringProps k).get (π e)).2 := h1
    have h2' : ((ringProps k).get e).2 = ((ringProps k).get (π e)).1 := h2
    rw [mem_ringProps] at hmemE hmemR
    rcases hmemE with hE | ⟨m, hE⟩ <;> rcases hmemR with hR | ⟨m', hR⟩ <;>
      rw [hE] at h1' h2' <;> rw [hR] at h1' h2' <;> simp only at h1' h2'
    · exact absurd h1' extI_ne_extJ
    · exact absurd h2' (aS_ne_extJ m').symm
    · exact absurd h1' (aS_ne_extJ m)
    · exact absurd h1' (aS_ne_bS m m')

/-- The external propagator index is fixed. -/
theorem pi_fixes_external {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (e : Fin (ring k).propagators.length) (he : e.val = 0) : (π e).val = 0 := by
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t, (π e).val = t + 1 := ⟨(π e).val - 1, by omega⟩
  have hlt : t + 1 < (ringProps k).length := by rw [← ht]; exact (π e).isLt
  obtain ⟨m, hm, _⟩ := ringProps_getElem_succ k t hlt
  have hpe : (ringProps k).get (π e) = (aS m, bS m) := by
    rw [List.get_eq_getElem]
    simpa [ht] using hm
  have hze : (ringProps k).get e = ((.extI : Site (2 * k)), .extJ) := by
    rw [List.get_eq_getElem]
    simpa [he] using ringProps_getElem_zero k
  rw [props_pair_eq h e, hze] at hpe
  exact absurd (congrArg Prod.fst hpe) (by simpa using (aS_ne_extI m).symm)

/-- A bubble copy maps to a copy of the SAME bubble. -/
theorem pi_same_bubble {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (e : Fin (ring k).propagators.length) (m : Fin k)
    (hm : (ringProps k).get e = (aS m, bS m)) :
    (ringProps k).get (π e) = (aS m, bS m) := by
  rw [props_pair_eq h e, hm]

/-! ### Classifying the propagator permutation -/

/-- The two propagator indices of bubble `m`. -/
def pIdx1 {k : ℕ} (m : Fin k) : Fin (ringProps k).length :=
  ⟨1 + 2 * m.val, by rw [ringProps_length]; omega⟩

def pIdx2 {k : ℕ} (m : Fin k) : Fin (ringProps k).length :=
  ⟨2 + 2 * m.val, by rw [ringProps_length]; omega⟩

theorem pIdx1_ne_pIdx2 {k : ℕ} (m : Fin k) : pIdx1 m ≠ pIdx2 m := by
  simp [pIdx1, pIdx2, Fin.ext_iff]

theorem get_pIdx1 {k : ℕ} (m : Fin k) :
    (ringProps k).get (pIdx1 m) = (aS m, bS m) := by
  have hb : 2 * m.val + 1 < (ringProps k).length := by
    rw [ringProps_length]; omega
  obtain ⟨m', hm', hidx⟩ := ringProps_getElem_succ k (2 * m.val) hb
  have hmm : m' = m := by
    rcases hidx with h | h
    · exact Fin.ext (by omega)
    · omega
  rw [hmm] at hm'
  have hfin : pIdx1 m = (⟨2 * m.val + 1, hb⟩ : Fin (ringProps k).length) :=
    Fin.ext (by simp [pIdx1]; omega)
  rw [hfin, List.get_eq_getElem]
  exact hm'

theorem get_pIdx2 {k : ℕ} (m : Fin k) :
    (ringProps k).get (pIdx2 m) = (aS m, bS m) := by
  have hb : 2 * m.val + 1 + 1 < (ringProps k).length := by
    rw [ringProps_length]; omega
  obtain ⟨m', hm', hidx⟩ := ringProps_getElem_succ k (2 * m.val + 1) hb
  have hmm : m' = m := by
    rcases hidx with h | h
    · omega
    · exact Fin.ext (by omega)
  rw [hmm] at hm'
  have hfin : pIdx2 m = (⟨2 * m.val + 1 + 1, hb⟩ : Fin (ringProps k).length) :=
    Fin.ext (by simp [pIdx2]; omega)
  rw [hfin, List.get_eq_getElem]
  exact hm'

/-- Every propagator index is the external one or one of a bubble's two. -/
theorem props_index_cases {k : ℕ} (e : Fin (ringProps k).length) :
    e.val = 0 ∨ ∃ m : Fin k, e = pIdx1 m ∨ e = pIdx2 m := by
  rcases Nat.eq_zero_or_pos e.val with h | h
  · exact Or.inl h
  · have hlt : e.val < 1 + 2 * k := by rw [← ringProps_length k]; exact e.isLt
    have hk : (e.val - 1) / 2 < k := by omega
    refine Or.inr ⟨⟨(e.val - 1) / 2, hk⟩, ?_⟩
    rcases Nat.even_or_odd (e.val - 1) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl (Fin.ext (by simp [pIdx1]; omega))
    · exact Or.inr (Fin.ext (by simp [pIdx2]; omega))

/-- The propagator permutation maps each bubble copy to a copy of the same
bubble, hence to one of that bubble's two indices. -/
theorem pi_bubble_mem {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) (m : Fin k)
    (e : Fin (ring k).propagators.length) (he : (ringProps k).get e = (aS m, bS m)) :
    π e = pIdx1 m ∨ π e = pIdx2 m := by
  have hpair : (ringProps k).get (π e) = (aS m, bS m) := pi_same_bubble h e m he
  rcases props_index_cases (π e) with hz | ⟨m', hm'⟩
  · exfalso
    have : (ringProps k).get (π e) = ((.extI : Site (2 * k)), .extJ) := by
      rw [List.get_eq_getElem]
      simpa [hz] using ringProps_getElem_zero k
    rw [hpair] at this
    exact absurd (congrArg Prod.fst this) (aS_ne_extI m)
  · rcases hm' with hm' | hm'
    · rw [hm'] at hpair
      rw [get_pIdx1] at hpair
      obtain rfl := aS_inj (congrArg Prod.fst hpair)
      exact Or.inl hm'
    · rw [hm'] at hpair
      rw [get_pIdx2] at hpair
      obtain rfl := aS_inj (congrArg Prod.fst hpair)
      exact Or.inr hm'

/-! ### The bubble-swap permutations, and the classification -/

/-- Flip the two copies of every bubble whose bit is set. Written as an
explicit involution so that its action on each index is computable, rather than
as a product of swaps whose action would need a disjointness argument. -/
def flipIdx {k : ℕ} (bits : Fin k → Bool) (e : Fin (ringProps k).length) :
    Fin (ringProps k).length :=
  if h : 0 < e.val then
    have hlt : e.val < 1 + 2 * k := by rw [← ringProps_length k]; exact e.isLt
    if bits ⟨(e.val - 1) / 2, by omega⟩ then
      if h2 : (e.val - 1) % 2 = 0 then
        ⟨e.val + 1, by have hL := ringProps_length k; omega⟩
      else
        ⟨e.val - 1, by have hL := ringProps_length k; omega⟩
    else e
  else e

theorem flipIdx_pIdx1 {k : ℕ} (bits : Fin k → Bool) (m : Fin k) :
    flipIdx bits (pIdx1 m) = if bits m then pIdx2 m else pIdx1 m := by
  have hv : (pIdx1 m).val = 1 + 2 * m.val := rfl
  rw [flipIdx]
  rw [dif_pos (by rw [hv]; omega)]
  have hm : (((pIdx1 m).val - 1) / 2) = m.val := by rw [hv]; omega
  have hmod : ((pIdx1 m).val - 1) % 2 = 0 := by rw [hv]; omega
  simp only [hmod, dif_pos]
  have : (⟨((pIdx1 m).val - 1) / 2, by rw [hv]; omega⟩ : Fin k) = m := Fin.ext hm
  rw [this]
  by_cases hb : bits m
  · simp only [hb, if_true]
    exact Fin.ext (by simp [pIdx1, pIdx2] <;> try omega)
  · simp [hb]

theorem flipIdx_pIdx2 {k : ℕ} (bits : Fin k → Bool) (m : Fin k) :
    flipIdx bits (pIdx2 m) = if bits m then pIdx1 m else pIdx2 m := by
  have hv : (pIdx2 m).val = 2 + 2 * m.val := rfl
  rw [flipIdx]
  rw [dif_pos (by rw [hv]; omega)]
  have hm : (((pIdx2 m).val - 1) / 2) = m.val := by rw [hv]; omega
  have hmod : ((pIdx2 m).val - 1) % 2 ≠ 0 := by rw [hv]; omega
  simp only [dif_neg hmod]
  have : (⟨((pIdx2 m).val - 1) / 2, by rw [hv]; omega⟩ : Fin k) = m := Fin.ext hm
  rw [this]
  by_cases hb : bits m
  · simp only [hb, if_true]
    exact Fin.ext (by simp [pIdx1, pIdx2] <;> try omega)
  · simp [hb]

theorem flipIdx_zero {k : ℕ} (bits : Fin k → Bool) (e : Fin (ringProps k).length)
    (he : e.val = 0) : flipIdx bits e = e := by
  rw [flipIdx, dif_neg (by omega)]

theorem flipIdx_involutive {k : ℕ} (bits : Fin k → Bool) :
    Function.Involutive (flipIdx bits) := by
  intro e
  rcases props_index_cases e with hz | ⟨m, hm | hm⟩
  · rw [flipIdx_zero bits e hz, flipIdx_zero bits e hz]
  · subst hm
    rw [flipIdx_pIdx1]
    by_cases hb : bits m
    · rw [if_pos hb, flipIdx_pIdx2, if_pos hb]
    · rw [if_neg hb, flipIdx_pIdx1, if_neg hb]
  · subst hm
    rw [flipIdx_pIdx2]
    by_cases hb : bits m
    · rw [if_pos hb, flipIdx_pIdx1, if_pos hb]
    · rw [if_neg hb, flipIdx_pIdx2, if_neg hb]

/-- The bubble-swap permutation selected by a bit vector. -/
def flipPerm {k : ℕ} (bits : Fin k → Bool) : Equiv.Perm (Fin (ringProps k).length) :=
  (flipIdx_involutive bits).toPerm _

theorem flipPerm_apply {k : ℕ} (bits : Fin k → Bool) (e) :
    flipPerm bits e = flipIdx bits e := rfl

/-- A bubble swap preserves every stored propagator pair. -/
theorem flipPerm_preserves {k : ℕ} (bits : Fin k → Bool)
    (e : Fin (ringProps k).length) :
    (ringProps k).get (flipPerm bits e) = (ringProps k).get e := by
  rcases props_index_cases e with hz | ⟨m, hm | hm⟩
  · rw [flipPerm_apply, flipIdx_zero bits e hz]
  · subst hm
    rw [flipPerm_apply, flipIdx_pIdx1]
    by_cases hb : bits m
    · rw [if_pos hb, get_pIdx1, get_pIdx2]
    · rw [if_neg hb]
  · subst hm
    rw [flipPerm_apply, flipIdx_pIdx2]
    by_cases hb : bits m
    · rw [if_pos hb, get_pIdx1, get_pIdx2]
    · rw [if_neg hb]

/-- Every bit vector gives an automorphism. -/
theorem isAut_flipPerm {k : ℕ} (bits : Fin k → Bool) :
    IsAut (ring k) 1 (flipPerm bits) 1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro e
    have := flipPerm_preserves bits e
    exact Or.inl ⟨congrArg Prod.fst this.symm, congrArg Prod.snd this.symm⟩
  · intro e
    exact Or.inl ⟨rfl, rfl⟩

/-- Within a bubble, an automorphism either fixes both copies or swaps them. -/
theorem pi_pIdx2_of_pIdx1 {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) (m : Fin k) :
    (π (pIdx1 m) = pIdx1 m → π (pIdx2 m) = pIdx2 m)
      ∧ (π (pIdx1 m) = pIdx2 m → π (pIdx2 m) = pIdx1 m) := by
  have h2 := pi_bubble_mem h m (pIdx2 m) (get_pIdx2 m)
  constructor
  · intro h1
    rcases h2 with h2 | h2
    · exact absurd (π.injective (h1.trans h2.symm)) (pIdx1_ne_pIdx2 m)
    · exact h2
  · intro h1
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd (π.injective (h1.trans h2.symm)) (pIdx1_ne_pIdx2 m)

/-- The bits of an automorphism: does it exchange bubble `m`'s two copies? -/
def autBits {k : ℕ} (a : Aut (ring k)) : Fin k → Bool :=
  fun m => decide (a.1.2.1 (pIdx1 m) = pIdx2 m)

/-- **The structural symmetry classification.** The automorphisms of `ring k`
are exactly the independent choices of whether to exchange the two propagators
inside each of the `k` bubbles. Proved for arbitrary `k` from chain rigidity,
with no enumeration over automorphisms at any order. -/
def autEquivBits (k : ℕ) : Aut (ring k) ≃ (Fin k → Bool) where
  toFun := autBits
  invFun bits := ⟨(1, flipPerm bits, 1), isAut_flipPerm bits⟩
  left_inv a := by
    obtain ⟨⟨σ, π, ρ⟩, ha⟩ := a
    have hσ : σ = 1 := sigma_eq_one ha
    have hρ : ρ = 1 := rho_eq_one ha
    refine Subtype.ext (Prod.ext hσ.symm (Prod.ext ?_ hρ.symm))
    refine Equiv.ext fun e => ?_
    have hbits : autBits (⟨(σ, π, ρ), ha⟩ : Aut (ring k))
        = fun m => decide (π (pIdx1 m) = pIdx2 m) := rfl
    show flipPerm (autBits (⟨(σ, π, ρ), ha⟩ : Aut (ring k))) e = π e
    rw [flipPerm_apply, hbits]
    rcases props_index_cases e with hz | ⟨m, hm | hm⟩
    · rw [flipIdx_zero _ e hz]
      exact Fin.ext (hz.trans (pi_fixes_external ha e hz).symm)
    · subst hm
      rcases pi_bubble_mem ha m (pIdx1 m) (get_pIdx1 m) with h1 | h1
      · rw [flipIdx_pIdx1]
        simp [h1, pIdx1_ne_pIdx2 m]
      · rw [flipIdx_pIdx1]
        simp [h1]
    · subst hm
      rcases pi_bubble_mem ha m (pIdx1 m) (get_pIdx1 m) with h1 | h1
      · have h2 := (pi_pIdx2_of_pIdx1 ha m).1 h1
        rw [flipIdx_pIdx2]
        simp [h1, pIdx1_ne_pIdx2 m, h2]
      · have h2 := (pi_pIdx2_of_pIdx1 ha m).2 h1
        rw [flipIdx_pIdx2]
        simp [h1, h2]
  right_inv bits := by
    funext m
    show decide (flipPerm bits (pIdx1 m) = pIdx2 m) = bits m
    rw [flipPerm_apply, flipIdx_pIdx1]
    by_cases hb : bits m
    · simp [hb]
    · simp [hb, pIdx1_ne_pIdx2 m]

/-- **The symmetry factor is `2 ^ k`, for every `k`.** Lin-Lindsey p. 42 states
`S_{Γ_k} = 2^k` "with a factor of 2 deriving from the each symmetry that
exchanges the two propagators in one of the k 'bubbles'". Here it is derived
from the automorphism definition rather than assumed, and without enumerating
automorphisms per order. -/
theorem card_aut_ring (k : ℕ) : Fintype.card (Aut (ring k)) = 2 ^ k := by
  rw [Fintype.card_congr (autEquivBits k)]
  simp

theorem ringInts_length (k : ℕ) : (ringInts k).length = k + 1 := by
  cases k with
  | zero => simp [ringInts]
  | succ j => simp [ringInts]

/-- **The general ring contribution.** Signed contraction divided by the proved
symmetry factor, for every `k` and every finite dimension `N`:

`contribution (ring k) = (-1)^(k+1) • (G ⊙ (v (B v)^k)) / 2^k`,

which is the paper's finite-order ring contribution. At `k = 0, 1, 2` this is
`-(G ⊙ v)`, `+(1/2)(G ⊙ vBv)`, `-(1/4)(G ⊙ vBvBv)`. -/
theorem contribution_ring {F : Type*} [Field F] {N : ℕ} (k : ℕ)
    (G v : Matrix (Fin N) (Fin N) F) (i j : Fin N) :
    contribution (ring k) G v i j
      = (-1) ^ (k + 1) * (G i j * (v * (bubble G * v) ^ k) i j) / (2 ^ k : F) := by
  rw [contribution, card_aut_ring, contraction_ring, signFactor,
    show (ring k).interactions.length = k + 1 from ringInts_length k]
  push_cast
  ring

/-! ### Refuting purported extra automorphisms

These follow from rigidity, so they are theorems about every `k`, not decisions
at one order. -/

/-- No automorphism moves an external label. -/
theorem aut_fixes_extI {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) :
    σ (.extI : Site (2 * k)) = .extI := h.1

theorem aut_fixes_extJ {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ) :
    σ (.extJ : Site (2 * k)) = .extJ := h.2.1

/-- No automorphism carries one bubble onto a different bubble: the interaction
path is rigid, so distinct bubbles cannot be exchanged. -/
theorem aut_no_bubble_exchange {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (m m' : Fin k) (hne : m ≠ m') : σ (aS m) ≠ aS m' := by
  rw [(sigma_fixes_all h m).1]
  exact fun hc => hne (aS_inj hc)

/-- No automorphism exchanges the two sites INSIDE a bubble either: `a` faces
the `I` side of the chain and `b` the `J` side. -/
theorem aut_no_intra_bubble_exchange {k : ℕ} {σ π ρ} (h : IsAut (ring k) σ π ρ)
    (m m' : Fin k) : σ (aS m) ≠ bS m' := by
  rw [(sigma_fixes_all h m).1]
  exact aS_ne_bS m m'

/-- The ring family has no self-loop, which is why the compressed
representation is faithful here while `selfLoopWitness` shows it is not in
general. -/
theorem ring_no_self_loop (k : ℕ) (p : Site (2 * k) × Site (2 * k))
    (hp : p ∈ ringProps k) : p.1 ≠ p.2 := by
  rw [mem_ringProps] at hp
  rcases hp with rfl | ⟨m, rfl⟩
  · exact extI_ne_extJ
  · exact aS_ne_bS m m

/-- The certification the executable evaluator relies on: using the literal
`2^k` as the symmetry divisor is equal to dividing by the automorphism count.
`2^k` is therefore never an INPUT to the definition of the graph value -- it is
the proved cardinality, substituted only for speed. -/
theorem contribution_ring_eq_contributionOf {F : Type*} [Field F] {N : ℕ}
    (k : ℕ) (G v : Matrix (Fin N) (Fin N) F) (i j : Fin N) :
    contribution (ring k) G v i j = contributionOf (2 ^ k) (ring k) G v i j :=
  contribution_eq_of_card (ring k) (2 ^ k) (card_aut_ring k) G v i j

end Membership

end GW.LL

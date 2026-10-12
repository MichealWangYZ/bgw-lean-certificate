/-
The first three ring diagrams of Lin-Lindsey Part I (arXiv:1809.02900v1),
PDF section 4.7.1, printed pp. 42-43, Fig. 4.11.

The graph data below was read off Fig. 4.11: an external propagator carrying
the two external labels, together with a chain of `k+1` interaction lines
separated by `k` bubbles, each bubble being two parallel propagators joining
the same pair of internal sites.

The paper states (p. 42) that the `k`-th ring has symmetry factor `S = 2^k`,
"with a factor of 2 deriving from the each symmetry that exchanges the two
propagators in one of the k 'bubbles'", and amplitude
`F(i,j) = -([-v(G ⊙ G)]^k v)_{ij} G_{ij}`; p. 43 then sums `F/S`.

The matrix expressions in `target0/1/2` are written down independently and are
never used to define contraction. `GW.LL.Diagram` computes a number from the
edge lists alone.
-/
import GW.LL.Diagram
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Push

namespace GW.LL

open FeynDiagram

variable {K : Type*} [CommRing K] {N : ℕ}

/-- `B = G ⊙ G`, the entrywise (Hadamard) square appearing in a bubble. -/
def bubble (G : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  fun a b => G a b * G a b

/-! ### The three graphs, as data -/

/-- Ring 0: the Fock exchange diagram, Fig. 4.10 (b). One external propagator
and one interaction line joining the two external sites. No bubbles. -/
def ring0 : FeynDiagram where
  numInternal := 0
  propagators := [(.extI, .extJ)]
  interactions := [(.extI, .extJ)]

/-- Ring 1: Fig. 4.10 (c). Internal sites `a = int 0`, `b = int 1`; one bubble
(two parallel propagators `a`-`b`) between two interaction lines. -/
def ring1 : FeynDiagram where
  numInternal := 2
  propagators := [(.extI, .extJ), (.int 0, .int 1), (.int 0, .int 1)]
  interactions := [(.extI, .int 0), (.int 1, .extJ)]

/-- Ring 2: two bubbles `a₁b₁`, `a₂b₂` and three interaction lines. -/
def ring2 : FeynDiagram where
  numInternal := 4
  propagators :=
    [(.extI, .extJ), (.int 0, .int 1), (.int 0, .int 1), (.int 2, .int 3), (.int 2, .int 3)]
  interactions := [(.extI, .int 0), (.int 1, .int 2), (.int 3, .extJ)]

/-! ### The independently written matrix expressions -/

/-- `-(G ⊙ v)` at `(i,j)`. -/
def target0 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  -(G i j * v i j)

/-- `+(1/2) • (G ⊙ (v * B * v))` at `(i,j)`, with the `1/2` supplied separately
by the symmetry factor; this is the unweighted matrix part. -/
def matrix1 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  G i j * (v * bubble G * v) i j

/-- `-(G ⊙ (v * B * v * B * v))` at `(i,j)`, unweighted matrix part. -/
def matrix2 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  G i j * (v * bubble G * v * bubble G * v) i j

/-! ### Contraction identities, for every finite dimension `N`

No symmetry, positivity or invertibility hypothesis is used: these are
polynomial identities in the matrix entries. -/

theorem contraction_ring0 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    contraction ring0 G v i j = G i j * v i j := by
  simp [contraction, ring0, edgeProd, siteIndex]

theorem contraction_ring1 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    contraction ring1 G v i j = matrix1 G v i j := by
  have lhs : contraction ring1 G v i j
      = ∑ a : Fin N, ∑ b : Fin N, G i j * (G a b * G a b) * (v i a * v b j) := by
    rw [contraction]
    simp only [ring1]
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ring1, edgeProd, siteIndex]
  have rhs : matrix1 G v i j
      = ∑ a : Fin N, ∑ b : Fin N, G i j * (G a b * G a b) * (v i a * v b j) := by
    simp only [matrix1, bubble, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [lhs, rhs]

/-- Reversing the nesting order of four finite sums. Used because a contraction
naturally enumerates internal sites along the chain, while an iterated matrix
product nests from the last index inwards. -/
theorem sum4_reverse (F : Fin N → Fin N → Fin N → Fin N → K) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  let rev : (Fin N × Fin N × Fin N × Fin N) ≃ (Fin N × Fin N × Fin N × Fin N) :=
    { toFun := fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)
      invFun := fun q => (q.2.2.2, q.2.2.1, q.2.1, q.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
      = ∑ p : Fin N × Fin N × Fin N × Fin N, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
        simp [Fintype.sum_prod_type]
    _ = ∑ q : Fin N × Fin N × Fin N × Fin N,
          F (rev q).1 (rev q).2.1 (rev q).2.2.1 (rev q).2.2.2 :=
        (rev.sum_comp fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2).symm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
        simp [Fintype.sum_prod_type, rev]

theorem contraction_ring2 (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    contraction ring2 G v i j = matrix2 G v i j := by
  have lhs : contraction ring2 G v i j
      = ∑ a1 : Fin N, ∑ b1 : Fin N, ∑ a2 : Fin N, ∑ b2 : Fin N,
          G i j * (G a1 b1 * G a1 b1) * (G a2 b2 * G a2 b2)
            * (v i a1 * v b1 a2 * v b2 j) := by
    rw [contraction]
    simp only [ring2]
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun b1 _ => ?_
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun a2 _ => ?_
    rw [sum_over_pi_succ]
    refine Finset.sum_congr rfl fun b2 _ => ?_
    -- `Fin.cons` at the numeral indices 2 and 3 reduces definitionally but is
    -- not touched by `simp`; supply the two reductions explicitly.
    have e1 : ∀ f : Fin 0 → Fin N,
        (Fin.cons a1 (Fin.cons b1 (Fin.cons a2 (Fin.cons b2 f))) : Fin 4 → Fin N) 1 = b1 :=
      fun _ => rfl
    have e2 : ∀ f : Fin 0 → Fin N,
        (Fin.cons a1 (Fin.cons b1 (Fin.cons a2 (Fin.cons b2 f))) : Fin 4 → Fin N) 2 = a2 :=
      fun _ => rfl
    have e3 : ∀ f : Fin 0 → Fin N,
        (Fin.cons a1 (Fin.cons b1 (Fin.cons a2 (Fin.cons b2 f))) : Fin 4 → Fin N) 3 = b2 :=
      fun _ => rfl
    simp only [edgeProd, siteIndex, List.map, List.prod_cons, List.prod_nil,
      Fin.cons_zero, Fin.cons_succ, e1, e2, e3, Fintype.sum_unique]
    ring
  have rhs : matrix2 G v i j
      = ∑ a1 : Fin N, ∑ b1 : Fin N, ∑ a2 : Fin N, ∑ b2 : Fin N,
          G i j * (G a1 b1 * G a1 b1) * (G a2 b2 * G a2 b2)
            * (v i a1 * v b1 a2 * v b2 j) := by
    simp only [matrix2, bubble, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [← sum4_reverse]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    refine Finset.sum_congr rfl fun b1 _ => ?_
    refine Finset.sum_congr rfl fun a2 _ => ?_
    refine Finset.sum_congr rfl fun b2 _ => ?_
    ring
  rw [lhs, rhs]

/-! ### Symmetry factors

Lin-Lindsey p. 42: the `k`-th ring has `S = 2^k`, "with a factor of 2 deriving
from the each symmetry that exchanges the two propagators in one of the k
'bubbles'". The counts below are computed from the automorphism definition, not
asserted. -/

set_option maxRecDepth 1000000 in
/-- `S = 1` for the Fock diagram. -/
theorem symmetry_ring0 : Fintype.card (Aut ring0) = 1 := by decide

set_option maxRecDepth 1000000 in
/-- `S = 2` for the first ring: the one bubble's two propagators may be
exchanged. Decided over all triples. -/
theorem symmetry_ring1 : Fintype.card (Aut ring1) = 2 := by decide

/-! For ring 2 the full triple enumeration is ~5·10⁵ candidates and overflows
the kernel. It is replaced by a proved reduction, not by a weaker statement:
the site relabeling and interaction permutation are *forced* to be trivial
(each by an exhaustive decision over its own much smaller space), after which
only the 120 propagator permutations remain. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 400 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Neither edge condition alone forces the site relabeling to be trivial:
the interactions permit exchanging `b₁ ↔ a₂` (their shared edge is unordered),
and the propagators permit exchanging the two whole bubbles. Together they do
force it. -/
theorem ring2_forces_id_site (σ : Equiv.Perm (Site 4))
    (h : σ .extI = .extI ∧ σ .extJ = .extJ ∧
      (∃ ρ : Equiv.Perm (Fin 3), ∀ e,
        samePair σ (ring2.interactions.get e) (ring2.interactions.get (ρ e))) ∧
      (∃ π : Equiv.Perm (Fin 5), ∀ e,
        samePair σ (ring2.propagators.get e) (ring2.propagators.get (π e)))) :
    σ = 1 := by
  revert σ h
  decide

set_option maxRecDepth 1000000 in
/-- With a trivial site relabeling the three interaction edges have pairwise
distinct endpoint pairs, so no interaction permutation is possible but the
identity. -/
theorem ring2_forces_id_int (ρ : Equiv.Perm (Fin 3))
    (h : ∀ e, samePair (1 : Equiv.Perm (Site 4))
      (ring2.interactions.get e) (ring2.interactions.get (ρ e))) : ρ = 1 := by
  revert ρ h
  decide

set_option maxRecDepth 1000000 in
/-- The surviving freedom: exchange the two propagators inside each of the two
bubbles, and nothing else. -/
theorem ring2_prop_card :
    Fintype.card {π : Equiv.Perm (Fin 5) // ∀ e, samePair (1 : Equiv.Perm (Site 4))
      (ring2.propagators.get e) (ring2.propagators.get (π e))} = 4 := by decide

/-- `S = 4` for the second ring: one factor of two per bubble. -/
theorem symmetry_ring2 : Fintype.card (Aut ring2) = 4 := by
  rw [Fintype.card_congr (autEquivProps ring2
    (fun σ π ρ hx => ring2_forces_id_site σ ⟨hx.1, hx.2.1, ⟨ρ, hx.2.2.2⟩, ⟨π, hx.2.2.1⟩⟩)
    (fun σ π ρ hx => by
      have hs := ring2_forces_id_site σ ⟨hx.1, hx.2.1, ⟨ρ, hx.2.2.2⟩, ⟨π, hx.2.2.1⟩⟩
      exact ring2_forces_id_int ρ (by rw [← hs]; exact hx.2.2.2)))]
  exact ring2_prop_card

/-! ### Scope evidence: where the compressed representation is NOT faithful -/

/-- The small witness identified by review of LL-C1: sites `I, J, a, b`,
interactions `(I,J)` and `(a,b)`, propagators `(I,a)`, `(a,J)` and the
self-loop `(b,b)`, with the external labels fixed at `I` and `J`.

**Kernel-checked below:** the compressed automorphism count is 1.

**External reasoning, NOT kernel-checked here:** in a half-edge reading the two
incidences of the `(b,b)` propagator may be exchanged while every site and edge
identifier stays fixed, giving 2. This repository does not formalize a
half-edge model for diagrams with self-loops -- `GW.LL.RingHalfEdge` is
deliberately ring-only -- so that 2 is stated as reasoning about the paper's
definition, not as a Lean theorem.

The gap therefore bounds the compressed representation's claim. It does not
touch the ring family: no `ring k` contains a self-loop (`ring_no_self_loop`). -/
def selfLoopWitness : FeynDiagram where
  numInternal := 2
  propagators := [(.extI, .int 0), (.int 0, .extJ), (.int 1, .int 1)]
  interactions := [(.extI, .extJ), (.int 0, .int 1)]

set_option maxRecDepth 100000 in
/-- The compressed representation counts 1. External reasoning puts the
half-edge count at 2; see the docstring for why that half is not a theorem. -/
theorem selfLoopWitness_compressed_card :
    Fintype.card (Aut selfLoopWitness) = 1 := by decide

/-! ### The three ring contributions

Each is the diagram's own contraction, signed by the uniform rule and divided
by its *proved* symmetry factor, shown equal to the matrix expression of
Lin-Lindsey p. 42. Nothing here is definitional: the left sides come from graph
data, the right sides are matrix polynomials written independently. -/

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- `k = 0`: `-(G ⊙ v)`. -/
theorem contribution_ring0 (G v : Matrix (Fin N) (Fin N) F) (i j : Fin N) :
    contribution ring0 G v i j = -(G i j * v i j) := by
  rw [contribution, symmetry_ring0, contraction_ring0]
  simp [signFactor, ring0]

/-- `k = 1`: `+(1/2) • (G ⊙ (v * B * v))`, the `1/2` being `1/S` with `S = 2`. -/
theorem contribution_ring1 (G v : Matrix (Fin N) (Fin N) F) (i j : Fin N) :
    contribution ring1 G v i j = (1 / 2) * matrix1 G v i j := by
  rw [contribution, symmetry_ring1, contraction_ring1]
  simp [signFactor, ring1]
  ring

/-- `k = 2`: `-(1/4) • (G ⊙ (v * B * v * B * v))`, with `S = 4`. -/
theorem contribution_ring2 (G v : Matrix (Fin N) (Fin N) F) (i j : Fin N) :
    contribution ring2 G v i j = -(1 / 4) * matrix2 G v i j := by
  rw [contribution, symmetry_ring2, contraction_ring2]
  simp [signFactor, ring2]
  ring

/-! ### Exact rationals and their real interpretation

The evaluator is exact over `ℚ`; the cast lemma says the real-valued reading of
a rational diagram value is the diagram value of the real-valued matrices. The
contraction is a finite sum of finite products, so this is a `RingHom` image
statement, not an analytic one. -/

/-- Casting commutes with contraction. -/
theorem contraction_ratCast (D : FeynDiagram) (G v : Matrix (Fin N) (Fin N) ℚ)
    (i j : Fin N) :
    ((contraction D G v i j : ℚ) : ℝ)
      = contraction D (fun a b => ((G a b : ℚ) : ℝ)) (fun a b => ((v a b : ℚ) : ℝ)) i j := by
  show (Rat.castHom ℝ) (contraction D G v i j) = _
  simp only [contraction, edgeProd, map_sum, map_mul, map_list_prod, List.map_map,
    Function.comp_def]
  rfl

/-- Casting commutes with the full contribution, symmetry divisor included. -/
theorem contribution_ratCast (D : FeynDiagram) (G v : Matrix (Fin N) (Fin N) ℚ)
    (i j : Fin N) :
    ((contribution D G v i j : ℚ) : ℝ)
      = contribution D (fun a b => ((G a b : ℚ) : ℝ)) (fun a b => ((v a b : ℚ) : ℝ)) i j := by
  show (Rat.castHom ℝ) (contribution D G v i j) = _
  simp only [contribution, signFactor, map_div₀, map_mul, map_pow, map_neg, map_one,
    map_natCast]
  rw [show (Rat.castHom ℝ) (contraction D G v i j) = _ from contraction_ratCast D G v i j]

end GW.LL

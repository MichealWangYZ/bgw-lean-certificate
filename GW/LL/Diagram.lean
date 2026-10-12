/-
Lin-Lindsey Part I (arXiv:1809.02900v1): a finite half-edge diagram model for
the *classical real Gibbs model* of that paper.

SCOPE. This namespace is about the Gibbs-measure model of Lin and Lindsey. It
is NOT electronic GW, not BerkeleyGW, and not connected to `GW.GPP.*` in this
repository. The name `GW` here is the repository's Lean library root, not a
claim about the electronic GW approximation.

WHAT IS AND IS NOT DEFINED HERE. A diagram carries only combinatorial data:
which sites an edge joins, and whether the edge is a propagator (`G`) or an
interaction (`v`). Its numerical value is obtained by *contracting* that data --
summing over assignments of matrix indices to internal sites and multiplying the
factors read off each edge. The matrix expressions that the ring diagrams are
expected to equal are defined separately in `GW.LL.Ring` and are never used to
define contraction; otherwise the intended theorems would be tautologies.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

namespace GW.LL

/-- A site of a self-energy diagram with two distinguished external legs.

`extI` and `extJ` carry the two external labels of `Σ i j`. The task's
convention is that automorphisms fix them, *even when the numerical indices
assigned to them happen to coincide*: they are labels, not values. -/
inductive Site (n : ℕ) where
  | extI : Site n
  | extJ : Site n
  | int : Fin n → Site n
deriving DecidableEq, Repr

/-- `Site n` is finite: two external labels and `n` internal ones. -/
def siteEquivSum (n : ℕ) : (Fin 2 ⊕ Fin n) ≃ Site n where
  toFun x := match x with
    | .inl i => if i = 0 then Site.extI else Site.extJ
    | .inr m => Site.int m
  invFun s := match s with
    | .extI => .inl 0
    | .extJ => .inl 1
    | .int m => .inr m
  left_inv := by
    rintro (i | m)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by rintro (_ | _ | m) <;> rfl

instance instFintypeSite (n : ℕ) : Fintype (Site n) :=
  Fintype.ofEquiv _ (siteEquivSum n)

/-- Combinatorial data of a self-energy diagram: internal site count and the
propagator/interaction edge lists. Repeated entries are *parallel* edges and
are deliberately kept distinct (a `List`, not a `Finset`): the two propagators
of a bubble are different edges, and that is exactly what produces the
symmetry factor. -/
structure FeynDiagram where
  numInternal : ℕ
  propagators : List (Site numInternal × Site numInternal)
  interactions : List (Site numInternal × Site numInternal)

namespace FeynDiagram

variable {K : Type*} [CommRing K] {N : ℕ}

/-- The matrix index carried by a site, given the two external indices and an
assignment of indices to internal sites. -/
def siteIndex {n : ℕ} (i j : Fin N) (f : Fin n → Fin N) : Site n → Fin N
  | .extI => i
  | .extJ => j
  | .int m => f m

/-- Product of the factors read off one edge list. -/
def edgeProd {n : ℕ} (M : Matrix (Fin N) (Fin N) K) (i j : Fin N)
    (f : Fin n → Fin N) (es : List (Site n × Site n)) : K :=
  (es.map fun e => M (siteIndex i j f e.1) (siteIndex i j f e.2)).prod

/-- The contraction of a diagram: sum over all assignments of indices to the
internal sites of the product of the edge factors.

This is the *only* way a diagram acquires a number in this development. It
reads the edge lists and nothing else. -/
def contraction (D : FeynDiagram) (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  ∑ f : Fin D.numInternal → Fin N,
    edgeProd G i j f D.propagators * edgeProd v i j f D.interactions

/-! ### Automorphisms and the symmetry factor

Lin-Lindsey Definition 3.8 defines an automorphism of a labeled diagram as a
relabeling `g` with `g · Γ ≅ Γ`, and sets the symmetry factor `S_Γ = |Aut(Γ)|`.
Remark 3.9 notes these are exactly the self-isomorphisms of the unlabeled
diagram. For a self-energy diagram the two external labels are held fixed. -/

/-- The image edge of a relabeling joins the images of the endpoints. The
disjunction only normalises how the pair happens to be stored; it is NOT an
extra "edge reversal" symmetry. An edge carries one half-edge at each endpoint,
and a relabeling permutes half-edges within each site, so the image edge is
determined -- there is no orientation freedom to exploit.

SCOPE, narrowed after review. For an edge whose two endpoints are DISTINCT this
compressed representation has a demonstrated interpretation: for the three ring
diagrams below an explicit half-edge model gives the same automorphism counts.
It is **not** a proved general equivalence to all Lin-Lindsey half-edge
diagrams. `loopExample` below is a counterexample outside that family: a
self-loop's two flags may be exchanged while site and edge identifiers stay
fixed, so the true half-edge count is 2 while this representation counts 1.

Separately: the polynomial identities proved for the rings hold for ARBITRARY
matrix entries. Reading the stored-order disjunction as saying that reversing a
stored pair preserves the contracted VALUE is a different statement, and that
one does use symmetric `G` and `v`. The two must not be conflated. -/
def samePair {n : ℕ} (σ : Equiv.Perm (Site n)) (e f : Site n × Site n) : Prop :=
  (σ e.1 = f.1 ∧ σ e.2 = f.2) ∨ (σ e.1 = f.2 ∧ σ e.2 = f.1)

instance {n : ℕ} (σ : Equiv.Perm (Site n)) (e f : Site n × Site n) :
    Decidable (samePair σ e f) := by unfold samePair; infer_instance

/-- An automorphism: a site relabeling fixing both external labels, together
with permutations of the propagator and interaction edges carrying each edge to
an edge joining the images of its endpoints. Propagators may only go to
propagators, so the two edge kinds are never mixed. -/
def IsAut (D : FeynDiagram) (σ : Equiv.Perm (Site D.numInternal))
    (π : Equiv.Perm (Fin D.propagators.length))
    (ρ : Equiv.Perm (Fin D.interactions.length)) : Prop :=
  σ .extI = .extI ∧ σ .extJ = .extJ ∧
    (∀ e, samePair σ (D.propagators.get e) (D.propagators.get (π e))) ∧
    (∀ e, samePair σ (D.interactions.get e) (D.interactions.get (ρ e)))

instance (D : FeynDiagram) (σ π ρ) : Decidable (IsAut D σ π ρ) := by
  unfold IsAut; infer_instance

/-- The automorphism group of `D` in the compressed site/edge representation,
as a finite type.

**What its cardinality is, and is not.** For the ring family it is proved
faithful to the rings' explicit half-edge symmetries (`GW.LL.RingHalfEdge`),
and there it computes the symmetry factor `S_Γ` of Lin-Lindsey Definition 3.8.
For an ARBITRARY `FeynDiagram` it is not identified with `S_Γ`: the structure
records incidence only, does not enforce well-formed quartic incidence, and
cannot express an exchange of a propagator's two incidences when both land on
the same site -- see `GW.LL.selfLoopWitness`. Do not read
`Fintype.card (Aut D)` as a symmetry factor outside a family where the
correspondence has been proved. -/
def Aut (D : FeynDiagram) : Type :=
  {x : Equiv.Perm (Site D.numInternal) × Equiv.Perm (Fin D.propagators.length)
        × Equiv.Perm (Fin D.interactions.length) // IsAut D x.1 x.2.1 x.2.2}

instance (D : FeynDiagram) : DecidablePred
    (fun x : Equiv.Perm (Site D.numInternal) × Equiv.Perm (Fin D.propagators.length)
        × Equiv.Perm (Fin D.interactions.length) => IsAut D x.1 x.2.1 x.2.2) :=
  fun _ => inferInstance

instance (D : FeynDiagram) : Fintype (Aut D) :=
  Subtype.fintype _

instance (D : FeynDiagram) : DecidableEq (Aut D) := by unfold Aut; infer_instance

/-- When the site relabeling and the interaction permutation are forced to be
trivial, the automorphism group is carried entirely by the propagator
permutations. This is the reduction that makes the symmetry factor computable:
enumerating all triples is infeasible, while enumerating propagator
permutations alone is small. The two hypotheses are proved, not assumed. -/
def autEquivProps (D : FeynDiagram)
    (hσ : ∀ σ π ρ, IsAut D σ π ρ → σ = 1)
    (hρ : ∀ σ π ρ, IsAut D σ π ρ → ρ = 1) :
    Aut D ≃ {π : Equiv.Perm (Fin D.propagators.length) //
      ∀ e, samePair 1 (D.propagators.get e) (D.propagators.get (π e))} where
  toFun x := ⟨x.1.2.1, by
    have h := hσ _ _ _ x.2
    have hp := x.2.2.2.1
    rwa [h] at hp⟩
  invFun p := ⟨(1, p.1, 1), by
    refine ⟨rfl, rfl, p.2, ?_⟩
    intro e
    exact Or.inl ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have h1 := hσ _ _ _ x.2
    have h2 := hρ _ _ _ x.2
    obtain ⟨⟨σ, π, ρ⟩, hx⟩ := x
    simp only at h1 h2 ⊢
    rw [h1, h2]
  right_inv _ := rfl

/-- Sign rule: each interaction edge contributes a factor `-1`, because the
Gibbs weight expands `exp(-V)`. This is a stated rule applied uniformly, not a
per-diagram adjustment. -/
def signFactor (D : FeynDiagram) : K := (-1) ^ D.interactions.length

/-- The contribution of a diagram: its signed contraction divided by its
symmetry factor, exactly as Lin-Lindsey p. 43 sums `F_Γ / S_Γ`. The three
ingredients are kept separate: `contraction` reads the graph, `signFactor`
applies a uniform rule, and the divisor is the *computed* cardinality of the
automorphism group. -/
def contribution {K : Type*} [Field K] {N : ℕ} (D : FeynDiagram)
    (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  signFactor D * contraction D G v i j / (Fintype.card (Aut D) : K)

/-- The Feynman amplitude `F_Γ` of Lin-Lindsey p. 42: the signed contraction,
BEFORE dividing by the symmetry factor. Kept as its own definition so that the
four levels the task distinguishes -- contraction, amplitude, symmetry count,
final contribution -- are separate objects rather than one fused formula. -/
def amplitude {K : Type*} [CommRing K] {N : ℕ} (D : FeynDiagram)
    (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  signFactor D * contraction D G v i j

theorem contribution_eq_amplitude_div {K : Type*} [Field K] {N : ℕ}
    (D : FeynDiagram) (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    contribution D G v i j = amplitude D G v i j / (Fintype.card (Aut D) : K) := rfl

/-- `contribution` with the symmetry divisor supplied as a literal. Evaluating
`Fintype.card (Aut D)` at runtime would re-run the automorphism enumeration,
which is exactly the computation that is too large for ring 2. This form is
used by the executable evaluator and is tied to the real definition by
`contribution_eq_of_card` below, so the literal is certified, not assumed. -/
def contributionOf {K : Type*} [Field K] {N : ℕ} (S : ℕ) (D : FeynDiagram)
    (G v : Matrix (Fin N) (Fin N) K) (i j : Fin N) : K :=
  signFactor D * contraction D G v i j / (S : K)

theorem contribution_eq_of_card {K : Type*} [Field K] {N : ℕ} (D : FeynDiagram)
    (S : ℕ) (hS : Fintype.card (Aut D) = S) (G v : Matrix (Fin N) (Fin N) K)
    (i j : Fin N) : contribution D G v i j = contributionOf S D G v i j := by
  rw [contribution, contributionOf, hS]

end FeynDiagram

/-! ### Summation helper

Rewriting a sum over `Fin (n+1) → Fin N` as an outer sum over the first
coordinate. Applied repeatedly this turns a contraction into the nested sums
that a matrix product is built from. -/

variable {K : Type*} [AddCommMonoid K] {N n : ℕ}

theorem sum_over_pi_succ (g : (Fin (n + 1) → Fin N) → K) :
    (∑ f : Fin (n + 1) → Fin N, g f)
      = ∑ x : Fin N, ∑ f' : Fin n → Fin N, g (Fin.cons x f') := by
  -- `Fin.consEquiv` is mathlib's own `Fin.cons` as an `Equiv`
  -- (`Mathlib/Data/Fin/Tuple/Basic.lean`); specialised here to the constant
  -- family. An earlier revision reimplemented it locally, which review
  -- correctly flagged as avoidable duplication.
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp g, Fintype.sum_prod_type]
  rfl

end GW.LL

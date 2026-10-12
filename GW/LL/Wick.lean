/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C3 (first subtask): finite Wick pairings, normalized first-order moments,
and the Hartree/Fock split of the classical real Gibbs model of Lin-Lindsey
Part I (arXiv:1809.02900v1, sections 3-4).

## What is PROVED here, and what is ASSUMED

C1, C2A and C2B all begin from graph data that was *asserted* to be the right
graph data for this model. Nothing in them derives that data from the model's
moments. This file tests one order of that derivation, and it is the first
place in the development where the diagrams are connected to anything upstream.

**The Gaussian-integral / pairing-sum equivalence -- Wick's (Isserlis')
theorem -- is an INPUT, not a result.** The pinned mathlib v4.19.0 has no
Isserlis theorem and no multivariate Gaussian with a covariance matrix
(`Mathlib/Probability/Distributions/Gaussian.lean` is one-dimensional real),
which was checked by source inspection before this design was chosen. So
`wickMoment` below *defines* the moment functional as a sum over perfect
matchings. Everything downstream of that definition is proved; the definition
itself is where the physics enters on trust.

Nothing here formalizes Gaussian perturbation theory, and a reader must not
take it to have done so.

**The interaction normalization** `U = (1/8) * sum_{i,j} v i j * x i ^ 2 * x j ^ 2`
is recorded as the named definition `interactionWeight`. It is **correct**, and
its source is Part I section 2.1, equation (2.4), **printed page 5** -- verified
by the C3/C4 review, not by this file's author, who has still not read the PDF.
An earlier version of this comment pointed at printed p. 42, which is the ring
section and not where the normalization is stated.

`G` is a covariance and is therefore symmetric; that hypothesis is named
`hG` wherever it is used, never assumed silently.
-/
import GW.LL.Screening
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Notation

namespace GW.LL

open scoped Matrix

-- Characteristic zero is a standing modelling assumption (the 1/8 and 1/2 are
-- physical weights, not Lean's totalized division), carried by every statement
-- here including those whose proof does not need it.
set_option linter.unusedSectionVars false

variable {ι : Type*}

/-! ### Perfect matchings of a finite list

`select` is the standard "pick one element, keep the rest" helper; `pairings`
uses it to enumerate perfect matchings. The enumeration is primary and the
Wick recursion is derived from it (`wickMoment_cons`), not the other way
round. Fuel equal to the list length keeps the recursion structural. -/

/-- Every way to remove one element, paired with the remainder. -/
def select : List ι → List (ι × List ι)
  | [] => []
  | a :: t => (a, t) :: (select t).map (fun p => (p.1, a :: p.2))

/-- All perfect matchings of `l`, as lists of pairs. Empty when `l` is odd. -/
def pairingsAux : ℕ → List ι → List (List (ι × ι))
  | _, [] => [[]]
  | 0, _ :: _ => []
  | n + 1, a :: rest =>
      (select rest).flatMap fun p => (pairingsAux n p.2).map fun m => (a, p.1) :: m

/-- All perfect matchings of `l`. -/
def pairings (l : List ι) : List (List (ι × ι)) := pairingsAux l.length l

/-- The involution induced by a matching: each paired position maps to its
partner. Used only to check `pairings` against an independent notion of
"perfect matching". -/
def matchFun {n : ℕ} (m : List (Fin n × Fin n)) (x : Fin n) : Fin n :=
  m.foldl (fun acc p => if p.1 = x then p.2 else if p.2 = x then p.1 else acc) x

/-! ### `pairings` really enumerates the perfect matchings

`pairings` is defined by a recursion, so on its own it is not evidence that it
enumerates what it claims to. These four facts check it at the arity this file
actually uses, against the independent characterization "fixed-point-free
involution". They are decided, not asserted.

The Wick recursion itself (`wickMoment_cons`) IS general. What is checked only
at arity six is the correspondence between `pairings` and fixed-point-free
involutions. -/

/-- Fifteen matchings of six positions, as `(6-1)!! = 15` requires. -/
theorem pairings_length_six : (pairings (List.finRange 6)).length = 15 := by decide

/-- Every enumerated matching is a fixed-point-free involution. -/
theorem pairings_six_fpf_involutive :
    ∀ m ∈ pairings (List.finRange 6),
      (∀ x, matchFun m (matchFun m x) = x) ∧ (∀ x, matchFun m x ≠ x) := by decide

/-- No matching is enumerated twice. -/
theorem pairings_six_nodup :
    ((pairings (List.finRange 6)).map (fun m => (List.finRange 6).map (matchFun m))).Nodup := by
  decide

set_option maxRecDepth 8000 in
/-- **Completeness.** Every fixed-point-free involution of `Fin 6` is realized
by one of the enumerated matchings, so `pairings` misses none. Decided over all
720 permutations of `Fin 6`. -/
theorem pairings_six_complete (σ : Equiv.Perm (Fin 6))
    (hinv : ∀ x, σ (σ x) = x) (hfpf : ∀ x, σ x ≠ x) :
    (List.finRange 6).map σ
      ∈ (pairings (List.finRange 6)).map (fun m => (List.finRange 6).map (matchFun m)) := by
  revert σ
  decide

/-! ### The Wick recursion, derived from the enumeration

The enumeration is primary; these derive the familiar recursion from it for
lists of ANY length, so the claim in the file header is a theorem rather than a
description. -/

theorem select_length : ∀ {l : List ι} {p : ι × List ι},
    p ∈ select l → p.2.length + 1 = l.length
  | [], _, h => by simp [select] at h
  | _ :: t, p, h => by
      rw [select, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        have := select_length hq
        simp only [List.length_cons]
        omega

/-- The fuel is irrelevant once it covers the list. -/
theorem pairingsAux_fuel : ∀ (n : ℕ) (l : List ι), l.length ≤ n →
    pairingsAux n l = pairingsAux l.length l
  | _, [], _ => by cases ‹ℕ› <;> rfl
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: t, h => by
      have hlen : t.length ≤ n := by simpa using h
      simp only [pairingsAux, List.length_cons]
      refine List.flatMap_congr fun p hp => ?_
      have hp2 : p.2.length ≤ n := by have := select_length hp; omega
      have hp2' : p.2.length ≤ t.length := by have := select_length hp; omega
      rw [pairingsAux_fuel n p.2 hp2, pairingsAux_fuel t.length p.2 hp2']
  termination_by n l => (n, l.length)

theorem pairings_cons (a : ι) (rest : List ι) :
    pairings (a :: rest)
      = (select rest).flatMap fun p => (pairings p.2).map fun m => (a, p.1) :: m := by
  rw [pairings, List.length_cons, pairingsAux]
  refine List.flatMap_congr fun p hp => ?_
  have h := select_length hp
  rw [pairings, pairingsAux_fuel rest.length p.2 (by omega)]

private theorem sum_map_flatMap {α β : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! ### The moment functional -/

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- The pairing sum: `sum over perfect matchings of prod of covariances`.

This is Wick's theorem taken as a DEFINITION; see the file header. -/
def wickMoment (G : Matrix (Fin N) (Fin N) K) (l : List (Fin N)) : K :=
  ((pairings l).map fun m => (m.map fun p => G p.1 p.2).prod).sum

/-- The paper's quartic interaction normalization. Source: Part I section 2.1,
equation (2.4), printed page 5 (verified by the C3/C4 review, not by the
implementer). -/
def interactionWeight : K := 1 / 8

/-- **The Wick recursion**, for a list of any length: pair the head with each
remaining element and recurse on what is left. Derived from the enumeration,
not assumed. -/
theorem wickMoment_cons (G : Matrix (Fin N) (Fin N) K) (a : Fin N)
    (rest : List (Fin N)) :
    wickMoment G (a :: rest)
      = ((select rest).map fun p => G a p.1 * wickMoment G p.2).sum := by
  rw [wickMoment, pairings_cons, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [wickMoment, List.map_map]
  simp only [Function.comp_def, List.map_cons, List.prod_cons]
  exact List.sum_map_mul_left _ _ _

theorem wickMoment_pair (G : Matrix (Fin N) (Fin N) K) (a b : Fin N) :
    wickMoment G [a, b] = G a b := by
  simp [wickMoment, pairings, pairingsAux, select]

/-- `<x_i^2 x_j^2>`: one direct pairing and two crossed ones. -/
theorem wickMoment_quartic (G : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    wickMoment G [i, i, j, j] = G i i * G j j + 2 * (G i j * G i j) := by
  simp [wickMoment, pairings, pairingsAux, select]
  ring

/-! ### The six-point moment and its connected part -/

/-- The part of `<x_a x_b x_i^2 x_j^2>` in which `a` is NOT paired with `b`.

Twelve of the fifteen matchings. No symmetry hypothesis on `G` is needed to
split them off. -/
def connected6 (G : Matrix (Fin N) (Fin N) K) (a b i j : Fin N) : K :=
  2 * (G a i * G b i * G j j) + 2 * (G a j * G b j * G i i)
    + 4 * (G a i * G b j * G i j) + 4 * (G a j * G b i * G i j)

/-- The six-point moment splits into the `a`-`b` pairing times the quartic
moment, plus the connected remainder. This is the whole combinatorial input to
the cancellation below. -/
theorem wick6_split (G : Matrix (Fin N) (Fin N) K) (a b i j : Fin N) :
    wickMoment G [a, b, i, i, j, j]
      = G a b * wickMoment G [i, i, j, j] + connected6 G a b i j := by
  simp [wickMoment, pairings, pairingsAux, select, connected6]
  ring

/-! ### The normalized first-order correction

`<x_a x_b U>` alone is not the first-order correction: the partition function
contributes `-<x_a x_b><U>`, and the two must cancel on the disconnected
matchings. That cancellation is `disconnected_cancels`, and it is proved, not
observed on examples. -/

variable (G v : Matrix (Fin N) (Fin N) K)

/-- `<x_a x_b U>` with `U = (1/8) sum v i j x_i^2 x_j^2`. -/
def momentWithInteraction (a b : Fin N) : K :=
  ∑ i, ∑ j, (interactionWeight : K) * v i j * wickMoment G [a, b, i, i, j, j]

/-- `<x_a x_b> <U>`, the normalization subtraction. -/
def disconnectedPart (a b : Fin N) : K :=
  ∑ i, ∑ j, (interactionWeight : K) * v i j * (G a b * wickMoment G [i, i, j, j])

/-- The normalized first-order correction to `<x_a x_b>`. -/
def firstOrder (a b : Fin N) : K :=
  -(momentWithInteraction G v a b - disconnectedPart G v a b)

/-- **Disconnected terms cancel exactly.** Every matching pairing `a` with `b`
is removed by the partition-function normalization, for every `i`, `j`. -/
theorem disconnected_cancels (a b : Fin N) :
    firstOrder G v a b
      = -∑ i, ∑ j, (interactionWeight : K) * v i j * connected6 G a b i j := by
  simp only [firstOrder, momentWithInteraction, disconnectedPart,
    ← Finset.sum_sub_distrib, ← mul_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [wick6_split]
  ring

/-! ### Hartree and Fock

With `G` a genuine covariance (symmetric) and `v` symmetric, the twelve
connected matchings collapse into exactly two matrix expressions. The `1/2`
in front of the Hartree term is the surviving remnant of the interaction's
`1/8`; it is not inserted by hand. -/

/-- `(v d)_i` with `d_k = G k k`: the closed propagator loop attached at `i`. -/
def loopVec (i : Fin N) : K := ∑ j, v i j * G j j

/-- The Hartree ("tadpole") matrix `G · diag(v d) · G`. -/
def hartreeMatrix : Matrix (Fin N) (Fin N) K :=
  G * Matrix.diagonal (loopVec G v) * G

/-- The Fock ("exchange") matrix `G · (v ⊙ G) · G`. -/
def fockMatrix : Matrix (Fin N) (Fin N) K := G * (v ⊙ G) * G

/-- `hartreeMatrix` entrywise: the closed loop at `i` weighted by `v i j`. -/
theorem hartreeMatrix_apply (a b : Fin N) :
    hartreeMatrix G v a b = ∑ i, ∑ j, G a i * (v i j * G j j) * G i b := by
  rw [hartreeMatrix, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, loopVec, Finset.mul_sum, Finset.sum_mul]

/-- `fockMatrix` entrywise: the exchange line `v i j * G i j` between `i`, `j`. -/
theorem fockMatrix_apply (a b : Fin N) :
    fockMatrix G v a b = ∑ i, ∑ j, G a i * (v i j * G i j) * G j b := by
  simp only [fockMatrix, Matrix.mul_apply, Matrix.hadamard_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Relabelling `i` and `j` inside a `v`-weighted double sum, for symmetric `v`. -/
private theorem sum_swap_of_isSymm (hv : v.IsSymm) (f : Fin N → Fin N → K) :
    (∑ i, ∑ j, v i j * f i j) = ∑ i, ∑ j, v i j * f j i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [hv.apply]

/-- **The first-order correction is Hartree plus Fock.**

`δ⟨x_a x_b⟩ = -( ½ (G · diag(v d) · G)_ab + (G · (v ⊙ G) · G)_ab )`.

The `½` is what the interaction's `1/8` becomes once the twelve connected
matchings are collected; it is not inserted by hand. -/
theorem firstOrder_eq_hartree_fock (hG : G.IsSymm) (hv : v.IsSymm) (a b : Fin N) :
    firstOrder G v a b
      = -((2⁻¹ : K) * hartreeMatrix G v a b + fockMatrix G v a b) := by
  have hA : ∀ f : Fin N → Fin N → K, _ := fun f => sum_swap_of_isSymm v hv f
  rw [disconnected_cancels]
  have hcon : ∀ i j : Fin N, (interactionWeight : K) * v i j * connected6 G a b i j
      = v i j * ((8⁻¹ : K) * (2 * (G a i * G b i * G j j)))
        + v i j * ((8⁻¹ : K) * (2 * (G a j * G b j * G i i)))
        + v i j * ((8⁻¹ : K) * (4 * (G a i * G b j * G i j)))
        + v i j * ((8⁻¹ : K) * (4 * (G a j * G b i * G i j))) := by
    intro i j
    simp only [interactionWeight, connected6]
    ring
  simp only [hcon, Finset.sum_add_distrib]
  have h1 : (∑ i, ∑ j, v i j * ((8⁻¹ : K) * (2 * (G a j * G b j * G i i))))
          = ∑ i, ∑ j, v i j * ((8⁻¹ : K) * (2 * (G a i * G b i * G j j))) :=
    (hA fun i j => (8⁻¹ : K) * (2 * (G a i * G b i * G j j))).symm
  have h2 : (∑ i, ∑ j, v i j * ((8⁻¹ : K) * (4 * (G a j * G b i * G i j))))
          = ∑ i, ∑ j, v i j * ((8⁻¹ : K) * (4 * (G a i * G b j * G i j))) := by
    rw [(hA fun i j => (8⁻¹ : K) * (4 * (G a i * G b j * G i j)))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [hG.apply j i]
  have hh : (∑ i, ∑ j, v i j * ((8⁻¹ : K) * (2 * (G a i * G b i * G j j))))
          = (4⁻¹ : K) * hartreeMatrix G v a b := by
    rw [hartreeMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG.apply i b]
    ring
  have hf : (∑ i, ∑ j, v i j * ((8⁻¹ : K) * (4 * (G a i * G b j * G i j))))
          = (2⁻¹ : K) * fockMatrix G v a b := by
    rw [fockMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG.apply j b]
    ring
  rw [h1, h2, hh, hf]
  ring

/-! ### The link back to the ring family

This is the point of the whole file. C1/C2A/C2B started from ring graph data
that was asserted to be the right data. Here the order-zero ring contribution
is *recovered* from the model's moments, and what the ring family leaves out
is identified. -/

/-- C2A's order-zero ring contribution, as a matrix. -/
def ring0Matrix : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => FeynDiagram.contribution (ring 0) G v i j

theorem ring0Matrix_eq : ring0Matrix G v = -(v ⊙ G) := by
  funext i j
  rw [ring0Matrix, Matrix.of_apply, contribution_ring]
  simp [Matrix.hadamard_apply]
  ring

/-- **The Fock term is the dressed order-zero ring.** The exchange part of the
first-order correction is exactly C2A's `contribution (ring 0)` with an
external propagator on each side. -/
theorem dressed_ring0_eq_neg_fock :
    G * ring0Matrix G v * G = -fockMatrix G v := by
  rw [ring0Matrix_eq, fockMatrix]
  simp [Matrix.mul_neg, Matrix.neg_mul]

/-- The first-order correction, split into the part the ring family accounts
for and the part it does not. -/
theorem firstOrder_eq_dressed_ring0_add_hartree
    (hG : G.IsSymm) (hv : v.IsSymm) (a b : Fin N) :
    firstOrder G v a b
      = (G * ring0Matrix G v * G) a b - (2⁻¹ : K) * hartreeMatrix G v a b := by
  rw [firstOrder_eq_hartree_fock G v hG hv, dressed_ring0_eq_neg_fock]
  simp only [Matrix.neg_apply]
  ring

/-- The Hartree term is not a harmless zero: there are symmetric `G`, `v` for
which it is nonzero, so the ring family genuinely does not exhaust the
first-order correction. This is the concrete content of C2B's remark that a
graph-derived Hartree contribution was outside its scope. -/
theorem hartreeMatrix_ne_zero :
    hartreeMatrix (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [hartreeMatrix, loopVec, Matrix.mul_apply, Matrix.one_apply,
    Fin.sum_univ_two] at h00

end GW.LL

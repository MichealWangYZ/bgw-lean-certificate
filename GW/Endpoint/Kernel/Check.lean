/-
G2 stage 1: a kernel-executable checker for the eps⁻¹ certificate of
`bgw/endpoint/cert.py` (`epsinv_iv` → `iv.inverse_cw`).

Everything is exact integer arithmetic on dyadic fixed-point data: a matrix
`M : List (List ℤ)` with scale `S` stands for the real matrix `M i j / 2^S`.
No rounding happens in Lean: the certificate's hints (`F`, `T0`, `T1`, `T2`,
`beta`, `rho`, `tail`, and the offset/midpoint encodings `mid2`, `rad2`,
`colM`, `Rabs`, produced by `bgw/endpoint/kernel_export.py`) are only
compared against exactly recomputed sums, so the checker trusts no Python
arithmetic. Soundness: `GW.Endpoint.Kernel.Cert.sound` (file `Sound.lean`).

Kernel-speed choices (measured, see `.agent/handoffs/G2-kernel-cert.md`):
* definitions use `List.rec` directly, not equation-compiled recursion
  (~1.7x faster kernel reduction); they are `noncomputable` only because the
  code generator does not support `List.rec` — they are for `decide +kernel`;
* all O(n³) work is `ℕ` multiply-adds (the kernel's GMP-accelerated `Nat.add`
  / `Nat.mul`); signed products are ~3.5x slower (`Int` has no kernel
  acceleration), so the signed product `R · mid(A)` is formed as
  `(R + MR) · (mid + M)` in `ℕ` and corrected by O(n) terms;
* the work is split into one row per theorem: a conjunction of k rows in one
  declaration is superlinear in k in the kernel (16 rows: 23 s vs 3 s).
-/
import Mathlib.Data.List.Basic

namespace GW.Endpoint.Kernel

/-- `acc_j + c * y_j`, truncated to the shorter list. -/
noncomputable def axpy {α : Type} [Add α] [Mul α] (c : α) (acc : List α) : List α → List α :=
  List.rec (motive := fun _ => List α → List α) (fun _ => [])
    (fun a _ ih ys => List.casesOn (motive := fun _ => List α) ys []
      (fun y ys' => (a + c * y) :: ih ys')) acc

/-- Pointwise `g`, truncated to the shorter list. -/
noncomputable def zipW {α β γ : Type} (g : α → β → γ) (l1 : List α) : List β → List γ :=
  List.rec (motive := fun _ => List β → List γ) (fun _ => [])
    (fun a _ ih ys => List.casesOn (motive := fun _ => List γ) ys []
      (fun y ys' => g a y :: ih ys')) l1

/-- `acc + ∑_k c_k * Y_k`: row `i` of a matrix product when `cs` is row `i` of
the left factor and `Ys` the rows of the right one. -/
noncomputable def comb {α : Type} [Add α] [Mul α] (cs : List α) :
    List α → List (List α) → List α :=
  List.rec (motive := fun _ => List α → List (List α) → List α) (fun acc _ => acc)
    (fun c _ ih acc Ys => List.casesOn (motive := fun _ => List α) Ys acc
      (fun y Ys' => ih (axpy c acc y) Ys')) cs

/-- Equal lengths and `p (l1 j) (l2 j)` for every `j`. -/
noncomputable def all2 {α β : Type} (p : α → β → Bool) (l1 : List α) : List β → Bool :=
  List.rec (motive := fun _ => List β → Bool)
    (fun ys => List.casesOn (motive := fun _ => Bool) ys true (fun _ _ => false))
    (fun a _ ih ys => List.casesOn (motive := fun _ => Bool) ys false
      (fun y ys' => p a y && ih ys')) l1

/-- `s + ∑ l`, accumulated left to right. -/
noncomputable def sumL {α : Type} [Add α] (l : List α) : α → α :=
  List.rec (motive := fun _ => α → α) (fun s => s) (fun a _ ih s => ih (s + a)) l

/-- The unit row `d · e_i` of length `n`. -/
def unitRow (n i : ℕ) (d : ℤ) : List ℤ := (List.range n).map fun j => if j = i then d else 0

/-- `n` rows, each of length `n`. -/
def shapeOK {α : Type} (n : ℕ) (M : List (List α)) : Bool :=
  M.length == n && M.all fun r => r.length == n

/-- The certificate of one q-point.

Statement data: `epsLo, epsHi` (scale `2^-SE`, cert.py's `eps.lo`, `eps.hi`),
`outLo, outHi` (scale `2^-SO`, the claimed enclosure of eps⁻¹), the balancing
exponents `f` (cert.py's `s_i` is `2^(f_i)` up to one common factor, which
cancels). Certificate data: `R` (scale `2^-SR`, the approximate inverse of the
balanced matrix), hints at scale `2^-K`, and the ℕ encodings `mid2 = lo + hi +
M`, `rad2 = hi - lo`, `colM_j = ∑_k mid2_kj`, `Rabs = |R|`; `MR` offsets the
balanced `R` to ℕ; `G ≥ f_i`. -/
structure Cert where
  n : ℕ
  K : ℕ
  SE : ℕ
  SR : ℕ
  SO : ℕ
  G : ℕ
  M : ℕ
  MR : ℕ
  f : List ℕ
  epsLo : List (List ℤ)
  epsHi : List (List ℤ)
  mid2 : List (List ℕ)
  rad2 : List (List ℕ)
  colM : List ℕ
  R : List (List ℤ)
  Rabs : List (List ℕ)
  outLo : List (List ℤ)
  outHi : List (List ℤ)
  F : List (List ℕ)
  T0 : List (List ℕ)
  T1 : List (List ℕ)
  T2 : List (List ℕ)
  beta : ℕ
  rho : ℕ
  tail : ℕ

namespace Cert

variable (c : Cert)

/-- The balanced row `c_k = R_ik 2^(G - f_k)`, offset by `MR` (as an integer). -/
def cOff (r : ℤ) (fk : ℕ) : ℤ := r * Int.ofNat (2 ^ (c.G - fk)) + Int.ofNat c.MR

/-- Entry test of the `E` row: `2^K (|δ - X 2^f| + Y 2^f) ≤ F 2^S1`, where
`X = Z - MR colM - M Σc' + n MR M` is (twice) the exact `(R · mid A')_ij` and
`Y` (twice) the `|R| · rad A'` bound, all at scale `2^-S1`. -/
def eOK (S1 : ℕ) (sc : ℕ) (Fij : ℕ) (q : ℕ × ℕ × ℕ × ℕ × ℤ) : Bool :=
  let X : ℤ := Int.ofNat q.1 - Int.ofNat (c.MR * q.2.1) - Int.ofNat (c.M * sc) +
    Int.ofNat (c.n * c.MR * c.M)
  decide (2 ^ c.K * ((q.2.2.2.2 - X * Int.ofNat (2 ^ q.2.2.2.1)).natAbs +
    q.2.2.1 * 2 ^ q.2.2.2.1) ≤ Fij * 2 ^ S1)

/-- Row check of `F ≥ |1 - R A'|` over the whole interval (`A'` the balanced
eps). O(n²): two ℕ row combinations. -/
noncomputable def chkE (i : ℕ) : Bool :=
  let S1 := c.SR + c.SE + c.G + 1
  let co := zipW c.cOff (c.R.getD i []) c.f
  let cs := zipW (fun x (_ : ℕ) => Int.toNat x) co c.f
  let ca := zipW (fun a fk => a * 2 ^ (c.G - fk)) (c.Rabs.getD i []) c.f
  let Z := comb cs (List.replicate c.n 0) c.mid2
  let Y := comb ca (List.replicate c.n 0) c.rad2
  (co.all fun x => decide (0 ≤ x)) &&
  all2 (c.eOK S1 (sumL cs 0)) (c.F.getD i [])
    (zipW Prod.mk Z (zipW Prod.mk c.colM (zipW Prod.mk Y (zipW Prod.mk c.f
      (unitRow c.n i (Int.ofNat (2 ^ S1)))))))

/-- Row check of `(F Y)_ij ≤ T_ij 2^SY` (`F` at scale K, `Y` at `SY`, `T` at K). -/
noncomputable def chkMul (SY : ℕ) (Y T : List (List ℕ)) (i : ℕ) : Bool :=
  all2 (fun t s => decide (s ≤ t * 2 ^ SY)) (T.getD i [])
    (comb (c.F.getD i []) (List.replicate c.n 0) Y)

/-- Entry check of the claimed enclosure against `[R - B, R + B] · s_i / s_j`. -/
def outOK (fi fj : ℕ) (r lo hi : ℤ) (b : ℕ) : Bool :=
  decide (lo * Int.ofNat (2 ^ (c.SR + c.K + fj)) ≤
      (r * Int.ofNat (2 ^ c.K) - Int.ofNat (b * 2 ^ c.SR)) * Int.ofNat (2 ^ (c.SO + fi))) &&
  decide ((r * Int.ofNat (2 ^ c.K) + Int.ofNat (b * 2 ^ c.SR)) * Int.ofNat (2 ^ (c.SO + fi)) ≤
      hi * Int.ofNat (2 ^ (c.SR + c.K + fj)))

/-- Entry check of the encodings: `mid2 = lo + hi + M`, `rad2 = hi - lo`. -/
def encOK (p : ℤ × ℤ) (q : ℕ × ℕ) : Bool :=
  decide (p.1 + p.2 + Int.ofNat c.M = Int.ofNat q.1) && decide (p.2 - p.1 = Int.ofNat q.2)

/-- The O(n) checks of row `i`: encodings, `Rabs`, row sums of `F` and `T0`,
and the claimed output enclosure with `B = T0 + T1 + T2 + tail`. -/
noncomputable def chkRow (i : ℕ) : Bool :=
  let fi := c.f.getD i 0
  all2 c.encOK (zipW Prod.mk (c.epsLo.getD i []) (c.epsHi.getD i []))
    (zipW Prod.mk (c.mid2.getD i []) (c.rad2.getD i [])) &&
  all2 (fun r a => decide (Int.natAbs r = a)) (c.R.getD i []) (c.Rabs.getD i []) &&
  decide (sumL (c.F.getD i []) 0 ≤ c.beta) && decide (sumL (c.T0.getD i []) 0 ≤ c.rho) &&
  all2 (fun fj (q : (ℤ × ℤ × ℤ) × ℕ) => c.outOK fi fj q.1.1 q.1.2.1 q.1.2.2 q.2) c.f
    (zipW Prod.mk (zipW Prod.mk (c.R.getD i []) (zipW Prod.mk (c.outLo.getD i [])
      (c.outHi.getD i [])))
      (zipW (· + ·) (zipW (· + ·) (c.T0.getD i []) (zipW (· + ·) (c.T1.getD i [])
        (c.T2.getD i []))) (List.replicate c.n c.tail)))

/-- The global checks: shapes, `G ≥ f`, `colM` the column sums of `mid2`,
`β < 1`, and the tail `tail ≥ β³ ρ / (1 - β)`. -/
noncomputable def chkGlobal : Bool :=
  shapeOK c.n c.epsLo && shapeOK c.n c.epsHi && shapeOK c.n c.mid2 && shapeOK c.n c.rad2 &&
  shapeOK c.n c.R && shapeOK c.n c.Rabs && shapeOK c.n c.outLo && shapeOK c.n c.outHi &&
  shapeOK c.n c.F && shapeOK c.n c.T0 && shapeOK c.n c.T1 && shapeOK c.n c.T2 &&
  c.f.length == c.n && c.f.all (· ≤ c.G) &&
  all2 (fun a b => a == b) c.colM (comb (List.replicate c.n 1) (List.replicate c.n 0) c.mid2) &&
  decide (c.beta < 2 ^ c.K) &&
  decide (c.beta ^ 3 * c.rho ≤ c.tail * ((2 ^ c.K - c.beta) * 2 ^ (2 * c.K)))

/-- Everything the soundness theorem needs, as one proposition. The data files
prove it from one kernel-checked theorem per row and per check. -/
def Valid : Prop :=
  c.chkGlobal = true ∧ ∀ i < c.n, c.chkE i = true ∧ c.chkMul c.SR c.Rabs c.T0 i = true ∧
    c.chkMul c.K c.T0 c.T1 i = true ∧ c.chkMul c.K c.T1 c.T2 i = true ∧ c.chkRow i = true

end Cert

/-- Assemble `∀ i < k + 1, p i` from `∀ i < k, p i` and `p k` (used by the
generated files to collect the per-row theorems). -/
theorem forall_lt_succ_of {p : ℕ → Prop} {k : ℕ} (h : ∀ i < k, p i) (hk : p k) :
    ∀ i < k + 1, p i := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · exact h i h'
  · exact hk

theorem forall_lt_zero (p : ℕ → Prop) : ∀ i < 0, p i := fun _ h => absurd h (Nat.not_lt_zero _)

end GW.Endpoint.Kernel

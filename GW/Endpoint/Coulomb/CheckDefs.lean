/-
G2-coulomb: the kernel-evaluated definitions (core Lean only, no Mathlib, so that the heavy
data modules load fast and stay small in memory).

* `gmRule d` — the Grundmann–Möller rule of odd degree `d` on `T2` (nodes `(a/m, b/m)`, weights
  `W / WCc`), `ruleOK` — its exactness check on all monomials of degree `≤ d`;
* `treeChk qc k t` — the enclosure of one triangle integral
  `J = ∫_{T2} |y(s)|_B^{-k} ds` from a quadtree `t` whose leaves carry a rule degree and a hint
  `tn` (`t ≤ tn / 2^TB`) [and, for `k = 1`, nothing else: square roots are computed and
  verified]; `qc` are the integer Gram numerators of `y(s) = a₀ + s₁ d₁ + s₂ d₂`.

Semantics (proved in `CheckSound.lean`): for `k = 1` or `k = 2`, if
`treeChk qc k t 0 0 0 false = some (lo, hi)` then `lo ≤ 2^K · WCc · J / sD^k ≤ hi`, with
`K = KB` for `k = 2` and `K = KB1` for `k = 1`, whenever every rule degree is certified
(`ruleOK` for each `d ∈ degList`) and `|a₀|² = q00/sD²`, `⟨a₀,d₁⟩ = q01/sD²`, … .
The Python image is `bgw/endpoint/coulomb_export.py` (`mirror_tri`).
-/

namespace GW.Endpoint.Coulomb

/-- Factorial (core Lean has none; `fact_eq` relates it to `Nat.factorial`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- A cubature node `(a/m, b/m)` with weight `W / WC`. -/
structure GNode where
  a : Nat
  b : Nat
  m : Nat
  W : Int
deriving DecidableEq, Repr

/-- The common weight denominator (lcm over the degrees 3..31). -/
def WCc : Nat := 282534584799830658138747693382332579840000000

/-- Nodes `(2β₁+1, 2β₂+1)/M` of one level, `|β| = n`. -/
def gmLevel (n M : Nat) (W : Int) : List GNode :=
  (List.range (n + 1)).flatMap fun b1 => (List.range (n + 1 - b1)).map fun b2 => ⟨2 * b1 + 1, 2 * b2 + 1, M, W⟩

/-- The Grundmann–Möller rule of degree `d` (odd): level `i` has `M = d + 2 - 2i`, weight
`(-1)^i M^d / (2^(2s) i! (d+2-i)!)` (times `WCc`, exact division checked by `ruleOK`). -/
def gmRule (d : Nat) : List GNode :=
  (List.range ((d - 1) / 2 + 1)).flatMap fun i =>
    gmLevel ((d - 1) / 2 - i) (d + 2 - 2 * i)
      ((if i % 2 = 0 then 1 else -1) *
        (((d + 2 - 2 * i) ^ d * WCc / (2 ^ (2 * ((d - 1) / 2)) * fact i * fact (d + 2 - i)) : Nat) : Int))

/-- A common multiple of the node denominators. -/
def gmM (d : Nat) : Nat :=
  (List.range ((d - 1) / 2 + 1)).foldl (fun acc i => Nat.lcm acc (d + 2 - 2 * i)) 1

/-- Every node in `T2`, `m ∣ M`. -/
def nodesOK (M : Nat) (r : List GNode) : Bool :=
  r.all fun n => decide (0 < n.m) && decide (n.a + n.b ≤ n.m) && decide (M % n.m = 0)

/-- Row `i` of the monomial checks: `(i+j+2)! Σ W a^i b^j (M/m)^(i+j) = WC i! j! M^(i+j)`. -/
def ruleRow (d WC M : Nat) (r : List GNode) (i : Nat) : Bool :=
  (List.range (d + 1 - i)).all fun j =>
    decide (((fact (i + j + 2) : Nat) : Int) *
        (r.map fun n => n.W * ((n.a ^ i * n.b ^ j * (M / n.m) ^ (i + j) : Nat) : Int)).sum =
      ((WC * fact i * fact j * M ^ (i + j) : Nat) : Int))

/-- The kernel check of a rule. -/
def ruleOK (d WC M : Nat) (r : List GNode) : Bool :=
  nodesOK M r && decide (0 < M) && decide (0 < WC) && (List.range (d + 1)).all (ruleRow d WC M r)

/-- `Σ |W|`. -/
def gAbs (r : List GNode) : Nat := (r.map fun n => n.W.natAbs).sum

/-! ### The triangle checker -/

/-- Fixed-point bits: `k = 2` (division), `k = 1` (square roots). -/
def KB : Nat := 300
def KB1 : Nat := 200
/-- Bits of the `t` hints. -/
def TB : Nat := 16

/-- Integer Gram numerators of a triangle: `|a₀|², ⟨a₀,d₁⟩, ⟨a₀,d₂⟩, |d₁|², ⟨d₁,d₂⟩, |d₂|²`. -/
structure QC where
  q00 : Int
  q01 : Int
  q02 : Int
  q11 : Int
  q12 : Int
  q22 : Int
deriving DecidableEq, Repr

/-- A quadtree over `T2`: a leaf carries the rule degree and the `t` hint. -/
inductive QT where
  | leaf (d tn : Nat)
  | node (c0 c1 c2 c3 : QT)
deriving Repr

/-- The leaf Gram numerators (scaled by `H² = 4^j`) of `s' ↦ y(p/H + e s'/H)`, `e = ±1`. -/
structure LQ where
  l00 : Int
  l01 : Int
  l02 : Int
  l11 : Int
  l12 : Int
  l22 : Int

def leafLQ (qc : QC) (j : Nat) (p1 p2 : Int) (e : Bool) : LQ :=
  let H : Int := (2 ^ j : Nat)
  let sg : Int := if e then -1 else 1
  ⟨qc.q00 * H * H + 2 * qc.q01 * p1 * H + 2 * qc.q02 * p2 * H + qc.q11 * p1 * p1 +
      2 * qc.q12 * p1 * p2 + qc.q22 * p2 * p2,
    sg * (qc.q01 * H + qc.q11 * p1 + qc.q12 * p2),
    sg * (qc.q02 * H + qc.q12 * p1 + qc.q22 * p2),
    qc.q11, qc.q12, qc.q22⟩

/-- `m² H² |y(a/m, b/m)|² sD²` for the leaf. -/
def nodeN (L : LQ) (a b m : Int) : Int :=
  m * m * L.l00 + 2 * m * (a * L.l01 + b * L.l02) + a * a * L.l11 + 2 * a * b * L.l12 + b * b * L.l22

/-- `9 H² |v - c|² sD²` for the offsets `(u, v)` of the three vertices from the centre. -/
def offR (L : LQ) (u v : Int) : Int := u * u * L.l11 + 2 * u * v * L.l12 + v * v * L.l22

/-- `φ_d(tn/2^TB) = pn / pd`. -/
def phiN (d tn : Nat) : Nat := (d + 2) * tn ^ (d + 1) * 2 ^ TB + (d + 1) * tn ^ (d + 2)
def phiD (d tn : Nat) : Nat := 2 ^ (TB * d) * (2 ^ TB - tn) ^ 2

/-- Floor square root by Newton (decreasing phase), with fuel; verified by the caller. -/
def isqrtD : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | f + 1, n, g =>
    let g' := (g + n / g) / 2
    bif Nat.blt g' g then isqrtD f n g' else g

/-- One unconditional Newton step (which lands at or above `⌊√n⌋`), then the decreasing phase. -/
def isqrtN (f n g : Nat) : Nat := isqrtD f n ((g + n / g) / 2)

/-- A node with its Nat constants precomputed (`m², 2ma, 2mb, a², 2ab, b²`, `|W| m^k 2^K`). -/
structure FN where
  m2 : Nat
  am : Nat
  bm : Nat
  a2 : Nat
  ab2 : Nat
  b2 : Nat
  w2 : Nat
  w1 : Nat
  m : Nat
  neg : Bool

def toFN (n : GNode) : FN :=
  ⟨n.m * n.m, 2 * n.m * n.a, 2 * n.m * n.b, n.a * n.a, 2 * n.a * n.b, n.b * n.b,
    (n.W.natAbs * n.m * n.m) <<< KB, n.W.natAbs * n.m, n.m, decide (n.W < 0)⟩

/-- The fast rule. -/
def fastRule (d : Nat) : List FN := (gmRule d).map toFN

/-- The leaf numerators split into nonnegative parts. -/
structure LN where
  l00 : Nat
  l11 : Nat
  l22 : Nat
  p01 : Nat
  n01 : Nat
  p02 : Nat
  n02 : Nat
  p12 : Nat
  n12 : Nat

def toLN (L : LQ) : LN :=
  ⟨L.l00.toNat, L.l11.toNat, L.l22.toNat, L.l01.toNat, (-L.l01).toNat, L.l02.toNat, (-L.l02).toNat,
    L.l12.toNat, (-L.l12).toNat⟩

/-- `N = P - Nn` for a node (nonnegative parts). -/
def nodeP (L : LN) (x : FN) : Nat :=
  x.m2 * L.l00 + x.am * L.p01 + x.bm * L.p02 + x.a2 * L.l11 + x.ab2 * L.p12 + x.b2 * L.l22
def nodeM (L : LN) (x : FN) : Nat := x.am * L.n01 + x.bm * L.n02 + x.ab2 * L.n12

/-- Sum of the node terms of a leaf, `k = 2`: floor sums of the positive / negative weights. -/
def sum2 (L : LN) : List FN → Nat → Nat → Option (Nat × Nat)
  | [], p, n => some (p, n)
  | x :: xs, p, n =>
    bif Nat.blt (nodeM L x) (nodeP L x) && !(Nat.beq p 1) && !(Nat.beq n 1) then
      (bif x.neg then sum2 L xs p (n + x.w2 / (nodeP L x - nodeM L x))
       else sum2 L xs (p + x.w2 / (nodeP L x - nodeM L x)) n)
    else none

/-- Sum of the node terms of a leaf, `k = 1` (`H = 2^j`): floors of `|W| m r / H` with
`r = ⌊√⌊2^(2 KB1)/N⌋⌋` (verified), and the sums of the ceilings. -/
def sum1 (L : LN) (j g0 : Nat) : List FN → Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat × Nat)
  | [], p, n, cp, cn => some (p, n, cp, cn)
  | x :: xs, p, n, cp, cn =>
    let N := nodeP L x - nodeM L x
    let Mv := (2 ^ (2 * KB1)) / N
    let r := isqrtN 64 Mv (g0 * 3 / x.m + 1)
    bif Nat.blt (nodeM L x) (nodeP L x) && Nat.ble (r * r) Mv && Nat.blt Mv ((r + 1) * (r + 1)) &&
        !(Nat.beq p 1) && !(Nat.beq n 1) then
      (bif x.neg then sum1 L j g0 xs p (n + (x.w1 * r) >>> j) cp (cn + (x.w1 * (r + 1) + 2 ^ j - 1) >>> j)
       else sum1 L j g0 xs (p + (x.w1 * r) >>> j) n (cp + (x.w1 * (r + 1) + 2 ^ j - 1) >>> j) cn)
    else none

/-- The largest vertex offset. -/
def Rmax (L : LQ) : Int := max (offR L (-1) (-1)) (max (offR L 2 (-1)) (offR L (-1) 2))

/-- The leaf admissibility: `t = tn/2^TB < 1`, centre `≠ 0`, `|v - c|² ≤ t² |c|²` at the vertices. -/
def leafCond (L : LQ) (tn : Nat) : Bool :=
  Nat.blt tn (2 ^ TB) && decide (0 < nodeN L 1 1 3) && decide (0 ≤ L.l00) && decide (0 ≤ L.l11) &&
    decide (0 ≤ L.l22) && decide (Rmax L * ((2 ^ (2 * TB) : Nat) : Int) ≤ ((tn * tn : Nat) : Int) * nodeN L 1 1 3)

def cntPos (r : List GNode) : Nat := (r.filter fun x => decide (0 ≤ x.W)).length
def cntNeg (r : List GNode) : Nat := (r.filter fun x => decide (x.W < 0)).length

/-- The remainder bound, `k = 2`: `⌈9 (WC + 2Σ|W|) φ 2^KB / (2 Nc)⌉`. -/
def err2 (d tn Nc : Nat) : Nat :=
  (9 * (WCc + 2 * gAbs (gmRule d)) * phiN d tn * 2 ^ KB + (2 * phiD d tn * Nc - 1)) / (2 * phiD d tn * Nc)

/-- The remainder bound, `k = 1`: `⌈3 (WC + 2Σ|W|) φ (rc+1) / (2 H)⌉`. -/
def err1 (d tn rc j : Nat) : Nat :=
  (3 * (WCc + 2 * gAbs (gmRule d)) * phiN d tn * (rc + 1) + (2 * phiD d tn * 2 ^ j - 1)) / (2 * phiD d tn * 2 ^ j)

/-- `⌊√⌊2^(2 KB1)/Nc⌋⌋` candidate. -/
def rcOf (Nc : Nat) : Nat := isqrtN 256 (2 ^ (2 * KB1) / Nc) (2 ^ (KB1 + 1))

def leaf2 (L : LQ) (d tn : Nat) : Option (Int × Int) :=
  match sum2 (toLN L) (fastRule d) 0 0 with
  | some (p, n) => some ((p : Int) - (n + cntNeg (gmRule d)) - err2 d tn (nodeN L 1 1 3).toNat,
      (p + cntPos (gmRule d) : Int) - n + err2 d tn (nodeN L 1 1 3).toNat)
  | none => none

def leaf1 (L : LQ) (d tn j : Nat) : Option (Int × Int) :=
  let rc := rcOf (nodeN L 1 1 3).toNat
  bif Nat.ble (rc * rc) (2 ^ (2 * KB1) / (nodeN L 1 1 3).toNat) &&
      Nat.blt (2 ^ (2 * KB1) / (nodeN L 1 1 3).toNat) ((rc + 1) * (rc + 1)) then
    (match sum1 (toLN L) j (rc + 1) (fastRule d) 0 0 0 0 with
     | some (p, n, cp, cn) => some ((p : Int) - cn - err1 d tn rc j, (cp : Int) - n + err1 d tn rc j)
     | none => none)
  else none

/-- The rule degrees the checker accepts (each certified by `ruleOK` in the data modules). -/
def degList : List Nat := [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23]

/-- The enclosure contributed by one leaf (in units `2^K WCc / sD^k`, times `4^-j`). -/
def leafChk (qc : QC) (k d tn : Nat) (j : Nat) (p1 p2 : Int) (e : Bool) : Option (Int × Int) :=
  bif degList.elem d && leafCond (leafLQ qc j p1 p2 e) tn then
    (bif Nat.beq k 2 then leaf2 (leafLQ qc j p1 p2 e) d tn else leaf1 (leafLQ qc j p1 p2 e) d tn j)
  else none

/-- The quadtree: children `(2p + e δ, e')`, `δ ∈ {(0,0),(1,0),(0,1),(1,1)}`, the last flipped. -/
def treeChk (qc : QC) (k : Nat) : QT → Nat → Int → Int → Bool → Option (Int × Int)
  | .leaf d tn, j, p1, p2, e => leafChk qc k d tn j p1 p2 e
  | .node c0 c1 c2 c3, j, p1, p2, e =>
    let s : Int := if e then -1 else 1
    match treeChk qc k c0 (j + 1) (2 * p1) (2 * p2) e,
      treeChk qc k c1 (j + 1) (2 * p1 + s) (2 * p2) e,
      treeChk qc k c2 (j + 1) (2 * p1) (2 * p2 + s) e,
      treeChk qc k c3 (j + 1) (2 * p1 + s) (2 * p2 + s) (!e) with
    | some a, some b, some c, some d => some (a.1 + b.1 + c.1 + d.1, a.2 + b.2 + c.2 + d.2)
    | _, _, _, _ => none

end GW.Endpoint.Coulomb

/-
G2 unfolding: the symmetry unfolding of the wavefunctions (`spec.Wfn.find/rotate`,
`cert.real_coeffs`, `spec.EpsilonRun.kfull`), the spheres (`spec.sphere_of`,
`spec.Run.sphere`, `spec.bgw_order`) and the eps index map (`spec.Screening.mapping`,
`cert.SigmaIV.eps_at`), as kernel-executable functions of the IRREDUCIBLE data of the
WFN files (`Wfn`: the header's integer rotations `mtrx`, fractional translations, k-points,
weights, `bdot`, `celvol`, the G-vector list, and every state's G-list, coefficients and
energies, all as exact dyadics `Dy` of the file's binary64 numbers).

Conventions exactly as `bgw/endpoint/spec.py` / `cert.py` (real flavour):

* An operation `(M, t)`: `M` acts on reciprocal crystal coordinates (the header's `mtrx`),
  the fractional translation is `t = t2 / 2` with `t2` integer (`tOK`: the header's
  `tnp` is within `10^-15` of `(PIL / 10^20) · t2`, `PIL / 10^20` a 20-decimal lower bound of π
  (`Real.pi_gt_d20`), so within
  `10^-15 + 10^-20` of `π t2` (`tOK1_sound`), i.e. `tnp / 2π = t2 / 2` to within
  `2·10^-16`; `atom_mapping_sign` only chooses between `±t`, which give the same state
  because `2t` is a lattice vector here).
* `find kp`: the FIRST `(ik, iop)` in `(ik, iop)` order with `kp - M k_ik` within `10^-9`
  of an integer vector `g` (`spec.Wfn.find`); the state at `kp` has the G-vectors
  `M G - g` and the coefficients `s(G) c(G)`, `s(G) = (-1)^((M G) · t2)`
  (`cert.real_coeffs`; `flipG_phase` in `UnfoldPhase.lean`: `s(G) = exp(-2πi (M G)·t)`,
  so these are the textbook `c'(M G - g) = exp(-2πi (M(k+G))·t) c(G)` times the global phase
  `exp(2πi (M k)·t)`, which cert.py drops because it cancels in every quantity used).
* `kfull`: the distinct points `M k - floor(M k + 10^-9)` over `k` in file order and
  `M` in op order, first occurrence kept (`spec.EpsilonRun.__init__`).

Numbers: k-points are integers at scale `2^-SK`; coefficients/energies are `Dy`,
encoded at a consumer's scale by `Dy.enc` (exact when `e ≤ S`, `Dy.enc_val`). All list
functions are structural (kernel reduction by `decide +kernel`).
-/
import GW.Endpoint.Kernel.SigmaSpec
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace GW.Endpoint.Kernel.Unf

open GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### Exact binary64 values -/

/-- The dyadic `(-1)^neg · m / 2^e` (a binary64 number of a file, exactly). -/
structure Dy where
  neg : Bool
  m : ℕ
  e : ℕ
deriving DecidableEq, Inhabited

/-- The real value of a `Dy`. -/
noncomputable def Dy.val (d : Dy) : ℝ := (if d.neg then -1 else 1) * (d.m : ℝ) / 2 ^ d.e

/-- The integer `d · 2^S` (exact if `d.e ≤ S`), in the literal form `zp`/`zn` of the data. -/
def Dy.enc (S : ℕ) (d : Dy) : ℤ :=
  if d.m = 0 then 0 else if d.neg then zn d.m (S - d.e) else zp d.m (S - d.e)

/-- The natural number `d · 2^S` of a nonnegative `d`. -/
def Dy.encN (S : ℕ) (d : Dy) : ℕ := d.m <<< (S - d.e)

/-- Multiply by `-1` if `s`. -/
def Dy.flip (s : Bool) (d : Dy) : Dy := ⟨xor d.neg s, d.m, d.e⟩

theorem zp_val (m t : ℕ) : ((zp m t : ℤ) : ℝ) = (m : ℝ) * 2 ^ t := by
  simp [zp, Nat.shiftLeft_eq]

theorem zn_val (m t : ℕ) (hm : 0 < m) : ((zn m t : ℤ) : ℝ) = -((m : ℝ) * 2 ^ t) := by
  have h1 : 1 ≤ m <<< t := by
    rw [Nat.shiftLeft_eq]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have : (zn m t : ℤ) = -((m <<< t : ℕ) : ℤ) := by
    unfold zn; rw [Int.negSucc_eq]; push_cast [Nat.cast_sub h1]; ring
  rw [this]; simp [Nat.shiftLeft_eq]

/-- `Dy.enc` is exact: `enc S d / 2^S = d`. -/
theorem Dy.enc_val (d : Dy) (S : ℕ) (h : d.e ≤ S) : ((d.enc S : ℤ) : ℝ) / 2 ^ S = d.val := by
  unfold Dy.enc Dy.val
  have hp : (2 : ℝ) ^ S = 2 ^ (S - d.e) * 2 ^ d.e := by rw [← pow_add, Nat.sub_add_cancel h]
  by_cases hm : d.m = 0
  · simp [hm]
  · have hm' : 0 < d.m := Nat.pos_of_ne_zero hm
    rw [if_neg hm]
    cases hn : d.neg
    · simp only [Bool.false_eq_true, if_false, zp_val, hp]; field_simp; ring
    · simp only [if_true, zn_val _ _ hm', hp]; field_simp; ring

theorem Dy.encN_val (d : Dy) (S : ℕ) (h : d.e ≤ S) (hn : d.neg = false) :
    ((d.encN S : ℕ) : ℝ) / 2 ^ S = d.val := by
  unfold Dy.encN Dy.val
  have hp : (2 : ℝ) ^ S = 2 ^ (S - d.e) * 2 ^ d.e := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [hn, Nat.shiftLeft_eq]; push_cast; rw [hp]; field_simp; ring

theorem Dy.flip_val (s : Bool) (d : Dy) : (d.flip s).val = (if s then -1 else 1) * d.val := by
  unfold Dy.flip Dy.val; cases s <;> cases d.neg <;> simp <;> ring

/-! ### Decidable equality of the stage-2/3 input records (for the kernel checks) -/

deriving instance DecidableEq for GW.Endpoint.Kernel.Eps.KPair
deriving instance DecidableEq for GW.Endpoint.Kernel.Eps.Input
deriving instance DecidableEq for GW.Endpoint.Kernel.Sig.QD
deriving instance DecidableEq for GW.Endpoint.Kernel.Sig.KQ
deriving instance DecidableEq for GW.Endpoint.Kernel.Sig.St

/-! ### Integer geometry -/

/-- Dot product. -/
def dot (a b : V3) : ℤ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- A 3×3 integer matrix by rows. -/
abbrev M3 := V3 × V3 × V3

/-- `M g`. -/
def mulMV (M : M3) (g : V3) : V3 := (dot M.1 g, dot M.2.1 g, dot M.2.2 g)

/-- `c g`. -/
def smul (c : ℤ) (g : V3) : V3 := (c * g.1, c * g.2.1, c * g.2.2)

/-- The adjugate (`M⁻¹ = det M · adj M` for `det M = ±1`). -/
def adj (M : M3) : M3 :=
  let a := M.1; let b := M.2.1; let c := M.2.2
  ((b.2.1 * c.2.2 - b.2.2 * c.2.1, a.2.2 * c.2.1 - a.2.1 * c.2.2, a.2.1 * b.2.2 - a.2.2 * b.2.1),
   (b.2.2 * c.1 - b.1 * c.2.2, a.1 * c.2.2 - a.2.2 * c.1, a.2.2 * b.1 - a.1 * b.2.2),
   (b.1 * c.2.1 - b.2.1 * c.1, a.2.1 * c.1 - a.1 * c.2.1, a.1 * b.2.1 - a.2.1 * b.1))

/-- The determinant. -/
def det (M : M3) : ℤ :=
  M.1.1 * (M.2.1.2.1 * M.2.2.2.2 - M.2.1.2.2 * M.2.2.2.1) -
  M.1.2.1 * (M.2.1.1 * M.2.2.2.2 - M.2.1.2.2 * M.2.2.1) +
  M.1.2.2 * (M.2.1.1 * M.2.2.2.1 - M.2.1.2.1 * M.2.2.1)

/-- `c M`. -/
def smulM (c : ℤ) (M : M3) : M3 := (smul c M.1, smul c M.2.1, smul c M.2.2)

/-! ### Lists (structural recursion) -/

/-- The first index of `a` in `l` (`l.length` if absent). -/
def idxOf (a : V3) : List V3 → ℕ
  | [] => 0
  | b :: l => if a = b then 0 else idxOf a l + 1

/-- The first `some` of `f i l_i`, `i` counted from `i0`. -/
def firstSome {α β : Type} (f : ℕ → α → Option β) : List α → ℕ → Option β
  | [], _ => none
  | a :: l, i => match f i a with
    | some b => some b
    | none => firstSome f l (i + 1)

/-- The last `some` of `f i l_i`. -/
def lastSome {α β : Type} (f : ℕ → α → Option β) : List α → ℕ → Option β
  | [], _ => none
  | a :: l, i => match lastSome f l (i + 1) with
    | some b => some b
    | none => f i a

/-- Append `p` unless it occurs already (first occurrences kept, in order). -/
def insNew (acc : List V3) (p : V3) : List V3 := if p ∈ acc then acc else acc ++ [p]

/-- Distinct elements in order of first occurrence. -/
def dedup (l : List V3) : List V3 := l.foldl insNew []

/-! ### The irreducible data of one WFN file -/

/-- The scale of k-points and q-points (integers at `2^-SK`). -/
def SK : ℕ := 64

/-- A space-group operation: `mtrx` (on reciprocal crystal coordinates) and `t2 = 2t`. -/
structure Op where
  M : M3
  t2 : V3
deriving DecidableEq, Inhabited

/-- A real-flavour WFN file, exactly: the operations, the header's fractional translations
`tnp` (radians, for `tOK`), the irreducible k-points and weights, per k-point the G-list,
the coefficient rows (one per band) and the energies (Ry), `bdot`, `celvol` and the
G-vector list `gvec`. -/
structure Wfn where
  ops : List Op
  tnp : List (Dy × Dy × Dy)
  kpt : List (Dy × Dy × Dy)
  kw : List Dy
  kg : List (List V3)
  coef : List (List (List Dy))
  en : List (List Dy)
  bdot : List (List Dy)
  celvol : Dy
  gvec : List V3

/-- A point with `Dy` coordinates as integers at scale `2^-S`. -/
def kn (S : ℕ) (x : Dy × Dy × Dy) : V3 := (x.1.enc S, x.2.1.enc S, x.2.2.enc S)

/-- The integer `g` with `|x / 2^S - g| < 10^-9`, if any (`spec.Wfn.find`). -/
def near9 (S : ℕ) (x : ℤ) : Option ℤ :=
  let g := (2 * x + 2 ^ S) / 2 ^ (S + 1)
  if 10 ^ 9 * (x - g * 2 ^ S).natAbs < 2 ^ S then some g else none

/-- The integer `g` with `|x / 2^S - g| ≤ 10^-6`, if any (`np.allclose(.., atol=1e-6)`). -/
def near6 (S : ℕ) (x : ℤ) : Option ℤ :=
  let g := (2 * x + 2 ^ S) / 2 ^ (S + 1)
  if 10 ^ 6 * (x - g * 2 ^ S).natAbs ≤ 2 ^ S then some g else none

/-- Componentwise. -/
def near3 (f : ℤ → Option ℤ) (x : V3) : Option V3 :=
  match f x.1, f x.2.1, f x.2.2 with
  | some a, some b, some c => some (a, b, c)
  | _, _, _ => none

/-- `(ik, iop, g)`: the first k-point and operation (in file order) with `kp = M k + g`
(within `10^-9`), as `spec.Wfn.find`. -/
def find (w : Wfn) (kp : V3) : Option (ℕ × ℕ × V3) :=
  firstSome (fun ik k => firstSome (fun iop (op : Op) =>
      (near3 (near9 SK) (kp - mulMV op.M (kn SK k))).map (fun g => (ik, iop, g))) w.ops 0)
    w.kpt 0

/-- An unfolded state list: G-vectors, coefficient rows (bands), energies. -/
structure USt where
  G : List V3
  c : List (List Dy)
  E : List Dy
deriving Inhabited

/-- The per-G sign flip `(M G)·t2` odd, i.e. `exp(-2πi (M G)·t) = -1`. -/
def flipG (op : Op) (G : V3) : Bool := decide (dot (mulMV op.M G) op.t2 % 2 = 1)

/-- The states of irreducible k-point `ik` rotated by operation `iop` to `M k + g`
(`cert.real_coeffs`): G-vectors `M G - g`, coefficients `s(G) c(G)`, energies unchanged. -/
def rot (w : Wfn) (ik iop : ℕ) (g : V3) : USt :=
  let op := w.ops.getD iop default
  let G := w.kg.getD ik []
  let s := G.map (flipG op)
  ⟨G.map (fun G => mulMV op.M G - g), (w.coef.getD ik []).map (fun r => List.zipWith Dy.flip s r),
    w.en.getD ik []⟩

/-- The states at `kp` (`default` if no operation maps an irreducible k-point there). -/
def stAt (w : Wfn) (kp : V3) : USt :=
  match find w kp with
  | some (ik, iop, g) => rot w ik iop g
  | none => default

/-- `x - floor(x + 10^-9)` at scale `2^-S`. -/
def fracI (S : ℕ) (x : ℤ) : ℤ := x - 2 ^ S * ((10 ^ 9 * x + 2 ^ S) / (10 ^ 9 * 2 ^ S))

def frac3 (S : ℕ) (x : V3) : V3 := (fracI S x.1, fracI S x.2.1, fracI S x.2.2)

/-- The images `M k` (reduced by `x - ⌊x + 10^-9⌋`, `fracI`) of one k-point under all
operations, in op order. -/
def images (w : Wfn) (k : Dy × Dy × Dy) : List V3 :=
  w.ops.map (fun op => frac3 SK (mulMV op.M (kn SK k)))

/-- The full k-grid Epsilon sums over: the distinct images of the irreducible k-points
under all operations, first occurrence kept (`spec.EpsilonRun.kfull`). -/
def kfull (w : Wfn) : List V3 := dedup (w.kpt.flatMap (images w))

/-- The orbit of irreducible k-point `k`. -/
def orbit (w : Wfn) (k : Dy × Dy × Dy) : List V3 := dedup (images w k)

/-! ### Spheres -/

/-- `bdot_ab` at scale `2^-SB`. -/
def bE (SB : ℕ) (B : List (List Dy)) (a b : ℕ) : ℤ := ((B.getD a []).getD b default).enc SB

/-- `|q + G|²_B` at scale `2^-(2 SK + SB)` (`q` at scale `2^-SK`). -/
def n2 (SB : ℕ) (B : List (List Dy)) (q G : V3) : ℤ :=
  let u := q + smul (2 ^ SK) G
  u.1 * (bE SB B 0 0 * u.1 + bE SB B 0 1 * u.2.1 + bE SB B 0 2 * u.2.2) +
  u.2.1 * (bE SB B 1 0 * u.1 + bE SB B 1 1 * u.2.1 + bE SB B 1 2 * u.2.2) +
  u.2.2 * (bE SB B 2 0 * u.1 + bE SB B 2 1 * u.2.1 + bE SB B 2 2 * u.2.2)

/-- The sphere `|q + G|² < ecut` in the order of `gvec` (`spec.sphere_of`, `Run.sphere`). -/
def sphere (SB : ℕ) (B : List (List Dy)) (gvec : List V3) (q : V3) (ecut : Dy) : List V3 :=
  gvec.filter (fun G => decide (n2 SB B q G < ecut.enc (2 * SK + SB)))

/-- The extents `max - min + 1` of the G-vector list (`spec.bgw_order`). -/
def ext (gvec : List V3) : V3 :=
  let mx := gvec.foldl (fun a g => (max a.1 g.1, max a.2.1 g.2.1, max a.2.2 g.2.2)) 0
  let mn := gvec.foldl (fun a g => (min a.1 g.1, min a.2.1 g.2.1, min a.2.2 g.2.2)) 0
  mx - mn + (1, 1, 1)

/-- The tie-break key `GK = g3 + E3 (g2 + E2 g1)` (`sort_inc.f90`). -/
def gk (E : V3) (g : V3) : ℤ := g.2.2 + E.2.2 * (g.2.1 + E.2.1 * g.1)

/-- Lexicographic `<` on (group, `GK`). -/
def ltK (a b : ℕ × ℤ) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

/-- Insertion into a list sorted by the key (after equal keys). -/
def insK (x : (ℕ × ℤ) × V3) : List ((ℕ × ℤ) × V3) → List ((ℕ × ℤ) × V3)
  | [] => [x]
  | y :: l => if ltK x.1 y.1 then x :: y :: l else y :: insK x l

/-- Stable insertion into a list sorted by the norm. -/
def insN (x : ℤ × V3) : List (ℤ × V3) → List (ℤ × V3)
  | [] => [x]
  | y :: l => if x.1 < y.1 then x :: y :: l else y :: insN x l

/-- The group index of every element of a norm-sorted list: a new group starts where the
norm exceeds the previous one by more than `TOL_Zero = 10^-12` (scale `2^-S`). -/
def gids (S : ℕ) : ℤ → ℕ → List (ℤ × V3) → List (ℕ × V3)
  | _, _, [] => []
  | p, g, x :: l =>
    let g' := if 2 ^ S < 10 ^ 12 * (x.1 - p) then g + 1 else g
    (g', x.2) :: gids S x.1 g' l

/-- The sphere with its norms, sorted by the norm (stable). -/
def byNorm (SB : ℕ) (B : List (List Dy)) (gvec : List V3) (q : V3) (ecut : Dy) : List (ℤ × V3) :=
  ((sphere SB B gvec q ecut).map (fun G => (n2 SB B q G, G))).foldr insN []

/-- Sigma's eps sphere at `q` in BerkeleyGW's order (`spec.bgw_order`, `sortrx`): ascending
`|q+G|²`, values within `TOL_Zero` of their predecessor tied, ties by `GK`. -/
def bgwSphere (SB : ℕ) (B : List (List Dy)) (gvec : List V3) (q : V3) (ecut : Dy) : List V3 :=
  let l := byNorm SB B gvec q ecut
  let g := gids (2 * SK + SB) (l.headD (0, 0)).1 0 l
  ((g.map (fun x => ((x.1, gk (ext gvec) x.2), x.2))).foldr insK []).map Prod.snd

/-- Robustness of the tie rule (not needed for the statements): consecutive norms differ by
at most `10^-14` or by more than `10^-10`, so rounding cannot change the groups. -/
def gapOK (S : ℕ) : List (ℤ × V3) → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => (decide (10 ^ 14 * (b.1 - a.1) ≤ 2 ^ S) || decide (2 ^ S < 10 ^ 10 * (b.1 - a.1)))
      && gapOK S (b :: l)

/-! ### The inputs of stage 2 (eps) -/

/-- `bdot` at scale `2^-SB`. -/
def encB (SB : ℕ) (B : List (List Dy)) : List (List ℤ) := B.map (fun r => r.map (Dy.enc SB))

/-- The k-point data of stage 2 at the full-grid point `k`: conduction bands `nv..nb-1`
at `k` from `w`, valence bands `0..nv-1` at `k + q` from `wv` (WFNq for q0). -/
def kpairOf (w wv : Wfn) (q : V3) (nv nb SC SEn : ℕ) (k : V3) : KPair :=
  let c := stAt w k
  let v := stAt wv (k + q)
  ⟨v.G, (v.c.take nv).map (fun r => r.map (Dy.enc SC)), (v.E.take nv).map (Dy.enc SEn),
    c.G, ((c.c.drop nv).take (nb - nv)).map (fun r => r.map (Dy.enc SC)),
    ((c.E.drop nv).take (nb - nv)).map (Dy.enc SEn)⟩

/-- **Stage 2's input from the irreducible data** (`cert.epsinv_iv`): `bdot`, `celvol` and
the G-list of `w` (WFN), the sphere `|q+G|² < ecut`, and the unfolded states at every
point of `kfull w`. The scales `SC … SQ` only fix the integer representation. -/
def epsIn (w wv : Wfn) (q3 : Dy × Dy × Dy) (ecut : Dy) (nv nb SC SEn SB SOm SQ : ℕ) : Input :=
  let q := kn SK q3
  ⟨SC, SEn, SB, SOm, SQ, kn SQ q3, encB SB w.bdot, w.celvol.encN SOm,
    sphere SB w.bdot w.gvec q ecut, (kfull w).map (kpairOf w wv q nv nb SC SEn)⟩

/-! ### The inputs of stage 3 (Sigma) -/

/-- One irreducible q of the eps files: `q` (scale `2^-SK`) and its block's G-list. -/
structure IrrQ where
  q : V3
  G : List V3

/-- `(iq, iop, g0)`: the LAST irreducible q and operation (in `(iq, iop)` order) with
`M q_iq = q + g0` within `10^-6` (`irrbz.f90`, `spec.Screening.mapping`). -/
def lastMatch (irr : List IrrQ) (ops : List Op) (q : V3) : Option (ℕ × ℕ × V3) :=
  lastSome (fun iq (b : IrrQ) => lastSome (fun iop (op : Op) =>
      (near3 (near6 SK) (mulMV op.M b.q - q)).map (fun g => (iq, iop, g))) ops 0) irr 0

/-- Sigma's q-point data at `qh = 2q` (`spec.Screening.mapping`, `cert.SigmaIV.eps_at`):
the sphere in BerkeleyGW's order, the exchange sphere (`ecutb`, `gvec` order), the block,
`idx_i` = position of `G_i^irr = M⁻¹(G_i - g0)` in the block, `neg_i` = the relative phase
`exp(-2πi M(G_i^irr - G_0^irr)·t) = -1`, and `z` = position of `g0`. -/
def qdOf (w : Wfn) (SB : ℕ) (irr : List IrrQ) (ecuts ecutb : Dy) (qh : V3) : QD :=
  let q := smul (2 ^ (SK - 1)) qh
  let Gs := bgwSphere SB w.bdot w.gvec q ecuts
  let Gb := sphere SB w.bdot w.gvec q ecutb
  match lastMatch irr w.ops q with
  | some (iq, iop, g0) =>
    let op := w.ops.getD iop default
    let Mi := smulM (det op.M) (adj op.M)
    let Gi := Gs.map (fun G => mulMV Mi (G - g0))
    let G0 := Gi.headD 0
    ⟨qh, Gs, Gb, iq, Gi.map (fun g => idxOf g ((irr.getD iq ⟨0, []⟩).G)),
      Gi.map (fun g => decide (dot (mulMV op.M (g - G0)) op.t2 % 2 = 1)), idxOf g0 Gs⟩
  | none => ⟨qh, Gs, Gb, 0, [], [], 0⟩

/-- The states at `k - q` (`cert.SigmaIV.qpart`: bands `0..nb-1`). -/
def kqOf (w : Wfn) (nb SC SEn : ℕ) (k : V3) (qh : V3) : KQ :=
  let s := stAt w (k - smul (2 ^ (SK - 1)) qh)
  ⟨s.G, (s.c.take nb).map (fun r => r.map (Dy.enc SC)), (s.E.take nb).map (Dy.enc SEn)⟩

/-- A Sigma state (`cert.SigmaIV.prepare`): the multiplet `bands` (1-based) at `k` and the
states at `k - q` for every `q` of the grid. -/
def stOf (w : Wfn) (bands : List ℕ) (nb SC SEn : ℕ) (k3 : Dy × Dy × Dy) (qhs : List V3) : St :=
  let k := kn SK k3
  let s := stAt w k
  ⟨s.G, bands.map (fun b => (s.c.getD (b - 1) []).map (Dy.enc SC)),
    bands.map (fun b => (s.E.getD (b - 1) default).enc SEn), qhs.map (kqOf w nb SC SEn k)⟩

/-- The q-grid `2 × 2 × 2` as `qh = 2q` in `spec.Run.qlist` order. -/
def qh8 : List V3 :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]

/-- The larger of two nonnegative `Dy`. -/
def Dy.maxP (a b : Dy) : Dy := if a.m * 2 ^ b.e < b.m * 2 ^ a.e then b else a

/-- **Stage 3's run data from the irreducible data**: `bdot`, `celvol`, `gvec` of `w`
(WFN_inner), the static-CH sphere `|G|² < max(ecuts, ecutb)`, the q-point data; RHO
(`rho`, scale `2^-SR`) is the file's list. -/
def glOf (w : Wfn) (irr : List IrrQ) (ecuts ecutb : Dy) (SC SEn SB SOm SR : ℕ)
    (rho : List (V3 × ℤ)) (nocc : ℕ) : Gl :=
  ⟨SC, SEn, SB, encB SB w.bdot, SOm, w.celvol.encN SOm, SR, rho,
    sphere SB w.bdot w.gvec 0 (Dy.maxP ecuts ecutb), qh8.map (qdOf w SB irr ecuts ecutb), nocc⟩

/-! ### Header and grid checks -/

/-- Lower bound of π (`Real.pi_gt_d20`), numerator over `10^20`. -/
def PIL : ℕ := 314159265358979323846

/-- `tnp` is within `10^-15` of `(PIL / 10^20) · t2` (componentwise), so within `10^-15 + 10^-20` of
`π t2` (`tOK1_sound`). -/
def tOK1 (d : Dy) (t : ℤ) : Bool :=
  !d.neg && decide (t.natAbs ≤ 1) &&
    decide (((d.m * 10 ^ 20 : ℕ) - t * (PIL * 2 ^ d.e : ℕ)).natAbs ≤ 2 ^ d.e * 10 ^ 5)

/-- Every operation's `t2` is the header's `tnp / π`: each `tnp` component is within `10^-15`
of `(PIL / 10^20) · t2` (so within `10^-15 + 10^-20` of `π t2`, `tOK1_sound`). -/
def tOK (w : Wfn) : Bool :=
  w.ops.length == w.tnp.length &&
  (List.zipWith (fun (op : Op) (x : Dy × Dy × Dy) =>
    tOK1 x.1 op.t2.1 && tOK1 x.2.1 op.t2.2.1 && tOK1 x.2.2 op.t2.2.2) w.ops w.tnp).all id

/-- `kfull` is closed under every operation (so it is the union of the orbits). -/
def closedOK (w : Wfn) : Bool :=
  (kfull w).all (fun p => w.ops.all (fun op => decide (frac3 SK (mulMV op.M p) ∈ kfull w)))

/-- The weights are the orbit fractions `|orbit k| / |kfull|` and the orbits partition
`kfull` (their sizes add up). -/
def kwOK (w : Wfn) : Bool :=
  w.kpt.length == w.kw.length &&
  (List.zipWith (fun k (d : Dy) => !d.neg && decide (d.m * (kfull w).length = (orbit w k).length * 2 ^ d.e))
    w.kpt w.kw).all id &&
  decide ((w.kpt.map (fun k => (orbit w k).length)).sum = (kfull w).length)

/-- Distinct points of `kfull` differ by more than `2 · 10^-9` in some component, so the
source's dedup by `round(p, 9)` keys equals the exact dedup. -/
def sepOK (w : Wfn) : Bool :=
  let l := kfull w
  l.all (fun a => l.all (fun b => decide (a = b) ||
    decide (2 * 2 ^ SK < 10 ^ 9 * (a.1 - b.1).natAbs) ||
    decide (2 * 2 ^ SK < 10 ^ 9 * (a.2.1 - b.2.1).natAbs) ||
    decide (2 * 2 ^ SK < 10 ^ 9 * (a.2.2 - b.2.2).natAbs)))

end GW.Endpoint.Kernel.Unf

namespace GW.Endpoint.Kernel.Unf

/-- Two lists agree if they agree entrywise (the per-entry facts are kernel checks). -/
theorem map_eq_of_getD {α β : Type} [Inhabited β] (f : α → β) (l : List α) (l' : List β) (d : α)
    (n : ℕ) (hl : l.length = n) (hl' : l'.length = n)
    (h : ∀ t < n, f (l.getD t d) = l'.getD t default) : l.map f = l' := by
  apply List.ext_getElem (by simp [hl, hl'])
  intro i h1 h2
  have hi : i < n := by simpa [hl] using h1
  have := h i hi
  have a1 : i < l.length := by omega
  have a2 : i < l'.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem a1, List.getElem?_eq_getElem a2,
    Option.getD_some] at this
  simpa using this

end GW.Endpoint.Kernel.Unf

namespace GW.Endpoint.Kernel.Unf

open GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-- Two lists agree if their lengths and their entries (as `getD`) agree. -/
theorem list_eq_of_getD {β : Type} [Inhabited β] (l l' : List β) (n : ℕ) (hl : l.length = n)
    (hl' : l'.length = n) (h : ∀ t < n, l.getD t default = l'.getD t default) : l = l' := by
  have := map_eq_of_getD id l l' default n hl hl' h
  simpa using this

theorem Input.eq_of (a b : Input) (h1 : a.SC = b.SC) (h2 : a.SEn = b.SEn) (h3 : a.SB = b.SB)
    (h4 : a.SOm = b.SOm) (h5 : a.SQ = b.SQ) (h6 : a.qn = b.qn) (h7 : a.B = b.B) (h8 : a.Om = b.Om)
    (h9 : a.Gs = b.Gs) (h10 : a.ks = b.ks) : a = b := by
  cases a; cases b; simp_all

theorem St.eq_of (a b : St) (h1 : a.Gk = b.Gk) (h2 : a.ck = b.ck) (h3 : a.Ek = b.Ek)
    (h4 : a.kq = b.kq) : a = b := by
  cases a; cases b; simp_all

theorem Gl.eq_of (a b : Gl) (h1 : a.SC = b.SC) (h2 : a.SEn = b.SEn) (h3 : a.SB = b.SB)
    (h4 : a.B = b.B) (h5 : a.SOm = b.SOm) (h6 : a.Om = b.Om) (h7 : a.SR = b.SR)
    (h8 : a.rho = b.rho) (h9 : a.Gch = b.Gch) (h10 : a.qs = b.qs) (h11 : a.nocc = b.nocc) :
    a = b := by
  cases a; cases b; simp_all

end GW.Endpoint.Kernel.Unf

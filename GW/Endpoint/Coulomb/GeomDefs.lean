/-
G2-coulomb: integer data types and kernel checks of the cell decomposition (core Lean).

The Wigner–Seitz cell `P` of the q-lattice (crystal coordinates, metric `B = Bint / 2^54`) is
cut into 72 tetrahedra `T_i = conv(0, c_F, V_j, V_{j+1})` (face-centre fans). All vertices are
integer vectors over `Dv`. `geomOK` checks (exact integers):

* `invOK` — `adj · M = M · adj = d I`, `d > 0` (`M` = columns `c, a, b`);
* `certOK` — the barycentric row `k` of `T_i` is a positive multiple of `φ_i - φ_n`
  (`φ_i = W_i · u / d_i`, `n` the neighbour across the face opposite vertex `k`);
* `outerOK` — `1 - Σ_k (row_k · u) Dv / d = 1 - 4 (Bint n_f) · u / (n_f Bint n_f)`
  (the outer face lies on the cell face `f`);
* `vertOK` — every vertex satisfies every cell inequality;
* `sepOK` — `φ_i ≥ φ_j` on the vertices of `T_i`, and `φ_i ≠ φ_j` (for `i ≠ j`).
-/
import GW.Endpoint.Coulomb.CheckDefs

namespace GW.Endpoint.Coulomb

/-- An integer 3-vector. -/
structure IV where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

def IV.g (v : IV) : Fin 3 → Int := fun i => match i with
  | ⟨0, _⟩ => v.x
  | ⟨1, _⟩ => v.y
  | _ => v.z

def IV.dot (a b : IV) : Int := a.x * b.x + a.y * b.y + a.z * b.z
def IV.add (a b : IV) : IV := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def IV.sub (a b : IV) : IV := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def IV.smul (s : Int) (a : IV) : IV := ⟨s * a.x, s * a.y, s * a.z⟩

/-- The rows of an integer 3×3 matrix. -/
structure IM where
  r0 : IV
  r1 : IV
  r2 : IV
deriving DecidableEq, Repr

def IM.mulV (M : IM) (v : IV) : IV := ⟨M.r0.dot v, M.r1.dot v, M.r2.dot v⟩

/-- One tetrahedron of the decomposition. -/
structure TD where
  c : IV
  a : IV
  b : IV
  d : Int
  q0 : IV
  q1 : IV
  q2 : IV
  W : IV
  n0 : Nat
  n1 : Nat
  n2 : Nat
  k0 : Nat
  k1 : Nat
  k2 : Nat
  kn0 : Nat
  kd0 : Nat
  kn1 : Nat
  kd1 : Nat
  kn2 : Nat
  kd2 : Nat
  f : Nat
deriving Repr

def TD.col (t : TD) (k : Nat) : IV := match k with | 0 => t.c | 1 => t.a | _ => t.b
def TD.row (t : TD) (k : Nat) : IV := match k with | 0 => t.q0 | 1 => t.q1 | _ => t.q2
def TD.nb (t : TD) (k : Nat) : Nat := match k with | 0 => t.n0 | 1 => t.n1 | _ => t.n2
def TD.nk (t : TD) (k : Nat) : Nat := match k with | 0 => t.k0 | 1 => t.k1 | _ => t.k2
def TD.kn (t : TD) (k : Nat) : Nat := match k with | 0 => t.kn0 | 1 => t.kn1 | _ => t.kn2
def TD.kd (t : TD) (k : Nat) : Nat := match k with | 0 => t.kd0 | 1 => t.kd1 | _ => t.kd2

def IV.gi (v : IV) (i : Nat) : Int := match i with | 0 => v.x | 1 => v.y | _ => v.z

/-- `Σ_k row_k[m] col_k[m'] = d δ` and `Σ_m col_k[m] row_{k'}[m] = d δ`. -/
def invOK (t : TD) : Bool :=
  decide (0 < t.d) &&
  (List.range 3).all fun m => (List.range 3).all fun m' =>
    decide (((List.range 3).map fun k => (t.col k).gi m * (t.row k).gi m').sum = if m = m' then t.d else 0) &&
    decide ((t.row m).dot (t.col m') = if m = m' then t.d else 0)

def dflt : TD := ⟨⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩,1,⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩,⟨0,0,0⟩,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

/-- `row_k d_n kd = kn (W_i d_n - W_n d_i)`, `kn, kd > 0`. -/
def certOK (ts : List TD) (t : TD) : Bool :=
  (List.range 3).all fun k =>
    let n := ts.getD (t.nb k) dflt
    decide (0 < t.kn k) && decide (0 < t.kd k) &&
    decide (IV.smul (n.d * t.kd k) (t.row k) = IV.smul (t.kn k) (IV.sub (IV.smul n.d t.W) (IV.smul t.d n.W)))

/-- `Dv (Σ_k row_k) (nᵀ B n) = 4 d (B n)`. -/
def outerOK (Bm : IM) (Dv : Int) (ns : List IV) (t : TD) : Bool :=
  let n := ns.getD t.f ⟨0,0,0⟩
  let e := Bm.mulV n
  decide (0 < n.dot e) &&
  decide (IV.smul (Dv * n.dot e) (IV.add (IV.add t.q0 t.q1) t.q2) = IV.smul (4 * t.d) e)

/-- `4 (B n) · v ≤ (nᵀ B n) Dv` for every cell inequality and vertex. -/
def vertOK (Bm : IM) (Dv : Int) (ns : List IV) (t : TD) : Bool :=
  ns.all fun n => decide (0 < n.dot (Bm.mulV n)) &&
    (List.range 3).all fun k => decide (4 * (Bm.mulV n).dot (t.col k) ≤ n.dot (Bm.mulV n) * Dv)

/-- Separation of `T_i` from `T_j` by `φ_i - φ_j`. -/
def sepOK (ts : List TD) : Bool :=
  (List.range ts.length).all fun i => (List.range ts.length).all fun j =>
    let ti := ts.getD i dflt
    let tj := ts.getD j dflt
    decide (i = j) ||
      ((List.range 3).all fun k => decide ((tj.W.dot (ti.col k)) * ti.d ≤ (ti.W.dot (ti.col k)) * tj.d)) &&
        !(decide (IV.smul tj.d ti.W = IV.smul ti.d tj.W))

/-- The neighbour data is an involution: the neighbour of `(n, k')` is `(i, k)`, and the two
shared vertices agree (`sw` = whether they appear swapped). -/
def shared (t : TD) (k : Nat) : IV × IV := match k with
  | 0 => (t.a, t.b)
  | 1 => (t.c, t.b)
  | _ => (t.c, t.a)

def nbOK (ts : List TD) (i : Nat) (t : TD) : Bool :=
  (List.range 3).all fun k =>
    let n := ts.getD (t.nb k) dflt
    decide (t.nb k < ts.length) && decide (t.nk k < 3) && decide (n.nb (t.nk k) = i) && decide (n.nk (t.nk k) = k) &&
      (decide (shared n (t.nk k) = shared t k) ||
        decide (shared n (t.nk k) = ((shared t k).2, (shared t k).1)))

def geomOK (Bm : IM) (Dv : Int) (ns : List IV) (ts : List TD) : Bool :=
  (ts.all fun t => invOK t && certOK ts t && outerOK Bm Dv ns t && vertOK Bm Dv ns t && decide (t.f < ns.length)) &&
  sepOK ts && ((List.range ts.length).all fun i => nbOK ts i (ts.getD i dflt)) && decide (0 < Dv)

/-- `det(c, a, b)` of integer vectors (columns). -/
def det3I (c a b : IV) : Int :=
  c.x * (a.y * b.z - b.y * a.z) - a.x * (c.y * b.z - b.y * c.z) + b.x * (c.y * a.z - a.y * c.z)

/-- The stored `d` is the determinant, and `Σ d = 3 Dv³ / 4` (i.e. `Σ d / (6 Dv³) = 1/8`). -/
def detOK (Dv : Int) (ts : List TD) : Bool :=
  ts.all (fun t => decide (t.d = det3I t.c t.a t.b)) && decide (4 * (ts.map TD.d).sum = 3 * Dv ^ 3)

end GW.Endpoint.Coulomb

namespace GW.Endpoint.Coulomb

/-! ### Per-`Q` integer data (`key = 2Q`) -/

def keyIV (key : Int × Int × Int) : IV := ⟨key.1, key.2.1, key.2.2⟩

/-- The numerator (over `Dv`) of the vertex `Q + col_m`. -/
def ncol (Dv : Int) (t : TD) (key : Int × Int × Int) (m : Nat) : IV := IV.add (t.col m) (IV.smul (Dv / 2) (keyIV key))

/-- `2 d · c₀(Q)` (the barycentric coordinate of the origin w.r.t. the apex). -/
def alN (Dv : Int) (t : TD) (key : Int × Int × Int) : Int :=
  2 * t.d + Dv * (IV.add (IV.add t.q0 t.q1) t.q2).dot (keyIV key)

/-- `Dv³ · det` of the outer face vertices. -/
def detN (Dv : Int) (t : TD) (key : Int × Int × Int) : Int := det3I (ncol Dv t key 0) (ncol Dv t key 1) (ncol Dv t key 2)

/-- The Gram numerators of the outer face `(Q + c, a - c, b - c)` (scale `Dv² 2^54`). -/
def qcOf (Bm : IM) (Dv : Int) (t : TD) (key : Int × Int × Int) : QC :=
  let n0 := ncol Dv t key 0
  let e1 := IV.sub t.a t.c
  let e2 := IV.sub t.b t.c
  ⟨n0.dot (Bm.mulV n0), n0.dot (Bm.mulV e1), n0.dot (Bm.mulV e2), e1.dot (Bm.mulV e1), e1.dot (Bm.mulV e2),
    e2.dot (Bm.mulV e2)⟩

/-- `sign(c₀) |det|` of the outer face `i` (integer). -/
def cN (Dv : Int) (t : TD) (key : Int × Int × Int) : Int := Int.sign (alN Dv t key) * (detN Dv t key).natAbs

/-- The lower / upper integer contributions of one outer face given its enclosure `[lo, hi]`. -/
def tLo (Dv : Int) (t : TD) (key : Int × Int × Int) (lo hi : Int) : Int :=
  if 0 ≤ cN Dv t key then cN Dv t key * lo else cN Dv t key * hi
def tHi (Dv : Int) (t : TD) (key : Int × Int × Int) (lo hi : Int) : Int :=
  if 0 ≤ cN Dv t key then cN Dv t key * hi else cN Dv t key * lo

/-- The common denominator `N_k = SK · Dv³ · (3-k)` as an integer (`k ∈ {1, 2}`). -/
def denN (WC : Nat) (Dv : Int) (k : Nat) : Int :=
  if k = 2 then 2 ^ 246 * WC * Dv else 2 ^ 174 * WC * Dv ^ 2

/-- The box check: `lo/2^SV ≤ 64 π_lo SL / N` and `64 π_hi SH / N ≤ hi/2^SV`, `SL ≥ 0`. -/
def boxOK (N : Int) (SV : Nat) (SL SH lo hi : Int) : Bool :=
  decide (0 ≤ SL) && decide (0 < N) &&
  decide (lo * N * 10 ^ 20 ≤ 64 * 314159265358979323846 * SL * 2 ^ SV) &&
  decide (64 * 314159265358979323847 * SH * 2 ^ SV ≤ hi * N * 10 ^ 20)

end GW.Endpoint.Coulomb

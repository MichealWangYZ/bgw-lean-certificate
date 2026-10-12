/-
G2 stage 3: kernel-executable checkers for spec A's GPP self-energy
(`SigmaSpec.lean`), in exact integer arithmetic.

* **Tables** (`tpackS`, `tget`): a list keyed by integer vectors in `[-h, h]³`
  (RHO, the Coulomb averages, the static-CH pair densities on `Gch`) packed as the
  base-`2^W` digits of one natural number, so that a lookup is one shift and one
  `mod` (Kronecker slots `slot g = (g₁+h) + L((g₂+h) + L(g₃+h))`, `L = 2h+1`).
* **Entries** (`entChk`): for one screening entry `(j, i)` of a q-point, the certified
  record `Ent` (class, box of `I_eps`, box of `wtilde`) is checked against the eps⁻¹
  box of stage 1, the wing factors, RHO and the Coulomb boxes: every drop decision of
  the source is decided by exact comparisons, and `wtilde = √(Omega²/I)` is bracketed
  by squaring.
* **Hot path** (`nOK`, one theorem per q-point, state band and inner band `n1`): for
  every entry and the two energies `x = e_a(k) + iw - e_n1(k-q)` the kernel values
  `sch`, `ssx` are enclosed (`schK`, `ssxK`: every branch decided by comparisons of
  interval endpoints, an undecided branch fails the check; the divisions bracketed by
  `Nat.div` and `Nat.div + 1`), accumulated with the exact pair densities as weights.
* **Exchange and static remainder** (`exOK`, `csOK`), **Coulomb alignment** (`vbOK`),
  **wing factors** (`wingOK`).

The hot path is `ℕ`-only (the kernel has GMP arithmetic for `Nat`, not `Int`); signs
are carried as `Bool`s and sign-split accumulators. All hints are written with
random low bits: the Lean 4.19 kernel's cache keys of literals that agree in their low
64 bits collide (measured up to ~50x slower).

Soundness: `SigmaKernel.lean`, `SigmaHot.lean`, `SigmaTab.lean`, `SigmaEnt.lean`,
`SigmaGlue.lean`, `SigmaStq.lean`, `SigmaAsm.lean`.
-/
import GW.Endpoint.Kernel.SigmaSpec

namespace GW.Endpoint.Kernel.Sig

open GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### Lists -/

/-- Append, by `List.rec`. -/
noncomputable def appL {α : Type} (l m : List α) : List α :=
  List.rec (motive := fun _ => List α) m (fun a _ ih => a :: ih) l

/-- Concatenation of a list of lists, by `List.rec`. -/
noncomputable def flatL {α : Type} (L : List (List α)) : List α :=
  List.rec (motive := fun _ => List α) [] (fun l _ ih => appL l ih) L

/-! ### Tables -/

/-- The Kronecker slot of `g ∈ [-h, h]³`. -/
def tslot (h : ℕ) (g : V3) : ℕ :=
  ((g.1 + h) + (2 * h + 1) * ((g.2.1 + h) + (2 * h + 1) * (g.2.2 + h))).toNat

/-- The (slot, digit) list of a table: digit `b + v` (`b` a bias making it positive). -/
noncomputable def tslots (h b : ℕ) (l : List (V3 × ℤ)) : List (ℕ × ℕ) :=
  mapL (fun p => (tslot h p.1, b + ipos p.2 - ineg p.2)) l

/-- `Σ d 2^(W s)` over (slot, digit) pairs. -/
noncomputable def tpackS (W : ℕ) (l : List (ℕ × ℕ)) : ℕ :=
  sumL (mapL (fun p => p.2 <<< (W * p.1)) l) 0

/-- The digit at `g`. -/
def tget (W h P : ℕ) (g : V3) : ℕ := (P >>> (W * tslot h g)) % 2 ^ W

/-- Distinctness of a list of naturals through a bit set: every new element's bit is
still clear (`(ok, bits)`). -/
noncomputable def distinctB (l : List ℕ) (bits : ℕ) : Bool × ℕ :=
  List.rec (motive := fun _ => ℕ → Bool × ℕ) (fun b => (true, b))
    (fun s _ ih b => let r := ih (b ||| (1 <<< s)); (Nat.beq ((b >>> s) % 2) 0 && r.1, r.2)) l bits

/-- The key conditions of a table (checked once per key list): keys in the box, slots
distinct. -/
noncomputable def keysOK (h : ℕ) (ks : List V3) : Bool :=
  ks.all (inBox (-(h : ℤ)) h) && (distinctB (mapL (tslot h) ks) 0).1

/-- The value conditions: `|v| < b`, `b + |v| < 2^W`. -/
noncomputable def valsOK (W b : ℕ) (vs : List ℤ) : Bool :=
  vs.all (fun v => Nat.blt (ipos v + ineg v) b && Nat.blt (b + (ipos v + ineg v)) (2 ^ W))

/-! ### Signed-magnitude enclosures -/

/-- A kernel value enclosure: when `ok`, the real value is `(-1)^neg m` with
`m ∈ [lo, hi] / scale`. -/
structure SM where
  ok : Bool
  neg : Bool
  lo : ℕ
  hi : ℕ

/-- The failed enclosure. -/
def smFail : SM := ⟨false, false, 0, 0⟩

/-- The value zero. -/
def smZero : SM := ⟨true, false, 0, 0⟩

/-- `d = x - t` for `x = (-1)^sx X` and `t ∈ [tl, th]`: sign and `|d|` bounds; fails
when the sign is undecided. -/
def subT (sx : Bool) (X tl th : ℕ) : SM :=
  bif sx then ⟨true, true, X + tl, X + th⟩
  else bif Nat.blt th X then ⟨true, false, X - th, X - tl⟩
  else bif Nat.blt X tl then ⟨true, true, tl - X, th - X⟩
  else smFail

/-- `s = x + t`: sign and `|s|` bounds; when the sign is undecided `ok = false` and the
bounds are `[0, max]` (enough for the clamp test). -/
def addT (sx : Bool) (X tl th : ℕ) : SM :=
  bif !sx then ⟨true, false, X + tl, X + th⟩
  else bif Nat.blt X tl then ⟨true, false, tl - X, th - X⟩
  else bif Nat.blt th X then ⟨true, true, X - th, X - tl⟩
  else ⟨false, false, 0, max (th - X) (X - tl)⟩

/-- `x² - t²` from `X2 = X²` and `t² ∈ [tl2, th2]`, as `addT`. -/
def sq2 (X2 tl2 th2 : ℕ) : SM :=
  bif Nat.blt th2 X2 then ⟨true, false, X2 - th2, X2 - tl2⟩
  else bif Nat.blt X2 tl2 then ⟨true, true, tl2 - X2, th2 - X2⟩
  else ⟨false, false, 0, max (th2 - X2) (X2 - tl2)⟩

/-- The entry data used by the kernel: `kept` (a GPP mode), the sign of `I`,
`|I| ∈ [al, ah]`, `t ∈ [tl, th]`, `t² ∈ [tl2, th2]`. -/
structure ED where
  kept : Bool
  sI : Bool
  al : ℕ
  ah : ℕ
  tl : ℕ
  th : ℕ
  tl2 : ℕ
  th2 : ℕ

/-- One energy `x = (-1)^sx X`, `X2 = X²`. -/
structure En where
  sx : Bool
  X : ℕ
  X2 : ℕ

/-- Checker constants: `Den2 = Den²` (energies are integers in units `1/Den` eV),
`lim1 = 250000` (`1/(4 TOL_Small)`), `TOL_Zero = tzn / 2^tze`. -/
structure KC where
  Den2 : ℕ
  lim1 : ℕ
  tzn : ℕ
  tze : ℕ

/-- The generic-branch test `(x - t)² > 1/4 ∧ t² < (x - t)² lim1` over the box, from
`|d| ∈ [dl, dh]`: `(decided, value)`. -/
def genT (kc : KC) (dl dh tl2 th2 : ℕ) : Bool × Bool :=
  bif Nat.blt kc.Den2 (4 * (dl * dl)) && Nat.blt th2 (dl * dl * kc.lim1) then (true, true)
  else bif Nat.ble (4 * (dh * dh)) kc.Den2 || Nat.ble (dh * dh * kc.lim1) tl2 then (true, false)
  else (false, false)

/-- `sch = t I / (x - t)` in the generic branch, else `0` (a kept mode). -/
def schK (kc : KC) (e : ED) (x : En) : SM :=
  let d := subT x.sx x.X e.tl e.th
  bif d.ok then
    let g := genT kc d.lo d.hi e.tl2 e.th2
    bif g.1 then
      bif g.2 then ⟨true, xor e.sI d.neg, e.tl * e.al / d.hi, e.th * e.ah / d.lo + 1⟩
      else smZero
    else smFail
  else smFail

/-- `ssx` of a kept mode: generic `t² I / (x² - t²)`, near-pole `-(I t) / (2 (x + t))`
(when `t² > (x - t)² TOL_Zero`), else `0`; each with the `sexcut = 4` clamp
(`GW.Endpoint.Cert.certSsx`). -/
def ssxK (kc : KC) (e : ED) (x : En) : SM :=
  let d := subT x.sx x.X e.tl e.th
  bif d.ok then
    let g := genT kc d.lo d.hi e.tl2 e.th2
    bif g.1 then
      bif g.2 then
        let q := sq2 x.X2 e.tl2 e.th2
        bif x.sx && Nat.blt (4 * q.hi) e.tl2 then smZero
        else bif q.ok && (!x.sx || Nat.ble e.th2 (4 * q.lo)) then
          ⟨true, xor e.sI q.neg, e.tl2 * e.al / q.hi, e.th2 * e.ah / q.lo + 1⟩
        else smFail
      else
        bif Nat.ble e.th2 ((d.lo * d.lo * kc.tzn) >>> kc.tze) then smZero
        else bif Nat.blt ((d.hi * d.hi * kc.tzn) >>> kc.tze) e.tl2 then
          let s := addT x.sx x.X e.tl e.th
          bif x.sx && Nat.blt (8 * s.hi) e.tl then smZero
          else bif s.ok && (!x.sx || Nat.ble e.th (8 * s.lo)) then
            ⟨true, !(xor e.sI s.neg), e.tl * e.al / (2 * s.hi), e.th * e.ah / (2 * s.lo) + 1⟩
          else smFail
        else smFail
    else smFail
  else smFail

/-! ### Entries and accumulators -/

/-- The certified record of one screening entry: class (`0`: `|I| < TOL_Small`; `1`:
`|I| ≥ TOL_Small`, no mode; `2`: valid mode; `3`: invalid mode, `t = 1/TOL_Zero`), the box
`[IL, IH] / 2^SI` of `I_eps`, the box `[tl, th] / Den` of `wtilde`. -/
structure Ent where
  cls : ℕ
  IL : ℤ
  IH : ℤ
  tl : ℕ
  th : ℕ

instance : Inhabited Ent := ⟨⟨0, 0, 0, 0, 0⟩⟩

/-- The kernel data of an entry. -/
noncomputable def entD (r : Ent) : ED :=
  Int.rec (motive := fun _ => ED)
    (fun a => ⟨Nat.ble 2 r.cls, false, a, ipos r.IH, r.tl, r.th, r.tl * r.tl, r.th * r.th⟩)
    (fun _ => ⟨Nat.ble 2 r.cls, true, ineg r.IH, ineg r.IL, r.tl, r.th, r.tl * r.tl, r.th * r.th⟩)
    r.IL

/-- A sign-split interval `[lp - ln, hp - hn]`. -/
structure Acc where
  lp : ℕ
  ln : ℕ
  hp : ℕ
  hn : ℕ

/-- The empty accumulator. -/
def acc0 : Acc := ⟨0, 0, 0, 0⟩

/-- Sum of accumulators. -/
def addA (a b : Acc) : Acc := ⟨a.lp + b.lp, a.ln + b.ln, a.hp + b.hp, a.hn + b.hn⟩

/-- `c (-1)^neg [lo, hi]` for `c ≥ 0`. -/
def smA (neg : Bool) (c lo hi : ℕ) : Acc :=
  bif neg then ⟨0, c * hi, 0, c * lo⟩ else ⟨c * lo, 0, c * hi, 0⟩

/-- `(-1)^s c [IL, IH]` for integers `IL ≤ IH`. -/
noncomputable def ivA (s : Bool) (c : ℕ) (IL IH : ℤ) : Acc :=
  bif s then ⟨c * ineg IH, c * ipos IH, c * ineg IL, c * ipos IL⟩
  else ⟨c * ipos IL, c * ineg IL, c * ipos IH, c * ineg IH⟩

/-- The column state: all enclosures decided, `2 P0`, `2 P1` (`P = sch / 2 - ssx` at the
two energies), `AC` (`Σ x I_eps`, the static remainder of `acc_static_ch`). -/
structure CS where
  ok : Bool
  p0 : Acc
  p1 : Acc
  ac : Acc

/-- The empty state. -/
def cs0 : CS := ⟨true, acc0, acc0, acc0⟩

/-- Sum of states. -/
def addCS (a b : CS) : CS := ⟨a.ok && b.ok, addA a.p0 b.p0, addA a.p1 b.p1, addA a.ac b.ac⟩

/-- `Σ` of a list of states, left to right. -/
noncomputable def sumCS (l : List CS) (s : CS) : CS :=
  List.rec (motive := fun _ => CS → CS) (fun s => s) (fun a _ ih s => ih (addCS s a)) l s

/-- The contribution of entry `(j, i)` of column `i`, weight `x_j = (-1)^sj cj`. -/
noncomputable def contrib (kc : KC) (occ : Bool) (e0 e1 : En) (sj : Bool) (cj : ℕ) (r : Ent) : CS :=
  let ac := bif Nat.ble 1 r.cls then ivA sj cj r.IL r.IH else acc0
  let d := entD r
  bif d.kept then
    let a0 := schK kc d e0
    let a1 := schK kc d e1
    bif occ then
      let b0 := ssxK kc d e0
      let b1 := ssxK kc d e1
      ⟨a0.ok && a1.ok && b0.ok && b1.ok,
        addA (smA (xor sj a0.neg) cj a0.lo a0.hi) (smA (!(xor sj b0.neg)) (2 * cj) b0.lo b0.hi),
        addA (smA (xor sj a1.neg) cj a1.lo a1.hi) (smA (!(xor sj b1.neg)) (2 * cj) b1.lo b1.hi),
        ac⟩
    else
      ⟨a0.ok && a1.ok, smA (xor sj a0.neg) cj a0.lo a0.hi, smA (xor sj a1.neg) cj a1.lo a1.hi, ac⟩
  else ⟨true, acc0, acc0, ac⟩

/-- The contribution, skipping a zero weight. -/
noncomputable def contribZ (kc : KC) (occ : Bool) (e0 e1 : En) (x : Bool × ℕ) (r : Ent) : CS :=
  bif Nat.beq x.2 0 then cs0 else contrib kc occ e0 e1 x.1 x.2 r

/-- Column `i`: `Σ_j x_j K(j, i)` over the rows (weights `xs`, entries `rs`). -/
noncomputable def colSum (kc : KC) (occ : Bool) (e0 e1 : En) (xs : List (Bool × ℕ)) (rs : List Ent) : CS :=
  sumCS (zipW (contribZ kc occ e0 e1) xs rs) cs0

/-! ### Column combination -/

/-- `v Y` for `v ∈ [vl, vh]`, `0 ≤ vl`, `Y ∈ [lp - ln, hp - hn]`. -/
def mulV (vl vh : ℕ) (a : Acc) : Acc :=
  ⟨bif Nat.ble a.ln a.lp then vl * (a.lp - a.ln) else 0,
   bif Nat.ble a.ln a.lp then 0 else vh * (a.ln - a.lp),
   bif Nat.ble a.hn a.hp then vh * (a.hp - a.hn) else 0,
   bif Nat.ble a.hn a.hp then 0 else vl * (a.hn - a.hp)⟩

/-- `(-1)^s c A`. -/
def sgnA (s : Bool) (c : ℕ) (a : Acc) : Acc :=
  bif s then ⟨c * a.hn, c * a.hp, c * a.ln, c * a.lp⟩ else ⟨c * a.lp, c * a.ln, c * a.hp, c * a.hn⟩

/-- `x_i v_i Y_i` of a column. -/
def colFin (x : Bool × ℕ) (v : ℕ × ℕ) (c : CS) : CS :=
  ⟨c.ok, sgnA x.1 x.2 (mulV v.1 v.2 c.p0), sgnA x.1 x.2 (mulV v.1 v.2 c.p1),
    sgnA x.1 x.2 (mulV v.1 v.2 c.ac)⟩

/-- `lo 2^sh ≤ Acc ≤ hi 2^sh`. -/
noncomputable def accIn (a : Acc) (sh : ℕ) (lo hi : ℤ) : Bool :=
  decide (lo * 2 ^ sh ≤ (a.lp : ℤ) - a.ln) && decide ((a.hp : ℤ) - a.hn ≤ hi * 2 ^ sh)

/-- The energy `x = RN (ek - eq) 2^(SX - SEn) + iw 10^8 2^SX` (units `1/(10^8 2^SX)` eV),
replaced by `TOL_Zero` when `|x| < TOL_Zero` (`tz` = TOL_Zero in the same unit). -/
noncomputable def mkEn (RN D1 sh tz : ℕ) (ek eq : ℤ) (iw : ℕ) : En :=
  let x : ℤ := (RN : ℤ) * (ek - eq) * 2 ^ sh + iw * D1
  bif Nat.blt x.natAbs tz then ⟨false, tz, tz * tz⟩ else ⟨decide (x < 0), x.natAbs, x.natAbs * x.natAbs⟩

/-- **The hot-path check** of one (q-point, band `a`, inner band `n1`): `cols` the entries
column by column (`cols i j` = entry `(j, i)`), `xs` the weights `M(G_j) 2^(2 SC - T)`
(sign, magnitude), `vbS` the Coulomb boxes of the sphere (scale `2^-SV`), `e0 e1` the two
energies, and the claimed enclosures (scale `2^-SO`, shift `sh`) of `2 P0 N_q Ω`,
`2 P1 N_q Ω` and `AC · 4 N_q Ω`. -/
noncomputable def nOK (kc : KC) (occ : Bool) (e0 e1 : En) (xs : List (Bool × ℕ))
    (vbS : List (ℕ × ℕ)) (cols : List (List Ent)) (sh : ℕ) (o : List ℤ) : Bool :=
  let T := sumCS (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (colSum kc occ e0 e1 xs rs))
    (zipW Prod.mk xs vbS) cols) cs0
  T.ok && Nat.beq xs.length cols.length && Nat.beq xs.length vbS.length &&
  cols.all (fun rs => Nat.beq rs.length xs.length) &&
  accIn T.p0 sh (o.getD 0 0) (o.getD 1 0) && accIn T.p1 sh (o.getD 2 0) (o.getD 3 0) &&
  accIn T.ac sh (o.getD 4 0) (o.getD 5 0)


/-- The weights of the hot path: `x = (-1)^s (|h| / 2^T)`. -/
noncomputable def xsOf (T : ℕ) (l : List ℤ) : List (Bool × ℕ) :=
  mapL (fun (h : ℤ) => (decide (h < 0), h.natAbs >>> T)) l

/-- The shifts of the hot-path claims: `sh + SOUT = SI + 2 (2 SC - T) + SV`, `T ≤ 2 SC`. -/
noncomputable def shOK (SOUT SI SC SV : ℕ) (shs : List (List ℕ)) (txs : List (List ℕ)) : Bool :=
  all2 (fun sr tr => all2 (fun sh tx => Nat.ble tx (2 * SC) && Nat.beq (sh + SOUT) (SI + 2 * (2 * SC - tx) + SV))
    sr tr) shs txs

/-- `2^T` divides every weight. -/
noncomputable def xsExact (T : ℕ) (l : List ℤ) : Bool :=
  l.all (fun (h : ℤ) => Nat.beq ((h.natAbs >>> T) <<< T) h.natAbs)

/-! ### Entries -/

/-- Constants of the entry check: scales (`SF` wing factors, `SI` the `I_eps` hints, `SV`
Coulomb boxes), `RN = RYD 10^8`, `bdot` (scale `SB`), RHO scale `SR`, `celvol = OmN / 2^SOm`,
the RHO table (`W`, box `h`, bias `bias`), `TOL_Small = tsn / 2^tse`, the energy unit
`1/Den`, `winv = 1/TOL_Zero`. -/
structure EG where
  SF : ℕ
  SI : ℕ
  SV : ℕ
  RN : ℕ
  SB : ℕ
  B : List (List ℤ)
  SR : ℕ
  SOm : ℕ
  OmN : ℕ
  W : ℕ
  h : ℕ
  bias : ℕ
  tsn : ℕ
  tse : ℕ
  Den : ℕ
  winv : ℕ

/-- The certified wing factors of a q-point (scale `2^-SF`): `frow ∈ [frl, frh]`,
`fcol ∈ [fcl, fch]`, and `|q| ∈ [ql, qu] / 2^SQ`. -/
structure Wing where
  frl : ℕ
  frh : ℕ
  fcl : ℕ
  fch : ℕ
  ql : ℕ
  qu : ℕ

/-- `(qh + 2 G) . B . (qh + 2 G')` (`= 4 · 2^SB · (q+G).B.(q+G')`). -/
def dotN (B : List (List ℤ)) (qh : V3) (G G' : V3) : ℤ :=
  let u : List ℤ := [qh.1 + 2 * G.1, qh.2.1 + 2 * G.2.1, qh.2.2 + 2 * G.2.2]
  let w : List ℤ := [qh.1 + 2 * G'.1, qh.2.1 + 2 * G'.2.1, qh.2.2 + 2 * G'.2.2]
  let b := fun a c => (B.getD a []).getD c 0
  u.getD 0 0 * (b 0 0 * w.getD 0 0 + b 0 1 * w.getD 1 0 + b 0 2 * w.getD 2 0) +
  u.getD 1 0 * (b 1 0 * w.getD 0 0 + b 1 1 * w.getD 1 0 + b 1 2 * w.getD 2 0) +
  u.getD 2 0 * (b 2 0 * w.getD 0 0 + b 2 1 * w.getD 1 0 + b 2 2 * w.getD 2 0)

/-- The box of a product of a signed box `[el, eh]` and a positive box `[fl, fh]`. -/
def pmul (el eh : ℤ) (fl fh : ℕ) : ℤ × ℤ :=
  (if 0 ≤ el then el * fl else el * fh, if 0 ≤ eh then eh * fh else eh * fl)

/-- An `Omega²` enclosure: nonzero, sign, `|Omega²| ∈ [lo, hi] / D_O`. -/
structure OM where
  nz : Bool
  neg : Bool
  lo : ℕ
  hi : ℕ

/-- `D_O = 10^36 · 4 · 2^(SB+SR+SV) · OmN`, the common denominator of `Omega²`. -/
def DO (g : EG) : ℕ := 10 ^ 36 * 4 * 2 ^ (g.SB + g.SR + g.SV) * g.OmN

/-- `Omega²` of entry `(j, i)` (row `G_j`): from the RHO digit at `G_j - G_i`, the Coulomb
box of row `j` and the exact `(q+G_i).B.(q+G_j)`; at `q = 0`, row `G_j = 0`: `16 π RYD²
rho(0) / celvol` at `G_i = 0`, else `0`. -/
noncomputable def om2 (g : EG) (qd : QD) (vbS : List (ℕ × ℕ)) (P : ℕ) (j i : ℕ) : OM :=
  let gj := gs qd j
  let gi := gs qd i
  let tg := tget g.W g.h P (gj - gi)
  let rv : ℤ := (tg : ℤ) - g.bias
  if tg = 0 then ⟨false, false, 0, 0⟩
  else if qd.qh = 0 ∧ gj = 0 then
    (if gi = 0 then
      ⟨decide (rv ≠ 0), decide (rv < 0), 16 * piLo * g.RN ^ 2 * rv.natAbs * 2 ^ g.SOm * 4 * 2 ^ (g.SB + g.SV),
        16 * piHi * g.RN ^ 2 * rv.natAbs * 2 ^ g.SOm * 4 * 2 ^ (g.SB + g.SV)⟩
     else ⟨false, false, 0, 0⟩)
  else
    let pr := dotN g.B qd.qh gi gj * rv
    let v := vbS.getD j (0, 0)
    ⟨decide (pr ≠ 0), decide (pr < 0), 2 * g.RN ^ 2 * v.1 * pr.natAbs * 2 ^ g.SOm * 10 ^ 20,
      2 * g.RN ^ 2 * v.2 * pr.natAbs * 2 ^ g.SOm * 10 ^ 20⟩

/-- The exact box of `I_eps(j, i) · 2^(SO+SF)` from the stage-1 box of the block
(scale `2^-SO`), the relative sign and the wing rule. -/
noncomputable def ieBox (g : EG) (SO : ℕ) (w : Wing) (qd : QD) (Elo Ehi : List (List ℤ)) (j i : ℕ) : ℤ × ℤ :=
  let a := qd.idx.getD j 0
  let b := qd.idx.getD i 0
  let lo := (Elo.getD a []).getD b 0
  let hi := (Ehi.getD a []).getD b 0
  let s := xor (qd.neg.getD j false) (qd.neg.getD i false)
  let el : ℤ := if s then -hi else lo
  let eh : ℤ := if s then -lo else hi
  let F : ℤ := 2 ^ g.SF
  let wr := j = qd.z ∧ i ≠ qd.z
  let wc := i = qd.z ∧ j ≠ qd.z
  let e : ℤ × ℤ :=
    if qd.qh = 0 then (if wr ∨ wc then (0, 0) else (el * F, eh * F))
    else if wr then pmul el eh w.frl w.frh
    else if wc then pmul el eh w.fcl w.fch
    else (el * F, eh * F)
  let d : ℤ := if j = i then 2 ^ (SO + g.SF) else 0
  (d - e.2, d - e.1)

/-- **The entry check** of `(j, i)` against its record `r`. -/
noncomputable def entChk (g : EG) (SO : ℕ) (w : Wing) (qd : QD) (Elo Ehi : List (List ℤ))
    (vbS : List (ℕ × ℕ)) (P : ℕ) (j i : ℕ) (r : Ent) : Bool :=
  let S1 := SO + g.SF
  let bx := ieBox g SO w qd Elo Ehi j i
  let ieok := decide (r.IL * 2 ^ S1 ≤ bx.1 * 2 ^ g.SI ∧ bx.2 * 2 ^ g.SI ≤ r.IH * 2 ^ S1)
  let tsI : ℤ := (g.tsn : ℤ) * 2 ^ g.SI
  let u := decide (tsI ≤ r.IL * 2 ^ g.tse ∨ r.IH * 2 ^ g.tse ≤ -tsI)
  let uf := decide (-tsI < r.IL * 2 ^ g.tse ∧ r.IH * 2 ^ g.tse < tsI)
  let al : ℕ := if 0 < r.IL then r.IL.natAbs else r.IH.natAbs
  let ah : ℕ := if 0 < r.IL then r.IH.natAbs else r.IL.natAbs
  let o := om2 g qd vbS P j i
  let D := DO g
  let k1 := o.nz && Nat.ble (g.tsn * D) (o.lo * 2 ^ g.tse)
  let k1f := !o.nz || Nat.blt (o.hi * 2 ^ g.tse) (g.tsn * D)
  let wtt := Nat.ble (g.tsn * D * ah) (o.lo * 2 ^ g.SI * 2 ^ g.tse)
  let wtf := Nat.blt (o.hi * 2 ^ g.SI * 2 ^ g.tse) (g.tsn * D * al)
  let sgnEq := o.neg == decide (r.IL < 0)
  let D2 := g.Den * g.Den
  ieok && decide (r.IL ≤ r.IH) &&
  (if r.cls = 0 then uf
   else if r.cls = 1 then u && (k1f || wtf)
   else if r.cls = 2 then u && k1 && wtt && sgnEq && Nat.blt 0 r.tl &&
     Nat.ble (r.tl * r.tl * D * ah) (D2 * o.lo * 2 ^ g.SI) &&
     Nat.ble (D2 * o.hi * 2 ^ g.SI) (r.th * r.th * D * al)
   else if r.cls = 3 then u && k1 && wtt && !sgnEq && Nat.blt 0 r.tl &&
     Nat.ble r.tl (g.winv * g.Den) && Nat.ble (g.winv * g.Den) r.th
   else false)

/-- Column `i` of the entry check (`rs j` = the record of entry `(j, i)`). -/
noncomputable def entCol (g : EG) (SO : ℕ) (w : Wing) (qd : QD) (Elo Ehi : List (List ℤ))
    (vbS : List (ℕ × ℕ)) (P : ℕ) (i : ℕ) (rs : List Ent) : Bool :=
  Nat.beq rs.length qd.Gs.length &&
  all2 (fun j r => entChk g SO w qd Elo Ehi vbS P j i r) (List.range qd.Gs.length) rs

/-! ### Coulomb alignment, wings -/

/-- The Coulomb boxes `vs` of the G-list `Gl` at `qd` are the table entries of
`key qd G` (tables `Plo`, `Phi` with width `W`, box `h`, bias `b`). -/
noncomputable def vbOK (W h b Plo Phi : ℕ) (qd : QD) (Gl : List V3) (vs : List (ℕ × ℕ)) : Bool :=
  Nat.blt 0 b &&
  all2 (fun G (v : ℕ × ℕ) => inBox (-(h : ℤ)) h (key qd G) && Nat.beq (tget W h Plo (key qd G)) (b + v.1) &&
    Nat.beq (tget W h Phi (key qd G)) (b + v.2) && Nat.blt 0 v.1) Gl vs

/-- The wing factors of `qd ≠ 0` against `oneoverq ∈ [ol, oh] / 2^SV`, `vbar(q + Gs₀) ∈
[vl, vh] / 2^SV`, `|q|² = q2N / (4 · 2^SB)` bracketed by `[ql, qu] / 2^SQ`, π. -/
noncomputable def wingOK (g : EG) (SQ : ℕ) (w : Wing) (qd : QD) (oqT : List (V3 × ℤ × ℤ))
    (ol oh : ℕ) (vbS : List (ℕ × ℕ)) : Bool :=
  let q2N := dotN g.B qd.qh 0 0
  let vl := (vbS.getD 0 (0, 0)).1
  let vh := (vbS.getD 0 (0, 0)).2
  oqT.elem (qd.qh, (ol : ℤ), (oh : ℤ)) &&
  Nat.blt 0 w.ql && Nat.blt 0 vl && Nat.blt 0 ol &&
  decide ((w.ql : ℤ) ^ 2 * (4 * 2 ^ g.SB) ≤ q2N * 2 ^ (2 * SQ)) &&
  decide (q2N * 2 ^ (2 * SQ) ≤ (w.qu : ℤ) ^ 2 * (4 * 2 ^ g.SB)) &&
  Nat.ble (w.frl * 2 ^ g.SV * 2 ^ SQ * 8 * piHi) (ol * w.ql * 2 ^ g.SF * 10 ^ 20) &&
  Nat.ble (oh * w.qu * 2 ^ g.SF * 10 ^ 20) (w.frh * 2 ^ g.SV * 2 ^ SQ * 8 * piLo) &&
  Nat.ble (w.fcl * vh * w.qu) (ol * 2 ^ SQ * 2 ^ g.SF) &&
  Nat.ble (oh * 2 ^ SQ * 2 ^ g.SF) (w.fch * vl * w.ql)

/-! ### Exchange and static remainder -/

/-- The bare exchange of one band at one q-point: the claimed box `[lo, hi] / 2^SO`
(shift `sh`) of `X · N_q Ω = -Σ_{n1 < nocc} Σ_G M² vbar` from the pair densities `Hb`
(scale `2^-2SC`) and the Coulomb boxes `vbB`. -/
noncomputable def exOK (Hb : List (List ℤ)) (vbB : List (ℕ × ℕ)) (sh : ℕ) (lo hi : ℤ) : Bool :=
  let Al := sumL (mapL (fun row => sumL (zipW (fun (h : ℤ) (v : ℕ × ℕ) => h.natAbs * h.natAbs * v.1) row vbB) 0) Hb) 0
  let Ah := sumL (mapL (fun row => sumL (zipW (fun (h : ℤ) (v : ℕ × ℕ) => h.natAbs * h.natAbs * v.2) row vbB) 0) Hb) 0
  Hb.all (fun row => Nat.beq row.length vbB.length) &&
  decide (lo * 2 ^ sh ≤ -(Ah : ℤ)) && decide (-(Al : ℤ) ≤ hi * 2 ^ sh)

/-- The static term of entry `(i, j)` of column `j`: `[|I| ≥ TOL_Small, G_i - G_j ∈ Gch]
A(G_i - G_j) (eps - δ)`, `A` read from the table `PA` of the band's `<a|e^{iG.r}|a>` on
`Gch` (scale `2^-2SC`, width `W`, box `h`, bias `b`). -/
noncomputable def csTerm (W h b PA : ℕ) (qd : QD) (j i : ℕ) (r : Ent) : Acc :=
  let tg := tget W h PA (gs qd i - gs qd j)
  let A : ℤ := (tg : ℤ) - b
  bif Nat.ble 1 r.cls && !(Nat.beq tg 0) then ivA (decide (0 < A)) A.natAbs r.IL r.IH else acc0

/-- The static remainder of one band at one q-point: the claimed box of
`CS · 4 N_q Ω = Σ_j vbar_j Σ_i [..] A (eps - δ)`; `tab` = `(Gch, <a|e^{iG.r}|a>)`. -/
noncomputable def csOK (W h b : ℕ) (tab : List (V3 × ℤ)) (qd : QD) (vbS : List (ℕ × ℕ))
    (cols : List (List Ent)) (sh : ℕ) (lo hi : ℤ) : Bool :=
  let PA := tpackS W (tslots h b tab)
  let T := sumCS (zipW (fun (jv : ℕ × (ℕ × ℕ)) rs =>
      colFin (false, 1) jv.2 ⟨true, acc0, acc0,
        sumCS (zipW (fun i r => ⟨true, acc0, acc0, csTerm W h b PA qd jv.1 i r⟩) (List.range rs.length) rs)
          cs0 |>.ac⟩)
    (zipW Prod.mk (List.range cols.length) vbS) cols) cs0
  valsOK W b (mapL Prod.snd tab) &&
  Nat.beq cols.length qd.Gs.length && Nat.beq vbS.length qd.Gs.length &&
  cols.all (fun rs => Nat.beq rs.length qd.Gs.length) && accIn T.ac sh lo hi

end GW.Endpoint.Kernel.Sig

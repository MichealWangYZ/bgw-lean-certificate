/-
G2 roots: kernel-executable checkers for the root brackets of the quasiparticle
equation (`RootSpec.lean`), in exact `ℕ` arithmetic, in the style of stage 3's
`SigmaCheck.lean` (whose entry records, weights, Coulomb boxes and point-energy hot path
`nOK` are reused unchanged).

* `mkEnP`: the point energy `wx(E) = E - e_n1(k-q)` (with the `TOL_Zero` replacement)
  for `E = C / Den`, as stage 3's `En`; the point values of `f` use stage 3's `nOK`.
* `mkEI`: the energy INTERVAL `wx([Ca, Cb] / Den)`, required to have a decided sign
  and `|wx| ≥ TOL_Zero` throughout (so `wx(E) = E - e_n1` there).
* `dschK`, `dssxK` (one kept mode over an interval `x ∈ (-1)^sx [XL, XH] / Den`): every
  branch condition of the source (generic, `sexcut` clamps, near-pole) must be decided
  on the WHOLE interval (an undecided condition fails the check), and `x ≠ w`, and for
  the SX kernel also `x ≠ -w` (so the interval contains no point where the source
  divides by zero); the value is an enclosure of the E-derivative of the active branch.
* `dOK`: one (q-point, band, inner band): all entries (zero weights included, so that
  every mode's branch is decided), accumulated with the exact weights into an enclosure
  of `Σ_i Σ_j W_i V_i W_j (S d sch - 2 [occ] S d ssx)(j, i)`.

Soundness: `RootKernel.lean`, `RootHot.lean`.
-/
import GW.Endpoint.Kernel.SigmaCheck

namespace GW.Endpoint.Kernel.QP

open GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### Energies -/

/-- The point energy `x = C - RN eq 2^sh` (units `1/Den` eV, `Den = 10^8 2^(SEn+sh)`),
replaced by `TOL_Zero` (`tz` in the same unit) when `|x| < TOL_Zero`. -/
noncomputable def mkEnP (RN sh tz : ℕ) (C eq : ℤ) : En :=
  let x : ℤ := C - (RN : ℤ) * eq * 2 ^ sh
  bif Nat.blt x.natAbs tz then ⟨false, tz, tz * tz⟩ else ⟨decide (x < 0), x.natAbs, x.natAbs * x.natAbs⟩

/-- An energy interval `x ∈ (-1)^sx [XL, XH]` (units `1/Den` eV), `XL2 = XL²`, `XH2 = XH²`. -/
structure EI where
  sx : Bool
  XL : ℕ
  XH : ℕ
  XL2 : ℕ
  XH2 : ℕ

instance : Inhabited EI := ⟨⟨false, 0, 0, 0, 0⟩⟩

/-- The interval `wx([Ca, Cb] / Den)`, `wx = E - e`, and whether it has a decided sign with
`|wx| ≥ TOL_Zero` (`tz`) throughout. -/
noncomputable def mkEI (RN sh tz : ℕ) (Ca Cb eq : ℤ) : EI × Bool :=
  let xa : ℤ := Ca - (RN : ℤ) * eq * 2 ^ sh
  let xb : ℤ := Cb - (RN : ℤ) * eq * 2 ^ sh
  if (tz : ℤ) ≤ xa ∧ xa ≤ xb then (⟨false, xa.natAbs, xb.natAbs, xa.natAbs * xa.natAbs, xb.natAbs * xb.natAbs⟩, true)
  else if xb ≤ -(tz : ℤ) ∧ xa ≤ xb then
    (⟨true, xb.natAbs, xa.natAbs, xb.natAbs * xb.natAbs, xa.natAbs * xa.natAbs⟩, true)
  else (default, false)

/-! ### Differences over an interval -/

/-- `d = x - t` for `x ∈ (-1)^sx [XL, XH]`, `t ∈ [tl, th]`: sign and `|d|` bounds; fails
when the sign is undecided. -/
def subI (sx : Bool) (XL XH tl th : ℕ) : SM :=
  bif sx then ⟨true, true, XL + tl, XH + th⟩
  else bif Nat.blt th XL then ⟨true, false, XL - th, XH - tl⟩
  else bif Nat.blt XH tl then ⟨true, true, tl - XH, th - XL⟩
  else smFail

/-- `s = x + t`: sign and `|s|` bounds; undecided sign: `ok = false`, bounds `[0, max]`. -/
def addI (sx : Bool) (XL XH tl th : ℕ) : SM :=
  bif !sx then ⟨true, false, XL + tl, XH + th⟩
  else bif Nat.blt XH tl then ⟨true, false, tl - XH, th - XL⟩
  else bif Nat.blt th XL then ⟨true, true, XL - th, XH - tl⟩
  else ⟨false, false, 0, max (th - XL) (XH - tl)⟩

/-- `x² - t²` from `x² ∈ [XL2, XH2]`, `t² ∈ [tl2, th2]`, as `addI`. -/
def sq2I (XL2 XH2 tl2 th2 : ℕ) : SM :=
  bif Nat.blt th2 XL2 then ⟨true, false, XL2 - th2, XH2 - tl2⟩
  else bif Nat.blt XH2 tl2 then ⟨true, true, tl2 - XH2, th2 - XL2⟩
  else ⟨false, false, 0, max (th2 - XL2) (XH2 - tl2)⟩

/-! ### Derivative kernels -/

/-- The derivative of `sch` of a kept mode over the interval `x`: generic branch decided;
value `-t I / d²` (times `Den`: scale-free in `1/eV`). -/
def dschK (kc : KC) (Den : ℕ) (e : ED) (x : EI) : SM :=
  let d := subI x.sx x.XL x.XH e.tl e.th
  bif d.ok then
    let g := genT kc d.lo d.hi e.tl2 e.th2
    bif g.1 then
      bif g.2 then ⟨true, !e.sI, e.tl * e.al * Den / (d.hi * d.hi), e.th * e.ah * Den / (d.lo * d.lo) + 1⟩
      else smZero
    else smFail
  else smFail

/-- The derivative of `ssx` of a kept mode over the interval `x`: every branch and clamp
decided, `x ≠ ±t`; generic `-2 x t² I / (x² - t²)²`, near-pole `I t / (2 (x + t)²)`. -/
def dssxK (kc : KC) (Den : ℕ) (e : ED) (x : EI) : SM :=
  let d := subI x.sx x.XL x.XH e.tl e.th
  bif d.ok then
    let g := genT kc d.lo d.hi e.tl2 e.th2
    bif g.1 then
      bif g.2 then
        let q := sq2I x.XL2 x.XH2 e.tl2 e.th2
        bif q.ok then
          bif x.sx && Nat.blt (4 * q.hi) e.tl2 then smZero
          else bif !x.sx || Nat.ble e.th2 (4 * q.lo) then
            ⟨true, !(xor x.sx e.sI), 2 * x.XL * e.tl2 * e.al * Den / (q.hi * q.hi),
              2 * x.XH * e.th2 * e.ah * Den / (q.lo * q.lo) + 1⟩
          else smFail
        else smFail
      else
        bif Nat.ble e.th2 ((d.lo * d.lo * kc.tzn) >>> kc.tze) then smZero
        else bif Nat.blt ((d.hi * d.hi * kc.tzn) >>> kc.tze) e.tl2 then
          let s := addI x.sx x.XL x.XH e.tl e.th
          bif s.ok then
            bif x.sx && Nat.blt (8 * s.hi) e.tl then smZero
            else bif !x.sx || Nat.ble e.th (8 * s.lo) then
              ⟨true, e.sI, e.tl * e.al * Den / (2 * (s.hi * s.hi)), e.th * e.ah * Den / (2 * (s.lo * s.lo)) + 1⟩
            else smFail
          else smFail
        else smFail
    else smFail
  else smFail

/-- The derivative contribution of entry `(j, i)`, weight `(-1)^sj cj`: `2 P' = sch' - 2 [occ] ssx'`
(in `p0`; `p1`, `ac` unused). Zero weights are NOT skipped: every mode is decided. -/
noncomputable def dcontrib (kc : KC) (Den : ℕ) (occ : Bool) (x : EI) (sj : Bool) (cj : ℕ) (r : Ent) : CS :=
  let d := entD r
  bif d.kept then
    let a := dschK kc Den d x
    bif occ then
      let b := dssxK kc Den d x
      ⟨a.ok && b.ok, addA (smA (xor sj a.neg) cj a.lo a.hi) (smA (!(xor sj b.neg)) (2 * cj) b.lo b.hi), acc0, acc0⟩
    else ⟨a.ok, smA (xor sj a.neg) cj a.lo a.hi, acc0, acc0⟩
  else cs0

/-- Column `i` of the derivative check. -/
noncomputable def dcolSum (kc : KC) (Den : ℕ) (occ : Bool) (x : EI) (xs : List (Bool × ℕ)) (rs : List Ent) : CS :=
  sumCS (zipW (fun (w : Bool × ℕ) r => dcontrib kc Den occ x w.1 w.2 r) xs rs) cs0

/-- **The derivative check** of one (q-point, band `a`, inner band `n1`) over the energy
interval `[Ca, Cb] / Den`: the interval is admissible (`mkEI`), every entry decided, and the
claimed enclosure `[lo, hi] 2^sh` of `Σ_i Σ_j W_i V_i W_j F(j, i)`,
`F = 2^SI (sch' - 2 [occ] ssx')`. -/
noncomputable def dOK (kc : KC) (Den RN she tz : ℕ) (occ : Bool) (Ca Cb eq : ℤ) (xs : List (Bool × ℕ))
    (vbS : List (ℕ × ℕ)) (cols : List (List Ent)) (sh : ℕ) (lo hi : ℤ) : Bool :=
  let xi := mkEI RN she tz Ca Cb eq
  let T := sumCS (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (dcolSum kc Den occ xi.1 xs rs))
    (zipW Prod.mk xs vbS) cols) cs0
  xi.2 && T.ok && Nat.beq xs.length cols.length && Nat.beq xs.length vbS.length &&
  cols.all (fun rs => Nat.beq rs.length xs.length) && accIn T.p0 sh lo hi

end GW.Endpoint.Kernel.QP

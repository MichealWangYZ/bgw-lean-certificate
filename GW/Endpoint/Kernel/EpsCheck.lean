/-
G2 stage 2: a kernel-executable checker that encloses the static RPA dielectric
matrix eps(q) of `GW.Endpoint.Kernel.Eps.epsR` (file `EpsSpec.lean`) from the
wavefunction coefficients, in exact integer arithmetic.

Two ideas make the work small enough for the kernel:

* **Kronecker packing.** The pair density
  `M_vc(G) = Σ_{G' - G2 = G} c_v(G') c_c(G2)` is a 3D correlation. With the
  linear index `φ(g) = g₁ + L g₂ + L² g₃` (injective on the differences that
  occur, see `inBox`) it becomes the coefficient of `2^(W s(G))` in the product
  of two integers `P_v = Σ c_v(G') 2^(W e(G'))` and `Q_c = Σ c_c(G2) 2^(W f(G2))`.
  One GMP multiplication (the kernel's `Nat.mul`) replaces #G_out × #G
  multiply-adds; the coefficients are read back as base-`2^W` digits
  (`dig`, with a bias that makes every digit nonnegative), which is exact as
  long as every slot is below `2^(W-1)` in absolute value (`l1` bound).
* **Packed rows.** `X_ij = Σ_p D_p m_p(G_i) m_p(G_j)` is accumulated one row
  vector at a time: `R_i += (D_p V_p) m_p(G_i)` with `V_p = Σ_j m_p(G_j) 2^(W2 j)`;
  the entries of row `i` are the base-`2^W2` digits of `R_i`.

Only `1/(E_c - E_v)`, `4/(N_k Ω)` and `8π/|q+G|²` are not exact; each is
bracketed by a floor division (`Nat.div`) whose defining inequalities the
soundness proof uses, and π by Mathlib's `Real.pi_gt_d20` / `Real.pi_lt_d20`.
Soundness: `GW.Endpoint.Kernel.Eps.sound_rows` (file `EpsSound.lean`), per block of rows.
-/
import GW.Endpoint.Kernel.Check

namespace GW.Endpoint.Kernel.Eps

open GW.Endpoint.Kernel

/-- An integer reciprocal-lattice vector in crystal coordinates. -/
abbrev V3 := ℤ × ℤ × ℤ

/-- One k-point of the (symmetry-unfolded) full grid: the valence states at
`k + q` (G-vectors `Gv`, coefficient rows `cv`, energies `Ev`) and the
conduction states at `k` (`Gc`, `cc`, `Ec`). Coefficients are integers at scale
`2^-SC`, energies (Ry) at scale `2^-SEn`. -/
structure KPair where
  Gv : List V3
  cv : List (List ℤ)
  Ev : List ℤ
  Gc : List V3
  cc : List (List ℤ)
  Ec : List ℤ

instance : Inhabited KPair := ⟨⟨[], [], [], [], [], []⟩⟩

/-- The exact input data of one q-point: the metric `B` (bdot, scale `2^-SB`),
the cell volume `Om` (scale `2^-SOm`), `q = qn / 2^SQ` in crystal coordinates,
the sphere `Gs` (the rows/columns of eps), the k-point data `ks`. -/
structure Input where
  SC : ℕ
  SEn : ℕ
  SB : ℕ
  SOm : ℕ
  SQ : ℕ
  qn : V3
  B : List (List ℤ)
  Om : ℕ
  Gs : List V3
  ks : List KPair

/-- Checker parameters (no influence on the statement): the index base `L`, the
box `[lo, lo + H]` of the wavefunction G-vectors, the slot widths `W`, `W2`,
the precision `SD` of `1/(E_c - E_v)`, `SU` of `v·fact`, and a bound `Mmax` on
the pair densities (scale `2^-(2 SC)`). -/
structure Cfg where
  L : ℤ
  lo : ℤ
  H : ℤ
  W : ℕ
  W2 : ℕ
  SD : ℕ
  SU : ℕ
  Mmax : ℕ

/-- The integer `m 2^t` (data literals are written with an odd `m`: literals that
agree in their low 64 bits get colliding kernel cache keys, measured 27x slower). -/
def zp (m t : ℕ) : ℤ := Int.ofNat (m <<< t)

/-- The integer `-(m 2^t)`. -/
def zn (m t : ℕ) : ℤ := Int.negSucc ((m <<< t) - 1)

/-! ### Kernel-friendly list functions (`List.rec`, as in `Check.lean`) -/

/-- `List.map`, by `List.rec`. -/
noncomputable def mapL {α β : Type} (g : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => g a :: ih) l

/-- Fold over two lists in parallel (truncating), left to right. -/
noncomputable def fold2 {α β γ : Type} (f : α → β → γ → γ) (l1 : List α) : List β → γ → γ :=
  List.rec (motive := fun _ => List β → γ → γ) (fun _ acc => acc)
    (fun a _ ih ys acc => List.casesOn (motive := fun _ => γ) ys acc
      (fun y ys' => ih ys' (f a y acc))) l1

/-- `Σ_j l_j 2^(W j)`, Horner form. -/
noncomputable def packIdx (W : ℕ) (l : List ℤ) : ℤ :=
  List.rec (motive := fun _ => ℤ) 0 (fun a _ ih => a + Int.ofNat (2 ^ W) * ih) l

/-! ### Kronecker index -/

/-- The linear index `g₁ + L g₂ + L² g₃`. -/
def phi (L : ℤ) (g : V3) : ℤ := g.1 + L * g.2.1 + L * L * g.2.2

/-- `φ(1,1,1)`. -/
def Phi1 (L : ℤ) : ℤ := 1 + L + L * L

/-- Every component of `g` in `[lo, hi]`. -/
def inBox (lo hi : ℤ) (g : V3) : Bool :=
  decide (lo ≤ g.1) && decide (g.1 ≤ hi) && decide (lo ≤ g.2.1) && decide (g.2.1 ≤ hi) &&
    decide (lo ≤ g.2.2) && decide (g.2.2 ≤ hi)

namespace Cfg

variable (cf : Cfg)

/-- Slot of a valence G-vector. -/
def ev (g : V3) : ℕ := (phi cf.L g - cf.lo * Phi1 cf.L).toNat
/-- Slot of a conduction G-vector (reversed). -/
def fc (g : V3) : ℕ := ((cf.lo + cf.H) * Phi1 cf.L - phi cf.L g).toNat
/-- Slot of the pair density at `G` in the product. -/
def so (G : V3) : ℕ := (phi cf.L G + cf.H * Phi1 cf.L).toNat
/-- Number of slots of the product. -/
def T : ℕ := (2 * cf.H * Phi1 cf.L + 1).toNat

end Cfg

/-- `Σ_{s<T} 2^(W-1) 2^(W s)`: adding it makes every signed digit of a packed
integer with digits in `(-2^(W-1), 2^(W-1))` nonnegative. -/
def bias (W T : ℕ) : ℕ := 2 ^ (W - 1) * ((2 ^ (W * T) - 1) / (2 ^ W - 1))

/-- Signed digit `s` of `Nb` (Nb = packed value + bias). -/
def dig (W s Nb : ℕ) : ℤ := Int.ofNat ((Nb >>> (W * s)) % 2 ^ W) - Int.ofNat (2 ^ (W - 1))

/-! ### Signed integers through `ℕ` (the kernel has no fast `Int` arithmetic) -/

/-- The nonnegative part of an integer (by `Int.rec`: measured ~10x cheaper in the
kernel than `Int` arithmetic, which unfolds several `match`es per operation). -/
noncomputable def ipos (x : ℤ) : ℕ := Int.rec (motive := fun _ => ℕ) (fun n => n) (fun _ => 0) x

/-- The negative part of an integer. -/
noncomputable def ineg (x : ℤ) : ℕ := Int.rec (motive := fun _ => ℕ) (fun _ => 0) (fun n => n + 1) x

/-- `x k + l ≤ r` for `x : ℤ`, `k l r : ℕ`, in `ℕ` arithmetic. -/
noncomputable def zleS (x : ℤ) (k l r : ℕ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun a => Nat.ble (a * k + l) r)
    (fun a => Nat.ble l (r + (a + 1) * k)) x

/-- `l ≤ x k + r` for `x : ℤ`, `k l r : ℕ`, in `ℕ` arithmetic. -/
noncomputable def zgeS (x : ℤ) (k l r : ℕ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun a => Nat.ble l (a * k + r))
    (fun a => Nat.ble (l + (a + 1) * k) r) x

/-- `d = x + h` for a digit `d`, `x : ℤ`, `h : ℕ`. -/
noncomputable def zeq (d : ℕ) (x : ℤ) (h : ℕ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun a => Nat.beq d (a + h)) (fun a => Nat.beq (d + (a + 1)) h) x

/-- `Σ |c_i|`. -/
noncomputable def l1 (cs : List ℤ) : ℕ := sumL (mapL (fun c => ipos c + ineg c) cs) 0

/-- `Σ_{c_i ≥ 0} c_i 2^(W p_i)`. -/
noncomputable def packPos (W : ℕ) (ps : List ℕ) (cs : List ℤ) : ℕ :=
  sumL (zipW (fun p c => ipos c <<< (W * p)) ps cs) 0

/-- `Σ_{c_i < 0} |c_i| 2^(W p_i)`. -/
noncomputable def packNeg (W : ℕ) (ps : List ℕ) (cs : List ℤ) : ℕ :=
  sumL (zipW (fun p c => ineg c <<< (W * p)) ps cs) 0

/-! ### The pair-density check of one k-point -/

/-- The biased product `P Q + bias` of two sign-split packed integers, in `ℕ`. -/
noncomputable def prodB (bs : ℕ) (P Q : ℕ × ℕ) : ℕ := P.1 * Q.1 + P.2 * Q.2 + bs - (P.1 * Q.2 + P.2 * Q.1)

/-- The check of one k-point against its hints `H` (`H v c j = m_vc(G_j)`, the pair
density at scale `2^-(2 SC)`): every product `P_v Q_c` is formed once, and its
digits at the slots `so G_j` must equal the hints. -/
noncomputable def kOK (cf : Cfg) (Gs : List V3) (kp : KPair) (H : List (List (List ℤ))) : Bool :=
  let sos := mapL (fun G => cf.W * cf.so G) Gs
  let pv := mapL cf.ev kp.Gv
  let pc := mapL cf.fc kp.Gc
  let Ps := mapL (fun cv => ((packPos cf.W pv cv, packNeg cf.W pv cv), l1 cv)) kp.cv
  let Qs := mapL (fun cc => ((packPos cf.W pc cc, packNeg cf.W pc cc), l1 cc)) kp.cc
  let bs := bias cf.W cf.T
  let h := 2 ^ (cf.W - 1)
  let B := 2 ^ cf.W
  decide (0 < cf.W) && decide (2 * cf.H < cf.L) && decide (0 ≤ cf.H) &&
  kp.Gv.all (inBox cf.lo (cf.lo + cf.H)) && kp.Gc.all (inBox cf.lo (cf.lo + cf.H)) &&
  Gs.all (inBox (-cf.H) cf.H) &&
  kp.cv.all (fun cv => cv.length == kp.Gv.length) &&
  kp.cc.all (fun cc => cc.length == kp.Gc.length) &&
  kp.Ev.length == kp.cv.length && kp.Ec.length == kp.cc.length &&
  all2 (fun P Hv => all2 (fun Q hs =>
      Nat.blt (P.2 * Q.2) h &&
      let Nb := prodB bs P.1 Q.1
      all2 (fun s x => zeq ((Nb >>> s) % B) x h) sos hs) Qs Hv) Ps H

/-! ### chi and the containment in the stage-1 box -/

/-- `2^SDE / (E_c - E_v)`: `1/(E_c - E_v)` at scale `2^-SD` (energies at `2^-SEn`,
`SDE = SD + SEn`), rounded down. -/
noncomputable def dval (SDE : ℕ) (ev ec : ℤ) : ℕ := 2 ^ SDE / (ec - ev).toNat

/-- Sign-split `Σ_j m_j 2^(W j)` (Horner). -/
noncomputable def packIdx2 (W : ℕ) (l : List ℤ) : ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ × ℕ) (0, 0)
    (fun a _ ih => (ipos a + (ih.1 <<< W), ineg a + (ih.2 <<< W))) l

/-- One pair's update of the sign-split row accumulators, `R_i += D m_i V`. -/
noncomputable def addPair (D : ℕ) (V : ℕ × ℕ) (acc : List (ℕ × ℕ)) (m : List ℤ) :
    List (ℕ × ℕ) :=
  zipW (fun a x => Int.rec (motive := fun _ => ℕ × ℕ)
      (fun k => (a.1 + D * k * V.1, a.2 + D * k * V.2))
      (fun k => (a.1 + D * (k + 1) * V.2, a.2 + D * (k + 1) * V.1)) x) acc m

/-- The accumulators of rows `r0, r0 + 1, …` (as many as `acc0` has) after all pairs
`(k, v, c)`. -/
noncomputable def accRows (W2 SDE r0 : ℕ) (ks : List KPair) (H : List (List (List (List ℤ))))
    (acc0 : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  fold2 (fun kp Ht acc => fold2 (fun ev Hv acc => fold2 (fun ec m acc =>
    addPair (dval SDE ev ec) (packIdx2 W2 m) acc (m.drop r0)) kp.Ec Hv acc) kp.Ev Ht acc) ks H acc0

/-- Per pair: `E_v < E_c`, `n` hint entries, each `|m| ≤ Mmax` (and the shapes of the
hint lists). -/
noncomputable def pairsOK (Mmax n : ℕ) (ks : List KPair) (H : List (List (List (List ℤ)))) : Bool :=
  all2 (fun kp Ht => all2 (fun ev Hv => all2 (fun ec m =>
    decide (ev < ec) && m.length == n && m.all (fun x => Nat.ble (ipos x + ineg x) Mmax))
    kp.Ec Hv) kp.Ev Ht) ks H

/-- `Σ_k Σ_v Σ_c g(E_v, E_c, m)` over all pairs. -/
noncomputable def sum3 (g : ℤ → ℤ → List ℤ → ℕ) (ks : List KPair) (H : List (List (List (List ℤ)))) : ℕ :=
  fold2 (fun kp Ht s => fold2 (fun ev Hv s => fold2 (fun ec m s => s + g ev ec m)
    kp.Ec Hv s) kp.Ev Ht s) ks H 0

/-- Lower bound `314159265358979323846 / 10^20` of π (`Real.pi_gt_d20`). -/
def piLo : ℕ := 314159265358979323846
/-- Upper bound `314159265358979323847 / 10^20` of π (`Real.pi_lt_d20`). -/
def piHi : ℕ := 314159265358979323847

/-- `2^(2 SQ + SB) |q + G|²_B`, exactly. -/
def n2 (inp : Input) (G : V3) : ℤ :=
  let s := Int.ofNat (2 ^ inp.SQ)
  let w : List ℤ := [G.1 * s + inp.qn.1, G.2.1 * s + inp.qn.2.1, G.2.2 * s + inp.qn.2.2]
  let b := fun a c => (inp.B.getD a []).getD c 0
  w.getD 0 0 * (b 0 0 * w.getD 0 0 + b 0 1 * w.getD 1 0 + b 0 2 * w.getD 2 0) +
  w.getD 1 0 * (b 1 0 * w.getD 0 0 + b 1 1 * w.getD 1 0 + b 1 2 * w.getD 2 0) +
  w.getD 2 0 * (b 2 0 * w.getD 0 0 + b 2 1 * w.getD 1 0 + b 2 2 * w.getD 2 0)

/-- The four entry tests of `lo ≤ δ + u y ≤ hi` for `u ∈ {ulo, uhi}`, `y` the ends of
`[(X - E), (X + E)]`, with `X = d - h2` (all rescaled to integers; `k = 2^P`,
`s = 2^SE`, `dl = δ 2^(SE+P)`). -/
noncomputable def entryOK (k s E h2 ulo uhi dl d : ℕ) (lo hi : ℤ) : Bool :=
  zleS lo k (ulo * (h2 + E) * s) (dl + ulo * d * s) &&
  zleS lo k (uhi * (h2 + E) * s) (dl + uhi * d * s) &&
  zgeS hi k (dl + ulo * (d + E) * s) (ulo * h2 * s) &&
  zgeS hi k (dl + uhi * (d + E) * s) (uhi * h2 * s)

/-- Row `i` of the containment check. -/
noncomputable def rowOK (cf : Cfg) (inp : Input) (SE E : ℕ) (i : ℕ) (G : V3) (a : ℕ × ℕ)
    (lo hi : List ℤ) : Bool :=
  let P := cf.SU + cf.SD + 4 * inp.SC
  let k := 2 ^ P
  let s := 2 ^ SE
  let h2 := 2 ^ (cf.W2 - 1)
  let B := 2 ^ cf.W2
  let N := n2 inp G
  let den := 10 ^ 20 * inp.ks.length * inp.Om * N.toNat
  let num := 32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + cf.SU)
  let ulo := num * piLo / den
  let uhi := num * piHi / den + 1
  let Rb := a.1 + bias cf.W2 inp.Gs.length - a.2
  decide (0 < N) &&
  all2 (fun j (q : ℤ × ℤ) => entryOK k s E h2 ulo uhi (if i = j then 2 ^ (SE + P) else 0)
      ((Rb >>> (cf.W2 * j)) % B) q.1 q.2) (List.range inp.Gs.length) (zipW Prod.mk lo hi)

/-- The row-independent part of the chi/eps check. -/
noncomputable def chiGlobal (cf : Cfg) (inp : Input) (H : List (List (List (List ℤ)))) : Bool :=
  pairsOK cf.Mmax inp.Gs.length inp.ks H &&
  Nat.blt (sum3 (fun ev ec _ => dval (cf.SD + inp.SEn) ev ec) inp.ks H * (cf.Mmax * cf.Mmax))
    (2 ^ (cf.W2 - 1)) &&
  decide (0 < cf.W2) && decide (0 < inp.Om)

/-- Rows `r0, …, r0 + L - 1` of the chi/eps check against the stage-1 box
`[epsLo, epsHi] / 2^SE` (one kernel theorem per block of rows bounds the memory). -/
noncomputable def chiRows (cf : Cfg) (inp : Input) (H : List (List (List (List ℤ)))) (SE : ℕ)
    (epsLo epsHi : List (List ℤ)) (r0 L : ℕ) : Bool :=
  let acc := accRows cf.W2 (cf.SD + inp.SEn) r0 inp.ks H (List.replicate L (0, 0))
  let E := sum3 (fun _ _ _ => 1) inp.ks H * (cf.Mmax * cf.Mmax)
  Nat.ble (r0 + L) inp.Gs.length &&
  all2 (fun (x : ℕ × V3) (y : (ℕ × ℕ) × List ℤ × List ℤ) =>
      rowOK cf inp SE E x.1 x.2 y.1 y.2.1 y.2.2)
    (zipW Prod.mk (mapL (· + r0) (List.range L)) (inp.Gs.drop r0))
    (zipW Prod.mk acc (zipW Prod.mk (epsLo.drop r0) (epsHi.drop r0)))

end GW.Endpoint.Kernel.Eps

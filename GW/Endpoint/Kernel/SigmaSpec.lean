/-
G2 stage 3: spec A's linearised quasiparticle energy Eqp1 and the observable
O1 = Eqp1(X, bands 5-6 avg) - Eqp1(L, band 5), as real-number definitions over
exact input data.

This is `bgw/endpoint/cert.py` (`SigmaIV.eps_at`, `modes`, `kernel`, `prepare`,
`qpart`, `eqp1`, `total`) read over the reals (BerkeleyGW 4.0 real flavour,
`Sigma/mtxel_cor.f90`, `wpeff.f90`, `sigma_main.f90`, `Common/fixwings.f90`):

* `epsS`: the eps⁻¹ entry Sigma uses at q, `±E(iq, idx i, idx j)` of the
  irreducible block (relative phase signs `neg`), with the wing rule: at `q = 0`
  row/column `z` zeroed except the head; at `q ≠ 0` row `z` times
  `oneoverq · |q| / (8π)`, column `z` times `oneoverq / (vbar(q + Gs₀) |q|)`.
* `IeS = δ - eps`, `Om2S` (wpeff: `wpsq/nelec · vbar(q+G)/(8π) · (q+G').B.(q+G) ·
  rho(G - G')`, and at `q = 0` the `G = 0` row `wpsq/nelec · rho(0)` on `G' = 0`,
  else `0`; `0` when `G - G'` is not in RHO), the drop thresholds, `wt2 = Om2/I`,
  `wtilde = √wt2`, or `1/TOL_Zero` for an invalid mode (`wt2 < 0`).
* the GPP kernel (`schM`, `ssxM`; `ssxM` uses `Cert.certSsx`, proved equal to the
  source's branch/clamp rule `srcSsx` by `certSsx_eq_srcSsx` wherever the source's formula
  is defined: `w > 0`, `sexcut > 0`, `x ≠ w`, `x + w ≠ 0`; at `x = ±w` see
  `CertSexcut.lean`), `wx` with the `TOL_Zero`
  replacement, the bare exchange with the Coulomb averages `vb`, the exact static
  remainder, the forward difference with `dE = 1 eV`, `Eqp1 = Eqp0 + dΣ/dE / (1 - dΣ/dE)
  (Eqp0 - Eo)`, the multiplet average and `O1`.

Inputs as exact dyadics: coefficients (scale `2^-SC`), energies (Ry, `2^-SEn`),
`bdot` (`2^-SB`), `celvol` (`2^-SOm`), RHO (`2^-SR`); the constants of the source
(`RYD` the decimal 13.60569253 of `nrtype.f90`, the thresholds as the binary64
values the source uses). The real-valued inputs are functions: `E iq a b` the
eps⁻¹ block entries (instantiated with the TRUE inverse in `S3Check`), `vb` the
mini-BZ Coulomb averages keyed by `2(q+G)`, `oq` the `oneoverq` averages keyed by
`2q`. For the certified run, the boxes of `coulomb_cert.json` are proved to contain the
exact mini-BZ averages (`Coul.vb_hyp`, `Coul.oq_hyp`), and the unfolding of the states,
the sphere orders and the symmetry map (`idx`, `neg`, `z`) are computed in Lean from the
irreducible data (`U.*`, `Headline.*`).

Trusted (not formalized): the decoding/export of the run files into Lean literals, and
that these formulas are BerkeleyGW's (a modelling claim, checked by source reading and
numerical agreement on one run).
-/
import GW.Endpoint.Kernel.EpsSpec
import GW.Endpoint.CertSexcut
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel.Eps

/-! ### Constants of the source -/

/-- `RYD = 13.60569253` eV (`Common/nrtype.f90:155`). -/
noncomputable def RYD : ℝ := 1360569253 / 10 ^ 8
/-- `TOL_Small`, the binary64 value of `1d-6`. -/
noncomputable def TS : ℝ := 4722366482869645 / 2 ^ 72
/-- `TOL_Zero`, the binary64 value of `1d-12`. -/
noncomputable def TZ : ℝ := 4951760157141521 / 2 ^ 92
/-- `limitone = 1/(4 TOL_Small)` in binary64 (exactly 250000). -/
noncomputable def LIM1 : ℝ := 250000
/-- The invalid-mode `wtilde = 1/TOL_Zero` in binary64 (exactly 10^12). -/
noncomputable def WINV : ℝ := 10 ^ 12
/-- `limittwo = gamma^2`, `gamma = 0.5`. -/
noncomputable def GAM2 : ℝ := 1 / 4
/-- `gpp_sexcutoff = 4`. -/
noncomputable def SEXC : ℝ := 4

/-! ### Data -/

/-- One q-point of Sigma's grid: `qh = 2q` (crystal coordinates), the eps sphere `Gs`
(BerkeleyGW order), the exchange sphere `Gb`, the irreducible block `iq`, the row map
`idx`, the relative phase signs `neg` (`true` = `-1`) and the wing index `z`. -/
structure QD where
  qh : V3
  Gs : List V3
  Gb : List V3
  iq : ℕ
  idx : List ℕ
  neg : List Bool
  z : ℕ

instance : Inhabited QD := ⟨⟨0, [], [], 0, [], [], 0⟩⟩

/-- The states at `k - q`: G-vectors, coefficient rows (all bands), energies (Ry). -/
structure KQ where
  Gq : List V3
  cq : List (List ℤ)
  Eq : List ℤ

instance : Inhabited KQ := ⟨⟨[], [], []⟩⟩

/-- One multiplet at `k`: G-vectors, the multiplet's coefficient rows and energies, and
the states at `k - q` for every q of the grid. -/
structure St where
  Gk : List V3
  ck : List (List ℤ)
  Ek : List ℤ
  kq : List KQ

/-- The run: scales, `bdot`, `celvol`, RHO, the static-CH sphere `Gch`, the q-grid,
the number of occupied bands. -/
structure Gl where
  SC : ℕ
  SEn : ℕ
  SB : ℕ
  B : List (List ℤ)
  SOm : ℕ
  Om : ℕ
  SR : ℕ
  rho : List (V3 × ℤ)
  Gch : List V3
  qs : List QD
  nocc : ℕ

section defs

variable (gl : Gl)

/-- `bdot_ab`. -/
noncomputable def bd (a b : ℕ) : ℝ := dy gl.SB ((gl.B.getD a []).getD b 0)

/-- The cell volume. -/
noncomputable def vol : ℝ := dy gl.SOm gl.Om

/-- `q + G` in crystal coordinates. -/
noncomputable def vec (qd : QD) (G : V3) : Fin 3 → ℝ :=
  ![(qd.qh.1 : ℝ) / 2 + G.1, (qd.qh.2.1 : ℝ) / 2 + G.2.1, (qd.qh.2.2 : ℝ) / 2 + G.2.2]

/-- `u.B.w`. -/
noncomputable def dotB (u w : Fin 3 → ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, u a * bd gl a b * w b

/-- The Coulomb-average key `2(q + G)`. -/
def key (qd : QD) (G : V3) : V3 := (qd.qh.1 + 2 * G.1, qd.qh.2.1 + 2 * G.2.1, qd.qh.2.2 + 2 * G.2.2)

/-- `Gs[i]`. -/
def gs (qd : QD) (i : ℕ) : V3 := qd.Gs.getD i 0

/-- RHO at `g` (the first matching entry of the file's list), if present. -/
noncomputable def rhoF (g : V3) : Option ℝ :=
  (gl.rho.find? (fun p => p.1 == g)).map (fun p => dy gl.SR p.2)

/-- `nelec = rho(G = 0)`. -/
noncomputable def nelec : ℝ := (rhoF gl 0).getD 0

/-- `wpsq = RYD² 16 π nelec / celvol` (`read_rho_vxc.f90:192-193`). -/
noncomputable def wpsq : ℝ := RYD * RYD * 16 * Real.pi * nelec gl / vol gl

/-- `fact = wpsq / nelec` (wpeff). -/
noncomputable def factW : ℝ := wpsq gl / nelec gl

/-- The number of q-points `N_q`. -/
noncomputable def Nq : ℝ := gl.qs.length

/-- `|q|`. -/
noncomputable def qlen (qd : QD) : ℝ := √(dotB gl (vec qd 0) (vec qd 0))

variable (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

/-- The eps⁻¹ entry `(i, j)` Sigma uses at `qd`, with the wing rule. -/
noncomputable def epsS (qd : QD) (i j : ℕ) : ℝ :=
  let e := (if qd.neg.getD i false = qd.neg.getD j false then 1 else -1) *
    E qd.iq (qd.idx.getD i 0) (qd.idx.getD j 0)
  if qd.qh = 0 then
    (if (i = qd.z ∧ j ≠ qd.z) ∨ (j = qd.z ∧ i ≠ qd.z) then 0 else e)
  else if i = qd.z ∧ j ≠ qd.z then e * (oq qd.qh * qlen gl qd / (8 * Real.pi))
  else if j = qd.z ∧ i ≠ qd.z then e * (oq qd.qh / (vb (key qd (gs qd 0)) * qlen gl qd))
  else e

/-- `I_eps = δ - eps⁻¹`. -/
noncomputable def IeS (qd : QD) (i j : ℕ) : ℝ := (if i = j then 1 else 0) - epsS gl E vb oq qd i j

/-- `Omega²(G_i, G_j)` (wpeff). -/
noncomputable def Om2S (qd : QD) (i j : ℕ) : ℝ :=
  match rhoF gl (gs qd i - gs qd j) with
  | none => 0
  | some r =>
    if qd.qh = 0 ∧ gs qd i = 0 then (if gs qd j = 0 then factW gl * r else 0)
    else factW gl * vb (key qd (gs qd i)) / (8 * Real.pi) *
      dotB gl (vec qd (gs qd j)) (vec qd (gs qd i)) * r

/-- The first drop test: `|I| ≥ TOL_Small` and `|Omega²| ≥ TOL_Small`. -/
def keep1 (I O : ℝ) : Prop := TS ≤ |I| ∧ TS ≤ |O|

/-- `wtilde²` (`0` for a dropped entry). -/
noncomputable def wt2 (I O : ℝ) : ℝ := if TS ≤ |I| ∧ TS ≤ |O| then O / I else 0

/-- A GPP mode is kept: both drop tests and `|wtilde²| ≥ TOL_Small`. -/
def keepM (I O : ℝ) : Prop := (TS ≤ |I| ∧ TS ≤ |O|) ∧ TS ≤ |wt2 I O|

noncomputable instance (I O : ℝ) : Decidable (keepM I O) := Classical.dec _

/-- `wtilde`: `√wt2` for a valid mode, `1/TOL_Zero` for an invalid one (`wt2 < 0`,
`invalid_gpp_mode` default), `0` for a dropped entry. -/
noncomputable def wtM (I O : ℝ) : ℝ :=
  if keepM I O then (if 0 < wt2 I O then √(wt2 I O) else WINV) else 0

/-- `I_eps` as used by the kernel: zeroed below `TOL_Small`. -/
noncomputable def IeU (I : ℝ) : ℝ := if TS ≤ |I| then I else 0

/-- The CH kernel of one mode: generic branch `wtilde I / (x - wtilde)`, else `0`. -/
noncomputable def schM (I O x : ℝ) : ℝ :=
  if keepM I O then
    (let w := wtM I O
     if (x - w) ^ 2 > GAM2 ∧ w ^ 2 < (x - w) ^ 2 * LIM1 then w * IeU I / (x - w) else 0)
  else 0

/-- The SX kernel of one mode (`Cert.certSsx`: generic / near-pole / zero, `sexcut`). -/
noncomputable def ssxM (I O x : ℝ) : ℝ :=
  if keepM I O then GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC (IeU I) (wtM I O) x else 0

/-- `vcoul(G_i) = vbar(q + G_i) / (N_q celvol)`. -/
noncomputable def vS (qd : QD) (i : ℕ) : ℝ := vb (key qd (gs qd i)) / (Nq gl * vol gl)

/-- The pair density `Σ_{Gv_i - Gc_j = G} cv_i cc_j` (`cert.mtxel_iv`). -/
noncomputable def pd (Gv : List V3) (cv : List ℤ) (Gc : List V3) (cc : List ℤ) (G : V3) : ℝ :=
  ∑ i ∈ range Gv.length, ∑ j ∈ range Gc.length,
    if Gv.getD i 0 - Gc.getD j 0 = G then dy gl.SC (cv.getD i 0) * dy gl.SC (cc.getD j 0) else 0

variable (st : St)

/-- `M_{a n1}(k, q_t, G) = <a k| e^{i(q+G).r} |n1 k-q>`. -/
noncomputable def xS (t a n1 : ℕ) (G : V3) : ℝ :=
  pd gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq ((st.kq.getD t default).cq.getD n1 []) G

/-- `wx = e_a(k) + iw dE - e_n1(k - q)` (eV) with the `|wx| < TOL_Zero` replacement. -/
noncomputable def wxS (t a n1 iw : ℕ) : ℝ :=
  let w := RYD * (dy gl.SEn (st.Ek.getD a 0) - dy gl.SEn ((st.kq.getD t default).Eq.getD n1 0)) + iw
  if |w| < TZ then TZ else w

/-- The quadratic form `Σ_i Σ_j M(G_i) v_i M(G_j) F(j, i)` (`(xv * matvec(F.T, x)).sum()`). -/
noncomputable def quad (t a n1 : ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  let qd := gl.qs.getD t default
  ∑ i ∈ range qd.Gs.length, ∑ j ∈ range qd.Gs.length,
    xS gl st t a n1 (gs qd i) * vS gl vb qd i * xS gl st t a n1 (gs qd j) * F j i

/-- The kernel arguments of entry `(j, i)` at q-point `t`. -/
noncomputable def Iq (t j i : ℕ) : ℝ := IeS gl E vb oq (gl.qs.getD t default) j i
noncomputable def Oq (t j i : ℕ) : ℝ := Om2S gl vb (gl.qs.getD t default) j i

/-- The GPP part of inner band `n1` at energy index `iw`: `CH/2 - [occ] SX`. -/
noncomputable def Pq (t a n1 iw : ℕ) : ℝ :=
  (1 / 2) * quad gl vb st t a n1 (fun j i => schM (Iq gl E vb oq t j i) (Oq gl vb t j i) (wxS gl st t a n1 iw)) -
  (if n1 < gl.nocc then
    quad gl vb st t a n1 (fun j i => ssxM (Iq gl E vb oq t j i) (Oq gl vb t j i) (wxS gl st t a n1 iw))
   else 0)

/-- The static-remainder part of inner band `n1`: `-achs/2`,
`achs = (1/2) Σ M v (-I_eps^T M)`. -/
noncomputable def ACq (t a n1 : ℕ) : ℝ :=
  -(1 / 2) * ((1 / 2) * quad gl vb st t a n1 (fun j i => -IeU (Iq gl E vb oq t j i)))

/-- The bare exchange of band `a` at q-point `t` (Ry). -/
noncomputable def Xq (t a : ℕ) : ℝ :=
  let qd := gl.qs.getD t default
  let kq := st.kq.getD t default;
  -(∑ n1 ∈ range gl.nocc, ∑ g ∈ range qd.Gb.length,
    (pd gl st.Gk (st.ck.getD a []) kq.Gq (kq.cq.getD n1 []) (qd.Gb.getD g 0)) ^ 2 *
      (vb (key qd (qd.Gb.getD g 0)) / (Nq gl * vol gl)))

/-- The exact static CH term of band `a` at q-point `t`:
`(1/4) Σ_j v_j Σ_i [|I| ≥ TOL_Small, G_i - G_j ∈ Gch] <a|e^{i(G_i-G_j).r}|a> (eps - δ)`. -/
noncomputable def CSq (t a : ℕ) : ℝ :=
  let qd := gl.qs.getD t default
  (1 / 4) * ∑ j ∈ range qd.Gs.length, vS gl vb qd j * ∑ i ∈ range qd.Gs.length,
    (if TS ≤ |IeS gl E vb oq qd i j| ∧ gs qd i - gs qd j ∈ gl.Gch then
      pd gl st.Gk (st.ck.getD a []) st.Gk (st.ck.getD a []) (gs qd i - gs qd j) *
        (epsS gl E vb oq qd i j - if i = j then 1 else 0)
     else 0)

/-- The number of bands summed over (`number_bands`). -/
def nbq (t : ℕ) : ℕ := ((st.kq.getD t default).cq).length

/-- Band `a`'s `Σ(E_o + iw dE) - Vxc` summed over q (Ry): `X + SX_iw + CH_iw + COR`. -/
noncomputable def SigA (a iw : ℕ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (Xq gl vb st t a + CSq gl E vb oq st t a +
    ∑ n1 ∈ range (nbq st t), (ACq gl E vb oq st t a n1 + Pq gl E vb oq st t a n1 iw))

/-- The multiplet average. -/
noncomputable def avg (f : ℕ → ℝ) : ℝ := (∑ a ∈ range st.ck.length, f a) / st.ck.length

/-- `Eqp1 = Eqp0 + dΣ/dE / (1 - dΣ/dE) (Eqp0 - Eo)` with the forward difference
`dΣ/dE = (Σ(Eo + dE) - Σ(Eo)) / dE`, `dE = 1 eV`, `Eqp0 = Eo + Σ(Eo)` (Vxc = 0). -/
noncomputable def eqp1 : ℝ :=
  let s0 := avg st (fun a => SigA gl E vb oq st a 0) * RYD
  let s1 := avg st (fun a => SigA gl E vb oq st a 1) * RYD
  let eo := avg st (fun a => RYD * dy gl.SEn (st.Ek.getD a 0))
  let d := (s1 - s0) / 1
  let eqp0 := eo + s0
  eqp0 + d / (1 - d) * (eqp0 - eo)

end defs

/-- **The observable** `O1 = Eqp1(X) - Eqp1(L)` of spec A. -/
noncomputable def O1 (gl : Gl) (stX stL : St) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) : ℝ :=
  eqp1 gl E vb oq stX - eqp1 gl E vb oq stL

end GW.Endpoint.Kernel.Sig

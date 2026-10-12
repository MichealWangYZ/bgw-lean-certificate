/-
G2 roots, soundness (2/3): the derivative hot-path check `dOK` of one (q-point, band,
inner band) over an energy interval.

`dOK_sound`: for the entry facts `EntOK` of stage 3 and an admissible interval
`[xa, xb]` of `x = wx`, a successful check gives
* for every entry `(j, i)`: the scaled GPP kernel `tPc` (with either convention `cv` at
  `x = wtilde`) is continuous on `[xa, xb]` with derivative `tD` on `(xa, xb)`, and no
  point of `[xa, xb]` is one where the source divides by zero (`EntFix`);
* for every `y ∈ [xa, xb]`: the quadratic form of `tD y` is in the claimed enclosure.
-/
import GW.Endpoint.Kernel.RootKernel
import GW.Endpoint.Kernel.SigmaHot
import GW.Endpoint.Kernel.SigmaGlue

namespace GW.Endpoint.Kernel.QP

open Finset Set GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps GW.Endpoint.Kernel.Sig

/-! ### Scaled targets -/

/-- The scaled GPP kernel of one entry with convention `cv`: `S sch - 2 [occ] S ssx`. -/
noncomputable def tPc (cv occ : Bool) (S I O x : ℝ) : ℝ :=
  S * schM I O x - (if occ then 2 * (S * ssxMc cv I O x) else 0)

/-- Its formal derivative. -/
noncomputable def tD (occ : Bool) (S I O x : ℝ) : ℝ :=
  S * dschM I O x - (if occ then 2 * (S * dssxM I O x) else 0)

/-- The per-entry facts on an interval. -/
def EntFix (occ : Bool) (S I O xa xb : ℝ) : Prop :=
  (∀ cv : Bool, FixedOn (tPc cv occ S I O) (tD occ S I O) xa xb) ∧
    (keepM I O → ∀ y ∈ Icc xa xb, y ≠ wtM I O ∧ (occ = true → y + wtM I O ≠ 0))

theorem dcertSsx_smul (c I w x : ℝ) :
    dcertSsx GAM2 LIM1 TZ SEXC (c * I) w x = c * dcertSsx GAM2 LIM1 TZ SEXC I w x := by
  unfold dcertSsx
  split_ifs <;> ring

theorem dschM_kept {S I O x : ℝ} (hk : keepM I O) (hU : IeU I = I) :
    S * dschM I O x = if Gen x (wtM I O) then -(wtM I O * (S * I)) / (x - wtM I O) ^ 2 else 0 := by
  unfold dschM
  rw [if_pos hk]
  dsimp only
  rw [hU]
  unfold Gen
  split_ifs <;> ring

theorem dssxM_kept {S I O x : ℝ} (hk : keepM I O) (hU : IeU I = I) :
    S * dssxM I O x = dssxV (S * I) (wtM I O) x := by
  unfold dssxM dssxV
  rw [if_pos hk, hU, dcertSsx_smul]

/-- The derivative-check semantics: when `ok`, the facts `P` hold and the accumulator
`p0` encloses `F y` for every `y ∈ [xa, xb]`. -/
def DSS (c : CS) (P : Prop) (F : ℝ → ℝ) (xa xb : ℝ) : Prop :=
  c.ok = true → P ∧ ∀ y ∈ Icc xa xb, AccS c.p0 (F y)

/-! ### One entry -/

theorem dcontrib_spec {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {DN : ℕ} (hDN : (DN : ℝ) = Den)
    {occ : Bool} {x : EI} {xa xb : ℝ} (hx : EIok x Den xa xb)
    {sj : Bool} {cj : ℕ} {r : Ent} {I O : ℝ} (hr : EntOK S Den r I O) :
    DSS (dcontrib kc DN occ x sj cj r) (EntFix occ S I O xa xb)
      (fun y => sg sj (cj * tD occ S I O y)) xa xb := by
  intro hok
  unfold dcontrib at hok ⊢
  dsimp only at hok ⊢
  rw [entD_kept] at hok ⊢
  by_cases h2 : 2 ≤ r.cls
  · have hb : Nat.ble 2 r.cls = true := Nat.ble_eq.mpr h2
    simp only [hb, cond_true] at hok ⊢
    obtain ⟨hk, -⟩ := hr.c2 h2
    have hU := (hr.c1 (by omega)).1
    have hed := entD_ok hr h2
    set w := wtM I O
    have hsch : ∀ y, S * schM I O y = if Gen y w then w * (S * I) / (y - w) else 0 := fun y => schM_kept hk hU
    have hdsch : ∀ y, S * dschM I O y = if Gen y w then -(w * (S * I)) / (y - w) ^ 2 else 0 :=
      fun y => dschM_kept hk hU
    cases occ
    · simp only [cond_false] at hok ⊢
      obtain ⟨hne, hG, hb⟩ := dschK_spec hD hk2 hl hDN hed hx hok
      have hF : FixedOn (fun y => S * schM I O y) (fun y => S * dschM I O y) xa xb := by
        have := sch_fixed (c := w * (S * I)) hne hG
        exact this.congr (fun y _ => (hsch y).symm) (fun y _ => by rw [hdsch y, neg_div])
      refine ⟨⟨fun cv => ?_, fun _ y hy => ⟨hne y hy, fun h => absurd h (by simp)⟩⟩, fun y hy => ?_⟩
      · refine hF.congr (fun y _ => ?_) (fun y _ => ?_) <;> simp [tPc, tD]
      · have := smA_spec (b := xor sj (dschK kc DN (entD r) x).neg) (c := cj) (hb y hy).1 (hb y hy).2
        rw [sg_xor, sg_mul, sg_sg] at this
        unfold tD; rw [hdsch y]; simpa using this
    · simp only [cond_true] at hok ⊢
      simp only [Bool.and_eq_true] at hok
      obtain ⟨ha, hbk⟩ := hok
      obtain ⟨hne, hG, hb⟩ := dschK_spec hD hk2 hl hDN hed hx ha
      obtain ⟨hne2, hFs, hbs⟩ := dssxK_spec hD hk2 hl htz hDN hed hx hbk
      have hF : FixedOn (fun y => S * schM I O y) (fun y => S * dschM I O y) xa xb := by
        have := sch_fixed (c := w * (S * I)) hne hG
        exact this.congr (fun y _ => (hsch y).symm) (fun y _ => by rw [hdsch y, neg_div])
      have hssc : ∀ cv, ∀ y ∈ Icc xa xb, S * ssxMc cv I O y = ssxV (S * I) w y := by
        intro cv y hy
        unfold ssxMc
        rw [if_neg (fun h => hne y hy h.2.2), ssxM_kept hk hU]
      have hF2 : ∀ cv, FixedOn (fun y => S * ssxMc cv I O y) (fun y => S * dssxM I O y) xa xb := fun cv =>
        hFs.congr (fun y hy => (hssc cv y hy).symm) (fun y _ => (dssxM_kept hk hU).symm)
      refine ⟨⟨fun cv => ?_, fun _ y hy => ⟨hne y hy, fun _ => (hne2 y hy).2⟩⟩, fun y hy => ?_⟩
      · have := hF.sub ((hF2 cv).const_mul 2)
        refine this.congr (fun y _ => ?_) (fun y _ => ?_) <;> simp [tPc, tD]
      · have A := smA_spec (b := xor sj (dschK kc DN (entD r) x).neg) (c := cj) (hb y hy).1 (hb y hy).2
        have B := smA_spec (b := !(xor sj (dssxK kc DN (entD r) x).neg)) (c := 2 * cj) (hbs y hy).1 (hbs y hy).2
        have := AccS_add A B
        unfold tD; rw [hdsch y, dssxM_kept hk hU, if_pos rfl]
        convert this using 1
        generalize (dschK kc DN (entD r) x).neg = n1 at *
        generalize (dssxK kc DN (entD r) x).neg = n2 at *
        cases sj <;> cases n1 <;> cases n2 <;> simp only [sg, Bool.not_false, Bool.not_true, if_true,
          if_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true, Bool.true_xor, Bool.false_xor,
          Bool.not_not] <;> push_cast <;> ring
  · have hb : Nat.ble 2 r.cls = false := by rw [ble_d]; simpa using h2
    simp only [hb, cond_false]
    have hnk : ¬keepM I O := by
      rcases Nat.lt_or_ge r.cls 1 with h | h
      · exact (hr.c0 (by omega)).2
      · exact hr.c1' (by omega)
    have z0 : ∀ cv y, tPc cv occ S I O y = 0 := fun cv y => by unfold tPc ssxMc schM ssxM; simp [hnk]
    have z1 : ∀ y, tD occ S I O y = 0 := fun y => by unfold tD dschM dssxM; simp [hnk]
    refine ⟨⟨fun cv => (FixedOn.const 0 xa xb).congr (fun y _ => (z0 cv y).symm) (fun y _ => (z1 y).symm),
      fun h => absurd h hnk⟩, fun y _ => ?_⟩
    rw [z1]; simpa [sg_zero, cs0] using AccS_zero

/-! ### Sums of derivative states -/

theorem DSS_add {a b : CS} {P Q : Prop} {F G : ℝ → ℝ} {xa xb : ℝ} (ha : DSS a P F xa xb)
    (hb : DSS b Q G xa xb) : DSS (addCS a b) (P ∧ Q) (fun y => F y + G y) xa xb := fun h => by
  simp only [addCS, Bool.and_eq_true] at h
  obtain ⟨p, hp⟩ := ha h.1
  obtain ⟨q, hq⟩ := hb h.2
  exact ⟨⟨p, q⟩, fun y hy => AccS_add (hp y hy) (hq y hy)⟩

theorem dsumCS_spec {xa xb : ℝ} (l : List CS) (P : ℕ → Prop) (F : ℕ → ℝ → ℝ)
    (hl : ∀ k < l.length, DSS (l.getD k cs0) (P k) (F k) xa xb) :
    ∀ (s : CS) (Q : Prop) (G : ℝ → ℝ), DSS s Q G xa xb →
      DSS (sumCS l s) (Q ∧ ∀ k < l.length, P k) (fun y => G y + ∑ k ∈ range l.length, F k y) xa xb := by
  induction l generalizing P F with
  | nil => intro s Q G h hok; obtain ⟨q, hq⟩ := h hok; exact ⟨⟨q, fun k hk => absurd hk (by simp)⟩, by simpa using hq⟩
  | cons c l ih =>
    intro s Q G h
    have h0 : DSS c (P 0) (F 0) xa xb := by simpa using hl 0 (by simp)
    have := ih (fun k => P (k + 1)) (fun k => F (k + 1))
      (fun k hk => by simpa using hl (k + 1) (by simp; omega)) (addCS s c) _ _ (DSS_add h h0)
    intro hok
    obtain ⟨⟨⟨q, p0⟩, pk⟩, hb⟩ := this hok
    refine ⟨⟨q, fun k hk => ?_⟩, fun y hy => ?_⟩
    · cases k with
      | zero => exact p0
      | succ k => exact pk k (by simpa using hk)
    · simp only [List.length_cons, sum_range_succ']
      convert hb y hy using 1; ring

theorem DSS_zero {xa xb : ℝ} : DSS cs0 True (fun _ => 0) xa xb :=
  fun _ => ⟨trivial, fun _ _ => AccS_zero⟩

theorem dcolSum_spec {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {DN : ℕ} (hDN : (DN : ℝ) = Den)
    {occ : Bool} {x : EI} {xa xb : ℝ} (hx : EIok x Den xa xb)
    {xs : List (Bool × ℕ)} {rs : List Ent} (hlen : rs.length = xs.length) {I O : ℕ → ℝ}
    (hE : ∀ j < xs.length, EntOK S Den (rs.getD j default) (I j) (O j)) :
    DSS (dcolSum kc DN occ x xs rs) (∀ j < xs.length, EntFix occ S (I j) (O j) xa xb)
      (fun y => ∑ j ∈ range xs.length, wv (xs.getD j (false, 0)) * tD occ S (I j) (O j) y) xa xb := by
  unfold dcolSum
  have hzl : (zipW (fun (w : Bool × ℕ) r => dcontrib kc DN occ x w.1 w.2 r) xs rs).length = xs.length := by
    rw [zipW_length, hlen, min_self]
  have := dsumCS_spec (xa := xa) (xb := xb) (zipW (fun (w : Bool × ℕ) r => dcontrib kc DN occ x w.1 w.2 r) xs rs)
    (fun j => EntFix occ S (I j) (O j) xa xb)
    (fun j y => wv (xs.getD j (false, 0)) * tD occ S (I j) (O j) y)
    (fun k hk => by
      rw [hzl] at hk
      rw [zipW_getD _ cs0 (false, 0) default _ _ k hk (by omega)]
      have := dcontrib_spec (sj := (xs.getD k (false, 0)).1) (cj := (xs.getD k (false, 0)).2) (occ := occ)
        hD hk2 hl htz hDN hx (hE k hk)
      intro hok
      obtain ⟨p, hp⟩ := this hok
      exact ⟨p, fun y hy => by dsimp only; unfold wv; rw [sg_mul_left]; exact hp y hy⟩) cs0 True (fun _ => 0) DSS_zero
  rw [hzl] at this
  intro hok
  obtain ⟨⟨-, p⟩, hb⟩ := this hok
  exact ⟨p, fun y hy => by simpa using hb y hy⟩

/-! ### The whole check -/

theorem DSS_colFin {x : Bool × ℕ} {v : ℕ × ℕ} {c : CS} {P : Prop} {F : ℝ → ℝ} {V xa xb : ℝ}
    (hc : DSS c P F xa xb) (h1 : (v.1 : ℝ) ≤ V) (h2 : V ≤ v.2) :
    DSS (colFin x v c) P (fun y => wv x * (V * F y)) xa xb := fun h => by
  obtain ⟨p, hp⟩ := hc h
  refine ⟨p, fun y hy => ?_⟩
  unfold wv colFin
  dsimp only
  rw [sg_mul_left]; exact sgnA_spec (mulV_spec (hp y hy) h1 h2)

/-- **The derivative hot-path check is sound.** -/
theorem dOK_sound {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {DN RN she tz : ℕ}
    (hDN : (DN : ℝ) = Den) {occ : Bool} {Ca Cb eq : ℤ} {xa xb : ℝ}
    (hx : (mkEI RN she tz Ca Cb eq).2 = true → EIok (mkEI RN she tz Ca Cb eq).1 Den xa xb)
    {xs : List (Bool × ℕ)} {vbS : List (ℕ × ℕ)} {cols : List (List Ent)} {sh : ℕ} {lo hi : ℤ}
    (hn : dOK kc DN RN she tz occ Ca Cb eq xs vbS cols sh lo hi = true) {I O : ℕ → ℕ → ℝ} {V : ℕ → ℝ}
    (hV : ∀ i < xs.length, ((vbS.getD i (0, 0)).1 : ℝ) ≤ V i ∧ V i ≤ (vbS.getD i (0, 0)).2)
    (hE : ∀ i < xs.length, ∀ j < xs.length, EntOK S Den ((cols.getD i []).getD j default) (I j i) (O j i)) :
    (mkEI RN she tz Ca Cb eq).2 = true ∧
    (∀ i < xs.length, ∀ j < xs.length, EntFix occ S (I j i) (O j i) xa xb) ∧
    ∀ y ∈ Icc xa xb,
      (lo : ℝ) * 2 ^ sh ≤ ∑ i ∈ range xs.length, ∑ j ∈ range xs.length,
          wv (xs.getD i (false, 0)) * V i * wv (xs.getD j (false, 0)) * tD occ S (I j i) (O j i) y ∧
      ∑ i ∈ range xs.length, ∑ j ∈ range xs.length,
          wv (xs.getD i (false, 0)) * V i * wv (xs.getD j (false, 0)) * tD occ S (I j i) (O j i) y
        ≤ (hi : ℝ) * 2 ^ sh := by
  unfold dOK at hn
  simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at hn
  obtain ⟨⟨⟨⟨⟨hxi, hok⟩, hl1⟩, hl2⟩, hl3⟩, h0⟩ := hn
  have hxo := hx hxi
  set xi := (mkEI RN she tz Ca Cb eq).1
  set T := sumCS (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (dcolSum kc DN occ xi xs rs))
    (zipW Prod.mk xs vbS) cols) cs0 with hT
  have hzl1 : (zipW Prod.mk xs vbS).length = xs.length := by rw [zipW_length, ← hl2, min_self]
  have hzl : (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (dcolSum kc DN occ xi xs rs))
      (zipW Prod.mk xs vbS) cols).length = xs.length := by rw [zipW_length, hzl1, ← hl1, min_self]
  have hcl : ∀ i < xs.length, (cols.getD i []).length = xs.length := fun i hi => by
    have := List.all_eq_true.mp hl3 _ (getD_mem (l := cols) (i := i) [] (by omega))
    simpa [beq_d] using this
  set W := fun k => wv (xs.getD k (false, 0))
  have hsum := dsumCS_spec (xa := xa) (xb := xb) _
    (fun i => ∀ j < xs.length, EntFix occ S (I j i) (O j i) xa xb)
    (fun i y => W i * (V i * ∑ j ∈ range xs.length, W j * tD occ S (I j i) (O j i) y))
    (fun i hi => by
      rw [hzl] at hi
      rw [zipW_getD _ cs0 ((false, 0), (0, 0)) [] (zipW Prod.mk xs vbS) cols i (by rw [hzl1]; exact hi)
          (by omega),
        zipW_getD _ ((false, 0), (0, 0)) (false, 0) (0, 0) xs vbS i hi (by omega)]
      exact DSS_colFin (dcolSum_spec hD hk2 hl htz hDN hxo (hcl i hi) (fun j hj => hE i hi j hj))
        (hV i hi).1 (hV i hi).2) cs0 True (fun _ => 0) DSS_zero
  rw [hzl] at hsum
  obtain ⟨⟨-, hP⟩, hb⟩ := hsum (by rw [← hT]; exact hok)
  refine ⟨hxi, hP, fun y hy => ?_⟩
  have e : ∑ i ∈ range xs.length, ∑ j ∈ range xs.length, W i * V i * W j * tD occ S (I j i) (O j i) y =
      0 + ∑ i ∈ range xs.length, W i * (V i * ∑ j ∈ range xs.length, W j * tD occ S (I j i) (O j i) y) := by
    rw [zero_add]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
  have := accIn_spec (hb y hy) h0
  simp only [W] at e this
  rw [e]; exact this

end GW.Endpoint.Kernel.QP

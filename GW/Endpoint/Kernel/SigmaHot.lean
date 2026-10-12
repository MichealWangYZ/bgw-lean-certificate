/-
G2 stage 3, soundness (2/4): the hot-path check `nOK` encloses the three quadratic
forms `Σ_i Σ_j W_i V_i W_j F(j, i)` of one (q-point, band, inner band), for
`F = 2^SI (sch - 2 [occ] ssx)` at the two energies and `F = 2^SI IeU(I_eps)` (`I_eps`
zeroed below `TOL_Small`) (`nOK_sound`), given the certified entry facts `EntOK` (proved
by the entry check, `SigmaEnt.lean`) and the Coulomb boxes.
-/
import GW.Endpoint.Kernel.SigmaKernel

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### The entry facts -/

/-- What the entry check certifies about one entry `(j, i)` with `I = I_eps(j, i)`,
`O = Omega²(j, i)`, for the scales `S = 2^SI` and `Den`. -/
structure EntOK (S Den : ℝ) (r : Ent) (I O : ℝ) : Prop where
  c0 : r.cls = 0 → IeU I = 0 ∧ ¬keepM I O
  c1 : 1 ≤ r.cls → IeU I = I ∧ (r.IL : ℝ) ≤ S * I ∧ S * I ≤ r.IH
  c1' : r.cls = 1 → ¬keepM I O
  c2 : 2 ≤ r.cls → keepM I O ∧ 0 < r.tl ∧ (r.tl : ℝ) ≤ wtM I O * Den ∧ wtM I O * Den ≤ r.th ∧
    (0 ≤ r.IL ∨ r.IH < 0)
  t0 : r.cls = 0 → |I| < TS
  t1 : 1 ≤ r.cls → TS ≤ |I|

theorem entD_kept (r : Ent) : (entD r).kept = Nat.ble 2 r.cls := by
  unfold entD; cases r.IL <;> rfl

theorem entD_t (r : Ent) : (entD r).tl = r.tl ∧ (entD r).th = r.th ∧
    (entD r).tl2 = r.tl * r.tl ∧ (entD r).th2 = r.th * r.th := by
  unfold entD; cases r.IL <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem ipos_nn {x : ℤ} (h : 0 ≤ x) : ((ipos x : ℕ) : ℝ) = x := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have : ipos (n : ℤ) = n := rfl
  rw [this]; push_cast; rfl

theorem ineg_neg {x : ℤ} (h : x < 0) : ((ineg x : ℕ) : ℝ) = -x := by
  cases x with
  | ofNat n => exact absurd h (by simp)
  | negSucc n => simp [ineg, Int.negSucc_eq]

theorem entD_nn (r : Ent) (h : 0 ≤ r.IL) :
    (entD r).sI = false ∧ ((entD r).al : ℝ) = r.IL ∧ (entD r).ah = ipos r.IH := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  unfold entD; rw [hn]
  refine ⟨rfl, ?_, rfl⟩
  show ((n : ℕ) : ℝ) = ((n : ℤ) : ℝ); push_cast; rfl

theorem entD_ng (r : Ent) (h : r.IL < 0) :
    (entD r).sI = true ∧ (entD r).al = ineg r.IH ∧ (entD r).ah = ineg r.IL := by
  unfold entD
  cases hh : r.IL with
  | ofNat n => rw [hh] at h; exact absurd h (by simp)
  | negSucc n => simp

/-- The kernel data of a kept entry satisfy `EDok` for the scaled `I`. -/
theorem entD_ok {S Den : ℝ} {r : Ent} {I O : ℝ} (h : EntOK S Den r I O) (h2 : 2 ≤ r.cls) :
    EDok (entD r) Den (wtM I O) (S * I) := by
  obtain ⟨-, htl, hw1, hw2, hsgn⟩ := h.c2 h2
  obtain ⟨-, hI1, hI2⟩ := h.c1 (by omega)
  obtain ⟨et, eth, et2, eth2⟩ := entD_t r
  have hLH : r.IL ≤ r.IH := by exact_mod_cast le_trans hI1 hI2
  refine ⟨by rw [et]; exact htl, by rw [et]; exact hw1, by rw [eth]; exact hw2, by rw [et2, et],
    by rw [eth2, eth], ?_, ?_⟩
  · rcases hsgn with hp | hn
    · obtain ⟨e1, e2, -⟩ := entD_nn r hp
      rw [e1, e2, sg_false]; exact hI1
    · have hIL : r.IL < 0 := by omega
      obtain ⟨e1, e2, -⟩ := entD_ng r hIL
      rw [e1, e2, sg_true, ineg_neg hn]; linarith
  · rcases hsgn with hp | hn
    · obtain ⟨e1, -, e3⟩ := entD_nn r hp
      rw [e1, e3, sg_false, ipos_nn (by omega)]; exact hI2
    · have hIL : r.IL < 0 := by omega
      obtain ⟨e1, -, e3⟩ := entD_ng r hIL
      rw [e1, e3, sg_true, ineg_neg hIL]; linarith

/-! ### Linearity of the kernel in `I` -/

theorem certSsx_smul (c I w x : ℝ) :
    GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC (c * I) w x =
      c * GW.Endpoint.Cert.certSsx GAM2 LIM1 TZ SEXC I w x := by
  unfold GW.Endpoint.Cert.certSsx
  split_ifs <;> ring

/-- `schM` of a kept mode, scaled. -/
theorem schM_kept {S I O x : ℝ} (hk : keepM I O) (hU : IeU I = I) :
    S * schM I O x = if Gen x (wtM I O) then wtM I O * (S * I) / (x - wtM I O) else 0 := by
  unfold schM
  rw [if_pos hk]
  dsimp only
  rw [hU]
  unfold Gen
  split_ifs <;> ring

theorem ssxM_kept {S I O x : ℝ} (hk : keepM I O) (hU : IeU I = I) :
    S * ssxM I O x = ssxV (S * I) (wtM I O) x := by
  unfold ssxM ssxV
  rw [if_pos hk, hU, certSsx_smul]

/-! ### Accumulator semantics -/

/-- `[lp - ln, hp - hn] ∋ y`. -/
def AccS (a : Acc) (y : ℝ) : Prop := (a.lp : ℝ) - a.ln ≤ y ∧ y ≤ (a.hp : ℝ) - a.hn

theorem AccS_zero : AccS acc0 0 := by simp [AccS, acc0]

theorem AccS_add {a b : Acc} {y z : ℝ} (ha : AccS a y) (hb : AccS b z) : AccS (addA a b) (y + z) := by
  unfold AccS addA at *; push_cast; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem smA_spec {b : Bool} {c lo hi : ℕ} {m : ℝ} (h1 : (lo : ℝ) ≤ m) (h2 : m ≤ hi) :
    AccS (smA b c lo hi) (sg b (c * m)) := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  cases b <;> simp only [smA, cond_true, cond_false, AccS, sg_true, sg_false] <;> push_cast <;>
    constructor <;> nlinarith

theorem ivA_spec {s : Bool} {c : ℕ} {IL IH : ℤ} {y : ℝ} (h1 : (IL : ℝ) ≤ y) (h2 : y ≤ IH) :
    AccS (ivA s c IL IH) (sg s (c * y)) := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have eL : ((ipos IL : ℕ) : ℝ) - ineg IL = IL := by exact_mod_cast ipos_sub_ineg IL
  have eH : ((ipos IH : ℕ) : ℝ) - ineg IH = IH := by exact_mod_cast ipos_sub_ineg IH
  cases s <;> simp only [ivA, cond_true, cond_false, AccS, sg_true, sg_false] <;> push_cast <;>
    constructor <;> nlinarith

/-- A state encloses the three targets (when `ok`). -/
def CSS (c : CS) (y0 y1 ya : ℝ) : Prop := c.ok = true → AccS c.p0 y0 ∧ AccS c.p1 y1 ∧ AccS c.ac ya

theorem CSS_zero : CSS cs0 0 0 0 := fun _ => ⟨AccS_zero, AccS_zero, AccS_zero⟩

theorem CSS_add {a b : CS} {a0 a1 aa b0 b1 ba : ℝ} (ha : CSS a a0 a1 aa) (hb : CSS b b0 b1 ba) :
    CSS (addCS a b) (a0 + b0) (a1 + b1) (aa + ba) := fun h => by
  simp only [addCS, Bool.and_eq_true] at h
  obtain ⟨x0, x1, xa⟩ := ha h.1
  obtain ⟨y0, y1, ya⟩ := hb h.2
  exact ⟨AccS_add x0 y0, AccS_add x1 y1, AccS_add xa ya⟩

theorem sumCS_ok {l : List CS} {s : CS} (h : (sumCS l s).ok = true) : s.ok = true := by
  induction l generalizing s with
  | nil => exact h
  | cons a l ih =>
    have := ih (s := addCS s a) h
    simp only [addCS, Bool.and_eq_true] at this; exact this.1

theorem sumCS_spec (l : List CS) (f0 f1 fa : ℕ → ℝ)
    (hl : ∀ k < l.length, CSS (l.getD k cs0) (f0 k) (f1 k) (fa k)) :
    ∀ (s : CS) (a0 a1 aa : ℝ), CSS s a0 a1 aa →
      CSS (sumCS l s) (a0 + ∑ k ∈ range l.length, f0 k) (a1 + ∑ k ∈ range l.length, f1 k)
        (aa + ∑ k ∈ range l.length, fa k) := by
  induction l generalizing f0 f1 fa with
  | nil => intro s a0 a1 aa h; simpa using h
  | cons c l ih =>
    intro s a0 a1 aa h
    have h0 : CSS c (f0 0) (f1 0) (fa 0) := by simpa using hl 0 (by simp)
    have := ih (fun k => f0 (k + 1)) (fun k => f1 (k + 1)) (fun k => fa (k + 1))
      (fun k hk => by simpa using hl (k + 1) (by simp; omega)) (addCS s c) _ _ _ (CSS_add h h0)
    simp only [List.length_cons, sum_range_succ']
    convert this using 1 <;> ring

/-! ### One entry -/

/-- The scaled targets of one entry `(j, i)` of column `i`, weight `(-1)^sj cj`. -/
noncomputable def tP (occ : Bool) (S I O x : ℝ) : ℝ :=
  S * schM I O x - (if occ then 2 * (S * ssxM I O x) else 0)

theorem contrib_spec {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {occ : Bool}
    {e0 e1 : En} {x0 x1 : ℝ} (hx0 : Enok e0 Den x0) (hx1 : Enok e1 Den x1)
    {sj : Bool} {cj : ℕ} {r : Ent} {I O : ℝ} (hr : EntOK S Den r I O) :
    CSS (contrib kc occ e0 e1 sj cj r) (sg sj (cj * tP occ S I O x0)) (sg sj (cj * tP occ S I O x1))
      (sg sj (cj * (S * IeU I))) := by
  intro hok
  -- the static remainder accumulator
  have hac : AccS (bif Nat.ble 1 r.cls then ivA sj cj r.IL r.IH else acc0) (sg sj (cj * (S * IeU I))) := by
    by_cases h1 : 1 ≤ r.cls
    · have hb : Nat.ble 1 r.cls = true := Nat.ble_eq.mpr h1
      rw [hb, cond_true]
      obtain ⟨hU, hI1, hI2⟩ := hr.c1 h1
      rw [hU]; exact ivA_spec hI1 hI2
    · have hb : Nat.ble 1 r.cls = false := by rw [ble_d]; simpa using h1
      rw [hb, cond_false]
      rw [(hr.c0 (by omega)).1]; simp [AccS_zero, sg_zero]
  unfold contrib at hok ⊢
  dsimp only at hok ⊢
  rw [entD_kept] at hok ⊢
  by_cases h2 : 2 ≤ r.cls
  · have hb : Nat.ble 2 r.cls = true := Nat.ble_eq.mpr h2
    simp only [hb, cond_true] at hok ⊢
    obtain ⟨hk, -⟩ := hr.c2 h2
    have hU := (hr.c1 (by omega)).1
    have hed := entD_ok hr h2
    have s0 := schM_kept (S := S) (x := x0) hk hU
    have s1 := schM_kept (S := S) (x := x1) hk hU
    cases occ
    · simp only [cond_false] at hok ⊢
      simp only [Bool.and_eq_true] at hok
      have k0 := schK_spec hD hk2 hl hed hx0 hok.1
      have k1 := schK_spec hD hk2 hl hed hx1 hok.2
      refine ⟨?_, ?_, hac⟩
      · have := smA_spec (b := xor sj (schK kc (entD r) e0).neg) (c := cj) k0.1 k0.2
        rw [sg_xor, sg_mul, sg_sg] at this
        unfold tP; rw [s0]; simpa using this
      · have := smA_spec (b := xor sj (schK kc (entD r) e1).neg) (c := cj) k1.1 k1.2
        rw [sg_xor, sg_mul, sg_sg] at this
        unfold tP; rw [s1]; simpa using this
    · simp only [cond_true] at hok ⊢
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨⟨ha0, ha1⟩, hb0⟩, hb1⟩ := hok
      have k0 := schK_spec hD hk2 hl hed hx0 ha0
      have k1 := schK_spec hD hk2 hl hed hx1 ha1
      have q0 := ssxK_spec hD hk2 hl htz hed hx0 hb0
      have q1 := ssxK_spec hD hk2 hl htz hed hx1 hb1
      have t0 := ssxM_kept (S := S) (x := x0) hk hU
      have t1 := ssxM_kept (S := S) (x := x1) hk hU
      refine ⟨?_, ?_, hac⟩
      · have A := smA_spec (b := xor sj (schK kc (entD r) e0).neg) (c := cj) k0.1 k0.2
        have B := smA_spec (b := !(xor sj (ssxK kc (entD r) e0).neg)) (c := 2 * cj) q0.1 q0.2
        have := AccS_add A B
        unfold tP; rw [s0, t0, if_pos rfl]
        convert this using 1
        generalize (schK kc (entD r) e0).neg = n1 at *
        generalize (ssxK kc (entD r) e0).neg = n2 at *
        cases sj <;> cases n1 <;> cases n2 <;> simp only [sg, Bool.not_false, Bool.not_true, if_true,
          if_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true, Bool.true_xor, Bool.false_xor,
          Bool.not_not] <;> push_cast <;> ring
      · have A := smA_spec (b := xor sj (schK kc (entD r) e1).neg) (c := cj) k1.1 k1.2
        have B := smA_spec (b := !(xor sj (ssxK kc (entD r) e1).neg)) (c := 2 * cj) q1.1 q1.2
        have := AccS_add A B
        unfold tP; rw [s1, t1, if_pos rfl]
        convert this using 1
        generalize (schK kc (entD r) e1).neg = n1 at *
        generalize (ssxK kc (entD r) e1).neg = n2 at *
        cases sj <;> cases n1 <;> cases n2 <;> simp only [sg, Bool.not_false, Bool.not_true, if_true,
          if_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true, Bool.true_xor, Bool.false_xor,
          Bool.not_not] <;> push_cast <;> ring
  · have hb : Nat.ble 2 r.cls = false := by rw [ble_d]; simpa using h2
    simp only [hb, cond_false]
    have hnk : ¬keepM I O := by
      rcases Nat.lt_or_ge r.cls 1 with h | h
      · exact (hr.c0 (by omega)).2
      · exact hr.c1' (by omega)
    have z0 : tP occ S I O x0 = 0 := by unfold tP schM ssxM; simp [hnk]
    have z1 : tP occ S I O x1 = 0 := by unfold tP schM ssxM; simp [hnk]
    rw [z0, z1]
    refine ⟨by simpa [sg_zero] using AccS_zero, by simpa [sg_zero] using AccS_zero, hac⟩

/-! ### Columns and the whole check -/

/-- The real weight `(-1)^s c` of a weight record. -/
def wv (x : Bool × ℕ) : ℝ := sg x.1 x.2

theorem sg_mul_left (b : Bool) (u v : ℝ) : sg b u * v = sg b (u * v) := by cases b <;> simp

theorem contribZ_spec {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {occ : Bool}
    {e0 e1 : En} {x0 x1 : ℝ} (hx0 : Enok e0 Den x0) (hx1 : Enok e1 Den x1)
    {x : Bool × ℕ} {r : Ent} {I O : ℝ} (hr : EntOK S Den r I O) :
    CSS (contribZ kc occ e0 e1 x r) (wv x * tP occ S I O x0) (wv x * tP occ S I O x1)
      (wv x * (S * IeU I)) := by
  unfold contribZ wv
  cases hz : Nat.beq x.2 0
  · simp only [cond_false]
    have := contrib_spec (sj := x.1) (cj := x.2) (occ := occ) hD hk2 hl htz hx0 hx1 hr
    rw [sg_mul_left, sg_mul_left, sg_mul_left]; exact this
  · simp only [cond_true]
    have : x.2 = 0 := by simpa [beq_d] using hz
    rw [this]; simpa [sg_zero] using CSS_zero

theorem colSum_spec {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {occ : Bool}
    {e0 e1 : En} {x0 x1 : ℝ} (hx0 : Enok e0 Den x0) (hx1 : Enok e1 Den x1)
    {xs : List (Bool × ℕ)} {rs : List Ent} (hlen : rs.length = xs.length) {I O : ℕ → ℝ}
    (hE : ∀ j < xs.length, EntOK S Den (rs.getD j default) (I j) (O j)) :
    CSS (colSum kc occ e0 e1 xs rs)
      (∑ j ∈ range xs.length, wv (xs.getD j (false, 0)) * tP occ S (I j) (O j) x0)
      (∑ j ∈ range xs.length, wv (xs.getD j (false, 0)) * tP occ S (I j) (O j) x1)
      (∑ j ∈ range xs.length, wv (xs.getD j (false, 0)) * (S * IeU (I j))) := by
  unfold colSum
  have hzl : (zipW (contribZ kc occ e0 e1) xs rs).length = xs.length := by
    rw [zipW_length, hlen, min_self]
  have := sumCS_spec (zipW (contribZ kc occ e0 e1) xs rs)
    (fun j => wv (xs.getD j (false, 0)) * tP occ S (I j) (O j) x0)
    (fun j => wv (xs.getD j (false, 0)) * tP occ S (I j) (O j) x1)
    (fun j => wv (xs.getD j (false, 0)) * (S * IeU (I j)))
    (fun k hk => by
      rw [hzl] at hk
      rw [zipW_getD _ cs0 (false, 0) default _ _ k hk (by omega)]
      exact contribZ_spec hD hk2 hl htz hx0 hx1 (hE k hk)) cs0 0 0 0 CSS_zero
  rw [hzl] at this; simpa using this

theorem mulV_spec {vl vh : ℕ} {a : Acc} {V y : ℝ} (ha : AccS a y) (h1 : (vl : ℝ) ≤ V)
    (h2 : V ≤ vh) : AccS (mulV vl vh a) (V * y) := by
  have hv0 : (0 : ℝ) ≤ vl := Nat.cast_nonneg _
  have hV : 0 ≤ V := le_trans hv0 h1
  obtain ⟨ha1, ha2⟩ := ha
  unfold mulV AccS
  simp only [ble_d, Bool.cond_decide]
  constructor
  · by_cases h : a.ln ≤ a.lp
    · simp only [h, if_true]; push_cast [Nat.cast_sub h]
      have : (0 : ℝ) ≤ (a.lp : ℝ) - a.ln := by
        have : (a.ln : ℝ) ≤ a.lp := by exact_mod_cast h
        linarith
      nlinarith
    · simp only [h, if_false]
      have h' : a.lp ≤ a.ln := by omega
      push_cast [Nat.cast_sub h']
      have : (a.lp : ℝ) - a.ln ≤ 0 := by
        have : (a.lp : ℝ) ≤ a.ln := by exact_mod_cast h'
        linarith
      nlinarith
  · by_cases h : a.hn ≤ a.hp
    · simp only [h, if_true]; push_cast [Nat.cast_sub h]
      have : (0 : ℝ) ≤ (a.hp : ℝ) - a.hn := by
        have : (a.hn : ℝ) ≤ a.hp := by exact_mod_cast h
        linarith
      nlinarith
    · simp only [h, if_false]
      have h' : a.hp ≤ a.hn := by omega
      push_cast [Nat.cast_sub h']
      have : (a.hp : ℝ) - a.hn ≤ 0 := by
        have : (a.hp : ℝ) ≤ a.hn := by exact_mod_cast h'
        linarith
      nlinarith

theorem sgnA_spec {s : Bool} {c : ℕ} {a : Acc} {y : ℝ} (ha : AccS a y) :
    AccS (sgnA s c a) (sg s (c * y)) := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  obtain ⟨h1, h2⟩ := ha
  cases s <;> simp only [sgnA, cond_true, cond_false, AccS, sg_true, sg_false] <;> push_cast <;>
    constructor <;> nlinarith

theorem colFin_spec {x : Bool × ℕ} {v : ℕ × ℕ} {c : CS} {y0 y1 ya V : ℝ} (hc : CSS c y0 y1 ya)
    (h1 : (v.1 : ℝ) ≤ V) (h2 : V ≤ v.2) :
    CSS (colFin x v c) (wv x * (V * y0)) (wv x * (V * y1)) (wv x * (V * ya)) := fun h => by
  obtain ⟨a0, a1, aa⟩ := hc h
  unfold wv
  refine ⟨?_, ?_, ?_⟩ <;> rw [sg_mul_left] <;> exact sgnA_spec (mulV_spec (by assumption) h1 h2)

theorem accIn_spec {a : Acc} {sh : ℕ} {lo hi : ℤ} {y : ℝ} (ha : AccS a y) (h : accIn a sh lo hi = true) :
    (lo : ℝ) * 2 ^ sh ≤ y ∧ y ≤ (hi : ℝ) * 2 ^ sh := by
  unfold accIn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : ((lo * 2 ^ sh : ℤ) : ℝ) ≤ (((a.lp : ℤ) - a.ln : ℤ) : ℝ) := by exact_mod_cast h.1
  have h2 : (((a.hp : ℤ) - a.hn : ℤ) : ℝ) ≤ ((hi * 2 ^ sh : ℤ) : ℝ) := by exact_mod_cast h.2
  push_cast at h1 h2
  exact ⟨le_trans h1 ha.1, le_trans ha.2 h2⟩

/-- **The hot-path check is sound**: with `W_k` the weights, `V_i ∈ vbS_i` (scaled
Coulomb averages), and the certified entry facts of every entry `(j, i)` (record
`cols i j`), the three quadratic forms lie in the claimed enclosures `o · 2^sh`. -/
theorem nOK_sound {Den S : ℝ} (hD : 0 < Den) {kc : KC} (hk2 : (kc.Den2 : ℝ) = Den ^ 2)
    (hl : kc.lim1 = 250000) (htz : TZ = (kc.tzn : ℝ) / 2 ^ kc.tze) {occ : Bool}
    {e0 e1 : En} {x0 x1 : ℝ} (hx0 : Enok e0 Den x0) (hx1 : Enok e1 Den x1)
    {xs : List (Bool × ℕ)} {vbS : List (ℕ × ℕ)} {cols : List (List Ent)} {sh : ℕ} {o : List ℤ}
    (hn : nOK kc occ e0 e1 xs vbS cols sh o = true) {I O : ℕ → ℕ → ℝ} {V : ℕ → ℝ}
    (hV : ∀ i < xs.length, ((vbS.getD i (0, 0)).1 : ℝ) ≤ V i ∧ V i ≤ (vbS.getD i (0, 0)).2)
    (hE : ∀ i < xs.length, ∀ j < xs.length, EntOK S Den ((cols.getD i []).getD j default) (I j i) (O j i)) :
    let W := fun k => wv (xs.getD k (false, 0))
    let Q := fun F : ℕ → ℕ → ℝ => ∑ i ∈ range xs.length, ∑ j ∈ range xs.length, W i * V i * W j * F j i
    ((o.getD 0 0 : ℝ) * 2 ^ sh ≤ Q (fun j i => tP occ S (I j i) (O j i) x0) ∧
      Q (fun j i => tP occ S (I j i) (O j i) x0) ≤ (o.getD 1 0 : ℝ) * 2 ^ sh) ∧
    ((o.getD 2 0 : ℝ) * 2 ^ sh ≤ Q (fun j i => tP occ S (I j i) (O j i) x1) ∧
      Q (fun j i => tP occ S (I j i) (O j i) x1) ≤ (o.getD 3 0 : ℝ) * 2 ^ sh) ∧
    ((o.getD 4 0 : ℝ) * 2 ^ sh ≤ Q (fun j i => S * IeU (I j i)) ∧
      Q (fun j i => S * IeU (I j i)) ≤ (o.getD 5 0 : ℝ) * 2 ^ sh) := by
  intro W Q
  unfold nOK at hn
  simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at hn
  obtain ⟨⟨⟨⟨⟨⟨hok, hl1⟩, hl2⟩, hl3⟩, h0⟩, h1⟩, h2⟩ := hn
  set T := sumCS (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (colSum kc occ e0 e1 xs rs))
    (zipW Prod.mk xs vbS) cols) cs0 with hT
  have hzl1 : (zipW Prod.mk xs vbS).length = xs.length := by rw [zipW_length, ← hl2, min_self]
  have hzl : (zipW (fun (xv : (Bool × ℕ) × (ℕ × ℕ)) rs => colFin xv.1 xv.2 (colSum kc occ e0 e1 xs rs))
      (zipW Prod.mk xs vbS) cols).length = xs.length := by rw [zipW_length, hzl1, ← hl1, min_self]
  have hcl : ∀ i < xs.length, (cols.getD i []).length = xs.length := fun i hi => by
    have := List.all_eq_true.mp hl3 _ (getD_mem (l := cols) (i := i) [] (by omega))
    simpa [beq_d] using this
  have hsum := sumCS_spec _
    (fun i => W i * (V i * ∑ j ∈ range xs.length, W j * tP occ S (I j i) (O j i) x0))
    (fun i => W i * (V i * ∑ j ∈ range xs.length, W j * tP occ S (I j i) (O j i) x1))
    (fun i => W i * (V i * ∑ j ∈ range xs.length, W j * (S * IeU (I j i))))
    (fun i hi => by
      rw [hzl] at hi
      rw [zipW_getD _ cs0 ((false, 0), (0, 0)) [] (zipW Prod.mk xs vbS) cols i (by rw [hzl1]; exact hi)
          (by omega),
        zipW_getD _ ((false, 0), (0, 0)) (false, 0) (0, 0) xs vbS i hi (by omega)]
      exact colFin_spec (colSum_spec hD hk2 hl htz hx0 hx1 (hcl i hi) (fun j hj => hE i hi j hj))
        (hV i hi).1 (hV i hi).2) cs0 0 0 0 CSS_zero
  rw [hzl] at hsum
  obtain ⟨a0, a1, aa⟩ := hsum (by rw [← hT]; exact hok)
  have eQ : ∀ F : ℕ → ℕ → ℝ, Q F = 0 + ∑ i ∈ range xs.length, W i * (V i * ∑ j ∈ range xs.length, W j * F j i) :=
    fun F => by
      simp only [Q, zero_add]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
  rw [eQ, eQ, eQ]
  exact ⟨accIn_spec a0 h0, accIn_spec a1 h1, accIn_spec aa h2⟩

end GW.Endpoint.Kernel.Sig

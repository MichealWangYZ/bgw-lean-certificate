/-
G2 stage 2: soundness of the eps checker (`EpsCheck.lean`) for the real
dielectric matrix `epsR` (`EpsSpec.lean`).

`Eps.sound_rows`: if `kOK` holds for every k-point (the hints are the exact pair
densities, read off Kronecker products) and `chiGlobal` and `chiRows` hold for the rows
`r0 … r0 + L - 1` (the exactly accumulated `Σ D m m'` with the bracketed
`1/(E_c - E_v)`, `v · 4/(N_k Ω)` and π lands inside the box), then for those rows every
entry `epsR i j` lies in `[lo_ij, hi_ij] / 2^SE`. The per-q statement over all rows is
assembled from these row blocks in the data modules (`Data/E*Check`).
-/
import GW.Endpoint.Kernel.EpsSpec
import GW.Endpoint.Kernel.Sound
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Real.Pi.Bounds

namespace GW.Endpoint.Kernel.Eps

open Finset GW.Endpoint.Kernel

/-! ### Signed integers through `ℕ` -/

theorem ipos_sub_ineg (x : ℤ) : (ipos x : ℤ) - ineg x = x := by
  cases x with
  | ofNat n => simp [ipos, ineg]
  | negSucc n => simp [ipos, ineg, Int.negSucc_eq]

theorem ipos_add_ineg (x : ℤ) : ipos x + ineg x = x.natAbs := by
  cases x with
  | ofNat n => simp [ipos, ineg]
  | negSucc n => simp [ipos, ineg, Int.natAbs_negSucc]

theorem zeq_spec {d : ℕ} {x : ℤ} {h : ℕ} (hz : zeq d x h = true) : (d : ℤ) = x + h := by
  cases x with
  | ofNat a => simp only [zeq, Nat.beq_eq] at hz; subst hz; simp
  | negSucc a => simp only [zeq, Nat.beq_eq] at hz; rw [Int.negSucc_eq]; push_cast [← hz]; ring

theorem zleS_spec {x : ℤ} {k l r : ℕ} (hz : zleS x k l r = true) : x * k + l ≤ (r : ℤ) := by
  cases x with
  | ofNat a => simp only [zleS, Nat.ble_eq] at hz; simp only [Int.ofNat_eq_coe]; exact_mod_cast hz
  | negSucc a =>
    simp only [zleS, Nat.ble_eq] at hz; rw [Int.negSucc_eq]
    have : (l : ℤ) ≤ r + (a + 1) * k := by exact_mod_cast hz
    linarith

theorem zgeS_spec {x : ℤ} {k l r : ℕ} (hz : zgeS x k l r = true) : (l : ℤ) ≤ x * k + r := by
  cases x with
  | ofNat a => simp only [zgeS, Nat.ble_eq] at hz; simp only [Int.ofNat_eq_coe]; exact_mod_cast hz
  | negSucc a =>
    simp only [zgeS, Nat.ble_eq] at hz; rw [Int.negSucc_eq]
    have : (l : ℤ) + (a + 1) * k ≤ r := by exact_mod_cast hz
    linarith

/-! ### List functions -/

section lists

variable {α β γ : Type}

@[simp] theorem mapL_nil (g : α → β) : mapL g [] = [] := rfl
@[simp] theorem mapL_cons (g : α → β) (a : α) (l : List α) : mapL g (a :: l) = g a :: mapL g l := rfl

theorem mapL_eq (g : α → β) : ∀ l : List α, mapL g l = l.map g
  | [] => rfl
  | a :: l => by simp [mapL_eq g l]

@[simp] theorem fold2_nil (f : α → β → γ → γ) (ys : List β) (acc : γ) : fold2 f [] ys acc = acc := rfl
@[simp] theorem fold2_cons_nil (f : α → β → γ → γ) (a : α) (l : List α) (acc : γ) :
    fold2 f (a :: l) [] acc = acc := rfl
@[simp] theorem fold2_cons_cons (f : α → β → γ → γ) (a : α) (l : List α) (y : β) (ys : List β)
    (acc : γ) : fold2 f (a :: l) (y :: ys) acc = fold2 f l ys (f a y acc) := rfl

/-- A fold that adds `g k` (for the `k`-th pair of list elements) to an integer-valued
measurement `F` of its state, while preserving an invariant `P`, adds `Σ_k g k`. -/
theorem fold2_sum (f : α → β → γ → γ) (P : γ → Prop) (F : γ → ℤ) (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β) (g : ℕ → ℤ) (x : γ), l1.length = l2.length →
      (∀ k < l1.length, ∀ y, P y →
        P (f (l1.getD k d1) (l2.getD k d2) y) ∧ F (f (l1.getD k d1) (l2.getD k d2) y) = F y + g k) →
      P x → P (fold2 f l1 l2 x) ∧ F (fold2 f l1 l2 x) = F x + ∑ k ∈ range l1.length, g k
  | [], [], _, x, _, _, hx => by simp [hx]
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | a :: l1, b :: l2, g, x, h, hf, hx => by
      obtain ⟨hP, hF⟩ := hf 0 (by simp) x hx
      simp only [List.getD_cons_zero] at hP hF
      obtain ⟨hP', hF'⟩ := fold2_sum f P F d1 d2 l1 l2 (fun k => g (k + 1)) (f a b x)
        (by simpa using h) (fun k hk y hy => by simpa using hf (k + 1) (by simpa using hk) y hy) hP
      refine ⟨by simpa using hP', ?_⟩
      rw [fold2_cons_cons, hF', hF, List.length_cons, sum_range_succ']
      ring

theorem getD_mem {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem all_getD {p : α → Bool} {l : List α} (h : l.all p = true) {i : ℕ} (d : α)
    (hi : i < l.length) : p (l.getD i d) = true :=
  List.all_eq_true.mp h _ (getD_mem d hi)

theorem getD_drop' (l : List α) (r k : ℕ) (d : α) : (l.drop r).getD k d = l.getD (r + k) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem mapL_length (g : α → β) (l : List α) : (mapL g l).length = l.length := by
  simp [mapL_eq]

theorem mapL_getD (g : α → β) (l : List α) (i : ℕ) (d : α) (h : i < l.length) (d' : β) :
    (mapL g l).getD i d' = g (l.getD i d) := by
  rw [mapL_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  simp

end lists

/-! ### Packing and digits -/

theorem sumL_nat_eq (l : List ℕ) : sumL l 0 = ∑ j ∈ range l.length, l.getD j 0 := by
  rw [sumL_eq]; simp

/-- `packPos - packNeg` is the signed packed sum. -/
theorem pack_eq (W : ℕ) (ps : List ℕ) (cs : List ℤ) (h : ps.length = cs.length) :
    ((packPos W ps cs : ℕ) : ℤ) - packNeg W ps cs =
      ∑ i ∈ range cs.length, cs.getD i 0 * ((2 : ℤ) ^ W) ^ ps.getD i 0 := by
  have hz : ∀ (g : ℤ → ℕ), sumL (zipW (fun p c => g c <<< (W * p)) ps cs) 0 =
      ∑ i ∈ range cs.length, g (cs.getD i 0) * 2 ^ (W * ps.getD i 0) := by
    intro g
    rw [sumL_nat_eq, zipW_length, h, min_self]
    refine sum_congr rfl fun i hi => ?_
    rw [zipW_getD _ 0 0 0 ps cs i (by rw [h]; exact mem_range.mp hi) (mem_range.mp hi),
      Nat.shiftLeft_eq]
  simp only [packPos, packNeg, hz]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sub_mul, ipos_sub_ineg, ← pow_mul]

theorem l1_eq (cs : List ℤ) : (l1 cs : ℤ) = ∑ i ∈ range cs.length, |cs.getD i 0| := by
  rw [l1, sumL_nat_eq, mapL_length]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  rw [mapL_getD _ _ _ 0 (mem_range.mp hi), ipos_add_ineg, Int.natCast_natAbs]

/-- `(Σ_{s<T} d_s B^s) / B^m % B = d_m` for digits `d_s < B`. -/
theorem digit_nat (B : ℕ) (hB : 0 < B) (d : ℕ → ℕ) (hd : ∀ s, d s < B) :
    ∀ T : ℕ, (∑ s ∈ range T, d s * B ^ s < B ^ T) ∧
      ∀ m < T, (∑ s ∈ range T, d s * B ^ s) / B ^ m % B = d m
  | 0 => by simp
  | T + 1 => by
    obtain ⟨hlt, hdig⟩ := digit_nat B hB d hd T
    have hBT : 0 < B ^ T := pow_pos hB T
    refine ⟨?_, fun m hm => ?_⟩
    · rw [sum_range_succ, pow_succ]
      calc _ < B ^ T + d T * B ^ T := by omega
        _ = (d T + 1) * B ^ T := by ring
        _ ≤ B * B ^ T := Nat.mul_le_mul_right _ (hd T)
        _ = B ^ T * B := by ring
    rw [sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · obtain ⟨e, rfl⟩ : ∃ e, T = m + (e + 1) := ⟨T - m - 1, by omega⟩
      have hsplit : d (m + (e + 1)) * B ^ (m + (e + 1)) = B ^ m * (d (m + (e + 1)) * B ^ (e + 1)) := by
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos hB m), Nat.add_mod, pow_succ,
        show d (m + (e + 1)) * (B ^ e * B) = (d (m + (e + 1)) * B ^ e) * B by ring,
        Nat.mul_mod_left, add_zero, Nat.mod_mod]
      exact hdig m hm
    · rw [Nat.add_mul_div_right _ _ hBT, Nat.div_eq_of_lt hlt, zero_add, Nat.mod_eq_of_lt (hd m)]

/-- The bias `Σ_{s<T} 2^(W-1) 2^(W s)`. -/
theorem bias_eq (W T : ℕ) (hW : 0 < W) :
    bias W T = ∑ s ∈ range T, 2 ^ (W - 1) * (2 ^ W) ^ s := by
  rw [bias, ← mul_sum, Nat.geomSum_eq _ T, pow_mul]
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW

/-- **Digit extraction.** If `N = Σ_{s<T} C_s 2^(W s)` with `|C_s| < 2^(W-1)`, then
`N + bias ≥ 0` and its base-`2^W` digit `m` is `C_m + 2^(W-1)`. -/
theorem digit_int (W T : ℕ) (hW : 0 < W) (C : ℕ → ℤ) (hC : ∀ s < T, |C s| < 2 ^ (W - 1))
    (N : ℤ) (hN : N = ∑ s ∈ range T, C s * (2 ^ W) ^ s) :
    0 ≤ N + bias W T ∧ ∀ m < T,
      ((((N + bias W T).toNat >>> (W * m)) % 2 ^ W : ℕ) : ℤ) = C m + 2 ^ (W - 1) := by
  obtain ⟨h, hh⟩ : ∃ h : ℕ, h = 2 ^ (W - 1) := ⟨_, rfl⟩
  have hhz : (2 : ℤ) ^ (W - 1) = (h : ℤ) := by rw [hh]; push_cast; rfl
  rw [hhz] at hC ⊢
  have hB : 2 ^ W = 2 * h := by rw [hh, ← pow_succ']; congr 1; omega
  let d : ℕ → ℕ := fun s => if s < T then (C s + h).toNat else 0
  have hd : ∀ s, d s < 2 ^ W := by
    intro s; simp only [d]; split_ifs with hs
    · have := abs_lt.mp (hC s hs); rw [hB]; omega
    · exact Nat.pow_pos (by norm_num)
  have hsum : N + bias W T = ((∑ s ∈ range T, d s * (2 ^ W) ^ s : ℕ) : ℤ) := by
    rw [bias_eq W T hW, hN, ← hh]; push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun s hs => ?_
    have hs' := mem_range.mp hs
    have := abs_lt.mp (hC s hs')
    simp only [d, if_pos hs']
    rw [Int.toNat_of_nonneg (by omega)]; ring
  refine ⟨by rw [hsum]; positivity, fun m hm => ?_⟩
  rw [hsum, Int.toNat_natCast, Nat.shiftRight_eq_div_pow, pow_mul,
    (digit_nat (2 ^ W) (by positivity) d hd T).2 m hm]
  have := abs_lt.mp (hC m hm)
  simp only [d, if_pos hm]
  rw [Int.toNat_of_nonneg (by omega)]

/-- Sparse product: the packed product groups the terms by slot. -/
theorem kron_prod (W T : ℕ) (ps qs : List ℕ) (as bs : List ℤ) (hp : ps.length = as.length)
    (hq : qs.length = bs.length)
    (hT : ∀ i < as.length, ∀ l < bs.length, ps.getD i 0 + qs.getD l 0 < T) :
    (((packPos W ps as : ℕ) : ℤ) - packNeg W ps as) * (((packPos W qs bs : ℕ) : ℤ) - packNeg W qs bs) =
      ∑ s ∈ range T, (∑ i ∈ range as.length, ∑ l ∈ range bs.length,
        if ps.getD i 0 + qs.getD l 0 = s then as.getD i 0 * bs.getD l 0 else 0) * (2 ^ W) ^ s := by
  rw [pack_eq W ps as hp, pack_eq W qs bs hq, sum_mul_sum]
  symm
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l hl => ?_
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_range.mpr (hT i (mem_range.mp hi) l (mem_range.mp hl))), pow_add]
  ring

theorem kron_bound (P : ℕ → ℕ → Prop) [∀ i l, Decidable (P i l)] (as bs : List ℤ) :
    |∑ i ∈ range as.length, ∑ l ∈ range bs.length,
        if P i l then as.getD i 0 * bs.getD l 0 else 0| ≤ (l1 as : ℤ) * l1 bs := by
  rw [l1_eq, l1_eq, sum_mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
  split_ifs
  · rw [abs_mul]
  · simp only [abs_zero]; positivity

/-! ### The Kronecker index -/

theorem inBox_spec {lo hi : ℤ} {g : V3} (h : inBox lo hi g = true) :
    lo ≤ g.1 ∧ g.1 ≤ hi ∧ lo ≤ g.2.1 ∧ g.2.1 ≤ hi ∧ lo ≤ g.2.2 ∧ g.2.2 ≤ hi := by
  simpa [inBox, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem eq_zero_of_abs_lt_of_dvd {L x : ℤ} (hx : |x| < L) (hd : L ∣ x) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd hd hx

/-- `φ` is injective on vectors with components of absolute value `< L`. -/
theorem phi_zero {L : ℤ} {d : V3} (h1 : |d.1| < L) (h2 : |d.2.1| < L) (h3 : |d.2.2| < L)
    (h : phi L d = 0) : d = 0 := by
  obtain ⟨a, b, c⟩ := d
  simp only [phi] at h h1 h2 h3
  have hL : 0 < L := lt_of_le_of_lt (abs_nonneg _) h1
  have ha : a = 0 := eq_zero_of_abs_lt_of_dvd h1 ⟨-(b + L * c), by linarith⟩
  subst ha
  have h' : b + L * c = 0 := by
    have : L * (b + L * c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hL.ne'
    · exact h0
  have hb : b = 0 := eq_zero_of_abs_lt_of_dvd h2 ⟨-c, by linarith⟩
  subst hb
  have hc : c = 0 := by
    rcases mul_eq_zero.mp (show L * c = 0 by linarith) with h0 | h0
    · exact absurd h0 hL.ne'
    · exact h0
  subst hc; rfl

namespace Cfg

variable (cf : Cfg)

theorem phi_bounds {g : V3} (hL : 0 ≤ cf.L)
    (hg : inBox cf.lo (cf.lo + cf.H) g = true) :
    0 ≤ phi cf.L g - cf.lo * Phi1 cf.L ∧ phi cf.L g - cf.lo * Phi1 cf.L ≤ cf.H * Phi1 cf.L := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
  have e : phi cf.L g - cf.lo * Phi1 cf.L =
      (g.1 - cf.lo) + cf.L * (g.2.1 - cf.lo) + cf.L * cf.L * (g.2.2 - cf.lo) := by
    simp only [phi, Phi1]; ring
  have eH : cf.H * Phi1 cf.L = cf.H + cf.L * cf.H + cf.L * cf.L * cf.H := by simp only [Phi1]; ring
  rw [e, eH]
  have hLL : 0 ≤ cf.L * cf.L := mul_nonneg hL hL
  constructor
  · have := mul_nonneg hL (show 0 ≤ g.2.1 - cf.lo by linarith)
    have := mul_nonneg hLL (show 0 ≤ g.2.2 - cf.lo by linarith)
    linarith
  · have := mul_le_mul_of_nonneg_left (show g.2.1 - cf.lo ≤ cf.H by linarith) hL
    have := mul_le_mul_of_nonneg_left (show g.2.2 - cf.lo ≤ cf.H by linarith) hLL
    linarith

theorem phi_bounds' {G : V3} (hL : 0 ≤ cf.L) (hG : inBox (-cf.H) cf.H G = true) :
    -(cf.H * Phi1 cf.L) ≤ phi cf.L G ∧ phi cf.L G ≤ cf.H * Phi1 cf.L := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hG
  have eH : cf.H * Phi1 cf.L = cf.H + cf.L * cf.H + cf.L * cf.L * cf.H := by simp only [Phi1]; ring
  rw [eH]; simp only [phi]
  have hLL : 0 ≤ cf.L * cf.L := mul_nonneg hL hL
  have := mul_le_mul_of_nonneg_left b2 hL
  have := mul_le_mul_of_nonneg_left c2 hLL
  have := mul_le_mul_of_nonneg_left b1 hL
  have := mul_le_mul_of_nonneg_left c1 hLL
  constructor <;> nlinarith

theorem so_lt {G : V3} (hL : 2 * cf.H < cf.L) (hG : inBox (-cf.H) cf.H G = true) :
    cf.so G < cf.T := by
  obtain ⟨s1, s2⟩ := cf.phi_bounds' (by linarith [(inBox_spec hG).1, (inBox_spec hG).2.1]) hG
  have hH : 0 ≤ cf.H := by linarith [(inBox_spec hG).1, (inBox_spec hG).2.1]
  have hP : 0 ≤ Phi1 cf.L := by simp only [Phi1]; nlinarith
  have hso : (cf.so G : ℤ) = phi cf.L G + cf.H * Phi1 cf.L := Int.toNat_of_nonneg (by linarith)
  have hT : (cf.T : ℤ) = 2 * cf.H * Phi1 cf.L + 1 := Int.toNat_of_nonneg (by nlinarith)
  have : (cf.so G : ℤ) < cf.T := by rw [hso, hT]; linarith
  exact_mod_cast this

/-- In the boxes, the slots of `g` (valence) and `g'` (conduction) add up to the
slot of `G` exactly when `g - g' = G`; all slots are below `T`. -/
theorem slot_iff {g g' G : V3} (hH : 0 ≤ cf.H) (hL : 2 * cf.H < cf.L)
    (hg : inBox cf.lo (cf.lo + cf.H) g = true) (hg' : inBox cf.lo (cf.lo + cf.H) g' = true)
    (hG : inBox (-cf.H) cf.H G = true) :
    (cf.ev g + cf.fc g' = cf.so G ↔ g - g' = G) ∧ cf.ev g + cf.fc g' < cf.T ∧ cf.so G < cf.T := by
  have hL0 : 0 ≤ cf.L := by linarith
  obtain ⟨e1, e2⟩ := cf.phi_bounds hL0 hg
  obtain ⟨f1, f2⟩ := cf.phi_bounds hL0 hg'
  obtain ⟨s1, s2⟩ := cf.phi_bounds' hL0 hG
  have hev : (cf.ev g : ℤ) = phi cf.L g - cf.lo * Phi1 cf.L := Int.toNat_of_nonneg e1
  have hfc : (cf.fc g' : ℤ) = (cf.lo + cf.H) * Phi1 cf.L - phi cf.L g' :=
    Int.toNat_of_nonneg (by nlinarith)
  have hso : (cf.so G : ℤ) = phi cf.L G + cf.H * Phi1 cf.L := Int.toNat_of_nonneg (by linarith)
  have hT : (cf.T : ℤ) = 2 * cf.H * Phi1 cf.L + 1 := Int.toNat_of_nonneg (by nlinarith)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have hz : (cf.ev g : ℤ) + cf.fc g' = cf.so G := by exact_mod_cast h
    rw [hev, hfc, hso] at hz
    have hphi : phi cf.L (g - g' - G) = 0 := by
      obtain ⟨a, b, c⟩ := g; obtain ⟨a', b', c'⟩ := g'; obtain ⟨A, B, C⟩ := G
      simp only [phi, Prod.mk_sub_mk] at hz ⊢; linarith
    obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
    obtain ⟨a1', a2', b1', b2', c1', c2'⟩ := inBox_spec hg'
    obtain ⟨A1, A2, B1, B2, C1, C2⟩ := inBox_spec hG
    have := phi_zero (L := cf.L) (d := g - g' - G) (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [abs_lt]; constructor <;> linarith)
      (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [abs_lt]; constructor <;> linarith)
      (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [abs_lt]; constructor <;> linarith) hphi
    rw [sub_eq_zero] at this; exact this
  · subst h
    have : (cf.ev g : ℤ) + cf.fc g' = cf.so (g - g') := by
      rw [hev, hfc, show (cf.so (g - g') : ℤ) = phi cf.L (g - g') + cf.H * Phi1 cf.L from hso]
      obtain ⟨a, b, c⟩ := g; obtain ⟨a', b', c'⟩ := g'
      simp only [phi, Prod.mk_sub_mk]; ring
    exact_mod_cast this
  · have : (cf.ev g : ℤ) + cf.fc g' < cf.T := by rw [hev, hfc, hT]; linarith
    exact_mod_cast this
  · have : (cf.so G : ℤ) < cf.T := by rw [hso, hT]; linarith
    exact_mod_cast this

end Cfg

/-! ### Soundness of the pair-density check -/

/-- The pair density as an integer at scale `2^-(2 SC)`. -/
def Mint (kp : KPair) (v c : ℕ) (G : V3) : ℤ :=
  ∑ i ∈ range kp.Gv.length, ∑ j ∈ range kp.Gc.length,
    if kp.Gv.getD i 0 - kp.Gc.getD j 0 = G then (kp.cv.getD v []).getD i 0 * (kp.cc.getD c []).getD j 0
    else 0

theorem M_eq (inp : Input) (kp : KPair) (v c : ℕ) (G : V3) :
    M inp kp v c G = (Mint kp v c G : ℝ) / 2 ^ (2 * inp.SC) := by
  simp only [M, Mint, dy]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [two_mul, pow_add]; field_simp
  · simp

theorem prodB_eq (bs : ℕ) (P Q : ℕ × ℕ) (h : 0 ≤ ((P.1 : ℤ) - P.2) * ((Q.1 : ℤ) - Q.2) + bs) :
    prodB bs P Q = (((P.1 : ℤ) - P.2) * ((Q.1 : ℤ) - Q.2) + bs).toNat := by
  have hle : P.1 * Q.2 + P.2 * Q.1 ≤ P.1 * Q.1 + P.2 * Q.2 + bs := by
    have : ((P.1 * Q.2 + P.2 * Q.1 : ℕ) : ℤ) ≤ ((P.1 * Q.1 + P.2 * Q.2 + bs : ℕ) : ℤ) := by
      push_cast; nlinarith
    exact_mod_cast this
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h, prodB, Nat.cast_sub hle]
  push_cast; ring

theorem kOK_sound {cf : Cfg} {Gs : List V3} {kp : KPair} {H : List (List (List ℤ))}
    (hk : kOK cf Gs kp H = true) :
    H.length = kp.cv.length ∧ kp.Ev.length = kp.cv.length ∧ kp.Ec.length = kp.cc.length ∧
      ∀ v < kp.cv.length, (H.getD v []).length = kp.cc.length ∧ ∀ c < kp.cc.length,
        ((H.getD v []).getD c []).length = Gs.length ∧ ∀ j < Gs.length,
          ((H.getD v []).getD c []).getD j 0 = Mint kp v c (Gs.getD j 0) := by
  simp only [kOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hW, hL⟩, hH⟩, hbv⟩, hbc⟩, hbG⟩, hlv⟩, hlc⟩, hEv⟩, hEc⟩, hall⟩ := hk
  obtain ⟨hPl, hP⟩ := all2_spec _ ((0, 0), 0) [] _ _ hall
  rw [mapL_length] at hPl
  refine ⟨hPl.symm, hEv, hEc, fun v hv => ?_⟩
  have hPv := hP v (by rw [mapL_length]; exact hv)
  rw [mapL_getD _ _ _ [] hv] at hPv
  obtain ⟨hQl, hQ⟩ := all2_spec _ ((0, 0), 0) [] _ _ hPv
  rw [mapL_length] at hQl
  refine ⟨hQl.symm, fun c hc => ?_⟩
  have hQc := hQ c (by rw [mapL_length]; exact hc)
  rw [mapL_getD _ _ _ [] hc] at hQc
  simp only [Bool.and_eq_true, Nat.blt_eq] at hQc
  obtain ⟨hl1, hdig⟩ := hQc
  obtain ⟨hsl, hs⟩ := all2_spec _ 0 0 _ _ hdig
  rw [mapL_length] at hsl
  refine ⟨hsl.symm, fun j hj => ?_⟩
  have hsj := zeq_spec (hs j (by rw [mapL_length]; exact hj))
  rw [mapL_getD _ _ _ 0 hj] at hsj
  -- the data of this pair
  set cv := kp.cv.getD v [] with hcv
  set cc := kp.cc.getD c [] with hcc
  have hcvl : cv.length = kp.Gv.length := by
    have := all_getD hlv [] hv; simpa [beq_iff_eq] using this
  have hccl : cc.length = kp.Gc.length := by
    have := all_getD hlc [] hc; simpa [beq_iff_eq] using this
  have hbox : ∀ {i l}, i < kp.Gv.length → l < kp.Gc.length →
      (cf.ev (kp.Gv.getD i 0) + cf.fc (kp.Gc.getD l 0) = cf.so (Gs.getD j 0) ↔
        kp.Gv.getD i 0 - kp.Gc.getD l 0 = Gs.getD j 0) ∧
      cf.ev (kp.Gv.getD i 0) + cf.fc (kp.Gc.getD l 0) < cf.T ∧ cf.so (Gs.getD j 0) < cf.T :=
    fun hi hl => cf.slot_iff hH hL (List.all_eq_true.mp hbv _ (getD_mem 0 hi))
      (List.all_eq_true.mp hbc _ (getD_mem 0 hl)) (List.all_eq_true.mp hbG _ (getD_mem 0 hj))
  have hpv : ∀ i < cv.length, (mapL cf.ev kp.Gv).getD i 0 = cf.ev (kp.Gv.getD i 0) :=
    fun i hi => mapL_getD _ _ _ 0 (hcvl ▸ hi) 0
  have hpc : ∀ l < cc.length, (mapL cf.fc kp.Gc).getD l 0 = cf.fc (kp.Gc.getD l 0) :=
    fun l hl => mapL_getD _ _ _ 0 (hccl ▸ hl) 0
  have hprod := kron_prod cf.W cf.T (mapL cf.ev kp.Gv) (mapL cf.fc kp.Gc) cv cc
    (by rw [mapL_length, hcvl]) (by rw [mapL_length, hccl])
    (fun i hi l hl => by
      rw [hpv i hi, hpc l hl]; exact (hbox (hcvl ▸ hi) (hccl ▸ hl)).2.1)
  have hW1 : 0 < cf.W := hW
  obtain ⟨hnn, hd⟩ := digit_int cf.W cf.T hW1 _ (fun s _ => by
      have hb := kron_bound (fun i l => (mapL cf.ev kp.Gv).getD i 0 + (mapL cf.fc kp.Gc).getD l 0 = s)
        cv cc
      have : ((l1 cv * l1 cc : ℕ) : ℤ) < ((2 ^ (cf.W - 1) : ℕ) : ℤ) := by exact_mod_cast hl1
      push_cast at this
      exact lt_of_le_of_lt hb this) _ hprod
  have hNb := prodB_eq (bias cf.W cf.T) (packPos cf.W (mapL cf.ev kp.Gv) cv,
    packNeg cf.W (mapL cf.ev kp.Gv) cv) (packPos cf.W (mapL cf.fc kp.Gc) cc,
    packNeg cf.W (mapL cf.fc kp.Gc) cc) hnn
  have hlt : cf.so (Gs.getD j 0) < cf.T := cf.so_lt hL (List.all_eq_true.mp hbG _ (getD_mem 0 hj))
  have hdj := hd _ hlt
  rw [← hNb] at hdj
  rw [hdj] at hsj
  push_cast at hsj
  have hx := add_right_cancel hsj
  rw [← hx, Mint, ← hcvl, ← hccl]
  refine sum_congr rfl fun i hi => sum_congr rfl fun l hl => ?_
  rw [hpv i (mem_range.mp hi), hpc l (mem_range.mp hl)]
  have := (hbox (hcvl ▸ mem_range.mp hi) (hccl ▸ mem_range.mp hl)).1
  simp only [this, hcv, hcc]

/-! ### The chi rows -/

theorem packIdx2_cons (W : ℕ) (a : ℤ) (l : List ℤ) :
    packIdx2 W (a :: l) = (ipos a + ((packIdx2 W l).1 <<< W), ineg a + ((packIdx2 W l).2 <<< W)) :=
  rfl

theorem packIdx2_eq (W : ℕ) : ∀ l : List ℤ,
    ((packIdx2 W l).1 : ℤ) - (packIdx2 W l).2 = ∑ j ∈ range l.length, l.getD j 0 * ((2 : ℤ) ^ W) ^ j
  | [] => by simp [packIdx2]
  | a :: l => by
    have ih := packIdx2_eq W l
    rw [packIdx2_cons, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.shiftLeft_eq]
    push_cast
    have : ∑ j ∈ range l.length, l.getD j 0 * ((2 : ℤ) ^ W) ^ (j + 1) =
        (2 : ℤ) ^ W * ∑ j ∈ range l.length, l.getD j 0 * ((2 : ℤ) ^ W) ^ j := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
    rw [this, ← ih]
    have := ipos_sub_ineg a
    linear_combination this

/-- The signed value of row accumulator `i`. -/
def val (acc : List (ℕ × ℕ)) (i : ℕ) : ℤ := ((acc.getD i (0, 0)).1 : ℤ) - (acc.getD i (0, 0)).2

theorem addPair_spec (D : ℕ) (V : ℕ × ℕ) (acc : List (ℕ × ℕ)) (m : List ℤ)
    (h : acc.length ≤ m.length) :
    (addPair D V acc m).length = acc.length ∧ ∀ i < acc.length,
      val (addPair D V acc m) i = val acc i + D * m.getD i 0 * ((V.1 : ℤ) - V.2) := by
  refine ⟨by rw [addPair, zipW_length, min_eq_left h], fun i hi => ?_⟩
  simp only [val, addPair]
  rw [zipW_getD _ (0, 0) (0, 0) 0 acc m i hi (lt_of_lt_of_le hi h)]
  generalize m.getD i 0 = x
  cases x with
  | ofNat k => simp only [Int.ofNat_eq_coe]; push_cast; ring
  | negSucc k => simp only [Int.negSucc_eq]; push_cast; ring

theorem pairsOK_spec {Mmax n : ℕ} {ks : List KPair} {H : List (List (List (List ℤ)))}
    (hp : pairsOK Mmax n ks H = true) :
    ks.length = H.length ∧ ∀ t < ks.length,
      (ks.getD t default).Ev.length = (H.getD t []).length ∧ ∀ v < (ks.getD t default).Ev.length,
        (ks.getD t default).Ec.length = ((H.getD t []).getD v []).length ∧
        ∀ c < (ks.getD t default).Ec.length,
          (ks.getD t default).Ev.getD v 0 < (ks.getD t default).Ec.getD c 0 ∧
          (((H.getD t []).getD v []).getD c []).length = n ∧
          ∀ j < n, |(((H.getD t []).getD v []).getD c []).getD j 0| ≤ Mmax := by
  obtain ⟨h1, h2⟩ := all2_spec _ default [] _ _ hp
  refine ⟨h1, fun t ht => ?_⟩
  obtain ⟨h3, h4⟩ := all2_spec _ 0 [] _ _ (h2 t ht)
  refine ⟨h3, fun v hv => ?_⟩
  obtain ⟨h5, h6⟩ := all2_spec _ 0 [] _ _ (h4 v hv)
  refine ⟨h5, fun c hc => ?_⟩
  have h7 := h6 c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h7
  obtain ⟨⟨h8, h9⟩, h10⟩ := h7
  refine ⟨h8, h9, fun j hj => ?_⟩
  have := all_getD h10 0 (h9 ▸ hj)
  simp only [Nat.ble_eq] at this
  rw [ipos_add_ineg] at this
  have h' : ((((H.getD t []).getD v []).getD c []).getD j 0).natAbs ≤ Mmax := this
  rw [← Int.natCast_natAbs]; exact_mod_cast h'

/-- The value of the pair `(t, v, c)` in the row sums: `D_tvc m_tvc(i) V_tvc`. -/
noncomputable def pairTerm (W2 SDE : ℕ) (ks : List KPair) (H : List (List (List (List ℤ))))
    (i t v c : ℕ) : ℤ :=
  dval SDE ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0) *
    (((H.getD t []).getD v []).getD c []).getD i 0 *
    (((packIdx2 W2 (((H.getD t []).getD v []).getD c [])).1 : ℤ) -
      (packIdx2 W2 (((H.getD t []).getD v []).getD c [])).2)

theorem accRows_spec {Mmax W2 SDE n : ℕ} {ks : List KPair} {H : List (List (List (List ℤ)))}
    (hp : pairsOK Mmax n ks H = true) (r0 L : ℕ) (hrL : r0 + L ≤ n) (acc0 : List (ℕ × ℕ))
    (h0 : acc0.length = L) (k : ℕ) (hk : k < L) :
    (accRows W2 SDE r0 ks H acc0).length = L ∧ val (accRows W2 SDE r0 ks H acc0) k = val acc0 k +
      ∑ t ∈ range ks.length, ∑ v ∈ range (ks.getD t default).Ev.length,
        ∑ c ∈ range (ks.getD t default).Ec.length, pairTerm W2 SDE ks H (r0 + k) t v c := by
  obtain ⟨hl, hks⟩ := pairsOK_spec hp
  refine fold2_sum _ (fun acc => acc.length = L) (fun acc => val acc k) default [] ks H _ acc0 hl
    (fun t ht y hy => ?_) h0
  obtain ⟨hEv, hv⟩ := hks t ht
  refine fold2_sum _ (fun acc => acc.length = L) (fun acc => val acc k) 0 [] _ _ _ y hEv
    (fun v hvl y hy => ?_) hy
  obtain ⟨hEc, hc⟩ := hv v hvl
  refine fold2_sum _ (fun acc => acc.length = L) (fun acc => val acc k) 0 [] _ _ _ y hEc
    (fun c hcl y hy => ?_) hy
  obtain ⟨_, hm, _⟩ := hc c hcl
  obtain ⟨h1, h2⟩ := addPair_spec (dval SDE ((ks.getD t default).Ev.getD v 0)
    ((ks.getD t default).Ec.getD c 0)) (packIdx2 W2 (((H.getD t []).getD v []).getD c [])) y
    ((((H.getD t []).getD v []).getD c []).drop r0) (by rw [hy, List.length_drop, hm]; omega)
  refine ⟨h1.trans hy, ?_⟩
  beta_reduce
  rw [h2 k (hy ▸ hk)]
  simp only [pairTerm, getD_drop']

theorem sum3_spec {Mmax n : ℕ} {ks : List KPair} {H : List (List (List (List ℤ)))}
    (hp : pairsOK Mmax n ks H = true) (g : ℤ → ℤ → List ℤ → ℕ) :
    (sum3 g ks H : ℤ) = ∑ t ∈ range ks.length, ∑ v ∈ range (ks.getD t default).Ev.length,
        ∑ c ∈ range (ks.getD t default).Ec.length,
          (g ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0)
            (((H.getD t []).getD v []).getD c []) : ℤ) := by
  obtain ⟨hl, hks⟩ := pairsOK_spec hp
  have key := fold2_sum (fun kp Ht s => fold2 (fun ev Hv s => fold2 (fun ec m s => s + g ev ec m)
      kp.Ec Hv s) kp.Ev Ht s) (fun _ => True) (fun s : ℕ => (s : ℤ)) default [] ks H
    (fun t => ∑ v ∈ range (ks.getD t default).Ev.length,
        ∑ c ∈ range (ks.getD t default).Ec.length,
          (g ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0)
            (((H.getD t []).getD v []).getD c []) : ℤ)) 0 hl (fun t ht y _ => ?_) trivial
  · simpa [sum3] using key.2
  obtain ⟨hEv, hv⟩ := hks t ht
  refine ⟨trivial, ?_⟩
  have key2 := fold2_sum (fun ev Hv s => fold2 (fun ec m s => s + g ev ec m)
      (ks.getD t default).Ec Hv s) (fun _ => True) (fun s : ℕ => (s : ℤ)) 0 []
    (ks.getD t default).Ev (H.getD t [])
    (fun v => ∑ c ∈ range (ks.getD t default).Ec.length,
          (g ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0)
            (((H.getD t []).getD v []).getD c []) : ℤ)) y hEv (fun v hvl y _ => ?_) trivial
  · exact key2.2
  obtain ⟨hEc, _⟩ := hv v hvl
  refine ⟨trivial, ?_⟩
  exact (fold2_sum (fun ec m s => s + g ((ks.getD t default).Ev.getD v 0) ec m) (fun _ => True)
    (fun s : ℕ => (s : ℤ)) 0 [] (ks.getD t default).Ec ((H.getD t []).getD v [])
    (fun c => (g ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0)
            (((H.getD t []).getD v []).getD c []) : ℤ)) y hEc
    (fun c _ y _ => ⟨trivial, by push_cast; rfl⟩) trivial).2

/-- The exact row sums `X_ij = Σ_{k,v,c} D m(G_i) m(G_j)` (checker ranges). -/
noncomputable def Xs (SDE : ℕ) (ks : List KPair) (H : List (List (List (List ℤ)))) (i j : ℕ) : ℤ :=
  ∑ t ∈ range ks.length, ∑ v ∈ range (ks.getD t default).Ev.length,
    ∑ c ∈ range (ks.getD t default).Ec.length,
      dval SDE ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0) *
        (((H.getD t []).getD v []).getD c []).getD i 0 * (((H.getD t []).getD v []).getD c []).getD j 0

theorem row_digits {Mmax W2 SDE n : ℕ} {ks : List KPair} {H : List (List (List (List ℤ)))}
    (hp : pairsOK Mmax n ks H = true)
    (hb : sum3 (fun ev ec _ => dval SDE ev ec) ks H * (Mmax * Mmax) < 2 ^ (W2 - 1))
    (hW2 : 0 < W2) (r0 L : ℕ) (hrL : r0 + L ≤ n) (k : ℕ) (hk : k < L) (j : ℕ) (hj : j < n) :
    ((((((accRows W2 SDE r0 ks H (List.replicate L (0, 0))).getD k (0, 0)).1 + bias W2 n -
      ((accRows W2 SDE r0 ks H (List.replicate L (0, 0))).getD k (0, 0)).2) >>> (W2 * j)) %
        2 ^ W2 : ℕ) : ℤ) = Xs SDE ks H (r0 + k) j + 2 ^ (W2 - 1) := by
  obtain ⟨hl, hks⟩ := pairsOK_spec hp
  set acc := accRows W2 SDE r0 ks H (List.replicate L (0, 0))
  obtain ⟨_, hv⟩ := accRows_spec (W2 := W2) (SDE := SDE) hp r0 L hrL (List.replicate L (0, 0))
    (by simp) k hk
  have hv0 : val (List.replicate L ((0 : ℕ), (0 : ℕ))) k = 0 := by
    simp [val, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk]
  rw [hv0, zero_add] at hv
  -- the row value as a packed sum over the columns
  have hrow : val acc k = ∑ j' ∈ range n, Xs SDE ks H (r0 + k) j' * ((2 : ℤ) ^ W2) ^ j' := by
    rw [hv]
    have e1 : ∀ t ∈ range ks.length, ∀ v ∈ range (ks.getD t default).Ev.length,
        ∀ c ∈ range (ks.getD t default).Ec.length, pairTerm W2 SDE ks H (r0 + k) t v c =
          ∑ j' ∈ range n, dval SDE ((ks.getD t default).Ev.getD v 0) ((ks.getD t default).Ec.getD c 0) *
            (((H.getD t []).getD v []).getD c []).getD (r0 + k) 0 *
            (((H.getD t []).getD v []).getD c []).getD j' 0 * ((2 : ℤ) ^ W2) ^ j' := by
      intro t ht v hvv c hc
      obtain ⟨_, hvs⟩ := hks t (mem_range.mp ht)
      obtain ⟨_, hcs⟩ := hvs v (mem_range.mp hvv)
      obtain ⟨_, hm, _⟩ := hcs c (mem_range.mp hc)
      rw [pairTerm, packIdx2_eq, hm, mul_sum]
      refine sum_congr rfl fun j' _ => by ring
    rw [sum_congr rfl fun t ht => sum_congr rfl fun v hvv => sum_congr rfl fun c hc =>
      e1 t ht v hvv c hc]
    simp only [Xs, sum_mul]
    symm
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_comm]
  have hX : ∀ j' < n, |Xs SDE ks H (r0 + k) j'| < 2 ^ (W2 - 1) := by
    intro j' _
    have hsum := sum3_spec hp (fun ev ec _ => dval SDE ev ec)
    have hb' : ((sum3 (fun ev ec _ => dval SDE ev ec) ks H : ℕ) : ℤ) * (Mmax * Mmax) < 2 ^ (W2 - 1) := by
      exact_mod_cast hb
    refine lt_of_le_of_lt ?_ hb'
    rw [hsum, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v hvv => ?_)
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c hc => ?_)
    obtain ⟨_, hvs⟩ := hks t (mem_range.mp ht)
    obtain ⟨_, hcs⟩ := hvs v (mem_range.mp hvv)
    obtain ⟨_, _, hM⟩ := hcs c (mem_range.mp hc)
    have h1 := hM (r0 + k) (by omega)
    have h2 := hM j' (by omega)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (dval _ _ _ : ℕ)), mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (by positivity)
  obtain ⟨hnn, hd⟩ := digit_int W2 n hW2 _ hX _ hrow
  have hle : (acc.getD k (0, 0)).2 ≤ (acc.getD k (0, 0)).1 + bias W2 n := by
    have : ((acc.getD k (0, 0)).2 : ℤ) ≤ ((acc.getD k (0, 0)).1 : ℤ) + (bias W2 n : ℕ) := by
      simp only [val] at hnn; linarith
    exact_mod_cast this
  have hcast : (acc.getD k (0, 0)).1 + bias W2 n - (acc.getD k (0, 0)).2 = (val acc k + bias W2 n).toNat := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn, Nat.cast_sub hle, val]; push_cast; ring
  rw [hcast]
  exact hd j hj

/-! ### Real-number bounds -/

/-- `D = ⌊2^(SD+SEn) / (e_c - e_v)⌋` brackets `2^SD / (E_c - E_v)`. -/
theorem dval_bounds (SD SEn : ℕ) {ev ec : ℤ} (h : ev < ec) :
    (dval (SD + SEn) ev ec : ℝ) ≤ 2 ^ SD * (1 / (dy SEn ec - dy SEn ev)) ∧
      2 ^ SD * (1 / (dy SEn ec - dy SEn ev)) < dval (SD + SEn) ev ec + 1 := by
  set δ := (ec - ev).toNat with hδ
  have hδz : (δ : ℤ) = ec - ev := Int.toNat_of_nonneg (by omega)
  have hδ0 : 0 < δ := by omega
  have hδr : (δ : ℝ) = (ec : ℝ) - ev := by exact_mod_cast hδz
  have e : 2 ^ SD * (1 / (dy SEn ec - dy SEn ev)) = (2 ^ (SD + SEn) : ℝ) / δ := by
    rw [hδr, dy, dy, pow_add]; field_simp
  rw [e]
  have hpos : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have h1 : ((2 ^ (SD + SEn) / δ * δ : ℕ) : ℝ) ≤ ((2 ^ (SD + SEn) : ℕ) : ℝ) :=
    by exact_mod_cast Nat.div_mul_le_self (2 ^ (SD + SEn)) δ
  have h2 : ((2 ^ (SD + SEn) : ℕ) : ℝ) < ((δ * (2 ^ (SD + SEn) / δ + 1) : ℕ) : ℝ) :=
    by exact_mod_cast Nat.lt_mul_div_succ (2 ^ (SD + SEn)) hδ0
  push_cast at h1 h2
  have hd : (dval (SD + SEn) ev ec : ℝ) = ((2 ^ (SD + SEn) / δ : ℕ) : ℝ) := rfl
  rw [hd]
  constructor
  · rw [le_div_iff₀ hpos]; exact h1
  · rw [div_lt_iff₀ hpos]; linarith

theorem qG2_eq (inp : Input) (G : V3) : qG2 inp G = (n2 inp G : ℝ) / 2 ^ (2 * inp.SQ + inp.SB) := by
  simp only [qG2, n2, Fin.sum_univ_three, dy, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, List.getD_cons_zero, List.getD_cons_succ,
    Fin.val_zero, Fin.val_one, Fin.val_two, Int.ofNat_eq_coe]
  push_cast
  rw [show (2 : ℝ) ^ (2 * inp.SQ + inp.SB) = ((2 : ℝ) ^ inp.SQ) ^ 2 * 2 ^ inp.SB by
    rw [pow_add, ← pow_mul, mul_comm inp.SQ 2]]
  have ha : (0 : ℝ) < 2 ^ inp.SQ := by positivity
  have hb : (0 : ℝ) < 2 ^ inp.SB := by positivity
  generalize (2 : ℝ) ^ inp.SQ = a at ha ⊢
  generalize (2 : ℝ) ^ inp.SB = b at hb ⊢
  field_simp
  ring

/-- `u = v(q + G) · 4/(N_k Ω)` and its bracket by `ulo, uhi` at scale `2^-SU`. -/
theorem u_bounds (inp : Input) (SU : ℕ) (G : V3) (hN : 0 < n2 inp G) (hOm : 0 < inp.Om) :
    0 ≤ vC inp G * (4 / (inp.ks.length * dy inp.SOm inp.Om)) ∧
    (((32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + SU)) * piLo /
        (10 ^ 20 * inp.ks.length * inp.Om * (n2 inp G).toNat) : ℕ) : ℝ) ≤
      2 ^ SU * (vC inp G * (4 / (inp.ks.length * dy inp.SOm inp.Om))) ∧
    2 ^ SU * (vC inp G * (4 / (inp.ks.length * dy inp.SOm inp.Om))) ≤
      (((32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + SU)) * piHi /
        (10 ^ 20 * inp.ks.length * inp.Om * (n2 inp G).toNat) + 1 : ℕ) : ℝ) := by
  generalize hnum : 32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + SU) = num
  generalize hNd : (n2 inp G).toNat = N
  generalize hden : 10 ^ 20 * inp.ks.length * inp.Om * N = den
  have hNz : (N : ℤ) = n2 inp G := by rw [← hNd]; exact Int.toNat_of_nonneg hN.le
  have hNr : (N : ℝ) = (n2 inp G : ℝ) := by exact_mod_cast hNz
  have hN0 : (0 : ℝ) < N := by rw [hNr]; exact_mod_cast hN
  have hOm0 : (0 : ℝ) < inp.Om := by exact_mod_cast hOm
  have hpi := Real.pi_pos
  have hnumr : (num : ℝ) = 32 * (2 ^ inp.SOm * ((2 : ℝ) ^ inp.SQ) ^ 2 * 2 ^ inp.SB) * 2 ^ SU := by
    rw [← hnum]; push_cast; rw [pow_add, pow_add, pow_add, ← pow_mul, mul_comm inp.SQ 2]; ring
  have hdenr : (den : ℝ) = 10 ^ 20 * inp.ks.length * inp.Om * N := by rw [← hden]; push_cast; ring
  rcases Nat.eq_zero_or_pos inp.ks.length with h0 | h0
  · have hd0 : den = 0 := by rw [← hden, h0]; simp
    have hz : vC inp G * (4 / (inp.ks.length * dy inp.SOm inp.Om)) = 0 := by rw [h0]; simp
    rw [hz, hd0]; simp
  have hk : (0 : ℝ) < inp.ks.length := by exact_mod_cast h0
  have hden0 : (0 : ℝ) < den := by rw [hdenr]; positivity
  have hdenN : 0 < den := by exact_mod_cast hden0
  -- the exact value
  have e : 2 ^ SU * (vC inp G * (4 / (inp.ks.length * dy inp.SOm inp.Om))) =
      num * (Real.pi * 10 ^ 20) / den := by
    rw [vC, qG2_eq, ← hNr, dy, hnumr, hdenr,
      show (2 : ℝ) ^ (2 * inp.SQ + inp.SB) = ((2 : ℝ) ^ inp.SQ) ^ 2 * 2 ^ inp.SB by
        rw [pow_add, ← pow_mul, mul_comm inp.SQ 2]]
    have ha : (0 : ℝ) < 2 ^ inp.SQ := by positivity
    have hb : (0 : ℝ) < 2 ^ inp.SB := by positivity
    have hc : (0 : ℝ) < 2 ^ inp.SOm := by positivity
    generalize (2 : ℝ) ^ inp.SQ = a at ha ⊢
    generalize (2 : ℝ) ^ inp.SB = b at hb ⊢
    generalize (2 : ℝ) ^ inp.SOm = c at hc ⊢
    field_simp; ring
  have hpl : (piLo : ℝ) < Real.pi * 10 ^ 20 := by
    have := Real.pi_gt_d20; simp only [piLo]; norm_num at this ⊢; linarith
  have hph : Real.pi * 10 ^ 20 < (piHi : ℝ) := by
    have := Real.pi_lt_d20; simp only [piHi]; norm_num at this ⊢; linarith
  have hnum0 : (0 : ℝ) ≤ num := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hU : (0 : ℝ) < 2 ^ SU := by positivity
    have hX : 0 ≤ (num : ℝ) * (Real.pi * 10 ^ 20) / den := by positivity
    rw [← e] at hX
    exact (mul_nonneg_iff_of_pos_left hU).mp hX
  · rw [e, le_div_iff₀ hden0]
    have h1 : ((num * piLo / den * den : ℕ) : ℝ) ≤ ((num * piLo : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self _ _
    push_cast at h1
    nlinarith [mul_le_mul_of_nonneg_left hpl.le hnum0]
  · rw [e, div_le_iff₀ hden0]
    have h2 : ((num * piHi : ℕ) : ℝ) < ((den * (num * piHi / den + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_mul_div_succ _ hdenN
    push_cast at h2 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hph.le hnum0]

/-- `Σ_{k,v,c} M_vc(G) M_vc(G') / (E_c - E_v)` (so `chi = -4/(N_k Ω) · Yr`). -/
noncomputable def Yr (inp : Input) (G G' : V3) : ℝ :=
  ∑ t ∈ range inp.ks.length, ∑ v ∈ range (inp.ks.getD t default).cv.length,
    ∑ c ∈ range (inp.ks.getD t default).cc.length,
      1 / (dy inp.SEn ((inp.ks.getD t default).Ec.getD c 0) - dy inp.SEn ((inp.ks.getD t default).Ev.getD v 0)) *
        M inp (inp.ks.getD t default) v c G * M inp (inp.ks.getD t default) v c G'

theorem epsR_eq (inp : Input) (i j : ℕ) :
    epsR inp i j = (if i = j then 1 else 0) +
      vC inp (inp.Gs.getD i 0) * (4 / (inp.ks.length * dy inp.SOm inp.Om)) *
        Yr inp (inp.Gs.getD i 0) (inp.Gs.getD j 0) := by
  have h : chi inp (inp.Gs.getD i 0) (inp.Gs.getD j 0) =
      -(4 / (inp.ks.length * dy inp.SOm inp.Om) * Yr inp (inp.Gs.getD i 0) (inp.Gs.getD j 0)) := by
    rw [chi, Yr, ← mul_neg]
    congr 1
    simp only [← sum_neg_distrib]
    refine sum_congr rfl fun t _ => sum_congr rfl fun v _ => sum_congr rfl fun c _ => ?_
    rw [div_eq_mul_one_div, show dy inp.SEn ((inp.ks.getD t default).Ev.getD v 0) -
      dy inp.SEn ((inp.ks.getD t default).Ec.getD c 0) = -(dy inp.SEn ((inp.ks.getD t default).Ec.getD c 0) -
      dy inp.SEn ((inp.ks.getD t default).Ev.getD v 0)) by ring, one_div_neg_eq_neg_one_div]
    ring
  rw [epsR, h]; ring

theorem Y_bound {cf : Cfg} {inp : Input} {H : List (List (List (List ℤ)))} {Mmax : ℕ}
    (hk : ∀ t < inp.ks.length, kOK cf inp.Gs (inp.ks.getD t default) (H.getD t []) = true)
    (hp : pairsOK Mmax inp.Gs.length inp.ks H = true) (SD : ℕ) {i j : ℕ} (hi : i < inp.Gs.length)
    (hj : j < inp.Gs.length) :
    |Yr inp (inp.Gs.getD i 0) (inp.Gs.getD j 0) * 2 ^ (SD + 4 * inp.SC) -
        Xs (SD + inp.SEn) inp.ks H i j| ≤ (sum3 (fun _ _ _ => 1) inp.ks H : ℝ) * (Mmax * Mmax) := by
  obtain ⟨hl, hks⟩ := pairsOK_spec hp
  have hcnt : (sum3 (fun _ _ _ => 1) inp.ks H : ℝ) = ∑ t ∈ range inp.ks.length,
      ∑ v ∈ range (inp.ks.getD t default).Ev.length, ∑ c ∈ range (inp.ks.getD t default).Ec.length,
        (1 : ℝ) := by
    have := sum3_spec hp (fun _ _ _ => 1); push_cast at this; exact_mod_cast this
  rw [hcnt, Yr, Xs, sum_mul]
  push_cast
  rw [← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  obtain ⟨hH, hEv, hEc, hK⟩ := kOK_sound (hk t (mem_range.mp ht))
  obtain ⟨_, hvs⟩ := hks t (mem_range.mp ht)
  rw [← hEv, sum_mul, sum_mul, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v hv => ?_)
  obtain ⟨_, hK2⟩ := hK v (hEv ▸ mem_range.mp hv)
  obtain ⟨_, hcs⟩ := hvs v (mem_range.mp hv)
  try rw [← hEc]
  try rw [sum_mul, sum_mul, ← sum_sub_distrib]
  try rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c hc => ?_)
  obtain ⟨_, hK3⟩ := hK2 c (hEc ▸ mem_range.mp hc)
  obtain ⟨hlt, _, hM⟩ := hcs c (mem_range.mp hc)
  obtain ⟨hD1, hD2⟩ := dval_bounds SD inp.SEn hlt
  rw [hK3 i hi, hK3 j hj, M_eq, M_eq]
  have hmi := hM i hi
  have hmj := hM j hj
  rw [hK3 i hi] at hmi
  rw [hK3 j hj] at hmj
  set a := (Mint (inp.ks.getD t default) v c (inp.Gs.getD i 0) : ℝ)
  set b := (Mint (inp.ks.getD t default) v c (inp.Gs.getD j 0) : ℝ)
  set ρ := 1 / (dy inp.SEn ((inp.ks.getD t default).Ec.getD c 0) - dy inp.SEn ((inp.ks.getD t default).Ev.getD v 0))
  set D := (dval (SD + inp.SEn) ((inp.ks.getD t default).Ev.getD v 0) ((inp.ks.getD t default).Ec.getD c 0) : ℝ)
  have ha : |a| ≤ Mmax := by simp only [a]; exact_mod_cast hmi
  have hb : |b| ≤ Mmax := by simp only [b]; exact_mod_cast hmj
  have e : ρ * (a / 2 ^ (2 * inp.SC)) * (b / 2 ^ (2 * inp.SC)) * 2 ^ (SD + 4 * inp.SC) - D * a * b =
      (2 ^ SD * ρ - D) * (a * b) := by
    rw [pow_add, show 4 * inp.SC = 2 * inp.SC + 2 * inp.SC by ring, pow_add]; field_simp; ring
  rw [e, abs_mul, one_mul]
  have h01 : |2 ^ SD * ρ - D| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hab : |a * b| ≤ Mmax * Mmax := by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
  calc |2 ^ SD * ρ - D| * |a * b| ≤ 1 * (Mmax * Mmax) := mul_le_mul h01 hab (abs_nonneg _) zero_le_one
    _ = Mmax * Mmax := one_mul _

/-- The final interval step: from the four integer tests to `lo ≤ δ + u Y ≤ hi`. Here
`U = 2^SU u ∈ [ulo, uhi]`, `y = 2^SY Y ∈ [X - E, X + E]`, `kP = 2^(SU+SY)`, `s = 2^SE`. -/
theorem combine {lo hi δ U y X E ulo uhi s kP : ℝ} (hs : 0 < s) (hk : 0 < kP) (hU1 : ulo ≤ U)
    (hU2 : U ≤ uhi) (hulo : 0 ≤ ulo) (hy1 : X - E ≤ y) (hy2 : y ≤ X + E)
    (h1 : lo * kP ≤ δ * s * kP + ulo * (X - E) * s) (h2 : lo * kP ≤ δ * s * kP + uhi * (X - E) * s)
    (h3 : δ * s * kP + ulo * (X + E) * s ≤ hi * kP) (h4 : δ * s * kP + uhi * (X + E) * s ≤ hi * kP) :
    lo / s ≤ δ + U * y / kP ∧ δ + U * y / kP ≤ hi / s := by
  have hU0 : 0 ≤ U := hulo.trans hU1
  have hlow : lo * kP ≤ δ * s * kP + U * y * s := by
    have : min (ulo * (X - E)) (uhi * (X - E)) ≤ U * y := by
      rcases le_total 0 (X - E) with hx | hx
      · exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_right hU1 hx).trans
          (mul_le_mul_of_nonneg_left hy1 hU0))
      · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hU2 hx).trans
          (mul_le_mul_of_nonneg_left hy1 hU0))
    rcases min_choice (ulo * (X - E)) (uhi * (X - E)) with hm | hm <;> rw [hm] at this <;> nlinarith
  have hupp : δ * s * kP + U * y * s ≤ hi * kP := by
    have : U * y ≤ max (ulo * (X + E)) (uhi * (X + E)) := by
      rcases le_total 0 (X + E) with hx | hx
      · exact ((mul_le_mul_of_nonneg_left hy2 hU0).trans (mul_le_mul_of_nonneg_right hU2 hx)).trans
          (le_max_right _ _)
      · exact ((mul_le_mul_of_nonneg_left hy2 hU0).trans (mul_le_mul_of_nonpos_right hU1 hx)).trans
          (le_max_left _ _)
    rcases max_choice (ulo * (X + E)) (uhi * (X + E)) with hm | hm <;> rw [hm] at this <;> nlinarith
  constructor
  · rw [div_le_iff₀ hs]
    have : (δ + U * y / kP) * s * kP = δ * s * kP + U * y * s := by field_simp; ring
    nlinarith
  · rw [le_div_iff₀ hs]
    have : (δ + U * y / kP) * s * kP = δ * s * kP + U * y * s := by field_simp; ring
    nlinarith

theorem getD_range {n j : ℕ} (h : j < n) : (List.range n).getD j 0 = j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range h, Option.getD_some]

/-! ### Soundness -/

/-- **Soundness of one block of rows.** If every k-point's pair-density check `kOK`, the
global check and the check of rows `r0 … r0 + L - 1` pass, then for those rows every
entry of the real dielectric matrix `epsR` lies in the box `[epsLo, epsHi] / 2^SE`. -/
theorem sound_rows {cf : Cfg} {inp : Input} {H : List (List (List (List ℤ)))} {SE : ℕ}
    {epsLo epsHi : List (List ℤ)} {r0 L : ℕ}
    (hk : ∀ t < inp.ks.length, kOK cf inp.Gs (inp.ks.getD t default) (H.getD t []) = true)
    (hg : chiGlobal cf inp H = true) (hr : chiRows cf inp H SE epsLo epsHi r0 L = true) :
    ∀ k < L, ∀ j < inp.Gs.length,
      ((ent epsLo (r0 + k) j : ℤ) : ℝ) / 2 ^ SE ≤ epsR inp (r0 + k) j ∧
        epsR inp (r0 + k) j ≤ ((ent epsHi (r0 + k) j : ℤ) : ℝ) / 2 ^ SE := by
  intro k hkL j hj
  simp only [chiGlobal, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hg
  obtain ⟨⟨⟨hp, hb⟩, hW2⟩, hOm⟩ := hg
  simp only [chiRows, Bool.and_eq_true, Nat.ble_eq] at hr
  obtain ⟨hrL, hall⟩ := hr
  set n := inp.Gs.length with hn
  set SDE := cf.SD + inp.SEn
  set acc := accRows cf.W2 SDE r0 inp.ks H (List.replicate L (0, 0)) with hacc
  obtain ⟨haccl, _⟩ := accRows_spec (W2 := cf.W2) (SDE := SDE) hp r0 L hrL (List.replicate L (0, 0))
    (by simp) k hkL
  obtain ⟨hlen, hrows⟩ := all2_spec _ ((0 : ℕ), (0 : V3)) (((0 : ℕ), (0 : ℕ)), ([] : List ℤ), ([] : List ℤ)) _ _ hall
  have hl1 : (zipW Prod.mk (mapL (· + r0) (List.range L)) (inp.Gs.drop r0)).length = L := by
    rw [zipW_length, mapL_length, List.length_range, List.length_drop]; omega
  have hkl : k < (zipW Prod.mk (mapL (· + r0) (List.range L)) (inp.Gs.drop r0)).length := by omega
  have hrow := hrows k hkl
  rw [hl1] at hlen
  -- the row index and the row data
  have hx : (zipW Prod.mk (mapL (· + r0) (List.range L)) (inp.Gs.drop r0)).getD k (0, 0) =
      (r0 + k, inp.Gs.getD (r0 + k) 0) := by
    rw [zipW_getD _ (0, 0) 0 0 _ _ k (by rw [mapL_length, List.length_range]; exact hkL)
      (by rw [List.length_drop]; omega), mapL_getD _ _ _ 0 (by rw [List.length_range]; exact hkL),
      getD_range hkL, getD_drop']
    simp [add_comm]
  have hyl := hlen.symm
  rw [zipW_length, zipW_length, List.length_drop, List.length_drop] at hyl
  have hk1 : k < acc.length := by omega
  have hk2 : k < (epsLo.drop r0).length := by rw [List.length_drop]; omega
  have hk3 : k < (epsHi.drop r0).length := by rw [List.length_drop]; omega
  have hk4 : k < (zipW Prod.mk (epsLo.drop r0) (epsHi.drop r0)).length := by
    rw [zipW_length]; omega
  have hy : (zipW Prod.mk acc (zipW Prod.mk (epsLo.drop r0) (epsHi.drop r0))).getD k
      (((0 : ℕ), (0 : ℕ)), ([] : List ℤ), ([] : List ℤ)) =
      (acc.getD k (0, 0), epsLo.getD (r0 + k) [], epsHi.getD (r0 + k) []) := by
    rw [zipW_getD _ _ (0, 0) (([] : List ℤ), ([] : List ℤ)) _ _ k hk1 hk4,
      zipW_getD _ _ ([] : List ℤ) ([] : List ℤ) _ _ k hk2 hk3, getD_drop', getD_drop']
  rw [hx, hy] at hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨hN, hent⟩ := hrow
  obtain ⟨hlen2, hent2⟩ := all2_spec _ 0 ((0 : ℤ), (0 : ℤ)) _ _ hent
  rw [List.length_range, zipW_length] at hlen2
  have he := hent2 j (by rw [List.length_range]; exact hj)
  rw [getD_range hj, zipW_getD _ _ 0 0 _ _ j (by omega) (by omega)] at he
  simp only [entryOK, Bool.and_eq_true] at he
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := he
  have e1 := zleS_spec e1
  have e2 := zleS_spec e2
  have e3 := zgeS_spec e3
  have e4 := zgeS_spec e4
  -- the digit
  have hd := row_digits hp hb hW2 r0 L hrL k hkL j hj
  -- real quantities
  set i := r0 + k
  obtain ⟨hu0, hulo, huhi⟩ := u_bounds inp cf.SU (inp.Gs.getD i 0) hN hOm
  have hY := Y_bound hk hp cf.SD (show i < n by omega) hj
  rw [abs_le] at hY
  rw [epsR_eq]
  set u := vC inp (inp.Gs.getD i 0) * (4 / (inp.ks.length * dy inp.SOm inp.Om))
  set Y := Yr inp (inp.Gs.getD i 0) (inp.Gs.getD j 0)
  set X := Xs SDE inp.ks H i j
  have hE : (((sum3 (fun _ _ _ => 1) inp.ks H * (cf.Mmax * cf.Mmax) : ℕ) : ℝ)) =
      (sum3 (fun _ _ _ => 1) inp.ks H : ℝ) * (cf.Mmax * cf.Mmax) := by push_cast; ring
  have hP : (2 : ℝ) ^ (cf.SU + cf.SD + 4 * inp.SC) = 2 ^ cf.SU * 2 ^ (cf.SD + 4 * inp.SC) := by
    rw [add_assoc, pow_add]
  have key := combine (lo := ((ent epsLo i j : ℤ) : ℝ)) (hi := ((ent epsHi i j : ℤ) : ℝ))
    (δ := if i = j then 1 else 0) (U := 2 ^ cf.SU * u) (y := Y * 2 ^ (cf.SD + 4 * inp.SC))
    (X := (X : ℝ)) (E := ((sum3 (fun _ _ _ => 1) inp.ks H * (cf.Mmax * cf.Mmax) : ℕ) : ℝ))
    (s := 2 ^ SE) (kP := 2 ^ (cf.SU + cf.SD + 4 * inp.SC))
    (by positivity) (by positivity) hulo huhi (by positivity)
    (by rw [hE]; linarith [hY.2]) (by rw [hE]; linarith [hY.1]) ?_ ?_ ?_ ?_
  · have hrw : 2 ^ cf.SU * u * (Y * 2 ^ (cf.SD + 4 * inp.SC)) / 2 ^ (cf.SU + cf.SD + 4 * inp.SC) =
        u * Y := by rw [hP]; field_simp; ring
    rw [hrw] at key
    simpa [ent] using key
  all_goals
    have hdl : (((if r0 + k = j then 2 ^ (SE + (cf.SU + cf.SD + 4 * inp.SC)) else 0 : ℕ) : ℤ) : ℝ) =
        (if i = j then 1 else 0) * 2 ^ SE * 2 ^ (cf.SU + cf.SD + 4 * inp.SC) := by
      split_ifs <;> push_cast <;> ring
    generalize (32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + cf.SU) * piLo /
      (10 ^ 20 * inp.ks.length * inp.Om * (n2 inp (inp.Gs.getD i 0)).toNat)) = UL at e1 e3 hulo ⊢
    generalize (32 * 2 ^ (inp.SOm + 2 * inp.SQ + inp.SB + cf.SU) * piHi /
      (10 ^ 20 * inp.ks.length * inp.Om * (n2 inp (inp.Gs.getD i 0)).toNat) + 1) = UH at e2 e4 huhi ⊢
    generalize (((acc.getD k (0, 0)).1 + bias cf.W2 n - (acc.getD k (0, 0)).2) >>> (cf.W2 * j)) %
      2 ^ cf.W2 = dd at e1 e2 e3 e4 hd
    generalize (if r0 + k = j then 2 ^ (SE + (cf.SU + cf.SD + 4 * inp.SC)) else 0 : ℕ) = DL
      at e1 e2 e3 e4 hdl
    have hdR : (dd : ℝ) = (X : ℝ) + 2 ^ (cf.W2 - 1) := by exact_mod_cast hd
    have c1 := (Int.cast_le (R := ℝ)).mpr e1
    have c2 := (Int.cast_le (R := ℝ)).mpr e2
    have c3 := (Int.cast_le (R := ℝ)).mpr e3
    have c4 := (Int.cast_le (R := ℝ)).mpr e4
    push_cast at c1 c2 c3 c4 hdl ⊢
    rw [hdR, hdl] at c1 c2 c3 c4
    simp only [ent]
    linarith

end GW.Endpoint.Kernel.Eps

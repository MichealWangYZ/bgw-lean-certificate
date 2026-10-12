/-
G2 stage 3, soundness (3a/4): the Kronecker tables. A table `l` keyed by vectors
in `[-h, h]³` with distinct slots, packed as `tpackS W (tslots h b l)`, returns
under `tget` the digit `b + v` of the (unique) entry with key `g`, or `0` when `g`
is not a key (`tget_find`).
-/
import GW.Endpoint.Kernel.SigmaHot

namespace GW.Endpoint.Kernel.Sig

open Finset GW.Endpoint.Kernel GW.Endpoint.Kernel.Eps

/-! ### Slots -/

theorem tslot_int {h : ℕ} {g : V3} (hg : inBox (-(h : ℤ)) h g = true) :
    (tslot h g : ℤ) = (g.1 + h) + (2 * h + 1) * ((g.2.1 + h) + (2 * h + 1) * (g.2.2 + h)) := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
  unfold tslot
  have hL : (0 : ℤ) ≤ 2 * h + 1 := by positivity
  have p1 : 0 ≤ (2 * (h : ℤ) + 1) * (g.2.2 + h) := mul_nonneg hL (by linarith)
  have p2 : 0 ≤ (2 * (h : ℤ) + 1) * ((g.2.1 + h) + (2 * h + 1) * (g.2.2 + h)) := mul_nonneg hL (by linarith)
  exact Int.toNat_of_nonneg (by linarith)

theorem tslot_lt {h : ℕ} {g : V3} (hg : inBox (-(h : ℤ)) h g = true) :
    tslot h g < (2 * h + 1) ^ 3 := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
  have e := tslot_int hg
  have : (tslot h g : ℤ) < (2 * h + 1) ^ 3 := by
    rw [e]
    have hL : (0 : ℤ) ≤ 2 * h + 1 := by positivity
    have := mul_le_mul_of_nonneg_left (show g.2.2 + h ≤ 2 * h by linarith) hL
    have := mul_le_mul_of_nonneg_left
      (show (g.2.1 + h) + (2 * h + 1) * (g.2.2 + h) ≤ 2 * h + (2 * h + 1) * (2 * h) by nlinarith) hL
    nlinarith
  exact_mod_cast this

theorem tslot_inj {h : ℕ} {g g' : V3} (hg : inBox (-(h : ℤ)) h g = true)
    (hg' : inBox (-(h : ℤ)) h g' = true) (he : tslot h g = tslot h g') : g = g' := by
  have e1 := tslot_int hg
  have e2 := tslot_int hg'
  have hz : (tslot h g : ℤ) = tslot h g' := by exact_mod_cast he
  rw [e1, e2] at hz
  obtain ⟨a, b, c⟩ := g
  obtain ⟨a', b', c'⟩ := g'
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := inBox_spec hg
  obtain ⟨a1', a2', b1', b2', c1', c2'⟩ := inBox_spec hg'
  simp only at hz a1 a2 b1 b2 c1 c2 a1' a2' b1' b2' c1' c2'
  have hd := phi_zero (L := 2 * h + 1) (d := (a - a', b - b', c - c'))
    (by simp only; rw [abs_lt]; constructor <;> linarith)
    (by simp only; rw [abs_lt]; constructor <;> linarith)
    (by simp only; rw [abs_lt]; constructor <;> linarith)
    (by simp only [phi]; linarith)
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg (fun v : V3 => v.2.1) hd
  have h3 := congrArg (fun v : V3 => v.2.2) hd
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2 h3
  have e1 : a = a' := by linarith
  have e2 : b = b' := by linarith
  have e3 : c = c' := by linarith
  rw [e1, e2, e3]

/-! ### Distinctness through the bit set -/

theorem distinctB_cons (s : ℕ) (l : List ℕ) (b : ℕ) :
    distinctB (s :: l) b = (Nat.beq ((b >>> s) % 2) 0 && (distinctB l (b ||| (1 <<< s))).1,
      (distinctB l (b ||| (1 <<< s))).2) := rfl

theorem distinctB_bits (l : List ℕ) (b : ℕ) :
    (distinctB l b).1 = true → (∀ s ∈ l, b.testBit s = false) ∧ l.Nodup := by
  induction l generalizing b with
  | nil => intro _; simp
  | cons s l ih =>
    intro h
    rw [distinctB_cons] at h
    simp only [Bool.and_eq_true, beq_d, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih (b ||| (1 <<< s)) h2
    have hbit : b.testBit s = false := by
      rw [Nat.testBit_to_div_mod]
      rw [Nat.shiftRight_eq_div_pow] at h1
      simp [h1]
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact hbit
      · have := ih1 t ht
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1
    · refine List.nodup_cons.mpr ⟨fun hs => ?_, ih2⟩
      have := ih1 s hs
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at this
      exact absurd this.2 (by simp)

theorem keysOK_spec {h : ℕ} {ks : List V3} (hk : keysOK h ks = true) :
    (∀ g ∈ ks, inBox (-(h : ℤ)) h g = true) ∧ (ks.map (tslot h)).Nodup := by
  unfold keysOK at hk
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  refine ⟨hk.1, ?_⟩
  have := (distinctB_bits _ 0 hk.2).2
  rwa [mapL_eq] at this

/-! ### Digits -/

theorem getD_eq_get {α : Type} (l : List α) (k : ℕ) (d : α) (h : k < l.length) : l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem tslots_getD {h b : ℕ} (l : List (V3 × ℤ)) (k : ℕ) (hk : k < l.length) :
    (tslots h b l).getD k (0, 0) =
      (tslot h (l.getD k (0, 0)).1, b + ipos (l.getD k (0, 0)).2 - ineg (l.getD k (0, 0)).2) := by
  unfold tslots; rw [mapL_getD _ _ _ (0, 0) hk]

theorem tslots_length {h b : ℕ} (l : List (V3 × ℤ)) : (tslots h b l).length = l.length :=
  mapL_length _ _

/-- `tpackS` as a sum over the entries. -/
theorem tpackS_eq (W : ℕ) (l : List (ℕ × ℕ)) :
    tpackS W l = ∑ k ∈ range l.length, (l.getD k (0, 0)).2 * (2 ^ W) ^ (l.getD k (0, 0)).1 := by
  unfold tpackS
  rw [sumL_nat_eq, mapL_length]
  refine sum_congr rfl fun k hk => ?_
  rw [mapL_getD _ _ _ (0, 0) (mem_range.mp hk), Nat.shiftLeft_eq, pow_mul]

/-- The digit of a value `v` with `|v| < b`: `b + ipos v - ineg v = b + v`. -/
theorem dig_val {b : ℕ} {v : ℤ} (hv : ipos v + ineg v < b) : ((b + ipos v - ineg v : ℕ) : ℤ) = b + v := by
  have e := ipos_sub_ineg v
  have : ineg v ≤ b + ipos v := by omega
  rw [Nat.cast_sub this]; push_cast; linarith

/-- **Table lookup.** With keys in the box and distinct slots, values `|v| < b`,
`b + |v| < 2^W`: the digit at `g` (in the box) is `b + v` for the entry with key `g`,
and `0` if there is none. -/
theorem tget_find {W h b : ℕ} {l : List (V3 × ℤ)}
    (hk : keysOK h (l.map Prod.fst) = true) (hv : valsOK W b (l.map Prod.snd) = true)
    {g : V3} (hg : inBox (-(h : ℤ)) h g = true) :
    (∀ p ∈ l, p.1 = g → (tget W h (tpackS W (tslots h b l)) g : ℤ) = b + p.2) ∧
    ((∀ p ∈ l, p.1 ≠ g) → tget W h (tpackS W (tslots h b l)) g = 0) := by
  obtain ⟨hbox, hnd⟩ := keysOK_spec hk
  simp only [List.map_map] at hnd
  have hv' : ∀ p ∈ l, ipos p.2 + ineg p.2 < b ∧ b + (ipos p.2 + ineg p.2) < 2 ^ W := by
    intro p hp
    unfold valsOK at hv
    have := List.all_eq_true.mp hv p.2 (List.mem_map_of_mem hp)
    simpa [Bool.and_eq_true, blt_d] using this
  set B := 2 ^ W with hB
  have hB0 : 0 < B := by positivity
  set T := (2 * h + 1) ^ 3
  set n := l.length
  let s : ℕ → ℕ := fun k => tslot h (l.getD k (0, 0)).1
  let d : ℕ → ℕ := fun k => b + ipos (l.getD k (0, 0)).2 - ineg (l.getD k (0, 0)).2
  have hmem : ∀ k < n, l.getD k (0, 0) ∈ l := fun k hk => getD_mem _ hk
  have hsT : ∀ k < n, s k < T := fun k hk => tslot_lt (hbox _ (List.mem_map_of_mem (hmem k hk)))
  have hsinj : ∀ k < n, ∀ k' < n, s k = s k' → k = k' := by
    intro k hk k' hk' he
    apply (List.Nodup.getElem_inj_iff hnd (hi := by simpa using hk) (hj := by simpa using hk')).mp
    simp only [List.getElem_map, Function.comp]
    have e1 : l.getD k (0, 0) = l[k] := getD_eq_get l k _ hk
    have e2 : l.getD k' (0, 0) = l[k'] := getD_eq_get l k' _ hk'
    have he' : tslot h (l.getD k (0, 0)).1 = tslot h (l.getD k' (0, 0)).1 := he
    rw [e1, e2] at he'; exact he'
  have hdB : ∀ k < n, d k < B := by
    intro k hk
    obtain ⟨h1, h2⟩ := hv' _ (hmem k hk)
    simp only [d]; omega
  -- regroup by slot
  let D : ℕ → ℕ := fun t => ∑ k ∈ (range n).filter (fun k => s k = t), d k
  have hP : tpackS W (tslots h b l) = ∑ t ∈ range T, D t * B ^ t := by
    rw [tpackS_eq, tslots_length]
    have e1 : ∀ k ∈ range n, ((tslots h b l).getD k (0, 0)).2 * B ^ ((tslots h b l).getD k (0, 0)).1 =
        d k * B ^ s k := fun k hk => by rw [tslots_getD _ _ (mem_range.mp hk)]
    rw [sum_congr rfl e1]
    rw [← sum_fiberwise_of_maps_to (s := range n) (t := range T) (g := s)
      (fun k hk => mem_range.mpr (hsT k (mem_range.mp hk)))]
    refine sum_congr rfl fun t _ => ?_
    simp only [D, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    rw [(mem_filter.mp hk).2]
  have hD1 : ∀ t, D t = 0 ∨ ∃ k < n, s k = t ∧ D t = d k := by
    intro t
    by_cases hex : ∃ k < n, s k = t
    · obtain ⟨k, hk, hkt⟩ := hex
      right; refine ⟨k, hk, hkt, ?_⟩
      simp only [D]
      rw [sum_eq_single_of_mem k (by simp [hk, hkt])]
      intro k' hk' hne
      simp only [mem_filter, mem_range] at hk'
      exact absurd (hsinj k' hk'.1 k hk (hk'.2.trans hkt.symm)) hne
    · left; simp only [D]
      refine sum_eq_zero fun k hk => ?_
      simp only [mem_filter, mem_range] at hk
      exact absurd ⟨k, hk.1, hk.2⟩ hex
  have hDB : ∀ t, D t < B := fun t => by
    rcases hD1 t with h0 | ⟨k, hk, -, he⟩
    · rw [h0]; exact hB0
    · rw [he]; exact hdB k hk
  obtain ⟨-, hdig⟩ := digit_nat B hB0 D hDB T
  have hgT := tslot_lt hg
  have htget : tget W h (tpackS W (tslots h b l)) g = D (tslot h g) := by
    unfold tget
    rw [hP, Nat.shiftRight_eq_div_pow, pow_mul]
    exact hdig _ hgT
  rw [htget]
  constructor
  · intro p hp hpg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have hkd : l.getD k (0, 0) = l[k] := getD_eq_get l k _ hk
    rcases hD1 (tslot h g) with h0 | ⟨k', hk', hs', he⟩
    · exfalso
      have : ∃ k₀ < n, s k₀ = tslot h g := ⟨k, hk, by show tslot h (l.getD k (0, 0)).1 = _; rw [hkd, hpg]⟩
      obtain ⟨k₀, hk₀, hs₀⟩ := this
      have : D (tslot h g) ≠ 0 := by
        simp only [D]
        apply Nat.ne_of_gt
        refine lt_of_lt_of_le ?_ (single_le_sum (f := d) (a := k₀) (fun _ _ => Nat.zero_le _)
          (mem_filter.mpr ⟨mem_range.mpr hk₀, hs₀⟩))
        obtain ⟨h1, -⟩ := hv' _ (hmem k₀ hk₀)
        simp only [d]; omega
      exact this h0
    · have hkk : k' = k := hsinj k' hk' k hk (by rw [hs']; show tslot h g = tslot h (l.getD k (0, 0)).1; rw [hkd, hpg])
      subst hkk
      rw [he]
      simp only [d, hkd]
      exact dig_val (hv' _ (List.getElem_mem _)).1
  · intro hno
    rcases hD1 (tslot h g) with h0 | ⟨k', hk', hs', he⟩
    · exact h0
    · exfalso
      have hin := hbox _ (List.mem_map_of_mem (hmem k' hk'))
      have := tslot_inj hin hg hs'
      exact hno _ (hmem k' hk') this

end GW.Endpoint.Kernel.Sig

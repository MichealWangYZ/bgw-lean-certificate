/-
G2-coulomb (13/n): from certified orbit representatives to a whole Coulomb table.

`RepOK k r`: the average `cavg k (r.key/2)` lies in `64π [r.SL, r.SH] / N_k`.
`tabChk`: every entry `(key, lo, hi)` of a table is `g · r.key` for a representative `r` and a
signed permutation `g` (hint), and `boxOK` places `64π [SL, SH]/N_k` inside `[lo, hi]/2^SV`.
`tab_sound`: then every entry's true average lies in its box.
-/
import GW.Endpoint.Coulomb.Symm
import GW.Endpoint.Coulomb.Core

namespace GW.Endpoint.Coulomb

open MeasureTheory

structure Rep where
  key : ℤ × ℤ × ℤ
  SL : ℤ
  SH : ℤ
deriving DecidableEq, Repr, Inhabited

/-- The certified enclosure of one representative. -/
def RepOK (k : ℕ) (r : Rep) : Prop :=
  64 * Real.pi * (r.SL : ℝ) / denN WCc Dvc k ≤ cavg k (keyQ r.key) ∧
    cavg k (keyQ r.key) ≤ 64 * Real.pi * (r.SH : ℝ) / denN WCc Dvc k

def dSG : SG := ⟨0, 1, 2, false⟩

/-- One entry, with hint `(representative index, group index)`. -/
def entryOK (k SV : ℕ) (reps : List Rep) (h : ℕ × ℕ) (p : (ℤ × ℤ × ℤ) × ℤ × ℤ) : Bool :=
  let r := reps.getD h.1 default
  let g := G12.getD h.2 dSG
  decide (h.1 < reps.length) && decide (h.2 < G12.length) && decide (g.actK r.key = p.1) &&
    boxOK (denN WCc Dvc k) SV r.SL r.SH p.2.1 p.2.2

def tabChk (k SV : ℕ) (reps : List Rep) : List ((ℤ × ℤ × ℤ) × ℤ × ℤ) → List (ℕ × ℕ) → Bool
  | [], _ => true
  | p :: ps, h :: hs => entryOK k SV reps h p && tabChk k SV reps ps hs
  | _ :: _, [] => false

theorem entry_sound {k SV : ℕ} {reps : List Rep} (hr : ∀ r ∈ reps, RepOK k r) {h : ℕ × ℕ}
    {p : (ℤ × ℤ × ℤ) × ℤ × ℤ} (he : entryOK k SV reps h p = true) :
    (p.2.1 : ℝ) / 2 ^ SV ≤ cavg k (keyQ p.1) ∧ cavg k (keyQ p.1) ≤ (p.2.2 : ℝ) / 2 ^ SV := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := he
  have hrm : reps.getD h.1 default ∈ reps := by
    rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem _
  have hgm : G12.getD h.2 dSG ∈ G12 := by
    rw [List.getD_eq_getElem _ _ h2]; exact List.getElem_mem _
  rw [← h3, keyQ_act, cavg_symm hgm]
  exact box_of _ SV h4 (hr _ hrm)

theorem tab_sound {k SV : ℕ} {reps : List Rep} (hr : ∀ r ∈ reps, RepOK k r) :
    ∀ (ps : List ((ℤ × ℤ × ℤ) × ℤ × ℤ)) (hs : List (ℕ × ℕ)), tabChk k SV reps ps hs = true →
      ∀ p ∈ ps, (p.2.1 : ℝ) / 2 ^ SV ≤ cavg k (keyQ p.1) ∧ cavg k (keyQ p.1) ≤ (p.2.2 : ℝ) / 2 ^ SV
  | [], _, _ => by simp
  | p :: ps, h :: hs, ht => by
    simp only [tabChk, Bool.and_eq_true] at ht
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact entry_sound hr ht.1
    · exact tab_sound hr ps hs ht.2 q hq
  | _ :: _, [], ht => by simp [tabChk] at ht

/-! ### A representative from its 72 face checks -/

theorem sum_fin_list (f : ℕ → ℤ) : ∀ n : ℕ, ∑ i : Fin n, f i.val = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Fin.sum_univ_castSucc, List.range_succ, List.map_append, List.sum_append, ← sum_fin_list f n]; simp

theorem rep_of_faces (key : ℤ × ℤ × ℤ) {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hDeg : ∀ d ∈ degList, ruleOK d WCc (gmM d) (gmRule d) = true) (fs : List (QT × ℤ × ℤ))
    (hf : ∀ i : Fin 72, faceChkC key k (fs.getD i.val dFace) i.val = true) {SL SH : ℤ}
    (hL : sumLoC key fs = SL) (hH : sumHiC key fs = SH) : RepOK k ⟨key, SL, SH⟩ := by
  have h := cavg_bound key hk hDeg (fun i => (fs.getD i.val dFace).2.1) (fun i => (fs.getD i.val dFace).2.2)
    (fun i => (fs.getD i.val dFace).1) (fun i => by
      have := hf i
      simp only [faceChkC, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this)
  have eL : (∑ i : Fin 72, fLo key i (fs.getD i.val dFace).2.1 (fs.getD i.val dFace).2.2) = SL := by
    rw [← hL, sumLoC, ← sum_fin_list (fun i => fLoC key i (fs.getD i dFace).2.1 (fs.getD i dFace).2.2)]; rfl
  have eH : (∑ i : Fin 72, fHi key i (fs.getD i.val dFace).2.1 (fs.getD i.val dFace).2.2) = SH := by
    rw [← hH, sumHiC, ← sum_fin_list (fun i => fHiC key i (fs.getD i dFace).2.1 (fs.getD i dFace).2.2)]; rfl
  rw [eL, eH] at h
  exact h

/-- A rule certificate from its rows. -/
theorem ruleOK_of_rows (d : ℕ) (hn : nodesOK (gmM d) (gmRule d) = true) (hM : 0 < gmM d)
    (hr : ∀ i < d + 1, ruleRow d WCc (gmM d) (gmRule d) i = true) : ruleOK d WCc (gmM d) (gmRule d) = true := by
  simp only [ruleOK, hn, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨hM, by norm_num [WCc]⟩, hr⟩

end GW.Endpoint.Coulomb

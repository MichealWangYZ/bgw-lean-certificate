/-
G2 stage 1: soundness of the kernel checker `GW.Endpoint.Kernel.Cert` (file
`Check.lean`), reusing the componentwise Neumann enclosure and the balancing
lemmas of `GW.Endpoint.CertInverse`.

Main result: `Cert.sound` — if `c.Valid` (every row check and the global check
evaluate to `true`), then every real matrix `A0` inside the interval matrix
`[epsLo, epsHi] / 2^SE` is invertible and `A0⁻¹ i j ∈ [outLo i j, outHi i j] / 2^SO`.
-/
import GW.Endpoint.Kernel.Check
import GW.Endpoint.CertInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

namespace GW.Endpoint.Kernel

open Finset

/-! ### List lemmas -/

section lists

variable {α β γ : Type}

@[simp] theorem axpy_nil [Add α] [Mul α] (c : α) (ys : List α) : axpy c [] ys = [] := rfl
@[simp] theorem axpy_cons_nil [Add α] [Mul α] (c a : α) (as : List α) :
    axpy c (a :: as) [] = [] := rfl
@[simp] theorem axpy_cons_cons [Add α] [Mul α] (c a y : α) (as ys : List α) :
    axpy c (a :: as) (y :: ys) = (a + c * y) :: axpy c as ys := rfl

@[simp] theorem zipW_nil (g : α → β → γ) (ys : List β) : zipW g [] ys = [] := rfl
@[simp] theorem zipW_cons_nil (g : α → β → γ) (a : α) (as : List α) :
    zipW g (a :: as) [] = [] := rfl
@[simp] theorem zipW_cons_cons (g : α → β → γ) (a : α) (y : β) (as : List α) (ys : List β) :
    zipW g (a :: as) (y :: ys) = g a y :: zipW g as ys := rfl

@[simp] theorem comb_nil [Add α] [Mul α] (acc : List α) (Ys : List (List α)) :
    comb [] acc Ys = acc := rfl
@[simp] theorem comb_cons_nil [Add α] [Mul α] (c : α) (cs acc : List α) :
    comb (c :: cs) acc [] = acc := rfl
@[simp] theorem comb_cons_cons [Add α] [Mul α] (c : α) (cs acc y : List α) (Ys : List (List α)) :
    comb (c :: cs) acc (y :: Ys) = comb cs (axpy c acc y) Ys := rfl

@[simp] theorem all2_nil_nil (p : α → β → Bool) : all2 p [] [] = true := rfl
@[simp] theorem all2_nil_cons (p : α → β → Bool) (y : β) (ys : List β) :
    all2 p [] (y :: ys) = false := rfl
@[simp] theorem all2_cons_nil (p : α → β → Bool) (a : α) (as : List α) :
    all2 p (a :: as) [] = false := rfl
@[simp] theorem all2_cons_cons (p : α → β → Bool) (a : α) (y : β) (as : List α) (ys : List β) :
    all2 p (a :: as) (y :: ys) = (p a y && all2 p as ys) := rfl

@[simp] theorem sumL_nil [Add α] (s : α) : sumL [] s = s := rfl
@[simp] theorem sumL_cons [Add α] (a : α) (as : List α) (s : α) :
    sumL (a :: as) s = sumL as (s + a) := rfl

theorem axpy_length [Add α] [Mul α] (c : α) :
    ∀ (acc ys : List α), acc.length = ys.length → (axpy c acc ys).length = acc.length
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | _ :: as, _ :: ys, h => by
      simp only [axpy_cons_cons, List.length_cons] at h ⊢
      rw [axpy_length c as ys (by omega)]

theorem axpy_getD [Semiring α] (c : α) :
    ∀ (acc ys : List α), acc.length = ys.length → ∀ j,
      (axpy c acc ys).getD j 0 = acc.getD j 0 + c * ys.getD j 0
  | [], [], _, j => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, y :: ys, h, j => by
      cases j with
      | zero => simp
      | succ j =>
        simp only [axpy_cons_cons, List.getD_cons_succ]
        exact axpy_getD c as ys (by simpa using h) j

theorem zipW_length (g : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β), (zipW g l1 l2).length = min l1.length l2.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | _ :: as, _ :: ys => by
      simp only [zipW_cons_cons, List.length_cons, zipW_length g as ys]; omega

theorem zipW_getD (g : α → β → γ) (d : γ) (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β) (j : ℕ), j < l1.length → j < l2.length →
      (zipW g l1 l2).getD j d = g (l1.getD j d1) (l2.getD j d2)
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, y :: ys, j, h1, h2 => by
      cases j with
      | zero => simp
      | succ j =>
        simp only [zipW_cons_cons, List.getD_cons_succ]
        exact zipW_getD g d d1 d2 as ys j (by simpa using h1) (by simpa using h2)

theorem comb_length [Add α] [Mul α] :
    ∀ (cs acc : List α) (Ys : List (List α)), (∀ y ∈ Ys, y.length = acc.length) →
      (comb cs acc Ys).length = acc.length
  | [], _, _, _ => rfl
  | _ :: _, _, [], _ => rfl
  | c :: cs, acc, y :: Ys, h => by
      simp only [comb_cons_cons]
      have hy : acc.length = y.length := (h y (by simp)).symm
      rw [comb_length cs _ Ys (fun z hz => by
        rw [axpy_length c acc y hy]; exact h z (by simp [hz])), axpy_length c acc y hy]

theorem comb_getD [Semiring α] :
    ∀ (cs acc : List α) (Ys : List (List α)), cs.length = Ys.length →
      (∀ y ∈ Ys, y.length = acc.length) → ∀ j,
      (comb cs acc Ys).getD j 0 =
        acc.getD j 0 + ∑ k ∈ range cs.length, cs.getD k 0 * (Ys.getD k []).getD j 0
  | [], acc, _, _, _, j => by simp
  | _ :: _, _, [], h, _, _ => by simp at h
  | c :: cs, acc, y :: Ys, h, hY, j => by
      simp only [comb_cons_cons, List.length_cons]
      have hy : acc.length = y.length := (hY y (by simp)).symm
      rw [comb_getD cs (axpy c acc y) Ys (by simpa using h) (fun z hz => by
        rw [axpy_length c acc y hy]; exact hY z (by simp [hz])) j,
        axpy_getD c acc y hy j, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_assoc]; congr 1; exact add_comm _ _

theorem all2_spec (p : α → β → Bool) (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β), all2 p l1 l2 = true →
      l1.length = l2.length ∧ ∀ j < l1.length, p (l1.getD j d1) (l2.getD j d2) = true
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, y :: ys, h => by
      simp only [all2_cons_cons, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := all2_spec p d1 d2 as ys h.2
      refine ⟨by simp [h1], fun j hj => ?_⟩
      cases j with
      | zero => simpa using h.1
      | succ j => simpa using h2 j (by simpa using hj)

theorem sumL_eq [AddCommMonoid α] :
    ∀ (l : List α) (s : α), sumL l s = s + ∑ j ∈ range l.length, l.getD j 0
  | [], s => by simp
  | a :: as, s => by
      rw [sumL_cons, sumL_eq as, List.length_cons, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_assoc, add_comm a]

theorem getD_replicate_zero [Zero α] : ∀ (n j : ℕ), (List.replicate n (0 : α)).getD j 0 = 0
  | 0, _ => by simp
  | _ + 1, 0 => by simp [List.replicate_succ]
  | n + 1, j + 1 => by simpa [List.replicate_succ] using getD_replicate_zero n j

theorem getD_replicate (n j : ℕ) {a d : α} (h : j < n) : (List.replicate n a).getD j d = a := by
  rw [List.getD_eq_getElem?_getD]; simp [h]

theorem unitRow_length (n i : ℕ) (d : ℤ) : (unitRow n i d).length = n := by simp [unitRow]

theorem unitRow_getD (n i j : ℕ) (d : ℤ) (h : j < n) :
    (unitRow n i d).getD j 0 = if j = i then d else 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [unitRow, h]

theorem shapeOK_spec {n : ℕ} {M : List (List α)} (h : shapeOK n M = true) :
    M.length = n ∧ ∀ i, i < n → (M.getD i []).length = n := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have hi' : i < M.length := h.1 ▸ hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  simpa using h.2 _ (List.getElem_mem hi')

theorem shape_mem {n : ℕ} {M : List (List α)} (h : shapeOK n M = true) :
    ∀ y ∈ M, y.length = n := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  intro y hy; simpa using h.2 y hy

end lists

/-! ### Real semantics -/

/-- Entry `(i, j)` of a list matrix (`0` outside). -/
def ent {α : Type} [Zero α] (M : List (List α)) (i j : ℕ) : α := (M.getD i []).getD j 0

namespace Cert

variable (c : Cert)

/-- The real matrix `M / 2^S`. -/
noncomputable def mat (S : ℕ) (M : List (List ℤ)) : Matrix (Fin c.n) (Fin c.n) ℝ :=
  Matrix.of fun i j => ((ent M i j : ℤ) : ℝ) / 2 ^ S

/-- The real matrix `M / 2^S` of a natural-number list matrix. -/
noncomputable def matN (S : ℕ) (M : List (List ℕ)) : Matrix (Fin c.n) (Fin c.n) ℝ :=
  Matrix.of fun i j => ((ent M i j : ℕ) : ℝ) / 2 ^ S

/-- The balancing vector `s_i = 2^(f_i)`. -/
noncomputable def sv (i : Fin c.n) : ℝ := 2 ^ (c.f.getD i 0)

variable {c}

/-- A row combination of an `n`-row matrix with rows of length `n`, entrywise. -/
theorem comb_row [Semiring α] {n : ℕ} {cs : List α} {Y : List (List α)} (hcs : cs.length = n)
    (hY : shapeOK n Y = true) (j : ℕ) :
    (comb cs (List.replicate n 0) Y).getD j 0 = ∑ k ∈ range n, cs.getD k 0 * ent Y k j := by
  have hY1 := shapeOK_spec hY
  rw [comb_getD cs _ Y (by rw [hcs, hY1.1]) (fun y hy => by
    rw [List.length_replicate]; exact shape_mem hY y hy) j, getD_replicate_zero, zero_add, hcs]
  rfl

theorem comb_row_length {α : Type} [Add α] [Mul α] [Zero α] {n : ℕ} (cs : List α)
    {Y : List (List α)} (hY : shapeOK n Y = true) :
    (comb cs (List.replicate n 0) Y).length = n := by
  rw [comb_length cs _ Y (fun y hy => by rw [List.length_replicate]; exact shape_mem hY y hy),
    List.length_replicate]

theorem sum_fin (n : ℕ) (g : ℕ → ℝ) : ∑ k : Fin n, g k = ∑ k ∈ range n, g k :=
  Fin.sum_univ_eq_sum_range g n

/-- `chkMul` on every row gives the entrywise bound `F Y ≤ T` of the real matrices. -/
theorem mul_le {SY : ℕ} {Y T : List (List ℕ)} (hF : shapeOK c.n c.F = true)
    (hY : shapeOK c.n Y = true) (hT : shapeOK c.n T = true)
    (h : ∀ i < c.n, c.chkMul SY Y T i = true) (i j : Fin c.n) :
    (c.matN c.K c.F * c.matN SY Y) i j ≤ c.matN c.K T i j := by
  have hFi := (shapeOK_spec hF).2 i i.2
  obtain ⟨_, hrow⟩ := all2_spec _ 0 0 _ _ (h i i.2)
  have hj := hrow j (by rw [(shapeOK_spec hT).2 i i.2]; exact j.2)
  rw [comb_row hFi hY, decide_eq_true_eq] at hj
  simp only [Matrix.mul_apply, matN, Matrix.of_apply]
  rw [sum_fin c.n (fun k => ((ent c.F i k : ℕ) : ℝ) / 2 ^ c.K * (((ent Y k j : ℕ) : ℝ) / 2 ^ SY))]
  have hcast : (∑ k ∈ range c.n, ((ent c.F i k : ℕ) : ℝ) * ((ent Y k j : ℕ) : ℝ)) ≤
      ((ent T i j : ℕ) : ℝ) * 2 ^ SY := by
    exact_mod_cast hj
  have e : ∑ k ∈ range c.n, ((ent c.F i k : ℕ) : ℝ) / 2 ^ c.K * (((ent Y k j : ℕ) : ℝ) / 2 ^ SY) =
      (∑ k ∈ range c.n, ((ent c.F i k : ℕ) : ℝ) * ((ent Y k j : ℕ) : ℝ)) / (2 ^ c.K * 2 ^ SY) := by
    rw [Finset.sum_div]; congr 1; ext k; field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ k ∈ range c.n, ((ent c.F i k : ℕ) : ℝ) * ((ent Y k j : ℕ) : ℝ)) * 2 ^ c.K
      ≤ ((ent T i j : ℕ) : ℝ) * 2 ^ SY * 2 ^ c.K := mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ((ent T i j : ℕ) : ℝ) * (2 ^ c.K * 2 ^ SY) := by ring


theorem zipW_prod_getD {α β : Type} {l1 : List α} {l2 : List β} {j : ℕ} (d1 : α) (d2 : β)
    (h1 : j < l1.length) (h2 : j < l2.length) :
    (zipW Prod.mk l1 l2).getD j (d1, d2) = (l1.getD j d1, l2.getD j d2) :=
  zipW_getD _ _ _ _ _ _ _ h1 h2

theorem zipW_len {α β γ : Type} {n : ℕ} (g : α → β → γ) {l1 : List α} {l2 : List β}
    (h1 : l1.length = n) (h2 : l2.length = n) : (zipW g l1 l2).length = n := by
  rw [zipW_length, h1, h2, min_self]

theorem getD_mem_of_lt {α : Type} {l : List α} {j : ℕ} (d : α) (h : j < l.length) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- The integer content of `chkE`: for `c_k = R_ik 2^(G - f_k)`, `m = lo + hi`,
`r = hi - lo`, `2^K (|δ_ij 2^S1 - (∑ c m) 2^f_j| + (∑ |c| r) 2^f_j) ≤ F_ij 2^S1`. -/
theorem e_int (hR : shapeOK c.n c.R = true) (hRabs : shapeOK c.n c.Rabs = true)
    (hmid : shapeOK c.n c.mid2 = true) (hrad : shapeOK c.n c.rad2 = true)
    (hF : shapeOK c.n c.F = true) (hf : c.f.length = c.n)
    (hcolL : c.colM.length = c.n)
    (hcol : ∀ j < c.n, c.colM.getD j 0 = ∑ k ∈ range c.n, ent c.mid2 k j)
    (henc : ∀ k < c.n, ∀ j < c.n,
      ent c.epsLo k j + ent c.epsHi k j + (c.M : ℤ) = ((ent c.mid2 k j : ℕ) : ℤ) ∧
      ent c.epsHi k j - ent c.epsLo k j = ((ent c.rad2 k j : ℕ) : ℤ))
    {i : ℕ} (hi : i < c.n) (habs : ∀ k < c.n, (ent c.R i k).natAbs = ent c.Rabs i k)
    (h : c.chkE i = true) {j : ℕ} (hj : j < c.n) :
    (2 : ℤ) ^ c.K * (|(if j = i then (2 : ℤ) ^ (c.SR + c.SE + c.G + 1) else 0) -
        (∑ k ∈ range c.n, ent c.R i k * 2 ^ (c.G - c.f.getD k 0) *
          (ent c.epsLo k j + ent c.epsHi k j)) * 2 ^ c.f.getD j 0| +
      (∑ k ∈ range c.n, |ent c.R i k * 2 ^ (c.G - c.f.getD k 0)| *
          (ent c.epsHi k j - ent c.epsLo k j)) * 2 ^ c.f.getD j 0) ≤
      ((ent c.F i j : ℕ) : ℤ) * 2 ^ (c.SR + c.SE + c.G + 1) := by
  simp only [chkE, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnn, hall⟩ := h
  have hRi : (c.R.getD i []).length = c.n := (shapeOK_spec hR).2 i hi
  have hRai : (c.Rabs.getD i []).length = c.n := (shapeOK_spec hRabs).2 i hi
  have hFi : (c.F.getD i []).length = c.n := (shapeOK_spec hF).2 i hi
  set co := zipW c.cOff (c.R.getD i []) c.f with hco
  have hcoL : co.length = c.n := zipW_len _ hRi hf
  have hcoK : ∀ k < c.n, co.getD k 0 = c.cOff (ent c.R i k) (c.f.getD k 0) := fun k hk =>
    zipW_getD _ _ 0 0 _ _ _ (by omega) (by omega)
  set cs := zipW (fun x (_ : ℕ) => Int.toNat x) co c.f with hcs
  have hcsL : cs.length = c.n := zipW_len _ hcoL hf
  have hcsK : ∀ k < c.n, (cs.getD k 0 : ℤ) =
      ent c.R i k * 2 ^ (c.G - c.f.getD k 0) + c.MR := fun k hk => by
    rw [hcs, zipW_getD _ _ 0 0 _ _ _ (by omega) (by omega)]
    have h0 := hnn _ (getD_mem_of_lt 0 (show k < co.length by omega))
    rw [Int.toNat_of_nonneg h0, hcoK k hk]
    simp [cOff]
  set ca := zipW (fun a fk => a * 2 ^ (c.G - fk)) (c.Rabs.getD i []) c.f with hca
  have hcaL : ca.length = c.n := zipW_len _ hRai hf
  have hcaK : ∀ k < c.n, (ca.getD k 0 : ℤ) = |ent c.R i k * 2 ^ (c.G - c.f.getD k 0)| :=
    fun k hk => by
      rw [hca, zipW_getD _ _ 0 0 _ _ _ (by omega) (by omega)]
      have := habs k hk
      rw [abs_mul, ← Int.natCast_natAbs, this]
      simp [ent]
  -- the entry `j` of the `all2`
  have hZL := comb_row_length cs hmid
  have hYL := comb_row_length ca hrad
  have huL := unitRow_length c.n i (Int.ofNat (2 ^ (c.SR + c.SE + c.G + 1)))
  obtain ⟨_, hj'⟩ := all2_spec _ 0 (0, 0, 0, 0, 0) _ _ hall
  have hjj := hj' j (by rw [hFi]; exact hj)
  have l4 := zipW_len Prod.mk hf huL
  have l3 := zipW_len Prod.mk hYL l4
  have l2 := zipW_len Prod.mk hcolL l3
  rw [zipW_prod_getD _ _ (by rw [hZL]; exact hj) (by rw [l2]; exact hj),
    zipW_prod_getD _ _ (by rw [hcolL]; exact hj) (by rw [l3]; exact hj),
    zipW_prod_getD _ _ (by rw [hYL]; exact hj) (by rw [l4]; exact hj),
    zipW_prod_getD _ _ (by rw [hf]; exact hj) (by rw [huL]; exact hj)] at hjj
  rw [comb_row hcsL hmid, comb_row hcaL hrad, unitRow_getD _ _ _ _ hj, hcol j hj] at hjj
  simp only [eOK, decide_eq_true_eq] at hjj
  rw [sumL_eq, hcsL, zero_add] at hjj
  have hz := (Nat.cast_le (α := ℤ)).mpr hjj
  push_cast [Int.ofNat_eq_coe, Int.natCast_natAbs] at hz
  set cc : ℕ → ℤ := fun k => ent c.R i k * 2 ^ (c.G - c.f.getD k 0) with hcc
  have e1 : ∑ k ∈ range c.n, ((cs.getD k 0 : ℕ) : ℤ) * ((ent c.mid2 k j : ℕ) : ℤ) =
      ∑ k ∈ range c.n, (cc k + c.MR) * ((ent c.epsLo k j + ent c.epsHi k j) + c.M) :=
    sum_congr rfl fun k hk => by rw [hcsK k (mem_range.mp hk), ← (henc k (mem_range.mp hk) j hj).1]
  have e2 : ∑ k ∈ range c.n, ((ent c.mid2 k j : ℕ) : ℤ) =
      ∑ k ∈ range c.n, ((ent c.epsLo k j + ent c.epsHi k j) + c.M) :=
    sum_congr rfl fun k hk => by rw [← (henc k (mem_range.mp hk) j hj).1]
  have e3 : ∑ k ∈ range c.n, ((cs.getD k 0 : ℕ) : ℤ) = ∑ k ∈ range c.n, (cc k + c.MR) :=
    sum_congr rfl fun k hk => by rw [hcsK k (mem_range.mp hk)]
  have e4 : ∑ k ∈ range c.n, ((ca.getD k 0 : ℕ) : ℤ) * ((ent c.rad2 k j : ℕ) : ℤ) =
      ∑ k ∈ range c.n, |cc k| * (ent c.epsHi k j - ent c.epsLo k j) :=
    sum_congr rfl fun k hk => by rw [hcaK k (mem_range.mp hk), ← (henc k (mem_range.mp hk) j hj).2]
  rw [e1, e2, e3, e4] at hz
  have key : ∑ k ∈ range c.n, (cc k + c.MR) * ((ent c.epsLo k j + ent c.epsHi k j) + c.M) -
      c.MR * ∑ k ∈ range c.n, ((ent c.epsLo k j + ent c.epsHi k j) + c.M) -
      c.M * ∑ k ∈ range c.n, (cc k + c.MR) + c.n * c.MR * c.M =
      ∑ k ∈ range c.n, cc k * (ent c.epsLo k j + ent c.epsHi k j) := by
    simp only [add_mul, mul_add, sum_add_distrib, ← mul_sum, ← sum_mul, sum_const, card_range,
      nsmul_eq_mul]
    ring
  rw [key] at hz
  refine le_of_eq_of_le ?_ (hz.trans (le_of_eq ?_))
  · split_ifs <;> simp [hcc]
  · simp [ent]

/-- Interval membership at the integer scale. -/
theorem scaled_mem {S : ℕ} {lo hi : ℤ} {x : ℝ}
    (h : x ∈ Set.Icc ((lo : ℝ) / 2 ^ S) ((hi : ℝ) / 2 ^ S)) :
    (lo : ℝ) ≤ x * 2 ^ S ∧ x * 2 ^ S ≤ hi := by
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  exact ⟨(div_le_iff₀ h2).mp h.1, (le_div_iff₀ h2).mp h.2⟩

/-- **The `E` bound**: the `chkE` rows give `F ≥ |1 - R A'|` for every member
`A0` of the interval matrix, `A' = balance s A0`. -/
theorem dom_E (hR : shapeOK c.n c.R = true) (hRabs : shapeOK c.n c.Rabs = true)
    (hmid : shapeOK c.n c.mid2 = true) (hrad : shapeOK c.n c.rad2 = true)
    (hF : shapeOK c.n c.F = true) (hf : c.f.length = c.n)
    (hG : ∀ k < c.n, c.f.getD k 0 ≤ c.G)
    (hcolL : c.colM.length = c.n)
    (hcol : ∀ j < c.n, c.colM.getD j 0 = ∑ k ∈ range c.n, ent c.mid2 k j)
    (henc : ∀ k < c.n, ∀ j < c.n,
      ent c.epsLo k j + ent c.epsHi k j + (c.M : ℤ) = ((ent c.mid2 k j : ℕ) : ℤ) ∧
      ent c.epsHi k j - ent c.epsLo k j = ((ent c.rad2 k j : ℕ) : ℤ))
    (habs : ∀ i < c.n, ∀ k < c.n, (ent c.R i k).natAbs = ent c.Rabs i k)
    (hE : ∀ i < c.n, c.chkE i = true) (A0 : Matrix (Fin c.n) (Fin c.n) ℝ)
    (hA : ∀ i j, A0 i j ∈ Set.Icc (c.mat c.SE c.epsLo i j) (c.mat c.SE c.epsHi i j)) :
    GW.Endpoint.Cert.Dom (1 - c.mat c.SR c.R * GW.Endpoint.Cert.balance c.sv A0)
      (c.matN c.K c.F) := by
  intro i j
  have hint := e_int hR hRabs hmid hrad hF hf hcolL hcol henc i.2 (habs i i.2) (hE i i.2) j.2
  have hr := (Int.cast_le (R := ℝ)).mpr hint
  push_cast at hr
  simp only [Finset.sum_range] at hr
  set S1 := c.SR + c.SE + c.G + 1 with hS1
  set p : ℝ := 2 ^ c.f.getD j 0 with hp
  set cc : Fin c.n → ℝ := fun k => ((ent c.R i k : ℤ) : ℝ) * 2 ^ (c.G - c.f.getD k 0) with hcc
  set a : Fin c.n → ℝ := fun k => A0 k j * 2 ^ c.SE with ha
  set m : Fin c.n → ℝ := fun k => ((ent c.epsLo k j : ℤ) : ℝ) + ent c.epsHi k j with hm
  set r : Fin c.n → ℝ := fun k => ((ent c.epsHi k j : ℤ) : ℝ) - ent c.epsLo k j with hrr
  set δ : ℝ := if (j : ℕ) = i then 2 ^ S1 else 0 with hδ
  have hp0 : 0 ≤ p := by positivity
  -- the balanced product at scale 2^S1
  have hsum : (c.mat c.SR c.R * GW.Endpoint.Cert.balance c.sv A0) i j * 2 ^ S1 =
      p * ∑ k, cc k * (2 * a k) := by
    simp only [Matrix.mul_apply, mat, GW.Endpoint.Cert.balance, Matrix.of_apply, sv]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have hGk : (2 : ℝ) ^ c.G = 2 ^ (c.G - c.f.getD k 0) * 2 ^ c.f.getD k 0 := by
      rw [← pow_add, Nat.sub_add_cancel (hG k k.2)]
    have e : (2 : ℝ) ^ S1 = 2 ^ c.SR * 2 ^ c.SE * 2 ^ c.G * 2 := by
      rw [hS1, pow_succ, pow_add, pow_add]
    rw [e, hGk, hp, hcc, ha]
    field_simp
    ring
  have hδ' : (1 : Matrix (Fin c.n) (Fin c.n) ℝ) i j * 2 ^ S1 = δ := by
    rw [Matrix.one_apply, hδ]
    by_cases h : i = j
    · subst h; simp
    · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
      simp [h, h']
  have hmr : ∀ k, |2 * a k - m k| ≤ r k := fun k => by
    obtain ⟨h1, h2⟩ := scaled_mem (hA k j)
    simp only [ha, hm, hrr]
    rw [abs_le]; constructor <;> linarith
  have hE0 : |(1 - c.mat c.SR c.R * GW.Endpoint.Cert.balance c.sv A0) i j| * 2 ^ S1 ≤
      |δ - (∑ k, cc k * m k) * p| + (∑ k, |cc k| * r k) * p := by
    rw [← abs_of_pos (show (0 : ℝ) < 2 ^ S1 by positivity), ← abs_mul, Matrix.sub_apply,
      sub_mul, hδ', hsum]
    have : δ - p * ∑ k, cc k * (2 * a k) =
        (δ - (∑ k, cc k * m k) * p) - p * ∑ k, cc k * (2 * a k - m k) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [this]
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    rw [abs_mul, abs_of_nonneg hp0, mul_comm]
    refine mul_le_mul_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun k _ => ?_)) hp0
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmr k) (abs_nonneg _)
  have hK : (0 : ℝ) < 2 ^ c.K := by positivity
  have hS : (0 : ℝ) < 2 ^ S1 := by positivity
  simp only [matN, Matrix.of_apply]
  rw [le_div_iff₀ hK]
  have h3 : (2 : ℝ) ^ c.K * (|(1 - c.mat c.SR c.R * GW.Endpoint.Cert.balance c.sv A0) i j| *
      2 ^ S1) ≤ ((ent c.F i j : ℕ) : ℝ) * 2 ^ S1 := by
    refine (mul_le_mul_of_nonneg_left hE0 hK.le).trans (le_of_eq_of_le ?_ hr)
    simp only [hδ, hcc, hm, hrr, hp]
  nlinarith

/-- What one `chkRow i` gives, entrywise. -/
theorem row_spec (hlo : shapeOK c.n c.epsLo = true) (hhi : shapeOK c.n c.epsHi = true)
    (hmid : shapeOK c.n c.mid2 = true) (hrad : shapeOK c.n c.rad2 = true)
    (hR : shapeOK c.n c.R = true) (hol : shapeOK c.n c.outLo = true) (hoh : shapeOK c.n c.outHi = true)
    (hT0 : shapeOK c.n c.T0 = true) (hT1 : shapeOK c.n c.T1 = true)
    (hT2 : shapeOK c.n c.T2 = true) (hF : shapeOK c.n c.F = true) (hf : c.f.length = c.n)
    {i : ℕ} (hi : i < c.n) (h : c.chkRow i = true) :
    (∀ j < c.n, ent c.epsLo i j + ent c.epsHi i j + (c.M : ℤ) = ((ent c.mid2 i j : ℕ) : ℤ) ∧
      ent c.epsHi i j - ent c.epsLo i j = ((ent c.rad2 i j : ℕ) : ℤ)) ∧
    (∀ j < c.n, (ent c.R i j).natAbs = ent c.Rabs i j) ∧
    ∑ j ∈ range c.n, ent c.F i j ≤ c.beta ∧ ∑ j ∈ range c.n, ent c.T0 i j ≤ c.rho ∧
    ∀ j < c.n, c.outOK (c.f.getD i 0) (c.f.getD j 0) (ent c.R i j) (ent c.outLo i j)
      (ent c.outHi i j) (ent c.T0 i j + (ent c.T1 i j + ent c.T2 i j) + c.tail) = true := by
  simp only [chkRow, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have L := fun {α : Type} (M : List (List α)) (hM : shapeOK c.n M = true) =>
    (shapeOK_spec hM).2 i hi
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨_, h1'⟩ := all2_spec _ (0, 0) (0, 0) _ _ h1
    have := h1' j (by rw [zipW_len _ (L _ hlo) (L _ hhi)]; exact hj)
    rw [zipW_prod_getD _ _ (by rw [L _ hlo]; exact hj) (by rw [L _ hhi]; exact hj),
      zipW_prod_getD _ _ (by rw [L _ hmid]; exact hj) (by rw [L _ hrad]; exact hj)] at this
    simpa [encOK] using this
  · obtain ⟨_, h2'⟩ := all2_spec _ 0 0 _ _ h2
    simpa using h2' j (by rw [L _ hR]; exact hj)
  · rw [sumL_eq, L _ hF, zero_add] at h3; exact h3
  · rw [sumL_eq, L _ hT0, zero_add] at h4; exact h4
  · obtain ⟨_, h5'⟩ := all2_spec _ 0 ((0, 0, 0), 0) _ _ h5
    have l1 := zipW_len Prod.mk (L _ hol) (L _ hoh)
    have l2 := zipW_len Prod.mk (L _ hR) l1
    have l3 := zipW_len (· + ·) (L _ hT1) (L _ hT2)
    have l4 := zipW_len (· + ·) (L _ hT0) l3
    have l5 := zipW_len (· + ·) l4 (List.length_replicate (n := c.n) (a := c.tail))
    have := h5' j (by rw [hf]; exact hj)
    rw [zipW_prod_getD _ _ (by rw [l2]; exact hj) (by rw [l5]; exact hj),
      zipW_prod_getD _ _ (by rw [L _ hR]; exact hj) (by rw [l1]; exact hj),
      zipW_prod_getD _ _ (by rw [L _ hol]; exact hj) (by rw [L _ hoh]; exact hj),
      zipW_getD _ _ 0 0 _ _ _ (by rw [l4]; exact hj) (by rw [List.length_replicate]; exact hj),
      zipW_getD _ _ 0 0 _ _ _ (by rw [L _ hT0]; exact hj) (by rw [l3]; exact hj),
      zipW_getD _ _ 0 0 _ _ _ (by rw [L _ hT1]; exact hj) (by rw [L _ hT2]; exact hj),
      getD_replicate _ _ hj] at this
    exact this

/-- The tail inequality in the reals. -/
theorem tail_real {K beta rho tail : ℕ} (h1 : beta < 2 ^ K)
    (h2 : beta ^ 3 * rho ≤ tail * ((2 ^ K - beta) * 2 ^ (2 * K))) :
    ((beta : ℝ) / 2 ^ K) ^ (2 + 1) * ((rho : ℝ) / 2 ^ K) / (1 - (beta : ℝ) / 2 ^ K) ≤
      (tail : ℝ) / 2 ^ K := by
  have hx : (0 : ℝ) < 2 ^ K := by positivity
  have hb : (beta : ℝ) < 2 ^ K := by exact_mod_cast h1
  have key : (beta : ℝ) ^ 3 * rho ≤ tail * ((2 ^ K - beta) * (2 ^ K) ^ 2) := by
    have := (Nat.cast_le (α := ℝ)).mpr h2
    push_cast [Nat.cast_sub h1.le] at this
    have e : (2 : ℝ) ^ (2 * K) = (2 ^ K) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e] at this
    exact this
  have hd : (0 : ℝ) < 2 ^ K - beta := by linarith
  have e : ((beta : ℝ) / 2 ^ K) ^ (2 + 1) * ((rho : ℝ) / 2 ^ K) / (1 - (beta : ℝ) / 2 ^ K) =
      (beta : ℝ) ^ 3 * rho / ((2 ^ K) ^ 3 * (2 ^ K - beta)) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) hx]
  nlinarith [pow_pos hx 3, pow_pos hx 2]

/-- **Soundness of the kernel checker.** If `c.Valid`, every real `A0` in the
interval matrix `[epsLo, epsHi] / 2^SE` is invertible and its inverse lies
entrywise in the claimed enclosure `[outLo, outHi] / 2^SO`. -/
theorem sound (h : c.Valid) (A0 : Matrix (Fin c.n) (Fin c.n) ℝ)
    (hA : ∀ i j, A0 i j ∈ Set.Icc (c.mat c.SE c.epsLo i j) (c.mat c.SE c.epsHi i j)) :
    IsUnit A0 ∧ ∀ i j, A0⁻¹ i j ∈ Set.Icc (c.mat c.SO c.outLo i j) (c.mat c.SO c.outHi i j) := by
  obtain ⟨hg, hrows⟩ := h
  simp only [chkGlobal, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hmid⟩, hrad⟩, hR⟩, hRabs⟩, hol⟩, hoh⟩, hF⟩, hT0⟩, hT1⟩,
    hT2⟩, hf⟩, hfG⟩, hcolA⟩, hb1⟩, htail⟩ := hg
  have hG : ∀ k < c.n, c.f.getD k 0 ≤ c.G := fun k hk =>
    hfG _ (getD_mem_of_lt 0 (by rw [hf]; exact hk))
  obtain ⟨hcolL, hcol'⟩ := all2_spec _ 0 0 _ _ hcolA
  rw [comb_row_length _ hmid] at hcolL
  have hcol : ∀ j < c.n, c.colM.getD j 0 = ∑ k ∈ range c.n, ent c.mid2 k j := fun j hj => by
    have := hcol' j (by rw [hcolL]; exact hj)
    rw [beq_iff_eq, comb_row (List.length_replicate) hmid] at this
    rw [this]
    exact sum_congr rfl fun k hk => by rw [getD_replicate _ _ (mem_range.mp hk), one_mul]
  have hrow := fun i (hi : i < c.n) =>
    row_spec hlo hhi hmid hrad hR hol hoh hT0 hT1 hT2 hF hf hi (hrows i hi).2.2.2.2
  have henc := fun k hk => (hrow k hk).1
  have habs := fun i hi => (hrow i hi).2.1
  -- the Neumann data
  set Rm := c.mat c.SR c.R
  set Fm := c.matN c.K c.F
  set β : ℝ := (c.beta : ℝ) / 2 ^ c.K
  set ρ : ℝ := (c.rho : ℝ) / 2 ^ c.K
  set T : ℕ → Matrix (Fin c.n) (Fin c.n) ℝ := fun k =>
    if k = 0 then c.matN c.K c.T0 else if k = 1 then c.matN c.K c.T1 else c.matN c.K c.T2
  set tl : ℝ := (c.tail : ℝ) / 2 ^ c.K
  set Sm : Matrix (Fin c.n) (Fin c.n) ℝ := Matrix.of fun i j => ∑ k ∈ range (2 + 1), T k i j
  set B : Matrix (Fin c.n) (Fin c.n) ℝ := Matrix.of fun i j => Sm i j + tl
  have hK : (0 : ℝ) < 2 ^ c.K := by positivity
  have hdomE := dom_E hR hRabs hmid hrad hF hf hG hcolL hcol henc habs
    (fun i hi => (hrows i hi).1) A0 hA
  have hβ : GW.Endpoint.Cert.RowLe Fm β := fun i => by
    have := (Nat.cast_le (α := ℝ)).mpr (hrow i i.2).2.2.1
    push_cast at this
    simp only [Fm, matN, Matrix.of_apply]
    rw [sum_fin c.n (fun j => ((ent c.F i j : ℕ) : ℝ) / 2 ^ c.K), ← Finset.sum_div]
    exact div_le_div_of_nonneg_right this hK.le
  have hβ1 : β < 1 := by
    rw [div_lt_one hK]; exact_mod_cast hb1
  have hRabsM : GW.Endpoint.Cert.absM Rm = c.matN c.SR c.Rabs := by
    ext i j
    simp only [GW.Endpoint.Cert.absM, Rm, mat, matN, Matrix.of_apply, abs_div,
      abs_of_pos (show (0 : ℝ) < 2 ^ c.SR by positivity)]
    rw [← habs i i.2 j j.2, Nat.cast_natAbs, Int.cast_abs]
  have hP : ∀ i j, (Fm * GW.Endpoint.Cert.absM Rm) i j ≤ c.matN c.K c.T0 i j := by
    rw [hRabsM]; exact mul_le hF hRabs hT0 fun i hi => (hrows i hi).2.1
  have hρ : GW.Endpoint.Cert.RowLe (c.matN c.K c.T0) ρ := fun i => by
    have := (Nat.cast_le (α := ℝ)).mpr (hrow i i.2).2.2.2.1
    push_cast at this
    simp only [matN, Matrix.of_apply]
    rw [sum_fin c.n (fun j => ((ent c.T0 i j : ℕ) : ℝ) / 2 ^ c.K), ← Finset.sum_div]
    exact div_le_div_of_nonneg_right this hK.le
  have hT : ∀ k < 2, ∀ i j, (Fm * T k) i j ≤ T (k + 1) i j := by
    intro k hk i j
    rcases k with _ | _ | k
    · exact mul_le hF hT0 hT1 (fun i hi => (hrows i hi).2.2.1) i j
    · exact mul_le hF hT1 hT2 (fun i hi => (hrows i hi).2.2.2.1) i j
    · omega
  have hd0 : (0 : ℝ) < 1 - β := by linarith
  obtain ⟨hU, hmem⟩ := GW.Endpoint.Cert.inverse_cw_sound
    (GW.Endpoint.Cert.balance c.sv A0) Rm Fm (c.matN c.K c.T0) β ρ hdomE hβ hβ1 hP hρ 2 T
    (fun i j => le_rfl) hT Sm (fun i j => le_rfl) (β ^ (2 + 1)) le_rfl (1 - β) hd0 le_rfl tl
    (tail_real hb1 htail) B (fun i j => le_rfl)
  have hs : ∀ i, 0 < c.sv i := fun i => by simp only [sv]; positivity
  have hdetB : IsUnit (GW.Endpoint.Cert.balance c.sv A0).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hdetA : IsUnit A0.det := by
    rwa [GW.Endpoint.Cert.det_balance c.sv (fun i => (hs i).ne')] at hdetB
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hdetA, fun i j => ?_⟩
  have hij := GW.Endpoint.Cert.inv_mem_of_balanced c.sv hs A0 hdetB (hmem i j)
  have hout := (hrow i i.2).2.2.2.2 j j.2
  simp only [outOK, Bool.and_eq_true, decide_eq_true_eq] at hout
  obtain ⟨ho1, ho2⟩ := hout
  simp only [Int.ofNat_eq_coe] at ho1 ho2
  have ho1r := (Int.cast_le (R := ℝ)).mpr ho1
  have ho2r := (Int.cast_le (R := ℝ)).mpr ho2
  push_cast at ho1r ho2r
  have hBij : B i j = (((ent c.T0 i j : ℕ) : ℝ) + (((ent c.T1 i j : ℕ) : ℝ) + ((ent c.T2 i j : ℕ) : ℝ)) +
      (c.tail : ℝ)) / 2 ^ c.K := by
    simp only [B, Sm, T, tl, Matrix.of_apply, sum_range_succ, sum_range_zero, matN]
    simp
    ring
  have hsij : c.sv i / c.sv j = 2 ^ c.f.getD i 0 / 2 ^ c.f.getD j 0 := rfl
  rw [hBij, hsij] at hij
  simp only [Rm, mat, Matrix.of_apply] at hij
  simp only [mat, Matrix.of_apply]
  simp only [pow_add] at ho1r ho2r
  generalize (((ent c.T0 i j : ℕ) : ℝ) + (((ent c.T1 i j : ℕ) : ℝ) + ((ent c.T2 i j : ℕ) : ℝ)) +
      (c.tail : ℝ)) = b at hij ho1r ho2r
  generalize ((ent c.R i j : ℤ) : ℝ) = r at hij ho1r ho2r
  generalize ((ent c.outLo (i : ℕ) (j : ℕ) : ℤ) : ℝ) = lo at hij ho1r ho2r ⊢
  generalize ((ent c.outHi i j : ℤ) : ℝ) = hi at hij ho1r ho2r ⊢
  have hpos : (0 : ℝ) < 2 ^ c.SO := by positivity
  have hSR : (0 : ℝ) < 2 ^ c.SR := by positivity
  have hfj : (0 : ℝ) < 2 ^ c.f.getD j 0 := by positivity
  have hfi : (0 : ℝ) < 2 ^ c.f.getD i 0 := by positivity
  generalize (2 : ℝ) ^ c.f.getD i 0 = xi at hij ho1r ho2r hfi
  generalize (2 : ℝ) ^ c.f.getD j 0 = xj at hij ho1r ho2r hfj
  generalize (2 : ℝ) ^ c.SO = xo at hij ho1r ho2r hpos ⊢
  generalize (2 : ℝ) ^ c.SR = xr at hij ho1r ho2r hSR
  generalize (2 : ℝ) ^ c.K = xk at hij ho1r ho2r hK
  constructor
  · refine le_trans ?_ hij.1
    rw [div_le_iff₀ hpos]
    have e : (r / xr - b / xk) * (xi / xj) * xo = (r * xk - b * xr) * (xo * xi) / (xr * xk * xj) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · refine le_trans hij.2 ?_
    rw [le_div_iff₀ hpos]
    have e : (r / xr + b / xk) * (xi / xj) * xo = (r * xk + b * xr) * (xo * xi) / (xr * xk * xj) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    linarith

end Cert

end GW.Endpoint.Kernel

/-
A3(a): the general two-body interaction and its commutators with the fermion
operators.

Index convention (spin-orbitals, real):

  V = ½ Σ_{pqrs} v_pqrs c_p† c_q† c_s c_r,

so `v_pqrs = ⟨pq|rs⟩` in physicists' notation (electron 1: p → r, electron 2:
q → s). Standing symmetry assumptions, carried as explicit hypotheses:

* `hv1 : v p q r s = v q p s r` (the two electrons are interchangeable), and
* `hv2 : v p q r s = v r s p q` (`V` is a real symmetric matrix, `vop_transpose`).

The antisymmetrized integral is `⟨pq||rs⟩ = asym v p q r s = v_pqrs - v_pqsr`.
No reality of orbitals (`v_pqrs = v_rqps`) is assumed.

Proved operator identities:
* `vop_mul_cre`   : `[V, c_t†] = ½ Σ_{ijl} ⟨ij||tl⟩ c_i† c_j† c_l`   (no hypothesis);
* `ann_mul_vop`   : `[c_t, V] = ½ Σ_{jkl} ⟨tj||kl⟩ c_j† c_l c_k`      (uses `hv1`);
* `ann_ccre`      : `{c_p, [V, c_q†]} = Σ_{jl} ⟨pj||ql⟩ c_j† c_l`   (uses `hv1`);
* `vop_isEig_num` : `V` conserves the particle number.
-/
import GW.Endpoint.ManyBody.Slater

namespace GW.Endpoint.ManyBody

open Matrix Finset

variable {n : ℕ}

/-! ### Sums of matrices acting on vectors -/

theorem sum_mulVec' {ι α : Type*} [Fintype α] (s : Finset ι) (M : ι → Matrix α α ℝ)
    (x : α → ℝ) : (∑ i ∈ s, M i) *ᵥ x = ∑ i ∈ s, M i *ᵥ x :=
  map_sum (AddMonoidHom.mk' (fun M : Matrix α α ℝ => M *ᵥ x) (fun M N => add_mulVec M N x)) M s

theorem mulVec_sum' {ι α : Type*} [Fintype α] (s : Finset ι) (M : Matrix α α ℝ)
    (x : ι → α → ℝ) : M *ᵥ (∑ i ∈ s, x i) = ∑ i ∈ s, M *ᵥ x i :=
  map_sum (AddMonoidHom.mk' (fun y : α → ℝ => M *ᵥ y) (fun y z => mulVec_add M y z)) x s

theorem dot_sum' {ι α : Type*} [Fintype α] (s : Finset ι) (x : α → ℝ) (y : ι → α → ℝ) :
    x ⬝ᵥ (∑ i ∈ s, y i) = ∑ i ∈ s, x ⬝ᵥ y i :=
  map_sum (AddMonoidHom.mk' (fun z : α → ℝ => x ⬝ᵥ z) (fun y z => dotProduct_add x y z)) y s

theorem sum_dot' {ι α : Type*} [Fintype α] (s : Finset ι) (x : ι → α → ℝ) (y : α → ℝ) :
    (∑ i ∈ s, x i) ⬝ᵥ y = ∑ i ∈ s, x i ⬝ᵥ y :=
  map_sum (AddMonoidHom.mk' (fun z : α → ℝ => z ⬝ᵥ y) (fun y z => add_dotProduct y z _)) x s

/-! ### Two ring identities (noncommutative, no hypotheses beyond those stated) -/

theorem quartic_comm_right {R : Type*} [Ring R] (ci cj cs cr ct d d' : R)
    (h1 : cr * ct + ct * cr = d) (h2 : cs * ct + ct * cs = d')
    (h3 : ct * ci + ci * ct = 0) (h4 : ct * cj + cj * ct = 0) :
    ci * cj * cs * cr * ct - ct * (ci * cj * cs * cr) = ci * cj * cs * d - ci * cj * d' * cr := by
  have e : ci * cj * cs * cr * ct - ct * (ci * cj * cs * cr) - (ci * cj * cs * d - ci * cj * d' * cr)
      = ci * cj * cs * (cr * ct + ct * cr - d) - ci * cj * (cs * ct + ct * cs - d') * cr
        - (ct * ci + ci * ct) * cj * cs * cr + ci * (ct * cj + cj * ct) * cs * cr := by
    noncomm_ring
  rw [h1, h2, h3, h4] at e
  simpa [sub_eq_zero] using e

theorem quartic_comm_left {R : Type*} [Ring R] (ci cj cs cr ct d d' : R)
    (h1 : ct * ci + ci * ct = d) (h2 : ct * cj + cj * ct = d')
    (h3 : ct * cs + cs * ct = 0) (h4 : ct * cr + cr * ct = 0) :
    ct * (ci * cj * cs * cr) - ci * cj * cs * cr * ct = d * cj * cs * cr - ci * d' * cs * cr := by
  have e : ct * (ci * cj * cs * cr) - ci * cj * cs * cr * ct - (d * cj * cs * cr - ci * d' * cs * cr)
      = (ct * ci + ci * ct - d) * cj * cs * cr - ci * (ct * cj + cj * ct - d') * cs * cr
        + ci * cj * (ct * cs + cs * ct) * cr - ci * cj * cs * (ct * cr + cr * ct) := by
    noncomm_ring
  rw [h1, h2, h3, h4] at e
  simpa [sub_eq_zero] using e

theorem cubic_anticomm {R : Type*} [Ring R] (ci cj cl cp d d' : R)
    (h1 : cp * ci + ci * cp = d) (h2 : cp * cj + cj * cp = d') (h3 : cp * cl + cl * cp = 0) :
    cp * (ci * cj * cl) + ci * cj * cl * cp = d * cj * cl - ci * d' * cl := by
  have e : cp * (ci * cj * cl) + ci * cj * cl * cp - (d * cj * cl - ci * d' * cl)
      = (cp * ci + ci * cp - d) * cj * cl - ci * (cp * cj + cj * cp - d') * cl
        + ci * cj * (cp * cl + cl * cp) := by
    noncomm_ring
  rw [h1, h2, h3] at e
  simpa [sub_eq_zero] using e

/-! ### The interaction -/

/-- `⟨pq||rs⟩ = v_pqrs - v_pqsr`. -/
def asym (v : Fin n → Fin n → Fin n → Fin n → ℝ) (p q r s : Fin n) : ℝ :=
  v p q r s - v p q s r

/-- `V = ½ Σ v_pqrs c_p† c_q† c_s c_r`. -/
noncomputable def vop (v : Fin n → Fin n → Fin n → Fin n → ℝ) : Matrix (Fock n) (Fock n) ℝ :=
  (2⁻¹ : ℝ) • ∑ p, ∑ q, ∑ r, ∑ s, v p q r s • (cre p * cre q * ann s * ann r)

/-- `[V, c_t†] = ½ Σ_{ijl} ⟨ij||tl⟩ c_i† c_j† c_l`. -/
noncomputable def ccre (v : Fin n → Fin n → Fin n → Fin n → ℝ) (t : Fin n) : Matrix (Fock n) (Fock n) ℝ :=
  (2⁻¹ : ℝ) • ∑ i, ∑ j, ∑ l, asym v i j t l • (cre i * cre j * ann l)

/-- `[c_t, V] = ½ Σ_{jkl} ⟨tj||kl⟩ c_j† c_l c_k`. -/
noncomputable def cann (v : Fin n → Fin n → Fin n → Fin n → ℝ) (t : Fin n) : Matrix (Fock n) (Fock n) ℝ :=
  (2⁻¹ : ℝ) • ∑ j, ∑ k, ∑ l, asym v t j k l • (cre j * ann l * ann k)

/-- `{c_p, [V, c_q†]} = Σ_{jl} ⟨pj||ql⟩ c_j† c_l`. -/
noncomputable def fop (v : Fin n → Fin n → Fin n → Fin n → ℝ) (p q : Fin n) : Matrix (Fock n) (Fock n) ℝ :=
  ∑ j, ∑ l, asym v p j q l • (cre j * ann l)

variable (v : Fin n → Fin n → Fin n → Fin n → ℝ)

theorem ann_cre_add' (r t : Fin n) :
    ann r * cre t + cre t * ann r = if r = t then 1 else 0 := ann_mul_cre_add r t

theorem cre_cre_add' (p q : Fin n) : cre p * cre q + cre q * cre p = 0 := cre_mul_cre_add p q

theorem ann_ann_add' (p q : Fin n) : ann p * ann q + ann q * ann p = 0 := ann_mul_ann_add p q

/-- Per-term commutator with `c_t†`. -/
theorem term_comm_cre (i j s r t : Fin n) :
    cre i * cre j * ann s * ann r * cre t - cre t * (cre i * cre j * ann s * ann r) =
      (if r = t then cre i * cre j * ann s else 0) - (if s = t then cre i * cre j * ann r else 0) := by
  rw [quartic_comm_right _ _ _ _ _ _ _ (ann_cre_add' r t) (ann_cre_add' s t) (cre_cre_add' t i)
    (cre_cre_add' t j)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- `[V, c_t†] = ½ Σ ⟨ij||tl⟩ c_i† c_j† c_l`. -/
theorem vop_mul_cre (t : Fin n) : vop v * cre t - cre t * vop v = ccre v t := by
  have e : ∀ p q r s, v p q r s • (cre p * cre q * ann s * ann r) * cre t -
      cre t * (v p q r s • (cre p * cre q * ann s * ann r)) =
      (if r = t then v p q t s • (cre p * cre q * ann s) else 0) -
        (if s = t then v p q r t • (cre p * cre q * ann r) else 0) := by
    intro p q r s
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, term_comm_cre, smul_sub]
    congr 1 <;> split_ifs with h <;> simp [h]
  have h1 : vop v * cre t - cre t * vop v = (2⁻¹ : ℝ) • ∑ p, ∑ q, ∑ r, ∑ s,
      (v p q r s • (cre p * cre q * ann s * ann r) * cre t -
        cre t * (v p q r s • (cre p * cre q * ann s * ann r))) := by
    simp only [vop, smul_mul_assoc, mul_smul_comm, sum_mul, mul_sum, sum_sub_distrib, smul_sub]
  rw [h1]
  simp only [e, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, if_true,
    ccre, asym, sub_smul]

/-- Per-term commutator with `c_t`. -/
theorem term_comm_ann (i j s r t : Fin n) :
    ann t * (cre i * cre j * ann s * ann r) - cre i * cre j * ann s * ann r * ann t =
      (if t = i then cre j * ann s * ann r else 0) - (if t = j then cre i * ann s * ann r else 0) := by
  rw [quartic_comm_left _ _ _ _ _ _ _ (ann_cre_add' t i) (ann_cre_add' t j) (ann_ann_add' t s)
    (ann_ann_add' t r)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- `[c_t, V] = ½ Σ ⟨tj||kl⟩ c_j† c_l c_k` (uses the particle-exchange symmetry). -/
theorem ann_mul_vop (hv1 : ∀ p q r s, v p q r s = v q p s r) (t : Fin n) :
    ann t * vop v - vop v * ann t = cann v t := by
  have e : ∀ p q r s, ann t * (v p q r s • (cre p * cre q * ann s * ann r)) -
      v p q r s • (cre p * cre q * ann s * ann r) * ann t =
      (if t = p then v t q r s • (cre q * ann s * ann r) else 0) -
        (if t = q then v p t r s • (cre p * ann s * ann r) else 0) := by
    intro p q r s
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, term_comm_ann, smul_sub]
    congr 1 <;> split_ifs with h <;> simp [h]
  have h1 : ann t * vop v - vop v * ann t = (2⁻¹ : ℝ) • ∑ p, ∑ q, ∑ r, ∑ s,
      (ann t * (v p q r s • (cre p * cre q * ann s * ann r)) -
        v p q r s • (cre p * cre q * ann s * ann r) * ann t) := by
    simp only [vop, smul_mul_assoc, mul_smul_comm, sum_mul, mul_sum, sum_sub_distrib, smul_sub]
  rw [h1]
  simp only [e, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true,
    cann, asym, sub_smul]
  simp_rw [hv1 _ t]

theorem asym_swap12 (hv1 : ∀ p q r s, v p q r s = v q p s r) (i p q l : Fin n) :
    asym v i p q l = -asym v p i q l := by
  unfold asym; rw [hv1 i p q l, hv1 i p l q]; ring

theorem asym_swap34 (p q r s : Fin n) : asym v p q r s = -asym v p q s r := by
  unfold asym; ring

/-- `⟨pq||rs⟩ = ⟨rs||pq⟩` from both symmetries. -/
theorem asym_herm (hv1 : ∀ p q r s, v p q r s = v q p s r) (hv2 : ∀ p q r s, v p q r s = v r s p q)
    (p q r s : Fin n) : asym v p q r s = asym v r s p q := by
  unfold asym; rw [hv2 p q r s, hv2 p q s r, hv1 s r p q]

/-- Per-term anticommutator of `c_p` with `c_i† c_j† c_l`. -/
theorem term_anticomm (p i j l : Fin n) :
    ann p * (cre i * cre j * ann l) + cre i * cre j * ann l * ann p =
      (if p = i then cre j * ann l else 0) - (if p = j then cre i * ann l else 0) := by
  rw [cubic_anticomm _ _ _ _ _ _ (ann_cre_add' p i) (ann_cre_add' p j) (ann_ann_add' p l)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- `{c_p, [V, c_q†]} = Σ_{jl} ⟨pj||ql⟩ c_j† c_l`. -/
theorem ann_ccre (hv1 : ∀ p q r s, v p q r s = v q p s r) (p q : Fin n) :
    ann p * ccre v q + ccre v q * ann p = fop v p q := by
  have e : ∀ i j l, ann p * (asym v i j q l • (cre i * cre j * ann l)) +
      asym v i j q l • (cre i * cre j * ann l) * ann p =
      (if p = i then asym v p j q l • (cre j * ann l) else 0) -
        (if p = j then asym v i p q l • (cre i * ann l) else 0) := by
    intro i j l
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, term_anticomm, smul_sub]
    congr 1 <;> split_ifs with h <;> simp [h]
  have h1 : ann p * ccre v q + ccre v q * ann p = (2⁻¹ : ℝ) • ∑ i, ∑ j, ∑ l,
      (ann p * (asym v i j q l • (cre i * cre j * ann l)) +
        asym v i j q l • (cre i * cre j * ann l) * ann p) := by
    simp only [ccre, smul_mul_assoc, mul_smul_comm, sum_mul, mul_sum, sum_add_distrib, smul_add]
  rw [h1]
  simp only [e, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true]
  simp_rw [asym_swap12 v hv1 _ p, neg_smul, sum_neg_distrib, sub_neg_eq_add]
  rw [← two_smul ℝ, smul_smul]; norm_num [fop]

theorem quartic_transpose (p q r s : Fin n) :
    (cre p * cre q * ann s * ann r)ᵀ = cre r * cre s * ann q * ann p := by
  simp only [transpose_mul, cre_transpose, ann_transpose, mul_assoc]

theorem sum4_swap {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ p, ∑ q, ∑ r, ∑ s, F p q r s = ∑ r, ∑ s, ∑ p, ∑ q, F p q r s := by
  calc ∑ p, ∑ q, ∑ r, ∑ s, F p q r s = ∑ p, ∑ r, ∑ q, ∑ s, F p q r s := by
        congr 1; funext p; exact sum_comm
    _ = ∑ r, ∑ p, ∑ q, ∑ s, F p q r s := sum_comm
    _ = ∑ r, ∑ p, ∑ s, ∑ q, F p q r s := by
        congr 1; funext r; congr 1; funext p; exact sum_comm
    _ = ∑ r, ∑ s, ∑ p, ∑ q, F p q r s := by congr 1; funext r; exact sum_comm

/-- `V` is symmetric (hermitian) when `v_pqrs = v_rspq`. -/
theorem vop_transpose (hv2 : ∀ p q r s, v p q r s = v r s p q) : (vop v)ᵀ = vop v := by
  unfold vop
  rw [transpose_smul, transpose_sum]
  congr 1
  simp only [transpose_sum, transpose_smul, quartic_transpose]
  rw [sum4_swap]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  rw [hv2]

theorem IsEig.congr {ε : Fin n → ℝ} {e e' : ℝ} {x : Fock n → ℝ} (h : IsEig ε e x) (he : e = e') :
    IsEig ε e' x := he ▸ h

/-- The interaction conserves the particle number. -/
theorem vop_isEig_num {k : ℝ} {x : Fock n → ℝ} (hx : IsEig (fun _ => 1) k x) :
    IsEig (fun _ => 1) k (vop v *ᵥ x) := by
  unfold vop
  rw [smul_mulVec_assoc]
  refine IsEig.smul ?_ _
  rw [sum_mulVec']
  refine IsEig.sum _ fun p _ => ?_
  rw [sum_mulVec']
  refine IsEig.sum _ fun q _ => ?_
  rw [sum_mulVec']
  refine IsEig.sum _ fun r _ => ?_
  rw [sum_mulVec']
  refine IsEig.sum _ fun s _ => ?_
  rw [smul_mulVec_assoc]
  refine IsEig.smul ?_ _
  simp only [← mulVec_mulVec]
  exact ((((hx.ann r).ann s).cre q).cre p).congr (by ring)

end GW.Endpoint.ManyBody

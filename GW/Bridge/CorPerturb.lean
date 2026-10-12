/-
R28-F3: a genuine tolerance statement for the BRIDGE-COR all-band enclosure.

**What `Cor.lean` does not cover (review finding F3).** `CompleteK κ` asks the STORED
dyadic computed rows `R` plus completion rows `C` to resolve `κ · 1`. For `κ > λ_max(RᵀR)`
the defect `κ·1 - RᵀR` has full rank `L`, so `C` needs at least `L` rows, while the
physical omitted bands of an `L`-dimensional basis are `L - N_b` rows. The true
finite-basis eigenvectors are therefore never an instance (`R = [1, 0]`, `κ = 1 + 2^-40`).

**What this file proves.** The stored rows are within an explicit distance of exactly
orthonormal rows, and the enclosure holds for every exactly orthonormal completion of
those, with an explicit propagation term.

* `Lowdin.lowdin_nat` (`CorPerturbLowdin.lean`): at each `q_t`, for the stored rows `R`
  (`Rst`) with Gram defect `η_t = ‖R Rᵀ - 1‖_F² < 1` (`gramDef`), there EXIST exactly
  orthonormal rows `P` with `‖P - R‖_F² ≤ η_t` (the proof uses Löwdin's
  `R* = (R Rᵀ)^{-1/2} R`; the statement does not pin `P` to it). Each row is then within
  `δ_t = √η_t`.
* `Lowdin.exists_completion_nat`: `P` is completed by exactly `L - N_b` rows to a resolution
  of the identity (`CompleteP`, `κ = 1`), with any prescribed omitted energies
  (`exists_compl`).
* For ANY real rows `P` within `d_t` of the stored rows (row-wise, `RowDist`) and ANY
  completion `cp` of `P` with `CompleteP` (`κ = 1`), the all-band Σ of the system with
  computed eigenvectors `P` (`SigAallP`, `SigTallP`: the spec's/theory's formula with `P` in
  place of the stored rows on the computed bands, plus `cp` on the omitted bands) satisfies
  `sigA_all_bands_true`, `sigA_diff_all_bands_true`, `sigT_all_bands_true`,
  `sigT_diff_all_bands_true`. These have the centre `cenK … 1` of `Cor.lean` at `κ = 1` on the
  STORED data, and the radius `radP` (Cor's radius with `T_ii` inflated to `T_ii + dT_ii`)
  plus the propagation terms `cenErr` and `compErr…`. All of them are computable from the
  stored data and `d`.
* `sigA_all_bands_lowdin`: the combination. If `η_t < 1` at every `q_t`, there exist
  exactly orthonormal rows `P` within `√η_t` of the stored rows. A completion of them by
  `L - N_b` rows exists, and every completion of that `P` obeys the enclosure with
  `d_t = √η_t`.

**The propagation term (explicit Lipschitz bound in the row data).** With `u_n(G) = M_n(G)`
the stored pair densities, `A_v(G)` the amplitudes of state `a`, and
`e(G) = √(Σ_v A_v(G)²) · d_t` (`eP`; `|M*_n(G) - M_n(G)| ≤ e(G)` by Cauchy-Schwarz,
`mP_close`), `πe(x, y; e_x, e_y) = e_x|y| + |x|e_y + e_x e_y` (`prodErr`) bounds
`|x*y* - xy|`. Then:

* `dT_ij = Σ_{n < N_b} πe(u_n(G_i), u_n(G_j); e_i, e_j)` bounds the change of the omitted
  pair sums `T_ij`.
* `cenErr = Σ |v_i| dT_ij |c_ji|`.
* `radP` replaces `√T_ii √T_jj` by `√(T_ii + dT_ii) √(T_jj + dT_jj)`.
* `compErr = Σ_{n < nocc} Σ_g |v^x_g| πe(u_n, u_n) + Σ_{n < N_b} Σ_{ij} |v_i| B_nji πe(u_i, u_j)`
  is the computed-band change, with `|K_nji| ≤ B_nji` on the computed-band kernels. For the
  spec `B = 751 |IeU|` is PROVED (`specKc_abs_le`: every branch of `schM`, `ssxM` is within
  `500 |IeU|`). For the theory kernel `B` is a hypothesis: `thK` is unbounded at its poles.

**Remaining trust.** That the rows `P` used here ARE the eigenvectors of the finite
Hamiltonian is not proved. `sigA_all_bands_lowdin` gives exactly orthonormal rows near the
stored ones, the eigenvectors of `H* = Σ_n E_n P_n P_nᵀ + Σ_n ε_n C_n C_nᵀ`, and covers the
completions of THOSE rows. The physical omitted bands complete the EPM Hamiltonian's own
eigenvectors instead. Covering them needs `sigA_all_bands_true` with the distance
hypothesis `RowDist P d` at the distance `d` between those eigenvectors and the stored
rows. That `d` would need `H` itself: a Davis-Kahan bound
`d ≤ ‖H Rᵀ - Rᵀ diag(E)‖_F / gap` (residual of the stored rows; gap from band `N_b` to
`N_b + 1`) is the computable quantity, and it is not formalised or evaluated here. Where
the cut splits an exact degeneracy (on Si-EPM at `N_b = 30` and `100`, gap ≈ 2e-15 Ry)
that gap is zero, and the bound must use the next nondegenerate gap. The state
`a` (rows at `k`) is the stored one throughout, the same input trust as E1. The omitted
energies enter only through `x ≤ -D`, a hypothesis as in `Cor.lean`.
-/
import GW.Bridge.Cor
import GW.Bridge.CorPerturbLowdin

namespace GW.Bridge

open Finset GW.Endpoint.Kernel.Sig GW.Endpoint.Kernel.Eps

/-! ### Real computed rows -/

section rows

variable (gl : Gl) (st : St)

/-- The sphere size at `q_t`. -/
def Lq (t : ℕ) : ℕ := (st.kq.getD t default).Gq.length

/-- The stored (dyadic) computed rows at `q_t`. -/
noncomputable def Rst (t n v : ℕ) : ℝ :=
  dy gl.SC (((st.kq.getD t default).cq.getD n []).getD v 0)

/-- `M_n(G)` of real computed rows `P t n`. -/
noncomputable def mP (P : ℕ → ℕ → ℕ → ℝ) (t a n : ℕ) (G : V3) : ℝ :=
  ∑ v ∈ range (Lq st t), amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq v G * P t n v

theorem mP_stored (t a n : ℕ) (G : V3) : mP gl st (Rst gl st) t a n G = xS gl st t a n G := by
  unfold mP xS Rst Lq; rw [pd_eq_amp]

/-- The real computed rows `P` plus the completion `cp` resolve the identity (`κ = 1`). -/
def CompleteP (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (t : ℕ) : Prop :=
  ∀ v < Lq st t, ∀ v' < Lq st t,
    ∑ n ∈ range (nbq st t), P t n v * P t n v' + ∑ n ∈ range (cp.K t), cp.C t n v * cp.C t n v' =
      if v = v' then 1 else 0

/-- The named hypothesis: the real rows `P` are within `d t` of the stored rows (a
distance bound, not an identification of `P`). -/
def RowDist (P : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ n < nbq st t, ∑ v ∈ range (Lq st t), (P t n v - Rst gl st t n v) ^ 2 ≤ d t ^ 2

/-- **Closure for real rows.** The omitted pair sums of a completion of `P`. -/
theorem tailP_eq (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (t a : ℕ) (G G' : V3)
    (hc : CompleteP st P cp t) :
    ∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' =
      cloP gl st t a G G' - ∑ n ∈ range (nbq st t), mP gl st P t a n G * mP gl st P t a n G' := by
  set L := (st.kq.getD t default).Gq.length
  set A := amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq
  have h1 : ∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' =
      ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' *
        ∑ n ∈ range (cp.K t), cp.C t n v * cp.C t n v' :=
    sum_prod_expand _ _ (cp.C t) _ _
  have h2 : ∑ n ∈ range (nbq st t), mP gl st P t a n G * mP gl st P t a n G' =
      ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' *
        ∑ n ∈ range (nbq st t), P t n v * P t n v' :=
    sum_prod_expand _ _ (P t) _ _
  have h3 : cloP gl st t a G G' = ∑ v ∈ range L, ∑ v' ∈ range L, A v G * A v' G' *
      (if v = v' then 1 else 0) := by
    unfold cloP
    refine sum_congr rfl fun v hv => ?_
    rw [sum_eq_single v (fun v' _ h => by rw [if_neg (Ne.symm h), mul_zero]) (fun h => absurd hv h),
      if_pos rfl, mul_one]
  rw [h1, h2, h3, ← sum_sub_distrib]
  refine sum_congr rfl fun v hv => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun v' hv' => ?_
  rw [← hc v (mem_range.mp hv) v' (mem_range.mp hv')]
  ring

/-- The bound `e(G) = √(Σ_v A_v(G)²) · d_t` on `|M*_n(G) - M_n(G)|`. -/
noncomputable def eP (d : ℕ → ℝ) (t a : ℕ) (G : V3) : ℝ := √(cloP gl st t a G G) * d t

/-- **Row perturbation → pair-density perturbation** (Cauchy-Schwarz). -/
theorem mP_close (P : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (t a n : ℕ) (G : V3) (hd : 0 ≤ d t)
    (hP : ∑ v ∈ range (Lq st t), (P t n v - Rst gl st t n v) ^ 2 ≤ d t ^ 2) :
    |mP gl st P t a n G - xS gl st t a n G| ≤ eP gl st d t a G := by
  set A := amp gl st.Gk (st.ck.getD a []) (st.kq.getD t default).Gq
  have e : mP gl st P t a n G - xS gl st t a n G =
      ∑ v ∈ range (Lq st t), A v G * (P t n v - Rst gl st t n v) := by
    rw [← mP_stored, mP, mP, ← sum_sub_distrib]
    exact sum_congr rfl fun v _ => by ring
  rw [e]
  have hsq : ∀ f : ℕ → ℝ, ∑ v ∈ range (Lq st t), |f v| ^ 2 = ∑ v ∈ range (Lq st t), f v * f v :=
    fun f => sum_congr rfl fun v _ => by rw [sq_abs, sq]
  calc _ ≤ ∑ v ∈ range (Lq st t), |A v G| * |P t n v - Rst gl st t n v| :=
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun v _ => abs_mul _ _))
    _ ≤ √(∑ v ∈ range (Lq st t), |A v G| ^ 2) *
          √(∑ v ∈ range (Lq st t), |P t n v - Rst gl st t n v| ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(cloP gl st t a G G) * d t := by
        rw [hsq, hsq]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [show ∑ v ∈ range (Lq st t), (P t n v - Rst gl st t n v) * (P t n v - Rst gl st t n v) =
          ∑ v ∈ range (Lq st t), (P t n v - Rst gl st t n v) ^ 2 from
          sum_congr rfl fun v _ => (sq _).symm]
        calc _ ≤ √(d t ^ 2) := Real.sqrt_le_sqrt hP
          _ = d t := Real.sqrt_sq hd
    _ = eP gl st d t a G := rfl

end rows

/-! ### Products and quadratic forms under perturbation -/

/-- `e_x |y| + |x| e_y + e_x e_y`, a bound on `|x' y' - x y|`. -/
noncomputable def prodErr (x y ex ey : ℝ) : ℝ := ex * |y| + |x| * ey + ex * ey

theorem prod_err {x y x' y' ex ey : ℝ} (hx : |x' - x| ≤ ex) (hy : |y' - y| ≤ ey) :
    |x' * y' - x * y| ≤ prodErr x y ex ey := by
  have e : x' * y' - x * y = (x' - x) * y + x * (y' - y) + (x' - x) * (y' - y) := by ring
  rw [e]
  have h0x : 0 ≤ ex := (abs_nonneg _).trans hx
  have h0y : 0 ≤ ey := (abs_nonneg _).trans hy
  calc _ ≤ |(x' - x) * y| + |x * (y' - y)| + |(x' - x) * (y' - y)| := abs_add_three _ _ _
    _ = |x' - x| * |y| + |x| * |y' - y| + |x' - x| * |y' - y| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ prodErr x y ex ey := by
        unfold prodErr
        gcongr

theorem prodErr_nonneg {x y ex ey : ℝ} (hx : 0 ≤ ex) (hy : 0 ≤ ey) : 0 ≤ prodErr x y ex ey := by
  unfold prodErr; positivity

section quadP

variable (gl : Gl)

/-- **Quadratic-form perturbation.** `|quadR u' F - quadR u F|` for `|u' - u| ≤ e`,
`|F| ≤ B`. -/
theorem quadR_perturb (vc : V3 → ℝ) (t : ℕ) (u u' e : V3 → ℝ) (F B : ℕ → ℕ → ℝ)
    (hu : ∀ G, |u' G - u G| ≤ e G) (hF : ∀ j < nG gl t, ∀ i < nG gl t, |F j i| ≤ B j i) :
    |quadR gl vc t u' F - quadR gl vc t u F| ≤
      ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
        |vS gl vc (gl.qs.getD t default) i| * B j i *
          prodErr (u (gs (gl.qs.getD t default) i)) (u (gs (gl.qs.getD t default) j))
            (e (gs (gl.qs.getD t default) i)) (e (gs (gl.qs.getD t default) j)) := by
  unfold quadR
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  set qd := gl.qs.getD t default
  have e1 : u' (gs qd i) * vS gl vc qd i * u' (gs qd j) * F j i -
      u (gs qd i) * vS gl vc qd i * u (gs qd j) * F j i =
      (u' (gs qd i) * u' (gs qd j) - u (gs qd i) * u (gs qd j)) * (vS gl vc qd i * F j i) := by ring
  rw [e1, abs_mul, abs_mul]
  have hp := prod_err (hu (gs qd i)) (hu (gs qd j))
  have hB := hF j (mem_range.mp hj) i (mem_range.mp hi)
  have h0 : 0 ≤ |u' (gs qd i) * u' (gs qd j) - u (gs qd i) * u (gs qd j)| := abs_nonneg _
  calc _ ≤ prodErr (u (gs qd i)) (u (gs qd j)) (e (gs qd i)) (e (gs qd j)) *
        (|vS gl vc qd i| * B j i) := by
          apply mul_le_mul hp (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (h0.trans hp)
    _ = _ := by ring

/-- The exchange of band `a` at `q_t` for pair densities `u n1 G`. -/
noncomputable def XqU (vc : V3 → ℝ) (t : ℕ) (u : ℕ → V3 → ℝ) : ℝ :=
  let qd := gl.qs.getD t default;
  -(∑ n1 ∈ range gl.nocc, ∑ g ∈ range qd.Gb.length,
    (u n1 (qd.Gb.getD g 0)) ^ 2 * (vc (key qd (qd.Gb.getD g 0)) / (Nq gl * vol gl)))

theorem XqU_stored (vc : V3 → ℝ) (st : St) (t a : ℕ) :
    XqU gl vc t (fun n G => xS gl st t a n G) = Xq gl vc st t a := rfl

/-- The exchange propagation term. -/
noncomputable def xErr (vc : V3 → ℝ) (t : ℕ) (u : ℕ → V3 → ℝ) (e : V3 → ℝ) : ℝ :=
  let qd := gl.qs.getD t default
  ∑ n1 ∈ range gl.nocc, ∑ g ∈ range qd.Gb.length,
    |vc (key qd (qd.Gb.getD g 0)) / (Nq gl * vol gl)| *
      prodErr (u n1 (qd.Gb.getD g 0)) (u n1 (qd.Gb.getD g 0)) (e (qd.Gb.getD g 0)) (e (qd.Gb.getD g 0))

theorem XqU_perturb (vc : V3 → ℝ) (t : ℕ) (u u' : ℕ → V3 → ℝ) (e : V3 → ℝ)
    (hu : ∀ n < gl.nocc, ∀ G, |u' n G - u n G| ≤ e G) :
    |XqU gl vc t u' - XqU gl vc t u| ≤ xErr gl vc t u e := by
  unfold XqU xErr
  dsimp only
  rw [neg_sub_neg, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun g _ => ?_)
  set qd := gl.qs.getD t default
  set G := qd.Gb.getD g 0
  have hu' := hu n (mem_range.mp hn) G
  have hp := prod_err hu' hu'
  rw [← sub_mul, abs_mul, abs_sub_comm, sq, sq, mul_comm]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)

end quadP

/-! ### The spec's computed-band kernel is bounded by `751 |IeU|` -/

theorem abs_div_le_of {a b c : ℝ} (hc : 0 ≤ c) (h : |a| ≤ c * |b|) : |a / b| ≤ c := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [hc]
  · rw [abs_div, div_le_iff₀ (abs_pos.mpr hb)]; exact h

theorem w_le_500 {w y : ℝ} (h : w ^ 2 < y ^ 2 * LIM1) : w ≤ 500 * |y| := by
  unfold LIM1 at h
  by_contra hc
  push_neg at hc
  have h0 : 0 ≤ 500 * |y| := by positivity
  have : (500 * |y|) ^ 2 < w ^ 2 := pow_lt_pow_left₀ hc h0 (by norm_num)
  rw [mul_pow, sq_abs] at this
  linarith

/-- The CH kernel of every mode, every `x`: `|schM| ≤ 500 |IeU|` (generic branch:
`w² < (x - w)² · 250000`). -/
theorem schM_abs_le (I O x : ℝ) : |schM I O x| ≤ 500 * |IeU I| := by
  unfold schM
  split_ifs with hk
  · have hw := wtM_pos hk
    dsimp only
    split_ifs with hg
    · apply abs_div_le_of (by positivity)
      rw [abs_mul, abs_of_pos hw]
      have := w_le_500 hg.2
      calc wtM I O * |IeU I| ≤ 500 * |x - wtM I O| * |IeU I| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = _ := by ring
    · simp only [abs_zero]; positivity
  · simp only [abs_zero]; positivity

/-- The SX kernel of every mode, every `x`: `|ssxM| ≤ 500 |IeU|` (every branch of
`certSsx`, `sexcut = 4`). -/
theorem ssxM_abs_le (I O x : ℝ) : |ssxM I O x| ≤ 500 * |IeU I| := by
  unfold ssxM
  split_ifs with hk
  · have hw := wtM_pos hk
    generalize IeU I = J
    generalize wtM I O = w at hw ⊢
    have hJ : 0 ≤ |J| := abs_nonneg J
    unfold GW.Endpoint.Cert.certSsx
    unfold SEXC
    split_ifs with h1 h2 h3 h4
    · simp only [abs_zero]; positivity
    · apply abs_div_le_of (by positivity)
      rw [abs_mul, abs_of_pos (by positivity : 0 < w ^ 2)]
      suffices key : w ^ 2 ≤ 500 * |x ^ 2 - w ^ 2| by
        nlinarith [mul_le_mul_of_nonneg_left key hJ]
      by_cases hx : x < 0
      · have : w ^ 2 * (1 / 4) ≤ |x ^ 2 - w ^ 2| := by
          exact le_of_not_lt fun hc => h2 ⟨hc, hx⟩
        nlinarith [abs_nonneg (x ^ 2 - w ^ 2)]
      · push_neg at hx
        have h5 := w_le_500 h1.2
        have e : |x ^ 2 - w ^ 2| = |x - w| * (x + w) := by
          rw [show x ^ 2 - w ^ 2 = (x - w) * (x + w) by ring, abs_mul,
            abs_of_pos (show (0 : ℝ) < x + w by linarith)]
        rw [e]
        nlinarith [abs_nonneg (x - w)]
    · simp only [abs_zero]; positivity
    · apply abs_div_le_of (by positivity)
      rw [abs_neg, abs_mul, abs_of_pos hw]
      suffices key : w ≤ 500 * |2 * (x + w)| by
        nlinarith [mul_le_mul_of_nonneg_left key hJ]
      by_cases hx : x < 0
      · have : w * (1 / 4) ≤ |2 * (x + w)| := by
          exact le_of_not_lt fun hc => h4 ⟨hc, hx⟩
        nlinarith [abs_nonneg (2 * (x + w))]
      · push_neg at hx
        rw [abs_of_pos (by linarith)]
        nlinarith
    · simp only [abs_zero]; positivity
  · simp only [abs_zero]; positivity

/-- The spec's whole computed-band kernel `ACq + Pq` per mode. -/
noncomputable def specKc (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)
    (t a n iw j i : ℕ) : ℝ :=
  IeU (Iq gl E vb oq t j i) / 4 +
    (1 / 2) * schM (Iq gl E vb oq t j i) (Oq gl vb t j i) (wxS gl st t a n iw) -
    (if n < gl.nocc then ssxM (Iq gl E vb oq t j i) (Oq gl vb t j i) (wxS gl st t a n iw) else 0)

theorem specKc_abs_le (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St)
    (t a n iw j i : ℕ) :
    |specKc gl E vb oq st t a n iw j i| ≤ 751 * |IeU (Iq gl E vb oq t j i)| := by
  unfold specKc
  set I := Iq gl E vb oq t j i
  have h1 := schM_abs_le I (Oq gl vb t j i) (wxS gl st t a n iw)
  have h2 := ssxM_abs_le I (Oq gl vb t j i) (wxS gl st t a n iw)
  have h3 : |(if n < gl.nocc then ssxM I (Oq gl vb t j i) (wxS gl st t a n iw) else 0)| ≤
      500 * |IeU I| := by
    split_ifs
    · exact h2
    · simp only [abs_zero]; positivity
  have h0 := abs_nonneg (IeU I)
  calc _ ≤ |IeU I / 4| + |(1 / 2) * schM I (Oq gl vb t j i) (wxS gl st t a n iw)| +
        |(if n < gl.nocc then ssxM I (Oq gl vb t j i) (wxS gl st t a n iw) else 0)| :=
        (abs_sub _ _).trans (by gcongr; exact abs_add _ _)
    _ ≤ |IeU I| / 4 + 1 / 2 * (500 * |IeU I|) + 500 * |IeU I| := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
    _ ≤ _ := by linarith

theorem acq_pq_eq (gl : Gl) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ) (st : St) (t a n iw : ℕ) :
    ACq gl E vb oq st t a n + Pq gl E vb oq st t a n iw =
      quad gl vb st t a n (specKc gl E vb oq st t a n iw) := by
  unfold ACq Pq specKc
  split_ifs with hn
  · simp only [quad, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  · simp only [quad, mul_sum, ← sum_add_distrib, sub_zero]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring

/-! ### The Σ of a system with real computed rows -/

section sigU

variable (gl : Gl)

/-- A Σ built from pair densities `u t n G`: exchange, a constant per `q_t`, and the
computed-band quadratic forms with kernels `K t n`. -/
noncomputable def SigU (vc : V3 → ℝ) (X0 : ℕ → ℝ) (nb : ℕ → ℕ) (u : ℕ → ℕ → V3 → ℝ)
    (K : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length,
    (XqU gl vc t (u t) + X0 t + ∑ n ∈ range (nb t), quadR gl vc t (u t n) (K t n))

/-- The computed-band propagation term. -/
noncomputable def compErrU (vc : V3 → ℝ) (nb : ℕ → ℕ) (u : ℕ → ℕ → V3 → ℝ) (e : ℕ → V3 → ℝ)
    (B : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, (xErr gl vc t (u t) (e t) +
    ∑ n ∈ range (nb t), ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
      |vS gl vc (gl.qs.getD t default) i| * B t n j i *
        prodErr (u t n (gs (gl.qs.getD t default) i)) (u t n (gs (gl.qs.getD t default) j))
          (e t (gs (gl.qs.getD t default) i)) (e t (gs (gl.qs.getD t default) j)))

theorem SigU_perturb (vc : V3 → ℝ) (X0 : ℕ → ℝ) (nb : ℕ → ℕ) (u u' : ℕ → ℕ → V3 → ℝ)
    (e : ℕ → V3 → ℝ) (K B : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nb t)
    (hu : ∀ t < gl.qs.length, ∀ n < nb t, ∀ G, |u' t n G - u t n G| ≤ e t G)
    (hK : ∀ t < gl.qs.length, ∀ n < nb t, ∀ j < nG gl t, ∀ i < nG gl t, |K t n j i| ≤ B t n j i) :
    |SigU gl vc X0 nb u' K - SigU gl vc X0 nb u K| ≤ compErrU gl vc nb u e B := by
  unfold SigU compErrU
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  have ht' := mem_range.mp ht
  have e1 : XqU gl vc t (u' t) + X0 t + ∑ n ∈ range (nb t), quadR gl vc t (u' t n) (K t n) -
      (XqU gl vc t (u t) + X0 t + ∑ n ∈ range (nb t), quadR gl vc t (u t n) (K t n)) =
      (XqU gl vc t (u' t) - XqU gl vc t (u t)) +
        ∑ n ∈ range (nb t), (quadR gl vc t (u' t n) (K t n) - quadR gl vc t (u t n) (K t n)) := by
    rw [sum_sub_distrib]; ring
  rw [e1]
  refine (abs_add _ _).trans (add_le_add ?_ ?_)
  · exact XqU_perturb gl vc t (u t) (u' t) (e t)
      fun n hn G => hu t ht' n (lt_of_lt_of_le hn (hocc t ht')) G
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    exact quadR_perturb gl vc t (u t n) (u' t n) (e t) (K t n) (B t n)
      (hu t ht' n (mem_range.mp hn)) (hK t ht' n (mem_range.mp hn))

end sigU

section truesys

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

/-- **The spec's Σ on the computed bands with real rows `P`** (stored energies, stored
state `a`). -/
noncomputable def SigAP (P : ℕ → ℕ → ℕ → ℝ) (a iw : ℕ) : ℝ :=
  SigU gl vb (fun t => CSq gl E vb oq st t a) (nbq st) (fun t n G => mP gl st P t a n G)
    (fun t n => specKc gl E vb oq st t a n iw)

theorem mP_stored_fun (a : ℕ) :
    (fun t n G => mP gl st (Rst gl st) t a n G) = (fun t n G => xS gl st t a n G) := by
  funext t n G; exact mP_stored gl st t a n G

theorem sigAP_stored (a iw : ℕ) : SigAP gl st E vb oq (Rst gl st) a iw = SigA gl E vb oq st a iw := by
  unfold SigAP
  rw [mP_stored_fun]
  unfold SigU SigA
  refine sum_congr rfl fun t _ => ?_
  rw [XqU_stored]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [acq_pq_eq]
  rfl

/-- **The spec's Σ with all bands of the system with computed rows `P` and omitted
bands `cp`.** -/
noncomputable def SigAallP (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (a iw : ℕ) : ℝ :=
  SigAP gl st E vb oq P a iw + tailS gl st E vb oq cp a iw

/-- The spec's computed-band propagation term (`B = 751 |IeU|`, `specKc_abs_le`). -/
noncomputable def compErrA (d : ℕ → ℝ) (a : ℕ) : ℝ :=
  compErrU gl vb (nbq st) (fun t n G => xS gl st t a n G) (fun t G => eP gl st d t a G)
    (fun t _ j i => 751 * |IeU (Iq gl E vb oq t j i)|)

end truesys

section truesysT

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ)

/-- The theory kernel of computed band `n`. -/
noncomputable def thKc (t a n iw j i : ℕ) : ℝ :=
  thK (decide (n < gl.nocc)) (ITq gl E t j i) (OTq gl vc t j i) (xT gl st t a n iw)

/-- **The theory Σ on the computed bands with real rows `P`.** -/
noncomputable def SigTP (P : ℕ → ℕ → ℕ → ℝ) (a iw : ℕ) : ℝ :=
  SigU gl vc (fun _ => 0) (nbq st) (fun t n G => mP gl st P t a n G)
    (fun t n => thKc gl st E vc t a n iw)

theorem sigTP_stored (a iw : ℕ) : SigTP gl st E vc (Rst gl st) a iw = SigT gl E vc st a iw := by
  unfold SigTP
  rw [mP_stored_fun]
  unfold SigU SigT
  refine sum_congr rfl fun t _ => ?_
  rw [XqU_stored, add_zero]
  rfl

/-- **The theory Σ with all bands of the system with computed rows `P` and omitted
bands `cp`.** -/
noncomputable def SigTallP (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (a iw : ℕ) : ℝ :=
  SigTP gl st E vc P a iw + tailT gl st E vc cp a iw

/-- The theory's computed-band propagation term, for a kernel bound `B`. -/
noncomputable def compErrT (d : ℕ → ℝ) (a : ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  compErrU gl vc (nbq st) (fun t n G => xS gl st t a n G) (fun t G => eP gl st d t a G) B

end truesysT

/-! ### The omitted-band tail for a completion of real rows -/

section tailP

variable (gl : Gl) (st : St)

/-- The bound on the change of the omitted pair sum `T(G, G')` (rows within `d`). -/
noncomputable def dT (d : ℕ → ℝ) (t a : ℕ) (G G' : V3) : ℝ :=
  ∑ n ∈ range (nbq st t),
    prodErr (xS gl st t a n G) (xS gl st t a n G') (eP gl st d t a G) (eP gl st d t a G')

/-- The radius of `Cor.radK` (`κ = 1`) with `T_ii` inflated to `T_ii + dT_ii`. -/
noncomputable def radP (vc : V3 → ℝ) (d : ℕ → ℝ) (a : ℕ) (r : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    |vS gl vc (gl.qs.getD t default) i| *
      (√(tailK gl st 1 t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) i) +
          dT gl st d t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) i)) *
        √(tailK gl st 1 t a (gs (gl.qs.getD t default) j) (gs (gl.qs.getD t default) j) +
          dT gl st d t a (gs (gl.qs.getD t default) j) (gs (gl.qs.getD t default) j))) * r t j i

/-- The change of the centre. -/
noncomputable def cenErr (vc : V3 → ℝ) (d : ℕ → ℝ) (a : ℕ) (c : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ range gl.qs.length, ∑ i ∈ range (nG gl t), ∑ j ∈ range (nG gl t),
    |vS gl vc (gl.qs.getD t default) i| *
      dT gl st d t a (gs (gl.qs.getD t default) i) (gs (gl.qs.getD t default) j) * |c t j i|

/-- The true omitted pair sum is within `dT` of the stored one (`κ = 1`). -/
theorem tailP_close (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (t a : ℕ) (G G' : V3)
    (hd : 0 ≤ d t) (hP : RowDist gl st P d t) (hc : CompleteP st P cp t) :
    |∑ n ∈ range (cp.K t), mR gl st cp t a n G * mR gl st cp t a n G' -
        tailK gl st 1 t a G G'| ≤ dT gl st d t a G G' := by
  rw [tailP_eq gl st P cp t a G G' hc, tailK, one_mul, parP,
    show ∀ X Y Z : ℝ, X - Y - (X - Z) = -(Y - Z) from fun _ _ _ => by ring, abs_neg,
    ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  exact prod_err (mP_close gl st P d t a n G hd (hP n (mem_range.mp hn)))
    (mP_close gl st P d t a n G' hd (hP n (mem_range.mp hn)))

/-- **The tail for a completion of real rows**, in terms of the stored data. -/
theorem tailP_sum (vc : V3 → ℝ) (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (a : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) (c r : ℕ → ℕ → ℕ → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hc : ∀ t < gl.qs.length, CompleteP st P cp t) (hr : ∀ t j i, 0 ≤ r t j i)
    (hF : ∀ t < gl.qs.length, ∀ n < cp.K t, ∀ j < nG gl t, ∀ i < nG gl t,
      |F t n j i - c t j i| ≤ r t j i) :
    |∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vc t (mR gl st cp t a n) (F t n) -
        cenK gl st vc 1 a c| ≤ radP gl st vc d a r + cenErr gl st vc d a c := by
  unfold cenK radP cenErr
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  have ht' := mem_range.mp ht
  set qd := gl.qs.getD t default
  set m := nG gl t
  set u : ℕ → ℕ → ℝ := fun n i => mR gl st cp t a n (gs qd i)
  set v : ℕ → ℝ := fun i => vS gl vc qd i
  set Ts : ℕ → ℕ → ℝ := fun i j => ∑ n ∈ range (cp.K t), u n i * u n j
  set T : ℕ → ℕ → ℝ := fun i j => tailK gl st 1 t a (gs qd i) (gs qd j)
  set δT : ℕ → ℕ → ℝ := fun i j => dT gl st d t a (gs qd i) (gs qd j)
  have hT : ∀ i j, |Ts i j - T i j| ≤ δT i j := fun i j =>
    tailP_close gl st P cp d t a (gs qd i) (gs qd j) (hd t) (hP t ht') (hc t ht')
  have hcore := tail_core m (cp.K t) u v (F t) (c t) (r t) (hr t) (hF t ht')
  change |∑ n ∈ range (cp.K t), ∑ i ∈ range m, ∑ j ∈ range m, u n i * v i * u n j * F t n j i -
      ∑ i ∈ range m, ∑ j ∈ range m, v i * T i j * c t j i| ≤
    ∑ i ∈ range m, ∑ j ∈ range m, |v i| * (√(T i i + δT i i) * √(T j j + δT j j)) * r t j i +
      ∑ i ∈ range m, ∑ j ∈ range m, |v i| * δT i j * |c t j i|
  have hrad : ∑ i ∈ range m, ∑ j ∈ range m, |v i| * (√(Ts i i) * √(Ts j j)) * r t j i ≤
      ∑ i ∈ range m, ∑ j ∈ range m, |v i| * (√(T i i + δT i i) * √(T j j + δT j j)) * r t j i := by
    have hs : ∀ i, √(Ts i i) ≤ √(T i i + δT i i) := fun i =>
      Real.sqrt_le_sqrt (by have := (abs_le.mp (hT i i)).2; linarith)
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    apply mul_le_mul_of_nonneg_right _ (hr t j i)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_mul (hs i) (hs j) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcen : |∑ i ∈ range m, ∑ j ∈ range m, v i * Ts i j * c t j i -
      ∑ i ∈ range m, ∑ j ∈ range m, v i * T i j * c t j i| ≤
      ∑ i ∈ range m, ∑ j ∈ range m, |v i| * δT i j * |c t j i| := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [show v i * Ts i j * c t j i - v i * T i j * c t j i = v i * (Ts i j - T i j) * c t j i by ring,
      abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (hT i j) (abs_nonneg _)
  calc _ ≤ |∑ n ∈ range (cp.K t), ∑ i ∈ range m, ∑ j ∈ range m, u n i * v i * u n j * F t n j i -
          ∑ i ∈ range m, ∑ j ∈ range m, v i * Ts i j * c t j i| +
        |∑ i ∈ range m, ∑ j ∈ range m, v i * Ts i j * c t j i -
          ∑ i ∈ range m, ∑ j ∈ range m, v i * T i j * c t j i| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (hcore.trans hrad) hcen

end tailP

/-! ### Main statements: the all-band Σ of a system with exactly orthonormal rows -/

section main

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

/-- The computed bands of the spec: `|SigAP P - SigA| ≤ compErrA`. -/
theorem sigAP_close (P : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (a iw : ℕ) (hd : ∀ t, 0 ≤ d t)
    (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t) :
    |SigAP gl st E vb oq P a iw - SigA gl E vb oq st a iw| ≤ compErrA gl st E vb oq d a := by
  rw [← sigAP_stored gl st E vb oq a iw]
  unfold SigAP compErrA
  rw [mP_stored_fun]
  exact SigU_perturb gl vb _ (nbq st) _ _ _ _ _ hocc
    (fun t ht n hn G => mP_close gl st P d t a n G (hd t) (hP t ht n hn))
    (fun t _ n _ j _ i _ => specKc_abs_le gl E vb oq st t a n iw j i)

/-- **The spec's Σ with all bands, for computed rows `P` within `d` of the stored rows and
ANY exactly orthonormal completion `cp` of `P`** (κ = 1). The centre is `Cor`'s at `κ = 1`
on the stored data. The radius is `radP`, Cor's radius with `T_ii` inflated by `dT_ii`.
The propagation is `cenErr + compErrA`. -/
theorem sigA_all_bands_true (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (a iw : ℕ)
    (D : ℕ → ℝ) (hd : ∀ t, 0 ≤ d t) (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t)
    (hc : ∀ t < gl.qs.length, CompleteP st P cp t) (hD : ∀ t, 1 / 2 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n iw ≤ -D t) :
    |SigAallP gl st E vb oq P cp a iw - SigA gl E vb oq st a iw -
        cenK gl st vb 1 a (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
      radP gl st vb d a (fun t j i => rS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
        cenErr gl st vb d a (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
        compErrA gl st E vb oq d a := by
  have h1 := sigAP_close gl st E vb oq P d a iw hd hP hocc
  have h2 := tailP_sum gl st vb P cp d a
    (fun t n j i => specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw))
    (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) (fun t j i => rS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) hd hP hc
    (fun t _ _ => rS_nonneg _ _ _ (by linarith [hD t]))
    (fun t ht n hn _ _ _ _ => specK_tail_mode (hD t) (hx t ht n hn))
  unfold SigAallP
  have e : ∀ A B S C : ℝ, A + B - S - C = (A - S) + (B - C) := fun _ _ _ _ => by ring
  rw [e]
  refine (abs_add _ _).trans ?_
  have : tailS gl st E vb oq cp a iw = ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t),
      quadR gl vb t (mR gl st cp t a n) (fun j i =>
        specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n iw)) := rfl
  rw [this]
  linarith

/-- **The spec's energy step with all bands**, same setting (`D > 3/2`). -/
theorem sigA_diff_all_bands_true (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (a : ℕ)
    (D : ℕ → ℝ) (hd : ∀ t, 0 ≤ d t) (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t)
    (hc : ∀ t < gl.qs.length, CompleteP st P cp t) (hD : ∀ t, 3 / 2 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n 0 ≤ -D t) :
    |(SigAallP gl st E vb oq P cp a 1 - SigAallP gl st E vb oq P cp a 0) -
        (SigA gl E vb oq st a 1 - SigA gl E vb oq st a 0) -
        cenK gl st vb 1 a (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
      radP gl st vb d a (fun t j i => rSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
        cenErr gl st vb d a (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
        2 * compErrA gl st E vb oq d a := by
  have h0 := sigAP_close gl st E vb oq P d a 0 hd hP hocc
  have h1 := sigAP_close gl st E vb oq P d a 1 hd hP hocc
  have h2 := tailP_sum gl st vb P cp d a
    (fun t n j i => specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0 + 1) - specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0))
    (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) (fun t j i => rSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) hd hP hc
    (fun t _ _ => rSd_nonneg _ _ _ (by linarith [hD t]))
    (fun t ht n hn _ _ _ _ => specK_diff_mode (hD t) (hx t ht n hn))
  have hq : tailS gl st E vb oq cp a 1 - tailS gl st E vb oq cp a 0 =
      ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vb t (mR gl st cp t a n) (fun j i =>
        specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0 + 1) -
          specK (Iq gl E vb oq t j i) (Oq gl vb t j i) (xR gl st cp t a n 0)) := by
    unfold tailS
    rw [← sum_sub_distrib]; refine sum_congr rfl fun t _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun n _ => ?_
    unfold quadR
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
    rw [xR_one]; ring
  unfold SigAallP
  have e : ∀ A1 B1 A0 B0 S1 S0 C : ℝ, (A1 + B1 - (A0 + B0)) - (S1 - S0) - C =
      (A1 - S1) - (A0 - S0) + ((B1 - B0) - C) := fun _ _ _ _ _ _ _ => by ring
  rw [e, hq]
  refine (abs_add _ _).trans ?_
  have := abs_sub (SigAP gl st E vb oq P a 1 - SigA gl E vb oq st a 1)
    (SigAP gl st E vb oq P a 0 - SigA gl E vb oq st a 0)
  linarith

end main

section mainT

variable (gl : Gl) (st : St) (E : ℕ → ℕ → ℕ → ℝ) (vc : V3 → ℝ)

theorem sigTP_close (P : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (a iw : ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t)
    (hB : ∀ t < gl.qs.length, ∀ n < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      |thKc gl st E vc t a n iw j i| ≤ B t n j i) :
    |SigTP gl st E vc P a iw - SigT gl E vc st a iw| ≤ compErrT gl st vc d a B := by
  rw [← sigTP_stored gl st E vc a iw]
  unfold SigTP compErrT
  rw [mP_stored_fun]
  exact SigU_perturb gl vc _ (nbq st) _ _ _ _ _ hocc
    (fun t ht n hn G => mP_close gl st P d t a n G (hd t) (hP t ht n hn)) hB

/-- **The theory Σ with all bands**, computed rows `P` within `d` of the stored rows, any
exactly orthonormal completion. `B` bounds the theory kernel on the computed bands (a
hypothesis: `thK` has poles). -/
theorem sigT_all_bands_true (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (a iw : ℕ)
    (D : ℕ → ℝ) (B : ℕ → ℕ → ℕ → ℕ → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t)
    (hB : ∀ t < gl.qs.length, ∀ n < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      |thKc gl st E vc t a n iw j i| ≤ B t n j i)
    (hc : ∀ t < gl.qs.length, CompleteP st P cp t) (hD : ∀ t, 0 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n iw ≤ -D t) :
    |SigTallP gl st E vc P cp a iw - SigT gl E vc st a iw -
        cenK gl st vc 1 a (fun t j i => cK (ITq gl E t j i) (OTq gl vc t j i) (D t))| ≤
      radP gl st vc d a (fun t j i => rK (ITq gl E t j i) (OTq gl vc t j i) (D t)) +
        cenErr gl st vc d a (fun t j i => cK (ITq gl E t j i) (OTq gl vc t j i) (D t)) +
        compErrT gl st vc d a B := by
  have h1 := sigTP_close gl st E vc P d a iw B hd hP hocc hB
  have h2 := tailP_sum gl st vc P cp d a
    (fun t n j i => thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n iw))
    (fun t j i => cK (ITq gl E t j i) (OTq gl vc t j i) (D t)) (fun t j i => rK (ITq gl E t j i) (OTq gl vc t j i) (D t)) hd hP hc
    (fun t _ _ => rK_nonneg _ _ _ (hD t))
    (fun t ht n hn _ _ _ _ => thK_tail_mode (hD t) (hx t ht n hn))
  unfold SigTallP
  have e : ∀ A B S C : ℝ, A + B - S - C = (A - S) + (B - C) := fun _ _ _ _ => by ring
  rw [e]
  refine (abs_add _ _).trans ?_
  have : tailT gl st E vc cp a iw = ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t),
      quadR gl vc t (mR gl st cp t a n) (fun j i =>
        thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n iw)) := rfl
  rw [this]
  linarith

/-- **The theory energy step with all bands** (`D > 1`; `B0`, `B1` bound the computed-band
kernels at `iw = 0, 1`). -/
theorem sigT_diff_all_bands_true (P : ℕ → ℕ → ℕ → ℝ) (cp : Compl) (d : ℕ → ℝ) (a : ℕ)
    (D : ℕ → ℝ) (B0 B1 : ℕ → ℕ → ℕ → ℕ → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hP : ∀ t < gl.qs.length, RowDist gl st P d t)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t)
    (hB0 : ∀ t < gl.qs.length, ∀ n < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      |thKc gl st E vc t a n 0 j i| ≤ B0 t n j i)
    (hB1 : ∀ t < gl.qs.length, ∀ n < nbq st t, ∀ j < nG gl t, ∀ i < nG gl t,
      |thKc gl st E vc t a n 1 j i| ≤ B1 t n j i)
    (hc : ∀ t < gl.qs.length, CompleteP st P cp t) (hD : ∀ t, 1 < D t)
    (hx : ∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n 0 ≤ -D t) :
    |(SigTallP gl st E vc P cp a 1 - SigTallP gl st E vc P cp a 0) -
        (SigT gl E vc st a 1 - SigT gl E vc st a 0) -
        cenK gl st vc 1 a (fun t j i => cKd (ITq gl E t j i) (OTq gl vc t j i) (D t))| ≤
      radP gl st vc d a (fun t j i => rKd (ITq gl E t j i) (OTq gl vc t j i) (D t)) +
        cenErr gl st vc d a (fun t j i => cKd (ITq gl E t j i) (OTq gl vc t j i) (D t)) +
        (compErrT gl st vc d a B0 + compErrT gl st vc d a B1) := by
  have h0 := sigTP_close gl st E vc P d a 0 B0 hd hP hocc hB0
  have h1 := sigTP_close gl st E vc P d a 1 B1 hd hP hocc hB1
  have h2 := tailP_sum gl st vc P cp d a
    (fun t n j i => thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0 + 1) - thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0))
    (fun t j i => cKd (ITq gl E t j i) (OTq gl vc t j i) (D t)) (fun t j i => rKd (ITq gl E t j i) (OTq gl vc t j i) (D t)) hd hP hc
    (fun t _ _ => rKd_nonneg _ _ _ (hD t))
    (fun t ht n hn _ _ _ _ => thK_diff_mode (hD t) (hx t ht n hn))
  have hq : tailT gl st E vc cp a 1 - tailT gl st E vc cp a 0 =
      ∑ t ∈ range gl.qs.length, ∑ n ∈ range (cp.K t), quadR gl vc t (mR gl st cp t a n) (fun j i =>
        thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0 + 1) -
          thK false (ITq gl E t j i) (OTq gl vc t j i) (xR gl st cp t a n 0)) := by
    unfold tailT
    rw [← sum_sub_distrib]; refine sum_congr rfl fun t _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun n _ => ?_
    unfold quadR
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
    rw [xR_one]; ring
  unfold SigTallP
  have e : ∀ A1 B1 A0 B0 S1 S0 C : ℝ, (A1 + B1 - (A0 + B0)) - (S1 - S0) - C =
      (A1 - S1) - (A0 - S0) + ((B1 - B0) - C) := fun _ _ _ _ _ _ _ => by ring
  rw [e, hq]
  refine (abs_add _ _).trans ?_
  have := abs_sub (SigTP gl st E vc P a 1 - SigT gl E vc st a 1)
    (SigTP gl st E vc P a 0 - SigT gl E vc st a 0)
  linarith

end mainT

/-! ### Existence: exactly orthonormal rows near the stored ones, and their completions -/

section exist

open Lowdin

variable (gl : Gl) (st : St)

/-- The per-row distance `δ_t = √η_t`, `η_t = ‖R Rᵀ - 1‖_F²` of the stored rows at `q_t`. -/
noncomputable def dL (t : ℕ) : ℝ := √(gramDef (nbq st t) (Lq st t) (Rst gl st t))

theorem gramDef_nonneg (k L : ℕ) (R : ℕ → ℕ → ℝ) : 0 ≤ gramDef k L R :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- **Löwdin at every `q_t`.** If the stored rows have Gram defect `η_t < 1`, there are
exactly orthonormal rows within `√η_t` of every stored row. -/
theorem exists_true_rows (hη : ∀ t < gl.qs.length, gramDef (nbq st t) (Lq st t) (Rst gl st t) < 1) :
    ∃ P : ℕ → ℕ → ℕ → ℝ, ∀ t < gl.qs.length,
      OrthRows (nbq st t) (Lq st t) (P t) ∧ RowDist gl st P (dL gl st) t := by
  have H : ∀ t, t < gl.qs.length → ∃ Q : ℕ → ℕ → ℝ, OrthRows (nbq st t) (Lq st t) Q ∧
      rowDist2 (nbq st t) (Lq st t) Q (Rst gl st t) ≤ gramDef (nbq st t) (Lq st t) (Rst gl st t) :=
    fun t ht => lowdin_nat _ _ _ (hη t ht)
  choose Q hQ using H
  refine ⟨fun t => if h : t < gl.qs.length then Q t h else fun _ _ => 0, fun t ht => ?_⟩
  simp only [dif_pos ht]
  refine ⟨(hQ t ht).1, fun n hn => ?_⟩
  simp only [dif_pos ht]
  rw [dL, Real.sq_sqrt (gramDef_nonneg _ _ _)]
  refine le_trans ?_ (hQ t ht).2
  unfold rowDist2
  exact single_le_sum (f := fun n => ∑ v ∈ range (Lq st t), (Q t ht n v - Rst gl st t n v) ^ 2)
    (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_range.mpr hn)

/-- **The physical completion exists**: exactly orthonormal computed rows are completed by
exactly `L - N_b` rows (the omitted bands' count), with any prescribed omitted energies. -/
theorem exists_compl (P : ℕ → ℕ → ℕ → ℝ)
    (hO : ∀ t < gl.qs.length, OrthRows (nbq st t) (Lq st t) (P t)) (ε : ℕ → ℕ → ℝ) :
    (∀ t < gl.qs.length, nbq st t ≤ Lq st t) ∧
      ∃ cp : Compl, cp.ε = ε ∧ ∀ t < gl.qs.length,
        cp.K t = Lq st t - nbq st t ∧ CompleteP st P cp t := by
  have H : ∀ t, t < gl.qs.length → nbq st t ≤ Lq st t ∧ ∃ C : ℕ → ℕ → ℝ,
      ∀ v < Lq st t, ∀ v' < Lq st t, ∑ n ∈ range (nbq st t), P t n v * P t n v' +
        ∑ n ∈ range (Lq st t - nbq st t), C n v * C n v' = if v = v' then 1 else 0 :=
    fun t ht => exists_completion_nat _ _ _ (hO t ht)
  refine ⟨fun t ht => (H t ht).1, ?_⟩
  choose _ C hC using H
  refine ⟨⟨fun t => Lq st t - nbq st t,
    fun t => if h : t < gl.qs.length then C t h else fun _ _ => 0, ε⟩, rfl, fun t ht => ⟨rfl, ?_⟩⟩
  intro v hv v' hv'
  simp only [dif_pos ht]
  exact hC t ht v hv v' hv'

variable (E : ℕ → ℕ → ℕ → ℝ) (vb oq : V3 → ℝ)

/-- **R28-F3, the combined statement (spec Σ, both quantities of the linearised Eqp1).**
If the stored rows have Gram defect `η_t < 1` at every `q_t`, there exist exactly
orthonormal rows `P` within `δ_t = √η_t` of the stored rows (built in the proof by Löwdin's
construction; the statement does not pin `P` to it). They have a completion by exactly
`L - N_b` rows with any energies. For EVERY exactly orthonormal completion of `P` whose
omitted bands lie above `E + D_t`, the all-band Σ(E_o) and the step Σ(E_o + 1) - Σ(E_o) of
the system with computed eigenvectors `P` lie in Cor's `κ = 1` enclosure on the stored
data, widened by the explicit propagation terms. This covers completions of `P`, not the
EPM Hamiltonian's own omitted eigenvectors (`sigA_all_bands_true` with `RowDist` at their
unevaluated distance `d`). -/
theorem sigA_all_bands_lowdin (a : ℕ) (D : ℕ → ℝ)
    (hη : ∀ t < gl.qs.length, gramDef (nbq st t) (Lq st t) (Rst gl st t) < 1)
    (hocc : ∀ t < gl.qs.length, gl.nocc ≤ nbq st t) (hD : ∀ t, 3 / 2 < D t) :
    ∃ P : ℕ → ℕ → ℕ → ℝ,
      (∀ t < gl.qs.length, OrthRows (nbq st t) (Lq st t) (P t) ∧ RowDist gl st P (dL gl st) t) ∧
      (∀ ε : ℕ → ℕ → ℝ, ∃ cp : Compl, cp.ε = ε ∧ ∀ t < gl.qs.length,
        cp.K t = Lq st t - nbq st t ∧ CompleteP st P cp t) ∧
      ∀ cp : Compl, (∀ t < gl.qs.length, CompleteP st P cp t) →
        (∀ t < gl.qs.length, ∀ n < cp.K t, xR gl st cp t a n 0 ≤ -D t) →
        |SigAallP gl st E vb oq P cp a 0 - SigA gl E vb oq st a 0 -
            cenK gl st vb 1 a (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
          radP gl st vb (dL gl st) a (fun t j i => rS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
            cenErr gl st vb (dL gl st) a
              (fun t j i => cS (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
            compErrA gl st E vb oq (dL gl st) a ∧
        |(SigAallP gl st E vb oq P cp a 1 - SigAallP gl st E vb oq P cp a 0) -
            (SigA gl E vb oq st a 1 - SigA gl E vb oq st a 0) -
            cenK gl st vb 1 a (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t))| ≤
          radP gl st vb (dL gl st) a
              (fun t j i => rSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
            cenErr gl st vb (dL gl st) a
              (fun t j i => cSd (Iq gl E vb oq t j i) (Oq gl vb t j i) (D t)) +
            2 * compErrA gl st E vb oq (dL gl st) a := by
  obtain ⟨P, hP⟩ := exists_true_rows gl st hη
  have hd : ∀ t, 0 ≤ dL gl st t := fun t => Real.sqrt_nonneg _
  refine ⟨P, hP, fun ε => (exists_compl gl st P (fun t ht => (hP t ht).1) ε).2, ?_⟩
  intro cp hc hx
  exact ⟨sigA_all_bands_true gl st E vb oq P cp (dL gl st) a 0 D hd (fun t ht => (hP t ht).2) hocc
      hc (fun t => by linarith [hD t]) hx,
    sigA_diff_all_bands_true gl st E vb oq P cp (dL gl st) a D hd (fun t ht => (hP t ht).2) hocc
      hc hD hx⟩

end exist

/-! ### The review's witness: `CompleteK κ`, `κ > 1`, cannot be met by `L - N_b` rows -/

/-- `L = 2`, one computed row `R = [1, 0]`: with `κ = 1 + ε`, `ε > 0`, no single completion
row `C = [c₀, c₁]` gives `RᵀR + CᵀC = κ·1`. -/
theorem f3_witness (ε c₀ c₁ : ℝ) (hε : 0 < ε) :
    ¬ (1 * 1 + c₀ * c₀ = 1 + ε ∧ 0 * 0 + c₁ * c₁ = 1 + ε ∧ 1 * 0 + c₀ * c₁ = 0) := by
  rintro ⟨h0, h1, h01⟩
  have : (c₀ * c₁) ^ 2 = ε * (1 + ε) := by nlinarith
  nlinarith

/-- At `κ = 1` (`CompleteP`) the single row `C = [0, 1]` completes `R = [1, 0]`. -/
theorem f3_witness_one : 1 * 1 + (0 : ℝ) * 0 = 1 ∧ 0 * 0 + (1 : ℝ) * 1 = 1 ∧ 1 * 0 + (0 : ℝ) * 1 = 0 := by
  norm_num

end GW.Bridge

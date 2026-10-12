/-
A3(a): the Feshbach (Schur-complement) form of a projected resolvent, over any
commutative ring. This is the exact finite-dimensional identity that turns the
Green's function into a self-energy without any diagram bookkeeping.

Setting: `𝓗 : κ × κ`, `A : κ × m` with Gram matrix `Aᵀ A = d • 1` (`d` a unit with
inverse `di`), the projector `P = di • A Aᵀ` and `Q = 1 - P`. If `(ω - 𝓗) X = A` and
`Ninv` is a left inverse of `N = ω - Q 𝓗 Q`, then

  (ω - di • (Aᵀ 𝓗 A + Aᵀ 𝓗 Ninv Q 𝓗 A)) * (di • Aᵀ X) = 1     (`feshbach`).

So `G = di • Aᵀ (ω - 𝓗)⁻¹ A` has inverse `ω - di • K`: the self-energy is
`di • K - (unperturbed part)`, with `K` split into a static part `Aᵀ 𝓗 A` and a
dynamic part that passes only through the complement `Q`.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace GW.Endpoint.ManyBody

open Matrix

variable {R : Type*} [CommRing R] {κ m : Type*} [Fintype κ] [DecidableEq κ] [Fintype m]
  [DecidableEq m]

theorem feshbach (𝓗 : Matrix κ κ R) (A : Matrix κ m R) (d di ω : R) (hdi : di * d = 1)
    (hA : Aᵀ * A = d • (1 : Matrix m m R)) (X : Matrix κ m R)
    (hX : (ω • (1 : Matrix κ κ R) - 𝓗) * X = A) (Ninv : Matrix κ κ R)
    (hN : Ninv * (ω • (1 : Matrix κ κ R) - (1 - di • (A * Aᵀ)) * 𝓗 * (1 - di • (A * Aᵀ))) = 1) :
    (ω • (1 : Matrix m m R) - di • (Aᵀ * 𝓗 * A +
        Aᵀ * 𝓗 * Ninv * ((1 - di • (A * Aᵀ)) * 𝓗 * A))) * (di • (Aᵀ * X)) = 1 := by
  set P := di • (A * Aᵀ) with hP
  set Q := 1 - P with hQ
  have hPA : P * A = A := by
    rw [hP, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one, smul_smul, hdi,
      one_smul]
  have hAP : Aᵀ * P = Aᵀ := by
    rw [hP, Matrix.mul_smul, ← Matrix.mul_assoc, hA, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      hdi, one_smul]
  have hPP : P * P = P := by
    rw [show P * P = di • (A * (Aᵀ * P)) by rw [hP, Matrix.smul_mul, Matrix.mul_assoc], hAP, ← hP]
  have hQA : Q * A = 0 := by rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPA, sub_self]
  have hAQ : Aᵀ * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, hAP, sub_self]
  have hQP : Q * P = 0 := by rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hQQ : Q * Q = Q := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← hQ, hQP, sub_zero]
  have hsplit : X = P * X + Q * X := by rw [hQ, Matrix.sub_mul, Matrix.one_mul]; abel
  have hX' : ω • X - 𝓗 * X = A := by
    rw [← hX, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  have h𝓗X : 𝓗 * X = 𝓗 * (P * X) + 𝓗 * (Q * X) := by
    conv_lhs => rw [hsplit]
    rw [Matrix.mul_add]
  -- the Q-projection of the resolvent equation
  have hq : ω • (Q * X) = Q * (𝓗 * (P * X)) + Q * (𝓗 * (Q * X)) := by
    have e := congrArg (fun M => Q * M) hX'
    simp only [Matrix.mul_sub, Matrix.mul_smul, hQA] at e
    rw [sub_eq_zero] at e
    rw [e, h𝓗X, Matrix.mul_add]
  have hNQX : (ω • (1 : Matrix κ κ R) - Q * 𝓗 * Q) * (Q * X) = Q * 𝓗 * (P * X) := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q X, hQQ]; abel
  have hQX : Q * X = Ninv * (Q * 𝓗 * (P * X)) := by
    rw [← hNQX, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  -- the A-projection
  have ha : ω • (Aᵀ * X) - Aᵀ * (𝓗 * X) = d • (1 : Matrix m m R) := by
    have e := congrArg (fun M => Aᵀ * M) hX'
    simp only [Matrix.mul_sub, Matrix.mul_smul, hA] at e
    exact e
  have hPX : P * X = A * (di • (Aᵀ * X)) := by
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rw [h𝓗X, hQX, hPX] at ha
  calc (ω • (1 : Matrix m m R) - di • (Aᵀ * 𝓗 * A + Aᵀ * 𝓗 * Ninv * (Q * 𝓗 * A))) *
        (di • (Aᵀ * X))
      = di • (ω • (Aᵀ * X) - Aᵀ * (𝓗 * (A * (di • (Aᵀ * X))) +
          𝓗 * (Ninv * (Q * 𝓗 * (A * (di • (Aᵀ * X))))))) := by
        simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_add, smul_sub, smul_add, smul_comm di ω]
    _ = di • (d • (1 : Matrix m m R)) := by rw [← ha]
    _ = 1 := by rw [smul_smul, hdi, one_smul]

end GW.Endpoint.ManyBody

import Mathlib

/-!
# Levent Alpöge/Fable 5's counterexample to the Jacobian conjecture
-/

noncomputable section

open Matrix Function

namespace MvPolynomial

variable {R : Type*} {σ : Type*}

/-- Jacobian matrix of a family of multivariate polynomials -/
def jacobianMatrix [CommSemiring R] [DecidableEq σ] (F : σ → MvPolynomial σ R) :
    Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- Jacobian determinant of a family of multivariate polynomials -/
def jacobianDet [CommRing R] [Fintype σ] [DecidableEq σ] (F : σ → MvPolynomial σ R) :
    MvPolynomial σ R :=
  (jacobianMatrix F).det

/-- Polynomial self-map induced by a family of multivariate polynomials -/
def evalMap [CommSemiring R] (F : σ → MvPolynomial σ R) (p : σ → R) : σ → R :=
  fun i => eval p (F i)

end MvPolynomial

open MvPolynomial

namespace Jacobian

variable (K : Type*) [Field K]

/-- The three components of the counterexample as multivariate polynomials -/
def F : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (C 4 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + C 3 * X 0 * X 1 ^ 2 * (C 4 + C 3 * (X 0 * X 1)),
    C 2 * X 0 - C 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

/-- Jacobian determinant of F is -2 -/
theorem jacobianDet_F : jacobianDet (F K) = C (-2) := by
  simp only [jacobianDet, jacobianMatrix, det_fin_three, of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_sub, Derivation.map_one_eq_zero, pderiv_mul,
    pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_neg, map_ofNat]
  ring

variable {K}

theorem evalMap_F_p0 : evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] := by
  funext i
  fin_cases i <;> simp [evalMap, F]

theorem evalMap_F_p1 (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [evalMap, F] <;> field_simp [h4] <;> ring

theorem evalMap_F_p2 (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [evalMap, F] <;> field_simp [h4] <;> ring

variable (K)

/-- Determinant 1 form of the counterexample: diag(1/2, 1/2, -1/2) ∘ F ∘ diag(1, 2, 2)
In characteristic 2 it reduces to (z, y + xz, x + x^2 y + x^3 z), which identifies (0, 1, 0) and
(1, 1, 0) -/
def G : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + C 2 * X 0 * X 1) ^ 3 * X 2
      + C 4 * X 1 ^ 2 * (1 + C 2 * X 0 * X 1) * (C 2 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + C 2 * X 0 * X 1) ^ 2 * X 2
      + C 12 * X 0 * X 1 ^ 2 * (C 2 + C 3 * (X 0 * X 1)),
    -X 0 + C 3 * X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2]

/-- Jacobian determinant of G is 1 -/
theorem jacobianDet_G : jacobianDet (G K) = 1 := by
  simp only [jacobianDet, jacobianMatrix, det_fin_three, of_apply, G, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_neg, Derivation.map_one_eq_zero,
    pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true]
  simp only [map_ofNat]
  ring

variable {K}

theorem evalMap_G_p0 : evalMap (G K) ![0, 0, -(1 / 8)] = ![-(1 / 8), 0, 0] := by
  funext i
  fin_cases i <;> simp [evalMap, G]

theorem evalMap_G_p1 (h2 : (2 : K) ≠ 0) :
    evalMap (G K) ![1, -(3 / 4), 13 / 4] = ![-(1 / 8), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := (by norm_num : (2 : K) * 4 = 8) ▸ mul_ne_zero h2 h4
  funext i
  fin_cases i <;> simp [evalMap, G] <;> field_simp [h4, h8] <;> ring

theorem evalMap_G_p2 (h2 : (2 : K) ≠ 0) :
    evalMap (G K) ![-1, 3 / 4, 13 / 4] = ![-(1 / 8), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := (by norm_num : (2 : K) * 4 = 8) ▸ mul_ne_zero h2 h4
  funext i
  fin_cases i <;> simp [evalMap, G] <;> field_simp [h4, h8] <;> ring

/-- In characteristic 2, G identifies (0, 1, 0) and (1, 1, 0) -/
theorem evalMap_G_char_two (h2 : (2 : K) = 0) :
    evalMap (G K) ![0, 1, 0] = evalMap (G K) ![1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp only [evalMap, G, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, map_add, map_mul, map_pow, map_neg, map_one,
      eval_C, eval_X]
  · linear_combination (-26 : K) * h2
  · linear_combination (-30 : K) * h2
  · linear_combination (-1 : K) * h2

end Jacobian

open Jacobian

/-- Full counterexample: over every field K of characteristic not 2, there is a polynomial self-map
of K^3 whose Jacobian determinant is a unit but which is not injective -/
theorem not_jacobianConjecture {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet F) → Injective (evalMap F) := by
  intro h
  have hunit : IsUnit (jacobianDet (F K)) := by
    rw [jacobianDet_F]
    exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr h2)).map C
  have h12 : (![1, -(3 / 2), 13 / 2] : Fin 3 → K) = ![-1, 3 / 2, 13 / 2] :=
    h (F K) hunit ((evalMap_F_p1 h2).trans (evalMap_F_p2 h2).symm)
  have h0 : (1 : K) = -1 := congrFun h12 0
  exact h2 (by linear_combination h0)

/-- Full counterexample in every characteristic: over every field K whatsoever, there is a
polynomial self-map of K^3 with Jacobian determinant 1 which is not injective -/
theorem not_jacobianConjecture_all_char (K : Type*) [Field K] :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet F) → Injective (evalMap F) := by
  intro h
  have hunit : IsUnit (jacobianDet (G K)) := jacobianDet_G K ▸ isUnit_one
  by_cases h2 : (2 : K) = 0
  · have h01 : (![0, 1, 0] : Fin 3 → K) = ![1, 1, 0] :=
      h (G K) hunit (evalMap_G_char_two h2)
    exact zero_ne_one (congrFun h01 0)
  · have h12 : (![1, -(3 / 4), 13 / 4] : Fin 3 → K) = ![-1, 3 / 4, 13 / 4] :=
      h (G K) hunit ((evalMap_G_p1 h2).trans (evalMap_G_p2 h2).symm)
    have h0 : (1 : K) = -1 := congrFun h12 0
    exact h2 (by linear_combination h0)

/-- Jacobian conjecture fails over C -/
theorem not_jacobianConjecture_complex :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ, IsUnit (jacobianDet F) → Injective (evalMap F) :=
  not_jacobianConjecture_all_char ℂ

#print axioms not_jacobianConjecture
#print axioms not_jacobianConjecture_all_char
#print axioms not_jacobianConjecture_complex

import Mathlib.Tactic
import Mathlib.Tactic.ReduceModChar
import Red61.AlgebraicGeometry.RationalForms.Lattices

/-! # The nine Jacobians of the coordinate systems of the second quotient

Each statement is a pure calculation in a field of characteristic five with a coordinate
basis of absolute differentials. The first column of each matrix has only one nonzero entry,
because differentials of fifth powers vanish.
-/

namespace Eff
open Red61 Module
noncomputable section

variable {E : Type*} [Field E] [CharP E 5]
variable (b : Basis (Fin 4) E (KaehlerDifferential ℤ E)) (r : Fin 4 → E)
  (hb : ∀ i, b i = KaehlerDifferential.D ℤ E (r i))

/-- The partial derivative dual to the coordinate differentials. -/
def pd (i : Fin 4) : Derivation ℤ E E := (b.coord i).compDer (KaehlerDifferential.D ℤ E)

omit [CharP E 5] in
theorem matrix_apply (w : Fin 4 → E) (i j : Fin 4) :
    coordinateDifferentialMatrix b w i j = pd b i (w j) := rfl

omit [CharP E 5] in
/-- A wedge of differentials, in terms of a reference basis. -/
theorem wedge_eq_det_smul (w : Fin 4 → E) :
    exteriorPower.ιMulti E 4 (fun k ↦ KaehlerDifferential.D ℤ E (w k)) =
      (coordinateDifferentialMatrix b w).det • exteriorPower.ιMulti E 4 b := by
  apply (topExteriorCoefficient_bijective b).injective
  rw [map_smul, topExteriorCoefficient_volume, topExteriorCoefficient_wedge, smul_eq_mul, mul_one,
    coordinateDifferentialMatrix_det_eq_topForm]

omit [CharP E 5] in
include hb in
theorem pd_coord (i k : Fin 4) : pd b i (r k) = if i = k then 1 else 0 := by
  change b.coord i (KaehlerDifferential.D ℤ E (r k)) = _
  rw [← hb, Basis.coord_apply, Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

omit [CharP E 5] in
theorem det_of_column (w : Fin 4 → E) (h : ∀ i, i ≠ 0 → pd b i (w 0) = 0) :
    (coordinateDifferentialMatrix b w).det =
      pd b 0 (w 0) * (pd b 1 (w 1) * (pd b 2 (w 2) * pd b 3 (w 3) - pd b 2 (w 3) * pd b 3 (w 2)) -
        pd b 1 (w 2) * (pd b 2 (w 1) * pd b 3 (w 3) - pd b 2 (w 3) * pd b 3 (w 1)) +
        pd b 1 (w 3) * (pd b 2 (w 1) * pd b 3 (w 2) - pd b 2 (w 2) * pd b 3 (w 1))) := by
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_succ, matrix_apply, Fin.sum_univ_zero]
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp [h1, h2, h3, Matrix.det_fin_three, Fin.succAbove, matrix_apply]
  left
  ring

variable (hne : ∀ k, r k ≠ 0)
include hb hne

/-- Closes a polynomial identity whose coefficients agree modulo five. -/
local macro "char5" : tactic =>
  `(tactic| (rw [← sub_eq_zero]; ring_nf; reduce_mod_char; try ring_nf; try simp))

omit [CharP E 5] hne in
theorem jac_q : (coordinateDifferentialMatrix b ![r 0, r 1, r 2, r 3]).det = 1 := by
  have h (i j : Fin 4) : coordinateDifferentialMatrix b ![r 0, r 1, r 2, r 3] i j =
      if i = j then 1 else 0 := by
    rw [matrix_apply]
    fin_cases j <;> simp [pd_coord b r hb]
  have hone : coordinateDifferentialMatrix b ![r 0, r 1, r 2, r 3] = 1 := by
    ext i j
    rw [h, Matrix.one_apply]
  rw [hone, Matrix.det_one]

theorem jac_B (W : E) (hW : W = r 1 * r 0 * r 2 + 3) (hW0 : W ≠ 0) :
    (coordinateDifferentialMatrix b
      ![W ^ 5 / (r 2 ^ 5 * r 0), r 0 + r 2 ^ 3 * r 3 * r 0 ^ 2, -r 2 / W ^ 2, r 2 ^ 2 / W ^ 3]).det = 4 * r 0 * r 2 / W := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hW1 : pd b 1 W = r 0 * r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; ring
  have hW2 : pd b 2 W = (W - 3) / r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; field_simp
  have hW3 : pd b 3 W = 0 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]
  have hN1 := hW1
  have hN2 := hW2
  have hN3 := hW3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  char5
  linear_combination -(W * r 2 ^ 2 * r 0) * h5

theorem jac_A (W : E) (hW : W = r 1 * r 0 * r 2 + 3) (hW0 : W ≠ 0) :
    (coordinateDifferentialMatrix b
      ![-1 / (r 2 ^ 5 * r 0 ^ 2), -W * r 2 ^ 2 * r 0, r 0 + r 2 ^ 3 * r 3 * r 0 ^ 2, r 2 ^ 3 * r 0]).det = r 2 ^ 3 * r 0 ^ 2 := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hW1 : pd b 1 W = r 0 * r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; ring
  have hW2 : pd b 2 W = (W - 3) / r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; field_simp
  have hW3 : pd b 3 W = 0 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]
  have hN1 := hW1
  have hN2 := hW2
  have hN3 := hW3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  char5
  exact h5

theorem jac_W (W : E) (hW : W = r 1 * r 0 * r 2 + 3) (hW0 : W ≠ 0) :
    (coordinateDifferentialMatrix b
      ![1 / (r 2 ^ 5 * r 0 ^ 3), W * r 2 * r 0, -r 2 ^ 3 * r 0 ^ 2, r 0 + r 2 ^ 3 * r 3 * r 0 ^ 2]).det = 4 * r 2 ^ 2 * r 0 ^ 2 := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hW1 : pd b 1 W = r 0 * r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; ring
  have hW2 : pd b 2 W = (W - 3) / r 2 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]; field_simp
  have hW3 : pd b 3 W = 0 := by
    rw [hW]; simp [Derivation.leibniz, pd_coord b r hb, h3]
  have hN1 := hW1
  have hN2 := hW2
  have hN3 := hW3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  char5
  linear_combination (r 2 ^ 4 * r 0) * h5

theorem jac_Q (N : E) (hN : N = r 3 + 2 * r 1 ^ 3 * r 0 ^ 2) (hN0 : N ≠ 0) :
    (coordinateDifferentialMatrix b
      ![r 0 * N ^ 5 / r 3 ^ 5, r 1 ^ 5 * r 0 ^ 4 + 3 * r 2 * r 3 ^ 2 * r 0, 4 * r 1 ^ 2 * r 0 * r 3 / N ^ 2, 2 * r 3 / (r 1 * r 0 * N)]).det = 4 * N * r 0 / r 3 := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hN1 : pd b 1 N = 6 * r 1 ^ 2 * r 0 ^ 2 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]; ring
  have hN2 : pd b 2 N = 0 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hN3 : pd b 3 N = 1 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hW1 := hN1
  have hW2 := hN2
  have hW3 := hN3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  subst hN
  char5
  linear_combination (8 * r 3 * r 1 ^ 3 * r 0 ^ 2 + 4 * r 3 ^ 2) * h5

theorem jac_H (N : E) (hN : N = r 3 + 2 * r 1 ^ 3 * r 0 ^ 2) (hN0 : N ≠ 0) :
    (coordinateDifferentialMatrix b
      ![4 * r 1 ^ 10 * r 0 ^ 7 / r 3 ^ 5, 4 * N * r 3 ^ 2 / (r 1 ^ 6 * r 0 ^ 4), r 1 ^ 5 * r 0 ^ 4 + 3 * r 2 * r 3 ^ 2 * r 0, 3 * r 3 ^ 3 / (r 1 ^ 7 * r 0 ^ 5)]).det = 4 * r 3 ^ 2 / (r 1 ^ 4 * r 0 ^ 2) := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hN1 : pd b 1 N = 6 * r 1 ^ 2 * r 0 ^ 2 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]; ring
  have hN2 : pd b 2 N = 0 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hN3 : pd b 3 N = 1 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hW1 := hN1
  have hW2 := hN2
  have hW3 := hN3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  subst hN
  char5
  linear_combination (2016 * r 1 ^ 3 * r 0 ^ 2 + 604 * r 3) * h5

theorem jac_G (N : E) (hN : N = r 3 + 2 * r 1 ^ 3 * r 0 ^ 2) (hN0 : N ≠ 0) :
    (coordinateDifferentialMatrix b
      ![r 0 * N ^ 5 / r 3 ^ 5, r 1 ^ 5 * r 0 ^ 4 + 3 * r 2 * r 3 ^ 2 * r 0, -2 * r 1 * r 3 ^ 4 / N ^ 4, r 3 ^ 3 / (r 0 * N ^ 4)]).det = 4 * r 3 ^ 4 / N ^ 4 := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hN1 : pd b 1 N = 6 * r 1 ^ 2 * r 0 ^ 2 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]; ring
  have hN2 : pd b 2 N = 0 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hN3 : pd b 3 N = 1 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hW1 := hN1
  have hW2 := hN2
  have hW3 := hN3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  subst hN
  char5
  linear_combination (32 * r 3 * r 1 ^ 3 * r 0 ^ 2 - 2 * r 3 ^ 2 + 72 * r 1 ^ 6 * r 0 ^ 4) * h5

theorem jac_τ (N : E) (hN : N = r 3 + 2 * r 1 ^ 3 * r 0 ^ 2) (hN0 : N ≠ 0) :
    (coordinateDifferentialMatrix b
      ![1 / (r 3 ^ 5 * r 0), N * r 3 ^ 3 * r 0, -2 * r 1 * r 3 * r 0, r 1 ^ 5 * r 0 ^ 4 + 3 * r 2 * r 3 ^ 2 * r 0]).det = 4 * r 3 * r 0 := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hN1 : pd b 1 N = 6 * r 1 ^ 2 * r 0 ^ 2 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]; ring
  have hN2 : pd b 2 N = 0 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hN3 : pd b 3 N = 1 := by
    rw [hN]; simp [Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb, h2]
  have hW1 := hN1
  have hW2 := hN2
  have hW3 := hN3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  subst hN
  char5
  linear_combination (4 * r 3) * h5

theorem jac_u :
    (coordinateDifferentialMatrix b
      ![r 2 ^ 5 * r 0 ^ 3, r 1 / (r 2 ^ 3 * r 0), 1 / (r 2 ^ 2 * r 0), r 3 / (r 2 ^ 2 * r 0)]).det = 4 / (r 2 ^ 3 * r 0) := by
  have hz := hne 0
  have ha := hne 1
  have hc := hne 2
  have hd := hne 3
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  have hf : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h1 (i : Fin 4) : pd b i (1 : E) = 0 := (pd b i).map_one_eq_zero
  have h2 (i : Fin 4) : pd b i (2 : E) = 0 := (pd b i).map_natCast 2
  have h3 (i : Fin 4) : pd b i (3 : E) = 0 := (pd b i).map_natCast 3
  have h4 (i : Fin 4) : pd b i (4 : E) = 0 := (pd b i).map_natCast 4
  have h10 : (10 : E) = 0 := by linear_combination 2 * h5
  have hW1 := h1 0
  have hW2 := h1 1
  have hW3 := h1 2
  have hN1 := hW1
  have hN2 := hW2
  have hN3 := hW3
  rw [det_of_column b _ (by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow, pd_coord b r hb,
        Derivation.leibniz_inv, h5, h1, h2, h3, h4, h10])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_div, Derivation.leibniz_pow,
    pd_coord b r hb, smul_eq_mul, nsmul_eq_mul, Fin.isValue, zero_ne_one,
    one_ne_zero, ite_true, ite_false, reduceCtorEq, Fin.reduceEq, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, mul_one, one_mul, Nat.reduceSub, Nat.cast_ofNat, pow_one, h5,
    h1, h2, h3, h4, hN1, hN2, hN3, hW1, hW2, hW3]
  field_simp
  char5
  linear_combination -2 * h5

end
end Eff

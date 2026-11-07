import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! # Algebra for a geometric codimension-one singularity

These identities support a direct proof of geometric nonnormality. They do not by themselves
prove that the displayed locus has codimension one or that its local ring is nonregular.
-/

namespace Eff.GeometricObstruction

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {F : Type*} [Field F] [CharP F 5]

/-- The equation of the proposed invariant chart after adjoining fifth roots of the constants.
The coefficient `3` represents `1/2` in characteristic five. -/
def equation (α β a b z : F) : F :=
  z - β ^ 5 + α ^ 5 * a ^ 5 * z ^ 2 + 3 * (α ^ 5) ^ 2 * b ^ 5 * z ^ 3

/-- Its partial derivative with respect to the invertible coordinate `z`. -/
def zPartial (α a b z : F) : F :=
  1 + 2 * α ^ 5 * a ^ 5 * z + 9 * (α ^ 5) ^ 2 * b ^ 5 * z ^ 2

/-- The actual polynomial, with variables in the order `(a,b,z)`. -/
def polynomial (α β : F) : MvPolynomial (Fin 3) F :=
  let a := MvPolynomial.X 0
  let b := MvPolynomial.X 1
  let z := MvPolynomial.X 2
  z - MvPolynomial.C (β ^ 5) + MvPolynomial.C (α ^ 5) * a ^ 5 * z ^ 2 +
    3 * MvPolynomial.C ((α ^ 5) ^ 2) * b ^ 5 * z ^ 3

omit [CharP F 5] in
theorem polynomial_aeval (α β a b z : F) :
    MvPolynomial.aeval ![a, b, z] (polynomial α β) = equation α β a b z := by
  simp [polynomial, equation, map_ofNat]

theorem aPartial_zero (α β : F) : MvPolynomial.pderiv 0 (polynomial α β) = 0 := by
  have h5 : (5 : MvPolynomial (Fin 3) F) = 0 := CharP.cast_eq_zero _ 5
  have h3 : MvPolynomial.pderiv 0 (3 : MvPolynomial (Fin 3) F) = 0 :=
    (MvPolynomial.pderiv 0).map_natCast 3
  simp [polynomial, h3, h5]

theorem bPartial_zero (α β : F) : MvPolynomial.pderiv 1 (polynomial α β) = 0 := by
  have h5 : (5 : MvPolynomial (Fin 3) F) = 0 := CharP.cast_eq_zero _ 5
  have h3 : MvPolynomial.pderiv 1 (3 : MvPolynomial (Fin 3) F) = 0 :=
    (MvPolynomial.pderiv 1).map_natCast 3
  simp [polynomial, h3, h5]

omit [CharP F 5] in
theorem zPartial_aeval (α β a b z : F) :
    MvPolynomial.aeval ![a, b, z] (MvPolynomial.pderiv 2 (polynomial α β)) =
      zPartial α a b z := by
  have h3 : MvPolynomial.pderiv 2 (3 : MvPolynomial (Fin 3) F) = 0 :=
    (MvPolynomial.pderiv 2).map_natCast 3
  simp [polynomial, zPartial, map_ofNat, h3]
  ring

/-- The parameter substitution lies on the hypersurface. -/
theorem parametrization_equation (α β r : F) (hα : α ≠ 0) (hr : r ≠ 0) :
    equation α β ((3 * β - 2 * r) / (α * r ^ 2))
      (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) (r ^ 5) = 0 := by
  have ha : α ^ 5 * ((3 * β - 2 * r) / (α * r ^ 2)) ^ 5 * (r ^ 5) ^ 2 =
      (3 * β - 2 * r) ^ 5 := by
    field_simp [hα, hr]
  have hb : (α ^ 5) ^ 2 * (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 *
      (r ^ 5) ^ 3 = (2 * (r - 2 * β)) ^ 5 := by
    field_simp [hα, hr]
  unfold equation
  rw [ha, show 3 * (α ^ 5) ^ 2 *
      (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 * (r ^ 5) ^ 3 =
      3 * ((α ^ 5) ^ 2 * (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 *
        (r ^ 5) ^ 3) by ring, hb]
  simp only [sub_pow_char (p := 5), mul_pow]
  norm_num
  linear_combination (13 * r ^ 5 - 566 * β ^ 5) * (CharP.cast_eq_zero F 5)

/-- The same substitution makes the remaining Jacobian entry vanish. -/
theorem parametrization_zPartial (α β r : F) (hα : α ≠ 0) (hr : r ≠ 0) :
    zPartial α ((3 * β - 2 * r) / (α * r ^ 2))
      (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) (r ^ 5) = 0 := by
  have ha : α ^ 5 * ((3 * β - 2 * r) / (α * r ^ 2)) ^ 5 * (r ^ 5) =
      (3 * β - 2 * r) ^ 5 / r ^ 5 := by
    field_simp [hα, hr]
  have hb : (α ^ 5) ^ 2 * (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 *
      (r ^ 5) ^ 2 = (2 * (r - 2 * β)) ^ 5 / r ^ 5 := by
    field_simp [hα, hr]
  unfold zPartial
  rw [show 2 * α ^ 5 * ((3 * β - 2 * r) / (α * r ^ 2)) ^ 5 * r ^ 5 =
      2 * (α ^ 5 * ((3 * β - 2 * r) / (α * r ^ 2)) ^ 5 * r ^ 5) by ring, ha]
  rw [show 9 * (α ^ 5) ^ 2 *
      (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 * (r ^ 5) ^ 2 =
      9 * ((α ^ 5) ^ 2 * (2 * (r - 2 * β) / (α ^ 2 * r ^ 3)) ^ 5 *
        (r ^ 5) ^ 2) by ring, hb]
  simp only [sub_pow_char (p := 5), mul_pow]
  field_simp [hα, hr]
  linear_combination (45 * r ^ 5 - 1746 * β ^ 5) * (CharP.cast_eq_zero F 5)

end
end Eff.GeometricObstruction

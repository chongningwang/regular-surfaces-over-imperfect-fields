import Mathlib.RingTheory.Derivation.Lie
import Red61.Surface.Field

/-! # The Euler derivation in the characteristic-five example

The construction takes place in the existing function field, with its actual coefficient
embedding. In particular the base field is `Red61.Fields.ell`, not the larger field `k`.
-/

namespace Eff

open Red61 Red61.Fields
noncomputable section

/-- The weights on `(c₁,c₂,t,w)` are `(-1,1,2,3)`. -/
def polynomialEuler : Derivation F₅ P₄ P₄ :=
  MvPolynomial.mkDerivation F₅
    ![-MvPolynomial.X 0, MvPolynomial.X 1, 2 * MvPolynomial.X 2,
      3 * MvPolynomial.X 3]

@[simp] theorem polynomialEuler_X (i : Fin 4) :
    polynomialEuler (MvPolynomial.X i) =
      ![-MvPolynomial.X 0, MvPolynomial.X 1, 2 * MvPolynomial.X 2,
        3 * MvPolynomial.X 3] i := by
  simp [polynomialEuler]

@[simp] theorem polynomialEuler_c₁ : polynomialEuler (MvPolynomial.X 0) =
    -MvPolynomial.X 0 := by simp [polynomialEuler]
@[simp] theorem polynomialEuler_c₂ : polynomialEuler (MvPolynomial.X 1) =
    MvPolynomial.X 1 := by simp [polynomialEuler]
@[simp] theorem polynomialEuler_t : polynomialEuler (MvPolynomial.X 2) =
    2 * MvPolynomial.X 2 := by simp [polynomialEuler]
@[simp] theorem polynomialEuler_w : polynomialEuler (MvPolynomial.X 3) =
    3 * MvPolynomial.X 3 := by simp [polynomialEuler]

/-- Extend the polynomial Euler derivation to the existing fraction field. -/
def euler : Derivation F₅ K K := FractionDerivation.extend polynomialEuler

@[simp] theorem euler_c₁ : euler c₁ = -c₁ := by simp [euler, coord]
@[simp] theorem euler_c₂ : euler c₂ = c₂ := by simp [euler, coord]
@[simp] theorem euler_t : euler t = 2 * t := by simp [euler, coord, map_ofNat]
@[simp] theorem euler_w : euler w = 3 * w := by simp [euler, coord, map_ofNat]

theorem euler_fifth : fifthDerivation euler = euler := by
  have hp : fifthDerivation polynomialEuler = polynomialEuler := by
    apply MvPolynomial.derivation_ext
    intro i
    have h2 : polynomialEuler (2 : P₄) = 0 := polynomialEuler.map_natCast 2
    have h3 : polynomialEuler (3 : P₄) = 0 := polynomialEuler.map_natCast 3
    fin_cases i <;> simp [Derivation.leibniz, smul_eq_mul, h2, h3]
    · left
      linear_combination 3 * MvPolynomial.X 2 * (CharP.cast_eq_zero P₄ 5)
    · left
      linear_combination 16 * MvPolynomial.X 3 * (CharP.cast_eq_zero P₄ 5)
  apply FractionDerivation.ext (A := P₄)
  intro f
  simpa only [fifthDerivation_apply, euler, FractionDerivation.extend_algebraMap] using
    congrArg (algebraMap P₄ K) (Derivation.congr_fun hp f)

theorem euler_bracket_delta : ⁅euler, delta⁆ = delta := by
  have hp : ⁅polynomialEuler, PolynomialModel.delta⁆ = PolynomialModel.delta := by
    apply MvPolynomial.derivation_ext
    intro i
    have h2 : PolynomialModel.delta (2 : P₄) = 0 := PolynomialModel.delta.map_natCast 2
    have h3 : PolynomialModel.delta (3 : P₄) = 0 := PolynomialModel.delta.map_natCast 3
    fin_cases i <;>
      simp [Derivation.commutator_apply, Derivation.leibniz, smul_eq_mul, h2, h3] <;> ring
  apply FractionDerivation.ext (A := P₄)
  intro f
  simpa only [Derivation.commutator_apply, euler, delta,
    FractionDerivation.extend_algebraMap, map_sub] using
    congrArg (algebraMap P₄ K) (Derivation.congr_fun hp f)

theorem euler_ell (a : ell) : euler (algebraMap ell K a) = 0 := by
  obtain ⟨x, hx⟩ := a.property
  change euler (includeK (a : k)) = 0
  change x ^ 5 = (a : k) at hx
  rw [← hx, map_pow, Derivation.leibniz_pow, nsmul_eq_mul,
    CharP.cast_eq_zero K 5, zero_mul]

/-- The same derivation, with its correct field of scalars. -/
def ellEuler : Derivation ell K K where
  toFun := euler
  map_add' := map_add euler
  map_smul' a x := by
    change euler (algebraMap ell K a * x) = algebraMap ell K a * euler x
    simp [Derivation.leibniz, euler_ell, smul_eq_mul]
  map_one_eq_zero' := euler.map_one_eq_zero
  leibniz' := euler.leibniz

/-- The commutator identity implies preservation of the original invariant field. -/
theorem euler_preserves_constants {x : K} (hx : x ∈ L) : euler x ∈ L := by
  have hx0 : delta x = 0 := hx
  have h := Derivation.congr_fun euler_bracket_delta x
  change euler (delta x) - delta (euler x) = delta x at h
  change delta (euler x) = 0
  simpa [hx0] using h

/-- Restriction to the actual function field of the existing surface. -/
def invariantEuler : Derivation ell L L where
  toFun x := ⟨euler (x : K), euler_preserves_constants x.property⟩
  map_add' a b := Subtype.ext (map_add euler (a : K) (b : K))
  map_smul' a x := Subtype.ext (ellEuler.map_smul a (x : K))
  map_one_eq_zero' := Subtype.ext euler.map_one_eq_zero
  leibniz' a b := Subtype.ext (ellEuler.leibniz (a : K) (b : K))

theorem invariantEuler_fifth : fifthDerivation invariantEuler = invariantEuler := by
  apply Derivation.ext
  intro x
  apply Subtype.ext
  exact Derivation.congr_fun euler_fifth (x : K)

end
end Eff

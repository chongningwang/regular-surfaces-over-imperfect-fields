import Red61.Canonical.InvariantCoordinates
import Red61.RingTheory.PolynomialModels

/-! # Differentials of the base field

Formerly the modules `BaseDifferentialVolume`, `BasePrimeSmooth`, `RationalBasePolynomialLocalization`.
-/

/-! The base field has an explicit two-dimensional absolute differential
module. Its nonzero second exterior volume and coefficient equivalence
make the base determinant factor explicit in relative constructions. -/

namespace Red61.Fields

open Module
noncomputable section
set_option maxRecDepth 4096

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

def rationalBaseDifferentialBasis : Basis (Fin 2) k (KaehlerDifferential F₅ k) :=
  polynomialLocalizationDifferentialBasis F₅ k (Fin 2) (nonZeroDivisors P₂)

def rationalBaseAbsoluteDifferentialBasis : Basis (Fin 2) k (KaehlerDifferential ℤ k) :=
  rationalBaseDifferentialBasis.map
    (quotientBaseDifferentialEquiv ℤ F₅ k ZMod.intCast_surjective).symm

def ellAbsoluteDifferentialBasis : Basis (Fin 2) ell (KaehlerDifferential ℤ ell) :=
  absoluteDifferentialBasisOfRingEquiv baseEquiv rationalBaseAbsoluteDifferentialBasis

abbrev BaseAbsoluteTopForms := ⋀[ell]^2 (KaehlerDifferential ℤ ell)

def ellAbsoluteVolume : BaseAbsoluteTopForms :=
  exteriorPower.ιMulti ell 2 ellAbsoluteDifferentialBasis

def ellAbsoluteVolumeCoefficient : BaseAbsoluteTopForms ≃ₗ[ell] ell :=
  LinearEquiv.ofBijective (topExteriorCoefficient ellAbsoluteDifferentialBasis)
    (topExteriorCoefficient_bijective ellAbsoluteDifferentialBasis)

@[simp] theorem ellAbsoluteVolumeCoefficient_volume :
    ellAbsoluteVolumeCoefficient ellAbsoluteVolume = 1 :=
  topExteriorCoefficient_volume ellAbsoluteDifferentialBasis

theorem ellAbsoluteVolumeCoefficient_symm_one :
    ellAbsoluteVolumeCoefficient.symm 1 = ellAbsoluteVolume := by
  apply ellAbsoluteVolumeCoefficient.injective
  rw [LinearEquiv.apply_symm_apply, ellAbsoluteVolumeCoefficient_volume]

end
end Red61.Fields

/-! The original scalar field is formally smooth over the prime field.
Its prime-field differential basis is the image of the already specified
integer-base basis, so normalization uses the same chosen base coordinates. -/

namespace Red61.Fields

open Module
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : @IsScalarTower ℤ F₅ ell
    (Algebra.toSMul : SMul ℤ F₅) (Algebra.toSMul : SMul F₅ ell)
    (Algebra.toSMul : SMul ℤ ell) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem ell_prime_formallySmooth : Algebra.FormallySmooth F₅ ell := by
  have : Algebra.FormallySmooth P₂ k :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P₂)
  have : Algebra.FormallySmooth F₅ k := Algebra.FormallySmooth.comp F₅ P₂ k
  exact formallySmooth_of_ringEquiv F₅ baseEquiv (Subsingleton.elim _ _)

def ellPrimeDifferentialBasis : Basis (Fin 2) ell (KaehlerDifferential F₅ ell) :=
  ellAbsoluteDifferentialBasis.map
    (quotientBaseDifferentialEquiv ℤ F₅ ell ZMod.intCast_surjective)

end
end Red61.Fields

/-! The original scalar field is explicitly a polynomial localization via
the chosen Frobenius field isomorphism. This representation makes its tensor
ambient over any coefficient algebra a polynomial localization as well. -/

namespace Red61.Fields

open scoped TensorProduct
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Module F₅ ell := Algebra.toModule

@[instance_reducible]
def ellPolynomialAlgebra : Algebra P₂ ell :=
  (baseEquiv.toRingHom.comp (algebraMap P₂ k)).toAlgebra

def ellPolynomialEquiv :
    letI := ellPolynomialAlgebra
    k ≃ₐ[P₂] ell :=
  letI := ellPolynomialAlgebra
  { baseEquiv with commutes' _ := rfl }

@[simp] theorem ellPolynomialAlgebra_X (i : Fin 2) :
    letI := ellPolynomialAlgebra
    algebraMap P₂ ell (MvPolynomial.X i) = baseEquiv (c i) := rfl

theorem ell_polynomial_isLocalization :
    letI := ellPolynomialAlgebra
    IsLocalization (nonZeroDivisors P₂) ell := by
  let := ellPolynomialAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors P₂) ellPolynomialEquiv

theorem ell_polynomial_primeTower :
    letI := ellPolynomialAlgebra
    @IsScalarTower F₅ P₂ ell (Algebra.toSMul : SMul F₅ P₂)
      (Algebra.toSMul : SMul P₂ ell) (Algebra.toSMul : SMul F₅ ell) := by
  let := ellPolynomialAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

end
end Red61.Fields

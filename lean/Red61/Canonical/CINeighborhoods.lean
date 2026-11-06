import Red61.Canonical.Adjunction

/-! # Complete-intersection neighbourhoods and tensor presentations

Formerly the modules `SurfaceTensorPresentation`, `SurfaceTensorPolynomial`, `SurfaceTensorEquations`, `SurfaceTensorPrimeModel`, `SurfaceTensorRegular`, `SurfaceLocalTensorPresentation`, `SurfaceFiniteCIModel`, `SurfaceFiniteCIScalars`, `SurfaceFiniteCIDifferentials`, `SurfaceFiniteCIOpen`, `SurfacePrincipalCI`, `SurfaceBasedCINeighborhoods`, `SurfaceNeighborhoodAbsoluteFiniteness`, `SurfaceAbsoluteCINeighborhoods`.
-/

/-! Actual tensor presentations and finite bases at every surface stalk.
The relative ambient has differential rank four and conormal rank two.
Consequently the local relative determinant comparison and its specified
generator no longer require a supplied presentation, bases, or rank equation.
Regular-immersion and canonical gluing results remain separate. -/

namespace Red61.Contraction

open Fields Module AlgebraicGeometry
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (priority := 100) (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (priority := 100) (s : S) : Algebra F₅ (S.presheaf.stalk s) :=
  sStalkPrimeAlgebra s
private local instance (priority := 100) (s : S) : @IsScalarTower F₅ ell (S.presheaf.stalk s)
    (Algebra.toSMul : SMul F₅ ell) (Algebra.toSMul : SMul ell (S.presheaf.stalk s))
    (Algebra.toSMul : SMul F₅ (S.presheaf.stalk s)) :=
  primeAlgebra_tower ell (S.presheaf.stalk s)
private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Module S.functionField RelativeRationalDeterminant := by
  let := functionFieldAlgebra ell sToBase
  infer_instance

def sTensorPresentation (s : S) : Algebra.Extension ell (S.presheaf.stalk s) :=
  tensorGraphExtension F₅ ell (S.presheaf.stalk s)

end
end Red61.Contraction

/-! The actual relative tensor ambients are polynomial localizations.
Their denominator monoids and coefficient maps are explicit; in particular
every such ambient ring is Noetherian. -/

namespace Red61.Contraction

open Fields
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Module F₅ ell := Algebra.toModule
private local instance (priority := 100) (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (priority := 100) (s : S) : Algebra F₅ (S.presheaf.stalk s) :=
  sStalkPrimeAlgebra s

@[instance_reducible]
def sTensorPolynomialAlgebra (s : S) :
    Algebra (MvPolynomial (Fin 2) (S.presheaf.stalk s)) (sTensorPresentation s).Ring := by
  let := ellPolynomialAlgebra
  have := ell_polynomial_primeTower
  exact tensorPolynomialAlgebra F₅ ell (S.presheaf.stalk s) (Fin 2)

end
end Red61.Contraction

/-! Two explicit equations generate the kernel of each actual tensor
presentation. Their polynomial-coordinate descriptions use the prescribed
ell-scalars, rather than the shifted residue coefficient section. -/

namespace Red61.Contraction

open Fields
open scoped TensorProduct
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Module F₅ ell := Algebra.toModule
private local instance (priority := 100) (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (priority := 100) (s : S) : Algebra F₅ (S.presheaf.stalk s) :=
  sStalkPrimeAlgebra s
private local instance (priority := 100) (s : S) : @IsScalarTower F₅ ell (S.presheaf.stalk s)
    (Algebra.toSMul : SMul F₅ ell) (Algebra.toSMul : SMul ell (S.presheaf.stalk s))
    (Algebra.toSMul : SMul F₅ (S.presheaf.stalk s)) :=
  primeAlgebra_tower ell (S.presheaf.stalk s)

def sTensorBaseCoordinate (s : S) (i : Fin 2) : S.presheaf.stalk s :=
  stalkScalarMap ell sToBase s (baseEquiv (c i))

def sTensorEquation (s : S) (i : Fin 2) : (sTensorPresentation s).Ring :=
  baseEquiv (c i) ⊗ₜ[F₅] (1 : S.presheaf.stalk s) -
    (1 : ell) ⊗ₜ[F₅] sTensorBaseCoordinate s i

theorem sTensorPresentation_kernel_pair (s : S) :
    (sTensorPresentation s).ker =
      Ideal.ofList [sTensorEquation s 0, sTensorEquation s 1] :=
  rationalTensor_kernel_pair (S.presheaf.stalk s)

end
end Red61.Contraction

/-! Every actual tensor ambient is a localization of the finite
four-variable polynomial ring over the original ell scalars. This model
is obtained by reversing prime-field tensor base change. -/

namespace Red61.Contraction
open Fields
noncomputable section
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s

def sTensorPrimePolynomialModel (s : S) :
    PolynomialLocalizationModel ell (sTensorPresentation s).Ring (Fin 4) :=
  (sStalkPrimePolynomialModel s).tensorLeft ell

end
end Red61.Contraction

/-! Every actual tensor presentation has a kernel generated by a regular
sequence of length two. The ambient is Noetherian and formally smooth over
ell; these are concrete local complete-intersection data. -/

namespace Red61.Contraction

open Fields RingTheory.Sequence
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Module F₅ ell := Algebra.toModule
private local instance (priority := 100) (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (priority := 100) (s : S) : Algebra F₅ (S.presheaf.stalk s) :=
  sStalkPrimeAlgebra s

theorem sTensorEquation_mem_kernel (s : S) (i : Fin 2) :
    sTensorEquation s i ∈ (sTensorPresentation s).ker :=
  rationalTensorEquation_mem_kernel (S.presheaf.stalk s) i

theorem sTensorEquations_regular (s : S) :
    IsRegular (sTensorPresentation s).Ring [sTensorEquation s 0, sTensorEquation s 1] :=
  rationalTensorEquations_regular (S.presheaf.stalk s)

end
end Red61.Contraction

/-! Localize each tensor presentation at the prime over the actual
surface stalk maximal ideal. The original quotient ring is retained, and
the two mapped equations generate its kernel and remain a regular pair. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry CategoryTheory RingTheory.Sequence
noncomputable section
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) :
    IsLocalization (IsLocalRing.maximalIdeal (S.presheaf.stalk s)).primeCompl
      (S.presheaf.stalk s) :=
  IsLocalization.of_le_isUnit (fun _ hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx)

def sTensorLocalPresentation (s : S) : Algebra.Extension ell (S.presheaf.stalk s) :=
  Algebra.Extension.localization (S' := S.presheaf.stalk s)
    (IsLocalRing.maximalIdeal (S.presheaf.stalk s)).primeCompl (sTensorPresentation s)

def sTensorLocalPrime (s : S) : PrimeSpectrum (sTensorPresentation s).Ring :=
  PrimeSpectrum.comap (algebraMap (sTensorPresentation s).Ring (S.presheaf.stalk s))
    ⟨IsLocalRing.maximalIdeal (S.presheaf.stalk s), inferInstance⟩

private local instance (s : S) :
    Algebra (sTensorPresentation s).Ring (sTensorLocalPresentation s).Ring :=
  inferInstanceAs (Algebra (sTensorPresentation s).Ring
    (Localization.AtPrime (sTensorLocalPrime s).asIdeal))
private local instance (s : S) :
    IsLocalization (sTensorLocalPrime s).asIdeal.primeCompl (sTensorLocalPresentation s).Ring :=
  inferInstanceAs (IsLocalization (sTensorLocalPrime s).asIdeal.primeCompl
    (Localization.AtPrime (sTensorLocalPrime s).asIdeal))

def sTensorLocalEquation (s : S) (i : Fin 2) : (sTensorLocalPresentation s).Ring :=
  algebraMap (sTensorPresentation s).Ring (sTensorLocalPresentation s).Ring (sTensorEquation s i)

theorem sTensorLocalPresentation_kernel (s : S) :
    (sTensorLocalPresentation s).ker =
      Ideal.ofList [sTensorLocalEquation s 0, sTensorLocalEquation s 1] := by
  calc
    (sTensorLocalPresentation s).ker = (sTensorPresentation s).ker.map
        (algebraMap (sTensorPresentation s).Ring (sTensorLocalPresentation s).Ring) :=
      extensionUnitLocalization_kernel
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s)).primeCompl (sTensorPresentation s)
    _ = _ := by
      rw [sTensorPresentation_kernel_pair, Ideal.map_ofList]
      rfl

theorem sTensorLocalPresentation_regular (s : S) :
    IsRegular (sTensorLocalPresentation s).Ring
      [sTensorLocalEquation s 0, sTensorLocalEquation s 1] :=
  extensionUnitLocalization_regular_pair
    (IsLocalRing.maximalIdeal (S.presheaf.stalk s)).primeCompl (sTensorPresentation s)
    (sTensorEquations_regular s) (sTensorEquation_mem_kernel s 0) (sTensorEquation_mem_kernel s 1)

end
end Red61.Contraction

/-! Finite complete-intersection models for all actual surface
stalks. Their ambients are smooth principal opens in four-variable
polynomial space over the original ell; their two equations are regular
and generate the actual kernel. The target stalk is a prime localization
of the finitely presented quotient. -/

namespace Red61.Contraction
open Fields Module AlgebraicGeometry RingTheory.Sequence
noncomputable section
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) : IsScalarTower ell (sTensorLocalPresentation s).Ring
    (S.presheaf.stalk s) := (sTensorLocalPresentation s).isScalarTower

def sTensorLocalPolynomialModel (s : S) :
    PolynomialLocalizationModel ell (sTensorLocalPresentation s).Ring (Fin 4) :=
  (sTensorPrimePolynomialModel s).atPrime (sTensorLocalPrime s)

private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization

def sFiniteCIModel (s : S) :
    PrincipalRegularPairModel (sTensorLocalPolynomialModel s).denominators
      (algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s)) :=
  Classical.choice (principalRegularPairModel_exists (sTensorLocalPolynomialModel s).denominators
    (algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s))
    (sTensorLocalEquation s 0) (sTensorLocalEquation s 1)
    (sTensorLocalPresentation_kernel s) (sTensorLocalPresentation_regular s).toIsWeaklyRegular)

abbrev sFiniteCIAmbient (s : S) := (sFiniteCIModel s).ambient
abbrev sFiniteCIAlgebra (s : S) := (sFiniteCIModel s).quotient

theorem sFiniteCIModel_regular (s : S) :
    IsRegular (sFiniteCIAmbient s)
      [algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).left,
        algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).right] :=
  (sFiniteCIModel s).regular

def sFiniteCIToStalk (s : S) : sFiniteCIAmbient s →+* S.presheaf.stalk s :=
  (sFiniteCIModel s).map

def sFiniteCIToStalkAlgHom (s : S) : sFiniteCIAmbient s →ₐ[ell] S.presheaf.stalk s where
  toRingHom := sFiniteCIToStalk s
  commutes' c := by
    let γ := awayLocalizationComparison (B := (sTensorLocalPresentation s).Ring)
      (sTensorLocalPolynomialModel s).denominators (sFiniteCIModel s).denominator
    change algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s)
      (γ (algebraMap ell (sFiniteCIAmbient s) c)) = algebraMap ell (S.presheaf.stalk s) c
    have hc : algebraMap ell (sFiniteCIAmbient s) c =
        algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (MvPolynomial.C c) :=
      ((IsScalarTower.toAlgHom ell (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s)).commutes c).symm
    rw [hc, γ.commutes]
    have hp : algebraMap (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring
        (MvPolynomial.C c) = algebraMap ell (sTensorLocalPresentation s).Ring c :=
      (sTensorLocalPolynomialModel s).map.commutes c
    rw [hp]
    exact (IsScalarTower.toAlgHom ell (sTensorLocalPresentation s).Ring
      (S.presheaf.stalk s)).commutes c

theorem sFiniteCIToStalk_kernel (s : S) :
    RingHom.ker (sFiniteCIToStalk s) = Ideal.ofList
      [algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).left,
        algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).right] :=
  (sFiniteCIModel s).kernel
theorem sFiniteCIAmbient_smooth (s : S) : Algebra.Smooth ell (sFiniteCIAmbient s) := by
  have : Algebra.Smooth ell (MvPolynomial (Fin 4) ell) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) :=
    Algebra.Smooth.of_isLocalization_Away
      ((sFiniteCIModel s).denominator : MvPolynomial (Fin 4) ell)
  exact Algebra.Smooth.comp ell (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s)

theorem sFiniteCIAlgebra_finitePresentation (s : S) :
    Algebra.FinitePresentation ell (sFiniteCIAlgebra s) := by
  have h₁ : Algebra.FiniteType ell (sFiniteCIAmbient s) := by
    have := (sFiniteCIAmbient_smooth s).finitePresentation
    infer_instance
  have h₂ : Algebra.FiniteType (sFiniteCIAmbient s) (sFiniteCIAlgebra s) := by
    change Algebra.FiniteType (sFiniteCIAmbient s)
      (sFiniteCIAmbient s ⧸ RingHom.ker (sFiniteCIToStalk s))
    infer_instance
  exact Algebra.FinitePresentation.of_finiteType.mp (Algebra.FiniteType.trans h₁ h₂)

@[instance_reducible] def sFiniteCIStalkAlgebra (s : S) :
    Algebra (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  (sFiniteCIModel s).quotientAlgebra

def sFiniteCIStalkPrime (s : S) : PrimeSpectrum (sFiniteCIAlgebra s) :=
  PrincipalRegularPairModel.quotientPrime (sTensorLocalPolynomialModel s).denominators
    (algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s)) (sFiniteCIModel s)

theorem sFiniteCIStalk_isLocalization (s : S) :
    letI := sFiniteCIStalkAlgebra s
    IsLocalization (sFiniteCIStalkPrime s).asIdeal.primeCompl (S.presheaf.stalk s) :=
  PrincipalRegularPairModel.quotient_isLocalization_atPrime
    (sTensorLocalPolynomialModel s).denominators
    (algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s)) (sFiniteCIModel s)
    (sTensorLocalPresentation s).algebraMap_surjective

end
end Red61.Contraction

/-! The finite complete-intersection quotient maps to the actual
surface stalk over the prescribed ell scalars. Its native prime-local
ring isomorphism is an ell-algebra isomorphism, with no change of the
original coefficient embedding. -/

namespace Red61.Contraction
open Fields Module AlgebraicGeometry
noncomputable section
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization
private local instance (s : S) : Algebra (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  sFiniteCIStalkAlgebra s
private local instance (s : S) :
    IsLocalization (sFiniteCIStalkPrime s).asIdeal.primeCompl (S.presheaf.stalk s) :=
  sFiniteCIStalk_isLocalization s

def sFiniteCIQuotientToStalk (s : S) : sFiniteCIAlgebra s →ₐ[ell] S.presheaf.stalk s :=
  Ideal.Quotient.liftₐ (RingHom.ker (sFiniteCIToStalk s)) (sFiniteCIToStalkAlgHom s)
    (fun _ hx ↦ hx)

theorem sFiniteCIQuotientToStalk_scalars (s : S) (c : ell) :
    algebraMap (sFiniteCIAlgebra s) (S.presheaf.stalk s)
      (algebraMap ell (sFiniteCIAlgebra s) c) = algebraMap ell (S.presheaf.stalk s) c :=
  (sFiniteCIQuotientToStalk s).commutes c

end
end Red61.Contraction

/-! The finite polynomial ambients and their principal localizations
have explicit relative differential bases of rank four. The coordinate
formulas use the actual polynomial maps and native differential localization. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization

def sFiniteCIAmbientDifferentialBasis (s : S) :
    Basis (Fin 4) (sFiniteCIAmbient s) (KaehlerDifferential ell (sFiniteCIAmbient s)) :=
  polynomialLocalizationDifferentialBasis ell (sFiniteCIAmbient s) (Fin 4)
    (Submonoid.powers ((sFiniteCIModel s).denominator : MvPolynomial (Fin 4) ell))

def sFiniteCILocalizedAmbientDifferentialBasis (s : S) (c : sFiniteCIAmbient s) :
    Basis (Fin 4) (Localization.Away c) (KaehlerDifferential ell (Localization.Away c)) := by
  have := KaehlerDifferential.isLocalizedModule_map ell (sFiniteCIAmbient s)
    (Localization.Away c) (Submonoid.powers c)
  exact (sFiniteCIAmbientDifferentialBasis s).ofIsLocalizedModule
    (Localization.Away c) (Submonoid.powers c)
    (KaehlerDifferential.map ell ell (sFiniteCIAmbient s) (Localization.Away c))

end
end Red61.Contraction

/-! Actual principal-open neighborhoods of every original affine-chart
point are constructed from the finite regular-pair stalk model, with open
immersion, point containment, and original ell base map verified. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization
private local instance (s : S) : Algebra (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  sFiniteCIStalkAlgebra s
private local instance (s : S) : IsScalarTower ell (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  IsScalarTower.of_algebraMap_eq (fun c ↦ (sFiniteCIQuotientToStalk_scalars s c).symm)
private local instance (s : S) :
    IsLocalization (sFiniteCIStalkPrime s).asIdeal.primeCompl (S.presheaf.stalk s) :=
  sFiniteCIStalk_isLocalization s
private local instance (s : S) : Algebra.FiniteType ell (sFiniteCIAlgebra s) :=
  @Algebra.FiniteType.of_finitePresentation ell (sFiniteCIAlgebra s) _ _ _
    (sFiniteCIAlgebra_finitePresentation s)

variable (i : quotientAtlas.Index) (p : PrimeSpectrum (quotientAtlas.ring i))
local notation "s" => quotientAtlas.chartInclusion i p

theorem sFiniteCIOpenNeighborhood :
    ∃ e : (sFiniteCIStalkPrime s).asIdeal.primeCompl,
      ∃ j : Spec (CommRingCat.of (Localization.Away (e : sFiniteCIAlgebra s))) ⟶ S,
        IsOpenImmersion j ∧ s ∈ Set.range j ∧
        j ≫ sToBase = Spec.map
          (CommRingCat.ofHom (algebraMap ell (Localization.Away (e : sFiniteCIAlgebra s)))) := by
  have : Algebra.FiniteType ell (quotientAtlas.ring i) := quotient_chart_finiteType i
  have hq : Function.Injective (algebraMap (sFiniteCIAlgebra s) (S.presheaf.stalk s)) :=
    PrincipalRegularPairModel.quotientMap_injective
      (R := MvPolynomial (Fin 4) ell) (B := (sTensorLocalPresentation s).Ring)
      (A := S.presheaf.stalk s) (sTensorLocalPolynomialModel s).denominators
      (algebraMap (sTensorLocalPresentation s).Ring (S.presheaf.stalk s)) (sFiniteCIModel s)
  exact quotientAtlas.commonFiniteLocalOpen i p (sFiniteCIAlgebra s)
    (sFiniteCIStalkPrime s) hq
end
end Red61.Contraction

/-! Principal opens of the actual finite stalk models have smooth
regular-pair presentations over the prescribed ell. Their denominators
are nonzero at the stalk point, so the localized quotients are nontrivial. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry
noncomputable section
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization
private local instance (s : S) : Algebra (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  sFiniteCIStalkAlgebra s
private local instance (s : S) : IsScalarTower ell (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  IsScalarTower.of_algebraMap_eq (fun c ↦ (sFiniteCIQuotientToStalk_scalars s c).symm)
private local instance (s : S) :
    IsLocalization (sFiniteCIStalkPrime s).asIdeal.primeCompl (S.presheaf.stalk s) :=
  sFiniteCIStalk_isLocalization s
private local instance (s : S) : Algebra.FiniteType ell (sFiniteCIAlgebra s) :=
  @Algebra.FiniteType.of_finitePresentation ell (sFiniteCIAlgebra s) _ _ _
    (sFiniteCIAlgebra_finitePresentation s)

abbrev sFiniteCIEquationLeft (s : S) : sFiniteCIAmbient s :=
  algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).left

abbrev sFiniteCIEquationRight (s : S) : sFiniteCIAmbient s :=
  algebraMap (MvPolynomial (Fin 4) ell) (sFiniteCIAmbient s) (sFiniteCIModel s).right

def sFiniteCIQuotientMap (s : S) : sFiniteCIAmbient s →ₐ[ell] sFiniteCIAlgebra s :=
  Ideal.Quotient.mkₐ ell (RingHom.ker (sFiniteCIToStalk s))

theorem sFiniteCIQuotientMap_kernel (s : S) :
    RingHom.ker (sFiniteCIQuotientMap s) =
      Ideal.ofList [sFiniteCIEquationLeft s, sFiniteCIEquationRight s] := by
  change RingHom.ker (Ideal.Quotient.mk (RingHom.ker (sFiniteCIToStalk s))) = _
  rw [Ideal.mk_ker]
  exact sFiniteCIToStalk_kernel s

theorem sFiniteCIPrincipalOpen_nontrivial (s : S)
    (e : (sFiniteCIStalkPrime s).asIdeal.primeCompl) :
    Nontrivial (Localization.Away (e : sFiniteCIAlgebra s)) := by
  have hu : IsUnit (algebraMap (sFiniteCIAlgebra s) (S.presheaf.stalk s)
      (e : sFiniteCIAlgebra s)) := IsLocalization.map_units (S.presheaf.stalk s) e
  let γ : Localization.Away (e : sFiniteCIAlgebra s) →+* S.presheaf.stalk s :=
    IsLocalization.Away.lift (S := Localization.Away (e : sFiniteCIAlgebra s))
      (g := algebraMap (sFiniteCIAlgebra s) (S.presheaf.stalk s)) (e : sFiniteCIAlgebra s) hu
  exact γ.domain_nontrivial

theorem sFiniteCIPrincipalOpen_presentation (s : S)
    (e : (sFiniteCIStalkPrime s).asIdeal.primeCompl) :
    ∃ c : sFiniteCIAmbient s,
      ∃ g : Localization.Away c →ₐ[ell] Localization.Away (e : sFiniteCIAlgebra s),
        sFiniteCIQuotientMap s c = (e : sFiniteCIAlgebra s) ∧
        Algebra.Smooth ell (Localization.Away c) ∧ Function.Surjective g ∧
        RingHom.ker g = Ideal.ofList
          [algebraMap (sFiniteCIAmbient s) (Localization.Away c) (sFiniteCIEquationLeft s),
            algebraMap (sFiniteCIAmbient s) (Localization.Away c) (sFiniteCIEquationRight s)] ∧
        RingTheory.Sequence.IsRegular (Localization.Away c)
          [algebraMap (sFiniteCIAmbient s) (Localization.Away c) (sFiniteCIEquationLeft s),
            algebraMap (sFiniteCIAmbient s) (Localization.Away c) (sFiniteCIEquationRight s)] := by
  have := sFiniteCIAmbient_smooth s
  have := sFiniteCIPrincipalOpen_nontrivial s e
  exact exists_smooth_regular_quotient_neighborhood (sFiniteCIQuotientMap s)
    Ideal.Quotient.mk_surjective (sFiniteCIEquationLeft s) (sFiniteCIEquationRight s)
    (sFiniteCIQuotientMap_kernel s) (sFiniteCIModel_regular s) (e : sFiniteCIAlgebra s)
end
end Red61.Contraction

/-! Every actual surface point has a finite complete-intersection
neighborhood with its explicit four-element ambient differential basis.
The chosen neighborhoods form a native scheme open cover over ell. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry
noncomputable section
set_option synthInstance.maxHeartbeats 80000
private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (s : S) : Algebra F₅ (S.presheaf.stalk s) := sStalkPrimeAlgebra s
private local instance (s : S) : Algebra (sTensorLocalPresentation s).Ring (S.presheaf.stalk s) :=
  (sTensorLocalPresentation s).algebra₂
private local instance (s : S) :
    Algebra (MvPolynomial (Fin 4) ell) (sTensorLocalPresentation s).Ring :=
  (sTensorLocalPolynomialModel s).map.toAlgebra
private local instance (s : S) : IsLocalization (sTensorLocalPolynomialModel s).denominators
    (sTensorLocalPresentation s).Ring := (sTensorLocalPolynomialModel s).isLocalization
private local instance (s : S) : Algebra (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  sFiniteCIStalkAlgebra s
private local instance (s : S) : IsScalarTower ell (sFiniteCIAlgebra s) (S.presheaf.stalk s) :=
  IsScalarTower.of_algebraMap_eq (fun c ↦ (sFiniteCIQuotientToStalk_scalars s c).symm)
private local instance (s : S) :
    IsLocalization (sFiniteCIStalkPrime s).asIdeal.primeCompl (S.presheaf.stalk s) :=
  sFiniteCIStalk_isLocalization s
private local instance (s : S) : Algebra.FiniteType ell (sFiniteCIAlgebra s) :=
  @Algebra.FiniteType.of_finitePresentation ell (sFiniteCIAlgebra s) _ _ _
    (sFiniteCIAlgebra_finitePresentation s)

theorem s_differential_regular_pair_neighborhood_exists (s : S) :
    Nonempty (DifferentialRegularPairNeighborhood 4 ell S sToBase s) := by
  obtain ⟨i, p, rfl⟩ := quotientAtlas.chartInclusion_cover s
  obtain ⟨e, j, hj, hpoint, hbase⟩ := sFiniteCIOpenNeighborhood i p
  obtain ⟨c, g, _, hsmooth, hsurj, hker, hreg⟩ :=
    sFiniteCIPrincipalOpen_presentation (quotientAtlas.chartInclusion i p) e
  exact ⟨{
    coordinateRing := Localization.Away (e : sFiniteCIAlgebra (quotientAtlas.chartInclusion i p))
    coordinateCommRing := inferInstance
    coordinateAlgebra := inferInstance
    ambientRing := Localization.Away c
    ambientCommRing := inferInstance
    ambientAlgebra := inferInstance
    openMap := j
    openImmersion := hj
    point_mem := hpoint
    base_comp := hbase
    quotient := g
    quotient_surjective := hsurj
    left := algebraMap (sFiniteCIAmbient (quotientAtlas.chartInclusion i p))
      (Localization.Away c) (sFiniteCIEquationLeft (quotientAtlas.chartInclusion i p))
    right := algebraMap (sFiniteCIAmbient (quotientAtlas.chartInclusion i p))
      (Localization.Away c) (sFiniteCIEquationRight (quotientAtlas.chartInclusion i p))
    kernel := hker
    regular := hreg
    smooth := hsmooth
    ambientBasis :=
      sFiniteCILocalizedAmbientDifferentialBasis (quotientAtlas.chartInclusion i p) c }⟩

def sDifferentialRegularPairNeighborhood (s : S) :
    DifferentialRegularPairNeighborhood 4 ell S sToBase s :=
  Classical.choice (s_differential_regular_pair_neighborhood_exists s)

end
end Red61.Contraction

/-! The finite surface-neighborhood coordinate algebras are essentially of finite
type over the integers. Their actual absolute differential modules are
finitely presented over the Noetherian coordinate rings. -/

namespace Red61.Contraction
open Fields Module
noncomputable section

theorem sFiniteNeighborhoodCoordinate_int_essFiniteType (s : S) :
    Algebra.EssFiniteType ℤ (sDifferentialRegularPairNeighborhood s).coordinateRing := by
  have := baseConstants_essFiniteType_int
  have := (sDifferentialRegularPairNeighborhood s).toSmoothRegularPairNeighborhood
    |>.coordinate_finiteType
  exact Algebra.EssFiniteType.comp ℤ ell
    (sDifferentialRegularPairNeighborhood s).coordinateRing

theorem sFiniteNeighborhoodCoordinate_absolute_finitePresentation (s : S) :
    Module.FinitePresentation (sDifferentialRegularPairNeighborhood s).coordinateRing
      (KaehlerDifferential ℤ (sDifferentialRegularPairNeighborhood s).coordinateRing) := by
  have := sFiniteNeighborhoodCoordinate_int_essFiniteType s
  have := (sDifferentialRegularPairNeighborhood s).toSmoothRegularPairNeighborhood
    |>.coordinate_noetherian
  exact Module.finitePresentation_of_finite _ _
end
end Red61.Contraction

/-! Every surface point has a finite complete-intersection neighborhood carrying
both the four-element ambient relative basis and the four-element coordinate
absolute basis. The constructed neighborhoods form a native scheme open cover. -/

namespace Red61.Contraction
open Fields AlgebraicGeometry
noncomputable section
set_option maxRecDepth 4096

theorem s_absolute_regular_pair_neighborhood_exists (s : S) :
    Nonempty (AbsoluteDifferentialRegularPairNeighborhood 4 4 ell S sToBase s) := by
  let P := sDifferentialRegularPairNeighborhood s
  have := sFiniteNeighborhoodCoordinate_absolute_finitePresentation s
  obtain ⟨p, hp⟩ := P.point_mem
  have h := absolute_differential_regular_neighborhood_of_stalk_basis P p
    (sStalkDifferentialBasis (P.openMap p))
  exact hp ▸ h

def sAbsoluteRegularPairNeighborhood (s : S) :
    AbsoluteDifferentialRegularPairNeighborhood 4 4 ell S sToBase s :=
  Classical.choice (s_absolute_regular_pair_neighborhood_exists s)

end
end Red61.Contraction

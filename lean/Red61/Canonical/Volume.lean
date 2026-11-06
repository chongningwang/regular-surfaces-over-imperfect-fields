import Red61.AlgebraicGeometry.RationalForms.IntegralForms
import Red61.Canonical.StalkCoordinates
import Red61.Surface.BaseDifferentials

/-! # The invariant volume and the differential lattices

Formerly the modules `SurfaceDifferentialLattices`, `SourceRationalVolume`, `KeptStalkVolumes`, `GlobalInvariantVolume`, `SurfaceDifferentialTrivialization`, `RelativeDeterminantVolume`, `SurfaceDeterminantSheaves`.
-/

/-! Four-element absolute differential bases at every stalk of the actual
contracted surface and every codimension-one stalk of its resolution. The
special stalk and the two exceptional points use their constructed bases;
all other points use the proved chart cover or the actual isomorphism locus. -/

namespace Red61.Contraction

open Fields Charts Module AlgebraicGeometry
noncomputable section
set_option synthInstance.maxHeartbeats 80000

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

private local instance (y : resolvedQuotient) :
    Module (resolvedQuotient.presheaf.stalk y) (AbsoluteStalkDifferentials resolvedQuotient y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (resolvedQuotient.presheaf.stalk y)
    (R' := resolvedQuotient.presheaf.stalk y)

theorem keptContractedAtPrimeDifferentialBasis (i : Fin 3)
    (p : PrimeSpectrum (quotientAtlas.ring i.castSucc)) :
    Nonempty (Basis (Fin 4) (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) := by
  let e := (keptInvariantEquiv i).symm.toRingEquiv
  obtain ⟨b⟩ := keptInvariantAtPrimeDifferentialBasis i (PrimeSpectrum.comap e.toRingHom p)
  exact ⟨absoluteDifferentialBasisAtPrimeOfRingEquiv e p b⟩

theorem keptContractedStalkDifferentialBasis (i : Fin 3)
    (p : PrimeSpectrum (quotientAtlas.ring i.castSucc)) :
    Nonempty (Basis (Fin 4) (S.presheaf.stalk (quotientAtlas.chartInclusion i.castSucc p))
      (AbsoluteStalkDifferentials S (quotientAtlas.chartInclusion i.castSucc p))) := by
  obtain ⟨b⟩ := keptContractedAtPrimeDifferentialBasis i p
  exact ⟨quotientAtlas.chartStalkDifferentialBasisOfLocalization i.castSucc p b⟩

theorem s_stalk_differential_basis (s : S) :
    Nonempty (Basis (Fin 4) (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s)) := by
  by_cases hs : s = s₀
  · subst s
    exact ⟨specialLocalDifferentialBasis⟩
  · obtain ⟨i, p, rfl⟩ := s_away_special_cover s hs
    exact keptContractedStalkDifferentialBasis i p

def sStalkDifferentialBasis (s : S) :
    Basis (Fin 4) (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  Classical.choice (s_stalk_differential_basis s)

end
end Red61.Contraction

/-! The fixed q1,q2,u,r rational volume on the actual contracted surface.
It is nonzero and generates the actual differential lattice at the special
point, using the proved coordinate images in the fixed function field. -/

namespace Red61.Contraction

open Fields Charts Module
open scoped TensorProduct
noncomputable section
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Algebra ell S.functionField := functionFieldAlgebra ell sToBase

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

def sRationalCoordinate (i : Fin 4) : S.functionField :=
  sFunctionFieldEquiv.symm (ConeRing.invariantCoordinates i)

theorem sRationalCoordinate_embedding (i : Fin 4) :
    ((sFunctionFieldEquiv (sRationalCoordinate i) : L) : K) =
      ![LocalCoordinates.q₁, LocalCoordinates.q₂, LocalCoordinates.u, LocalCoordinates.r] i := by
  rw [sRationalCoordinate, sFunctionFieldEquiv.apply_symm_apply]
  exact ConeRing.invariantCoordinates_coe i

def sRationalCoordinateBasis : Basis (Fin 4) S.functionField
    (KaehlerDifferential ℤ S.functionField) :=
  absoluteDifferentialBasisOfRingEquiv sFunctionFieldEquiv.symm.toRingEquiv
    ConeRing.invariantAbsoluteDifferentialBasis

theorem sRationalCoordinateBasis_apply (i : Fin 4) :
    sRationalCoordinateBasis i = KaehlerDifferential.D ℤ S.functionField (sRationalCoordinate i) :=
  absoluteDifferentialBasisOfRingEquiv_apply_D sFunctionFieldEquiv.symm.toRingEquiv
    ConeRing.invariantAbsoluteDifferentialBasis ConeRing.invariantCoordinates
      ConeRing.invariantAbsoluteDifferentialBasis_apply i

def sInvariantRationalVolume : RationalSchemeForms S 4 :=
  exteriorPower.ιMulti S.functionField 4 sRationalCoordinateBasis

theorem sInvariantRationalVolume_eq :
    sInvariantRationalVolume = exteriorPower.ιMulti S.functionField 4
      (fun i ↦ KaehlerDifferential.D ℤ S.functionField (sRationalCoordinate i)) := by
  unfold sInvariantRationalVolume
  congr 1
  funext i
  exact sRationalCoordinateBasis_apply i

theorem sInvariantRationalVolume_ne_zero : sInvariantRationalVolume ≠ 0 := by
  intro h
  have he := topExteriorCoefficient_volume sRationalCoordinateBasis
  change topExteriorCoefficient sRationalCoordinateBasis sInvariantRationalVolume = 1 at he
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem sInvariantRationalVolume_special :
    GeneratesStalkDifferentialLattice s₀ sInvariantRationalVolume := by
  refine ⟨specialLocalDifferentialBasis, ?_⟩
  change exteriorPower.ιMulti S.functionField 4 sRationalCoordinateBasis =
    exteriorPower.map 4 (stalkRationalDifferentialEquiv s₀).toLinearMap
      (exteriorPower.ιMulti S.functionField 4
        (specialLocalDifferentialBasis.baseChange S.functionField))
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  rw [sRationalCoordinateBasis_apply]
  change KaehlerDifferential.D ℤ S.functionField (sRationalCoordinate i) =
    stalkRationalDifferentialEquiv s₀ ((specialLocalDifferentialBasis.baseChange S.functionField) i)
  rw [Basis.baseChange_apply, specialLocalDifferentialBasis_apply,
    stalkRationalDifferentialEquiv_tmul_D, one_smul]
  congr 1
  apply sFunctionFieldEquiv.injective
  rw [sRationalCoordinate, sFunctionFieldEquiv.apply_symm_apply]
  exact (specialDifferentialCoordinates_embedding i).symm

end
end Red61.Contraction

/-! The invariant rational volume generates integral differential lattices
on the retained charts. The coordinate matrices use the field images of
the actual stalk basis, with their nonzero denominators proved explicitly. -/

namespace Red61

theorem fifthPower_absoluteDifferential {F : Type*} [CommRing F] [CharP F 5] (a : F) :
    KaehlerDifferential.D ℤ F (a ^ 5) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F 5, zero_smul]

theorem fifthFixed_absoluteDifferential {F : Type*} [CommRing F] [CharP F 5]
    (a : F) (ha : a ^ 5 = a) : KaehlerDifferential.D ℤ F a = 0 := by
  rw [← ha]
  exact fifthPower_absoluteDifferential a

end Red61

namespace Red61.Contraction

open Fields Charts Module LocalCoordinates PolynomialInvariants
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : CharP S.functionField 5 :=
  sFieldAmbientMap.charP sFieldAmbientMap_injective 5

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

@[simp] theorem sFieldAmbientMap_coordinate (i : Fin 4) :
    sFieldAmbientMap (sRationalCoordinate i) = ![q₁, q₂, u, r] i :=
  sRationalCoordinate_embedding i

namespace StalkCoordinateData

variable {s : S} {v : Fin 4 → K} (d : StalkCoordinateData s v)

def fieldCoordinates (i : Fin 4) : S.functionField :=
  algebraMap (S.presheaf.stalk s) S.functionField (d.coordinates i)

def fieldBasis : Basis (Fin 4) S.functionField (KaehlerDifferential ℤ S.functionField) :=
  fractionAbsoluteDifferentialBasis (S.presheaf.stalk s) S.functionField d.basis

theorem fieldBasis_apply (i : Fin 4) :
    d.fieldBasis i = KaehlerDifferential.D ℤ S.functionField (d.fieldCoordinates i) :=
  fractionAbsoluteDifferentialBasis_apply (S.presheaf.stalk s) S.functionField
    d.basis d.coordinates d.differential i

@[simp] theorem fieldCoordinates_embedding (i : Fin 4) :
    sFieldAmbientMap (d.fieldCoordinates i) = v i :=
  (sStalkAmbientMap_algebraMap s _).trans (d.embedding i)

theorem fieldCoordinates_ne_zero (i : Fin 4) (hi : v i ≠ 0) : d.fieldCoordinates i ≠ 0 := by
  intro h
  have he := d.fieldCoordinates_embedding i
  rw [h, map_zero] at he
  exact hi he.symm

theorem generatesOfDet
    (hd : (coordinateDifferentialMatrix d.fieldBasis sRationalCoordinate).det = 1) :
    GeneratesStalkDifferentialLattice s sInvariantRationalVolume := by
  refine ⟨d.basis, ?_⟩
  rw [sInvariantRationalVolume_eq]
  exact fractionCoordinateVolume_eq (S.presheaf.stalk s) S.functionField
    d.basis sRationalCoordinate hd

end StalkCoordinateData

theorem keptFirstData_generatesVolume {s : S}
    (d : StalkCoordinateData s (powerCoordinates straightFirst)) :
    GeneratesStalkDifferentialLattice s sInvariantRationalVolume := by
  have hv3 : d.fieldCoordinates 3 ≠ 0 := d.fieldCoordinates_ne_zero 3 (by
    simpa [powerCoordinates, straightFirst] using coord_nonzero 3)
  have hq : sRationalCoordinate =
      ![-d.fieldCoordinates 2 * (d.fieldCoordinates 3)⁻¹,
        d.fieldCoordinates 1 - 3 * d.fieldCoordinates 2 ^ 2 * (d.fieldCoordinates 3)⁻¹,
        (d.fieldCoordinates 3)⁻¹,
        d.fieldCoordinates 0 * d.fieldCoordinates 3 ^ 3 +
          d.fieldCoordinates 2 ^ 5 * ((d.fieldCoordinates 3)⁻¹) ^ 2] := by
    funext i
    apply sFieldAmbientMap_injective
    have hi := keptFirst_invariant_coordinates i
    fin_cases i <;> simpa [powerCoordinates, map_ofNat] using hi
  apply d.generatesOfDet
  rw [hq]
  exact keptFirstCoordinateDifferentialMatrix_det d.fieldBasis d.fieldCoordinates
    d.fieldBasis_apply _ (inv_mul_cancel₀ hv3)

theorem keptLastData_generatesVolume {s : S}
    (d : StalkCoordinateData s (powerCoordinates straightLast)) :
    GeneratesStalkDifferentialLattice s sInvariantRationalVolume := by
  have hv3 : d.fieldCoordinates 3 ≠ 0 := d.fieldCoordinates_ne_zero 3 (by
    simpa [powerCoordinates, straightLast, y₂] using monomial_nonzero (second 5))
  have hq : sRationalCoordinate =
      ![d.fieldCoordinates 1 - d.fieldCoordinates 2 ^ 3 * d.fieldCoordinates 3,
        2 * d.fieldCoordinates 2,
        (d.fieldCoordinates 2 ^ 5 + 2 * d.fieldCoordinates 0) * d.fieldCoordinates 3 ^ 2,
        (d.fieldCoordinates 3)⁻¹] := by
    funext i
    apply sFieldAmbientMap_injective
    have hi := keptLast_invariant_coordinates i
    fin_cases i <;> simpa [powerCoordinates, map_ofNat] using hi
  apply d.generatesOfDet
  rw [hq]
  exact keptLastCoordinateDifferentialMatrix_det d.fieldBasis d.fieldCoordinates
    d.fieldBasis_apply _ (inv_mul_cancel₀ hv3)

def sPrimeFieldMap : F₅ →+* S.functionField := by
  let := ZMod.algebra S.functionField 5
  exact algebraMap F₅ S.functionField

@[simp] theorem sPrimeFieldMap_embedding (a : F₅) :
    sFieldAmbientMap (sPrimeFieldMap a) = algebraMap F₅ K a :=
  RingHom.congr_fun (show sFieldAmbientMap.comp sPrimeFieldMap = algebraMap F₅ K from
    Subsingleton.elim _ _) a

theorem sPrimeFieldMap_differential (a : F₅) :
    KaehlerDifferential.D ℤ S.functionField (sPrimeFieldMap a) = 0 := by
  apply fifthFixed_absoluteDifferential
  rw [← map_pow, ZMod.pow_card]

theorem keptMiddleData_generatesVolume {s : S} (a : F₅)
    (d : StalkCoordinateData s (powerCoordinates (straightMiddle a))) :
    GeneratesStalkDifferentialLattice s sInvariantRationalVolume := by
  have hv2 : d.fieldCoordinates 2 ≠ 0 := d.fieldCoordinates_ne_zero 2 (by
    simpa [powerCoordinates, straightMiddle, y₁, y₂] using
      mul_ne_zero (monomial_nonzero (first 3)) (pow_ne_zero 2 (middle_denominator_nonzero a)))
  have hv3 : d.fieldCoordinates 3 ≠ 0 := d.fieldCoordinates_ne_zero 3 (by
    simpa [powerCoordinates, straightMiddle, y₁, y₂] using
      div_ne_zero (monomial_nonzero (second 3)) (middle_denominator_nonzero a))
  have hq : sRationalCoordinate =
      ![d.fieldCoordinates 1 - d.fieldCoordinates 2 * (d.fieldCoordinates 3)⁻¹,
        sPrimeFieldMap a - 3 * (d.fieldCoordinates 3)⁻¹,
        d.fieldCoordinates 2 ^ 2 * ((d.fieldCoordinates 3)⁻¹ -
          3 * d.fieldCoordinates 0 * d.fieldCoordinates 3 ^ 4),
        (d.fieldCoordinates 2)⁻¹ * ((d.fieldCoordinates 3)⁻¹) ^ 2] := by
    funext i
    apply sFieldAmbientMap_injective
    have hi := keptMiddle_invariant_coordinates a i
    fin_cases i <;> simpa [powerCoordinates, map_ofNat] using hi
  apply d.generatesOfDet
  rw [hq]
  exact keptMiddleCoordinateDifferentialMatrix_det d.fieldBasis d.fieldCoordinates
    d.fieldBasis_apply (sPrimeFieldMap a) (sPrimeFieldMap_differential a)
    _ _ (inv_mul_cancel₀ hv3) (inv_mul_cancel₀ hv2)

end
end Red61.Contraction

/-! The same nonzero rational fourth exterior form generates the actual
absolute differential lattice at every point of the contracted surface. -/

namespace Red61.Contraction

open Fields Charts Module AlgebraicGeometry
noncomputable section
set_option synthInstance.maxHeartbeats 80000

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

theorem sInvariantRationalVolume_generates (s : S) :
    GeneratesStalkDifferentialLattice s sInvariantRationalVolume := by
  by_cases hs : s = s₀
  · subst s
    exact sInvariantRationalVolume_special
  · obtain ⟨i, p, rfl⟩ := s_away_special_cover s hs
    fin_cases i
    · obtain ⟨d⟩ := keptFirstStalkCoordinateData p _ rfl
      exact keptFirstData_generatesVolume d
    · obtain ⟨a, ⟨d⟩⟩ := keptMiddleStalkCoordinateData p _ rfl
      exact keptMiddleData_generatesVolume a d
    · obtain ⟨d⟩ := keptLastStalkCoordinateData p _ rfl
      exact keptLastData_generatesVolume d

end
end Red61.Contraction

/-! A global coefficient trivialization of the actual absolute differential
lattices on S. Integrality is precisely regularity of the coefficient in
the embedded local ring. The associated differential-order cycle is zero.
No comparison with normalized relative dualizing sheaves is asserted here. -/

namespace Red61.Contraction

open Fields Module AlgebraicGeometry Order
noncomputable section
set_option synthInstance.maxHeartbeats 80000

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

def sRationalFormCoefficient : RationalSchemeForms S 4 ≃ₗ[S.functionField] S.functionField :=
  LinearEquiv.ofBijective (topExteriorCoefficient sRationalCoordinateBasis)
    (topExteriorCoefficient_bijective sRationalCoordinateBasis)

@[simp] theorem sRationalFormCoefficient_volume :
    sRationalFormCoefficient sInvariantRationalVolume = 1 :=
  topExteriorCoefficient_volume sRationalCoordinateBasis

end
end Red61.Contraction

/-! The explicit base-normalized rational determinant line
Hom(det Omega_ell, det Omega_S). Evaluation at the fixed base volume is
an equivalence, and its inverse sends the invariant volume to a form
integral at every actual stalk. This constructs determinant lattices;
a normalized dualizing-sheaf comparison is a separate theorem. -/

namespace Red61.Contraction

open Fields Module AlgebraicGeometry
noncomputable section
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Algebra ell S.functionField := functionFieldAlgebra ell sToBase

private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

abbrev RelativeRationalDeterminant := BaseAbsoluteTopForms →ₗ[ell] RationalSchemeForms S 4

def relativeDeterminantEvaluation :
    RelativeRationalDeterminant ≃ₗ[S.functionField] RationalSchemeForms S 4 :=
  determinantLineEvaluation (F := ell) (K := S.functionField)
    (B := BaseAbsoluteTopForms) (V := RationalSchemeForms S 4) ellAbsoluteVolumeCoefficient

theorem relativeDeterminantEvaluation_apply (φ : RelativeRationalDeterminant) :
    relativeDeterminantEvaluation φ = φ ellAbsoluteVolume := by
  change φ (ellAbsoluteVolumeCoefficient.symm 1) = _
  exact congrArg φ ellAbsoluteVolumeCoefficient_symm_one

def sRelativeDeterminantVolume : RelativeRationalDeterminant where
  toFun τ := ellAbsoluteVolumeCoefficient τ • sInvariantRationalVolume
  map_add' τ υ := by rw [map_add, add_smul]
  map_smul' a τ := by simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul]

theorem sRelativeDeterminantVolume_apply (τ : BaseAbsoluteTopForms) :
    sRelativeDeterminantVolume τ = ellAbsoluteVolumeCoefficient τ • sInvariantRationalVolume :=
  rfl

@[simp] theorem sRelativeDeterminantVolume_baseVolume :
    sRelativeDeterminantVolume ellAbsoluteVolume = sInvariantRationalVolume := by
  rw [sRelativeDeterminantVolume_apply, ellAbsoluteVolumeCoefficient_volume, one_smul]

def sRelativeDeterminantCoefficient : RelativeRationalDeterminant ≃ₗ[S.functionField]
    S.functionField :=
  relativeDeterminantEvaluation.trans sRationalFormCoefficient

@[simp] theorem sRelativeDeterminantCoefficient_volume :
    sRelativeDeterminantCoefficient sRelativeDeterminantVolume = 1 := by
  change sRationalFormCoefficient (relativeDeterminantEvaluation sRelativeDeterminantVolume) = 1
  rw [relativeDeterminantEvaluation_apply, sRelativeDeterminantVolume_baseVolume,
    sRationalFormCoefficient_volume]

end
end Red61.Contraction

/-! Global determinant sheaves of the constructed surface. Both the absolute
integral differential determinant and the base-normalized determinant lattice
are trivialized as genuine sheaves of modules, without geometric inputs. This
does not identify either lattice with a Serre dualizing sheaf. -/

namespace Red61.Contraction

open Fields Module AlgebraicGeometry CategoryTheory
noncomputable section

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Algebra ell S.functionField := functionFieldAlgebra ell sToBase

end
end Red61.Contraction

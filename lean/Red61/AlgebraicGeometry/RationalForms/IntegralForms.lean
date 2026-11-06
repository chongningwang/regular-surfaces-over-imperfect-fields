import Red61.Canonical.InvariantCoordinates

/-! # Integral top forms and volumes

Formerly the modules `RationalCoordinateLattices`, `IntegralRationalVolumes`, `IntegralFormCoordinates`, `IntegralDifferentialSheaf`, `StalkIntegralTopForms`, `AdjunctionLatticeTransport`, `StalkTopNaturality`.
-/

/-! A determinant-one rational coordinate change identifies the rational
coordinate volume with the volume of a genuine integral differential basis.
The localization map and its action on coordinate differentials are explicit. -/

namespace Red61
open Module
open scoped TensorProduct
noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

theorem topExteriorCoefficient_equiv (b : Basis (Fin n) R M) (e : M ≃ₗ[R] N)
    (ω : ⋀[R]^n M) :
    topExteriorCoefficient (b.map e) (exteriorPower.map n e.toLinearMap ω) =
      topExteriorCoefficient b ω := by
  have hm : LinearMap.toMatrix b (b.map e) e.toLinearMap = 1 := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [topExteriorCoefficient_map, hm, Matrix.det_one, one_mul]

variable (A F : Type*) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]

def fractionAbsoluteDifferentialBasis
    (b : Basis (Fin 4) A (KaehlerDifferential ℤ A)) :
    Basis (Fin 4) F (KaehlerDifferential ℤ F) :=
  (b.baseChange F).map (fractionDifferentialEquiv A F)

theorem fractionAbsoluteDifferentialBasis_apply
    (b : Basis (Fin 4) A (KaehlerDifferential ℤ A)) (v : Fin 4 → A)
    (hb : ∀ i, b i = KaehlerDifferential.D ℤ A (v i)) (i : Fin 4) :
    fractionAbsoluteDifferentialBasis A F b i =
      KaehlerDifferential.D ℤ F (algebraMap A F (v i)) := by
  simp [fractionAbsoluteDifferentialBasis, Basis.baseChange_apply, hb]

theorem fractionCoordinateVolume_eq
    (b : Basis (Fin 4) A (KaehlerDifferential ℤ A)) (w : Fin 4 → F)
    (hd : (coordinateDifferentialMatrix (fractionAbsoluteDifferentialBasis A F b) w).det = 1) :
    exteriorPower.ιMulti F 4 (fun i ↦ KaehlerDifferential.D ℤ F (w i)) =
      exteriorLinearEquiv 4 (fractionDifferentialEquiv A F)
        (exteriorPower.ιMulti F 4 (b.baseChange F)) := by
  apply (topExteriorCoefficient_bijective (fractionAbsoluteDifferentialBasis A F b)).injective
  change topExteriorCoefficient (fractionAbsoluteDifferentialBasis A F b) _ =
    topExteriorCoefficient ((b.baseChange F).map (fractionDifferentialEquiv A F))
      (exteriorPower.map 4 (fractionDifferentialEquiv A F).toLinearMap _)
  rw [topExteriorCoefficient_equiv, topExteriorCoefficient_volume, topExteriorCoefficient_wedge]
  exact (coordinateDifferentialMatrix_det_eq_topForm _ _).symm.trans hd

end
end Red61

/-! A common rational form generates an integral differential lattice when
it is the rational image of the volume of an actual stalk basis. Such a
form has intrinsic order zero at a codimension-one DVR stalk. -/

namespace Red61

open AlgebraicGeometry Order Module
open scoped TensorProduct
noncomputable section

variable {Y : Scheme} [IsIntegral Y] (y : Y) {n : ℕ}

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

def GeneratesStalkDifferentialLattice (ω : RationalSchemeForms Y n) : Prop :=
  ∃ b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y),
    ω = stalkRationalTopEquiv y n (exteriorPower.ιMulti Y.functionField n
      (b.baseChange Y.functionField))

theorem GeneratesStalkDifferentialLattice.ne_zero
    {ω : RationalSchemeForms Y n} (h : GeneratesStalkDifferentialLattice y ω) : ω ≠ 0 := by
  obtain ⟨b, rfl⟩ := h
  exact (map_ne_zero_iff _ (stalkRationalTopEquiv y n).injective).mpr
    (rationalTopVolume_ne_zero b)

end
end Red61

/-! Integral top-form lattices in the actual rational differential space.
Integral basis changes preserve these lattices. A generating rational form
identifies the lattice with the embedded local ring, with an explicit
coefficient equivalence. -/

namespace Red61

open AlgebraicGeometry Module
noncomputable section

variable {Y : Scheme} [IsIntegral Y] (y : Y) {n : ℕ}

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

def stalkTopVolume
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    RationalSchemeForms Y n :=
  stalkRationalTopEquiv y n (exteriorPower.ιMulti Y.functionField n
    (b.baseChange Y.functionField))

def stalkTopCoefficient
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    RationalSchemeForms Y n ≃ₗ[Y.functionField] Y.functionField :=
  (stalkRationalTopEquiv y n).symm.trans (LinearEquiv.ofBijective
    (topExteriorCoefficient (b.baseChange Y.functionField))
      (topExteriorCoefficient_bijective (b.baseChange Y.functionField)))

@[simp] theorem stalkTopCoefficient_volume
    (b c : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    stalkTopCoefficient y b (stalkTopVolume y c) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (b.det c) := by
  change topExteriorCoefficient (b.baseChange Y.functionField)
    ((stalkRationalTopEquiv y n).symm (stalkRationalTopEquiv y n _)) = _
  rw [LinearEquiv.symm_apply_apply, topExteriorCoefficient_wedge, basisDet_baseChange]

theorem stalkTopVolume_changeBasis
    (b c : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    stalkTopVolume y c =
      algebraMap (Y.presheaf.stalk y) Y.functionField (b.det c) • stalkTopVolume y b := by
  apply (stalkTopCoefficient y b).injective
  rw [map_smul, stalkTopCoefficient_volume, stalkTopCoefficient_volume, b.det_self,
    map_one, smul_eq_mul, mul_one]

def IsIntegralStalkTopForm (ω : RationalSchemeForms Y n) : Prop :=
  ∃ (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (a : Y.presheaf.stalk y),
    ω = algebraMap (Y.presheaf.stalk y) Y.functionField a • stalkTopVolume y b

theorem isIntegralStalkTopForm_iff (b : Basis (Fin n) (Y.presheaf.stalk y)
    (AbsoluteStalkDifferentials Y y)) (ω : RationalSchemeForms Y n) :
    IsIntegralStalkTopForm y ω ↔ ∃ a : Y.presheaf.stalk y,
      ω = algebraMap (Y.presheaf.stalk y) Y.functionField a • stalkTopVolume y b := by
  constructor
  · rintro ⟨c, a, rfl⟩
    refine ⟨a * b.det c, ?_⟩
    rw [stalkTopVolume_changeBasis y b c, smul_smul, map_mul]
  · rintro ⟨a, ha⟩
    exact ⟨b, a, ha⟩

theorem isIntegralStalkTopForm_iff_generator {κ : RationalSchemeForms Y n}
    (hκ : GeneratesStalkDifferentialLattice y κ) (ω : RationalSchemeForms Y n) :
    IsIntegralStalkTopForm y ω ↔ ∃ a : Y.presheaf.stalk y,
      ω = algebraMap (Y.presheaf.stalk y) Y.functionField a • κ := by
  obtain ⟨b, hb⟩ := hκ
  change κ = stalkTopVolume y b at hb
  rw [hb]
  exact isIntegralStalkTopForm_iff y b ω

end
end Red61

/-! The integral absolute determinant lattice as a genuine sheaf of modules.
A rational form generating every actual stalk lattice gives a global
trivialization. The sections and their pointwise operations are inherited
from the intrinsic lattice construction. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

variable (Y : Scheme) [IsIntegral Y] (n : ℕ)

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

def integralDifferentialLattice (y : Y) : Set (RationalSchemeForms Y n) :=
  {ω | IsIntegralStalkTopForm y ω}

variable (κ : RationalSchemeForms Y n) (hκ : κ ≠ 0)
  (generates : ∀ y : Y, GeneratesStalkDifferentialLattice y κ)

include generates in
theorem integralDifferentialLattice_iff (y : Y) (ω : RationalSchemeForms Y n) :
    ω ∈ integralDifferentialLattice Y n y ↔
      ∃ a : Y.presheaf.stalk y, ω = algebraMap (Y.presheaf.stalk y) Y.functionField a • κ :=
  isIntegralStalkTopForm_iff_generator y (generates y) ω

def integralDifferentialModule : Y.Modules :=
  rationalLatticeModule Y (RationalSchemeForms Y n) (integralDifferentialLattice Y n) κ
    (integralDifferentialLattice_iff Y n κ generates) hκ

def integralDifferentialVolumeIso :
    structureSheafModule Y ≅ integralDifferentialModule Y n κ hκ generates :=
  latticeVolumeModuleIso Y (RationalSchemeForms Y n) (integralDifferentialLattice Y n) κ
    (integralDifferentialLattice_iff Y n κ generates) hκ

end
end Red61

/-! The actual integral top exterior module maps into the fixed rational
form space. The map is independent of a chosen integral basis, is injective,
and its image is precisely the previously defined integral stalk lattice. -/

namespace Red61

open AlgebraicGeometry Module
noncomputable section

variable {Y : Scheme} [IsIntegral Y] (y : Y) {n : ℕ}

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

def integralStalkTopToRational
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    (⋀[Y.presheaf.stalk y]^n (AbsoluteStalkDifferentials Y y))
      →ₛₗ[algebraMap (Y.presheaf.stalk y) Y.functionField] RationalSchemeForms Y n where
  toFun ω := algebraMap (Y.presheaf.stalk y) Y.functionField (topExteriorCoefficient b ω) •
    stalkTopVolume y b
  map_add' ω η := by rw [map_add, map_add, add_smul]
  map_smul' a ω := by rw [map_smul, smul_eq_mul, map_mul, mul_smul]

@[simp] theorem integralStalkTopToRational_apply
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : ⋀[Y.presheaf.stalk y]^n (AbsoluteStalkDifferentials Y y)) :
    integralStalkTopToRational y b ω =
      algebraMap (Y.presheaf.stalk y) Y.functionField (topExteriorCoefficient b ω) •
        stalkTopVolume y b := rfl

theorem integralStalkTopToRational_volume
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    integralStalkTopToRational y b (exteriorPower.ιMulti (Y.presheaf.stalk y) n b) =
      stalkTopVolume y b := by
  rw [integralStalkTopToRational_apply, topExteriorCoefficient_volume, map_one, one_smul]

theorem integralStalkTopToRational_range
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : RationalSchemeForms Y n) :
    ω ∈ Set.range (integralStalkTopToRational y b) ↔ IsIntegralStalkTopForm y ω := by
  rw [isIntegralStalkTopForm_iff y b]
  constructor
  · rintro ⟨η, rfl⟩
    exact ⟨topExteriorCoefficient b η, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a • exteriorPower.ιMulti (Y.presheaf.stalk y) n b, ?_⟩
    simp only [integralStalkTopToRational_apply, map_smul, topExteriorCoefficient_volume,
      smul_eq_mul, mul_one]

end
end Red61

/-! Transport of integral differential lattices through a presented
adjunction isomorphism. The lemmas use the maps' stated types and evaluation
identities without expanding the construction of an adjunction comparison. -/

namespace Red61

open Module AlgebraicGeometry
noncomputable section

variable {Y : Scheme} [IsIntegral Y] (y : Y) {n : ℕ}

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

end
end Red61

/-! Native formulas for integral top forms in the function field and
compatibility of top differential transport along algebra towers. -/

namespace Red61
open AlgebraicGeometry Module
noncomputable section

section Rings
variable (A B F : Type*) [CommRing A] [CommRing B] [CommRing F]
  [Algebra A B] [Algebra A F] [Algebra B F] [IsScalarTower A B F]
  {n : ℕ}
private local instance : RingHomCompTriple (algebraMap A B) (algebraMap B F)
    (algebraMap A F) := ⟨(IsScalarTower.algebraMap_eq A B F).symm⟩

end Rings

variable {Y : Scheme} [IsIntegral Y] (y : Y) {n : ℕ}
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

theorem stalkTopVolume_native
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)) :
    stalkTopVolume y b = exteriorPower.ιMulti Y.functionField n
      (fun i ↦ KaehlerDifferential.map ℤ ℤ (Y.presheaf.stalk y) Y.functionField (b i)) := by
  unfold stalkTopVolume stalkRationalTopEquiv
  rw [exteriorLinearEquiv_wedge]
  congr 1
  funext i
  simp only [Function.comp_apply, Basis.baseChange_apply]
  change fractionDifferentialEquiv (Y.presheaf.stalk y) Y.functionField
    ((1 : Y.functionField) ⊗ₜ[Y.presheaf.stalk y] b i) = _
  rw [fractionDifferentialEquiv_tmul, one_smul]

theorem integralStalkTopToRational_native
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : ⋀[Y.presheaf.stalk y]^n (AbsoluteStalkDifferentials Y y)) :
    integralStalkTopToRational y b ω =
      semilinearTopExteriorMap b
        (linearToAlgebraSemilinear (S := Y.functionField)
          (KaehlerDifferential.map ℤ ℤ (Y.presheaf.stalk y) Y.functionField)) ω := by
  change algebraMap (Y.presheaf.stalk y) Y.functionField (topExteriorCoefficient b ω) •
      stalkTopVolume y b = _
  rw [stalkTopVolume_native]
  rfl

end
end Red61

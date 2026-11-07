import Eff.YCover

/-! # Absolute differentials of the second quotient

Each principal open of `Y` has an explicit basis of absolute differentials, given by the
differentials of its coordinates. Hence the differential sheaf is locally free of rank four.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent
  AlgebraicGeometry CategoryTheory Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

namespace YOpen

variable {i : Fin 4} (U : YOpen i)

def primeBasis : Basis (Fin 4) U.kernel (KaehlerDifferential F₅ U.kernel) :=
  polynomialKernelDifferentialBasis U.D U.v U.independent U.values U.A U.poly_le U.hull_le

def absBasis : Basis (Fin 4) U.kernel (KaehlerDifferential ℤ U.kernel) :=
  U.primeBasis.map
    (quotientBaseDifferentialEquiv ℤ F₅ U.kernel ZMod.intCast_surjective).symm

def coordinates : Fin 4 → U.kernel :=
  powerKernelCoordinate U.D U.v U.independent U.values U.A U.poly_le

theorem coordinates_coe (k : Fin 4) : (U.coordinates k : L) = powerCoordinates U.v k := rfl

theorem absBasis_apply (k : Fin 4) :
    U.absBasis k = KaehlerDifferential.D ℤ U.kernel (U.coordinates k) := by
  simp [absBasis, primeBasis, coordinates, polynomialKernelDifferentialBasis_apply]

/-- The principal open as a scheme. -/
def openMap : Spec (CommRingCat.of U.kernel) ⟶ Y :=
  Spec.map (CommRingCat.ofHom U.toKernel) ≫ yAtlas.chartInclusion i

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom U.toKernel)) := by
  let := U.algebra
  have := U.isLocalization
  exact IsOpenImmersion.of_isLocalization (R := yAtlas.ring i) (S := U.kernel) U.d

instance : IsOpenImmersion U.openMap := by
  unfold openMap
  infer_instance

theorem mem_openMap (q : PrimeSpectrum (yAtlas.ring i)) (hd : U.d ∉ q.asIdeal) :
    yAtlas.chartInclusion i q ∈ Set.range U.openMap := by
  let := U.algebra
  have := U.isLocalization
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap (yAtlas.ring i) U.kernel)) := by
    rw [PrimeSpectrum.localization_away_comap_range U.kernel U.d]
    exact hd
  obtain ⟨z, rfl⟩ := hq
  exact ⟨z, rfl⟩

end YOpen

/-- The absolute differential sheaf of `Y` is locally free of rank four. -/
theorem yAbsoluteDifferentials_isLocallyFreeOfRank :
    IsLocallyFreeOfRank 4 (nativeAbsoluteDifferentialModule Y) := fun y ↦ by
  obtain ⟨a, q, hd, rfl⟩ := y_open_cover y
  exact ⟨{
    U := _
    j := (yOpen a).openMap
    mem := (yOpen a).mem_openMap q hd
    frame := affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of (yOpen a).kernel)
      (yOpen a).openMap (yOpen a).absBasis }⟩

end
end Eff

import Red61.AlgebraicGeometry.RationalForms.ExteriorLattice
import Red61.Canonical.CINeighborhoods
import Red61.Omega

/-! The invariant differential volume trivializes `omega` on the constructed surface.
The differential sheaf and exterior powers in its definition are genuine native sheaves.
Local differential bases give rank-one exterior stalks; the previously computed integral
rational volume then gives the global isomorphism with the structure sheaf.
-/

namespace Red61.Contraction
open Fields AlgebraicGeometry CategoryTheory
noncomputable section

/-- The fourth exterior power of the actual absolute differential sheaf. -/
abbrev sAbsoluteTopDifferentials : S.Modules :=
  nativeExteriorModule S (nativeAbsoluteDifferentialModule S) 4

variable {s : S} (P : AbsoluteDifferentialRegularPairNeighborhood 4 4 ell S sToBase s)
private local instance : IsOpenImmersion P.openMap := P.openImmersion

/-- A local differential basis induces a genuine top exterior sheaf frame. -/
def sAbsoluteTopDifferentialFrame :
    structureSheafModule (Spec (CommRingCat.of P.coordinateRing)) ≅
      sAbsoluteTopDifferentials.restrict P.openMap :=
  (nativeFiniteFreeTopExteriorIso (Spec (CommRingCat.of P.coordinateRing)) 4).symm ≪≫
    (nativeExteriorFunctor (Spec (CommRingCat.of P.coordinateRing)) 4).mapIso
      (affineOpenNativeAbsoluteDifferentialFrame P.openMap P.absoluteBasis) ≪≫
        nativeExteriorRestrictionIso P.openMap (nativeAbsoluteDifferentialModule S) 4

private local instance (s : S) :
    Module (S.presheaf.stalk s) (sAbsoluteTopDifferentials.presheaf.stalk s) :=
  schemeModuleNativeStalkModule S sAbsoluteTopDifferentials s

/-- Every actual top differential stalk is free of rank one over its local ring. -/
def sAbsoluteTopDifferentialStalkFrame (s : S) :
    S.presheaf.stalk s ≃ₗ[S.presheaf.stalk s] sAbsoluteTopDifferentials.presheaf.stalk s := by
  let P := sAbsoluteRegularPairNeighborhood s
  have : IsOpenImmersion P.openMap := P.openImmersion
  let p := Classical.choose P.point_mem
  have hp := Classical.choose_spec P.point_mem
  exact hp ▸ openImmersionStalkFrameEquiv P.openMap p sAbsoluteTopDifferentials
    (sAbsoluteTopDifferentialFrame P)

/-- The invariant rational volume gives a global frame of the actual exterior sheaf. -/
def sAbsoluteTopDifferentialVolumeIso :
    structureSheafModule S ≅ sAbsoluteTopDifferentials :=
  nativeAbsoluteExteriorVolumeIso S 4 sInvariantRationalVolume sInvariantRationalVolume_ne_zero
    sInvariantRationalVolume_generates sStalkDifferentialBasis
    (fun s ↦ ⟨sAbsoluteTopDifferentialStalkFrame s⟩)

/-- Evaluation at the base volume followed by the invariant volume trivializes `omega`. -/
def omegaIsoStructureSheaf (F : Type) [Field F] [Algebra ℤ F]
    (b : S ⟶ Spec (CommRingCat.of F))
    (bF : Module.Basis (Fin 2) F (KaehlerDifferential ℤ F)) :
    omega F b bF ≅ structureSheafModule S :=
  omegaEvaluationIso F b bF ≪≫ sAbsoluteTopDifferentialVolumeIso.symm

end
end Red61.Contraction

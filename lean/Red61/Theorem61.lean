import Red61.Canonical.OmegaTrivialization

/-! Theorem 6.1 with the explicit differential definition of `omega`.
The absolute differential sheaf is locally free of rank four, and the normalized absolute
differential line is isomorphic to the structure sheaf and has Euler degree zero on every
proper integral curve. No geometric input is assumed.
-/

namespace Red61.Contraction
open Fields AlgebraicGeometry CategoryTheory
noncomputable section

/-- The absolute differential sheaf of the constructed surface is locally free of rank
four: each point has a neighbourhood with a basis of four absolute differentials. -/
theorem sAbsoluteDifferentials_isLocallyFreeOfRank :
    IsLocallyFreeOfRank 4 (nativeAbsoluteDifferentialModule S) := fun s ↦
  let P := sAbsoluteRegularPairNeighborhood s
  haveI := P.openImmersion
  ⟨{ U := _, j := P.openMap, mem := P.point_mem,
     frame := affineOpenNativeAbsoluteDifferentialFrame P.openMap P.absoluteBasis }⟩

/-- Theorem 6.1 with the explicit differential sheaf `omega`.
The definition is the Hom from the pulled-back base differential determinant to the
absolute fourth exterior differential sheaf; its triviality is a conclusion. The absolute
differential sheaf is locally free of rank four. -/
theorem exists_theorem61_omega_rationalBase :
    ∃ (Y : Scheme) (f : Y ⟶ Spec (CommRingCat.of k)),
      IsProper f ∧ IsIntegral Y ∧ IsNoetherian Y ∧ topologicalKrullDim Y = 2 ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      Function.Bijective (globalScalarMap k f) ∧ ¬ GeometricallyReduced f ∧
      IsLocallyFreeOfRank 4 (nativeAbsoluteDifferentialModule Y) ∧
      let ω := omega k f rationalBaseAbsoluteDifferentialBasis
      Nonempty (ω ≅ structureSheafModule Y) ∧ IsCurveNumericallyTrivial k f ω := by
  obtain ⟨hp, hi, hn, hd, hr, hc, hg⟩ := proper_regular_surface_rationalBase_properties
  let e := omegaIsoStructureSheaf k sToRationalBase rationalBaseAbsoluteDifferentialBasis
  exact ⟨S, sToRationalBase, hp, hi, hn, hd, hr, hc, hg,
    sAbsoluteDifferentials_isLocallyFreeOfRank, ⟨e⟩,
    isCurveNumericallyTrivial_of_trivial k sToRationalBase e⟩

end
end Red61.Contraction

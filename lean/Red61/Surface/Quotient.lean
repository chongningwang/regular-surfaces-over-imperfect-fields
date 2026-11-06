import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Red61.Surface.ConeStalk
import Red61.Surface.ContractionCharts

/-! # The quotient surface and the contracted models

Formerly the modules `GluedQuotient`, `ContractedModels`, `ContractedSpecialPoint`, `ContractedCover`, `AtlasOpenMembership`, `ContractionFunctionFields`, `SpecialPointFieldCompatibility`, `QuotientTopology`, `BoundaryPoints`, `ExceptionalContraction`.
-/

/-! The global six-chart invariant quotient, corresponding to tilde S in the paper.

This constructs an actual integral ell-scheme and a morphism from tilde X.
ContractedModels constructs the maps to the four-chart quotient S.
-/

namespace Red61.Charts

open Fields AffineGluing CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def invariantAtlas : PrincipalAtlas ell L where
  Index := Fin 6
  ring := invariantChartRing
  localization := invariant_pair_isLocalization

instance : Nonempty invariantAtlas.Index := ⟨(0 : Fin 6)⟩

abbrev resolvedQuotient : Scheme := invariantAtlas.glued

abbrev quotientChartInclusion (i : Fin 6) : invariantAtlas.chart i ⟶ resolvedQuotient :=
  invariantAtlas.chartInclusion i

def resolvedQuotientToBase : resolvedQuotient ⟶ Spec (CommRingCat.of ell) :=
  invariantAtlas.toBase

instance resolvedQuotient_integral : IsIntegral resolvedQuotient :=
  invariantAtlas.glued_integral

theorem quotient_chart_cover (x : resolvedQuotient) :
    ∃ i y, quotientChartInclusion i y = x := invariantAtlas.chartInclusion_cover x

def chartQuotient (i : Fin 6) : chartSpec i ⟶ invariantAtlas.chart i :=
  Spec.map (CommRingCat.ofHom (invariantChartEmbedding i).toRingHom)

def overlapQuotient (i j : Fin 6) : pairSpec i j ⟶ invariantAtlas.overlap i j :=
  Spec.map (CommRingCat.ofHom (invariantOverlapEmbedding i j).toRingHom)

theorem chartQuotient_left (i j : Fin 6) :
    pairToChart i j ≫ chartQuotient i = overlapQuotient i j ≫ invariantAtlas.left i j := by
  simp only [pairToChart, chartQuotient, overlapQuotient, PrincipalAtlas.left, specMap,
    ← Spec.map_comp]
  congr 1

theorem chartQuotient_right (i j : Fin 6) :
    sixChartAtlas.transition i j ≫ pairToChart j i ≫ chartQuotient j =
      overlapQuotient i j ≫ invariantAtlas.transition i j ≫ invariantAtlas.left j i := by
  simp only [PrincipalAtlas.transition, pairToChart, chartQuotient, overlapQuotient,
    PrincipalAtlas.left, specMap, ← Spec.map_comp]
  congr 1

theorem chartQuotient_compatible (i j : Fin 6) :
    pairToChart i j ≫ chartQuotient i ≫ quotientChartInclusion i =
      sixChartAtlas.transition i j ≫ pairToChart j i ≫ chartQuotient j ≫
        quotientChartInclusion j := by
  calc
    _ = overlapQuotient i j ≫ invariantAtlas.left i j ≫ quotientChartInclusion i := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ quotientChartInclusion i) (chartQuotient_left i j)
    _ = overlapQuotient i j ≫ invariantAtlas.transition i j ≫ invariantAtlas.left j i ≫
        quotientChartInclusion j := by
      exact congrArg (fun f ↦ overlapQuotient i j ≫ f)
        (invariantAtlas.glueData.glue_condition i j).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ quotientChartInclusion j) (chartQuotient_right i j).symm

/-- The chart quotient maps descend along the actual source gluing diagram. -/
def resolvedQuotientMap : resolvedScheme ⟶ resolvedQuotient :=
  Multicoequalizer.desc sixChartAtlas.glueData.toGlueData.diagram _
    (fun i ↦ chartQuotient i ≫ quotientChartInclusion i)
    (fun ⟨i,j⟩ ↦ by
      change pairToChart i j ≫ (chartQuotient i ≫ quotientChartInclusion i) =
        (sixChartAtlas.transition i j ≫ pairToChart j i) ≫
          (chartQuotient j ≫ quotientChartInclusion j)
      simpa only [Category.assoc] using chartQuotient_compatible i j)

@[simp, reassoc] theorem chartInclusion_quotient (i : Fin 6) :
    chartInclusion i ≫ resolvedQuotientMap = chartQuotient i ≫ quotientChartInclusion i := by
  apply Multicoequalizer.π_desc

/-- View the source over ell using the specified inclusion ell into k. -/
def resolvedToEll : resolvedScheme ⟶ Spec (CommRingCat.of ell) :=
  resolvedToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ell k))

theorem resolvedQuotient_over_ell :
    resolvedQuotientMap ≫ resolvedQuotientToBase = resolvedToEll := by
  apply sixChartAtlas.glueData.openCover.hom_ext
  intro i
  change chartInclusion i ≫ _ = chartInclusion i ≫ _
  simp only [chartInclusion_quotient_assoc, resolvedQuotientToBase,
    PrincipalAtlas.chartInclusion_toBase, resolvedToEll, resolvedToBase,
    PrincipalAtlas.chartInclusion_toBase_assoc]
  simp only [chartQuotient, PrincipalAtlas.chartToBase, ← Spec.map_comp]
  congr 1

def quotientChartFunctionFieldEquiv (i : Fin 6) :
    (invariantAtlas.chart i).functionField ≃+* L :=
  affineFunctionFieldEquiv (CommRingCat.of (invariantChartRing i)) L

def resolvedQuotientFunctionFieldEquiv : resolvedQuotient.functionField ≃+* L :=
  (invariantAtlas.functionFieldChartEquiv (0 : Fin 6)).trans (quotientChartFunctionFieldEquiv 0)

end
end Red61.Charts

/-! The four-chart models X and S and their maps from the six-chart models. -/

namespace Red61.Contraction

open Fields Charts AffineGluing FrobeniusDescent CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def contractedAtlas : PrincipalAtlas k K where
  Index := Fin 4
  ring := ring
  localization := all_pairs_localization

instance : Nonempty contractedAtlas.Index := ⟨(0 : Fin 4)⟩

abbrev X : Scheme := contractedAtlas.glued
def xToBase : X ⟶ Spec (CommRingCat.of k) := contractedAtlas.toBase
instance x_integral : IsIntegral X := contractedAtlas.glued_integral

def targetChart : Fin 6 → Fin 4 := ![0,3,3,1,3,2]

theorem refinement (i : Fin 6) : ring (targetChart i) ≤ chartRing i := by
  fin_cases i
  · exact le_rfl
  · exact cone_le_exceptional 0
  · exact cone_le_exceptional 1
  · exact le_rfl
  · exact cone_le_exceptional 2
  · exact le_rfl

def resolutionData : PrincipalAtlas.MapData sixChartAtlas contractedAtlas :=
  PrincipalAtlas.inclusionMapData sixChartAtlas contractedAtlas targetChart refinement

def sigma : resolvedScheme ⟶ X := resolutionData.gluedMap

theorem sigma_over_k : sigma ≫ xToBase = resolvedToBase :=
  PrincipalAtlas.inclusionMapData_over_base sixChartAtlas contractedAtlas targetChart refinement

def quotientAtlas : PrincipalAtlas ell L :=
  AtlasDescent.atlas contractedAtlas L 5 field_fifth_power_invariant

instance : Nonempty quotientAtlas.Index := ⟨(0 : Fin 4)⟩

abbrev S : Scheme := quotientAtlas.glued
def sToBase : S ⟶ Spec (CommRingCat.of ell) := quotientAtlas.toBase
instance s_integral : IsIntegral S := quotientAtlas.glued_integral

def pi : X ⟶ S := AtlasDescent.quotientMap contractedAtlas L 5 field_fifth_power_invariant

theorem pi_over_ell : pi ≫ sToBase =
    xToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ell k)) :=
  AtlasDescent.quotientMap_over_base contractedAtlas L 5 field_fifth_power_invariant

theorem invariant_refinement (i : Fin 6) :
    quotientAtlas.ring (targetChart i) ≤ invariantAtlas.ring i :=
  fixed_mono L (show (ring (targetChart i)).restrictScalars ell ≤ ellChartRing i from
    fun _ hx ↦ refinement i hx)

def quotientResolutionData : PrincipalAtlas.MapData invariantAtlas quotientAtlas :=
  PrincipalAtlas.inclusionMapData invariantAtlas quotientAtlas targetChart invariant_refinement

def sigmaBar : resolvedQuotient ⟶ S := quotientResolutionData.gluedMap

theorem sigmaBar_over_ell : sigmaBar ≫ sToBase = resolvedQuotientToBase :=
  PrincipalAtlas.inclusionMapData_over_base invariantAtlas quotientAtlas
    targetChart invariant_refinement

/-- The contraction maps commute with both invariant quotient morphisms. -/
theorem quotient_contraction_square : sigma ≫ pi = resolvedQuotientMap ≫ sigmaBar := by
  apply sixChartAtlas.glueData.openCover.hom_ext
  intro i
  change chartInclusion i ≫ _ = chartInclusion i ≫ _
  simp only [sigma, sigmaBar, pi, PrincipalAtlas.MapData.chartInclusion_gluedMap_assoc,
    Charts.chartInclusion_quotient_assoc,
    PrincipalAtlas.MapData.chartInclusion_gluedMap]
  change (specMap (refinement i) ≫ AtlasDescent.chartMap contractedAtlas L 5
    field_fifth_power_invariant (targetChart i)) ≫ quotientAtlas.chartInclusion (targetChart i) =
    (chartQuotient i ≫ specMap (invariant_refinement i)) ≫
      quotientAtlas.chartInclusion (targetChart i)
  congr 1
  simp only [specMap, AtlasDescent.chartMap, chartQuotient, ← Spec.map_comp]
  congr 1

theorem pi_bijective : Function.Bijective pi :=
  ⟨AtlasDescent.quotientMap_injective contractedAtlas L 5 field_fifth_power_invariant,
    AtlasDescent.quotientMap_surjective contractedAtlas L 5 field_fifth_power_invariant⟩

theorem pi_homeomorph : IsHomeomorph pi :=
  AtlasDescent.quotientMap_homeomorph contractedAtlas L 5 field_fifth_power_invariant

/-- On each of the three surviving charts the ring is the original derivation kernel. -/
def keptKernelEquiv (i : Fin 3) :
    quotientAtlas.ring i.castSucc ≃ₐ[ell] invariantAlgebra (chartDerivation (kept i)) := by
  apply Classical.choice
  fin_cases i
  · exact ⟨invariantChartKernelEquiv 0⟩
  · exact ⟨invariantChartKernelEquiv 3⟩
  · exact ⟨invariantChartKernelEquiv 5⟩

theorem sigma_common_chart : chartInclusion 0 ≫ sigma = contractedAtlas.chartInclusion (0 : Fin 4) := by
  change sixChartAtlas.chartInclusion (0 : Fin 6) ≫ resolutionData.gluedMap = _
  rw [resolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (chartRing 0)) ≫ contractedAtlas.chartInclusion (0 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

theorem sigmaBar_common_chart :
    quotientChartInclusion 0 ≫ sigmaBar = quotientAtlas.chartInclusion (0 : Fin 4) := by
  change invariantAtlas.chartInclusion (0 : Fin 6) ≫ quotientResolutionData.gluedMap = _
  rw [quotientResolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (invariantChartRing 0)) ≫ quotientAtlas.chartInclusion (0 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

def xFunctionFieldEquiv :
    letI := functionFieldAlgebra k xToBase
    X.functionField ≃ₐ[k] K := by
  have : IsFractionRing (contractedAtlas.ring (0 : Fin 4)) K := chart_isFractionRing 0
  exact contractedAtlas.functionFieldAlgEquiv (0 : Fin 4)

def sFunctionFieldEquiv :
    letI := functionFieldAlgebra ell sToBase
    S.functionField ≃ₐ[ell] L := by
  have : IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L := invariantChart_isFractionRing 0
  exact quotientAtlas.functionFieldAlgEquiv (0 : Fin 4)

theorem s_not_geometricallyReduced : ¬ GeometricallyReduced sToBase := by
  have : IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L := invariantChart_isFractionRing 0
  exact not_geometricallyReduced_of_affine_fraction ell (quotientAtlas.ring (0 : Fin 4)) L k
    sToBase (quotientAtlas.chartInclusion (0 : Fin 4))
    (quotientAtlas.chartInclusion_toBase (0 : Fin 4)) baseChange_not_reduced

end
end Red61.Contraction

/-! The special point of the actual global quotient S has the previously verified
regular, two-dimensional invariant local ring. -/

namespace Red61.Contraction

open Fields CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original cone spectrum is an actual affine open chart of X. -/
def coneOpen : ConeRing.coneSpec ⟶ X :=
  coneIso.hom ≫ contractedAtlas.chartInclusion (3 : Fin 4)

instance coneOpen_isOpenImmersion : IsOpenImmersion coneOpen := by
  unfold coneOpen
  infer_instance

/-- The affine invariant spectrum from the local calculation is an actual chart of S. -/
def invariantConeOpen : ConeRing.affineInvariantSpec ⟶ S :=
  coneInvariantIso.hom ≫ quotientAtlas.chartInclusion (3 : Fin 4)

instance invariantConeOpen_isOpenImmersion : IsOpenImmersion invariantConeOpen := by
  unfold invariantConeOpen
  infer_instance

theorem coneOpen_quotient :
    coneOpen ≫ pi = ConeRing.affineQuotientMap ≫ invariantConeOpen := by
  unfold coneOpen invariantConeOpen
  rw [Category.assoc]
  rw [show contractedAtlas.chartInclusion (3 : Fin 4) ≫ pi =
    coneQuotient ≫ quotientAtlas.chartInclusion (3 : Fin 4) from
      AtlasDescent.chartInclusion_quotientMap contractedAtlas L 5
        Charts.field_fifth_power_invariant (3 : Fin 4)]
  rw [← Category.assoc, cone_quotient_square, Category.assoc]

def P : X := coneOpen ConeRing.vertex
def s₀ : S := invariantConeOpen ConeRing.invariantVertex

theorem special_point_image : pi P = s₀ := by
  have h := congrArg (fun f : ConeRing.coneSpec ⟶ S ↦ f ConeRing.vertex) coneOpen_quotient
  simpa only [P, s₀, Scheme.Hom.comp_apply, ConeRing.affineQuotientMap_vertex] using h

def sSpecialStalkEquiv : S.presheaf.stalk s₀ ≃+* ConeRing.B :=
  (asIso (invariantConeOpen.stalkMap ConeRing.invariantVertex)).commRingCatIsoToRingEquiv.trans
    ConeRing.affineInvariantStalkEquiv

theorem s_special_stalk_regular : IsRegularLocalRing (S.presheaf.stalk s₀) := by
  have := ConeRing.invariant_local_ring_regular
  exact IsRegularLocalRing.of_ringEquiv sSpecialStalkEquiv.symm

theorem s_special_stalk_dimension : ringKrullDim (S.presheaf.stalk s₀) = 2 := by
  rw [ringKrullDim_eq_of_ringEquiv sSpecialStalkEquiv, ConeRing.invariant_local_ring_dimension]

end
end Red61.Contraction

/-! The three surviving charts cover the complement of the contracted point.
This proves the cover from the cone algebra and the actual gluing maps. -/

namespace Red61

open CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AffineGluing.PrincipalAtlas

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem point_in_chart_of_localization (D : PrincipalAtlas k F) (i j : D.Index)
    (d : D.ring i)
    (hloc : letI := inclusionAlgebra (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
      IsLocalization.Away d ↥(D.ring i ⊔ D.ring j))
    (p : PrimeSpectrum (D.ring i)) (hd : d ∉ p.asIdeal) :
    ∃ q, D.chartInclusion j q = D.chartInclusion i p := by
  let := inclusionAlgebra (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
  have := hloc
  have hp : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (D.ring i) ↥(D.ring i ⊔ D.ring j))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ d]
    exact hd
  obtain ⟨z,hz⟩ := hp
  refine ⟨(D.transition i j ≫ D.left j i) z, ?_⟩
  have he := congrArg (fun f : D.overlap i j ⟶ D.glued ↦ f z)
    (D.glueData.glue_condition i j)
  change D.chartInclusion j (D.left j i (D.transition i j z)) =
    D.chartInclusion i (D.left i j z) at he
  exact he.trans (congrArg (D.chartInclusion i) hz)

end AffineGluing.PrincipalAtlas

namespace ConeRing

open Fields

theorem maximal_le_of_generators (I : Ideal A) (h : ∀ i, ag i ∈ I) : maximal ≤ I := by
  let f : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
  let g : A →ₐ[k] A ⧸ I := (Algebra.ofId k (A ⧸ I)).comp residue
  have he : f = g := by
    apply AlgHom.ext_of_adjoin_eq_top (TruncatedCone.subtype_generators_top generator)
    rintro x ⟨i,rfl⟩
    change Ideal.Quotient.mk I (ag i) = algebraMap k (A ⧸ I) (residue (ag i))
    rw [show residue (ag i) = 0 from generator_residue_zero i, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f x = 0
  rw [he]
  change algebraMap k (A ⧸ I) (residue x) = 0
  rw [show residue x = 0 from hx, map_zero]

theorem prime_eq_vertex_of_parameters (p : PrimeSpectrum A)
    (hu : ag 0 ∈ p.asIdeal) (hr : ag 3 ∈ p.asIdeal) : p = vertex := by
  apply PrimeSpectrum.ext
  apply Eq.symm
  change maximal = p.asIdeal
  apply Ideal.IsMaximal.eq_of_le inferInstance p.isPrime.ne_top
  apply maximal_le_of_generators
  intro i
  fin_cases i
  · exact hu
  · apply p.isPrime.mem_of_pow_mem 2
    change ag 1 ^ 2 ∈ p.asIdeal
    rw [ag_relations.1]
    exact p.asIdeal.mul_mem_right _ hu
  · apply p.isPrime.mem_of_pow_mem 3
    change ag 2 ^ 3 ∈ p.asIdeal
    rw [ag_relations.2.2]
    exact p.asIdeal.mul_mem_left _ hr
  · exact hr

end ConeRing

namespace Contraction

open Fields Charts AffineGluing

theorem coneDenominator_zero : coneRingEquiv (ConeRing.ag 0) = coneDenominator 0 := by
  apply Subtype.ext
  exact cone_generator_image 0

theorem coneDenominator_two : coneRingEquiv (ConeRing.ag 3) = coneDenominator 2 := by
  apply Subtype.ext
  exact cone_generator_image 3

theorem cone_prime_eq_vertex (p : PrimeSpectrum coneRing)
    (h0 : coneDenominator 0 ∈ p.asIdeal) (h2 : coneDenominator 2 ∈ p.asIdeal) :
    p = coneIso.hom ConeRing.vertex := by
  have he : PrimeSpectrum.comap coneRingEquiv.toRingHom p = ConeRing.vertex := by
    apply ConeRing.prime_eq_vertex_of_parameters
    · change coneRingEquiv (ConeRing.ag 0) ∈ p.asIdeal
      rwa [coneDenominator_zero]
    · change coneRingEquiv (ConeRing.ag 3) ∈ p.asIdeal
      rwa [coneDenominator_two]
  change p = PrimeSpectrum.comap coneRingEquiv.symm.toRingHom ConeRing.vertex
  rw [← he]
  apply PrimeSpectrum.ext
  ext x
  change x ∈ p.asIdeal ↔ coneRingEquiv (coneRingEquiv.symm x) ∈ p.asIdeal
  rw [coneRingEquiv.apply_symm_apply]

/-- The actual affine opens V1,V4,V6 cover X outside its cone vertex. -/
theorem x_away_special_cover (x : X) (hx : x ≠ P) :
    ∃ (i : Fin 3) (y : PrimeSpectrum (contractedAtlas.ring i.castSucc)),
      contractedAtlas.chartInclusion i.castSucc y = x := by
  obtain ⟨i,y,rfl⟩ := (show ∃ (i : Fin 4) (y : PrimeSpectrum (ring i)),
    contractedAtlas.chartInclusion i y = x from contractedAtlas.chartInclusion_cover x)
  fin_cases i
  · exact ⟨0,y,rfl⟩
  · exact ⟨1,y,rfl⟩
  · exact ⟨2,y,rfl⟩
  · have h : coneDenominator 0 ∉ y.asIdeal ∨ coneDenominator 2 ∉ y.asIdeal := by
      by_contra hn
      push Not at hn
      apply hx
      rw [cone_prime_eq_vertex y hn.1 hn.2]
      rfl
    rcases h with h | h
    · obtain ⟨z,hz⟩ := contractedAtlas.point_in_chart_of_localization (3 : Fin 4) (0 : Fin 4)
        (coneDenominator 0) (cone_pair_localization 0) y h
      exact ⟨0,z,hz⟩
    · obtain ⟨z,hz⟩ := contractedAtlas.point_in_chart_of_localization (3 : Fin 4) (2 : Fin 4)
        (coneDenominator 2) (cone_pair_localization 2) y h
      exact ⟨2,z,hz⟩

/-- Quotient chart maps really cover every point outside s₀. -/
theorem s_away_special_cover (s : S) (hs : s ≠ s₀) :
    ∃ (i : Fin 3) (y : PrimeSpectrum (quotientAtlas.ring i.castSucc)),
      quotientAtlas.chartInclusion i.castSucc y = s := by
  obtain ⟨x,rfl⟩ := pi_bijective.surjective s
  have hx : x ≠ P := fun h ↦ hs (h ▸ special_point_image)
  obtain ⟨i,y,rfl⟩ := x_away_special_cover x hx
  refine ⟨i,AtlasDescent.chartMap contractedAtlas L 5 field_fifth_power_invariant i.castSucc y, ?_⟩
  have he := congrArg (fun f : contractedAtlas.chart i.castSucc ⟶ S ↦ f y)
    (AtlasDescent.chartInclusion_quotientMap contractedAtlas L 5
      field_fifth_power_invariant i.castSucc)
  exact he.symm

end Contraction
end
end Red61

/-! Exact chart membership for principal overlaps of an affine atlas. -/

namespace Red61.AffineGluing.PrincipalAtlas

open AlgebraicGeometry CategoryTheory
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem point_in_chart_iff_of_localization (D : PrincipalAtlas k F) (i j : D.Index)
    (d : D.ring i)
    (hloc : letI := inclusionAlgebra (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
      IsLocalization.Away d ↥(D.ring i ⊔ D.ring j))
    (p : PrimeSpectrum (D.ring i)) :
    (∃ q, D.chartInclusion j q = D.chartInclusion i p) ↔ d ∉ p.asIdeal := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,hz,_⟩ := (D.glueData.ι_eq_iff i j _ _).mp hq.symm
    let := inclusionAlgebra (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
    have := hloc
    have hp : p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (D.ring i) ↥(D.ring i ⊔ D.ring j))) := ⟨z,hz⟩
    rwa [PrimeSpectrum.localization_away_comap_range _ d] at hp
  · exact D.point_in_chart_of_localization i j d hloc p

end
end Red61.AffineGluing.PrincipalAtlas

/-! The maps on function fields induced by the four actual morphisms in the
contraction square. Quotients induce the specified inclusion L into K;
contractions induce the identity in the fixed field identifications. -/

namespace Red61

open Fields Charts AffineGluing AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Charts

theorem chartQuotient_generic (i : Fin 6) :
    chartQuotient i (genericPoint (chartSpec i)) = genericPoint (invariantAtlas.chart i) := by
  apply specMap_generic_of_injective
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg (fun x : chartRing i ↦ (x : K)) h))

theorem resolvedQuotientMap_generic :
    resolvedQuotientMap (genericPoint resolvedScheme) = genericPoint resolvedQuotient :=
  genericPoint_morphism_of_chart resolvedQuotientMap (chartInclusion 0) (quotientChartInclusion 0)
    (chartQuotient 0) (chartQuotient_generic 0) (chartInclusion_quotient 0)

def resolvedQuotientPullback : resolvedQuotient.functionField →+* resolvedScheme.functionField :=
  genericFieldMap resolvedQuotientMap resolvedQuotientMap_generic

theorem resolvedQuotientPullback_compat :
    resolvedFunctionFieldEquiv.toRingHom.comp resolvedQuotientPullback =
      L.subtype.comp resolvedQuotientFunctionFieldEquiv.toRingHom := by
  have : IsFractionRing (sixChartAtlas.ring (0 : Fin 6)) K := chart_isFractionRing 0
  have : IsFractionRing (invariantAtlas.ring (0 : Fin 6)) L := invariantChart_isFractionRing 0
  exact sixChartAtlas.functionFieldMap_compat invariantAtlas
    resolvedQuotientMap resolvedQuotientMap_generic (0 : Fin 6) (0 : Fin 6)
    (CommRingCat.ofHom (invariantChartEmbedding 0).toRingHom) (chartQuotient_generic 0)
    (chartInclusion_quotient 0) L.subtype (fun _ ↦ rfl)

@[simp] theorem resolvedQuotientPullback_apply (f : resolvedQuotient.functionField) :
    resolvedFunctionFieldEquiv (resolvedQuotientPullback f) =
      (resolvedQuotientFunctionFieldEquiv f : K) :=
  RingHom.congr_fun resolvedQuotientPullback_compat f

end Charts

namespace Contraction

end Contraction
end
end Red61

/-! The special-point stalk identification commutes with its actual embedding
into the function field of S and the specified embedding of B into L. -/

namespace Red61

open Fields AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace ConeRing

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
theorem affineInvariantStalkEquiv_embedding
    (a : affineInvariantSpec.presheaf.stalk invariantVertex) :
    affineInvariantFunctionFieldEquiv (algebraMap _ affineInvariantSpec.functionField a) =
      invariantEmbedding (affineInvariantStalkEquiv a) := by
  let := affineInvariantFieldAlgebra
  have := affineInvariant_isFractionRing
  have h := AffineGluing.affineFunctionFieldEquiv_stalk
    (CommRingCat.of affineInvariantRing) L invariantVertex
  have : IsLocalization invariantVertexIdeal.primeCompl (Localization.AtPrime invariantVertex.asIdeal) :=
    inferInstanceAs (IsLocalization invariantVertexIdeal.primeCompl
      (Localization.AtPrime invariantVertexIdeal))
  have he : atPrimeEmbedding affineInvariantRing L invariantVertex =
      invariantEmbedding.comp
        (IsLocalization.algEquiv invariantVertexIdeal.primeCompl
          (Localization.AtPrime invariantVertexIdeal) B).toRingHom := by
    apply IsLocalization.ringHom_ext invariantVertexIdeal.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, atPrimeEmbedding_algebraMap]
    change algebraMap affineInvariantRing L x = invariantEmbedding
      ((IsLocalization.algEquiv invariantVertexIdeal.primeCompl
        (Localization.AtPrime invariantVertexIdeal) B)
          (algebraMap affineInvariantRing (Localization.AtPrime invariantVertexIdeal) x))
    rw [AlgEquiv.commutes]
    rfl
  exact (RingHom.congr_fun h a).trans (RingHom.congr_fun he _)

end ConeRing

namespace Contraction

theorem coneInvariantEquiv_embedding (a : ConeRing.affineInvariantRing) :
    (coneInvariantEquiv a : L) = ConeRing.affineInvariantEmbedding a := by
  apply Subtype.ext
  change ConeRing.embed (a : ConeRing.A) =
    ConeRing.localEmbed (algebraMap ConeRing.A ConeRing.R (a : ConeRing.A))
  exact (ConeRing.localEmbed_algebraMap _).symm

theorem coneFixed_isFractionRing : IsFractionRing coneFixedRing L := by
  let := ConeRing.affineInvariantFieldAlgebra
  have := ConeRing.affineInvariant_isFractionRing
  apply IsFractionRing.of_ringEquiv_left coneInvariantEquiv.symm.toRingEquiv
  intro a
  change (a : L) = ConeRing.affineInvariantEmbedding (coneInvariantEquiv.symm a)
  rw [← coneInvariantEquiv_embedding, coneInvariantEquiv.apply_symm_apply]

theorem invariantConeOpen_functionField_compat :
    ConeRing.affineInvariantFunctionFieldEquiv.toRingHom.comp
      (genericFieldMap invariantConeOpen (genericPoint_eq_of_isOpenImmersion invariantConeOpen)) =
      sFunctionFieldEquiv.toRingHom := by
  let := ConeRing.affineInvariantFieldAlgebra
  have := ConeRing.affineInvariant_isFractionRing
  have : IsFractionRing coneFixedRing L := coneFixed_isFractionRing
  have : IsFractionRing (quotientAtlas.ring (3 : Fin 4)) L := coneFixed_isFractionRing
  have : IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L := Charts.invariantChart_isFractionRing 0
  have hchart := quotientAtlas.functionField_identification_independent (3 : Fin 4) (0 : Fin 4)
  have hmap := genericFieldMap_comp coneInvariantIso.hom
    (quotientAtlas.chartInclusion (3 : Fin 4))
    (genericPoint_eq_of_isOpenImmersion coneInvariantIso.hom)
    (genericPoint_eq_of_isOpenImmersion (quotientAtlas.chartInclusion (3 : Fin 4)))
  have haff := genericFieldMap_affine_compat L L
    (CommRingCat.ofHom coneInvariantEquiv.symm.toRingHom)
    (genericPoint_eq_of_isOpenImmersion coneInvariantIso.hom)
    (RingHom.id L) (fun a ↦ by
      change (a : L) = ConeRing.affineInvariantEmbedding (coneInvariantEquiv.symm a)
      rw [← coneInvariantEquiv_embedding, coneInvariantEquiv.apply_symm_apply])
  change ConeRing.affineInvariantFunctionFieldEquiv.toRingHom.comp
    (genericFieldMap (coneInvariantIso.hom ≫ quotientAtlas.chartInclusion (3 : Fin 4)) _) = _
  rw [hmap, ← RingHom.comp_assoc]
  rw [show ConeRing.affineInvariantFunctionFieldEquiv.toRingHom.comp
      (genericFieldMap coneInvariantIso.hom _) =
      (affineFunctionFieldEquiv (CommRingCat.of coneFixedRing) L).toRingHom from haff]
  exact congrArg RingEquiv.toRingHom hchart

theorem sSpecialStalkEquiv_functionField (a : S.presheaf.stalk s₀) :
    sFunctionFieldEquiv (algebraMap (S.presheaf.stalk s₀) S.functionField a) =
      ConeRing.invariantEmbedding (sSpecialStalkEquiv a) := by
  have hs := congrArg (fun f : S.presheaf.stalk s₀ ⟶ ConeRing.affineInvariantSpec.functionField ↦ f a)
    (genericFieldMap_stalk invariantConeOpen
      (genericPoint_eq_of_isOpenImmersion invariantConeOpen) ConeRing.invariantVertex)
  change genericFieldMap invariantConeOpen (genericPoint_eq_of_isOpenImmersion invariantConeOpen)
    (algebraMap (S.presheaf.stalk s₀) S.functionField a) =
      algebraMap _ ConeRing.affineInvariantSpec.functionField
        (invariantConeOpen.stalkMap ConeRing.invariantVertex a) at hs
  calc
    _ = ConeRing.affineInvariantFunctionFieldEquiv
        (genericFieldMap invariantConeOpen (genericPoint_eq_of_isOpenImmersion invariantConeOpen)
          (algebraMap (S.presheaf.stalk s₀) S.functionField a)) :=
      (RingHom.congr_fun invariantConeOpen_functionField_compat _).symm
    _ = _ := by
      rw [hs, ConeRing.affineInvariantStalkEquiv_embedding]
      rfl

end Contraction
end
end Red61

/-! The quotient has the same underlying space, and its affine charts pull back to the
original charts. The cartesian squares identify its affine restrictions with Spec of
the actual invariant-ring inclusions. -/

namespace Red61.Charts

open Fields AffineGluing FrobeniusDescent CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem chartQuotient_homeomorph (i : Fin 6) : IsHomeomorph (chartQuotient i) := by
  apply PrimeSpectrum.isHomeomorph_comap (invariantChartEmbedding i).toRingHom
  · intro x
    exact ⟨5, by decide, powerElement L 5 field_fifth_power_invariant (ellChartRing i) x, rfl⟩
  · rw [(RingHom.injective_iff_ker_eq_bot _).mp ?_]
    · exact bot_le
    · intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : chartRing i ↦ (z : K)) h))

theorem overlapQuotient_homeomorph (i j : Fin 6) : IsHomeomorph (overlapQuotient i j) := by
  apply PrimeSpectrum.isHomeomorph_comap (invariantOverlapEmbedding i j).toRingHom
  · intro x
    refine ⟨5, by decide, ⟨powerMap L 5 field_fifth_power_invariant (x : K), ?_⟩, rfl⟩
    rw [← invariant_pair_eq_sup]
    exact (pairRing i j).pow_mem x.property 5
  · rw [(RingHom.injective_iff_ker_eq_bot _).mp ?_]
    · exact bot_le
    · intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ellPairRing i j ↦ (z : K)) h))

theorem resolvedQuotientMap_surjective : Function.Surjective resolvedQuotientMap := by
  intro y
  obtain ⟨i,a,rfl⟩ := quotient_chart_cover y
  obtain ⟨b,rfl⟩ := (chartQuotient_homeomorph i).surjective a
  refine ⟨chartInclusion i b, ?_⟩
  exact congrArg (fun f : chartSpec i ⟶ resolvedQuotient ↦ f b) (chartInclusion_quotient i)

theorem resolvedQuotientMap_injective : Function.Injective resolvedQuotientMap := by
  intro x y hxy
  obtain ⟨i,a,rfl⟩ := resolved_chart_cover x
  obtain ⟨j,b,rfl⟩ := resolved_chart_cover y
  have hq (l : Fin 6) (c : chartSpec l) :
      resolvedQuotientMap (chartInclusion l c) = quotientChartInclusion l (chartQuotient l c) :=
    congrArg (fun f : chartSpec l ⟶ resolvedQuotient ↦ f c) (chartInclusion_quotient l)
  rw [hq, hq] at hxy
  obtain ⟨z,hz₁,hz₂⟩ := (invariantAtlas.glueData.ι_eq_iff i j _ _).mp hxy
  obtain ⟨v,rfl⟩ := (overlapQuotient_homeomorph i j).surjective z
  apply (sixChartAtlas.glueData.ι_eq_iff i j a b).mpr
  refine ⟨v, ?_, ?_⟩
  · apply (chartQuotient_homeomorph i).injective
    have he := congrArg (fun f : pairSpec i j ⟶ invariantAtlas.chart i ↦ f v)
      (chartQuotient_left i j)
    exact he.trans hz₁
  · apply (chartQuotient_homeomorph j).injective
    have he := congrArg (fun f : pairSpec i j ⟶ invariantAtlas.chart j ↦ f v)
      (chartQuotient_right i j)
    exact he.trans hz₂

theorem quotient_chart_preimage (i : Fin 6) :
    resolvedQuotientMap ⁻¹ᵁ (quotientChartInclusion i).opensRange =
      (chartInclusion i).opensRange := by
  ext x
  change (∃ y, quotientChartInclusion i y = resolvedQuotientMap x) ↔
    ∃ z, chartInclusion i z = x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,rfl⟩ := (chartQuotient_homeomorph i).surjective y
    refine ⟨z, resolvedQuotientMap_injective ?_⟩
    exact (congrArg (fun f : chartSpec i ⟶ resolvedQuotient ↦ f z)
      (chartInclusion_quotient i)).trans hy
  · rintro ⟨z,rfl⟩
    exact ⟨chartQuotient i z,
      (congrArg (fun f : chartSpec i ⟶ resolvedQuotient ↦ f z)
        (chartInclusion_quotient i)).symm⟩

/-- Each local invariant-ring quotient is the actual restriction of the global morphism. -/
theorem quotient_chart_isPullback (i : Fin 6) :
    IsPullback (chartQuotient i) (chartInclusion i)
      (quotientChartInclusion i) resolvedQuotientMap :=
  IsOpenImmersion.isPullback _ _ _ _ (chartInclusion_quotient i) (quotient_chart_preimage i)

end
end Red61.Charts

/-! Boundary divisors as actual codimension-one points and algebraic cycles on
the six-chart schemes. No toric existence result is used. -/

namespace Red61.Charts

open Fields AlgebraicGeometry CategoryTheory Order
noncomputable section

theorem chartParameter_prime (i : Fin 6) (a : Fin 2) : Prime (chartParameter i a) :=
  (MulEquiv.prime_iff (chartPolynomialEquiv i)).mpr (MvPolynomial.X_prime (i := a))

def coordinatePrime (i : Fin 6) (a : Fin 2) : PrimeSpectrum (chartRing i) :=
  ⟨Ideal.span {chartParameter i a},
    (Ideal.span_singleton_prime (chartParameter_prime i a).ne_zero).mpr
      (chartParameter_prime i a)⟩

/-- The generic point of the boundary given by the indicated chart coordinate. -/
def boundaryPoint (i : Fin 6) (a : Fin 2) : resolvedScheme :=
  chartInclusion i (coordinatePrime i a)

end
end Red61.Charts

/-! The two exceptional codimension-one points and their images under the
actual contraction maps. All four local descriptions are covered. -/

namespace Red61.Contraction

open Fields Charts Fan AffineGluing AlgebraicGeometry CategoryTheory Order
noncomputable section
set_option backward.isDefEq.respectTransparency false

def coneRefinementMap (i : Fin 3) : chartSpec (exceptional i) ⟶ Spec (CommRingCat.of coneRing) :=
  specMap (cone_le_exceptional i)

theorem sigma_exceptional_chart (i : Fin 3) :
    chartInclusion (exceptional i) ≫ sigma =
      coneRefinementMap i ≫ contractedAtlas.chartInclusion (3 : Fin 4) := by
  fin_cases i
  · exact resolutionData.chartInclusion_gluedMap (1 : Fin 6)
  · exact resolutionData.chartInclusion_gluedMap (2 : Fin 6)
  · exact resolutionData.chartInclusion_gluedMap (4 : Fin 6)

theorem refinement_generator (i : Fin 3) (j : Fin 4) :
    Subalgebra.inclusion (cone_le_exceptional i) (coneRingEquiv (ConeRing.ag j)) =
      chartParameter (exceptional i) 0 ^ refinementCoefficients i j 0 *
        chartParameter (exceptional i) 1 ^ refinementCoefficients i j 1 := by
  apply Subtype.ext
  change ConeRing.evaluate (ConeRing.generator j) = _
  rw [cone_generator_image, refinement_certificate i j, combination, Fin.sum_univ_two]
  rw [monomial_mul, monomial_zsmul, monomial_zsmul]
  simp [chartParameter, chartCoordinates, y₁, y₂]

theorem refined_generator_mem (i : Fin 3) (a : Fin 2) (j : Fin 4)
    (h : 0 < refinementCoefficients i j a) :
    Subalgebra.inclusion (cone_le_exceptional i) (coneRingEquiv (ConeRing.ag j)) ∈
      (coordinatePrime (exceptional i) a).asIdeal := by
  rw [refinement_generator]
  let p := (coordinatePrime (exceptional i) a).asIdeal
  have ha : chartParameter (exceptional i) a ∈ p := Ideal.subset_span (by simp)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  fin_cases a
  · change refinementCoefficients i j 0 = n + 1 at hn
    rw [hn, pow_succ]
    exact p.mul_mem_right _ (p.mul_mem_left _ ha)
  · change refinementCoefficients i j 1 = n + 1 at hn
    rw [hn, pow_succ]
    exact p.mul_mem_left _ (p.mul_mem_left _ ha)

theorem sigma_boundary_eq_vertex (i : Fin 3) (a : Fin 2)
    (hu : 0 < refinementCoefficients i 0 a) (hr : 0 < refinementCoefficients i 3 a) :
    sigma (boundaryPoint (exceptional i) a) = P := by
  have hp : coneRefinementMap i (coordinatePrime (exceptional i) a) =
      coneIso.hom ConeRing.vertex := by
    apply cone_prime_eq_vertex
    · change Subalgebra.inclusion (cone_le_exceptional i) (coneDenominator 0) ∈
        (coordinatePrime (exceptional i) a).asIdeal
      rw [← coneDenominator_zero]
      exact refined_generator_mem i a 0 hu
    · change Subalgebra.inclusion (cone_le_exceptional i) (coneDenominator 2) ∈
        (coordinatePrime (exceptional i) a).asIdeal
      rw [← coneDenominator_two]
      exact refined_generator_mem i a 3 hr
  have he := congrArg (fun f : chartSpec (exceptional i) ⟶ X ↦
    f (coordinatePrime (exceptional i) a)) (sigma_exceptional_chart i)
  simpa only [Scheme.Hom.comp_apply, hp, boundaryPoint, P, coneOpen] using he

/-- Both chart descriptions of E₁ and both descriptions of E₂ are contracted. -/
theorem all_exceptional_charts_contract (j : Fin 4) :
    sigma (boundaryPoint (exceptionalCoordinate j).1 (exceptionalCoordinate j).2) = P := by
  fin_cases j
  · exact sigma_boundary_eq_vertex 0 1 (by decide) (by decide)
  · exact sigma_boundary_eq_vertex 1 1 (by decide) (by decide)
  · exact sigma_boundary_eq_vertex 1 0 (by decide) (by decide)
  · exact sigma_boundary_eq_vertex 2 1 (by decide) (by decide)

def exceptionalPoint₁ : resolvedScheme := boundaryPoint 1 1
theorem sigma_exceptionalPoint₁ : sigma exceptionalPoint₁ = P := all_exceptional_charts_contract 0
end
end Red61.Contraction

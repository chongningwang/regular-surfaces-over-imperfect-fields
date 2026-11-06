import Red61.Surface.Contraction

/-! # Properness of the resolved models

Formerly the modules `ResolutionFiniteness`, `ResolvedProperness`.
-/

/-! Finiteness and separation properties of the six-chart models and their
contractions. Properness of the contractions is reduced to properness of the
resolved models; no properness assertion for those models is assumed. -/

namespace Red61.Contraction

open Fields Charts AffineGluing FrobeniusDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem original_chart_finiteType_ell (i : Fin 6) : Algebra.FiniteType ell (ellChartRing i) := by
  change Algebra.FiniteType ell (chartRing i)
  exact Algebra.FiniteType.trans (S := k) inferInstance (original_chart_finiteType i)

theorem invariant_chart_finiteType (i : Fin 6) : Algebra.FiniteType ell (invariantChartRing i) := by
  have := original_chart_finiteType_ell i
  exact fixed_finiteType L 5 field_fifth_power_invariant (ellChartRing i)

instance resolved_separated : IsSeparated resolvedToBase := sixChartAtlas.toBase_separated
instance resolvedQuotient_separated : IsSeparated resolvedQuotientToBase := invariantAtlas.toBase_separated

instance resolved_finiteType : LocallyOfFiniteType resolvedToBase :=
  sixChartAtlas.toBase_locallyOfFiniteType original_chart_finiteType

instance resolvedQuotient_finiteType : LocallyOfFiniteType resolvedQuotientToBase :=
  invariantAtlas.toBase_locallyOfFiniteType invariant_chart_finiteType

instance resolvedQuotient_noetherian : IsNoetherian resolvedQuotient := by
  have : Finite invariantAtlas.glueData.openCover.I₀ := inferInstanceAs (Finite (Fin 6))
  have : ∀ i : invariantAtlas.glueData.openCover.I₀,
      IsAffine (invariantAtlas.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (invariantChartRing i))))
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := invariantAtlas.glueData.openCover)).mpr
  intro i
  have := invariant_chart_finiteType i
  have := Algebra.FiniteType.isNoetherianRing ell (invariantChartRing i)
  change IsNoetherianRing Γ(Spec (CommRingCat.of (invariantChartRing i)), ⊤)
  exact isNoetherianRing_of_ringEquiv (invariantChartRing i)
    (Scheme.ΓSpecIso (CommRingCat.of (invariantChartRing i))).symm.commRingCatIsoToRingEquiv

instance resolved_quasiCompact : QuasiCompact resolvedToBase := inferInstance
instance resolvedQuotient_quasiCompact : QuasiCompact resolvedQuotientToBase := inferInstance

instance chartQuotient_finite (i : Fin 6) : IsFinite (chartQuotient i) := by
  rw [chartQuotient, IsFinite.SpecMap_iff]
  have := original_chart_finiteType_ell i
  exact embed_finite L 5 field_fifth_power_invariant (ellChartRing i)

instance resolvedQuotientMap_finite : IsFinite resolvedQuotientMap := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) invariantAtlas.glueData.openCover
  intro i
  change IsFinite (pullback.snd resolvedQuotientMap (quotientChartInclusion i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (quotient_chart_isPullback i).flip.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  exact chartQuotient_finite i

instance resolvedQuotientMap_surjective_morphism : Surjective resolvedQuotientMap :=
  ⟨resolvedQuotientMap_surjective⟩

instance sigma_separated : IsSeparated sigma := by
  have : IsSeparated (sigma ≫ xToBase) := sigma_over_k ▸ resolved_separated
  exact IsSeparated.of_comp sigma xToBase

instance sigmaBar_separated : IsSeparated sigmaBar := by
  have : IsSeparated (sigmaBar ≫ sToBase) := sigmaBar_over_ell ▸ resolvedQuotient_separated
  exact IsSeparated.of_comp sigmaBar sToBase

instance sigma_finiteType : LocallyOfFiniteType sigma := by
  have : LocallyOfFiniteType (sigma ≫ xToBase) := sigma_over_k ▸ resolved_finiteType
  exact locallyOfFiniteType_of_comp sigma xToBase

instance sigmaBar_finiteType : LocallyOfFiniteType sigmaBar := by
  have : LocallyOfFiniteType (sigmaBar ≫ sToBase) := sigmaBar_over_ell ▸ resolvedQuotient_finiteType
  exact locallyOfFiniteType_of_comp sigmaBar sToBase

instance sigma_quasiCompact : QuasiCompact sigma := inferInstance
instance sigmaBar_quasiCompact : QuasiCompact sigmaBar := inferInstance

theorem sigma_proper_iff_resolved_proper : IsProper sigma ↔ IsProper resolvedToBase := by
  rw [← sigma_over_k]
  exact IsProper.comp_iff.symm

theorem sigmaBar_proper_iff_resolvedQuotient_proper :
    IsProper sigmaBar ↔ IsProper resolvedQuotientToBase := by
  rw [← sigmaBar_over_ell]
  exact IsProper.comp_iff.symm

theorem resolved_proper_iff : IsProper resolvedQuotientToBase ↔ IsProper resolvedToBase := by
  constructor
  · intro h
    have := h
    have : IsProper (resolvedToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ell k))) := by
      change IsProper resolvedToEll
      rw [← resolvedQuotient_over_ell]
      infer_instance
    exact IsProper.of_comp resolvedToBase (Spec.map (CommRingCat.ofHom (algebraMap ell k)))
  · intro h
    have := h
    have : UniversallyClosed (resolvedQuotientMap ≫ resolvedQuotientToBase) := by
      rw [resolvedQuotient_over_ell]
      change UniversallyClosed (resolvedToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ell k)))
      infer_instance
    have : UniversallyClosed resolvedQuotientToBase :=
      UniversallyClosed.of_comp_surjective resolvedQuotientMap resolvedQuotientToBase
    exact ⟨⟩

end
end Red61.Contraction

/-! Properness of both actual resolved models and both contraction morphisms,
obtained from the explicit six-vertex Proj comparison. -/

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry CategoryTheory
noncomputable section

def resolvedProjectiveIso : resolvedScheme ≅
    MonomialProjectiveModel.projectiveScheme ResolvedProjectiveModel.data :=
  MonomialProjectiveModel.projectiveIso ResolvedProjectiveModel.data

theorem resolvedProjectiveIso_over_base :
    resolvedProjectiveIso.hom ≫
      MonomialProjectiveModel.projectiveToBase ResolvedProjectiveModel.data = resolvedToBase :=
  MonomialProjectiveModel.projectiveIso_over_base ResolvedProjectiveModel.data

instance resolved_proper : IsProper resolvedToBase := by
  rw [← resolvedProjectiveIso_over_base]
  infer_instance

instance resolvedQuotient_proper : IsProper resolvedQuotientToBase :=
  resolved_proper_iff.mpr resolved_proper

instance sigma_proper : IsProper sigma := sigma_proper_iff_resolved_proper.mpr resolved_proper

instance sigmaBar_proper : IsProper sigmaBar :=
  sigmaBar_proper_iff_resolvedQuotient_proper.mpr resolvedQuotient_proper

end
end Red61.Contraction

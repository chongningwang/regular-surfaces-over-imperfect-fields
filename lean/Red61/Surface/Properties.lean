import Red61.Surface.ResolvedProperness

/-! # Regularity, dimension, normality and the final surface

Formerly the modules `KeptChartRegularity`, `ContractedRegularity`, `ContractedDimension`, `NormalLocalRings`, `RationalBaseSurface`.
-/

/-! Regularity of every stalk on the three affine quotient charts retained in S. -/

namespace Red61.Charts

open Fields PolynomialInvariants FieldLocalization AffineGluing
noncomputable section

theorem first_kernel_regular : IsRegularRing (kernelIn (localGenerator 0) firstRing) :=
  kernel_regular (localGenerator 0) straightFirst first_independent first_derivatives
    firstRing first_polynomial_le first_localization

theorem last_kernel_regular : IsRegularRing (kernelIn (localGenerator 5) lastRing) :=
  kernel_regular (localGenerator 5) straightLast last_independent last_derivatives
    lastRing last_polynomial_le last_localization

theorem middle_kernel_regular (a : F₅) :
    IsRegularRing (kernelIn (localGenerator 3) (middleRing a)) :=
  kernel_regular (localGenerator 3) (straightMiddle a) (middle_independent a)
    (middle_derivatives a) (middleRing a) (middle_polynomial_le a) (middle_localization a)

abbrev middleOriginal : Subalgebra F₅ K := (chartRing 3).restrictScalars F₅
abbrev middleKernel : Subalgebra F₅ K := kernelIn (localGenerator 3) middleOriginal

def middleKernelDenominator (a : F₅) : middleKernel :=
  kernelPower (localGenerator 3) middleOriginal ⟨middleDenominator a, middle_denominator_mem a⟩

theorem middle_kernel_localization (a : F₅) :
    letI := inclusionAlgebra
      (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from inf_le_inf_right _ le_sup_left)
    IsLocalization.Away (middleKernelDenominator a) (kernelIn (localGenerator 3) (middleRing a)) := by
  apply kernel_away (localGenerator 3) le_sup_left
    (⟨middleDenominator a,middle_denominator_mem a⟩ : middleOriginal)
  exact subalgebra_isLocalizationAway _ _ le_sup_left _ (middle_denominator_nonzero a)
    ((show Algebra.adjoin F₅ {(middleDenominator a)⁻¹} ≤ middleRing a from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_singleton _))) le_rfl

theorem middle_kernel_cover (p : PrimeSpectrum middleKernel) :
    ∃ a : F₅, middleKernelDenominator a ∉ p.asIdeal := by
  by_cases h0 : middleKernelDenominator 0 ∈ p.asIdeal
  · refine ⟨1, ?_⟩
    intro h1
    let b : middleOriginal := ⟨c₂, (constants_mem_chart 3).2⟩
    let b₅ : middleKernel := kernelPower (localGenerator 3) middleOriginal b
    let a₅ : middleKernel := kernelPower (localGenerator 3) middleOriginal (1-b)
    have he : a₅*middleKernelDenominator 0 + b₅*middleKernelDenominator 1 = 1 := by
      apply Subtype.ext
      change (1-c₂)^5*(middleDenominator 0)^5 + c₂^5*(middleDenominator 1)^5 = 1
      have h : (1-c₂)*middleDenominator 0 + c₂*middleDenominator 1 = 1 := by
        simp only [middleDenominator, middleSlice, map_zero, map_one, sub_zero]
        ring
      have hh := congrArg (frobenius K 5) h
      simpa only [map_add, map_mul, map_one, frobenius_def] using hh
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (he ▸ p.asIdeal.add_mem (p.asIdeal.mul_mem_left a₅ h0) (p.asIdeal.mul_mem_left b₅ h1))
      isUnit_one)
  · exact ⟨0,h0⟩

theorem middle_atPrime_regular (p : PrimeSpectrum middleKernel) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  obtain ⟨a,ha⟩ := middle_kernel_cover p
  let := inclusionAlgebra
    (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from inf_le_inf_right _ le_sup_left)
  have := middle_kernel_localization a
  have := middle_kernel_regular a
  exact atPrime_regular_of_away (A := kernelIn (localGenerator 3) (middleRing a))
    (middleKernelDenominator a) p ha

theorem middle_kernel_noetherian : IsNoetherianRing middleKernel := by
  classical
  let T : Finset middleKernel := Finset.univ.image middleKernelDenominator
  have hT : Ideal.span (T : Set middleKernel) = ⊤ := by
    by_contra hn
    obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨a,ha⟩ := middle_kernel_cover ⟨m,hm.isPrime⟩
    exact ha (hle (Ideal.subset_span (by simp [T])))
  apply AlgebraicGeometry.isNoetherianRing_of_away T hT
  intro s
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp s.property
  rw [← ha]
  let := inclusionAlgebra
    (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from inf_le_inf_right _ le_sup_left)
  have := middle_kernel_localization a
  have := middle_kernel_regular a
  exact isNoetherianRing_of_ringEquiv (kernelIn (localGenerator 3) (middleRing a))
    (IsLocalization.algEquiv (Submonoid.powers (middleKernelDenominator a))
      (kernelIn (localGenerator 3) (middleRing a))
      (Localization.Away (middleKernelDenominator a))).toRingEquiv

theorem middle_original_kernel_regular : IsRegularRing middleKernel := by
  have := middle_kernel_noetherian
  constructor
  intro p hp
  exact middle_atPrime_regular ⟨p,hp⟩

theorem field_chart_kernel (i : Fin 6) (x : K) : localGenerator i x = 0 ↔ x ∈ L := by
  change monomial (scale i)*delta x = 0 ↔ delta x = 0
  simp [mul_eq_zero, monomial_nonzero]

/-- Change only the presentation and scalar bookkeeping of the same invariant elements. -/
def chartKernelInEquiv (i : Fin 6) :
    kernelIn (localGenerator i) ((chartRing i).restrictScalars F₅) ≃+* invariantChartRing i where
  toFun x := ⟨⟨x.val,(field_chart_kernel i x.val).mp x.property.2⟩,x.property.1⟩
  invFun x := ⟨x.val.val,⟨x.property,(field_chart_kernel i x.val.val).mpr x.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem kept_kernel_regular (i : Fin 3) : IsRegularRing (invariantChartRing (Contraction.kept i)) := by
  have : IsRegularRing (kernelIn (localGenerator (Contraction.kept i))
      ((chartRing (Contraction.kept i)).restrictScalars F₅)) := by
    fin_cases i
    · exact first_kernel_regular
    · exact middle_original_kernel_regular
    · exact last_kernel_regular
  exact IsRegularRing.of_ringEquiv (chartKernelInEquiv (Contraction.kept i))

theorem kept_atPrime_regular (i : Fin 3) (p : PrimeSpectrum (invariantChartRing (Contraction.kept i))) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  apply atPrime_regular_of_equiv (chartKernelInEquiv (Contraction.kept i))
  intro q
  fin_cases i
  · exact @IsRegularRing.isRegularLocalRing_localization
      (kernelIn (localGenerator 0) firstRing) _ first_kernel_regular q.asIdeal q.isPrime
  · exact middle_atPrime_regular q
  · exact @IsRegularRing.isRegularLocalRing_localization
      (kernelIn (localGenerator 5) lastRing) _ last_kernel_regular q.asIdeal q.isPrime

end
end Red61.Charts

/-! Every stalk of the actual quotient scheme S is regular. No geometric
regularity criterion or flat-descent theorem is assumed. -/

namespace Red61.Contraction

open Fields Charts CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def keptInvariantEquiv (i : Fin 3) :
    quotientAtlas.ring i.castSucc ≃ₐ[ell] invariantChartRing (kept i) :=
  (keptKernelEquiv i).trans (invariantChartKernelEquiv (kept i)).symm

theorem kept_quotient_regular (i : Fin 3) : IsRegularRing (quotientAtlas.ring i.castSucc) := by
  have := kept_kernel_regular i
  exact IsRegularRing.of_ringEquiv (keptInvariantEquiv i).symm.toRingEquiv

theorem quotient_chart_noetherian (i : Fin 4) : IsNoetherianRing (quotientAtlas.ring i) := by
  fin_cases i
  · have := kept_quotient_regular (0 : Fin 3)
    exact inferInstanceAs (IsNoetherianRing (quotientAtlas.ring (0 : Fin 3).castSucc))
  · have := kept_quotient_regular (1 : Fin 3)
    exact inferInstanceAs (IsNoetherianRing (quotientAtlas.ring (1 : Fin 3).castSucc))
  · have := kept_quotient_regular (2 : Fin 3)
    exact inferInstanceAs (IsNoetherianRing (quotientAtlas.ring (2 : Fin 3).castSucc))
  · exact isNoetherianRing_of_ringEquiv ConeRing.affineInvariantRing coneInvariantEquiv.toRingEquiv

instance s_noetherian : IsNoetherian S := by
  have : Finite quotientAtlas.glueData.openCover.I₀ := inferInstanceAs (Finite (Fin 4))
  have : ∀ i : quotientAtlas.glueData.openCover.I₀,
      IsAffine (quotientAtlas.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (quotientAtlas.ring i))))
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := quotientAtlas.glueData.openCover)).mpr
  intro i
  have := quotient_chart_noetherian i
  change IsNoetherianRing Γ(Spec (CommRingCat.of (quotientAtlas.ring i)), ⊤)
  exact isNoetherianRing_of_ringEquiv (quotientAtlas.ring i)
    (Scheme.ΓSpecIso (CommRingCat.of (quotientAtlas.ring i))).symm.commRingCatIsoToRingEquiv

theorem kept_quotient_stalk_regular (i : Fin 3)
    (p : PrimeSpectrum (quotientAtlas.ring i.castSucc)) :
    IsRegularLocalRing ((quotientAtlas.chart i.castSucc).presheaf.stalk p) := by
  have := atPrime_regular_of_equiv (keptInvariantEquiv i).symm.toRingEquiv
    (kept_atPrime_regular i) p
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of (quotientAtlas.ring i.castSucc)) p).symm.commRingCatIsoToRingEquiv

/-- Regularity away from the contracted point, for the actual scheme S. -/
theorem s_stalk_regular_away (s : S) (hs : s ≠ s₀) :
    IsRegularLocalRing (S.presheaf.stalk s) := by
  obtain ⟨i,p,rfl⟩ := s_away_special_cover s hs
  have := kept_quotient_stalk_regular i p
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((quotientAtlas.chartInclusion i.castSucc).stalkMap p)).symm.commRingCatIsoToRingEquiv

/-- Combining the affine calculations with the independently proved special stalk. -/
theorem s_stalk_regular (s : S) : IsRegularLocalRing (S.presheaf.stalk s) := by
  classical
  by_cases hs : s = s₀
  · subst s
    exact s_special_stalk_regular
  · exact s_stalk_regular_away s hs

end
end Red61.Contraction

/-! The actual four-chart models X and S have global dimension two. -/

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem original_chart_dimension (i : Fin 6) : ringKrullDim (chartRing i) = 2 := by
  rw [← ringKrullDim_eq_of_ringEquiv (chartPolynomialEquiv i).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field k]
  norm_num

theorem s_stalk_dimension_le_two (s : S) : ringKrullDim (S.presheaf.stalk s) ≤ 2 := by
  by_cases hs : s = s₀
  · subst s
    exact s_special_stalk_dimension.le
  obtain ⟨x,rfl⟩ := pi_bijective.surjective s
  have hx : x ≠ P := fun h ↦ hs (h ▸ special_point_image)
  obtain ⟨i,p,rfl⟩ := x_away_special_cover x hx
  rw [stalk_dimension_eq_of_homeomorph pi pi_homeomorph]
  apply (stalk_dimension_le_of_affine_open
    (CommRingCat.of (contractedAtlas.ring i.castSucc))
    (contractedAtlas.chartInclusion i.castSucc) p).trans
  fin_cases i
  · exact (original_chart_dimension 0).le
  · exact (original_chart_dimension 3).le
  · exact (original_chart_dimension 5).le

/-- Global Krull dimension, not just the dimension of the distinguished stalk. -/
theorem s_dimension : topologicalKrullDim S = 2 := by
  apply le_antisymm
  · rw [scheme_dimension_eq_iSup_stalk]
    exact iSup_le s_stalk_dimension_le_two
  · rw [← s_special_stalk_dimension]
    exact stalk_dimension_le_scheme S s₀

end
end Red61.Contraction

/-! Normality of the resolved models, stated as integral closedness of every
actual scheme stalk, and DVRs at all codimension-one quotient points. -/

namespace Red61

open AlgebraicGeometry CategoryTheory Order
noncomputable section

namespace Charts

open Fields FrobeniusDescent

instance chartRing_isIntegrallyClosed (i : Fin 6) : IsIntegrallyClosed (chartRing i) :=
  IsIntegrallyClosed.of_equiv (chartPolynomialEquiv i).toRingEquiv

instance invariantChartRing_isIntegrallyClosed (i : Fin 6) :
    IsIntegrallyClosed (invariantChartRing i) := by
  have : IsIntegrallyClosed (ellChartRing i) := chartRing_isIntegrallyClosed i
  have : IsFractionRing (ellChartRing i) K := chart_isFractionRing i
  have : IsFractionRing (fixed L (ellChartRing i)) L := invariantChart_isFractionRing i
  exact fixed_isIntegrallyClosed L (ellChartRing i)

end Charts
end
end Red61

/-! Return the construction to the original rational coefficient field
F5(s1,s2), represented by k with renamed variables. Properness, global
constants and geometric nonreducedness use the fixed field isomorphism.
All conclusions in this module are unconditional. The canonical comparison
and optional projectivity results are kept in separate modules. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

theorem globalScalarMap_comp_specMap (F E : Type) [Field F] [Field E]
    {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of E)) (e : F →+* E) :
    globalScalarMap F (f ≫ Spec.map (CommRingCat.ofHom e)) =
      (globalScalarMap E f).comp e := by
  unfold globalScalarMap
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

namespace Contraction

open Fields

def rationalBaseIso : Spec (CommRingCat.of ell) ≅ Spec (CommRingCat.of k) :=
  Scheme.Spec.mapIso baseEquiv.toCommRingCatIso.op

def sToRationalBase : S ⟶ Spec (CommRingCat.of k) :=
  sToBase ≫ rationalBaseIso.hom

instance sToRationalBase_proper : IsProper sToRationalBase := by
  unfold sToRationalBase
  infer_instance

instance sToRationalBase_finiteType : LocallyOfFiniteType sToRationalBase := by
  unfold sToRationalBase
  infer_instance

theorem sToRationalBase_constants :
    Function.Bijective (globalScalarMap k sToRationalBase) := by
  change Function.Bijective
    (globalScalarMap k (sToBase ≫ Spec.map (CommRingCat.ofHom baseEquiv.toRingHom)))
  rw [globalScalarMap_comp_specMap]
  exact s_globalScalarMap_bijective.comp baseEquiv.bijective

theorem sToRationalBase_not_geometricallyReduced :
    ¬ GeometricallyReduced sToRationalBase := by
  intro h
  have hp : IsPullback (𝟙 S) sToBase sToRationalBase rationalBaseIso.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [sToRationalBase]⟩
  exact s_not_geometricallyReduced (MorphismProperty.of_isPullback hp h)

theorem proper_regular_surface_rationalBase_properties :
    IsProper sToRationalBase ∧ IsIntegral S ∧ IsNoetherian S ∧
      topologicalKrullDim S = 2 ∧
      (∀ s : S, IsRegularLocalRing (S.presheaf.stalk s)) ∧
      Function.Bijective (globalScalarMap k sToRationalBase) ∧
      ¬ GeometricallyReduced sToRationalBase :=
  ⟨sToRationalBase_proper, s_integral, s_noetherian, s_dimension, s_stalk_regular,
    sToRationalBase_constants, sToRationalBase_not_geometricallyReduced⟩

end Contraction
end
end Red61

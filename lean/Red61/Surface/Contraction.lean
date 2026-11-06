import Red61.Surface.Projective

/-! # Exceptional fibres and the contraction isomorphisms

Formerly the modules `ExceptionalSupports`, `ExceptionalFibers`, `ContractionAwayCover`, `ContractionAwayIso`.
-/

/-! The exceptional prime divisors as irreducible closed subsets, their images
in the invariant quotient, and contraction of their entire supports. -/

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem P_isClosed : IsClosed ({P} : Set X) := by
  let : IsJacobsonRing k := isJacobsonRing_iff_prime_eq.mpr fun I hI ↦ by
    rcases Ideal.eq_bot_or_top I with h | h
    · subst I
      let : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
      exact Ideal.jacobson_eq_self_of_isMaximal
    · exact (hI.ne_top h).elim
  let hbase : JacobsonSpace (Spec (CommRingCat.of k)) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp inferInstance
  let : JacobsonSpace X := @LocallyOfFiniteType.jacobsonSpace X
    (Spec (CommRingCat.of k)) xToBase x_finiteType hbase
  have hv : IsClosed ({ConeRing.vertex} : Set ConeRing.coneSpec) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal ConeRing.vertex).mpr
      (show ConeRing.maximal.IsMaximal from inferInstance)
  exact coneOpen.closePoints_subset_preimage_closedPoints hv

theorem s₀_isClosed : IsClosed ({s₀} : Set S) := by
  simpa only [Set.image_singleton, special_point_image] using
    pi.isClosedMap _ P_isClosed

end
end Red61.Contraction

/-! The complete set-theoretic exceptional fibers of both contractions.
The proof checks all six charts, including exclusion of the three surviving
charts, and transfers the result through the quotient homeomorphisms. -/

namespace Red61.Contraction

open Fields Charts Fan AffineGluing AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem cone_generator_mem_vertex (j : Fin 4) :
    coneRingEquiv (ConeRing.ag j) ∈ (coneIso.hom ConeRing.vertex).asIdeal := by
  change coneRingEquiv.symm (coneRingEquiv (ConeRing.ag j)) ∈ ConeRing.maximal
  rw [coneRingEquiv.symm_apply_apply]
  exact ConeRing.generator_residue_zero j

theorem coneDenominator_one : coneDenominator 1 = coneDenominator 0 * coneDenominator 2 := by
  apply Subtype.ext
  change monomial (5,-3) = monomial (0,-1) * monomial (5,-2)
  rw [← monomial_mul]
  rfl

theorem coneDenominator_mem_vertex (i : Fin 3) :
    coneDenominator i ∈ (coneIso.hom ConeRing.vertex).asIdeal := by
  change coneRingEquiv.symm (coneDenominator i) ∈ ConeRing.maximal
  fin_cases i
  · change coneRingEquiv.symm (coneDenominator (0 : Fin 3)) ∈ ConeRing.maximal
    rw [← coneDenominator_zero, coneRingEquiv.symm_apply_apply]
    exact ConeRing.generator_residue_zero 0
  · change coneRingEquiv.symm (coneDenominator (1 : Fin 3)) ∈ ConeRing.maximal
    rw [coneDenominator_one, map_mul, ← coneDenominator_zero,
      coneRingEquiv.symm_apply_apply]
    exact ConeRing.maximal.mul_mem_right _ (ConeRing.generator_residue_zero 0)
  · change coneRingEquiv.symm (coneDenominator (2 : Fin 3)) ∈ ConeRing.maximal
    rw [← coneDenominator_two, coneRingEquiv.symm_apply_apply]
    exact ConeRing.generator_residue_zero 3

theorem P_not_mem_chart_of_localization (j : Fin 4) (d : coneRing)
    (hloc : letI := inclusionAlgebra (show coneRing ≤ coneRing ⊔ contractedAtlas.ring j from le_sup_left)
      IsLocalization.Away d ↥(coneRing ⊔ contractedAtlas.ring j))
    (hd : d ∈ (coneIso.hom ConeRing.vertex).asIdeal) :
    P ∉ Set.range (contractedAtlas.chartInclusion j) := by
  intro h
  exact (contractedAtlas.point_in_chart_iff_of_localization (3 : Fin 4) j d hloc
    (coneIso.hom ConeRing.vertex)).mp h hd

/-- None of the surviving affine opens contains the contracted point. -/
theorem P_not_mem_kept_chart (i : Fin 3) :
    P ∉ Set.range (contractedAtlas.chartInclusion i.castSucc) := by
  fin_cases i
  · exact P_not_mem_chart_of_localization 0 (coneDenominator 0)
      (cone_pair_localization 0) (coneDenominator_mem_vertex 0)
  · exact P_not_mem_chart_of_localization 1 (coneDenominator 1)
      (cone_pair_localization 1) (coneDenominator_mem_vertex 1)
  · exact P_not_mem_chart_of_localization 2 (coneDenominator 2)
      (cone_pair_localization 2) (coneDenominator_mem_vertex 2)

theorem sigma_exceptional_fiber_iff (i : Fin 3)
    (p : PrimeSpectrum (chartRing (exceptional i))) :
    sigma (chartInclusion (exceptional i) p) = P ↔
      Subalgebra.inclusion (cone_le_exceptional i) (coneRingEquiv (ConeRing.ag 0)) ∈ p.asIdeal ∧
      Subalgebra.inclusion (cone_le_exceptional i) (coneRingEquiv (ConeRing.ag 3)) ∈ p.asIdeal := by
  have he := congrArg (fun f : chartSpec (exceptional i) ⟶ X ↦ f p)
    (sigma_exceptional_chart i)
  change sigma (chartInclusion (exceptional i) p) =
    contractedAtlas.chartInclusion (3 : Fin 4) (coneRefinementMap i p) at he
  rw [he]
  change contractedAtlas.chartInclusion (3 : Fin 4) (coneRefinementMap i p) =
    contractedAtlas.chartInclusion (3 : Fin 4) (coneIso.hom ConeRing.vertex) ↔ _
  rw [(contractedAtlas.chartInclusion (3 : Fin 4)).isOpenEmbedding.injective.eq_iff]
  constructor
  · intro h
    have h0 := h ▸ cone_generator_mem_vertex 0
    have h3 := h ▸ cone_generator_mem_vertex 3
    exact ⟨h0,h3⟩
  · rintro ⟨h0,h3⟩
    apply cone_prime_eq_vertex
    · change Subalgebra.inclusion (cone_le_exceptional i) (coneDenominator 0) ∈ p.asIdeal
      rwa [← coneDenominator_zero]
    · change Subalgebra.inclusion (cone_le_exceptional i) (coneDenominator 2) ∈ p.asIdeal
      rwa [← coneDenominator_two]

theorem sigma_fiber_chart_one (p : PrimeSpectrum (chartRing 1)) :
    sigma (chartInclusion 1 p) = P ↔ chartParameter 1 1 ∈ p.asIdeal := by
  refine (sigma_exceptional_fiber_iff (0 : Fin 3) p).trans ?_
  rw [refinement_generator, refinement_generator]
  change (chartParameter 1 0 ^ 0 * chartParameter 1 1 ^ 1 ∈ p.asIdeal ∧
    chartParameter 1 0 ^ 5 * chartParameter 1 1 ^ 2 ∈ p.asIdeal) ↔ _
  simp only [pow_zero, pow_one, one_mul]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, p.asIdeal.mul_mem_left _ ((p.isPrime.pow_mem_iff_mem 2 (by decide)).mpr h)⟩

theorem sigma_fiber_chart_two (p : PrimeSpectrum (chartRing 2)) :
    sigma (chartInclusion 2 p) = P ↔
      chartParameter 2 0 ∈ p.asIdeal ∨ chartParameter 2 1 ∈ p.asIdeal := by
  refine (sigma_exceptional_fiber_iff (1 : Fin 3) p).trans ?_
  rw [refinement_generator, refinement_generator]
  change (chartParameter 2 0 ^ 3 * chartParameter 2 1 ^ 1 ∈ p.asIdeal ∧
    chartParameter 2 0 ^ 1 * chartParameter 2 1 ^ 2 ∈ p.asIdeal) ↔ _
  simp only [pow_one, p.isPrime.mul_mem_iff_mem_or_mem,
    p.isPrime.pow_mem_iff_mem 3 (by decide), p.isPrime.pow_mem_iff_mem 2 (by decide), and_self]

theorem sigma_fiber_chart_four (p : PrimeSpectrum (chartRing 4)) :
    sigma (chartInclusion 4 p) = P ↔ chartParameter 4 1 ∈ p.asIdeal := by
  refine (sigma_exceptional_fiber_iff (2 : Fin 3) p).trans ?_
  rw [refinement_generator, refinement_generator]
  change (chartParameter 4 0 ^ 5 * chartParameter 4 1 ^ 3 ∈ p.asIdeal ∧
    chartParameter 4 0 ^ 0 * chartParameter 4 1 ^ 1 ∈ p.asIdeal) ↔ _
  simp only [pow_zero, pow_one, one_mul]
  constructor
  · exact And.right
  · intro h
    exact ⟨p.asIdeal.mul_mem_left _ ((p.isPrime.pow_mem_iff_mem 3 (by decide)).mpr h), h⟩

theorem sigma_common_chart_three :
    chartInclusion 3 ≫ sigma = contractedAtlas.chartInclusion (1 : Fin 4) := by
  change sixChartAtlas.chartInclusion (3 : Fin 6) ≫ resolutionData.gluedMap = _
  rw [resolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (chartRing 3)) ≫ contractedAtlas.chartInclusion (1 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

theorem sigma_common_chart_five :
    chartInclusion 5 ≫ sigma = contractedAtlas.chartInclusion (2 : Fin 4) := by
  change sixChartAtlas.chartInclusion (5 : Fin 6) ≫ resolutionData.gluedMap = _
  rw [resolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (chartRing 5)) ≫ contractedAtlas.chartInclusion (2 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

end
end Red61.Contraction

/-! The three surviving charts cover exactly the complements of the exceptional
fibers, on both sides of the quotient diagram. -/

namespace Red61.Contraction

open Fields Charts Fan AffineGluing AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem chart_one_zero_localization :
    letI := pairAlgebra 1 0
    IsLocalization.Away (chartParameter 1 1) (pairRing 1 0) := by
  apply pair_localization_of_eq
  · change (chartPolynomialEquiv 1 (MvPolynomial.X 1) : K) ≠ 0
    rw [chartPolynomialEquiv_X]
    exact monomial_nonzero _
  · have h := overlap_adjoin_inverse 5 0
    change chartRing 1 ⊔ chartRing 0 =
      chartRing 1 ⊔ Algebra.adjoin k ({(chartCoordinates 1 1)⁻¹} : Set K) at h
    simpa only [pairRing, chartParameter, chartPolynomialEquiv_X] using h

theorem chart_four_five_localization :
    letI := pairAlgebra 4 5
    IsLocalization.Away (chartParameter 4 1) (pairRing 4 5) := by
  apply pair_localization_of_eq
  · change (chartPolynomialEquiv 4 (MvPolynomial.X 1) : K) ≠ 0
    rw [chartPolynomialEquiv_X]
    exact monomial_nonzero _
  · change chartRing 4 ⊔ chartRing 5 = _
    rw [sup_comm]
    have h := overlap_adjoin_inverse 2 1
    change chartRing 5 ⊔ chartRing 4 =
      chartRing 4 ⊔ Algebra.adjoin k ({(chartCoordinates 4 1)⁻¹} : Set K) at h
    simpa only [chartParameter, chartPolynomialEquiv_X] using h

theorem sigma_kept_ne_P (i : Fin 3) (p : PrimeSpectrum (chartRing (kept i))) :
    sigma (chartInclusion (kept i) p) ≠ P := by
  fin_cases i
  · intro h
    have he := congrArg (fun f : chartSpec 0 ⟶ X ↦ f p) sigma_common_chart
    exact P_not_mem_kept_chart 0 ⟨p,he.symm.trans h⟩
  · intro h
    have he := congrArg (fun f : chartSpec 3 ⟶ X ↦ f p) sigma_common_chart_three
    exact P_not_mem_kept_chart 1 ⟨p,he.symm.trans h⟩
  · intro h
    have he := congrArg (fun f : chartSpec 5 ⟶ X ↦ f p) sigma_common_chart_five
    exact P_not_mem_kept_chart 2 ⟨p,he.symm.trans h⟩

theorem resolved_away_special_cover (x : resolvedScheme) (hx : sigma x ≠ P) :
    ∃ (i : Fin 3) (p : PrimeSpectrum (chartRing (kept i))), chartInclusion (kept i) p = x := by
  obtain ⟨i,p,rfl⟩ := resolved_chart_cover x
  fin_cases i
  · exact ⟨0,p,rfl⟩
  · obtain ⟨q,hq⟩ := sixChartAtlas.point_in_chart_of_localization (1 : Fin 6) (0 : Fin 6)
      (chartParameter 1 1) chart_one_zero_localization p
      (fun hp ↦ hx ((sigma_fiber_chart_one p).mpr hp))
    exact ⟨0,q,hq⟩
  · have hd : torusDenominator 2 = chartParameter 2 0 * chartParameter 2 1 := by
      apply Subtype.ext
      simp only [torusDenominator, chartParameter, Subalgebra.coe_mul,
        chartPolynomialEquiv_X]
      rfl
    have hn : torusDenominator 2 ∉ p.asIdeal := by
      rw [hd]
      intro hm
      exact hx ((sigma_fiber_chart_two p).mpr (p.isPrime.mem_or_mem hm))
    obtain ⟨q,hq⟩ := sixChartAtlas.point_in_chart_of_localization (2 : Fin 6) (0 : Fin 6)
      (torusDenominator 2) (nonAdjacent_pair_isLocalization 2 0 (by decide)) p hn
    exact ⟨0,q,hq⟩
  · exact ⟨1,p,rfl⟩
  · obtain ⟨q,hq⟩ := sixChartAtlas.point_in_chart_of_localization (4 : Fin 6) (5 : Fin 6)
      (chartParameter 4 1) chart_four_five_localization p
      (fun hp ↦ hx ((sigma_fiber_chart_four p).mpr hp))
    exact ⟨2,q,hq⟩
  · exact ⟨2,p,rfl⟩

theorem resolved_kept_union :
    (⋃ i : Fin 3, Set.range (chartInclusion (kept i))) = (sigma ⁻¹' {P})ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,p,rfl⟩ := Set.mem_iUnion.mp hx
    exact sigma_kept_ne_P i p
  · exact fun hx ↦ Set.mem_iUnion.mpr (resolved_away_special_cover x hx)

theorem x_kept_union :
    (⋃ i : Fin 3, Set.range (contractedAtlas.chartInclusion i.castSucc)) = ({P} : Set X)ᶜ := by
  ext x
  constructor
  · intro hx he
    obtain ⟨i,p,hp⟩ := Set.mem_iUnion.mp hx
    exact P_not_mem_kept_chart i ⟨p,hp.trans he⟩
  · exact fun hx ↦ Set.mem_iUnion.mpr (x_away_special_cover x hx)

theorem s₀_not_mem_kept_chart (i : Fin 3) :
    s₀ ∉ Set.range (quotientAtlas.chartInclusion i.castSucc) := by
  intro h
  have hp : P ∈ pi ⁻¹ᵁ (quotientAtlas.chartInclusion i.castSucc).opensRange := by
    change pi P ∈ Set.range (quotientAtlas.chartInclusion i.castSucc)
    rwa [special_point_image]
  have he := AtlasDescent.chart_preimage (R := ell) contractedAtlas L 5
    field_fifth_power_invariant i.castSucc
  change pi ⁻¹ᵁ (quotientAtlas.chartInclusion i.castSucc).opensRange =
    (contractedAtlas.chartInclusion i.castSucc).opensRange at he
  rw [he] at hp
  exact P_not_mem_kept_chart i hp

theorem s_kept_union :
    (⋃ i : Fin 3, Set.range (quotientAtlas.chartInclusion i.castSucc)) = ({s₀} : Set S)ᶜ := by
  ext s
  constructor
  · intro hs he
    obtain ⟨i,p,hp⟩ := Set.mem_iUnion.mp hs
    exact s₀_not_mem_kept_chart i ⟨p,hp.trans he⟩
  · exact fun hs ↦ Set.mem_iUnion.mpr (s_away_special_cover s hs)

theorem resolvedQuotient_kept_union :
    (⋃ i : Fin 3, Set.range (quotientChartInclusion (kept i))) =
      (sigmaBar ⁻¹' {s₀})ᶜ := by
  ext y
  obtain ⟨x,rfl⟩ := resolvedQuotientMap_surjective y
  have he (i : Fin 3) :
      resolvedQuotientMap x ∈ Set.range (quotientChartInclusion (kept i)) ↔
        x ∈ Set.range (chartInclusion (kept i)) := by
    exact (show x ∈ resolvedQuotientMap ⁻¹ᵁ (quotientChartInclusion (kept i)).opensRange ↔
      x ∈ (chartInclusion (kept i)).opensRange from
      Iff.of_eq (congrArg (fun U : resolvedScheme.Opens ↦ x ∈ U) (quotient_chart_preimage (kept i))))
  have hs : sigmaBar (resolvedQuotientMap x) = pi (sigma x) :=
    (congrArg (fun f : resolvedScheme ⟶ S ↦ f x) quotient_contraction_square).symm
  simp only [Set.mem_iUnion, he]
  change (∃ i : Fin 3, x ∈ Set.range (chartInclusion (kept i))) ↔
    sigmaBar (resolvedQuotientMap x) ≠ s₀
  rw [hs, ← special_point_image, ne_eq, pi_bijective.injective.eq_iff]
  exact (Set.mem_iUnion).symm.trans (Set.ext_iff.mp resolved_kept_union x)

theorem sigma_surjective : Function.Surjective sigma := by
  intro x
  by_cases hx : x = P
  · exact ⟨exceptionalPoint₁, sigma_exceptionalPoint₁.trans hx.symm⟩
  · obtain ⟨i,p,rfl⟩ := x_away_special_cover x hx
    fin_cases i
    · exact ⟨chartInclusion 0 p,
        congrArg (fun f : chartSpec 0 ⟶ X ↦ f p) sigma_common_chart⟩
    · exact ⟨chartInclusion 3 p,
        congrArg (fun f : chartSpec 3 ⟶ X ↦ f p) sigma_common_chart_three⟩
    · exact ⟨chartInclusion 5 p,
        congrArg (fun f : chartSpec 5 ⟶ X ↦ f p) sigma_common_chart_five⟩

instance sigma_surjective_morphism : Surjective sigma := ⟨sigma_surjective⟩

theorem sigmaBar_surjective : Function.Surjective sigmaBar := by
  intro s
  obtain ⟨x,rfl⟩ := pi_bijective.surjective s
  obtain ⟨y,rfl⟩ := sigma_surjective x
  exact ⟨resolvedQuotientMap y,
    (congrArg (fun f : resolvedScheme ⟶ S ↦ f y) quotient_contraction_square).symm⟩

instance sigmaBar_surjective_morphism : Surjective sigmaBar := ⟨sigmaBar_surjective⟩

end
end Red61.Contraction

/-! Both contractions are actual scheme isomorphisms away from their complete
exceptional fibers. The isomorphisms preserve the stated base-field maps. -/

namespace Red61.Contraction

open Fields Charts AffineGluing AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

def commonAtlas : PrincipalAtlas k K := sixChartAtlas.reindex kept

theorem common_chart_eq (i : Fin 3) :
    contractedAtlas.ring i.castSucc = commonAtlas.ring i := by
  fin_cases i <;> rfl

def commonToResolved : commonAtlas.glued ⟶ resolvedScheme :=
  (PrincipalAtlas.ringEqMapData commonAtlas sixChartAtlas kept (fun _ ↦ rfl)).gluedMap

def commonToX : commonAtlas.glued ⟶ X :=
  (PrincipalAtlas.ringEqMapData commonAtlas contractedAtlas Fin.castSucc common_chart_eq).gluedMap

instance commonToResolved_open : IsOpenImmersion commonToResolved :=
  PrincipalAtlas.ringEqMapData_open _ _ _ _

instance commonToX_open : IsOpenImmersion commonToX :=
  PrincipalAtlas.ringEqMapData_open _ _ _ _

theorem common_contraction_chart (i : Fin 3) :
    commonAtlas.chartInclusion i ≫ commonToResolved ≫ sigma =
      commonAtlas.chartInclusion i ≫ commonToX := by
  simp only [commonToResolved, commonToX, PrincipalAtlas.MapData.chartInclusion_gluedMap_assoc,
    PrincipalAtlas.MapData.chartInclusion_gluedMap]
  fin_cases i
  · change specMap (le_refl (chartRing 0)) ≫ chartInclusion 0 ≫ sigma =
      specMap (le_refl (chartRing 0)) ≫ contractedAtlas.chartInclusion (0 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigma_common_chart
  · change specMap (le_refl (chartRing 3)) ≫ chartInclusion 3 ≫ sigma =
      specMap (le_refl (chartRing 3)) ≫ contractedAtlas.chartInclusion (1 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigma_common_chart_three
  · change specMap (le_refl (chartRing 5)) ≫ chartInclusion 5 ≫ sigma =
      specMap (le_refl (chartRing 5)) ≫ contractedAtlas.chartInclusion (2 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigma_common_chart_five

theorem common_contraction : commonToResolved ≫ sigma = commonToX := by
  apply commonAtlas.glueData.openCover.hom_ext
  exact common_contraction_chart

theorem commonToResolved_range : Set.range commonToResolved = (sigma ⁻¹' {P})ᶜ :=
  (PrincipalAtlas.ringEqMapData_range commonAtlas sixChartAtlas kept (fun _ ↦ rfl)).trans
    resolved_kept_union

theorem commonToX_range : Set.range commonToX = ({P} : Set X)ᶜ :=
  (PrincipalAtlas.ringEqMapData_range commonAtlas contractedAtlas Fin.castSucc
    common_chart_eq).trans x_kept_union

def xAway : X.Opens := ⟨({P} : Set X)ᶜ, P_isClosed.isOpen_compl⟩

instance sigma_away_isIso : IsIso (sigma ∣_ xAway) :=
  isIso_restrict_of_common_open sigma commonToResolved commonToX common_contraction xAway
    commonToResolved_range commonToX_range

def quotientCommonAtlas : PrincipalAtlas ell L := invariantAtlas.reindex kept

theorem quotient_common_chart_eq (i : Fin 3) :
    quotientAtlas.ring i.castSucc = quotientCommonAtlas.ring i := by
  fin_cases i <;> rfl

def commonToResolvedQuotient : quotientCommonAtlas.glued ⟶ resolvedQuotient :=
  (PrincipalAtlas.ringEqMapData quotientCommonAtlas invariantAtlas kept (fun _ ↦ rfl)).gluedMap

def commonToS : quotientCommonAtlas.glued ⟶ S :=
  (PrincipalAtlas.ringEqMapData quotientCommonAtlas quotientAtlas Fin.castSucc
    quotient_common_chart_eq).gluedMap

instance commonToResolvedQuotient_open : IsOpenImmersion commonToResolvedQuotient :=
  PrincipalAtlas.ringEqMapData_open _ _ _ _

instance commonToS_open : IsOpenImmersion commonToS :=
  PrincipalAtlas.ringEqMapData_open _ _ _ _

theorem sigmaBar_common_chart_three :
    quotientChartInclusion 3 ≫ sigmaBar = quotientAtlas.chartInclusion (1 : Fin 4) := by
  change invariantAtlas.chartInclusion (3 : Fin 6) ≫ quotientResolutionData.gluedMap = _
  rw [quotientResolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (invariantChartRing 3)) ≫ quotientAtlas.chartInclusion (1 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

theorem sigmaBar_common_chart_five :
    quotientChartInclusion 5 ≫ sigmaBar = quotientAtlas.chartInclusion (2 : Fin 4) := by
  change invariantAtlas.chartInclusion (5 : Fin 6) ≫ quotientResolutionData.gluedMap = _
  rw [quotientResolutionData.chartInclusion_gluedMap]
  change specMap (le_refl (invariantChartRing 5)) ≫ quotientAtlas.chartInclusion (2 : Fin 4) = _
  simp only [specMap_refl, Category.id_comp]

theorem quotient_common_contraction_chart (i : Fin 3) :
    quotientCommonAtlas.chartInclusion i ≫ commonToResolvedQuotient ≫ sigmaBar =
      quotientCommonAtlas.chartInclusion i ≫ commonToS := by
  simp only [commonToResolvedQuotient, commonToS,
    PrincipalAtlas.MapData.chartInclusion_gluedMap_assoc,
    PrincipalAtlas.MapData.chartInclusion_gluedMap]
  fin_cases i
  · change specMap (le_refl (invariantChartRing 0)) ≫ quotientChartInclusion 0 ≫ sigmaBar =
      specMap (le_refl (invariantChartRing 0)) ≫ quotientAtlas.chartInclusion (0 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigmaBar_common_chart
  · change specMap (le_refl (invariantChartRing 3)) ≫ quotientChartInclusion 3 ≫ sigmaBar =
      specMap (le_refl (invariantChartRing 3)) ≫ quotientAtlas.chartInclusion (1 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigmaBar_common_chart_three
  · change specMap (le_refl (invariantChartRing 5)) ≫ quotientChartInclusion 5 ≫ sigmaBar =
      specMap (le_refl (invariantChartRing 5)) ≫ quotientAtlas.chartInclusion (2 : Fin 4)
    simpa only [specMap_refl, Category.id_comp] using sigmaBar_common_chart_five

theorem quotient_common_contraction : commonToResolvedQuotient ≫ sigmaBar = commonToS := by
  apply quotientCommonAtlas.glueData.openCover.hom_ext
  exact quotient_common_contraction_chart

theorem commonToResolvedQuotient_range :
    Set.range commonToResolvedQuotient = (sigmaBar ⁻¹' {s₀})ᶜ :=
  (PrincipalAtlas.ringEqMapData_range quotientCommonAtlas invariantAtlas kept (fun _ ↦ rfl)).trans
    resolvedQuotient_kept_union

theorem commonToS_range : Set.range commonToS = ({s₀} : Set S)ᶜ :=
  (PrincipalAtlas.ringEqMapData_range quotientCommonAtlas quotientAtlas Fin.castSucc
    quotient_common_chart_eq).trans s_kept_union

def sAway : S.Opens := ⟨({s₀} : Set S)ᶜ, s₀_isClosed.isOpen_compl⟩

instance sigmaBar_away_isIso : IsIso (sigmaBar ∣_ sAway) :=
  isIso_restrict_of_common_open sigmaBar commonToResolvedQuotient commonToS
    quotient_common_contraction sAway commonToResolvedQuotient_range commonToS_range

end
end Red61.Contraction

import Mathlib.RingTheory.Kaehler.Basic
import Red61.AlgebraicGeometry.RationalForms.Lattices
import Red61.Surface.Properties

/-! # Invariant-field coordinates and the exceptional coordinate changes

Formerly the modules `DifferentialBasisCoordinates`, `InvariantCoefficientLifts`, `InvariantCoefficientSection`, `InvariantLocalDifferentialFiniteness`, `InvariantRationalCoordinates`, `ExceptionalFirstDifferentials`, `ExceptionalSecondCoordinates`, `ExceptionalSecondDifferentials`, `ExceptionalChartCoordinates`, `InvariantRationalField`, `ExceptionalKernelEmbedding`, `InvariantFieldDifferentials`, `KeptCoordinateJacobians`.
-/

/-! Coordinate formulas for the constructed differential bases. These keep
track of the actual differentials through polynomial localization. -/

namespace Red61

open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem differentialBasisOfFormallyEtale_apply (R A B ι : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Algebra.FormallyEtale A B]
    (b : Basis ι A (KaehlerDifferential R A)) (i : ι) :
    differentialBasisOfFormallyEtale R A B ι b i =
      KaehlerDifferential.map R R A B (b i) := by
  simp [differentialBasisOfFormallyEtale,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]

theorem differentialBasisOfLocalization_apply (R A B ι : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (M : Submonoid A) [IsLocalization M B]
    (b : Basis ι A (KaehlerDifferential R A)) (i : ι) :
    differentialBasisOfLocalization R A B ι M b i =
      KaehlerDifferential.map R R A B (b i) := by
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) M
  exact differentialBasisOfFormallyEtale_apply R A B ι b i

theorem differentialBasisOfRingEquiv_apply_D (R : Type*) {A B ι : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃+* B) (he : e.toRingHom.comp (algebraMap R A) = algebraMap R B)
    (b : Basis ι A (KaehlerDifferential R A)) (v : ι → A)
    (hv : ∀ i, b i = KaehlerDifferential.D R A (v i)) (i : ι) :
    differentialBasisOfRingEquiv R e he b i = KaehlerDifferential.D R B (e (v i)) := by
  let := e.toRingHom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' he.symm
  have : Algebra.FormallyEtale A B := formallyEtale_of_bijective A B e.bijective
  change differentialBasisOfFormallyEtale R A B ι b i = _
  rw [differentialBasisOfFormallyEtale_apply, hv, KaehlerDifferential.map_D]
  rfl

theorem absoluteDifferentialBasisOfRingEquiv_apply_D {A B ι : Type*}
    [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (e : A ≃+* B) (b : Basis ι A (KaehlerDifferential ℤ A)) (v : ι → A)
    (hv : ∀ i, b i = KaehlerDifferential.D ℤ A (v i)) (i : ι) :
    absoluteDifferentialBasisOfRingEquiv e b i = KaehlerDifferential.D ℤ B (e (v i)) :=
  differentialBasisOfRingEquiv_apply_D ℤ e (Subsingleton.elim _ _) b v hv i

end
end Red61

namespace Red61.PolynomialInvariants

open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP F 5] [CharP K 5]

def powerKernelCoordinate (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A) (i : Fin 4) : kernelIn D A :=
  ⟨powerCoordinates v i, powerPolynomial_le_kernel D v hi hv A hle
    (Algebra.subset_adjoin (Set.mem_range_self i))⟩

theorem polynomialKernelDifferentialBasis_apply (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A)
    (hloc : A ≤ FieldLocalization.hull (polynomialRing v) A) (i : Fin 4) :
    polynomialKernelDifferentialBasis D v hi hv A hle hloc i =
      KaehlerDifferential.D F (kernelIn D A) (powerKernelCoordinate D v hi hv A hle i) := by
  let P := polynomialRing (F := F) (powerCoordinates v)
  let C := kernelIn D A
  have hPC : P ≤ C := powerPolynomial_le_kernel D v hi hv A hle
  let := AffineGluing.inclusionAlgebra hPC
  have : IsScalarTower F P C := IsScalarTower.of_algHom (Subalgebra.inclusion hPC)
  have : IsLocalization (FieldLocalization.denominators hPC) C :=
    FieldLocalization.isLocalization hPC (kernel_le_hull D v hi hv A hloc)
  let e := (powerCoordinates_independent hi).aevalEquiv
  rw [polynomialKernelDifferentialBasis, differentialBasisOfLocalization_apply]
  simp only [polynomialRing] at *
  rw [differentialBasisOfRingEquiv_apply_D F e.toRingEquiv e.toAlgHom.comp_algebraMap
      (KaehlerDifferential.mvPolynomialBasis F (Fin 4)) MvPolynomial.X
      (fun j ↦ KaehlerDifferential.mvPolynomialBasis_apply F (Fin 4) j),
    KaehlerDifferential.map_D]
  congr 1
  apply Subtype.ext
  exact (powerCoordinates_independent hi).algebraMap_aevalEquiv (MvPolynomial.X i)
    |>.trans (MvPolynomial.aeval_X _ _)

end
end Red61.PolynomialInvariants

/-! Explicit lifts of the residue variables into the invariant local ring.
These lifts belong to B and map to q1,q2 in the fixed function field. They
do not turn the original embedding of k into a scalar field of B. -/

namespace Red61.ConeRing

open Fields LocalCoordinates
noncomputable section

instance local_charFive : CharP R 5 :=
  charP_of_injective_algebraMap (algebraMap k R).injective 5

instance invariant_charFive : CharP B 5 :=
  charP_of_injective_algebraMap (algebraMap F₅ B).injective 5

@[simp] theorem localEmbed_coefficient (a : k) :
    localEmbed (algebraMap k R a) = includeK a := by
  rw [IsScalarTower.algebraMap_apply k A R, localEmbed_algebraMap]
  exact embed_coefficient a

def shiftedCoefficientR (i : Fin 2) : R :=
  algebraMap k R (c i) - ![localGenerator 1, 3 * localGenerator 2] i

theorem shiftedCoefficientR_embedding (i : Fin 2) :
    localEmbed (shiftedCoefficientR i) = ![q₁,q₂] i := by
  fin_cases i <;>
    simp [shiftedCoefficientR, q₁, q₂, includeK_c, map_ofNat localEmbed 3, mul_assoc]

theorem shiftedCoefficientR_invariant (i : Fin 2) : localD (shiftedCoefficientR i) = 0 := by
  apply localEmbed_injective
  rw [localEmbed_D, shiftedCoefficientR_embedding, map_zero]
  fin_cases i <;> simp

def shiftedCoefficient (i : Fin 2) : B :=
  ⟨shiftedCoefficientR i, shiftedCoefficientR_invariant i⟩

@[simp] theorem shiftedCoefficient_embedding (i : Fin 2) :
    (invariantEmbedding (shiftedCoefficient i) : K) = ![q₁,q₂] i :=
  shiftedCoefficientR_embedding i

@[simp] theorem shiftedCoefficient_residue (i : Fin 2) :
    residueB (shiftedCoefficient i) = c i := by
  change localResidue (shiftedCoefficientR i) = c i
  fin_cases i <;> simp [shiftedCoefficientR, localResidue.commutes]

@[simp] theorem invariantEmbedding_scalar (a : ell) :
    (invariantEmbedding (algebraMap ell B a) : K) = algebraMap ell K a :=
  localEmbed.commutes a

end
end Red61.ConeRing

/-! A concrete copy of the rational residue field inside B. This is a named
ring section of the residue map, distinct from the prescribed ell-scalars. -/

namespace Red61.ConeRing

open Fields LocalCoordinates
noncomputable section

def shiftedPolynomial : P₂ →ₐ[F₅] B := MvPolynomial.aeval shiftedCoefficient

theorem residue_shiftedPolynomial :
    residueB.toRingHom.comp shiftedPolynomial.toRingHom = algebraMap P₂ k := by
  ext i
  · exact RingHom.congr_fun (Subsingleton.elim _ _) i
  · simp [shiftedPolynomial, c]

def coefficientSection : k →+* B :=
  rationalResidueSection shiftedPolynomial.toRingHom residueB.toRingHom
    residueB_surjective residue_shiftedPolynomial

@[simp] theorem coefficientSection_polynomial (p : P₂) :
    coefficientSection (algebraMap P₂ k p) = shiftedPolynomial p :=
  rationalResidueSection_algebraMap _ _ _ _ p

@[simp] theorem coefficientSection_variable (i : Fin 2) :
    coefficientSection (c i) = shiftedCoefficient i := by
  simp [c, shiftedPolynomial]

@[simp] theorem residue_coefficientSection (a : k) :
    residueB (coefficientSection a) = a :=
  residue_rationalResidueSection _ _ _ _ a

theorem coefficientSection_variable_embedding (i : Fin 2) :
    (invariantEmbedding (coefficientSection (c i)) : K) = ![q₁,q₂] i := by
  rw [coefficientSection_variable, shiftedCoefficient_embedding]

end
end Red61.ConeRing

/-! The actual invariant local ring is essentially of finite type over the
integers. In particular its absolute differential module is finite. -/

namespace Red61

open Fields
noncomputable section

theorem rationalConstants_essFiniteType_int : Algebra.EssFiniteType ℤ k := by
  have h₀ : (algebraMap ℤ F₅).EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ ZMod.intCast_surjective).essFiniteType
  have h₁ : (algebraMap F₅ P₂).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr inferInstance
  have h₂ : (algebraMap P₂ k).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr
      (Algebra.EssFiniteType.of_isLocalization k (nonZeroDivisors P₂))
  have h := (h₀.comp h₁).comp h₂
  have he : (algebraMap P₂ k).comp ((algebraMap F₅ P₂).comp (algebraMap ℤ F₅)) =
      algebraMap ℤ k := Subsingleton.elim _ _
  rw [he] at h
  exact RingHom.essFiniteType_algebraMap.mp h

theorem baseConstants_essFiniteType_int : Algebra.EssFiniteType ℤ ell := by
  have hk := RingHom.essFiniteType_algebraMap.mpr rationalConstants_essFiniteType_int
  have he := (RingHom.FiniteType.of_surjective baseEquiv.toRingHom
    baseEquiv.surjective).essFiniteType
  have h := hk.comp he
  have hmap : baseEquiv.toRingHom.comp (algebraMap ℤ k) = algebraMap ℤ ell :=
    Subsingleton.elim _ _
  rw [hmap] at h
  exact RingHom.essFiniteType_algebraMap.mp h

namespace ConeRing

theorem affineInvariant_finiteType : Algebra.FiniteType ell affineInvariantRing := by
  have h : Algebra.FiniteType ell Contraction.coneFixedRing :=
    Contraction.quotient_chart_finiteType 3
  exact Algebra.FiniteType.equiv h Contraction.coneInvariantEquiv.symm

theorem invariantLocal_essFiniteType_ell : Algebra.EssFiniteType ell B := by
  let : Algebra affineInvariantRing B := affineInvariantToLocalAlgebra
  let : SMul affineInvariantRing B := affineInvariantToLocalAlgebra.toSMul
  have := affineInvariant_finiteType
  have : Algebra.EssFiniteType affineInvariantRing B :=
    Algebra.EssFiniteType.of_isLocalization B invariantVertexIdeal.primeCompl
  have : IsScalarTower ell affineInvariantRing B :=
    IsScalarTower.of_algHom invariantLocalizationMap
  exact Algebra.EssFiniteType.comp ell affineInvariantRing B

theorem invariantLocal_essFiniteType_int : Algebra.EssFiniteType ℤ B := by
  have h₀ := RingHom.essFiniteType_algebraMap.mpr baseConstants_essFiniteType_int
  have h₁ := RingHom.essFiniteType_algebraMap.mpr invariantLocal_essFiniteType_ell
  have h := h₀.comp h₁
  have he : (algebraMap ell B).comp (algebraMap ℤ ell) = algebraMap ℤ B :=
    Subsingleton.elim _ _
  rw [he] at h
  exact RingHom.essFiniteType_algebraMap.mp h

end ConeRing
end
end Red61

/-! A rational coordinate system straightening the original field derivation
near the contracted cone. The coefficient coordinates agree with the concrete
residue-field section already constructed in B. -/

namespace Red61.ConeRing

open Fields LocalCoordinates PolynomialInvariants
noncomputable section

def coneStraightCoordinates : Fin 4 → K := ![T,q₁,q₂,U]

theorem coneStraight_recovery :
    c₁ ∈ polynomialRing (F := F₅) coneStraightCoordinates ∧
    c₂ ∈ polynomialRing (F := F₅) coneStraightCoordinates ∧
    T ∈ polynomialRing (F := F₅) coneStraightCoordinates ∧
    U ∈ polynomialRing (F := F₅) coneStraightCoordinates := by
  let P := polynomialRing (F := F₅) coneStraightCoordinates
  have hv (i : Fin 4) : coneStraightCoordinates i ∈ P :=
    Algebra.subset_adjoin (Set.mem_range_self i)
  have ht : T ∈ P := hv 0
  have hq₁ : q₁ ∈ P := hv 1
  have hq₂ : q₂ ∈ P := hv 2
  have hu : U ∈ P := hv 3
  refine ⟨?_, ?_, ht, hu⟩
  · have he : c₁ = q₁ + U*T := by dsimp [q₁]; ring
    rw [he]
    exact P.add_mem hq₁ (P.mul_mem hu ht)
  · have he : c₂ = q₂ + 3*U*T^2 := by dsimp [q₂]; ring
    rw [he]
    exact P.add_mem hq₂ (P.mul_mem (P.mul_mem (P.natCast_mem 3) hu) (P.pow_mem ht 2))

theorem coneStraight_independent : AlgebraicIndependent F₅ coneStraightCoordinates := by
  apply Charts.independent_of_chart_recovery 1 _ coneStraight_recovery.1
    coneStraight_recovery.2.1
  · simpa [Charts.y₁, Charts.first, Charts.monomial, T] using coneStraight_recovery.2.2.1
  · have hu : U ∈ IntermediateField.adjoin F₅ (Set.range coneStraightCoordinates) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_range_self 3)
    simpa [Charts.y₂, Charts.second, Charts.monomial, U] using hu

theorem coneStraight_field_generation :
    IntermediateField.adjoin F₅ (Set.range coneStraightCoordinates) = ⊤ := by
  have hle : polynomialRing (F := F₅) coneStraightCoordinates ≤
      (IntermediateField.adjoin F₅ (Set.range coneStraightCoordinates)).toSubalgebra :=
    Algebra.adjoin_le (IntermediateField.subset_adjoin _ _)
  apply Charts.chart_generators_field 1 _ (hle coneStraight_recovery.1)
    (hle coneStraight_recovery.2.1)
  · simpa [Charts.y₁, Charts.first, Charts.monomial, T] using
      hle coneStraight_recovery.2.2.1
  · simpa [Charts.y₂, Charts.second, Charts.monomial, U] using
      hle coneStraight_recovery.2.2.2

def coneSliceDerivation : Derivation F₅ K K := U • delta

theorem coneSlice_on_coordinates (i : Fin 4) :
    coneSliceDerivation (coneStraightCoordinates i) = if i = 0 then 1 else 0 := by
  have hU : U ≠ 0 := inv_ne_zero (coord_nonzero 3)
  have hT : T ≠ 0 := coord_nonzero 2
  have he (x : K) : theta x = T * coneSliceDerivation x := by
    change U * T * delta x = T * (U * delta x)
    ring
  fin_cases i
  · change U * delta t = 1
    rw [delta_t]
    exact inv_mul_cancel₀ (coord_nonzero 3)
  · exact (mul_eq_zero.mp ((he q₁).symm.trans theta_q₁)).resolve_left hT
  · exact (mul_eq_zero.mp ((he q₂).symm.trans theta_q₂)).resolve_left hT
  · change U * delta U = 0
    simp [U, Derivation.leibniz_inv]

theorem coneSlice_polynomial_kernel :
    kernelIn coneSliceDerivation (polynomialRing coneStraightCoordinates) =
      polynomialRing (powerCoordinates coneStraightCoordinates) :=
  kernel_polynomial _ _ coneStraight_independent coneSlice_on_coordinates

end
end Red61.ConeRing

/-! Polynomial localization coordinates and a differential basis on the
first exceptional quotient chart. This is the actual invariant chart ring. -/

namespace Red61.Charts

open Fields LocalCoordinates PolynomialInvariants FieldLocalization Module
noncomputable section

def exceptionalFirstRing : Subalgebra F₅ K := (chartRing 1).restrictScalars F₅

theorem exceptionalFirst_derivation : localGenerator 1 = ConeRing.coneSliceDerivation := by
  ext x
  simp [localGenerator, scale, monomial, ConeRing.coneSliceDerivation, U]

theorem exceptionalFirst_polynomial_le :
    polynomialRing (F := F₅) ConeRing.coneStraightCoordinates ≤ exceptionalFirstRing := by
  have hc₁ : c₁ ∈ exceptionalFirstRing := (constants_mem_chart 1).1
  have hc₂ : c₂ ∈ exceptionalFirstRing := (constants_mem_chart 1).2
  have ht : T ∈ exceptionalFirstRing := by
    change T ∈ chartRing 1
    simpa [T, y₁, first, monomial] using y₁_mem 1
  have hu : U ∈ exceptionalFirstRing := by
    change U ∈ chartRing 1
    simpa [U, y₂, second, monomial] using y₂_mem 1
  apply Algebra.adjoin_le
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ht
  · exact exceptionalFirstRing.sub_mem hc₁ (exceptionalFirstRing.mul_mem hu ht)
  · exact exceptionalFirstRing.sub_mem hc₂
      (exceptionalFirstRing.mul_mem
        (exceptionalFirstRing.mul_mem (exceptionalFirstRing.natCast_mem 3) hu)
        (exceptionalFirstRing.pow_mem ht 2))
  · exact hu

abbrev exceptionalFirstKernel := kernelIn (localGenerator 1) exceptionalFirstRing

end
end Red61.Charts

/-! Coordinates near the second exceptional generic point. The transverse
coordinate y is invertible there; the scaled derivation differentiates y. -/

namespace Red61.Charts

open Fields LocalCoordinates PolynomialInvariants
noncomputable section

theorem exceptionalSecond_q_relations :
    q₁ = c₁ - y₁ 2 ^ 2 * y₂ 2 ∧ q₂ = c₂ - 3 * y₁ 2 * y₂ 2 := by
  constructor <;> norm_num [q₁, q₂, U, T, y₁, y₂, monomial, first, second] <;>
    field_simp [coord_nonzero 2, coord_nonzero 3]

theorem exceptionalSecond_y_formula : y₂ 2 = U*T^3 := by
  norm_num [y₂, second, monomial, U, T]
  ring

theorem exceptionalSecond_generator_apply (x : K) : localGenerator 2 x = theta x := by
  change monomial (scale 2) * delta x = U*T*delta x
  simp [scale, monomial, U, T, mul_comm, mul_assoc]

theorem exceptionalSecond_y_derivative : localGenerator 2 (y₂ 2) = 3 * y₂ 2 := by
  rw [exceptionalSecond_generator_apply, exceptionalSecond_y_formula]
  simp [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
  ring

theorem exceptionalSecond_three_y_nonzero : (3 : K) * y₂ 2 ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have hh := (CharP.cast_eq_zero_iff K 5 3).mp h
    norm_num at hh
  · exact monomial_nonzero _

def exceptionalSecondStraight : Fin 4 → K := ![y₂ 2, q₁, q₂, r]

def exceptionalSecondSlice : Derivation F₅ K K := ((3 : K) * y₂ 2)⁻¹ • localGenerator 2

theorem exceptionalSecond_slice_coordinates (i : Fin 4) :
    exceptionalSecondSlice (exceptionalSecondStraight i) = if i = 0 then 1 else 0 := by
  fin_cases i
  · change ((3 : K) * y₂ 2)⁻¹ * localGenerator 2 (y₂ 2) = 1
    rw [exceptionalSecond_y_derivative, inv_mul_cancel₀ exceptionalSecond_three_y_nonzero]
  · change ((3 : K) * y₂ 2)⁻¹ * localGenerator 2 q₁ = 0
    rw [exceptionalSecond_generator_apply, theta_q₁, mul_zero]
  · change ((3 : K) * y₂ 2)⁻¹ * localGenerator 2 q₂ = 0
    rw [exceptionalSecond_generator_apply, theta_q₂, mul_zero]
  · change ((3 : K) * y₂ 2)⁻¹ * localGenerator 2 r = 0
    rw [exceptionalSecond_generator_apply, theta_r, mul_zero]

theorem exceptionalSecond_field_generation :
    IntermediateField.adjoin F₅ (Set.range exceptionalSecondStraight) = ⊤ := by
  let M := IntermediateField.adjoin F₅ (Set.range exceptionalSecondStraight)
  have hv (i : Fin 4) : exceptionalSecondStraight i ∈ M :=
    IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
  have hy : y₂ 2 ∈ M := hv 0
  have hr : r ∈ M := hv 3
  have hx : y₁ 2 ∈ M := by
    have he : y₁ 2 = r / y₂ 2 ^ 2 := by
      rw [parameters_in_boundary_charts.2.2.2]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero 2 (monomial_nonzero (second 2)))).symm
    rw [he]
    exact M.div_mem hr (M.pow_mem hy 2)
  have hc₁ : c₁ ∈ M := by
    have he : c₁ = q₁ + y₁ 2 ^ 2 * y₂ 2 := by
      rw [exceptionalSecond_q_relations.1]
      ring
    rw [he]
    exact M.add_mem (hv 1) (M.mul_mem (M.pow_mem hx 2) hy)
  have hc₂ : c₂ ∈ M := by
    have he : c₂ = q₂ + 3 * y₁ 2 * y₂ 2 := by
      rw [exceptionalSecond_q_relations.2]
      ring
    rw [he]
    exact M.add_mem (hv 2) (M.mul_mem (M.mul_mem (M.natCast_mem 3) hx) hy)
  exact chart_generators_field 2 M hc₁ hc₂ hx hy

theorem exceptionalSecond_independent : AlgebraicIndependent F₅ exceptionalSecondStraight := by
  have : Algebra.IsAlgebraic (Algebra.adjoin F₅ (Set.range exceptionalSecondStraight)) K := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, exceptionalSecond_field_generation]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₅
    exceptionalSecondStraight coordinates_independent.cardinalMk_le_trdeg).1

end
end Red61.Charts

/-! The invariant quotient near the second exceptional generic point is a
localization of a polynomial algebra in y^5,q1,q2,r. -/

namespace Red61.Charts

open Fields LocalCoordinates PolynomialInvariants FieldLocalization AffineGluing Module
noncomputable section

def exceptionalSecondOriginal : Subalgebra F₅ K := (chartRing 2).restrictScalars F₅

def exceptionalSecondRing : Subalgebra F₅ K :=
  exceptionalSecondOriginal ⊔ Algebra.adjoin F₅ {(y₂ 2)⁻¹}

theorem exceptionalSecond_polynomial_le_original :
    polynomialRing (F := F₅) exceptionalSecondStraight ≤ exceptionalSecondOriginal := by
  have hx : y₁ 2 ∈ exceptionalSecondOriginal := y₁_mem 2
  have hy : y₂ 2 ∈ exceptionalSecondOriginal := y₂_mem 2
  apply Algebra.adjoin_le
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact hy
  · change q₁ ∈ exceptionalSecondOriginal
    rw [exceptionalSecond_q_relations.1]
    exact exceptionalSecondOriginal.sub_mem (constants_mem_chart 2).1
      (exceptionalSecondOriginal.mul_mem (exceptionalSecondOriginal.pow_mem hx 2) hy)
  · change q₂ ∈ exceptionalSecondOriginal
    rw [exceptionalSecond_q_relations.2]
    exact exceptionalSecondOriginal.sub_mem (constants_mem_chart 2).2
      (exceptionalSecondOriginal.mul_mem
        (exceptionalSecondOriginal.mul_mem (exceptionalSecondOriginal.natCast_mem 3) hx) hy)
  · change r ∈ exceptionalSecondOriginal
    rw [parameters_in_boundary_charts.2.2.2]
    exact exceptionalSecondOriginal.mul_mem hx (exceptionalSecondOriginal.pow_mem hy 2)

theorem exceptionalSecond_polynomial_le :
    polynomialRing (F := F₅) exceptionalSecondStraight ≤ exceptionalSecondRing :=
  exceptionalSecond_polynomial_le_original.trans le_sup_left

theorem exceptionalSecond_inverse_mem : (y₂ 2)⁻¹ ∈ exceptionalSecondRing :=
  (show Algebra.adjoin F₅ {(y₂ 2)⁻¹} ≤ exceptionalSecondRing from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_singleton _))

abbrev exceptionalSecondKernel := kernelIn exceptionalSecondSlice exceptionalSecondOriginal
abbrev exceptionalSecondOpenKernel := kernelIn exceptionalSecondSlice exceptionalSecondRing

theorem exceptionalSecond_kernel_iff (z : K) :
    exceptionalSecondSlice z = 0 ↔ localGenerator 2 z = 0 := by
  change ((3 : K) * y₂ 2)⁻¹ * localGenerator 2 z = 0 ↔ _
  rw [mul_eq_zero]
  exact or_iff_right (inv_ne_zero exceptionalSecond_three_y_nonzero)

def exceptionalSecondKernelEquiv : exceptionalSecondKernel ≃+* invariantChartRing 2 :=
  (Subalgebra.equivOfEq exceptionalSecondKernel
    (kernelIn (localGenerator 2) exceptionalSecondOriginal) (by
      ext z
      change (z ∈ exceptionalSecondOriginal ∧ exceptionalSecondSlice z = 0) ↔
        (z ∈ exceptionalSecondOriginal ∧ localGenerator 2 z = 0)
      rw [exceptionalSecond_kernel_iff])).toRingEquiv.trans (chartKernelInEquiv 2)

end
end Red61.Charts

/-! Explicit coordinate differentials for the exceptional invariant rings.
The second coordinate system belongs to the open chart where y is inverted. -/

namespace Red61.Charts

open Fields LocalCoordinates PolynomialInvariants Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

def exceptionalFirstKernelCoordinates : Fin 4 → exceptionalFirstKernel :=
  powerKernelCoordinate (localGenerator 1) ConeRing.coneStraightCoordinates
    ConeRing.coneStraight_independent
    (by rw [exceptionalFirst_derivation]; exact ConeRing.coneSlice_on_coordinates)
    exceptionalFirstRing exceptionalFirst_polynomial_le

@[simp] theorem exceptionalFirstKernelCoordinates_coe (i : Fin 4) :
    (exceptionalFirstKernelCoordinates i : K) = ![T ^ 5, q₁, q₂, U] i := by
  fin_cases i <;>
    rfl

def exceptionalSecondOpenCoordinates : Fin 4 → exceptionalSecondOpenKernel :=
  powerKernelCoordinate exceptionalSecondSlice exceptionalSecondStraight
    exceptionalSecond_independent exceptionalSecond_slice_coordinates
    exceptionalSecondRing exceptionalSecond_polynomial_le

@[simp] theorem exceptionalSecondOpenCoordinates_coe (i : Fin 4) :
    (exceptionalSecondOpenCoordinates i : K) = ![(y₂ 2) ^ 5, q₁, q₂, r] i := by
  fin_cases i <;>
    rfl

def exceptionalSecondOpenInverse : exceptionalSecondOpenKernel :=
  ⟨((y₂ 2) ^ 5)⁻¹, by
    constructor
    · simpa [inv_pow] using exceptionalSecondRing.pow_mem exceptionalSecond_inverse_mem 5
    · change exceptionalSecondSlice (((y₂ 2) ^ 5)⁻¹) = 0
      have h : exceptionalSecondSlice ((y₂ 2) ^ 5) = 0 := by
        rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]
      simp [Derivation.leibniz_inv, h]⟩

@[simp] theorem exceptionalSecondOpenInverse_coe :
    (exceptionalSecondOpenInverse : K) = ((y₂ 2) ^ 5)⁻¹ := rfl

end
end Red61.Charts

/-! The invariant field is rational in q1,q2,u,r over the prime field. The
proof clears fifth powers of denominators in the straightened coordinates. -/

namespace Red61.ConeRing

open Fields LocalCoordinates PolynomialInvariants
noncomputable section
set_option backward.isDefEq.respectTransparency false

instance invariantField_charFive : CharP L 5 :=
  L.subtype.charP L.subtype.injective 5

instance invariantFieldPrimeAlgebra : Algebra F₅ L :=
  ZMod.algebraOfModule 5 L

def invariantCoordinatesB : Fin 4 → B :=
  ![shiftedCoefficient 0, shiftedCoefficient 1, uB, rB]

def invariantCoordinates (i : Fin 4) : L := invariantEmbedding (invariantCoordinatesB i)

@[simp] theorem invariantCoordinates_coe (i : Fin 4) :
    (invariantCoordinates i : K) = ![q₁,q₂,u,r] i := by
  fin_cases i <;>
    simp [invariantCoordinates, invariantCoordinatesB, parameters_embedding.1,
      parameters_embedding.2]

def invariantInclusion : L →ₐ[F₅] K where
  __ := L.subtype
  commutes' a := RingHom.congr_fun (Subsingleton.elim
    (L.subtype.comp (algebraMap F₅ L)) (algebraMap F₅ K)) a

theorem powerCoordinates_invariant (i : Fin 4) :
    powerCoordinates coneStraightCoordinates i ∈ L := by
  apply theta_kernel_in_L
  fin_cases i
  · change theta (T^5) = 0
    rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]
  all_goals simp [powerCoordinates, coneStraightCoordinates]

def invariantPowerCoordinates (i : Fin 4) : L :=
  ⟨powerCoordinates coneStraightCoordinates i, powerCoordinates_invariant i⟩

theorem invariantPowerCoordinates_independent :
    AlgebraicIndependent F₅ invariantPowerCoordinates :=
  AlgebraicIndependent.of_comp invariantInclusion
    (powerCoordinates_independent coneStraight_independent)

theorem invariant_mem_powerField (x : L) :
    (x : K) ∈ IntermediateField.adjoin F₅
      (Set.range (powerCoordinates coneStraightCoordinates)) := by
  let P := polynomialRing (F := F₅) coneStraightCoordinates
  let Q := polynomialRing (F := F₅) (powerCoordinates coneStraightCoordinates)
  let M := IntermediateField.adjoin F₅ (Set.range (powerCoordinates coneStraightCoordinates))
  by_cases hx : x = 0
  · simp [hx]
  have hx0 : (x : K) ≠ 0 := fun h ↦ hx (Subtype.ext h)
  have hgen : (x : K) ∈ IntermediateField.adjoin F₅ (Set.range coneStraightCoordinates) := by
    rw [coneStraight_field_generation]
    trivial
  obtain ⟨a, ha, b, hb, he⟩ := IntermediateField.mem_adjoin_iff_div.mp hgen
  have hb0 : b ≠ 0 := by
    intro hb0
    exact hx0 (by simpa [hb0] using he)
  have hDx : coneSliceDerivation (x : K) = 0 := by
    change U * delta (x : K) = 0
    rw [show delta (x : K) = 0 from x.property, mul_zero]
  have hp (z : K) : coneSliceDerivation (z^5) = 0 := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]
  have hab : (x : K) * b = a := by rw [he]; exact div_mul_cancel₀ _ hb0
  have hnum : a*b^4 ∈ Q := by
    change a*b^4 ∈ polynomialRing (powerCoordinates coneStraightCoordinates)
    rw [← coneSlice_polynomial_kernel]
    refine ⟨P.mul_mem ha (P.pow_mem hb 4), ?_⟩
    change coneSliceDerivation (a*b^4) = 0
    have heq : a*b^4 = (x : K)*b^5 := by rw [← hab]; ring
    rw [heq, Derivation.leibniz, hDx, hp]
    simp
  have hden : b^5 ∈ Q := by
    change b^5 ∈ polynomialRing (powerCoordinates coneStraightCoordinates)
    rw [← coneSlice_polynomial_kernel]
    exact ⟨P.pow_mem hb 5, hp b⟩
  have hQM : Q ≤ M.toSubalgebra := Algebra.adjoin_le (IntermediateField.subset_adjoin _ _)
  have heq : (x : K) = (a*b^4)/b^5 := by rw [← hab]; field_simp
  rw [heq]
  exact M.div_mem (hQM hnum) (hQM hden)

theorem invariant_coordinate_fields_eq :
    IntermediateField.adjoin F₅ (Set.range (fun i ↦ (invariantCoordinates i : K))) =
      IntermediateField.adjoin F₅ (Set.range (powerCoordinates coneStraightCoordinates)) := by
  let M := IntermediateField.adjoin F₅ (Set.range (powerCoordinates coneStraightCoordinates))
  let N := IntermediateField.adjoin F₅ (Set.range (fun i ↦ (invariantCoordinates i : K)))
  have hm (i : Fin 4) : powerCoordinates coneStraightCoordinates i ∈ M :=
    IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
  have hn (i : Fin 4) : (invariantCoordinates i : K) ∈ N :=
    IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨i,rfl⟩
    change (invariantCoordinates i : K) ∈ M
    rw [invariantCoordinates_coe]
    fin_cases i
    · exact hm 1
    · exact hm 2
    · exact hm 3
    · exact M.mul_mem (M.pow_mem (hm 3) 2) (hm 0)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨i,rfl⟩
    change powerCoordinates coneStraightCoordinates i ∈ N
    fin_cases i
    · have hu : U ∈ N := by simpa [u] using hn 2
      have hr : r ∈ N := by simpa using hn 3
      have he : T^5 = r/U^2 := by
        dsimp [r]
        field_simp [show U ≠ 0 from inv_ne_zero (coord_nonzero 3)]
      change T^5 ∈ N
      rw [he]
      exact N.div_mem hr (N.pow_mem hu 2)
    · simpa [powerCoordinates, coneStraightCoordinates] using hn 0
    · simpa [powerCoordinates, coneStraightCoordinates] using hn 1
    · simpa [powerCoordinates, coneStraightCoordinates, u] using hn 2

theorem invariantCoordinates_field_generation :
    IntermediateField.adjoin F₅ (Set.range invariantCoordinates) = ⊤ := by
  let M := IntermediateField.adjoin F₅ (Set.range invariantCoordinates)
  have hmap : M.map invariantInclusion =
      IntermediateField.adjoin F₅ (Set.range (fun i ↦ (invariantCoordinates i : K))) := by
    rw [IntermediateField.adjoin_map, ← Set.range_comp]
    rfl
  apply top_unique
  intro x _
  have hx : (x : K) ∈ M.map invariantInclusion := by
    rw [hmap, invariant_coordinate_fields_eq]
    exact invariant_mem_powerField x
  obtain ⟨y,hy,he⟩ := (IntermediateField.mem_map (S := M)).mp hx
  exact (invariantInclusion.injective he) ▸ hy

theorem invariantCoordinates_independent : AlgebraicIndependent F₅ invariantCoordinates := by
  have : Algebra.IsAlgebraic (Algebra.adjoin F₅ (Set.range invariantCoordinates)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, invariantCoordinates_field_generation]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₅
    invariantCoordinates invariantPowerCoordinates_independent.cardinalMk_le_trdeg).1

end
end Red61.ConeRing

/-! Underlying field elements are preserved by the kernel-presentation
isomorphisms. The generic coercion lemmas avoid reducing concrete ring data. -/

namespace Red61

noncomputable section

theorem subalgebra_equivOfEq_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S T : Subalgebra R A) (h : S = T) (x : S) :
    ((Subalgebra.equivOfEq S T h x : T) : A) = (x : A) := rfl

theorem inclusionAlgebra_coe {k F : Type} [Field k] [Field F] [Algebra k F]
    {A B : Subalgebra k F} (h : A ≤ B) (x : A) :
    letI := AffineGluing.inclusionAlgebra h
    ((algebraMap A B x : B) : F) = (x : F) := rfl

namespace Charts

open Fields PolynomialInvariants

theorem chartKernelInEquiv_coe (i : Fin 6)
    (x : kernelIn (localGenerator i) ((chartRing i).restrictScalars F₅)) :
    ((chartKernelInEquiv i x : L) : K) = (x : K) := rfl

end Charts
end
end Red61

/-! The genuine prime-field differential module of the invariant function
field has basis dq1,dq2,du,dr. Local freeness at special stalks is a separate
question and is not inferred merely from this field calculation. -/

namespace Red61.ConeRing

open Fields LocalCoordinates Module
noncomputable section

def invariantPolynomialMap : P₄ →ₐ[F₅] L := MvPolynomial.aeval invariantCoordinates

@[instance_reducible] def invariantPolynomialAlgebra : Algebra P₄ L :=
  invariantPolynomialMap.toRingHom.toAlgebra

theorem invariantPolynomial_isScalarTower :
    letI := invariantPolynomialAlgebra
    IsScalarTower F₅ P₄ L := by
  let := invariantPolynomialAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (invariantPolynomialMap.commutes a).symm

theorem invariantPolynomial_isFractionRing :
    letI := invariantPolynomialAlgebra
    IsFractionRing P₄ L := by
  let := invariantPolynomialAlgebra
  have : FaithfulSMul P₄ L :=
    (faithfulSMul_iff_algebraMap_injective P₄ L).mpr invariantCoordinates_independent
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ IntermediateField.adjoin F₅ (Set.range invariantCoordinates) := by
    rw [invariantCoordinates_field_generation]
    trivial
  obtain ⟨a,ha,b,hb,he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  rw [Algebra.adjoin_range_eq_range_aeval] at ha hb
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  exact ⟨a,b,he⟩

def invariantDifferentialBasis : Basis (Fin 4) L (KaehlerDifferential F₅ L) := by
  let := invariantPolynomialAlgebra
  have := invariantPolynomial_isScalarTower
  have := invariantPolynomial_isFractionRing
  exact polynomialLocalizationDifferentialBasis F₅ L (Fin 4) (nonZeroDivisors P₄)

@[simp] theorem invariantDifferentialBasis_apply (i : Fin 4) :
    invariantDifferentialBasis i = KaehlerDifferential.D F₅ L (invariantCoordinates i) := by
  let := invariantPolynomialAlgebra
  have := invariantPolynomial_isScalarTower
  have := invariantPolynomial_isFractionRing
  exact (polynomialLocalizationDifferentialBasis_apply F₅ L (Fin 4)
    (nonZeroDivisors P₄) i).trans (by
      congr 1
      exact MvPolynomial.aeval_X _ _)

def invariantAbsoluteDifferentialEquiv :
    KaehlerDifferential ℤ L ≃ₗ[L] KaehlerDifferential F₅ L :=
  quotientBaseDifferentialEquiv ℤ F₅ L ZMod.intCast_surjective

def invariantAbsoluteDifferentialBasis : Basis (Fin 4) L (KaehlerDifferential ℤ L) :=
  invariantDifferentialBasis.map invariantAbsoluteDifferentialEquiv.symm

@[simp] theorem invariantAbsoluteDifferentialBasis_apply (i : Fin 4) :
    invariantAbsoluteDifferentialBasis i = KaehlerDifferential.D ℤ L (invariantCoordinates i) := by
  simp [invariantAbsoluteDifferentialBasis, invariantAbsoluteDifferentialEquiv]

end
end Red61.ConeRing

/-! The three rational coordinate changes on the retained invariant charts
have determinant one in characteristic five. Every denominator condition
is explicit; no regularity of the rational coordinate functions is assumed. -/

namespace Red61

open Module
noncomputable section

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [CharP R 5]

theorem keptFirstCoordinateDifferentialMatrix
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i)) (z : R) (hz : z * v 3 = 1) :
    coordinateDifferentialMatrix b
      ![-v 2 * z, v 1 - 3 * v 2 ^ 2 * z, z, v 0 * v 3 ^ 3 + v 2 ^ 5 * z ^ 2] =
      !![0, 0, 0, v 3 ^ 3; 0, 1, 0, 0; -z, -6 * v 2 * z, 0, 0;
        v 2 * z ^ 2, 3 * v 2 ^ 2 * z ^ 2, -z ^ 2,
          3 * v 0 * v 3 ^ 2 - 2 * v 2 ^ 5 * z ^ 3] := by
  have hr (i : Fin 4) : b.repr (KaehlerDifferential.D A R (v i)) = Finsupp.single i 1 := by
    rw [← hb]; exact b.repr_self i
  have hd : KaehlerDifferential.D A R z = -z ^ 2 • KaehlerDifferential.D A R (v 3) :=
    (KaehlerDifferential.D A R).leibniz_of_mul_eq_one hz
  have h5 : (5 : R) = 0 := CharP.cast_eq_zero R 5
  have h3 : KaehlerDifferential.D A R (3 : R) = 0 :=
    (KaehlerDifferential.D A R).map_natCast 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDifferentialMatrix, Derivation.leibniz, Derivation.leibniz_pow,
      hd, map_add, map_sub, map_smul, map_nsmul, hr, h5, h3] <;> ring

theorem keptFirstCoordinateDifferentialMatrix_det
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i)) (z : R) (hz : z * v 3 = 1) :
    (coordinateDifferentialMatrix b
      ![-v 2 * z, v 1 - 3 * v 2 ^ 2 * z, z, v 0 * v 3 ^ 3 + v 2 ^ 5 * z ^ 2]).det = 1 := by
  rw [keptFirstCoordinateDifferentialMatrix b v hb z hz, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  calc
    _ = (z * v 3) ^ 3 := by ring
    _ = 1 := by rw [hz]; simp

theorem keptLastCoordinateDifferentialMatrix
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i)) (z : R) (hz : z * v 3 = 1) :
    coordinateDifferentialMatrix b
      ![v 1 - v 2 ^ 3 * v 3, 2 * v 2, (v 2 ^ 5 + 2 * v 0) * v 3 ^ 2, z] =
      !![0, 0, 2 * v 3 ^ 2, 0; 1, 0, 0, 0; -3 * v 2 ^ 2 * v 3, 2, 0, 0;
        -v 2 ^ 3, 0, 2 * (v 2 ^ 5 + 2 * v 0) * v 3, -z ^ 2] := by
  have hr (i : Fin 4) : b.repr (KaehlerDifferential.D A R (v i)) = Finsupp.single i 1 := by
    rw [← hb]; exact b.repr_self i
  have hd : KaehlerDifferential.D A R z = -z ^ 2 • KaehlerDifferential.D A R (v 3) :=
    (KaehlerDifferential.D A R).leibniz_of_mul_eq_one hz
  have h5 : (5 : R) = 0 := CharP.cast_eq_zero R 5
  have h2 : KaehlerDifferential.D A R (2 : R) = 0 :=
    (KaehlerDifferential.D A R).map_natCast 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDifferentialMatrix, Derivation.leibniz, Derivation.leibniz_pow,
      hd, map_add, map_sub, map_smul, map_nsmul, hr, h5, h2] <;> ring

theorem keptLastCoordinateDifferentialMatrix_det
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i)) (z : R) (hz : z * v 3 = 1) :
    (coordinateDifferentialMatrix b
      ![v 1 - v 2 ^ 3 * v 3, 2 * v 2, (v 2 ^ 5 + 2 * v 0) * v 3 ^ 2, z]).det = 1 := by
  rw [keptLastCoordinateDifferentialMatrix b v hb z hz, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  calc
    _ = -4 * (z * v 3) ^ 2 := by ring
    _ = -4 := by rw [hz]; ring
    _ = 1 := by have h5 : (5 : R) = 0 := CharP.cast_eq_zero R 5; linear_combination -h5

omit [CharP R 5] in
theorem keptMiddleCoordinateDifferentialMatrix
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i))
    (a : R) (ha : KaehlerDifferential.D A R a = 0)
    (z h : R) (hz : z * v 3 = 1) (hh : h * v 2 = 1) :
    coordinateDifferentialMatrix b
      ![v 1 - v 2 * z, a - 3 * z, v 2 ^ 2 * (z - 3 * v 0 * v 3 ^ 4), h * z ^ 2] =
      !![0, 0, -3 * v 2 ^ 2 * v 3 ^ 4, 0; 1, 0, 0, 0;
        -z, 0, 2 * v 2 * (z - 3 * v 0 * v 3 ^ 4), -h ^ 2 * z ^ 2;
        v 2 * z ^ 2, 3 * z ^ 2,
          v 2 ^ 2 * (-z ^ 2 - 12 * v 0 * v 3 ^ 3), -2 * h * z ^ 3] := by
  have hr (i : Fin 4) : b.repr (KaehlerDifferential.D A R (v i)) = Finsupp.single i 1 := by
    rw [← hb]; exact b.repr_self i
  have hdz : KaehlerDifferential.D A R z = -z ^ 2 • KaehlerDifferential.D A R (v 3) :=
    (KaehlerDifferential.D A R).leibniz_of_mul_eq_one hz
  have hdh : KaehlerDifferential.D A R h = -h ^ 2 • KaehlerDifferential.D A R (v 2) :=
    (KaehlerDifferential.D A R).leibniz_of_mul_eq_one hh
  have h3 : KaehlerDifferential.D A R (3 : R) = 0 :=
    (KaehlerDifferential.D A R).map_natCast 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDifferentialMatrix, Derivation.leibniz, Derivation.leibniz_pow,
      hdz, hdh, ha, h3, map_add, map_sub, map_smul, map_nsmul, hr] <;> ring

theorem keptMiddleCoordinateDifferentialMatrix_det
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (v : Fin 4 → R)
    (hb : ∀ i, b i = KaehlerDifferential.D A R (v i))
    (a : R) (ha : KaehlerDifferential.D A R a = 0)
    (z h : R) (hz : z * v 3 = 1) (hh : h * v 2 = 1) :
    (coordinateDifferentialMatrix b
      ![v 1 - v 2 * z, a - 3 * z, v 2 ^ 2 * (z - 3 * v 0 * v 3 ^ 4), h * z ^ 2]).det = 1 := by
  rw [keptMiddleCoordinateDifferentialMatrix b v hb a ha z h hz hh, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  calc
    _ = -9 * (h * v 2) ^ 2 * (z * v 3) ^ 4 := by ring
    _ = -9 := by rw [hh, hz]; ring
    _ = 1 := by have h5 : (5 : R) = 0 := CharP.cast_eq_zero R 5; linear_combination -2 * h5

end
end Red61

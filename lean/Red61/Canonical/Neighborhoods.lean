import Red61.Canonical.Volume

/-! # Finite local models of the surface stalks

Formerly the modules `AbsoluteRegularNeighborhood`, `AtlasPrincipalNeighborhood`, `AtlasFiniteLocalModel`, `AtlasPrincipalBase`, `AtlasFiniteLocalOpen`, `RationalBaseGraphEquations`, `SurfacePrimeSmooth`, `SurfacePrimePolynomial`.
-/

/-! A regular-pair neighborhood can be refined to carry an absolute differential
basis descended from an actual stalk. The refinement is a native principal
open immersion and retains its smooth ambient and regular equations. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Module
noncomputable section
variable (m n : ℕ) (F : Type) [Field F] (X : Scheme)
  (b : X ⟶ Spec (CommRingCat.of F)) (x : X)
structure AbsoluteDifferentialRegularPairNeighborhood
    extends DifferentialRegularPairNeighborhood n F X b x where
  absoluteBasis : Basis (Fin m) coordinateRing (KaehlerDifferential ℤ coordinateRing)
variable {m n F X b x}
  (P : DifferentialRegularPairNeighborhood n F X b x)
private local instance : IsOpenImmersion P.openMap := P.openImmersion
private local instance : Algebra.Smooth F P.ambientRing := P.smooth
variable [Module.FinitePresentation P.coordinateRing (KaehlerDifferential ℤ P.coordinateRing)]
  (p : PrimeSpectrum P.coordinateRing)
private local instance : Algebra P.coordinateRing (X.presheaf.stalk (P.openMap p)) :=
  (affineOpenToStalk P.openMap p).toAlgebra
private local instance : IsLocalization p.asIdeal.primeCompl
    (X.presheaf.stalk (P.openMap p)) := affineOpenToStalk_isLocalization P.openMap p

theorem absolute_differential_regular_neighborhood_of_stalk_basis
    (b' : Basis (Fin m) (X.presheaf.stalk (P.openMap p))
      (KaehlerDifferential ℤ (X.presheaf.stalk (P.openMap p)))) :
    Nonempty (AbsoluteDifferentialRegularPairNeighborhood m n F X b (P.openMap p)) := by
  obtain ⟨a, ha, ⟨ba⟩⟩ := exists_away_differential_basis p.asIdeal.primeCompl b'
  have hp : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap P.coordinateRing (Localization.Away a))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
    exact ha
  obtain ⟨q, hq⟩ := hp
  have : Nonempty (PrimeSpectrum (Localization.Away a)) := ⟨q⟩
  have : Nontrivial (Localization.Away a) := PrimeSpectrum.nontrivial q
  obtain ⟨c, g, _, hsmooth, hsurj, hker, hreg⟩ :=
    exists_smooth_regular_quotient_neighborhood P.quotient P.quotient_surjective
      P.left P.right P.kernel P.regular a
  have := KaehlerDifferential.isLocalizedModule_map F P.ambientRing
    (Localization.Away c) (.powers c)
  refine ⟨{
    coordinateRing := Localization.Away a
    coordinateCommRing := inferInstance
    coordinateAlgebra := inferInstance
    ambientRing := Localization.Away c
    ambientCommRing := inferInstance
    ambientAlgebra := inferInstance
    openMap := Spec.map (CommRingCat.ofHom
      (algebraMap P.coordinateRing (Localization.Away a))) ≫ P.openMap
    openImmersion := inferInstance
    point_mem := ?_
    base_comp := ?_
    quotient := g
    quotient_surjective := hsurj
    left := algebraMap P.ambientRing (Localization.Away c) P.left
    right := algebraMap P.ambientRing (Localization.Away c) P.right
    kernel := hker
    regular := hreg
    smooth := hsmooth
    ambientBasis := P.ambientBasis.ofIsLocalizedModule (Localization.Away c) (.powers c)
      (KaehlerDifferential.map F F P.ambientRing (Localization.Away c))
    absoluteBasis := intDifferentialBasisCanonical (inferInstance : Algebra ℤ _) ba }⟩
  · exact ⟨q, congrArg P.openMap hq⟩
  · rw [Category.assoc, P.base_comp, ← Spec.map_comp]
    congr 1
end
end Red61

/-! Two successive principal localizations give actual open immersions
into a principal atlas. A compatible stalk evaluation whose inverted
element is a unit proves that the original point belongs to the open. -/

namespace Red61.AffineGluing.PrincipalAtlas
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) (i : D.Index) (d : D.ring i)
  (z : Localization.Away d)

def iteratedPrincipalOpenMap :
    Spec (CommRingCat.of (Localization.Away z)) ⟶ D.glued :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away d) (Localization.Away z))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (D.ring i) (Localization.Away d))) ≫
      D.chartInclusion i

instance iteratedPrincipalOpenMap_open : IsOpenImmersion (D.iteratedPrincipalOpenMap i d z) := by
  unfold iteratedPrincipalOpenMap
  infer_instance

variable (p : PrimeSpectrum (D.ring i))
local notation "s" => D.chartInclusion i p
private local instance : Algebra (D.ring i) (D.glued.presheaf.stalk s) :=
  (D.chartToStalkAt i p s rfl).toAlgebra
private local instance : IsLocalization p.asIdeal.primeCompl (D.glued.presheaf.stalk s) :=
  D.chartToStalkAt_isLocalization i p s rfl

theorem chartToStalkAt_scalarTower :
    letI := (stalkScalarMap k D.toBase s).toAlgebra
    letI := (D.chartToStalkAt i p s rfl).toAlgebra
    IsScalarTower k (D.ring i) (D.glued.presheaf.stalk s) := by
  let := (stalkScalarMap k D.toBase s).toAlgebra
  let := (D.chartToStalkAt i p s rfl).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (D.chartToStalkAt_scalarMap i p s rfl).symm

theorem iteratedPrincipalOpenMap_mem_range
    (β : Localization.Away d →+* D.glued.presheaf.stalk s)
    (hβ : β.comp (algebraMap (D.ring i) (Localization.Away d)) =
      D.chartToStalkAt i p s rfl) (hz : IsUnit (β z)) :
    s ∈ Set.range (D.iteratedPrincipalOpenMap i d z) := by
  let γ : Localization.Away z →+* D.glued.presheaf.stalk s :=
    IsLocalization.Away.lift (S := Localization.Away z) (g := β) z hz
  let q : PrimeSpectrum (Localization.Away z) :=
    (IsLocalRing.closedPoint (D.glued.presheaf.stalk s)).comap γ
  refine ⟨q, ?_⟩
  change D.chartInclusion i
    (PrimeSpectrum.comap (algebraMap (D.ring i) (Localization.Away d))
      (PrimeSpectrum.comap (algebraMap (Localization.Away d) (Localization.Away z)) q)) = _
  congr 1
  apply PrimeSpectrum.ext
  change (((IsLocalRing.maximalIdeal (D.glued.presheaf.stalk s)).comap γ).comap
    (algebraMap (Localization.Away d) (Localization.Away z))).comap
      (algebraMap (D.ring i) (Localization.Away d)) = p.asIdeal
  have he : γ.comp (algebraMap (Localization.Away d) (Localization.Away z)) = β :=
    IsLocalization.Away.lift_comp z hz
  apply Ideal.ext
  intro x
  change γ (algebraMap (Localization.Away d) (Localization.Away z)
    (algebraMap (D.ring i) (Localization.Away d) x)) ∈
      IsLocalRing.maximalIdeal (D.glued.presheaf.stalk s) ↔ x ∈ p.asIdeal
  have hx : γ (algebraMap (Localization.Away d) (Localization.Away z)
      (algebraMap (D.ring i) (Localization.Away d) x)) =
      algebraMap (D.ring i) (D.glued.presheaf.stalk s) x :=
    (RingHom.congr_fun he (algebraMap (D.ring i) (Localization.Away d) x)).trans
      (RingHom.congr_fun hβ x)
  exact (iff_of_eq (congrArg (fun y : D.glued.presheaf.stalk s ↦
    y ∈ IsLocalRing.maximalIdeal (D.glued.presheaf.stalk s)) hx)).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (D.glued.presheaf.stalk s) p.asIdeal x)
end
end Red61.AffineGluing.PrincipalAtlas

/-! A finite-type local model of an actual atlas stalk has a common
principal-open refinement with the original chart. The retained stalk
evaluation proves that both denominators give neighborhoods of the point. -/

namespace Red61.AffineGluing.PrincipalAtlas
open AlgebraicGeometry
noncomputable section
variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) (i : D.Index) (p : PrimeSpectrum (D.ring i))
private local instance : Algebra k (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
  (stalkScalarMap k D.toBase (D.chartInclusion i p)).toAlgebra
private local instance : Algebra (D.ring i) (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
  (D.chartToStalkAt i p (D.chartInclusion i p) rfl).toAlgebra
private local instance :
    IsScalarTower k (D.ring i) (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
  D.chartToStalkAt_scalarTower i p
private local instance :
    IsLocalization p.asIdeal.primeCompl (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
  D.chartToStalkAt_isLocalization i p (D.chartInclusion i p) rfl
variable (Q : Type) [CommRing Q] [Algebra k Q] [Algebra.FiniteType k Q]
  [Algebra Q (D.glued.presheaf.stalk (D.chartInclusion i p))]
  [IsScalarTower k Q (D.glued.presheaf.stalk (D.chartInclusion i p))]
  (q : PrimeSpectrum Q)
  [IsLocalization q.asIdeal.primeCompl (D.glued.presheaf.stalk (D.chartInclusion i p))]

theorem commonFiniteLocalNeighborhood [Algebra.FiniteType k (D.ring i)]
    (hu : Function.Injective (algebraMap Q (D.glued.presheaf.stalk (D.chartInclusion i p)))) :
    ∃ d : p.asIdeal.primeCompl, ∃ e : q.asIdeal.primeCompl,
      ∃ f : Q →ₐ[k] Localization.Away (d : D.ring i),
      ∃ β : Localization.Away (d : D.ring i) →+* D.glued.presheaf.stalk (D.chartInclusion i p),
        β.comp (algebraMap (D.ring i) (Localization.Away (d : D.ring i))) =
          D.chartToStalkAt i p (D.chartInclusion i p) rfl ∧ IsUnit (β (f (e : Q))) ∧
        Nonempty (Localization.Away (e : Q) ≃ₐ[k] Localization.Away (f (e : Q))) := by
  have : FaithfulSMul (D.ring i) (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
    IsLocalization.AtPrime.faithfulSMul
      (D.glued.presheaf.stalk (D.chartInclusion i p)) (D.ring i) p.asIdeal
  have hi : Function.Injective
      (algebraMap (D.ring i) (D.glued.presheaf.stalk (D.chartInclusion i p))) :=
    (faithfulSMul_iff_algebraMap_injective (D.ring i)
      (D.glued.presheaf.stalk (D.chartInclusion i p))).mp inferInstance
  obtain ⟨d, e, f, hf, hE⟩ := exists_common_principal_open k
    (R := D.ring i) (Q := Q) (A := D.glued.presheaf.stalk (D.chartInclusion i p))
    p.asIdeal.primeCompl q.asIdeal.primeCompl hi hu
  let β := awayLocalizationBaseMap
    (A := D.glued.presheaf.stalk (D.chartInclusion i p)) k p.asIdeal.primeCompl d
  refine ⟨d, e, f, β.toRingHom, ?_, ?_, hE⟩
  · ext r
    exact (awayLocalizationComparison (B := D.glued.presheaf.stalk (D.chartInclusion i p))
      p.asIdeal.primeCompl d).commutes r
  · have hunit : IsUnit (algebraMap Q (D.glued.presheaf.stalk (D.chartInclusion i p)) (e : Q)) :=
      IsLocalization.map_units (D.glued.presheaf.stalk (D.chartInclusion i p)) e
    have he : β (f (e : Q)) =
        algebraMap Q (D.glued.presheaf.stalk (D.chartInclusion i p)) (e : Q) :=
      AlgHom.congr_fun hf (e : Q)
    exact he.symm ▸ hunit
end
end Red61.AffineGluing.PrincipalAtlas

/-! Iterated principal-open neighborhoods of an atlas retain the
original map to the coefficient-field spectrum. -/

namespace Red61.AffineGluing.PrincipalAtlas
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) (i : D.Index) (d : D.ring i) (z : Localization.Away d)

theorem iteratedPrincipalOpenMap_toBase :
    D.iteratedPrincipalOpenMap i d z ≫ D.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away z))) := by
  simp only [iteratedPrincipalOpenMap, Category.assoc, D.chartInclusion_toBase]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
end
end Red61.AffineGluing.PrincipalAtlas

/-! A finite-type local model of an actual atlas stalk yields an
actual principal-open neighborhood in the glued scheme. The construction
retains the point and the original coefficient-field base map. -/

namespace Red61.AffineGluing.PrincipalAtlas
open AlgebraicGeometry CategoryTheory
noncomputable section
set_option maxHeartbeats 800000
variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) (i : D.Index) (p : PrimeSpectrum (D.ring i))
private local instance : Algebra k (D.glued.presheaf.stalk (D.chartInclusion i p)) :=
  (stalkScalarMap k D.toBase (D.chartInclusion i p)).toAlgebra
variable (Q : Type) [CommRing Q] [Algebra k Q] [Algebra.FiniteType k Q]
  [Algebra Q (D.glued.presheaf.stalk (D.chartInclusion i p))]
  [IsScalarTower k Q (D.glued.presheaf.stalk (D.chartInclusion i p))]
  (q : PrimeSpectrum Q)
  [IsLocalization q.asIdeal.primeCompl (D.glued.presheaf.stalk (D.chartInclusion i p))]

theorem commonFiniteLocalOpen [Algebra.FiniteType k (D.ring i)]
    (hu : Function.Injective (algebraMap Q (D.glued.presheaf.stalk (D.chartInclusion i p)))) :
    ∃ e : q.asIdeal.primeCompl,
      ∃ j : Spec (CommRingCat.of (Localization.Away (e : Q))) ⟶ D.glued,
        IsOpenImmersion j ∧ D.chartInclusion i p ∈ Set.range j ∧
        j ≫ D.toBase =
          Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away (e : Q)))) := by
  obtain ⟨d, e, f, β, hβ, he, ⟨E⟩⟩ := D.commonFiniteLocalNeighborhood i p Q q hu
  let I := affineAlgebraIso (F := k) (Q := Localization.Away (e : Q))
    (R := Localization.Away (f (e : Q))) E
  let J := D.iteratedPrincipalOpenMap i (d : D.ring i) (f (e : Q))
  let j := I.hom ≫ J
  refine ⟨e, j, ?_, ?_, ?_⟩
  · dsimp only [j, J]
    infer_instance
  · obtain ⟨r, hr⟩ := D.iteratedPrincipalOpenMap_mem_range i
      (d : D.ring i) (f (e : Q)) p β hβ he
    refine ⟨I.inv r, ?_⟩
    change J (I.hom (I.inv r)) = D.chartInclusion i p
    rw [Scheme.inv_hom_apply]
    exact hr
  · have hJ : J ≫ D.toBase =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away (f (e : Q))))) :=
      D.iteratedPrincipalOpenMap_toBase i (d : D.ring i) (f (e : Q))
    let hI := affineAlgebraIso_toBase (F := k) (Q := Localization.Away (e : Q))
      (R := Localization.Away (f (e : Q))) E
    exact (Category.assoc I.hom J D.toBase).trans
      ((congrArg (fun g ↦ I.hom ≫ g) hJ).trans hI)
end
end Red61.AffineGluing.PrincipalAtlas

/-! Tensor graphs over the actual rational base field have two explicit
equations over every compatible coefficient algebra. Their ambient rings
are the specified polynomial localizations. The equations generate the
actual kernel and form a regular sequence for a nontrivial target. Their
native quotient classes form the natural conormal basis. -/

namespace Red61
open Fields Module RingTheory.Sequence
open scoped TensorProduct
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Module F₅ ell := Algebra.toModule
private local instance : SMul F₅ ell := Algebra.toSMul

variable (A : Type*) [CommRing A] [Algebra F₅ A] [Algebra ell A]
  [IsScalarTower F₅ ell A]

@[instance_reducible] def rationalTensorPolynomialAlgebra :
    Algebra (MvPolynomial (Fin 2) A) (ell ⊗[F₅] A) := by
  let := ellPolynomialAlgebra
  have := ell_polynomial_primeTower
  exact tensorPolynomialAlgebra F₅ ell A (Fin 2)

def rationalTensorPolynomialDenominators : Submonoid (MvPolynomial (Fin 2) A) :=
  tensorPolynomialDenominators F₅ A (Fin 2) (nonZeroDivisors P₂)

omit [Algebra ell A] [IsScalarTower F₅ ell A] in
theorem rationalTensor_polynomialLocalization :
    letI := rationalTensorPolynomialAlgebra A
    IsLocalization (rationalTensorPolynomialDenominators A) (ell ⊗[F₅] A) := by
  let := ellPolynomialAlgebra
  have := ell_polynomial_primeTower
  have := ell_polynomial_isLocalization
  let := rationalTensorPolynomialAlgebra A
  exact tensorPolynomial_isLocalization F₅ ell A (Fin 2) (nonZeroDivisors P₂)

def rationalTensorBaseCoordinate (i : Fin 2) : A := algebraMap ell A (baseEquiv (c i))

def rationalTensorEquation (i : Fin 2) : ell ⊗[F₅] A :=
  baseEquiv (c i) ⊗ₜ[F₅] (1 : A) - (1 : ell) ⊗ₜ[F₅] rationalTensorBaseCoordinate A i

omit [IsScalarTower F₅ ell A] in
theorem rationalTensorEquation_polynomial (i : Fin 2) :
    letI := rationalTensorPolynomialAlgebra A
    algebraMap (MvPolynomial (Fin 2) A) (ell ⊗[F₅] A)
      (MvPolynomial.X i - MvPolynomial.C (rationalTensorBaseCoordinate A i)) =
        rationalTensorEquation A i := by
  let := ellPolynomialAlgebra
  have := ell_polynomial_primeTower
  let := rationalTensorPolynomialAlgebra A
  change @algebraMap (MvPolynomial (Fin 2) A) (ell ⊗[F₅] A) _ _
    (tensorPolynomialAlgebra F₅ ell A (Fin 2))
      (MvPolynomial.X i - MvPolynomial.C (rationalTensorBaseCoordinate A i)) = _
  rw [map_sub, tensorPolynomialAlgebra_X, tensorPolynomialAlgebra_C, ellPolynomialAlgebra_X]
  rfl

theorem rationalTensor_kernel_span :
    (tensorGraphExtension F₅ ell A).ker = Ideal.span (Set.range (rationalTensorEquation A)) := by
  let := ellPolynomialAlgebra
  have := ell_polynomial_primeTower
  have := ell_polynomial_isLocalization
  have hv : tensorGraphPolynomialValues F₅ ell A (Fin 2) = rationalTensorBaseCoordinate A := by
    funext i
    simp only [tensorGraphPolynomialValues, ellPolynomialAlgebra_X]
    rfl
  have h := tensorGraphKernel_eq_span F₅ ell A (Fin 2) (nonZeroDivisors P₂)
  rw [hv] at h
  change RingHom.ker (tensorGraphMap F₅ ell A).toRingHom =
    Ideal.span (Set.range (fun i : Fin 2 ↦ baseEquiv (c i) ⊗ₜ[F₅] (1 : A) -
      (1 : ell) ⊗ₜ[F₅] rationalTensorBaseCoordinate A i))
  simpa only [ellPolynomialAlgebra_X] using h

theorem rationalTensor_kernel_pair :
    (tensorGraphExtension F₅ ell A).ker =
      Ideal.ofList [rationalTensorEquation A 0, rationalTensorEquation A 1] := by
  rw [rationalTensor_kernel_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

theorem rationalTensorEquation_mem_kernel (i : Fin 2) :
    rationalTensorEquation A i ∈ (tensorGraphExtension F₅ ell A).ker := by
  rw [rationalTensor_kernel_span]
  exact Ideal.subset_span (Set.mem_range_self i)

theorem rationalTensorEquations_regular [Nontrivial A] :
    IsRegular (ell ⊗[F₅] A) [rationalTensorEquation A 0, rationalTensorEquation A 1] := by
  let := rationalTensorPolynomialAlgebra A
  have := rationalTensor_polynomialLocalization A
  have hs := (shiftedBivariate_regular A
    (rationalTensorBaseCoordinate A 0) (rationalTensorBaseCoordinate A 1)).toIsWeaklyRegular
  let f := (tensorGraphMap F₅ ell A).toRingHom
  have hf (p : MvPolynomial (Fin 2) A)
      (hp : p ∈ [MvPolynomial.X 0 - MvPolynomial.C (rationalTensorBaseCoordinate A 0),
        MvPolynomial.X 1 - MvPolynomial.C (rationalTensorBaseCoordinate A 1)]) :
      f (algebraMap (MvPolynomial (Fin 2) A) (ell ⊗[F₅] A) p) = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [rationalTensorEquation_polynomial]
      exact rationalTensorEquation_mem_kernel A 0
    · rw [rationalTensorEquation_polynomial]
      exact rationalTensorEquation_mem_kernel A 1
  have h := regular_localization_of_killed (rationalTensorPolynomialDenominators A) hs f hf
  simpa only [List.map_cons, List.map_nil, rationalTensorEquation_polynomial] using h

end
end Red61

/-! Formal smoothness over the perfect prime field at every actual stalk
of S. The special point uses its proved polynomial localization; the
remaining points use the retained chart kernels and their principal-open
cover. Smoothness over the original imperfect scalar field is not asserted. -/

namespace Red61.Charts

open Fields PolynomialInvariants FieldLocalization AffineGluing
noncomputable section

theorem keptKernelAtPrime_formallySmooth (i : Fin 3)
    (p : PrimeSpectrum (kernelIn (localGenerator (Contraction.kept i))
      ((chartRing (Contraction.kept i)).restrictScalars F₅))) :
    Algebra.FormallySmooth F₅ (Localization.AtPrime p.asIdeal) := by
  fin_cases i
  · have : Algebra.FormallySmooth F₅ (kernelIn (localGenerator 0) firstRing) :=
      polynomialKernel_formallySmooth (localGenerator 0) straightFirst first_independent
        first_derivatives firstRing first_polynomial_le first_localization
    exact formallySmooth_atPrime F₅ (kernelIn (localGenerator 0) firstRing) p
  · obtain ⟨a, ha⟩ := middle_kernel_cover p
    let := inclusionAlgebra
      (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
        inf_le_inf_right _ le_sup_left)
    have := middle_kernel_localization a
    have : Algebra.FormallySmooth F₅ (kernelIn (localGenerator 3) (middleRing a)) :=
      polynomialKernel_formallySmooth (localGenerator 3) (straightMiddle a) (middle_independent a)
        (middle_derivatives a) (middleRing a) (middle_polynomial_le a) (middle_localization a)
    exact formallySmooth_atPrime_of_away
      (R := F₅) (A := middleKernel) (B := kernelIn (localGenerator 3) (middleRing a))
      (middleKernelDenominator a) p ha
  · have : Algebra.FormallySmooth F₅ (kernelIn (localGenerator 5) lastRing) :=
      polynomialKernel_formallySmooth (localGenerator 5) straightLast last_independent
        last_derivatives lastRing last_polynomial_le last_localization
    exact formallySmooth_atPrime F₅ (kernelIn (localGenerator 5) lastRing) p

end
end Red61.Charts

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry PolynomialInvariants Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000

theorem s_stalk_formallySmooth (s : S) [Algebra F₅ (S.presheaf.stalk s)] :
    Algebra.FormallySmooth F₅ (S.presheaf.stalk s) := by
  by_cases hs : s = s₀
  · subst s
    let : Algebra F₅ ConeRing.B := ZMod.algebra ConeRing.B 5
    have := ConeRing.invariantLocal_formallySmooth
    exact formallySmooth_of_ringEquiv F₅ sSpecialStalkEquiv.symm (Subsingleton.elim _ _)
  · obtain ⟨i, p, rfl⟩ := s_away_special_cover s hs
    let e := kernelKeptCoordinateRingEquiv i
    have : Algebra.FormallySmooth F₅ (Localization.AtPrime (p.asIdeal.comap e.toRingHom)) :=
      keptKernelAtPrime_formallySmooth i (PrimeSpectrum.comap e.toRingHom p)
    let E := (primeLocalizationRingEquiv e p).trans
      (quotientAtlas.chartLocalizationEquivAt i.castSucc p _ rfl)
    exact formallySmooth_of_ringEquiv F₅ E (Subsingleton.elim _ _)

end
end Red61.Contraction

/-! Four-variable prime-field polynomial-localization models for
every actual surface stalk, including the special point and the middle
chart principal-open denominator. -/

namespace Red61.Charts
open Fields PolynomialInvariants FieldLocalization AffineGluing
noncomputable section

theorem keptKernelAtPrime_polynomialModel (i : Fin 3)
    (p : PrimeSpectrum (kernelIn (localGenerator (Contraction.kept i))
      ((chartRing (Contraction.kept i)).restrictScalars F₅))) :
    Nonempty (PolynomialLocalizationModel F₅ (Localization.AtPrime p.asIdeal) (Fin 4)) := by
  fin_cases i
  · exact ⟨(polynomialKernelLocalizationModel (localGenerator 0) straightFirst first_independent
      first_derivatives firstRing first_polynomial_le first_localization).atPrime p⟩
  · obtain ⟨a, ha⟩ := middle_kernel_cover p
    let := inclusionAlgebra
      (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
        inf_le_inf_right _ le_sup_left)
    have : IsScalarTower F₅ middleKernel (kernelIn (localGenerator 3) (middleRing a)) :=
      IsScalarTower.of_algHom (Subalgebra.inclusion
        (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
          inf_le_inf_right _ le_sup_left))
    have := middle_kernel_localization a
    exact ⟨(polynomialKernelLocalizationModel (localGenerator 3) (straightMiddle a)
      (middle_independent a) (middle_derivatives a) (middleRing a) (middle_polynomial_le a)
      (middle_localization a)).atPrimeOfAway (middleKernelDenominator a) p ha⟩
  · exact ⟨(polynomialKernelLocalizationModel (localGenerator 5) straightLast last_independent
      last_derivatives lastRing last_polynomial_le last_localization).atPrime p⟩
end
end Red61.Charts
namespace Red61.Contraction
open Fields Charts PolynomialInvariants
noncomputable section
set_option synthInstance.maxHeartbeats 80000

theorem s_stalk_polynomialModel_exists (s : S) [Algebra F₅ (S.presheaf.stalk s)] :
    Nonempty (PolynomialLocalizationModel F₅ (S.presheaf.stalk s) (Fin 4)) := by
  by_cases hs : s = s₀
  · subst s
    let : Algebra F₅ ConeRing.B := ZMod.algebra ConeRing.B 5
    exact ⟨ConeRing.invariantLocalPolynomialModel.transportRingEquiv sSpecialStalkEquiv.symm
      (Subsingleton.elim _ _)⟩
  · obtain ⟨i, p, rfl⟩ := s_away_special_cover s hs
    let e := kernelKeptCoordinateRingEquiv i
    obtain ⟨P⟩ := keptKernelAtPrime_polynomialModel i (PrimeSpectrum.comap e.toRingHom p)
    let E := (primeLocalizationRingEquiv e p).trans
      (quotientAtlas.chartLocalizationEquivAt i.castSucc p _ rfl)
    exact ⟨P.transportRingEquiv E (Subsingleton.elim _ _)⟩

def sStalkPrimePolynomialModel (s : S) [Algebra F₅ (S.presheaf.stalk s)] :
    PolynomialLocalizationModel F₅ (S.presheaf.stalk s) (Fin 4) :=
  Classical.choice (s_stalk_polynomialModel_exists s)
end
end Red61.Contraction

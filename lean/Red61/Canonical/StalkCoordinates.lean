import Red61.AlgebraicGeometry.StalkCoordinates
import Red61.Canonical.LocalBases

/-! # Coordinates on stalks of the retained charts

Formerly the modules `AtlasStalkScalarGeometry`, `PrimeFieldStalks`, `KeptStalkCoordinates`.
-/

/-! The native chart-to-stalk map of a principal atlas agrees with the
spectrum-of-stalk morphism, preserves the prescribed ground-field scalars,
and exhibits the actual stalk as the prime localization of the chart ring. -/

namespace Red61.AffineGluing.PrincipalAtlas
open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F)

theorem chartToStalkAt_spec (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    Spec.map (CommRingCat.ofHom (D.chartToStalkAt i p y hy)) ≫ D.chartInclusion i =
      D.glued.fromSpecStalk y := by
  subst y
  let u : Spec (CommRingCat.of (D.ring i)) ⟶ D.glued := D.chartInclusion i
  have : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (D.chartInclusion i))
  have hp : CommRingCat.ofHom (D.chartToStalkAt i p _ rfl) =
      (CommRingCat.ofHom (algebraMap (D.ring i) (Localization.AtPrime p.asIdeal)) ≫
        (Spec.stalkIso (CommRingCat.of (D.ring i)) p).inv) ≫ inv (u.stalkMap p) := rfl
  have hp' : CommRingCat.ofHom (D.chartToStalkAt i p _ rfl) =
      ((Scheme.ΓSpecIso (CommRingCat.of (D.ring i))).inv ≫
        (Spec (CommRingCat.of (D.ring i))).presheaf.germ ⊤ p trivial) ≫
          inv (u.stalkMap p) :=
    hp.trans (congrArg (fun t : CommRingCat.of (D.ring i) ⟶
      (Spec (CommRingCat.of (D.ring i))).presheaf.stalk p ↦ t ≫ inv (u.stalkMap p))
        (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of (D.ring i)) (x := p)))
  change Spec.map (CommRingCat.ofHom (D.chartToStalkAt i p _ rfl)) ≫ u =
    D.glued.fromSpecStalk (u p)
  rw [hp', Spec.map_comp, ← Spec.fromSpecStalk_eq, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk u, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id, Spec.map_id]
  exact Category.id_comp (D.glued.fromSpecStalk (u p))

theorem chartToStalkAt_scalarMap (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    (D.chartToStalkAt i p y hy).comp (algebraMap k (D.ring i)) =
      stalkScalarMap k D.toBase y := by
  let u : Spec (CommRingCat.of (D.ring i)) ⟶ D.glued := D.chartInclusion i
  let φ := CommRingCat.ofHom (D.chartToStalkAt i p y hy)
  let b := CommRingCat.ofHom (algebraMap k (D.ring i))
  have hb : u ≫ D.toBase = Spec.map b := D.chartInclusion_toBase i
  have hs : Spec.map (b ≫ φ) =
      Spec.map (CommRingCat.ofHom (stalkScalarMap k D.toBase y)) := by
    calc
      Spec.map (b ≫ φ) = Spec.map φ ≫ Spec.map b := Spec.map_comp _ _
      _ = (Spec.map φ ≫ u) ≫ D.toBase :=
        (congrArg (fun j ↦ Spec.map φ ≫ j) hb.symm).trans
          (Category.assoc (Spec.map φ) u D.toBase).symm
      _ = D.glued.fromSpecStalk y ≫ D.toBase :=
        congrArg (fun j ↦ j ≫ D.toBase) (D.chartToStalkAt_spec i p y hy)
      _ = Spec.map (CommRingCat.ofHom (stalkScalarMap k D.toBase y)) :=
        fromSpecStalk_scalar k D.toBase y
  exact congrArg (fun j : CommRingCat.of k ⟶ D.glued.presheaf.stalk y ↦ j.hom)
    (Spec.map_injective hs)

def chartLocalizationAlgEquivAt (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    letI := (D.chartToStalkAt i p y hy).toAlgebra
    Localization.AtPrime p.asIdeal ≃ₐ[D.ring i] D.glued.presheaf.stalk y := by
  subst y
  letI := (D.chartToStalkAt i p _ rfl).toAlgebra
  exact { D.chartLocalizationEquivAt i p _ rfl with commutes' := fun a ↦ rfl }

theorem chartToStalkAt_isLocalization (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (y : D.glued) (hy : y = D.chartInclusion i p) :
    letI := (D.chartToStalkAt i p y hy).toAlgebra
    IsLocalization p.asIdeal.primeCompl (D.glued.presheaf.stalk y) := by
  let := (D.chartToStalkAt i p y hy).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
    (D.chartLocalizationAlgEquivAt i p y hy)

end
end Red61.AffineGluing.PrincipalAtlas

/-! Actual prime-field algebra structures on source and target stalks, and
their compatibility with the contraction. These use injective field maps,
not a presumed coefficient field inside a local ring. -/

namespace Red61

open Fields AlgebraicGeometry
noncomputable section

@[instance_reducible]
def primeAlgebraOfEmbedding (A : Type*) [CommRing A] (f : A →+* L)
    (hf : Function.Injective f) : Algebra F₅ A := by
  have : CharP A 5 := f.charP hf 5
  exact ZMod.algebra A 5

theorem primeAlgebra_tower (A B : Type*) [CommRing A] [CommRing B]
    [Algebra F₅ A] [Algebra F₅ B] [Algebra A B] : IsScalarTower F₅ A B :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

namespace Contraction

def sStalkFieldMap (x : S) : S.presheaf.stalk x →+* L :=
  letI := functionFieldAlgebra ell sToBase
  sFunctionFieldEquiv.toRingHom.comp (algebraMap (S.presheaf.stalk x) S.functionField)

theorem sStalkFieldMap_injective (x : S) : Function.Injective (sStalkFieldMap x) := by
  let := functionFieldAlgebra ell sToBase
  exact sFunctionFieldEquiv.injective.comp
    (IsFractionRing.injective (S.presheaf.stalk x) S.functionField)

@[instance_reducible]
def sStalkPrimeAlgebra (x : S) : Algebra F₅ (S.presheaf.stalk x) :=
  primeAlgebraOfEmbedding _ (sStalkFieldMap x) (sStalkFieldMap_injective x)

@[instance_reducible]
def resolvedStalkPrimeAlgebra (y : Charts.resolvedQuotient) :
    Algebra F₅ (Charts.resolvedQuotient.presheaf.stalk y) :=
  primeAlgebraOfEmbedding _ (resolvedStalkFieldMap y) (resolvedStalkFieldMap_injective y)

end Contraction
end
end Red61

/-! Explicit coordinate differential bases in the actual retained-chart
stalks of S. Their images in the fixed ambient field are proved, including
the middle chart's principal-open choice and its denominator condition. -/

namespace Red61.Contraction

open Fields Charts Module AffineGluing PolynomialInvariants AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Algebra ell S.functionField := functionFieldAlgebra ell sToBase

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

def sFieldAmbientMap : S.functionField →+* K :=
  L.subtype.comp sFunctionFieldEquiv.toRingHom

def sStalkAmbientMap (s : S) : S.presheaf.stalk s →+* K :=
  L.subtype.comp (sStalkFieldMap s)

theorem sFieldAmbientMap_injective : Function.Injective sFieldAmbientMap :=
  L.subtype_injective.comp sFunctionFieldEquiv.injective

theorem sStalkAmbientMap_algebraMap (s : S) (a : S.presheaf.stalk s) :
    sFieldAmbientMap (algebraMap (S.presheaf.stalk s) S.functionField a) =
      sStalkAmbientMap s a := rfl

structure StalkCoordinateData (s : S) (v : Fin 4 → K) where
  coordinates : Fin 4 → S.presheaf.stalk s
  basis : Basis (Fin 4) (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s)
  differential (i : Fin 4) : basis i = KaehlerDifferential.D ℤ (S.presheaf.stalk s) (coordinates i)
  embedding (i : Fin 4) : sStalkAmbientMap s (coordinates i) = v i

theorem s_chart_field_identification (i : Fin 4) [IsFractionRing (quotientAtlas.ring i) L] :
    (quotientAtlas.functionFieldChartEquiv i).trans
      (affineFunctionFieldEquiv (CommRingCat.of (quotientAtlas.ring i)) L) =
        sFunctionFieldEquiv.toRingEquiv := by
  have : IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L := invariantChart_isFractionRing 0
  exact quotientAtlas.functionField_identification_independent i (0 : Fin 4)

theorem quotientChartToStalk_ambient (i : Fin 4) [IsFractionRing (quotientAtlas.ring i) L]
    (p : PrimeSpectrum (quotientAtlas.ring i)) (s : S)
    (hs : s = quotientAtlas.chartInclusion i p) (a : quotientAtlas.ring i) :
    sStalkAmbientMap s (quotientAtlas.chartToStalkAt i p s hs a) = ((a : L) : K) :=
  congrArg (fun z : L ↦ (z : K))
    (quotientAtlas.chartToStalkAt_embedding i p s hs sFunctionFieldEquiv.toRingEquiv
      (s_chart_field_identification i) a)

def keptCoordinateRingEquiv (i : Fin 3) :
    invariantChartRing (kept i) ≃+* quotientAtlas.ring i.castSucc :=
  (Subalgebra.equivOfEq _ _ (quotient_common_chart_eq i).symm).toRingEquiv

theorem keptCoordinateRingEquiv_coe (i : Fin 3) (x : invariantChartRing (kept i)) :
    (keptCoordinateRingEquiv i x : L) = (x : L) :=
  subalgebra_equivOfEq_coe _ _ (quotient_common_chart_eq i).symm x

def kernelKeptCoordinateRingEquiv (i : Fin 3) :
    kernelIn (localGenerator (kept i)) ((chartRing (kept i)).restrictScalars F₅) ≃+*
      quotientAtlas.ring i.castSucc :=
  (chartKernelInEquiv (kept i)).trans (keptCoordinateRingEquiv i)

theorem kernelKeptCoordinateRingEquiv_coe (i : Fin 3)
    (x : kernelIn (localGenerator (kept i)) ((chartRing (kept i)).restrictScalars F₅)) :
    ((kernelKeptCoordinateRingEquiv i x : L) : K) = (x : K) :=
  (congrArg (fun z : L ↦ (z : K))
    (keptCoordinateRingEquiv_coe i (chartKernelInEquiv (kept i) x))).trans
      (chartKernelInEquiv_coe (kept i) x)

theorem keptFirstStalkCoordinateData (p : PrimeSpectrum (quotientAtlas.ring (0 : Fin 4)))
    (s : S) (hs : s = quotientAtlas.chartInclusion (0 : Fin 4) p) :
    Nonempty (StalkCoordinateData s (powerCoordinates straightFirst)) := by
  have : IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L := invariantChart_isFractionRing 0
  let A := kernelIn (localGenerator 0) firstRing
  let e : A ≃+* quotientAtlas.ring (0 : Fin 4) :=
    kernelKeptCoordinateRingEquiv 0
  let p₀ := PrimeSpectrum.comap e.toRingHom p
  let eR : Localization.AtPrime p₀.asIdeal ≃+* S.presheaf.stalk s :=
    (primeLocalizationRingEquiv e p).trans
      (quotientAtlas.chartLocalizationEquivAt (0 : Fin 4) p s hs)
  have hA (x : A) :
      sStalkAmbientMap s (eR (algebraMap A (Localization.AtPrime p₀.asIdeal) x)) = (x : K) := by
    change sStalkAmbientMap s (quotientAtlas.chartLocalizationEquivAt (0 : Fin 4) p s hs
      (primeLocalizationRingEquiv e p (algebraMap A (Localization.AtPrime p₀.asIdeal) x))) = _
    exact (congrArg (fun z ↦ sStalkAmbientMap s
      (quotientAtlas.chartLocalizationEquivAt (0 : Fin 4) p s hs z))
        (primeLocalizationRingEquiv_algebraMap e p x)).trans
      ((congrArg (sStalkAmbientMap s)
        (quotientAtlas.chartLocalizationEquivAt_algebraMap (0 : Fin 4) p s hs (e x))).trans
          ((quotientChartToStalk_ambient 0 p s hs (e x)).trans
            (kernelKeptCoordinateRingEquiv_coe 0 x)))
  obtain ⟨f, b, hb, hf⟩ := differentialCoordinatesAtPrime_transport_direct
    (A := A) (R := S.presheaf.stalk s) (F := K) (ι := Fin 4)
    p₀ firstKernelAbsoluteDifferentialBasis keptFirstKernelCoordinates
    firstKernelAbsoluteDifferentialBasis_apply eR (sStalkAmbientMap s) A.val.toRingHom hA
  exact ⟨⟨fun i ↦ f (keptFirstKernelCoordinates i), b, hb,
    fun i ↦ (hf _).trans (keptFirstKernelCoordinates_coe i)⟩⟩

theorem keptLastStalkCoordinateData (p : PrimeSpectrum (quotientAtlas.ring (2 : Fin 4)))
    (s : S) (hs : s = quotientAtlas.chartInclusion (2 : Fin 4) p) :
    Nonempty (StalkCoordinateData s (powerCoordinates straightLast)) := by
  have : IsFractionRing (quotientAtlas.ring (2 : Fin 4)) L := invariantChart_isFractionRing 5
  let A := kernelIn (localGenerator 5) lastRing
  let e : A ≃+* quotientAtlas.ring (2 : Fin 4) :=
    kernelKeptCoordinateRingEquiv 2
  let p₀ := PrimeSpectrum.comap e.toRingHom p
  let eR : Localization.AtPrime p₀.asIdeal ≃+* S.presheaf.stalk s :=
    (primeLocalizationRingEquiv e p).trans
      (quotientAtlas.chartLocalizationEquivAt (2 : Fin 4) p s hs)
  have hA (x : A) :
      sStalkAmbientMap s (eR (algebraMap A (Localization.AtPrime p₀.asIdeal) x)) = (x : K) := by
    change sStalkAmbientMap s (quotientAtlas.chartLocalizationEquivAt (2 : Fin 4) p s hs
      (primeLocalizationRingEquiv e p (algebraMap A (Localization.AtPrime p₀.asIdeal) x))) = _
    exact (congrArg (fun z ↦ sStalkAmbientMap s
      (quotientAtlas.chartLocalizationEquivAt (2 : Fin 4) p s hs z))
        (primeLocalizationRingEquiv_algebraMap e p x)).trans
      ((congrArg (sStalkAmbientMap s)
        (quotientAtlas.chartLocalizationEquivAt_algebraMap (2 : Fin 4) p s hs (e x))).trans
          ((quotientChartToStalk_ambient 2 p s hs (e x)).trans
            (kernelKeptCoordinateRingEquiv_coe 2 x)))
  obtain ⟨f, b, hb, hf⟩ := differentialCoordinatesAtPrime_transport_direct
    (A := A) (R := S.presheaf.stalk s) (F := K) (ι := Fin 4)
    p₀ lastKernelAbsoluteDifferentialBasis keptLastKernelCoordinates
    lastKernelAbsoluteDifferentialBasis_apply eR (sStalkAmbientMap s) A.val.toRingHom hA
  exact ⟨⟨fun i ↦ f (keptLastKernelCoordinates i), b, hb,
    fun i ↦ (hf _).trans (keptLastKernelCoordinates_coe i)⟩⟩

@[instance_reducible] def keptMiddleOpenAlgebra (a : F₅) :
    Algebra middleKernel (kernelIn (localGenerator 3) (middleRing a)) :=
  inclusionAlgebra
    (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
      inf_le_inf_right _ le_sup_left)

set_option maxHeartbeats 800000 in
theorem keptMiddleStalkCoordinateData (p : PrimeSpectrum (quotientAtlas.ring (1 : Fin 4)))
    (s : S) (hs : s = quotientAtlas.chartInclusion (1 : Fin 4) p) :
    ∃ a : F₅, Nonempty (StalkCoordinateData s (powerCoordinates (straightMiddle a))) := by
  have : IsFractionRing (quotientAtlas.ring (1 : Fin 4)) L := invariantChart_isFractionRing 3
  let e : middleKernel ≃+* quotientAtlas.ring (1 : Fin 4) :=
    kernelKeptCoordinateRingEquiv 1
  let p₀ := PrimeSpectrum.comap e.toRingHom p
  obtain ⟨a, ha⟩ := middle_kernel_cover p₀
  let eR : Localization.AtPrime p₀.asIdeal ≃+* S.presheaf.stalk s :=
    (primeLocalizationRingEquiv e p).trans
      (quotientAtlas.chartLocalizationEquivAt (1 : Fin 4) p s hs)
  let := keptMiddleOpenAlgebra a
  have := middle_kernel_localization a
  have hA (x : middleKernel) :
      sStalkAmbientMap s (eR (algebraMap middleKernel (Localization.AtPrime p₀.asIdeal) x)) =
        (x : K) := by
    change sStalkAmbientMap s (quotientAtlas.chartLocalizationEquivAt (1 : Fin 4) p s hs
      (primeLocalizationRingEquiv e p
        (algebraMap middleKernel (Localization.AtPrime p₀.asIdeal) x))) = _
    exact (congrArg (fun z ↦ sStalkAmbientMap s
      (quotientAtlas.chartLocalizationEquivAt (1 : Fin 4) p s hs z))
        (primeLocalizationRingEquiv_algebraMap e p x)).trans
      ((congrArg (sStalkAmbientMap s)
        (quotientAtlas.chartLocalizationEquivAt_algebraMap (1 : Fin 4) p s hs (e x))).trans
          ((quotientChartToStalk_ambient 1 p s hs (e x)).trans
            (kernelKeptCoordinateRingEquiv_coe 1 x)))
  have hAopen (x : middleKernel) :
      sStalkAmbientMap s (eR (algebraMap middleKernel (Localization.AtPrime p₀.asIdeal) x)) =
        (kernelIn (localGenerator 3) (middleRing a)).val.toRingHom
          (algebraMap middleKernel (kernelIn (localGenerator 3) (middleRing a)) x) := by
    exact (hA x).trans (inclusionAlgebra_coe
      (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
        inf_le_inf_right _ le_sup_left) x).symm
  obtain ⟨f, b, hb, hf⟩ := differentialCoordinatesAtPrime_transport
    (A := middleKernel) (B := kernelIn (localGenerator 3) (middleRing a))
    (R := S.presheaf.stalk s) (F := K) (ι := Fin 4)
    (middleKernelDenominator a) p₀ ha (middleOpenKernelAbsoluteDifferentialBasis a)
    (keptMiddleOpenCoordinates a) (middleOpenKernelAbsoluteDifferentialBasis_apply a)
    eR (sStalkAmbientMap s) (kernelIn (localGenerator 3) (middleRing a)).val.toRingHom hAopen
  refine ⟨a, ⟨{
    coordinates := fun i ↦ f (keptMiddleOpenCoordinates a i)
    basis := b
    differential := hb
    embedding := fun i ↦ (hf _).trans (keptMiddleOpenCoordinates_coe a i) }⟩⟩

end
end Red61.Contraction

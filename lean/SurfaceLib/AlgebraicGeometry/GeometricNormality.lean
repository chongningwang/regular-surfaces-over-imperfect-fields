import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Red61.AlgebraicGeometry.StalkCoordinates

/-! # Geometric normality

A scheme is normal when all of its local rings are integrally closed domains. A scheme over a
field `ℓ` is not geometrically normal as soon as one affine open `Spec C` over `ℓ` has a base
change `C ⊗[ℓ] ℓ'`, for some field extension `ℓ'`, that is a domain but is not integrally closed:
`Spec (C ⊗[ℓ] ℓ')` is an open subscheme of the base change of the scheme.
-/

namespace SurfaceLib

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A normal scheme: every local ring is an integrally closed domain. -/
def IsNormalScheme : ObjectProperty Scheme :=
  fun X ↦ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- A scheme over `ℓ` with an affine open `Spec C` over `ℓ` is not geometrically normal when
`C ⊗[ℓ] ℓ'` is isomorphic to a domain that is not integrally closed. -/
theorem not_geometrically_normal_of_open {ℓ ℓ' : Type} [Field ℓ] [Field ℓ'] [Algebra ℓ ℓ']
    {X : Scheme} (b : X ⟶ Spec (CommRingCat.of ℓ)) {C : Type} [CommRing C] [Algebra ℓ C]
    (j : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap ℓ C)))
    {R : Type} [CommRing R] [IsDomain R] (e : C ⊗[ℓ] ℓ' ≃+* R) (hR : ¬ IsIntegrallyClosed R) :
    ¬ geometrically IsNormalScheme b := by
  intro hG
  let y : Spec (CommRingCat.of ℓ') ⟶ Spec (CommRingCat.of ℓ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℓ ℓ'))
  let Z := Limits.pullback b y
  have hZ : IsNormalScheme Z :=
    hG y (Limits.pullback.fst b y) (Limits.pullback.snd b y) (.of_hasPullback _ _)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℓ C ℓ')
  have hZsq : IsPullback (Limits.pullback.fst b y) (Limits.pullback.snd b y) b y :=
    .of_hasPullback _ _
  let P := CommRingCat.of (C ⊗[ℓ] ℓ')
  let pr₁ : Spec P ⟶ Spec (CommRingCat.of C) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom))
  let pr₂ : Spec P ⟶ Spec (CommRingCat.of ℓ') := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight.toRingHom))
  have hw : (pr₁ ≫ j) ≫ b = pr₂ ≫ y := by
    rw [Category.assoc, hj]
    exact hsq.w
  let ι : Spec P ⟶ Z := Limits.pullback.lift (pr₁ ≫ j) pr₂ hw
  have hι₁ : ι ≫ Limits.pullback.fst b y = pr₁ ≫ j := Limits.pullback.lift_fst _ _ _
  have hι₂ : ι ≫ Limits.pullback.snd b y = pr₂ := Limits.pullback.lift_snd _ _ _
  have hwhole : IsPullback (ι ≫ Limits.pullback.snd b y) pr₁ y (j ≫ b) := by
    rw [hι₂, hj]
    exact hsq.flip
  have hleft : IsPullback ι pr₁ (Limits.pullback.fst b y) j :=
    IsPullback.of_right hwhole hι₁ hZsq.flip
  have hopen : IsOpenImmersion ι :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hleft.flip inferInstance
  have hloc (m : PrimeSpectrum (C ⊗[ℓ] ℓ')) :
      IsIntegrallyClosed (Localization.AtPrime m.asIdeal) := by
    have hint := (hZ (ι m)).2
    have h1 : IsIntegrallyClosed ((Spec P).presheaf.stalk m) :=
      IsIntegrallyClosed.of_equiv (asIso (ι.stalkMap m)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (Spec.stalkIso P m).commRingCatIsoToRingEquiv
  apply hR
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : PrimeSpectrum R := ⟨p, hp.isPrime⟩
  have h2 : IsIntegrallyClosed (Localization.AtPrime (q.asIdeal.comap e.toRingHom)) :=
    hloc (PrimeSpectrum.comap e.toRingHom q)
  exact @IsIntegrallyClosed.of_equiv _ _ _ _ (Red61.primeLocalizationRingEquiv e q) h2

end
end SurfaceLib

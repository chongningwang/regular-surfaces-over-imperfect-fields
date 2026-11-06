import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Red61.Surface.Field

/-! A tensor-product witness of nonreducedness gives an actual scheme-theoretic obstruction. -/

namespace Red61

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section

/-- Reducedness after scalar extension survives localization of the original algebra. -/
theorem tensor_reduced_of_localization
    (F A Q E : Type) [CommRing F] [CommRing A] [CommRing Q] [CommRing E]
    [Algebra F A] [Algebra F Q] [Algebra A Q] [IsScalarTower F A Q] [Algebra F E]
    (M : Submonoid A) [IsLocalization M Q] [_root_.IsReduced (A ⊗[F] E)] :
    _root_.IsReduced (Q ⊗[F] E) := by
  let φ : A ⊗[F] E →ₐ[A] Q ⊗[F] E :=
    Algebra.TensorProduct.map (Algebra.ofId A Q) (.id F E)
  let := φ.toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[F] E) M) (Q ⊗[F] E) := by
    apply IsLocalization.tensorProduct_tensorProduct F E M Q
    ext x
    simp [φ, RingHom.algebraMap_toAlgebra]
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (A ⊗[F] E) M) (Q ⊗[F] E) inferInstance

theorem spec_not_geometricallyReduced_of_tensor
    (F A E : Type) [Field F] [CommRing A] [Field E] [Algebra F A] [Algebra F E]
    (h : ¬ _root_.IsReduced (A ⊗[F] E)) :
    ¬ GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap F A))) := by
  intro hf
  have : IsReduced (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap F A)))
      (Spec.map (CommRingCat.ofHom (algebraMap F E)))) :=
    hf.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  have : IsReduced (Spec (CommRingCat.of (A ⊗[F] E))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso F A E).inv
  exact h ((affine_isReduced_iff (CommRingCat.of (A ⊗[F] E))).mp inferInstance)

/-- Nonreduced scalar extension of a fraction field obstructs geometric reducedness of Spec A. -/
theorem spec_not_geometricallyReduced_of_fraction
    (F A Q E : Type) [Field F] [CommRing A] [Field Q] [Field E]
    [Algebra F A] [Algebra F Q] [Algebra A Q] [IsScalarTower F A Q]
    [IsFractionRing A Q] [Algebra F E] (h : ¬ _root_.IsReduced (Q ⊗[F] E)) :
    ¬ GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap F A))) := by
  apply spec_not_geometricallyReduced_of_tensor F A E
  intro hA
  let := hA
  exact h (tensor_reduced_of_localization F A Q E (nonZeroDivisors A))

/-- Restriction to an open subscheme preserves geometric reducedness. -/
theorem geometricallyReduced_open {X Y S : Scheme} (f : X ⟶ S) (j : Y ⟶ X)
    [IsOpenImmersion j] (hf : GeometricallyReduced f) : GeometricallyReduced (j ≫ f) := by
  constructor
  intro E _ y Z a b h
  have : IsReduced (pullback f y) := hf.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  let q : Z ⟶ pullback f y :=
    (IsPullback.of_hasPullback f y).lift (a ≫ j) b (by rw [Category.assoc, h.w])
  have hq : IsPullback a q j (pullback.fst f y) :=
    h.of_bot' (.of_hasPullback f y)
  have : IsOpenImmersion q := MorphismProperty.of_isPullback hq inferInstance
  exact isReduced_of_isOpenImmersion q

/-- A fraction-field tensor witness on one affine open obstructs geometric reducedness globally. -/
theorem not_geometricallyReduced_of_affine_fraction
    (F A Q E : Type) [Field F] [CommRing A] [Field Q] [Field E]
    [Algebra F A] [Algebra F Q] [Algebra A Q] [IsScalarTower F A Q]
    [IsFractionRing A Q] [Algebra F E]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F))
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F A)))
    (h : ¬ _root_.IsReduced (Q ⊗[F] E)) : ¬ GeometricallyReduced f := by
  intro hf
  have hjf := geometricallyReduced_open f j hf
  rw [hj] at hjf
  exact spec_not_geometricallyReduced_of_fraction F A Q E h hjf

namespace Fields

end Fields
end
end Red61

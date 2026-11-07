import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Para-abelian varieties and the classical rigidity input

A para-abelian variety is a proper scheme whose base change to an algebraic closure carries the
structure of a proper geometrically integral group scheme. This is the class used for the Albanese
variety over a non-closed field. `ClassicalRationalRigidity` is an explicit hypothesis, with no
supplied inhabitant: it is the classical statement that maps from the affine plane to a para-abelian
variety are constant. See `SurfaceLib/Abelian/README.md`.
-/

namespace SurfaceLib.Abelian

open AlgebraicGeometry CategoryTheory
open scoped MonoidalCategory

/-- A para-abelian variety over a field. -/
def IsParaAbelianVariety (F : Type) [Field F] {P : Scheme.{0}} (π : P ⟶ Spec (.of F)) : Prop :=
  IsProper π ∧ ∃ (G : Over (Spec (.of (AlgebraicClosure F)))) (_ : GrpObj G) (fst : G.left ⟶ P),
    IsProper G.hom ∧ GeometricallyIntegral G.hom ∧
      IsPullback fst G.hom π (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))

/-- Classical rigidity: morphisms from an affine plane to a para-abelian variety are constant. -/
structure ClassicalRationalRigidity : Prop where
  constant : ∀ (F : Type) [Field F] {P : Scheme.{0}} (π : P ⟶ Spec (.of F)),
    IsParaAbelianVariety F π →
    ∀ (E : Type) [Field E] [Algebra F E]
      (φ : Spec (.of (MvPolynomial (Fin 2) E)) ⟶ P),
      φ ≫ π = Spec.map (CommRingCat.ofHom (algebraMap F (MvPolynomial (Fin 2) E))) →
      ∃ p : Spec (.of E) ⟶ P,
        φ = Spec.map (CommRingCat.ofHom (MvPolynomial.C : E →+* MvPolynomial (Fin 2) E)) ≫ p

/-- The point `Spec F` is itself a para-abelian variety: it is the trivial abelian variety. -/
theorem isParaAbelianVariety_id (F : Type) [Field F] :
    IsParaAbelianVariety F (𝟙 (Spec (.of F))) := by
  let S := Spec (.of (AlgebraicClosure F))
  have hint : GeometricallyIntegral (𝟙 S) := ⟨by
    intro K _ y Z fst snd h
    have hiso : IsIso snd := h.isIso_snd_of_isIso
    have hne : Nonempty Z := ⟨(inv snd) (⊥ : PrimeSpectrum K)⟩
    exact isIntegral_of_isOpenImmersion snd⟩
  refine ⟨inferInstance, 𝟙_ (Over S), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))), inferInstanceAs (IsProper (𝟙 S)),
    hint, ?_⟩
  have hiso : IsIso (𝟙_ (Over S)).hom := inferInstanceAs (IsIso (𝟙 S))
  have hsq : CommSq (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))
      (𝟙_ (Over S)).hom (𝟙 (Spec (.of F)))
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))) :=
    ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩
  exact IsPullback.of_vert_isIso hsq

/-- The universal property of the Albanese morphism over a field, from para-abelian varieties. -/
structure IsAlbaneseMorphism {F : Type} [Field F] {X P : Scheme.{0}} (f : X ⟶ Spec (.of F))
    (π : P ⟶ Spec (.of F)) (a : X ⟶ P) : Prop where
  target : IsParaAbelianVariety F π
  overBase : a ≫ π = f
  universal : ∀ {Q : Scheme.{0}} (ρ : Q ⟶ Spec (.of F)), IsParaAbelianVariety F ρ →
    ∀ g : X ⟶ Q, g ≫ ρ = f → ∃! φ : P ⟶ Q, φ ≫ ρ = π ∧ a ≫ φ = g

end SurfaceLib.Abelian

import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Red61.Surface.Properties

/-! # Scalars and valuations at the special point

Formerly the modules `GeometricMonomialValuations`, `SpecialPointScalars`, `StalkSpecScalars`, `AffineOpenStalk`.
-/

/-! Monomial valuation filtrations on the actual local ring O_(S,s0), with
regular parameters and compatibility with pullback by the actual contraction. -/

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry CategoryTheory IsLocalRing WeightedFiltration
noncomputable section

abbrev SpecialLocalRing := S.presheaf.stalk s₀

def specialU : SpecialLocalRing := sSpecialStalkEquiv.symm ConeRing.uB
def specialR : SpecialLocalRing := sSpecialStalkEquiv.symm ConeRing.rB

theorem special_parameters_generate :
    maximalIdeal SpecialLocalRing = Ideal.span ({specialU,specialR} : Set SpecialLocalRing) := by
  calc
    _ = (maximalIdeal ConeRing.B).map sSpecialStalkEquiv.symm :=
      (IsLocalRing.map_ringEquiv_maximalIdeal sSpecialStalkEquiv.symm).symm
    _ = _ := by
      rw [ConeRing.maximalIdeal_eq_parameters, ConeRing.invariantParameterIdeal, Ideal.map_span]
      simp only [Set.image_insert_eq, Set.image_singleton]
      rfl

def specialResidue : SpecialLocalRing →+* k :=
  ConeRing.residueB.toRingHom.comp sSpecialStalkEquiv.toRingHom

theorem specialResidue_surjective : Function.Surjective specialResidue :=
  ConeRing.residueB_surjective.comp sSpecialStalkEquiv.surjective

theorem special_maximal_eq_residue_kernel : maximalIdeal SpecialLocalRing = RingHom.ker specialResidue :=
  (IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective specialResidue specialResidue_surjective)).symm

end
end Red61.Contraction

/-! The actual ell-algebra structure on the special stalk agrees with the
concrete invariant ring. Its residue field is k as an ell-algebra. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

def stalkScalarMap (F : Type) [Field F] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F)) (x : X) : F →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by trivial)).hom.comp (globalScalarMap F f)

namespace Contraction

open Fields

end Contraction
end
end Red61

/-! The canonical map from the spectrum of a stalk is compatible with
the scalar map induced by the specified structure morphism. Both the
global and stalk statements use the native spectrum adjunction maps. -/

namespace Red61
open AlgebraicGeometry CategoryTheory
noncomputable section

variable (F : Type) [Field F] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of F))

theorem schemeToSpec_globalScalar :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (globalScalarMap F f)) = f := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  simp

theorem fromSpecStalk_scalar (x : X) :
    X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom (stalkScalarMap F f x)) := by
  conv_lhs => rw [← schemeToSpec_globalScalar F f]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

end
end Red61

/-! Every affine open immersion gives the actual prime-localization
identification of its scheme stalks. The coordinate map agrees with the
native spectrum-of-stalk morphism, without atlas-specific assumptions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CommRing A] {X : Scheme}
  (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum A)

def affineOpenStalkEquiv : X.presheaf.stalk (j p) ≃+* Localization.AtPrime p.asIdeal :=
  (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv

/-- The coordinate map to an actual target stalk of an affine open immersion. -/
def affineOpenToStalk : A →+* X.presheaf.stalk (j p) :=
  (affineOpenStalkEquiv j p).symm.toRingHom.comp
    (algebraMap A (Localization.AtPrime p.asIdeal))

/-- The affine localization and the actual target stalk agree as coordinate algebras. -/
def affineOpenLocalizationAlgEquiv :
    letI := (affineOpenToStalk j p).toAlgebra
    Localization.AtPrime p.asIdeal ≃ₐ[A] X.presheaf.stalk (j p) := by
  letI := (affineOpenToStalk j p).toAlgebra
  exact { (affineOpenStalkEquiv j p).symm with commutes' _ := rfl }

theorem affineOpenToStalk_isLocalization :
    letI := (affineOpenToStalk j p).toAlgebra
    IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk (j p)) := by
  let := (affineOpenToStalk j p).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
    (affineOpenLocalizationAlgEquiv j p)

end
end Red61

import Eff.YAlbanese
import Eff.YCanonical
import Eff.YNonnormal
import Eff.Projective

/-! # The order-five example

`Eff.y_example` collects what is proved without any classical input. `Eff.case_C_p5` adds the
canonical sheaf and the Albanese morphism, using the two explicit general classical parameters.
The relation `K_Y ≡ 0` is the immediate consequence of `5 K_Y ∼ 0`; numerical equivalence is not
formalized separately.
-/

namespace Eff

open Red61 Red61.Fields Red61.Contraction AlgebraicGeometry CategoryTheory
  SurfaceLib.Abelian SurfaceLib.Canonical SurfaceLib.LineBundle SurfaceLib.Projective
noncomputable section

/-- The field of constants `ell` is a rational function field in two variables, and `Y` is a regular
projective integral surface over it, with constants `ell` and geometrically non-normal. The explicit
determinant line of its differentials has exact order five. -/
theorem y_example :
    Nonempty (FractionRing (MvPolynomial (Fin 2) (ZMod 5)) ≃+* ell) ∧
      IsProjectiveOver ell yToBase ∧ IsProper yToBase ∧ IsIntegral Y ∧
      topologicalKrullDim Y = 2 ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      Function.Bijective (globalScalarMap ell yToBase) ∧
      (∀ n, Nonempty (tensorPower yOmega n ≅ structureSheafModule Y) ↔ 5 ∣ n) ∧
      ¬ geometrically IsNormalScheme yToBase :=
  ⟨⟨baseEquiv⟩, y_projective, y_proper, y_integral, y_dimension, y_stalk_regular,
    y_globalScalarMap_bijective, omega_tensorPower_trivial_iff, y_not_geometrically_normal⟩

/-- Example `ex:case-C-p5`: `Y` has a canonical sheaf, every canonical sheaf has exact order five, and
the Albanese morphism of `Y` is the structure morphism to the point `Spec ell`. -/
theorem case_C_p5 (adjunction : ClassicalAdjunction) (rigidity : ClassicalRationalRigidity) :
    (∃ K : Y.Modules, Nonempty (TopDuality ell yToBase 2 K)) ∧
      (∀ (K : Y.Modules) (_ : TopDuality ell yToBase 2 K) (n : ℕ),
        Nonempty (tensorPower K n ≅ structureSheafModule Y) ↔ 5 ∣ n) ∧
      IsAlbaneseMorphism yToBase (𝟙 _) yToBase :=
  ⟨⟨yOmega, ⟨yDifferentialLineDuality adjunction⟩⟩,
    fun K DK n ↦ canonicalSheaf_tensorPower_trivial_iff adjunction K DK n,
    y_albanese_is_base rigidity⟩

end
end Eff

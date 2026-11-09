import Eff.Canonical
import Eff.Projective

/-! # Theorem 6.1 of the red paper

`Eff.s_example` collects what is proved about `S` with no classical input. `Eff.theorem_6_1` adds the
canonical sheaf, using the explicit general classical parameter. The `Red61` theorem and its audit
are not changed.
-/

namespace Eff

open Red61 Red61.Fields Red61.Contraction AlgebraicGeometry CategoryTheory
  SurfaceLib.Canonical SurfaceLib.Projective
noncomputable section

/-- The field of constants `ell` is a rational function field in two variables, and `S` is a regular
projective integral surface over it, with constants `ell` and geometrically non-reduced. -/
theorem s_example :
    Nonempty (FractionRing (MvPolynomial (Fin 2) (ZMod 5)) ≃+* ell) ∧
      IsProjectiveOver ell sToBase ∧ IsProper sToBase ∧ IsIntegral S ∧
      topologicalKrullDim S = 2 ∧
      (∀ s : S, IsRegularLocalRing (S.presheaf.stalk s)) ∧
      Function.Bijective (globalScalarMap ell sToBase) ∧ ¬ GeometricallyReduced sToBase :=
  ⟨⟨baseEquiv⟩, s_projective, s_proper, s_integral, s_dimension, s_stalk_regular,
    s_globalScalarMap_bijective, s_not_geometricallyReduced⟩

/-- Theorem 6.1: `S` has a canonical sheaf, and every canonical sheaf is trivial, so it has degree
zero on every proper integral curve. -/
theorem theorem_6_1 (adjunction : ClassicalAdjunction) :
    (∃ K : S.Modules, Nonempty (TopDuality ell sToBase 2 K)) ∧
      ∀ (K : S.Modules) (_ : TopDuality ell sToBase 2 K),
        Nonempty (K ≅ structureSheafModule S) ∧ IsCurveNumericallyTrivial ell sToBase K :=
  ⟨(Eff.Canonical.exists_trivial_canonicalSheaf adjunction).imp fun _ h ↦ h.1, fun K DK ↦
    ⟨Eff.Canonical.canonicalSheaf_trivial adjunction K DK,
      Eff.Canonical.canonicalSheaf_curveNumericallyTrivial adjunction K DK⟩⟩

end
end Eff

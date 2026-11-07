import Red61.Theorem61
import SurfaceLib.Canonical.ClassicalAdjunction

/-! # Canonical triviality of the input surface, with an explicit classical parameter

This does not change the unconditional `Red61` theorem. Given the general classical
adjunction/duality input, the existing differential line is a canonical sheaf in the
independent top-duality sense. Uniqueness then gives a genuine global sheaf isomorphism
from every such canonical sheaf to the structure sheaf. No projectivity input is needed.
-/

namespace Eff.Canonical

open Red61 Red61.Fields Red61.Contraction SurfaceLib.Canonical
  AlgebraicGeometry CategoryTheory
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5

/-- Essential finite generation of the actual base field over the prime field. -/
theorem ell_essFiniteType : Algebra.EssFiniteType F₅ ell := by
  have : Algebra.EssFiniteType P₂ k := .of_isLocalization k (nonZeroDivisors P₂)
  have : Algebra.EssFiniteType F₅ k := .comp F₅ P₂ k
  let e : k ≃ₐ[F₅] ell :=
    { baseEquiv with
      commutes' := fun a ↦ RingHom.congr_fun
        (show baseEquiv.toRingHom.comp (algebraMap F₅ k) = algebraMap F₅ ell from
          Subsingleton.elim _ _) a }
  exact Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective

private local instance : Algebra.EssFiniteType F₅ ell := ell_essFiniteType

/-- The only use of the external classical input: establish normalized duality for the
already defined differential line, using the hypotheses proved for the actual surface. -/
def differentialLineDuality (adjunction : ClassicalAdjunction) :
    TopDuality ell sToBase 2 (omega ell sToBase ellAbsoluteDifferentialBasis) :=
  Classical.choice (adjunction.normalizedDuality ell sToBase ellAbsoluteDifferentialBasis
    s_dimension s_stalk_regular sAbsoluteDifferentials_isLocallyFreeOfRank)

/-- Comparison with any independently characterized canonical sheaf. -/
def canonicalComparison (adjunction : ClassicalAdjunction) (K : S.Modules)
    (DK : TopDuality ell sToBase 2 K) :
    K ≅ omega ell sToBase ellAbsoluteDifferentialBasis :=
  comparisonIso DK (differentialLineDuality adjunction)

/-- The canonical sheaf of the input surface is trivial, conditional only on the
explicit general classical input. The final map composes with the existing Red61 proof. -/
def canonicalSheafIsoStructureSheaf (adjunction : ClassicalAdjunction) (K : S.Modules)
    (DK : TopDuality ell sToBase 2 K) : K ≅ structureSheafModule S :=
  canonicalComparison adjunction K DK ≪≫
    omegaIsoStructureSheaf ell sToBase ellAbsoluteDifferentialBasis

theorem canonicalSheaf_trivial (adjunction : ClassicalAdjunction) (K : S.Modules)
    (DK : TopDuality ell sToBase 2 K) : Nonempty (K ≅ structureSheafModule S) :=
  ⟨canonicalSheafIsoStructureSheaf adjunction K DK⟩

/-- Existence of a trivial canonical sheaf in the independent top-duality sense. -/
theorem exists_trivial_canonicalSheaf (adjunction : ClassicalAdjunction) :
    ∃ K : S.Modules, Nonempty (TopDuality ell sToBase 2 K) ∧
      Nonempty (K ≅ structureSheafModule S) :=
  ⟨omega ell sToBase ellAbsoluteDifferentialBasis,
    ⟨differentialLineDuality adjunction⟩,
    ⟨omegaIsoStructureSheaf ell sToBase ellAbsoluteDifferentialBasis⟩⟩

theorem canonicalSheaf_curveNumericallyTrivial (adjunction : ClassicalAdjunction)
    (K : S.Modules) (DK : TopDuality ell sToBase 2 K) :
    IsCurveNumericallyTrivial ell sToBase K :=
  isCurveNumericallyTrivial_of_trivial ell sToBase
    (canonicalSheafIsoStructureSheaf adjunction K DK)

end
end Eff.Canonical

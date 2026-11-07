import Eff.Canonical
import Eff.YOrder

/-! # The canonical sheaf of the second quotient has exact order five

`omega_tensorPower_trivial_iff` is unconditional, for the differential definition of `omega`.
For a genuine canonical sheaf, characterized by top-degree duality, the same conclusion follows
from the explicit general classical parameter `ClassicalAdjunction`.
-/

namespace Eff

open Red61 Red61.Fields Red61.Contraction SurfaceLib.Canonical SurfaceLib.LineBundle
  AlgebraicGeometry CategoryTheory
noncomputable section

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : Algebra.EssFiniteType F₅ ell := Canonical.ell_essFiniteType

/-- The normalized differential line of `Y`, on the actual structure morphism. -/
abbrev yOmega : Y.Modules := omega ell yToBase ellAbsoluteDifferentialBasis

/-- Exact order five of the differential line of the second quotient. -/
theorem omega_tensorPower_trivial_iff (n : ℕ) :
    Nonempty (tensorPower yOmega n ≅ structureSheafModule Y) ↔ 5 ∣ n :=
  tensorPower_trivial_iff (omegaEvaluationIso ell yToBase ellAbsoluteDifferentialBasis) n

/-- The only use of the external classical input for `Y`: normalized duality for its line. -/
def yDifferentialLineDuality (adjunction : ClassicalAdjunction) :
    TopDuality ell yToBase 2 yOmega :=
  Classical.choice (adjunction.normalizedDuality ell yToBase ellAbsoluteDifferentialBasis
    y_dimension y_stalk_regular yAbsoluteDifferentials_isLocallyFreeOfRank)

/-- Exact order five of the canonical sheaf of the second quotient. -/
theorem canonicalSheaf_tensorPower_trivial_iff (adjunction : ClassicalAdjunction)
    (K : Y.Modules) (DK : TopDuality ell yToBase 2 K) (n : ℕ) :
    Nonempty (tensorPower K n ≅ structureSheafModule Y) ↔ 5 ∣ n :=
  tensorPower_trivial_iff
    (comparisonIso DK (yDifferentialLineDuality adjunction) ≪≫
      omegaEvaluationIso ell yToBase ellAbsoluteDifferentialBasis) n

/-- In particular, the canonical class has exact order five. -/
theorem canonicalSheaf_order_five (adjunction : ClassicalAdjunction) (K : Y.Modules)
    (DK : TopDuality ell yToBase 2 K) :
    Nonempty (tensorPower K 5 ≅ structureSheafModule Y) ∧
      ∀ n, 0 < n → n < 5 → IsEmpty (tensorPower K n ≅ structureSheafModule Y) := by
  refine ⟨(canonicalSheaf_tensorPower_trivial_iff adjunction K DK 5).mpr dvd_rfl, fun n hn hn5 ↦ ?_⟩
  refine ⟨fun e ↦ ?_⟩
  have := (canonicalSheaf_tensorPower_trivial_iff adjunction K DK n).mp ⟨e⟩
  exact Nat.not_dvd_of_pos_of_lt hn hn5 this

end
end Eff

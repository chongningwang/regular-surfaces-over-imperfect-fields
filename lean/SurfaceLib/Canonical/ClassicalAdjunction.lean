import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RegularLocalRing.Defs
import Red61.Omega
import SurfaceLib.Canonical.TopDuality

/-! # Explicit classical input for the canonical comparison

`ClassicalAdjunction` is a proposition supplied as a theorem parameter. There is no global
instance or proof of it. Its field is a general classical corollary of lci adjunction and
Serre duality, for regular proper surfaces over essentially finitely generated fields of
characteristic five. It asserts duality for the normalized determinant, not its triviality.

The missing infrastructure includes presentation-independent adjunction, its gluing and
the comparison with normalized relative duality. This input includes those classical
ingredients; this file does not claim to have formalized their proofs or their equivariant
base-change enhancements. See `SurfaceLib/Canonical/README.md` for references and scope.
-/

namespace SurfaceLib.Canonical

open Red61 AlgebraicGeometry CategoryTheory

/-- Classical normalized adjunction and top-degree Serre duality, in the ranks required here.
This is a general theorem interface, not a hypothesis about the particular surface `S`.
The canonical-sheaf predicate is independently specified by `TopDuality`. -/
structure ClassicalAdjunction : Prop where
  normalizedDuality : ∀ (F : Type) [Field F] [CharP F 5] [Algebra ℤ F]
    [Algebra (ZMod 5) F] [Algebra.EssFiniteType (ZMod 5) F]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F))
    [IsProper f] [IsIntegral X] [IsNoetherian X]
    (bF : Module.Basis (Fin 2) F (KaehlerDifferential ℤ F)),
    topologicalKrullDim X = 2 →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
    IsLocallyFreeOfRank 4 (nativeAbsoluteDifferentialModule X) →
    Nonempty (TopDuality F f 2 (omega F f bF))

end SurfaceLib.Canonical

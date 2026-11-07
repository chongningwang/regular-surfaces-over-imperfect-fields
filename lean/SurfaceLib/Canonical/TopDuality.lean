import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.LinearAlgebra.Dual.Defs
import Red61.CurveNumericalTriviality

/-! # A normalized canonical sheaf via top-degree Serre duality

On a proper Cohen--Macaulay scheme of pure dimension `n`, the canonical sheaf is the
coherent sheaf representing the dual of degree-`n` coherent cohomology. This file gives
that characterization mathematical content using actual sheaf morphisms and Ext
cohomology. It proves uniqueness, including compatibility with the trace, without any
additional geometric inputs. Existence or adjunction is not assumed in this file.
-/

namespace SurfaceLib.Canonical

open Red61 AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
noncomputable section

variable {X : Scheme} (F : Type) [Field F] (f : X ⟶ Spec (CommRingCat.of F))

private local instance : HasExt.{0} X.Modules := hasExt_of_enoughInjectives X.Modules
/-- Topological module-sheaf cohomology, tagged by the specified base morphism.
The tag ensures that its field action always uses this morphism. -/
def Cohomology (F : Type) [Field F] {X : Scheme}
    (_f : X ⟶ Spec (CommRingCat.of F)) (M : X.Modules) (n : ℕ) : Type :=
  ModuleCohomology X M n

instance cohomologyAddCommGroup (M : X.Modules) (n : ℕ) :
    AddCommGroup (Cohomology F f M n) :=
  inferInstanceAs (AddCommGroup (ModuleCohomology X M n))

instance cohomologyModule (M : X.Modules) (n : ℕ) : Module F (Cohomology F f M n) := by
  letI := schemeModulesBaseLinear F f
  exact inferInstanceAs (Module F (ModuleCohomology X M n))

/-- The actual field-linear map on Ext cohomology induced by a sheaf morphism. -/
def cohomologyMap {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    Cohomology F f M n →ₗ[F] Cohomology F f N n := by
  letI := schemeModulesBaseLinear F f
  exact { cohomologyPostcompose φ n with
    map_smul' := fun a x ↦ Ext.smul_comp x (Ext.mk₀ φ) (add_zero n) a }

theorem cohomologyMap_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    cohomologyMap F f (φ ≫ ψ) n = (cohomologyMap F f ψ n).comp
      (cohomologyMap F f φ n) := by
  apply LinearMap.toAddMonoidHom_injective
  exact cohomologyPostcompose_comp φ ψ n

@[simp] theorem cohomologyMap_id (M : X.Modules) (n : ℕ) :
    cohomologyMap F f (𝟙 M) n = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  exact cohomologyPostcompose_id X M n

/-- The Serre pairing sends a sheaf map to the trace of its induced cohomology map. -/
def tracePairing {K : X.Modules} (n : ℕ)
    (trace : Cohomology F f K n →ₗ[F] F) (M : X.Modules) (φ : M ⟶ K) :
    Module.Dual F (Cohomology F f M n) :=
  trace.comp (cohomologyMap F f φ n)

theorem tracePairing_comp {K M N : X.Modules} (n : ℕ)
    (trace : Cohomology F f K n →ₗ[F] F) (u : M ⟶ N) (v : N ⟶ K) :
    tracePairing F f n trace M (u ≫ v) =
      (tracePairing F f n trace N v).comp (cohomologyMap F f u n) := by
  unfold tracePairing
  rw [cohomologyMap_comp, LinearMap.comp_assoc]

/-- Normalized top-degree duality on coherent sheaves. On a Noetherian scheme,
the finite-presentation condition here is the usual coherence condition. -/
structure TopDuality (n : ℕ) (K : X.Modules) where
  finitePresentation : K.IsFinitePresentation
  trace : Cohomology F f K n →ₗ[F] F
  perfect : ∀ (M : X.Modules), M.IsFinitePresentation →
    Function.Bijective (tracePairing F f n trace M)

variable {F f} {n : ℕ} {K L : X.Modules}

/-- The unique morphism between two top-duality sheaves preserving their traces. -/
def comparisonHom (DK : TopDuality F f n K) (DL : TopDuality F f n L) : K ⟶ L :=
  Classical.choose ((DL.perfect K DK.finitePresentation).surjective DK.trace)

theorem comparisonHom_trace (DK : TopDuality F f n K) (DL : TopDuality F f n L) :
    tracePairing F f n DL.trace K (comparisonHom DK DL) = DK.trace :=
  Classical.choose_spec ((DL.perfect K DK.finitePresentation).surjective DK.trace)

theorem comparisonHom_unique (DK : TopDuality F f n K) (DL : TopDuality F f n L)
    (u : K ⟶ L) (hu : tracePairing F f n DL.trace K u = DK.trace) :
    u = comparisonHom DK DL :=
  (DL.perfect K DK.finitePresentation).injective (hu.trans (comparisonHom_trace DK DL).symm)

theorem comparisonHom_inverse (DK : TopDuality F f n K) (DL : TopDuality F f n L) :
    comparisonHom DK DL ≫ comparisonHom DL DK = 𝟙 K := by
  apply (DK.perfect K DK.finitePresentation).injective
  rw [tracePairing_comp, comparisonHom_trace, tracePairing]
  change tracePairing F f n DL.trace K (comparisonHom DK DL) =
    DK.trace.comp (cohomologyMap F f (𝟙 K) n)
  rw [comparisonHom_trace, cohomologyMap_id, LinearMap.comp_id]

/-- Uniqueness is an isomorphism of actual sheaves, not just stalkwise existence. -/
def comparisonIso (DK : TopDuality F f n K) (DL : TopDuality F f n L) : K ≅ L where
  hom := comparisonHom DK DL
  inv := comparisonHom DL DK
  hom_inv_id := comparisonHom_inverse DK DL
  inv_hom_id := comparisonHom_inverse DL DK

/-- The comparison is functorial among normalized top-duality sheaves. -/
theorem comparisonHom_trans {P : X.Modules} (DK : TopDuality F f n K)
    (DL : TopDuality F f n L) (DP : TopDuality F f n P) :
    comparisonHom DK DL ≫ comparisonHom DL DP = comparisonHom DK DP := by
  apply comparisonHom_unique DK DP
  rw [tracePairing_comp, comparisonHom_trace]
  exact comparisonHom_trace DK DL

@[simp] theorem comparisonHom_self (DK : TopDuality F f n K) :
    comparisonHom DK DK = 𝟙 K := by
  symm
  apply comparisonHom_unique DK DK
  simp [tracePairing]

end
end SurfaceLib.Canonical

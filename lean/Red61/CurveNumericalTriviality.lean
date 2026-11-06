import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Red61.AlgebraicGeometry.Modules

/-! Field-linear cohomology and the curve Euler-degree criterion.
The degree formula is chi(M) - chi(O), with chi on a curve computed from
H0 and H1. It uses genuine Ext cohomology and the specified field scalars.
For coherent line modules on proper curves this is the usual degree formula
(Stacks Project, Definition 33.44.1, tag 0AYR). Pullbacks of trivial modules
have degree zero on every proper integral curve. -/

namespace Red61
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
private local instance (Y : Scheme.{u}) : HasExt.{u} Y.Modules :=
  hasExt_of_enoughInjectives Y.Modules

variable {Y : Scheme} (F : Type) [Field F] (f : Y ⟶ Spec (CommRingCat.of F))

def cohomologyPostcomposeBaseEquiv {M N : Y.Modules} (e : M ≅ N) (n : ℕ) :
    letI := schemeModulesBaseLinear F f
    ModuleCohomology Y M n ≃ₗ[F] ModuleCohomology Y N n := by
  letI := schemeModulesBaseLinear F f
  exact
    { cohomologyPostcomposeEquiv e n with
      map_smul' := fun a x ↦ Ext.smul_comp x (Ext.mk₀ e.hom) (add_zero n) a }

def curveEulerCharacteristic (M : Y.Modules) : ℤ :=
  letI := schemeModulesBaseLinear F f
  (Module.finrank F (ModuleCohomology Y M 0) : ℤ) -
    (Module.finrank F (ModuleCohomology Y M 1) : ℤ)

def curveEulerDegree (M : Y.Modules) : ℤ :=
  curveEulerCharacteristic F f M - curveEulerCharacteristic F f (structureSheafModule Y)

theorem curveEulerCharacteristic_iso {M N : Y.Modules} (e : M ≅ N) :
    curveEulerCharacteristic F f M = curveEulerCharacteristic F f N := by
  let := schemeModulesBaseLinear F f
  have h0 := (cohomologyPostcomposeBaseEquiv F f e 0).finrank_eq
  have h1 := (cohomologyPostcomposeBaseEquiv F f e 1).finrank_eq
  exact congrArg₂ (fun a b : ℕ ↦ (a : ℤ) - (b : ℤ)) h0 h1

theorem curveEulerDegree_trivial {M : Y.Modules} (e : M ≅ structureSheafModule Y) :
    curveEulerDegree F f M = 0 := by
  unfold curveEulerDegree
  rw [curveEulerCharacteristic_iso F f e, sub_self]

def pullbackStructureSheafIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).obj (structureSheafModule Y) ≅ structureSheafModule X :=
by
  letI : (TopologicalSpace.Opens.map g.base).Final := inferInstance
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

theorem curveEulerDegree_pullback_trivial {X : Scheme} (g : X ⟶ Y)
    {M : Y.Modules} (e : M ≅ structureSheafModule Y) :
    curveEulerDegree F (g ≫ f) ((Scheme.Modules.pullback g).obj M) = 0 :=
  curveEulerDegree_trivial F (g ≫ f)
    ((Scheme.Modules.pullback g).mapIso e ≪≫ pullbackStructureSheafIso g)

/-- The degree-zero test on every proper integral curve mapping to the scheme.
For coherent line modules this is the usual Euler-characteristic definition
of numerical triviality. -/
def IsCurveNumericallyTrivial (M : Y.Modules) : Prop :=
  ∀ (C : Scheme) (g : C ⟶ Y), IsIntegral C → IsProper (g ≫ f) →
    topologicalKrullDim C = 1 →
      curveEulerDegree F (g ≫ f) ((Scheme.Modules.pullback g).obj M) = 0

theorem isCurveNumericallyTrivial_of_trivial {M : Y.Modules}
    (e : M ≅ structureSheafModule Y) : IsCurveNumericallyTrivial F f M := by
  intro C g _ _ _
  exact curveEulerDegree_pullback_trivial F f g e

end
end Red61

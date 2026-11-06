import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Sheafify
import Red61.AlgebraicGeometry.Differentials.Basic

/-! # Sheaves of modules: scalars, stalks, cohomology, local freeness and framed Hom

Formerly the modules `FiniteFreeSections`, `GlobalSections`, `LocallyFreeOfRank`, `ModuleSheafStalks`, `ModuleSheafTransport`, `NativeFramedLineHom`, `PresheafDerivationStalkMap`, `ModulePresheafStalkLinearMap`, `ModuleSheafStalkCriterion`, `ModuleStalkSpecializes`, `NativeModuleSheafificationStalk`, `ModuleSheafificationRestriction`, `OpenImmersionStalkLinear`, `OpenImmersionStalkFrame`, `SheafModuleScalars`, `SchemeBaseLinear`, `SchemeModuleCohomology`, `SchemeModuleStalks`.
-/

/-! The sections of a native finite free module sheaf have their
canonical finite basis on every open. Evaluation preserves the finite
coproduct; the resulting coordinate isomorphism preserves each free
generator section, and the section bases commute with restrictions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) (I : Type) [Fintype I] (U : Y.Opens)

def finiteFreeSectionsFinsuppIso :
    ModuleCat.of Γ(Y, U) Γ((SheafOfModules.free (R := Y.ringCatSheaf) I : Y.Modules), U) ≅
      ModuleCat.of Γ(Y, U) (I →₀ Γ(Y, U)) := by
  let F := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : F.Additive := by
    change (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)).Additive
    infer_instance
  let H : IsColimit (F.mapCocone (SheafOfModules.freeCofan (R := Y.ringCatSheaf) I)) :=
    isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan (R := Y.ringCatSheaf) I)
  let e : (Discrete.functor (fun _ : I ↦ SheafOfModules.unit Y.ringCatSheaf)) ⋙ F ≅
      Discrete.functor (fun _ : I ↦ ModuleCat.of Γ(Y, U) Γ(Y, U)) :=
    Discrete.natIso (fun _ ↦ Iso.refl _)
  exact IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv e.symm _).symm H)
      (ModuleCat.finsuppCoconeIsColimit Γ(Y, U) Γ(Y, U) I)

theorem finiteFreeSectionsFinsuppIso_ι (i : I) :
    (SheafOfModules.evaluation Y.ringCatSheaf (op U)).map
        (SheafOfModules.ιFree (R := Y.ringCatSheaf) i) ≫
          (finiteFreeSectionsFinsuppIso Y I U).hom =
      ModuleCat.ofHom (Finsupp.lsingle i (R := Γ(Y, U)) (M := Γ(Y, U))) := by
  dsimp [finiteFreeSectionsFinsuppIso]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (C := ModuleCat Γ(Y, U))
    _ _ (Discrete.mk i)

def finiteFreeSectionBasis :
    Basis I Γ(Y, U) Γ((SheafOfModules.free (R := Y.ringCatSheaf) I : Y.Modules), U) :=
  Finsupp.basisSingleOne.map (finiteFreeSectionsFinsuppIso Y I U).symm.toLinearEquiv

theorem finiteFreeSectionBasis_apply (i : I) :
    finiteFreeSectionBasis Y I U i =
      (SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op U) := by
  apply (finiteFreeSectionsFinsuppIso Y I U).toLinearEquiv.injective
  have hi := ConcreteCategory.congr_hom (finiteFreeSectionsFinsuppIso_ι Y I U i) (1 : Γ(Y, U))
  change (finiteFreeSectionsFinsuppIso Y I U).toLinearEquiv
    ((finiteFreeSectionsFinsuppIso Y I U).toLinearEquiv.symm (Finsupp.single i 1)) = _
  exact ((finiteFreeSectionsFinsuppIso Y I U).toLinearEquiv.apply_symm_apply _).trans hi.symm

theorem finiteFreeSectionBasis_natural {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (j : I) :
    (SheafOfModules.free (R := Y.ringCatSheaf) I).val.map i
        (finiteFreeSectionBasis Y I U.unop j) = finiteFreeSectionBasis Y I V.unop j := by
  exact (congrArg ((SheafOfModules.free (R := Y.ringCatSheaf) I).val.map i)
    (finiteFreeSectionBasis_apply Y I U.unop j)).trans
      (((SheafOfModules.freeSection (R := Y.ringCatSheaf) j).property i).trans
        (finiteFreeSectionBasis_apply Y I V.unop j).symm)
end
end Red61

/-! Global sections and constants, with scalar maps determined by the structure morphism. -/

namespace Red61

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u

/-- The map from the base field to global sections induced by the structure morphism. -/
def globalScalarMap (F : Type u) [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) : F →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appTop).hom

theorem globalScalarMap_integral (F : Type u) [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) [UniversallyClosed f] :
    (globalScalarMap F f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

theorem globalSections_algebraic (F : Type u) [Field F] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of F)) [UniversallyClosed f] :
    letI := (globalScalarMap F f).toAlgebra
    Algebra.IsAlgebraic F Γ(X, ⊤) := by
  let := (globalScalarMap F f).toAlgebra
  have : Algebra.IsIntegral F Γ(X, ⊤) := ⟨globalScalarMap_integral F f⟩
  infer_instance

/-- Restriction of global sections to the generic point. -/
def globalGerm (X : Scheme.{u}) [IrreducibleSpace X] : Γ(X, ⊤) →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) (by trivial)).hom

theorem globalGerm_injective (X : Scheme.{u}) [IsIntegral X] :
    Function.Injective (globalGerm X) :=
  germ_injective_of_isIntegral X (genericPoint X) (by trivial)

def functionFieldScalarMap (F : Type u) [Field F] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of F)) : F →+* X.functionField :=
  (globalGerm X).comp (globalScalarMap F f)

/-- The function field's algebra structure is fixed by the given structure morphism. -/
@[instance_reducible] def functionFieldAlgebra (F : Type u) [Field F]
    {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of F)) : Algebra F X.functionField :=
  (functionFieldScalarMap F f).toAlgebra

/-- If algebraic elements of the function field are constants, every global section is constant.
The equality `he` explicitly checks compatibility with the structure morphism. -/
theorem globalScalarMap_bijective_of_constants
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    [UniversallyClosed f]
    (hconstants : ∀ x : E, IsAlgebraic F x → ∃ c : F, algebraMap F E c = x)
    (e : X.functionField ≃+* E)
    (he : e.toRingHom.comp (functionFieldScalarMap F f) = algebraMap F E) :
    Function.Bijective (globalScalarMap F f) := by
  let := (globalScalarMap F f).toAlgebra
  let q : Γ(X, ⊤) →ₐ[F] E :=
    { e.toRingHom.comp (globalGerm X) with
      commutes' := fun c ↦ RingHom.congr_fun he c }
  have hq : Function.Injective q := e.injective.comp (globalGerm_injective X)
  have : Algebra.IsAlgebraic F Γ(X, ⊤) := globalSections_algebraic F f
  constructor
  · intro a b hab
    apply (algebraMap F E).injective
    exact (q.commutes a).symm.trans ((congrArg q hab).trans (q.commutes b))
  · intro x
    obtain ⟨c, hc⟩ := hconstants (q x) ((Algebra.IsAlgebraic.isAlgebraic x).algHom q)
    exact ⟨c, hq ((q.commutes c).trans hc)⟩

/-- The isomorphism is the original scalar map, rather than an unspecified field isomorphism. -/
def globalSectionsEquivOfConstants
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    [UniversallyClosed f]
    (hconstants : ∀ x : E, IsAlgebraic F x → ∃ c : F, algebraMap F E c = x)
    (e : X.functionField ≃+* E)
    (he : e.toRingHom.comp (functionFieldScalarMap F f) = algebraMap F E) :
    letI := (globalScalarMap F f).toAlgebra
    F ≃ₐ[F] Γ(X, ⊤) :=
  letI := (globalScalarMap F f).toAlgebra
  AlgEquiv.ofBijective (Algebra.ofId F Γ(X, ⊤))
    (globalScalarMap_bijective_of_constants F E f hconstants e he)

/-- A version whose function-field input is already an isomorphism over the base field. -/
def globalSectionsEquivOfFunctionField
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    [UniversallyClosed f]
    (hconstants : ∀ x : E, IsAlgebraic F x → ∃ c : F, algebraMap F E c = x)
    (e : letI := functionFieldAlgebra F f
      X.functionField ≃ₐ[F] E) :
    letI := (globalScalarMap F f).toAlgebra
    F ≃ₐ[F] Γ(X, ⊤) := by
  letI := functionFieldAlgebra F f
  exact globalSectionsEquivOfConstants F E f hconstants e.toRingEquiv
    (RingHom.ext fun c ↦ e.commutes c)

end
end Red61

/-! Local freeness of a given rank for sheaves of modules on a scheme: every point lies in
the image of an open immersion over which the sheaf is isomorphic to the free sheaf on
`n` generators. -/

namespace Red61
open AlgebraicGeometry CategoryTheory

/-- A chart on which `M` is free of rank `n` near `y`: an open immersion `j : U ⟶ Y` whose
image contains `y`, and an isomorphism from the free sheaf on `n` generators to the
restriction of `M` along `j`. -/
structure LocallyFreeChart {Y : Scheme.{0}} (n : ℕ) (M : Y.Modules) (y : Y) where
  U : Scheme.{0}
  j : U ⟶ Y
  [isOpenImmersion : IsOpenImmersion j]
  mem : y ∈ Set.range j
  frame : SheafOfModules.free (R := U.ringCatSheaf) (Fin n) ≅ M.restrict j

/-- `M` is locally free of rank `n`: every point has a chart on which `M` is free of
rank `n`. -/
def IsLocallyFreeOfRank {Y : Scheme.{0}} (n : ℕ) (M : Y.Modules) : Prop :=
  ∀ y : Y, Nonempty (LocallyFreeChart n M y)

end Red61

/-! Genuine linear maps on stalks of presheaves of modules. Scalar
linearity follows from common germ representatives. The unit-module stalk
is identified with the actual ring stalk using preservation of filtered
colimits, with the expected formula on germs. -/

namespace Red61
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})
  {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  (f : M ⟶ N) (x : X)

def presheafModuleStalkMap : ↑(Presheaf.stalk (C := Ab.{u}) M.presheaf x) →ₗ[R.stalk x]
    ↑(Presheaf.stalk (C := Ab.{u}) N.presheaf x) where
  toFun := (Presheaf.stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map f)
  map_add' := map_add ((Presheaf.stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf _).map f)).hom
  map_smul' r m := by
    obtain ⟨U, hU, rU, rfl⟩ := R.exists_germ_eq r
    obtain ⟨V, hVU, hV, mV, rfl⟩ := Presheaf.exists_le_germ_eq M.presheaf m hU
    change ↑(M.obj (op V)) at mV
    have hr : R.germ U x hU rU = R.germ V x hV (R.map (homOfLE hVU).op rU) :=
      (Presheaf.germ_res_apply R (homOfLE hVU) x hV rU).symm
    rw [hr, ← PresheafOfModules.germ_smul]
    simp only [RingHom.id_apply]
    let g := (PresheafOfModules.toPresheaf _).map f
    have hm := Presheaf.stalkFunctor_map_germ_apply V x hV g
      (R.map (homOfLE hVU).op rU • mV)
    have hn := Presheaf.stalkFunctor_map_germ_apply V x hV g mV
    exact hm.trans
      ((congrArg (Presheaf.germ N.presheaf V x hV)
        (map_smul (f.app (op V)).hom (R.map (homOfLE hVU).op rU) mV)).trans
          ((PresheafOfModules.germ_smul N x V hV
            (R.map (homOfLE hVU).op rU) (f.app (op V) mV)).trans
              (congrArg (fun v : ↑(Presheaf.stalk (C := Ab.{u}) N.presheaf x) ↦
                R.germ V x hV (R.map (homOfLE hVU).op rU) • v) hn).symm))

theorem presheafModuleStalkMap_germ (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    presheafModuleStalkMap R f x (Presheaf.germ M.presheaf U x hx m) =
      Presheaf.germ N.presheaf U x hx (f.app (op U) m) :=
  show ((Presheaf.stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf _).map f)) (Presheaf.germ M.presheaf U x hx m) = _ from
      Presheaf.stalkFunctor_map_germ_apply U x hx
        ((PresheafOfModules.toPresheaf _).map f) m

def presheafModuleStalkEquiv (e : M ≅ N) :
    ↑(Presheaf.stalk (C := Ab.{u}) M.presheaf x) ≃ₗ[R.stalk x]
      ↑(Presheaf.stalk (C := Ab.{u}) N.presheaf x) := by
  let g := (Presheaf.stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map e.hom)
  have : IsIso g := by dsimp [g]; infer_instance
  exact LinearEquiv.ofBijective (presheafModuleStalkMap R e.hom x)
    (ConcreteCategory.bijective_of_isIso g)

theorem presheafModuleStalk_smul_of_germ {V : Type u} [AddCommGroup V] [Module (R.stalk x) V]
    (g : (↑(Presheaf.stalk (C := Ab.{u}) M.presheaf x)) →+ V)
    (hg : ∀ (U : Opens X) (hU : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)),
      g (Presheaf.germ M.presheaf U x hU (r • m)) =
        R.germ U x hU r • g (Presheaf.germ M.presheaf U x hU m))
    (r : R.stalk x) (m : ↑(Presheaf.stalk (C := Ab.{u}) M.presheaf x)) :
    g (r • m) = r • g m := by
  obtain ⟨U, hU, rU, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hVU, hV, mV, rfl⟩ := Presheaf.exists_le_germ_eq M.presheaf m hU
  change ↑(M.obj (op V)) at mV
  have hr : R.germ U x hU rU = R.germ V x hV (R.map (homOfLE hVU).op rU) :=
    (Presheaf.germ_res_apply R (homOfLE hVU) x hV rU).symm
  rw [hr, ← PresheafOfModules.germ_smul]
  exact hg V hV (R.map (homOfLE hVU).op rU) mV

def unitModuleStalkAddEquiv :
    ↑(Presheaf.stalk (C := Ab.{u})
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf x) ≃+ R.stalk x := by
  let e := preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u})
    ((OpenNhds.inclusion x).op ⋙ R)
  exact e.symm.addCommGroupIsoToAddEquiv

theorem unitModuleStalkAddEquiv_germ (U : Opens X) (hU : x ∈ U) (a : R.obj (op U)) :
    unitModuleStalkAddEquiv R x
        (Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf
          U x hU a) = R.germ U x hU a := by
  exact ConcreteCategory.congr_hom (ι_preservesColimitIso_inv
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hU⟩)) a

def unitModuleStalkEquiv :
    ↑(Presheaf.stalk (C := Ab.{u})
      (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf x) ≃ₗ[R.stalk x]
        R.stalk x where
  __ := unitModuleStalkAddEquiv R x
  map_smul' := presheafModuleStalk_smul_of_germ R x
    (unitModuleStalkAddEquiv R x).toAddMonoidHom (fun U hU r a ↦ by
      change ↑(R.obj (op U)) at a
      change unitModuleStalkAddEquiv R x
          (Presheaf.germ (PresheafOfModules.unit
            (R ⋙ forget₂ CommRingCat RingCat)).presheaf U x hU (r * a)) =
        R.germ U x hU r * unitModuleStalkAddEquiv R x
          (Presheaf.germ (PresheafOfModules.unit
            (R ⋙ forget₂ CommRingCat RingCat)).presheaf U x hU a)
      rw [unitModuleStalkAddEquiv_germ, unitModuleStalkAddEquiv_germ]
      exact map_mul (R.germ U x hU).hom r a)

end
end Red61

section
/-! Transport genuine module sheaves along equivalences of their section
sets. The restriction maps are conjugated explicitly, and the resulting
sheaf is isomorphic to the original as a sheaf of modules. -/

universe u v u₁ v₁

namespace Red61

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

def moduleEquivTransport {R : Type u} [Ring R] (M : ModuleCat.{v} R)
    (A : Type v) (e : A ≃ M) : ModuleCat.{v} R := by
  letI := e.addCommGroup
  letI := e.addEquiv.module R
  exact ModuleCat.of R A

def moduleEquivTransportIso {R : Type u} [Ring R] (M : ModuleCat.{v} R)
    (A : Type v) (e : A ≃ M) : moduleEquivTransport M A e ≅ M := by
  letI := e.addCommGroup
  letI := e.addEquiv.module R
  exact (e.addEquiv.linearEquiv R).toModuleIso

@[simp] theorem moduleEquivTransportIso_hom_apply {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) (A : Type v) (e : A ≃ M) (a : A) :
    (moduleEquivTransportIso M A e).hom a = e a := rfl

@[simp] theorem moduleEquivTransportIso_inv_apply {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) (A : Type v) (e : A ≃ M) (m : M) :
    (moduleEquivTransportIso M A e).inv m = e.symm m := rfl

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  (M : PresheafOfModules.{v} R) (A : Cᵒᵖ → Type v) (e : ∀ U, A U ≃ M.obj U)

def transportedModulePresheaf : PresheafOfModules.{v} R where
  obj U := moduleEquivTransport (M.obj U) (A U) (e U)
  map {U W} i := (moduleEquivTransportIso (M.obj U) (A U) (e U)).hom ≫ M.map i ≫
    (ModuleCat.restrictScalars (R.map i).hom).map
      (moduleEquivTransportIso (M.obj W) (A W) (e W)).inv
  map_id U := by
    ext a
    change (e U).symm (M.map (𝟙 U) (e U a)) = a
    rw [M.map_id]
    exact (e U).symm_apply_apply a
  map_comp {U W Z} i j := by
    ext a
    change (e Z).symm (M.map (i ≫ j) (e U a)) =
      (e Z).symm (M.map j (e W ((e W).symm (M.map i (e U a)))))
    rw [M.map_comp_apply, (e W).apply_symm_apply]

def transportedModulePresheafIso : transportedModulePresheaf M A e ≅ M :=
  PresheafOfModules.isoMk (fun U ↦ moduleEquivTransportIso (M.obj U) (A U) (e U)) (by
    intro U W i
    ext a
    change e W ((e W).symm (M.map i (e U a))) = M.map i (e U a)
    exact (e W).apply_symm_apply _)

section Sheaf

variable {J : GrothendieckTopology C} (S : Sheaf J RingCat.{u})
  (N : SheafOfModules.{v} S) (B : Cᵒᵖ → Type v) (f : ∀ U, B U ≃ N.val.obj U)

def transportedModuleSheaf : SheafOfModules.{v} S where
  val := transportedModulePresheaf N.val B f
  isSheaf := (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf S.obj).mapIso
      (transportedModulePresheafIso N.val B f))).mpr N.isSheaf

def transportedModuleSheafIso : transportedModuleSheaf S N B f ≅ N :=
  (SheafOfModules.fullyFaithfulForget S).preimageIso
    (transportedModulePresheafIso N.val B f)

end Sheaf

end
end Red61
end

/-! A framed invertible sheaf has a genuine native Hom sheaf into every
module sheaf. Its sections are the actual linear Hom modules with their
original module structures. Evaluation at the frame gives a sectionwise
isomorphism and proves the sheaf condition. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) {B : Y.Modules} (e : SheafOfModules.unit Y.ringCatSheaf ≅ B)
  (M : Y.Modules)
private local instance (Q : Y.Modules) (U : Y.Opensᵒᵖ) :
    Module (Y.presheaf.obj U) (Q.val.obj U) := (Q.val.obj U).isModule

/-- The actual scalar coefficient of a section in the given line frame. -/
def framedLineSectionCoefficient (U : Y.Opensᵒᵖ) :
    B.val.obj U ≃ₗ[Y.presheaf.obj U] Y.presheaf.obj U :=
  ((SheafOfModules.evaluation Y.ringCatSheaf U).mapIso e.symm).toLinearEquiv

/-- Evaluation at the given line frame on actual linear Hom modules. -/
def framedLineHomSectionEvaluation (U : Y.Opensᵒᵖ) :
    (B.val.obj U →ₗ[Y.presheaf.obj U] M.val.obj U) ≃ₗ[Y.presheaf.obj U] M.val.obj U :=
  determinantLineEvaluation (K := Y.presheaf.obj U) (framedLineSectionCoefficient Y e U)

/-- The additive presheaf of actual section Hom modules. -/
def framedLineHomAbPresheaf : Y.Opensᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (B.val.obj U →ₗ[Y.presheaf.obj U] M.val.obj U)
  map {U V} i := AddCommGrpCat.ofHom
    ((framedLineHomSectionEvaluation Y e M V).symm.toAddMonoidHom.comp
      (((M.val.map i).hom.toAddMonoidHom).comp
        (framedLineHomSectionEvaluation Y e M U).toAddMonoidHom))
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    change (framedLineHomSectionEvaluation Y e M U).symm
      (M.val.map (𝟙 U) (framedLineHomSectionEvaluation Y e M U f)) = f
    rw [M.val.map_id]
    exact (framedLineHomSectionEvaluation Y e M U).symm_apply_apply f
  map_comp {U V W} i j := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    change (framedLineHomSectionEvaluation Y e M W).symm
      (M.val.map (i ≫ j) (framedLineHomSectionEvaluation Y e M U f)) =
        (framedLineHomSectionEvaluation Y e M W).symm
          (M.val.map j (framedLineHomSectionEvaluation Y e M V
            ((framedLineHomSectionEvaluation Y e M V).symm
              (M.val.map i (framedLineHomSectionEvaluation Y e M U f)))))
    rw [LinearEquiv.apply_symm_apply, M.val.map_comp_apply]

/-- The section Hom presheaf with the original linear Hom module structures. -/
def framedLineHomPresheaf : PresheafOfModulesOfCommRing.{0} Y.presheaf := by
  letI (U : Y.Opensᵒᵖ) : Module ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
      ((framedLineHomAbPresheaf Y e M).obj U) :=
    inferInstanceAs (Module (Y.presheaf.obj U)
      (B.val.obj U →ₗ[Y.presheaf.obj U] M.val.obj U))
  refine PresheafOfModules.ofPresheaf (R := Y.presheaf ⋙ forget₂ CommRingCat RingCat)
    (framedLineHomAbPresheaf Y e M) (fun {U V} i r f ↦ ?_)
  exact (congrArg (framedLineHomSectionEvaluation Y e M V).symm
    ((congrArg (M.val.map i) ((framedLineHomSectionEvaluation Y e M U).map_smul r f)).trans
      (M.val.map_smul i r (framedLineHomSectionEvaluation Y e M U f)))).trans
        ((framedLineHomSectionEvaluation Y e M V).symm.map_smul _ _)

/-- Evaluation at the frame is a native module-presheaf isomorphism. -/
def framedLineHomPresheafEvaluationIso : framedLineHomPresheaf Y e M ≅ M.val :=
  PresheafOfModulesOfCommRing.isoMk
    (fun U ↦ (framedLineHomSectionEvaluation Y e M U).toModuleIso)
    (fun {U V} i ↦ by
      refine ModuleCat.hom_ext
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun f ↦ ?_))
      exact (framedLineHomSectionEvaluation Y e M V).apply_symm_apply
        (M.val.map i (framedLineHomSectionEvaluation Y e M U f)))

/-- The genuine native Hom sheaf for a globally framed source line. -/
def nativeFramedLineHom : Y.Modules where
  val := framedLineHomPresheaf Y e M
  isSheaf := (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).mapIso
      (framedLineHomPresheafEvaluationIso Y e M))).mpr M.isSheaf

/-- Evaluation at the frame is an actual native module-sheaf isomorphism. -/
def nativeFramedLineHomEvaluationIso : nativeFramedLineHom Y e M ≅ M :=
  (SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).preimageIso
    (framedLineHomPresheafEvaluationIso Y e M)
end
end Red61

/-! Additive stalk maps of absolute sheaf derivations use native filtered
colimits and the additive comparison of the actual ring stalk. Germ formulas
and the native stalk module structure are retained explicitly. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
variable (Y : Scheme.{0})

def schemeRingAbPresheaf : TopCat.Presheaf Ab Y :=
  Y.presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)

def schemeRingAbStalkIso (x : Y) :
    (schemeRingAbPresheaf Y).stalk x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).obj (Y.presheaf.stalk x) :=
  Limits.colimit.isoColimitCocone
    ⟨_, Limits.isColimitOfPreserves ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab))
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ Y.presheaf))⟩

theorem schemeRingAbStalkIso_germ (x : Y) (U : Y.Opens) (hx : x ∈ U) (s : Γ(Y, U)) :
    (schemeRingAbStalkIso Y x).hom ((schemeRingAbPresheaf Y).germ U x hx s) =
      Y.presheaf.germ U x hx s := by
  have h : (schemeRingAbPresheaf Y).germ U x hx ≫ (schemeRingAbStalkIso Y x).hom =
      ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab)).map (Y.presheaf.germ U x hx) :=
    Limits.colimit.isoColimitCocone_ι_hom (C := Ab) ..
  exact ConcreteCategory.congr_hom h s

theorem schemeRingAbStalkIso_inv_germ
    (x : Y) (U : Y.Opens) (hx : x ∈ U) (s : Γ(Y, U)) :
    (schemeRingAbStalkIso Y x).inv (Y.presheaf.germ U x hx s) =
      (schemeRingAbPresheaf Y).germ U x hx s := by
  calc
    _ = (schemeRingAbStalkIso Y x).inv ((schemeRingAbStalkIso Y x).hom
        ((schemeRingAbPresheaf Y).germ U x hx s)) :=
      congrArg (schemeRingAbStalkIso Y x).inv (schemeRingAbStalkIso_germ Y x U hx s).symm
    _ = _ := (schemeRingAbStalkIso Y x).addCommGroupIsoToAddEquiv.symm_apply_apply _

variable (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)
  (d : PresheafOfModulesOfCommRing.Derivation' M (schemeIntegerScalars Y))

abbrev modulePresheafAbPresheaf : TopCat.Presheaf Ab Y := M.presheaf

def derivationAdditivePresheafMap : schemeRingAbPresheaf Y ⟶ (modulePresheafAbPresheaf Y M) where
  app U := AddCommGrpCat.ofHom (d.d (X := U))
  naturality := by
    intro U V i
    ext a
    exact d.d_map i a

def presheafDerivationStalkAddHom (x : Y) :
    Y.presheaf.stalk x →+ (modulePresheafAbPresheaf Y M).stalk x :=
  ((TopCat.Presheaf.stalkFunctor Ab x).map (derivationAdditivePresheafMap Y M d)).hom.comp
    (schemeRingAbStalkIso Y x).inv.hom

theorem presheafDerivationStalkAddHom_germ
    (x : Y) (U : Y.Opens) (hx : x ∈ U) (s : Γ(Y, U)) :
    presheafDerivationStalkAddHom Y M d x (Y.presheaf.germ U x hx s) =
      (modulePresheafAbPresheaf Y M).germ U x hx (d.d s) := by
  change ((TopCat.Presheaf.stalkFunctor Ab x).map (derivationAdditivePresheafMap Y M d))
    ((schemeRingAbStalkIso Y x).inv (Y.presheaf.germ U x hx s)) = _
  exact (congrArg ((TopCat.Presheaf.stalkFunctor Ab x).map
    (derivationAdditivePresheafMap Y M d)) (schemeRingAbStalkIso_inv_germ Y x U hx s)).trans
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        (derivationAdditivePresheafMap Y M d) s)

@[instance_reducible] def schemeModuleStalkModule (x : Y) :
    Module (Y.presheaf.stalk x) ((modulePresheafAbPresheaf Y M).stalk x) :=
  inferInstanceAs (Module (Y.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (modulePresheafAbPresheaf Y M) x))
end
end Red61

/-! Actual module-presheaf morphisms induce linear maps of native stalks
over the native ring stalk. Linearity and the germ formula retain both
source and target stalk scalar actions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
@[instance_reducible] def schemeModuleNativeStalkModule
    (Y : Scheme.{0}) (M : Y.Modules) (x : Y) :
    Module (Y.presheaf.stalk x) (M.presheaf.stalk x) :=
  schemeModuleStalkModule Y M.val x

variable (Y : Scheme.{0}) (M N : PresheafOfModulesOfCommRing.{0} Y.presheaf) (f : M ⟶ N)
  (x : Y)

def modulePresheafStalkMapAddHom :
    (modulePresheafAbPresheaf Y M).stalk x →+ (modulePresheafAbPresheaf Y N).stalk x :=
  ((TopCat.Presheaf.stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map f)).hom

theorem modulePresheafStalkMapAddHom_germ
    (U : Y.Opens) (hx : x ∈ U) (η : M.obj (op U)) :
    modulePresheafStalkMapAddHom Y M N f x
        ((modulePresheafAbPresheaf Y M).germ U x hx η) =
      (modulePresheafAbPresheaf Y N).germ U x hx (f.app (op U) η) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map f) η

theorem modulePresheafStalkMapAddHom_smul
    (a : Y.presheaf.stalk x) (ω : (modulePresheafAbPresheaf Y M).stalk x) :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y N x
    modulePresheafStalkMapAddHom Y M N f x (a • ω) =
      a • modulePresheafStalkMapAddHom Y M N f x ω := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y N x
  obtain ⟨U, hxU, r, hr⟩ := Y.presheaf.exists_germ_eq a
  obtain ⟨W, hWU, hxW, η, hη⟩ := (modulePresheafAbPresheaf Y M).exists_le_germ_eq ω hxU
  let η₀ : M.obj (op W) := η
  have hη₀ : (modulePresheafAbPresheaf Y M).germ W x hxW η₀ = ω := hη
  let rW := Y.presheaf.map (homOfLE hWU).op r
  have hrW : Y.presheaf.germ W x hxW rW = a :=
    (Y.presheaf.germ_res_apply (homOfLE hWU) x hxW r).trans hr
  rw [← hrW, ← hη₀]
  calc
    _ = modulePresheafStalkMapAddHom Y M N f x
        ((modulePresheafAbPresheaf Y M).germ W x hxW (rW • η₀)) :=
      congrArg (modulePresheafStalkMapAddHom Y M N f x)
        (PresheafOfModules.germ_smul M x W hxW rW η₀).symm
    _ = (modulePresheafAbPresheaf Y N).germ W x hxW (f.app (op W) (rW • η₀)) :=
      modulePresheafStalkMapAddHom_germ Y M N f x W hxW (rW • η₀)
    _ = (modulePresheafAbPresheaf Y N).germ W x hxW (rW • f.app (op W) η₀) :=
      congrArg ((modulePresheafAbPresheaf Y N).germ W x hxW)
        ((f.app (op W)).hom.map_smul rW η₀)
    _ = Y.presheaf.germ W x hxW rW •
        (modulePresheafAbPresheaf Y N).germ W x hxW (f.app (op W) η₀) :=
      PresheafOfModules.germ_smul N x W hxW rW (f.app (op W) η₀)
    _ = _ := congrArg (fun v ↦ Y.presheaf.germ W x hxW rW • v)
      (modulePresheafStalkMapAddHom_germ Y M N f x W hxW η₀).symm

def modulePresheafStalkLinearMap :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y N x
    (modulePresheafAbPresheaf Y M).stalk x →ₗ[Y.presheaf.stalk x]
      (modulePresheafAbPresheaf Y N).stalk x := by
  letI := schemeModuleStalkModule Y M x
  letI := schemeModuleStalkModule Y N x
  exact
    { toFun := modulePresheafStalkMapAddHom Y M N f x
      map_add' := map_add _
      map_smul' := modulePresheafStalkMapAddHom_smul Y M N f x }

theorem modulePresheafStalkLinearMap_germ
    (U : Y.Opens) (hx : x ∈ U) (η : M.obj (op U)) :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y N x
    modulePresheafStalkLinearMap Y M N f x
        ((modulePresheafAbPresheaf Y M).germ U x hx η) =
      (modulePresheafAbPresheaf Y N).germ U x hx (f.app (op U) η) :=
  modulePresheafStalkMapAddHom_germ Y M N f x U hx η
end
end Red61

/-! A morphism of native scheme module sheaves is an isomorphism when
its actual additive stalk maps are bijective, using the native sheaf stalk criterion. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) {M N : Y.Modules} (f : M ⟶ N)

theorem schemeModule_isIso_of_stalk_bijective
    (h : ∀ x : Y, Function.Bijective (modulePresheafStalkMapAddHom Y M.val N.val f.val x)) :
    IsIso f := by
  let g := (SheafOfModules.toSheaf Y.ringCatSheaf).map f
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective g U
    (fun x _ ↦ h x)
end
end Red61

/-! Module stalk specialization is semilinear for the actual ring stalk
specialization. Both the scalar compatibility and original germ formula
are proved using common section representatives. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat
noncomputable section
variable (Y : Scheme.{0}) (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)
  {x y : Y} (h : x ⤳ y)
private local instance (z : Y) :
    Module (Y.presheaf.stalk z) ((modulePresheafAbPresheaf Y M).stalk z) :=
  schemeModuleStalkModule Y M z

/-- The actual specialization map, with its native scalar compatibility. -/
def moduleStalkSpecializesSemilinear :
    (modulePresheafAbPresheaf Y M).stalk y →ₛₗ[(Y.presheaf.stalkSpecializes h).hom]
      (modulePresheafAbPresheaf Y M).stalk x := by
  let g := ((modulePresheafAbPresheaf Y M).stalkSpecializes h).hom
  let : Module (Y.presheaf.stalk y) ((modulePresheafAbPresheaf Y M).stalk x) :=
    Module.compHom _ (Y.presheaf.stalkSpecializes h).hom
  refine { g with map_smul' := ?_ }
  exact presheafModuleStalk_smul_of_germ Y.presheaf y g (fun U hy r m ↦ by
    have hm := ConcreteCategory.congr_hom
      ((modulePresheafAbPresheaf Y M).germ_stalkSpecializes hy h) m
    have hr := ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hy h) r
    have hs := ConcreteCategory.congr_hom
      ((modulePresheafAbPresheaf Y M).germ_stalkSpecializes hy h) (r • m)
    change g ((modulePresheafAbPresheaf Y M).germ U y hy (r • m)) =
      (Y.presheaf.stalkSpecializes h) (Y.presheaf.germ U y hy r) •
        g ((modulePresheafAbPresheaf Y M).germ U y hy m)
    exact hs.trans ((PresheafOfModules.germ_smul M x U
      (h.mem_open U.isOpen hy) r m).trans
        (congrArg₂ (fun a b ↦ a • b) hr.symm hm.symm)))

/-- Module specialization sends an original germ to the same section germ. -/
theorem moduleStalkSpecializesSemilinear_germ (U : Y.Opens) (hy : y ∈ U)
    (m : M.obj (op U)) :
    moduleStalkSpecializesSemilinear Y M h
        ((modulePresheafAbPresheaf Y M).germ U y hy m) =
      (modulePresheafAbPresheaf Y M).germ U x (h.mem_open U.isOpen hy) m :=
  ConcreteCategory.congr_hom ((modulePresheafAbPresheaf Y M).germ_stalkSpecializes hy h) m
end
end Red61

/-! Native module sheafification preserves actual stalks as modules over
the native ring stalk. The unit is the ordinary sheafification map on
additive presheaves; its linear equivalence retains the actual germ formula. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
variable (Y : Scheme.{0}) (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)

def modulePresheafSheafification : Y.Modules :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj M

def modulePresheafSheafificationUnit : M ⟶ (modulePresheafSheafification Y M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app M

theorem modulePresheafSheafificationUnit_stalk_isIso (x : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        (modulePresheafSheafificationUnit Y M))) := by
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) M.presheaf))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab M.presheaf

def modulePresheafSheafificationStalkEquiv (x : Y) :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
    (modulePresheafAbPresheaf Y M).stalk x ≃ₗ[Y.presheaf.stalk x]
      (modulePresheafAbPresheaf Y (modulePresheafSheafification Y M).val).stalk x := by
  letI := schemeModuleStalkModule Y M x
  letI := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
  have : IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        (modulePresheafSheafificationUnit Y M))) :=
    modulePresheafSheafificationUnit_stalk_isIso Y M x
  exact LinearEquiv.ofBijective (modulePresheafStalkLinearMap Y M
    (modulePresheafSheafification Y M).val (modulePresheafSheafificationUnit Y M) x)
      (asIso ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
          (modulePresheafSheafificationUnit Y M)))).addCommGroupIsoToAddEquiv.bijective

theorem modulePresheafSheafificationStalkEquiv_germ
    (x : Y) (U : Y.Opens) (hx : x ∈ U) (η : M.obj (op U)) :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
    modulePresheafSheafificationStalkEquiv Y M x
        ((modulePresheafAbPresheaf Y M).germ U x hx η) =
      (modulePresheafAbPresheaf Y (modulePresheafSheafification Y M).val).germ U x hx
        ((modulePresheafSheafificationUnit Y M).app (op U) η) :=
  modulePresheafStalkLinearMap_germ Y M (modulePresheafSheafification Y M).val
    (modulePresheafSheafificationUnit Y M) x U hx η
end
end Red61

/-! Native module sheafification commutes with open-immersion restriction.
The actual module morphism is identified with mathlib’s existing underlying
sheafification compatibility isomorphism through its unit formula. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

def openImmersionPresheafScalars : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf where
  app U := (f.appIso U.unop).inv
  naturality {_U _V} i := f.appIso_inv_naturality i

def nativeModulePresheafRestrictionFunctor :
    PresheafOfModulesOfCommRing.{0} Y.presheaf ⥤ PresheafOfModulesOfCommRing.{0} X.presheaf :=
  PresheafOfModulesOfCommRing.pushforward (openImmersionPresheafScalars f)

variable (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)

def moduleSheafificationRestrictionRawMap :
    (nativeModulePresheafRestrictionFunctor f).obj M ⟶
      ((modulePresheafSheafification Y M).restrict f).val :=
  (nativeModulePresheafRestrictionFunctor f).map (modulePresheafSheafificationUnit Y M)

def moduleSheafificationRestrictionMap :
    modulePresheafSheafification X ((nativeModulePresheafRestrictionFunctor f).obj M) ⟶
      (modulePresheafSheafification Y M).restrict f :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    (moduleSheafificationRestrictionRawMap f M)

def moduleSheafificationRestrictionAbIso :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
        (modulePresheafSheafification X ((nativeModulePresheafRestrictionFunctor f).obj M)) ≅
      (SheafOfModules.toSheaf X.ringCatSheaf).obj
        ((modulePresheafSheafification Y M).restrict f) :=
  (f.opensFunctor.pushforwardContinuousSheafificationCompatibility Ab
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).app M.presheaf

theorem moduleSheafificationRestrictionMap_unit :
    modulePresheafSheafificationUnit X ((nativeModulePresheafRestrictionFunctor f).obj M) ≫
        (moduleSheafificationRestrictionMap f M).val =
      moduleSheafificationRestrictionRawMap f M := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let P := (nativeModulePresheafRestrictionFunctor f).obj M
  let N := (modulePresheafSheafification Y M).restrict f
  have he := (adj.homEquiv P N).apply_symm_apply (moduleSheafificationRestrictionRawMap f M)
  exact (adj.homEquiv_unit P N ((adj.homEquiv P N).symm
    (moduleSheafificationRestrictionRawMap f M))).symm.trans he

theorem moduleSheafificationRestrictionAbIso_unit :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (f.opensFunctor.op ⋙ M.presheaf) ≫
          (moduleSheafificationRestrictionAbIso f M).hom.hom =
      Functor.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) M.presheaf) :=
  f.opensFunctor.toSheafify_pullbackSheafificationCompatibility Ab
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) M.presheaf

theorem moduleSheafificationRestrictionMap_ab :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (moduleSheafificationRestrictionMap f M) =
      (moduleSheafificationRestrictionAbIso f M).hom := by
  apply (sheafToPresheaf (Opens.grothendieckTopology X) Ab).map_injective
  apply CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology X) _ _
    (SheafOfModules.isSheaf ((modulePresheafSheafification Y M).restrict f))
  have hu : CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (f.opensFunctor.op ⋙ M.presheaf) ≫
          ((SheafOfModules.toSheaf X.ringCatSheaf).map
            (moduleSheafificationRestrictionMap f M)).hom =
      Functor.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) M.presheaf) := by
    exact congrArg (PresheafOfModules.toPresheaf
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        (moduleSheafificationRestrictionMap_unit f M)
  exact hu.trans (moduleSheafificationRestrictionAbIso_unit f M).symm

theorem moduleSheafificationRestrictionMap_isIso :
    IsIso (moduleSheafificationRestrictionMap f M) := by
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (moduleSheafificationRestrictionMap f M)) := by
    rw [moduleSheafificationRestrictionMap_ab]
    infer_instance
  have : IsIso ((Scheme.Modules.toPresheaf X).map
      (moduleSheafificationRestrictionMap f M)) := by
    change IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) Ab).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (moduleSheafificationRestrictionMap f M)))
    infer_instance
  exact isIso_of_reflects_iso (moduleSheafificationRestrictionMap f M)
    (Scheme.Modules.toPresheaf X)

def moduleSheafificationRestrictionIso :
    modulePresheafSheafification X ((nativeModulePresheafRestrictionFunctor f).obj M) ≅
      (modulePresheafSheafification Y M).restrict f := by
  have := moduleSheafificationRestrictionMap_isIso f M
  exact asIso (moduleSheafificationRestrictionMap f M)
end
end Red61

/-! The native stalk isomorphism for restriction along an open immersion
is linear over the source local ring through the inverse stalk-ring map.
The inverse ring map and module equivalence have actual germ formulas. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)

theorem openImmersion_stalkMap_appIso_inv_germ
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    f.stalkMap x
        (Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((f.appIso U).inv a)) =
      X.presheaf.germ U x hx a := by
  have hg := f.germ_stalkMap_apply (f ''ᵁ U) x ⟨x, hx, rfl⟩ ((f.appIso U).inv a)
  have ha := ConcreteCategory.congr_hom
    (f.appIso_hom U) ((f.appIso U).inv a)
  have hai : X.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op
      (f.app (f ''ᵁ U) ((f.appIso U).inv a)) = a :=
    ha.symm.trans ((f.appIso U).commRingCatIsoToRingEquiv.apply_symm_apply a)
  have hr := X.presheaf.germ_res_apply
    (eqToHom (f.preimage_image_eq U).symm) x hx
      (f.app (f ''ᵁ U) ((f.appIso U).inv a))
  exact hg.trans (hr.symm.trans (congrArg (X.presheaf.germ U x hx) hai))

theorem openImmersion_inverseStalkMap_germ
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    inv (f.stalkMap x) (X.presheaf.germ U x hx a) =
      Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((f.appIso U).inv a) := by
  apply (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.injective
  change f.stalkMap x (inv (f.stalkMap x) _) = _
  exact ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.apply_symm_apply _).trans
    (openImmersion_stalkMap_appIso_inv_germ f x U hx a).symm

variable (M : Y.Modules)

@[instance_reducible] def openImmersionTargetStalkModule :
    letI := schemeModuleNativeStalkModule Y M (f x)
    Module (X.presheaf.stalk x) (M.presheaf.stalk (f x)) := by
  letI := schemeModuleNativeStalkModule Y M (f x)
  exact Module.compHom (R := Y.presheaf.stalk (f x)) _ (inv (f.stalkMap x)).hom

def restrictModuleStalkAddEquiv :
    (M.restrict f).presheaf.stalk x ≃+ M.presheaf.stalk (f x) :=
  ((Scheme.Modules.restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv

theorem restrictModuleStalkAddEquiv_germ
    (U : X.Opens) (hx : x ∈ U) (η : Γ(M.restrict f, U)) :
    restrictModuleStalkAddEquiv f x M ((M.restrict f).presheaf.germ U x hx η) =
      M.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ η :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x M hx) η

theorem restrictModuleStalkAddEquiv_smul
    (a : X.presheaf.stalk x) (ω : (M.restrict f).presheaf.stalk x) :
    letI := schemeModuleNativeStalkModule X (M.restrict f) x
    letI := schemeModuleNativeStalkModule Y M (f x)
    letI := openImmersionTargetStalkModule f x M
    restrictModuleStalkAddEquiv f x M (a • ω) = a • restrictModuleStalkAddEquiv f x M ω := by
  let := schemeModuleNativeStalkModule X (M.restrict f) x
  let := schemeModuleNativeStalkModule Y M (f x)
  let := openImmersionTargetStalkModule f x M
  obtain ⟨U, hxU, r, hr⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨W, hWU, hxW, η, hη⟩ := (M.restrict f).presheaf.exists_le_germ_eq ω hxU
  let η₀ : Γ(M.restrict f, W) := η
  have hη₀ : (M.restrict f).presheaf.germ W x hxW η₀ = ω := hη
  let rW := X.presheaf.map (homOfLE hWU).op r
  have hrW : X.presheaf.germ W x hxW rW = a :=
    (X.presheaf.germ_res_apply (homOfLE hWU) x hxW r).trans hr
  rw [← hrW, ← hη₀]
  calc
    _ = restrictModuleStalkAddEquiv f x M
        ((M.restrict f).presheaf.germ W x hxW (rW • η₀)) :=
      congrArg (restrictModuleStalkAddEquiv f x M)
        (PresheafOfModules.germ_smul (M.restrict f).val x W hxW rW η₀).symm
    _ = M.presheaf.germ (f ''ᵁ W) (f x) ⟨x, hxW, rfl⟩ (rW • η₀) :=
      restrictModuleStalkAddEquiv_germ f x M W hxW _
    _ = Y.presheaf.germ (f ''ᵁ W) (f x) ⟨x, hxW, rfl⟩ ((f.appIso W).inv rW) •
        M.presheaf.germ (f ''ᵁ W) (f x) ⟨x, hxW, rfl⟩ η₀ :=
      PresheafOfModules.germ_smul M.val (f x) (f ''ᵁ W) ⟨x, hxW, rfl⟩ _ η₀
    _ = _ := by
      change _ = inv (f.stalkMap x) (X.presheaf.germ W x hxW rW) •
        restrictModuleStalkAddEquiv f x M ((M.restrict f).presheaf.germ W x hxW η₀)
      rw [openImmersion_inverseStalkMap_germ, restrictModuleStalkAddEquiv_germ]

def restrictModuleStalkLinearEquiv :
    letI := schemeModuleNativeStalkModule X (M.restrict f) x
    letI := schemeModuleNativeStalkModule Y M (f x)
    letI := openImmersionTargetStalkModule f x M
    (M.restrict f).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] M.presheaf.stalk (f x) := by
  letI := schemeModuleNativeStalkModule X (M.restrict f) x
  letI := schemeModuleNativeStalkModule Y M (f x)
  letI := openImmersionTargetStalkModule f x M
  exact { restrictModuleStalkAddEquiv f x M with
    map_smul' := restrictModuleStalkAddEquiv_smul f x M }
end
end Red61

/-! A genuine rank-one frame on an open immersion gives a frame of each
original target stalk over its actual local ring. The construction uses
native module restriction and the inverse local-ring isomorphism. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) (M : Y.Modules)
  (e : SheafOfModules.unit X.ringCatSheaf ≅ M.restrict f)
private local instance : Module (Y.presheaf.stalk (f x)) (M.presheaf.stalk (f x)) :=
  schemeModuleNativeStalkModule Y M (f x)
private local instance : Module (X.presheaf.stalk x) ((M.restrict f).presheaf.stalk x) :=
  schemeModuleNativeStalkModule X (M.restrict f) x

/-- A local sheaf frame induces a frame of the actual target local-ring module. -/
def openImmersionStalkFrameEquiv :
    Y.presheaf.stalk (f x) ≃ₗ[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x) := by
  letI := openImmersionTargetStalkModule f x M
  let F : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] M.presheaf.stalk (f x) :=
    ((unitModuleStalkEquiv X.presheaf x).symm.trans
      (presheafModuleStalkEquiv X.presheaf x
        ((SheafOfModules.forget X.ringCatSheaf).mapIso e))).trans
          (restrictModuleStalkLinearEquiv f x M)
  let G : Y.presheaf.stalk (f x) →ₗ[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x) :=
    { toFun := fun a ↦ F (f.stalkMap x a)
      map_add' a b := (congrArg F (map_add (f.stalkMap x).hom a b)).trans (F.map_add _ _)
      map_smul' a b := by
        change F (f.stalkMap x (a * b)) = a • F (f.stalkMap x b)
        have hm := F.map_smul (f.stalkMap x a) (f.stalkMap x b)
        have hi := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm_apply_apply a
        exact (congrArg F (map_mul (f.stalkMap x).hom a b)).trans
          (hm.trans (congrArg (fun r ↦ r • F (f.stalkMap x b)) hi)) }
  exact LinearEquiv.ofBijective G
    (F.bijective.comp (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.bijective)
end
end Red61

/-! Scalar endomorphisms of genuine sheaves of modules, induced by the
specified structure morphism to a field. Naturality is proved on actual
sections, for use in base-linear cohomological duality. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Y : Scheme}

def structureSheafModule (Y : Scheme) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

def topSectionRestriction (Y : Scheme) (U : Y.Opens) (a : Γ(Y, ⊤)) : Γ(Y, U) :=
  Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a

theorem topSectionRestriction_natural (Y : Scheme) {U V : Y.Opens}
    (i : Opposite.op U ⟶ Opposite.op V) (a : Γ(Y, ⊤)) :
    Y.presheaf.map i (topSectionRestriction Y U a) = topSectionRestriction Y V a := by
  change (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ Y.presheaf.map i) a = _
  rw [← Y.presheaf.map_comp]
  rfl

def globalSectionModuleScalar (M : Y.Modules) (a : Γ(Y, ⊤)) : M ⟶ M where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul Γ(Y, U.unop) Γ(M, U.unop)
        (topSectionRestriction Y U.unop a))
      naturality := by
        intro U V i
        let : Module Γ(Y, V.unop) (M.presheaf.obj V) :=
          inferInstanceAs (Module Γ(Y, V.unop) Γ(M, V.unop))
        ext x
        exact ((M.val.map_smul i (topSectionRestriction Y U.unop a) x).trans
          (congrArg (fun r : Γ(Y, V.unop) ↦ r • (M.val.map i x : Γ(M, V.unop)))
            (topSectionRestriction_natural Y i a))).symm }

theorem globalSectionModuleScalar_natural {M N : Y.Modules} (φ : M ⟶ N)
    (a : Γ(Y, ⊤)) :
    globalSectionModuleScalar M a ≫ φ = φ ≫ globalSectionModuleScalar N a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact φ.app_smul _ _

def fieldModuleScalar (F : Type) [Field F] (f : Y ⟶ Spec (CommRingCat.of F))
    (M : Y.Modules) (a : F) : M ⟶ M :=
  globalSectionModuleScalar M (globalScalarMap F f a)

theorem fieldModuleScalar_natural (F : Type) [Field F]
    (f : Y ⟶ Spec (CommRingCat.of F)) {M N : Y.Modules} (φ : M ⟶ N) (a : F) :
    fieldModuleScalar F f M a ≫ φ = φ ≫ fieldModuleScalar F f N a :=
  globalSectionModuleScalar_natural φ _

end
end Red61

/-! The category of module sheaves is linear over a field through the
specified structure morphism. The scalar action is the actual sectionwise
field scalar action, so its Ext groups carry the corresponding field
module structure. -/

namespace Red61
open AlgebraicGeometry CategoryTheory
noncomputable section

variable {Y : Scheme} (F : Type) [Field F] (f : Y ⟶ Spec (CommRingCat.of F))

def fieldSectionScalarMap (U : Y.Opens) : F →+* Γ(Y, U) :=
  (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp (globalScalarMap F f)

@[instance_reducible] def schemeHomBaseModule (M N : Y.Modules) : Module F (M ⟶ N) where
  smul a φ := φ ≫ fieldModuleScalar F f N a
  one_smul φ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U 1 • φ.app U x = φ.app U x
    rw [map_one, one_smul]
  mul_smul a b φ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U (a * b) • φ.app U x =
      fieldSectionScalarMap F f U a • (fieldSectionScalarMap F f U b • φ.app U x)
    rw [map_mul, mul_smul]
  smul_zero a := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U a • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add a φ ψ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U a • (φ.app U x + ψ.app U x) =
      fieldSectionScalarMap F f U a • φ.app U x + fieldSectionScalarMap F f U a • ψ.app U x
    exact smul_add _ _ _
  add_smul a b φ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U (a + b) • φ.app U x =
      fieldSectionScalarMap F f U a • φ.app U x + fieldSectionScalarMap F f U b • φ.app U x
    rw [map_add, add_smul]
  zero_smul φ := by
    apply Scheme.Modules.hom_ext
    intro U
    ext x
    change fieldSectionScalarMap F f U 0 • φ.app U x = 0
    rw [map_zero, zero_smul]

@[instance_reducible] def schemeModulesBaseLinear : Linear F Y.Modules where
  homModule := schemeHomBaseModule F f
  smul_comp M N P a φ ψ := by
    change (φ ≫ fieldModuleScalar F f N a) ≫ ψ = (φ ≫ ψ) ≫ fieldModuleScalar F f P a
    rw [Category.assoc, fieldModuleScalar_natural, ← Category.assoc]
  comp_smul M N P φ a ψ := by
    change φ ≫ (ψ ≫ fieldModuleScalar F f P a) = (φ ≫ ψ) ≫ fieldModuleScalar F f P a
    exact (Category.assoc _ _ _).symm

end
end Red61

section
/-! Cohomology of a sheaf of modules on a scheme, as Ext from the structure
sheaf in the abelian category of sheaves of modules, and its transport along
isomorphisms of sheaves of modules. -/

universe u

namespace Red61

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
noncomputable section

private local instance (Y : Scheme.{u}) : HasExt.{u} Y.Modules :=
  hasExt_of_enoughInjectives Y.Modules

abbrev ModuleCohomology (Y : Scheme) (M : Y.Modules) (n : ℕ) :=
  Ext (structureSheafModule Y) M n

def cohomologyPostcompose {Y : Scheme} {M N : Y.Modules} (φ : M ⟶ N) (n : ℕ) :
    ModuleCohomology Y M n →+ ModuleCohomology Y N n where
  toFun α := α.comp (Ext.mk₀ φ) (add_zero n)
  map_zero' := by simp
  map_add' _ _ := by simp

theorem cohomologyPostcompose_comp {Y : Scheme} {M N P : Y.Modules}
    (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    cohomologyPostcompose (φ ≫ ψ) n =
      (cohomologyPostcompose ψ n).comp (cohomologyPostcompose φ n) := by
  ext α
  change α.comp (Ext.mk₀ (φ ≫ ψ)) (add_zero n) =
    (α.comp (Ext.mk₀ φ) (add_zero n)).comp (Ext.mk₀ ψ) (add_zero n)
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

theorem cohomologyPostcompose_id (Y : Scheme) (M : Y.Modules) (n : ℕ) :
    cohomologyPostcompose (𝟙 M) n = AddMonoidHom.id (ModuleCohomology Y M n) := by
  ext α
  simp [cohomologyPostcompose]

def cohomologyPostcomposeEquiv {Y : Scheme} {M N : Y.Modules} (e : M ≅ N) (n : ℕ) :
    ModuleCohomology Y M n ≃+ ModuleCohomology Y N n where
  toFun := cohomologyPostcompose e.hom n
  invFun := cohomologyPostcompose e.inv n
  left_inv α := by
    change ((cohomologyPostcompose e.inv n).comp (cohomologyPostcompose e.hom n)) α = α
    rw [← cohomologyPostcompose_comp, e.hom_inv_id, cohomologyPostcompose_id]
    rfl
  right_inv α := by
    change ((cohomologyPostcompose e.hom n).comp (cohomologyPostcompose e.inv n)) α = α
    rw [← cohomologyPostcompose_comp, e.inv_hom_id, cohomologyPostcompose_id]
    rfl
  map_add' := (cohomologyPostcompose e.hom n).map_add

end
end Red61
end

/-! Native stalk maps and equivalences for module sheaves on a scheme.
The structure module's stalk identifies linearly with the actual local
ring, and all comparisons have their expected formulas on germs. -/

namespace Red61
open CategoryTheory AlgebraicGeometry TopCat Opposite
noncomputable section

universe u
variable (Y : Scheme.{u}) (y : Y)

private local instance (M : Y.Modules) :
    Module (Y.presheaf.stalk y) ↑(Presheaf.stalk (C := Ab.{u}) M.presheaf y) := by
  let M' : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
  exact inferInstanceAs (Module (Y.presheaf.stalk y)
    ↑(Presheaf.stalk (C := Ab.{u}) M'.presheaf y))

def schemeModuleStalkMap {M N : Y.Modules} (f : M ⟶ N) :
    ↑(Presheaf.stalk (C := Ab.{u}) M.presheaf y) →ₗ[Y.presheaf.stalk y]
      ↑(Presheaf.stalk (C := Ab.{u}) N.presheaf y) :=
  presheafModuleStalkMap Y.presheaf f.val y

def structureSheafModuleStalkEquiv :
    ↑(Presheaf.stalk (C := Ab.{u}) (structureSheafModule Y).presheaf y) ≃ₗ[Y.presheaf.stalk y]
      Y.presheaf.stalk y :=
  unitModuleStalkEquiv Y.presheaf y

theorem structureSheafModuleStalkEquiv_germ (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y, U)) :
    structureSheafModuleStalkEquiv Y y
        (Presheaf.germ (structureSheafModule Y).presheaf U y hy a) =
      Y.presheaf.germ U y hy a :=
  unitModuleStalkAddEquiv_germ Y.presheaf y U hy a

end
end Red61

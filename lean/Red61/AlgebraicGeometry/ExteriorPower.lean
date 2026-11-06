import Red61.AlgebraicGeometry.Differentials.Stalks
import Red61.AlgebraicGeometry.RationalForms.IntegralForms

/-! # Exterior powers of sheaves of modules

Formerly the modules `ModuleExteriorPresheaf`, `ModuleExteriorUniversal`, `NativeExteriorFunctor`, `ExteriorPresheafStalkMap`, `NativeExteriorRestriction`, `NativeExteriorStalkMap`, `ExteriorStalkSpecializes`, `ExteriorStalkSurjective`, `NativeFreeTopExterior`, `NativeAbsoluteExteriorStalk`, `NativeAbsoluteExteriorRange`, `NativeAbsoluteExteriorSpecializes`.
-/

/-! Ordinary exterior powers of modules over a ring presheaf assemble into
a native module presheaf via their actual semilinear restriction maps.
Functoriality is proved on wedges; native sheafification defines the
exterior module sheaf and its actual unit. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 4096
variable {C : Type} [Category.{0} C] (R : Cᵒᵖ ⥤ CommRingCat.{0})
  (M : PresheafOfModulesOfCommRing.{0} R) (n : ℕ)

def moduleExteriorPresheafObj (U : Cᵒᵖ) : ModuleCat (R.obj U) :=
  ModuleCat.of (R.obj U) (⋀[(R.obj U)]^n (M.obj U))

def moduleExteriorPresheafMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    moduleExteriorPresheafObj R M n U ⟶
      (ModuleCat.restrictScalars (R.map i).hom).obj
        (moduleExteriorPresheafObj R M n V) := by
  let g := semilinearExteriorMap (R.map i).hom n (M.restrictₛₗ i)
  exact ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (R.map i).hom).obj
    (moduleExteriorPresheafObj R M n V))
      { g.toAddHom with map_smul' := g.map_smul' }

theorem moduleExteriorPresheafMap_wedge {U V : Cᵒᵖ} (i : U ⟶ V)
    (a : Fin n → M.obj U) :
    moduleExteriorPresheafMap R M n i (exteriorPower.ιMulti (R.obj U) n a) =
      exteriorPower.ιMulti (R.obj V) n (fun j ↦ M.map i (a j)) :=
  semilinearExteriorMap_wedge (R.map i).hom n (M.restrictₛₗ i) a

theorem moduleExteriorMap_id_apply (U : Cᵒᵖ)
    (ω : ⋀[(R.obj U)]^n (M.obj U)) :
    moduleExteriorPresheafMap R M n (𝟙 U) ω = ω := by
  let g := semilinearExteriorMap (R.map (𝟙 U)).hom n (M.restrictₛₗ (𝟙 U))
  let f : (⋀[(R.obj U)]^n (M.obj U)) →ₗ[R.obj U] (⋀[(R.obj U)]^n (M.obj U)) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r v
        exact (g.map_smul' r v).trans (congrArg (fun a ↦ a • g v)
          (ConcreteCategory.congr_hom (R.map_id U) r)) }
  have hf : f = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    have ha : (fun j ↦ M.map (𝟙 U) (a j)) = a :=
      funext (fun j ↦ ConcreteCategory.congr_hom (M.presheaf.map_id U) (a j))
    exact (semilinearExteriorMap_wedge (R.map (𝟙 U)).hom n (M.restrictₛₗ (𝟙 U)) a).trans
      (congrArg (exteriorPower.ιMulti (R.obj U) n) ha)
  exact DFunLike.congr_fun hf ω

theorem moduleExteriorMap_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (ω : ⋀[(R.obj U)]^n (M.obj U)) :
    moduleExteriorPresheafMap R M n (i ≫ j) ω =
      moduleExteriorPresheafMap R M n j (moduleExteriorPresheafMap R M n i ω) := by
  let gi := semilinearExteriorMap (R.map i).hom n (M.restrictₛₗ i)
  let gj := semilinearExteriorMap (R.map j).hom n (M.restrictₛₗ j)
  let gij := semilinearExteriorMap (R.map (i ≫ j)).hom n (M.restrictₛₗ (i ≫ j))
  let f : (⋀[(R.obj U)]^n (M.obj U)) →ₛₗ[(R.map (i ≫ j)).hom]
      (⋀[(R.obj W)]^n (M.obj W)) :=
    { toFun := fun v ↦ gj (gi v)
      map_add' := by intro a b; rw [map_add, map_add]
      map_smul' := by
        intro r v
        have hr : (R.map j).hom ((R.map i).hom r) = (R.map (i ≫ j)).hom r :=
          (ConcreteCategory.congr_hom (R.map_comp i j) r).symm
        exact (congrArg gj (gi.map_smul' r v)).trans
          ((gj.map_smul' _ _).trans (congrArg (fun a ↦ a • gj (gi v)) hr)) }
  have hf : gij = f := by
    apply exteriorSemilinearMap_ext (R.map (i ≫ j)).hom n
    intro a
    have ha : (fun k ↦ M.map (i ≫ j) (a k)) =
        (fun k ↦ M.map j (M.map i (a k))) :=
      funext (fun k ↦ M.map_comp_apply i j (a k))
    change semilinearExteriorMap (R.map (i ≫ j)).hom n (M.restrictₛₗ (i ≫ j))
      (exteriorPower.ιMulti (R.obj U) n a) =
        semilinearExteriorMap (R.map j).hom n (M.restrictₛₗ j)
          (semilinearExteriorMap (R.map i).hom n (M.restrictₛₗ i)
            (exteriorPower.ιMulti (R.obj U) n a))
    rw [semilinearExteriorMap_wedge, semilinearExteriorMap_wedge, semilinearExteriorMap_wedge]
    exact congrArg (exteriorPower.ιMulti (R.obj W) n) ha

  exact DFunLike.congr_fun hf ω

def moduleExteriorAbPresheaf : Cᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (⋀[(R.obj U)]^n (M.obj U))
  map i := AddCommGrpCat.ofHom (semilinearExteriorMap (R.map i).hom n (M.restrictₛₗ i)).toAddHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact moduleExteriorMap_id_apply R M n U
  map_comp i j := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact moduleExteriorMap_comp_apply R M n i j

def moduleExteriorPresheaf : PresheafOfModulesOfCommRing.{0} R := by
  letI (U : Cᵒᵖ) : Module ((R ⋙ forget₂ CommRingCat RingCat).obj U)
      ((moduleExteriorAbPresheaf R M n).obj U) :=
    inferInstanceAs (Module (R.obj U) (⋀[(R.obj U)]^n (M.obj U)))
  exact PresheafOfModules.ofPresheaf (R := R ⋙ forget₂ CommRingCat RingCat)
    (moduleExteriorAbPresheaf R M n)
      (fun {U V} (i : U ⟶ V) r ω ↦
        (semilinearExteriorMap (R.map i).hom n (M.restrictₛₗ i)).map_smul' r ω)

variable (Y : Scheme.{0})

def nativeExteriorModule (N : Y.Modules) (n : ℕ) : Y.Modules :=
  modulePresheafSheafification Y (moduleExteriorPresheaf Y.presheaf N.val n)

def nativeExteriorModuleUnit (N : Y.Modules) (n : ℕ) :
    moduleExteriorPresheaf Y.presheaf N.val n ⟶ (nativeExteriorModule Y N n).val :=
  modulePresheafSheafificationUnit Y (moduleExteriorPresheaf Y.presheaf N.val n)
end
end Red61

/-! The native exterior module sheaf represents restriction-compatible
alternating maps into actual module sheaves. The Hom equivalence is proved
to be actual postcomposition with the universal alternating map, giving
existence and uniqueness with no basis or smoothness assumptions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
variable {C : Type} [Category.{0} C] (R : Cᵒᵖ ⥤ CommRingCat.{0})
  (M N : PresheafOfModulesOfCommRing.{0} R) (n : ℕ)

@[ext] structure ModulePresheafAlternatingMap where
  app (U : Cᵒᵖ) : M.obj U [⋀^Fin n]→ₗ[R.obj U] (N.obj U)
  naturality {U V : Cᵒᵖ} (i : U ⟶ V) (a : Fin n → M.obj U) :
    app V (fun j ↦ M.map i (a j)) = N.map i (app U a)

theorem moduleExteriorPresheaf_map_wedge {U V : Cᵒᵖ} (i : U ⟶ V)
    (a : Fin n → M.obj U) :
    (moduleExteriorPresheaf R M n).map i (exteriorPower.ιMulti (R.obj U) n a) =
      exteriorPower.ιMulti (R.obj V) n (fun j ↦ M.map i (a j)) :=
  moduleExteriorPresheafMap_wedge R M n i a

def moduleExteriorHomToAlternating (f : moduleExteriorPresheaf R M n ⟶ N) :
    ModulePresheafAlternatingMap R M N n where
  app U := (f.app U).hom.compAlternatingMap (exteriorPower.ιMulti (R.obj U) n)
  naturality {U V} i a :=
    (congrArg (f.app V) (moduleExteriorPresheaf_map_wedge R M n i a).symm).trans
      (PresheafOfModules.naturality_apply f i (exteriorPower.ιMulti (R.obj U) n a))

def moduleExteriorAlternatingDesc (a : ModulePresheafAlternatingMap R M N n) :
    moduleExteriorPresheaf R M n ⟶ N where
  app U := ModuleCat.ofHom (R := R.obj U) (X := (moduleExteriorPresheaf R M n).obj U)
    (Y := N.obj U) (exteriorPower.alternatingMapLinearEquiv (a.app U))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := R.obj U) (M := M.obj U) (n := n)
    apply AlternatingMap.ext
    intro v
    change exteriorPower.alternatingMapLinearEquiv (a.app V)
      ((moduleExteriorPresheaf R M n).map i (exteriorPower.ιMulti (R.obj U) n v)) =
        N.map i (exteriorPower.alternatingMapLinearEquiv (a.app U)
          (exteriorPower.ιMulti (R.obj U) n v))
    exact (congrArg (exteriorPower.alternatingMapLinearEquiv (a.app V))
      (moduleExteriorPresheaf_map_wedge R M n i v)).trans
        ((exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (a.app V) _).trans
          ((a.naturality i v).trans (congrArg (N.map i)
            (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (a.app U) v).symm)))

def moduleExteriorHomEquiv :
    (moduleExteriorPresheaf R M n ⟶ N) ≃ ModulePresheafAlternatingMap R M N n where
  toFun := moduleExteriorHomToAlternating R M N n
  invFun := moduleExteriorAlternatingDesc R M N n
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := R.obj U) (M := M.obj U) (n := n)
    apply AlternatingMap.ext
    intro a
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
      ((moduleExteriorHomToAlternating R M N n f).app U) a
  right_inv a := by
    apply ModulePresheafAlternatingMap.ext
    funext U
    apply AlternatingMap.ext
    intro v
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (a.app U) v

variable {R M N n} in
def ModulePresheafAlternatingMap.postcomp {L : PresheafOfModulesOfCommRing.{0} R}
    (a : ModulePresheafAlternatingMap R M N n) (f : N ⟶ L) :
    ModulePresheafAlternatingMap R M L n where
  app U := (f.app U).hom.compAlternatingMap (a.app U)
  naturality {U V} i v := (congrArg (f.app V) (a.naturality i v)).trans
    (PresheafOfModules.naturality_apply f i (a.app U v))

variable (Y : Scheme.{0}) (P Q : Y.Modules)

def nativeExteriorHomEquiv (n : ℕ) :
    (nativeExteriorModule Y P n ⟶ Q) ≃ ModulePresheafAlternatingMap Y.presheaf P.val Q.val n :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    (moduleExteriorPresheaf Y.presheaf P.val n) Q).trans
      (moduleExteriorHomEquiv Y.presheaf P.val Q.val n)

def nativeExteriorUniversalAlternatingMap (n : ℕ) :
    ModulePresheafAlternatingMap Y.presheaf P.val (nativeExteriorModule Y P n).val n :=
  moduleExteriorHomToAlternating Y.presheaf P.val (nativeExteriorModule Y P n).val n
    (nativeExteriorModuleUnit Y P n)

theorem nativeExteriorHomEquiv_apply (n : ℕ) (f : nativeExteriorModule Y P n ⟶ Q) :
    nativeExteriorHomEquiv Y P Q n f =
      (nativeExteriorUniversalAlternatingMap Y P n).postcomp f.val := by
  apply ModulePresheafAlternatingMap.ext
  funext U
  apply AlternatingMap.ext
  intro a
  rfl

end
end Red61

/-! Native exterior module sheaves form a genuine functor on module
sheaves. Its maps preserve actual unit wedges, satisfy identity and
composition, and are uniquely determined by those wedge values. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
variable {C : Type} [Category.{0} C] {R : Cᵒᵖ ⥤ CommRingCat.{0}}
  {M N : PresheafOfModulesOfCommRing.{0} R} {n : ℕ}

def ModulePresheafAlternatingMap.precomp {L : PresheafOfModulesOfCommRing.{0} R}
    (a : ModulePresheafAlternatingMap R M N n) (f : L ⟶ M) :
    ModulePresheafAlternatingMap R L N n where
  app U := (a.app U).compLinearMap (f.app U).hom
  naturality {U V} i v := by
    have hv : (fun j ↦ f.app V (L.map i (v j))) =
        (fun j ↦ M.map i (f.app U (v j))) :=
      funext (fun j ↦ PresheafOfModules.naturality_apply f i (v j))
    exact (congrArg (a.app V) hv).trans (a.naturality i (fun j ↦ f.app U (v j)))

variable (Y : Scheme.{0}) {P Q T : Y.Modules}

def nativeExteriorMap (n : ℕ) (f : P ⟶ Q) :
    nativeExteriorModule Y P n ⟶ nativeExteriorModule Y Q n :=
  (nativeExteriorHomEquiv Y P (nativeExteriorModule Y Q n) n).symm
    ((nativeExteriorUniversalAlternatingMap Y Q n).precomp f.val)

theorem nativeExteriorMap_wedge (n : ℕ) (f : P ⟶ Q) (U : Y.Opensᵒᵖ)
    (v : Fin n → P.val.obj U) :
    (nativeExteriorMap Y n f).val.app U
        ((nativeExteriorModuleUnit Y P n).app U (exteriorPower.ιMulti (Y.presheaf.obj U) n v)) =
      (nativeExteriorModuleUnit Y Q n).app U
        (exteriorPower.ιMulti (Y.presheaf.obj U) n (fun j ↦ f.val.app U (v j))) := by
  have he := (nativeExteriorHomEquiv_apply Y P (nativeExteriorModule Y Q n) n
    (nativeExteriorMap Y n f)).symm.trans
      (Equiv.apply_symm_apply (nativeExteriorHomEquiv Y P (nativeExteriorModule Y Q n) n) _)
  exact congrArg (fun a ↦ a.app U v) he

theorem nativeExterior_hom_ext (n : ℕ) {f g : nativeExteriorModule Y P n ⟶ Q}
    (h : ∀ (U : Y.Opensᵒᵖ) (v : Fin n → P.val.obj U),
      f.val.app U ((nativeExteriorModuleUnit Y P n).app U
        (exteriorPower.ιMulti (Y.presheaf.obj U) n v)) =
      g.val.app U ((nativeExteriorModuleUnit Y P n).app U
        (exteriorPower.ιMulti (Y.presheaf.obj U) n v))) : f = g := by
  apply (nativeExteriorHomEquiv Y P Q n).injective
  rw [nativeExteriorHomEquiv_apply, nativeExteriorHomEquiv_apply]
  apply ModulePresheafAlternatingMap.ext
  funext U
  apply AlternatingMap.ext
  intro v
  exact h U v

theorem nativeExteriorMap_id (n : ℕ) (P : Y.Modules) :
    nativeExteriorMap Y n (𝟙 P) = 𝟙 (nativeExteriorModule Y P n) := by
  apply nativeExterior_hom_ext Y n
  intro U v
  exact nativeExteriorMap_wedge Y n (𝟙 P) U v

theorem nativeExteriorMap_comp (n : ℕ) (f : P ⟶ Q) (g : Q ⟶ T) :
    nativeExteriorMap Y n (f ≫ g) = nativeExteriorMap Y n f ≫ nativeExteriorMap Y n g := by
  apply nativeExterior_hom_ext Y n
  intro U v
  exact (nativeExteriorMap_wedge Y n (f ≫ g) U v).trans
    (((congrArg ((nativeExteriorMap Y n g).val.app U)
      (nativeExteriorMap_wedge Y n f U v)).trans
        (nativeExteriorMap_wedge Y n g U (fun j ↦ f.val.app U (v j)))).symm)

def nativeExteriorFunctor (n : ℕ) : Y.Modules ⥤ Y.Modules where
  obj P := nativeExteriorModule Y P n
  map f := nativeExteriorMap Y n f
  map_id P := nativeExteriorMap_id Y n P
  map_comp f g := nativeExteriorMap_comp Y n f g
end
end Red61

/-! The actual germ maps induce a canonical map from a stalk of the
exterior module presheaf to the exterior power of the native module stalk.
It commutes with restrictions and is linear over the actual local ring. -/

namespace Red61
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Module
noncomputable section
variable (Y : Scheme.{0}) (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) (x : Y) (n : ℕ)
private local instance : Module (Y.presheaf.stalk x) ((modulePresheafAbPresheaf Y M).stalk x) :=
  schemeModuleStalkModule Y M x

/-- The actual module germ, semilinear for the native ring germ. -/
def moduleSectionToStalkSemilinear (U : Y.Opens) (hx : x ∈ U) :
    M.obj (op U) →ₛₗ[(Y.presheaf.germ U x hx).hom] (modulePresheafAbPresheaf Y M).stalk x where
  toFun := (modulePresheafAbPresheaf Y M).germ U x hx
  map_add' := map_add ((modulePresheafAbPresheaf Y M).germ U x hx).hom
  map_smul' := PresheafOfModules.germ_smul M x U hx

/-- Exterior transport through the actual module and ring germs. -/
def moduleExteriorGermMap (U : Y.Opens) (hx : x ∈ U) :
    (moduleExteriorPresheaf Y.presheaf M n).obj (op U)
      →ₛₗ[(Y.presheaf.germ U x hx).hom]
        (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x)) :=
  semilinearExteriorMap (Y.presheaf.germ U x hx).hom n
    (moduleSectionToStalkSemilinear Y M x U hx)

/-- Exterior germs preserve the wedge of the actual section germs. -/
theorem moduleExteriorGermMap_wedge (U : Y.Opens) (hx : x ∈ U) (v : Fin n → M.obj (op U)) :
    moduleExteriorGermMap Y M x n U hx (exteriorPower.ιMulti (Y.presheaf.obj (op U)) n v) =
      exteriorPower.ιMulti (Y.presheaf.stalk x) n
        (fun j ↦ (modulePresheafAbPresheaf Y M).germ U x hx (v j)) :=
  semilinearExteriorMap_wedge (Y.presheaf.germ U x hx).hom n
    (moduleSectionToStalkSemilinear Y M x U hx) v

/-- Exterior germs commute with neighborhood restriction. -/
theorem moduleExteriorGermMap_restrict {U W : Y.Opens} (i : W ⟶ U) (hx : x ∈ W)
    (ω : (moduleExteriorPresheaf Y.presheaf M n).obj (op U)) :
    moduleExteriorGermMap Y M x n W hx
        ((moduleExteriorPresheaf Y.presheaf M n).map i.op ω) =
      moduleExteriorGermMap Y M x n U (i.le hx) ω := by
  let : RingHomCompTriple
      (RingCat.Hom.hom ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).map i.op))
      (Y.presheaf.germ W x hx).hom
      (Y.presheaf.germ U x (i.le hx)).hom :=
    ⟨congrArg CommRingCat.Hom.hom (Y.presheaf.germ_res i x hx)⟩
  have he : ((moduleExteriorGermMap Y M x n W hx).comp
      ((moduleExteriorPresheaf Y.presheaf M n).restrictₛₗ i.op) :
      (moduleExteriorPresheaf Y.presheaf M n).obj (op U) →ₛₗ[
        (Y.presheaf.germ U x (i.le hx)).hom]
          (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x))) =
      moduleExteriorGermMap Y M x n U (i.le hx) := by
    apply exteriorSemilinearMap_ext (Y.presheaf.germ U x (i.le hx)).hom n
    intro v
    change moduleExteriorGermMap Y M x n W hx
      ((moduleExteriorPresheaf Y.presheaf M n).map i.op
        (exteriorPower.ιMulti (Y.presheaf.obj (op U)) n v)) = _
    have hw := moduleExteriorPresheaf_map_wedge Y.presheaf M n i.op v
    have hW := moduleExteriorGermMap_wedge Y M x n W hx
      (fun j ↦ (show M.obj (op W) from M.map i.op (v j)))
    have hU := moduleExteriorGermMap_wedge Y M x n U (i.le hx) v
    exact (congrArg (moduleExteriorGermMap Y M x n W hx) hw).trans
      (hW.trans ((congrArg (exteriorPower.ιMulti (Y.presheaf.stalk x) n)
        (funext (fun j ↦ TopCat.Presheaf.germ_res_apply
          (modulePresheafAbPresheaf Y M) i x hx (v j)))).trans hU.symm))
  exact LinearMap.congr_fun he ω

/-- The compatible exterior germ maps as an actual stalk cocone. -/
def moduleExteriorStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      modulePresheafAbPresheaf Y (moduleExteriorPresheaf Y.presheaf M n)) where
  pt := AddCommGrpCat.of
    (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x))
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (moduleExteriorGermMap Y M x n U.unop.val U.unop.property).toAddMonoidHom
      naturality := by
        intro U V i
        ext ω
        exact moduleExteriorGermMap_restrict Y M x n
          ((OpenNhds.inclusion x).map i.unop) V.unop.property ω }

/-- The canonical additive comparison induced by the stalk colimit. -/
def moduleExteriorStalkToExteriorAddHom :
    (modulePresheafAbPresheaf Y (moduleExteriorPresheaf Y.presheaf M n)).stalk x →+
      (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x)) :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙
    modulePresheafAbPresheaf Y (moduleExteriorPresheaf Y.presheaf M n))
      (moduleExteriorStalkCocone Y M x n)).hom

/-- The stalk comparison retains every original exterior germ. -/
theorem moduleExteriorStalkToExteriorAddHom_germ (U : Y.Opens) (hx : x ∈ U)
    (ω : (moduleExteriorPresheaf Y.presheaf M n).obj (op U)) :
    moduleExteriorStalkToExteriorAddHom Y M x n
        ((modulePresheafAbPresheaf Y (moduleExteriorPresheaf Y.presheaf M n)).germ U x hx ω) =
      moduleExteriorGermMap Y M x n U hx ω :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (moduleExteriorStalkCocone Y M x n) (op ⟨U, hx⟩)) ω

/-- The canonical exterior stalk comparison is linear over the local ring. -/
def moduleExteriorStalkToExteriorLinear :
    letI := schemeModuleStalkModule Y (moduleExteriorPresheaf Y.presheaf M n) x
    (modulePresheafAbPresheaf Y (moduleExteriorPresheaf Y.presheaf M n)).stalk x →ₗ[
      Y.presheaf.stalk x] (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x)) := by
  letI := schemeModuleStalkModule Y (moduleExteriorPresheaf Y.presheaf M n) x
  exact
    { moduleExteriorStalkToExteriorAddHom Y M x n with
      map_smul' := presheafModuleStalk_smul_of_germ Y.presheaf x
        (moduleExteriorStalkToExteriorAddHom Y M x n) (fun U hx r ω ↦ by
          rw [moduleExteriorStalkToExteriorAddHom_germ,
            moduleExteriorStalkToExteriorAddHom_germ]
          exact map_smulₛₗ (moduleExteriorGermMap Y M x n U hx) r ω) }
end
end Red61

/-! Genuine exterior module sheaves commute with native open-immersion
restriction. The actual ring-isomorphism component maps are bijective,
commute on overlaps, and retain the unit wedge formula after native
module sheafification. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
  (n : ℕ)

def moduleRestrictionSectionSemilinear (U : X.Opensᵒᵖ) :
    (M.restrict f).val.obj U →ₛₗ[(f.appIso U.unop).inv.hom] M.val.obj (op (f ''ᵁ U.unop)) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def moduleRestrictionSectionSemilinearInv (U : X.Opensᵒᵖ) :
    M.val.obj (op (f ''ᵁ U.unop)) →ₛₗ[(f.appIso U.unop).hom.hom] (M.restrict f).val.obj U where
  toFun := id
  map_add' _ _ := rfl
  map_smul' r v := by
    change r • v = (f.appIso U.unop).inv ((f.appIso U.unop).hom r) • v
    exact (congrArg (fun a ↦ a • v)
      ((f.appIso U.unop).commRingCatIsoToRingEquiv.symm_apply_apply r)).symm

def exteriorRestrictionComponent (U : X.Opensᵒᵖ) :
    (moduleExteriorPresheaf X.presheaf (M.restrict f).val n).obj U ⟶
      ((nativeModulePresheafRestrictionFunctor f).obj
        (moduleExteriorPresheaf Y.presheaf M.val n)).obj U := by
  let g := semilinearExteriorMap (f.appIso U.unop).inv.hom n
    (moduleRestrictionSectionSemilinear f M U)
  exact ModuleCat.ofHom (R := X.presheaf.obj U)
    (X := (moduleExteriorPresheaf X.presheaf (M.restrict f).val n).obj U)
    (Y := ((nativeModulePresheafRestrictionFunctor f).obj
      (moduleExteriorPresheaf Y.presheaf M.val n)).obj U)
        { g.toAddHom with map_smul' := g.map_smul' }

theorem exteriorRestrictionComponent_bijective (U : X.Opensᵒᵖ) :
    Function.Bijective (exteriorRestrictionComponent f M n U) :=
  semilinearExteriorMap_bijective n (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
    (moduleRestrictionSectionSemilinear f M U) (moduleRestrictionSectionSemilinearInv f M U)
      (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem exteriorRestrictionComponent_natural {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (moduleExteriorPresheaf X.presheaf (M.restrict f).val n).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (exteriorRestrictionComponent f M n V) =
      exteriorRestrictionComponent f M n U ≫
        ((nativeModulePresheafRestrictionFunctor f).obj
          (moduleExteriorPresheaf Y.presheaf M.val n)).map i := by
  let yi := f.opensFunctor.op.map i
  let τ := (Y.presheaf.map yi).hom.comp (f.appIso U.unop).inv.hom
  let : RingHomCompTriple (f.appIso U.unop).inv.hom (Y.presheaf.map yi).hom τ := ⟨rfl⟩
  let : RingHomCompTriple (X.presheaf.map i).hom (f.appIso V.unop).inv.hom τ :=
    ⟨congrArg CommRingCat.Hom.hom (f.appIso_inv_naturality i)⟩
  refine ModuleCat.hom_ext
    (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun ω ↦ ?_))
  have hm : ∀ v, M.val.restrictₛₗ yi (moduleRestrictionSectionSemilinear f M U v) =
      moduleRestrictionSectionSemilinear f M V ((M.restrict f).val.restrictₛₗ i v) := by
    intro v
    exact (ConcreteCategory.congr_hom
      (PresheafOfModules.forget₂_map_pushforward_obj_map
        (φ := Functor.whiskerRight (openImmersionPresheafScalars f)
          (forget₂ CommRingCat RingCat)) i M.val) v).symm
  have h := semilinearExteriorMap_natural (X.presheaf.map i).hom
    (f.appIso U.unop).inv.hom (Y.presheaf.map yi).hom (f.appIso V.unop).inv.hom τ n
      ((M.restrict f).val.restrictₛₗ i) (moduleRestrictionSectionSemilinear f M U)
      (M.val.restrictₛₗ yi) (moduleRestrictionSectionSemilinear f M V) hm ω
  have hp := PresheafOfModules.forget₂_map_pushforward_obj_map
    (φ := Functor.whiskerRight (openImmersionPresheafScalars f)
      (forget₂ CommRingCat RingCat)) i (moduleExteriorPresheaf Y.presheaf M.val n)
  exact h.symm.trans (ConcreteCategory.congr_hom hp
    (exteriorRestrictionComponent f M n U ω)).symm

def exteriorPresheafRestrictionIso :
    moduleExteriorPresheaf X.presheaf (M.restrict f).val n ≅
      (nativeModulePresheafRestrictionFunctor f).obj
        (moduleExteriorPresheaf Y.presheaf M.val n) :=
  PresheafOfModulesOfCommRing.isoMk
    (fun U ↦ (LinearEquiv.ofBijective (exteriorRestrictionComponent f M n U).hom
      (exteriorRestrictionComponent_bijective f M n U)).toModuleIso)
    (fun {_U _V} i ↦ exteriorRestrictionComponent_natural f M n i)

def nativeExteriorRestrictionIso :
    nativeExteriorModule X (M.restrict f) n ≅ (nativeExteriorModule Y M n).restrict f :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorPresheafRestrictionIso f M n) ≪≫
      moduleSheafificationRestrictionIso f (moduleExteriorPresheaf Y.presheaf M.val n)

end
end Red61

/-! The genuine exterior module sheaf has a canonical linear stalk map
to the ordinary exterior power of the native module stalk. The map retains
the actual sheafification-unit germs and their wedge values. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) (M : Y.Modules) (x : Y) (n : ℕ)
private local instance : Module (Y.presheaf.stalk x) (M.presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y M x
private local instance :
    Module (Y.presheaf.stalk x) ((nativeExteriorModule Y M n).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (nativeExteriorModule Y M n) x

/-- The canonical comparison for the genuine exterior sheaf stalk. -/
def nativeExteriorStalkToExterior :
    (nativeExteriorModule Y M n).presheaf.stalk x →ₗ[Y.presheaf.stalk x]
      (⋀[Y.presheaf.stalk x]^n (M.presheaf.stalk x)) := by
  letI := schemeModuleStalkModule Y (moduleExteriorPresheaf Y.presheaf M.val n) x
  exact (moduleExteriorStalkToExteriorLinear Y M.val x n).comp
    (modulePresheafSheafificationStalkEquiv Y
      (moduleExteriorPresheaf Y.presheaf M.val n) x).symm.toLinearMap

/-- The comparison preserves the original sheafification-unit germs. -/
theorem nativeExteriorStalkToExterior_unit_germ (U : Y.Opens) (hx : x ∈ U)
    (ω : (moduleExteriorPresheaf Y.presheaf M.val n).obj (op U)) :
    nativeExteriorStalkToExterior Y M x n
        ((nativeExteriorModule Y M n).presheaf.germ U x hx
          ((nativeExteriorModuleUnit Y M n).app (op U) ω)) =
      moduleExteriorGermMap Y M.val x n U hx ω := by
  let := schemeModuleStalkModule Y (moduleExteriorPresheaf Y.presheaf M.val n) x
  have h := modulePresheafSheafificationStalkEquiv_germ Y
    (moduleExteriorPresheaf Y.presheaf M.val n) x U hx ω
  change moduleExteriorStalkToExteriorLinear Y M.val x n
    ((modulePresheafSheafificationStalkEquiv Y
      (moduleExteriorPresheaf Y.presheaf M.val n) x).symm _) = _
  let e := modulePresheafSheafificationStalkEquiv Y
    (moduleExteriorPresheaf Y.presheaf M.val n) x
  have hi := (congrArg e.symm h.symm).trans (e.symm_apply_apply _)
  exact (congrArg (moduleExteriorStalkToExteriorLinear Y M.val x n) hi).trans
    (moduleExteriorStalkToExteriorAddHom_germ Y M.val x n U hx ω)

/-- A genuine exterior wedge germ maps to the wedge of its section germs. -/
theorem nativeExteriorStalkToExterior_wedge_germ (U : Y.Opens) (hx : x ∈ U)
    (v : Fin n → M.val.obj (op U)) :
    nativeExteriorStalkToExterior Y M x n
        ((nativeExteriorModule Y M n).presheaf.germ U x hx
          ((nativeExteriorModuleUnit Y M n).app (op U)
            (exteriorPower.ιMulti (Y.presheaf.obj (op U)) n v))) =
      exteriorPower.ιMulti (Y.presheaf.stalk x) n
        (fun j ↦ M.presheaf.germ U x hx (v j)) :=
  (nativeExteriorStalkToExterior_unit_germ Y M x n U hx _).trans
    (moduleExteriorGermMap_wedge Y M.val x n U hx v)
end
end Red61

/-! The exterior stalk comparison commutes with specialization, before
and after genuine native sheafification. The diagrams retain the actual
ring and module specialization maps in every exterior degree. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)
  {x y : Y} (h : x ⤳ y) (n : ℕ)
private local instance (z : Y) :
    Module (Y.presheaf.stalk z) ((modulePresheafAbPresheaf Y M).stalk z) :=
  schemeModuleStalkModule Y M z

/-- Exterior germ transport commutes with actual module specialization. -/
theorem moduleExteriorGermMap_specializes (U : Y.Opens) (hy : y ∈ U)
    (ω : (moduleExteriorPresheaf Y.presheaf M n).obj (op U)) :
    semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
        (moduleStalkSpecializesSemilinear Y M h) (moduleExteriorGermMap Y M y n U hy ω) =
      moduleExteriorGermMap Y M x n U (h.mem_open U.isOpen hy) ω := by
  let τ := (Y.presheaf.germ U x (h.mem_open U.isOpen hy)).hom
  let : RingHomCompTriple (Y.presheaf.germ U y hy).hom
      (Y.presheaf.stalkSpecializes h).hom τ :=
    ⟨congrArg CommRingCat.Hom.hom (Y.presheaf.germ_stalkSpecializes hy h)⟩
  have he : ((semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
      (moduleStalkSpecializesSemilinear Y M h)).comp
        (moduleExteriorGermMap Y M y n U hy) :
      (moduleExteriorPresheaf Y.presheaf M n).obj (op U) →ₛₗ[τ]
        (⋀[Y.presheaf.stalk x]^n ((modulePresheafAbPresheaf Y M).stalk x))) =
      moduleExteriorGermMap Y M x n U (h.mem_open U.isOpen hy) := by
    apply exteriorSemilinearMap_ext τ n
    intro v
    change semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
      (moduleStalkSpecializesSemilinear Y M h)
        (moduleExteriorGermMap Y M y n U hy
          (exteriorPower.ιMulti (Y.presheaf.obj (op U)) n v)) = _
    have hyw := moduleExteriorGermMap_wedge Y M y n U hy v
    have hxw := moduleExteriorGermMap_wedge Y M x n U (h.mem_open U.isOpen hy) v
    exact (congrArg (semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
      (moduleStalkSpecializesSemilinear Y M h)) hyw).trans
        ((semilinearExteriorMap_wedge (Y.presheaf.stalkSpecializes h).hom n
          (moduleStalkSpecializesSemilinear Y M h)
          (fun j ↦ (modulePresheafAbPresheaf Y M).germ U y hy (v j))).trans
            ((congrArg (exteriorPower.ιMulti (Y.presheaf.stalk x) n)
              (funext (fun j ↦ moduleStalkSpecializesSemilinear_germ Y M h U hy (v j)))).trans
                hxw.symm))
  exact LinearMap.congr_fun he ω

variable (N : Y.Modules)
private local instance (z : Y) : Module (Y.presheaf.stalk z) (N.presheaf.stalk z) :=
  schemeModuleNativeStalkModule Y N z
private local instance (z : Y) :
    Module (Y.presheaf.stalk z) ((nativeExteriorModule Y N n).presheaf.stalk z) :=
  schemeModuleNativeStalkModule Y (nativeExteriorModule Y N n) z

/-- The genuine exterior sheaf stalk comparison commutes with specialization. -/
theorem nativeExteriorStalkToExterior_specializes
    (ξ : (nativeExteriorModule Y N n).presheaf.stalk y) :
    nativeExteriorStalkToExterior Y N x n
        (moduleStalkSpecializesSemilinear Y (nativeExteriorModule Y N n).val h ξ) =
      semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
        (moduleStalkSpecializesSemilinear Y N.val h)
        (nativeExteriorStalkToExterior Y N y n ξ) := by
  let E := moduleExteriorPresheaf Y.presheaf N.val n
  let := schemeModuleStalkModule Y E y
  let e := modulePresheafSheafificationStalkEquiv Y E y
  obtain ⟨η, hη⟩ := e.surjective ξ
  obtain ⟨U, hy, ω, rfl⟩ := (modulePresheafAbPresheaf Y E).exists_germ_eq η
  have hξ : (nativeExteriorModule Y N n).presheaf.germ U y hy
      ((nativeExteriorModuleUnit Y N n).app (op U) ω) = ξ :=
    (modulePresheafSheafificationStalkEquiv_germ Y E y U hy ω).symm.trans hη
  rw [← hξ]
  have hs := moduleStalkSpecializesSemilinear_germ Y
    (nativeExteriorModule Y N n).val h U hy ((nativeExteriorModuleUnit Y N n).app (op U) ω)
  exact (congrArg (nativeExteriorStalkToExterior Y N x n) hs).trans
    ((nativeExteriorStalkToExterior_unit_germ Y N x n U (h.mem_open U.isOpen hy) ω).trans
      ((moduleExteriorGermMap_specializes Y N.val h n U hy ω).symm.trans
        (congrArg (semilinearExteriorMap (Y.presheaf.stalkSpecializes h).hom n
          (moduleStalkSpecializesSemilinear Y N.val h))
          (nativeExteriorStalkToExterior_unit_germ Y N y n U hy ω).symm)))
end
end Red61

/-! The canonical comparison from the genuine exterior sheaf stalk is
surjective in every degree. Finite tuples of stalk elements have original
section representatives on one common neighborhood. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
variable (Y : Scheme.{0}) (M : Y.Modules) (x : Y) (n : ℕ)
private local instance : Module (Y.presheaf.stalk x) (M.presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y M x
private local instance :
    Module (Y.presheaf.stalk x) ((nativeExteriorModule Y M n).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (nativeExteriorModule Y M n) x

/-- Every finite tuple of native module stalk elements has common section representatives. -/
theorem moduleStalk_fin_germ_representatives (v : Fin n → M.presheaf.stalk x) :
    ∃ (U : Y.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
      ∀ j, M.presheaf.germ U x hx (a j) = v j := by
  choose U hx a ha using (fun j ↦ M.presheaf.exists_germ_eq (v j))
  let W : Y.Opens := ⨅ j, U j
  have hW : x ∈ W := by
    change x ∈ (↑(⨅ j, U j) : Set Y)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  let b (j : Fin n) : M.val.obj (op W) :=
    M.val.map (homOfLE (iInf_le U j)).op (a j)
  refine ⟨W, hW, b, fun j ↦ ?_⟩
  exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (iInf_le U j)) x hW (a j)).trans
    (ha j)

/-- The genuine exterior stalk comparison is surjective in every degree. -/
theorem nativeExteriorStalkToExterior_surjective :
    Function.Surjective (nativeExteriorStalkToExterior Y M x n) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← exteriorPower.ιMulti_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  obtain ⟨U, hx, a, ha⟩ := moduleStalk_fin_germ_representatives Y M x n v
  refine ⟨(nativeExteriorModule Y M n).presheaf.germ U x hx
    ((nativeExteriorModuleUnit Y M n).app (op U)
      (exteriorPower.ιMulti (Y.presheaf.obj (op U)) n a)), ?_⟩
  exact (nativeExteriorStalkToExterior_wedge_germ Y M x n U hx a).trans
    (congrArg (exteriorPower.ιMulti (Y.presheaf.stalk x) n) (funext ha))
end
end Red61

/-! The genuine top exterior sheaf of a finite free native module sheaf
is the structure sheaf. The comparison is formed on actual open sections,
commutes with restrictions, and sends the standard volume to one after
native sheafification. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) (n : ℕ)
set_option quotPrecheck false in
local notation "P" => (SheafOfModules.free (R := Y.ringCatSheaf) (Fin n) : Y.Modules)
set_option quotPrecheck false in
local notation "O" => (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)

private local instance (U : Y.Opensᵒᵖ) :
    Module (Y.presheaf.obj U) ((P).val.obj U) := ((P).val.obj U).isModule

/-- The standard finite free basis, typed in the native module presheaf. -/
def nativeFiniteFreeSectionBasis (U : Y.Opensᵒᵖ) :
    Basis (Fin n) (Y.presheaf.obj U) ((P).val.obj U) :=
  finiteFreeSectionBasis Y (Fin n) U.unop

/-- The standard basis is preserved by the actual section restrictions. -/
theorem nativeFiniteFreeSectionBasis_natural {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (j : Fin n) :
    (P).val.map i (nativeFiniteFreeSectionBasis Y n U j) =
      nativeFiniteFreeSectionBasis Y n V j :=
  finiteFreeSectionBasis_natural Y (Fin n) i j

/-- Coefficient of the standard top exterior volume on one open. -/
def finiteFreeTopExteriorComponent (U : Y.Opensᵒᵖ) :
    (moduleExteriorPresheaf Y.presheaf (P).val n).obj U ⟶ (O).val.obj U := by
  let e := integralTopExteriorCoefficient (nativeFiniteFreeSectionBasis Y n U)
  exact ModuleCat.ofHom (R := Y.presheaf.obj U)
    (X := (moduleExteriorPresheaf Y.presheaf (P).val n).obj U) (Y := (O).val.obj U)
      { e.toAddHom with map_smul' := e.map_smul }

/-- The top exterior coefficient is an isomorphism on every open. -/
def finiteFreeTopExteriorComponentIso (U : Y.Opensᵒᵖ) :
    (moduleExteriorPresheaf Y.presheaf (P).val n).obj U ≅ (O).val.obj U :=
  (LinearEquiv.ofBijective (finiteFreeTopExteriorComponent Y n U).hom
    (integralTopExteriorCoefficient (nativeFiniteFreeSectionBasis Y n U)).bijective).toModuleIso

/-- Top exterior coefficients commute with all section restrictions. -/
theorem finiteFreeTopExteriorComponent_natural {U V : Y.Opensᵒᵖ} (i : U ⟶ V) :
    (moduleExteriorPresheaf Y.presheaf (P).val n).map i ≫
        (ModuleCat.restrictScalars (Y.presheaf.map i).hom).map
          (finiteFreeTopExteriorComponent Y n V) =
      finiteFreeTopExteriorComponent Y n U ≫ (O).val.map i := by
  refine ModuleCat.hom_ext
    (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun ω ↦ ?_))
  exact integralTopExteriorCoefficient_ringHom
    (V := (P).val.obj U) (W := (P).val.obj V) (Y.presheaf.map i).hom
    (nativeFiniteFreeSectionBasis Y n U) (nativeFiniteFreeSectionBasis Y n V)
    ((P).val.restrictₛₗ i) (nativeFiniteFreeSectionBasis_natural Y n i) ω

/-- The top exterior presheaf of the finite free sheaf is the unit presheaf. -/
def finiteFreeTopExteriorPresheafIso :
    moduleExteriorPresheaf Y.presheaf (P).val n ≅ (O).val :=
  PresheafOfModulesOfCommRing.isoMk (R := Y.presheaf)
    (M₁ := moduleExteriorPresheaf Y.presheaf (P).val n) (M₂ := (O).val)
    (finiteFreeTopExteriorComponentIso Y n)
    (fun {_U _V} i ↦ finiteFreeTopExteriorComponent_natural Y n i)

/-- The genuine top exterior sheaf of the finite free sheaf is the unit sheaf. -/
def nativeFiniteFreeTopExteriorIso : nativeExteriorModule Y (P) n ≅ (O) := by
  have : IsIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit :=
    PresheafOfModules.instIsIsoFunctorSheafOfModulesCounitSheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)
  exact (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso
    (finiteFreeTopExteriorPresheafIso Y n) ≪≫
      asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit.app (O))

end
end Red61

/-! The genuine absolute exterior sheaf maps at every stalk to ordinary
local-ring exterior differentials and then to rational forms. Its wedge germ
formula is explicit, and a local differential basis proves integrality. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
variable (Y : Scheme.{0}) (x : Y) (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : Module (Y.presheaf.stalk x) ((D).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (D) x
private local instance : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x

/-- The genuine exterior stalk comparison with ordinary local differentials. -/
def nativeAbsoluteExteriorStalkToOrdinary :
    (E).presheaf.stalk x →ₗ[Y.presheaf.stalk x]
      (⋀[Y.presheaf.stalk x]^n (KaehlerDifferential ℤ (Y.presheaf.stalk x))) :=
  (exteriorPower.map n (nativeAbsoluteDifferentialSheafStalkEquiv Y x).symm.toLinearMap).comp
    (nativeExteriorStalkToExterior Y (D) x n)

variable [IsIntegral Y]
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

/-- The basis-free rational realization of the genuine exterior sheaf stalk. -/
def nativeAbsoluteExteriorStalkToRational :
    (E).presheaf.stalk x →ₛₗ[algebraMap (Y.presheaf.stalk x) Y.functionField]
      RationalSchemeForms Y n :=
  (integerDifferentialExteriorMap (algebraMap (Y.presheaf.stalk x) Y.functionField) n).comp
    (nativeAbsoluteExteriorStalkToOrdinary Y x n)

theorem nativeAbsoluteExteriorStalkToRational_integral
    (b : Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))
    (ξ : (E).presheaf.stalk x) :
    IsIntegralStalkTopForm x (nativeAbsoluteExteriorStalkToRational Y x n ξ) := by
  let η := nativeAbsoluteExteriorStalkToOrdinary Y x n ξ
  have he : nativeAbsoluteExteriorStalkToRational Y x n ξ =
      integralStalkTopToRational x b η :=
    (LinearMap.congr_fun (integerDifferentialExteriorMap_eq_top (B := Y.functionField) b) η).trans
      (integralStalkTopToRational_native x b η).symm
  exact (integralStalkTopToRational_range x b _).mp ⟨η, he.symm⟩
end
end Red61

/-! The genuine absolute exterior sheaf stalk surjects onto ordinary
local-ring exterior differentials. Its basis-free rational image is exactly
the intrinsic integral top-form lattice. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Module
noncomputable section
variable (Y : Scheme.{0}) (x : Y) (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : Module (Y.presheaf.stalk x) ((D).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (D) x
private local instance : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x

/-- The ordinary exterior stalk realization is surjective. -/
theorem nativeAbsoluteExteriorStalkToOrdinary_surjective :
    Function.Surjective (nativeAbsoluteExteriorStalkToOrdinary Y x n) :=
  (exteriorLinearEquiv n (nativeAbsoluteDifferentialSheafStalkEquiv Y x).symm).surjective.comp
    (nativeExteriorStalkToExterior_surjective Y (D) x n)

variable [IsIntegral Y]
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

theorem nativeAbsoluteExteriorStalkToRational_eq_integral
    (b : Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))
    (ξ : (E).presheaf.stalk x) :
    nativeAbsoluteExteriorStalkToRational Y x n ξ =
      integralStalkTopToRational x b (nativeAbsoluteExteriorStalkToOrdinary Y x n ξ) :=
  (LinearMap.congr_fun (integerDifferentialExteriorMap_eq_top (B := Y.functionField) b) _).trans
    (integralStalkTopToRational_native x b _).symm

theorem nativeAbsoluteExteriorStalkToRational_range
    (b : Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))
    (ω : RationalSchemeForms Y n) :
    ω ∈ Set.range (nativeAbsoluteExteriorStalkToRational Y x n) ↔ IsIntegralStalkTopForm x ω := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact nativeAbsoluteExteriorStalkToRational_integral Y x n b ξ
  · intro h
    obtain ⟨η, hη⟩ := (integralStalkTopToRational_range x b ω).mpr h
    obtain ⟨ξ, hξ⟩ := nativeAbsoluteExteriorStalkToOrdinary_surjective Y x n η
    refine ⟨ξ, ?_⟩
    exact (nativeAbsoluteExteriorStalkToRational_eq_integral Y x n b ξ).trans
      ((congrArg (integralStalkTopToRational x b) hξ).trans hη)
end
end Red61

/-! The genuine absolute exterior stalk comparison commutes with every
specialization. Native differential specialization becomes the ordinary
differential of the actual ring map, including exterior wedge transport. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) {x y : Y} (h : x ⤳ y) (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance (z : Y) : Module (Y.presheaf.stalk z) ((D).presheaf.stalk z) :=
  schemeModuleNativeStalkModule Y (D) z
private local instance (z : Y) : Module (Y.presheaf.stalk z) ((E).presheaf.stalk z) :=
  schemeModuleNativeStalkModule Y (E) z

/-- Ordinary absolute exterior realization commutes with actual specialization. -/
theorem nativeAbsoluteExteriorStalkToOrdinary_specializes (ξ : (E).presheaf.stalk y) :
    nativeAbsoluteExteriorStalkToOrdinary Y x n
        (moduleStalkSpecializesSemilinear Y (E).val h ξ) =
      integerDifferentialExteriorMap (Y.presheaf.stalkSpecializes h).hom n
        (nativeAbsoluteExteriorStalkToOrdinary Y y n ξ) := by
  let φ := (Y.presheaf.stalkSpecializes h).hom
  let ex := (nativeAbsoluteDifferentialSheafStalkEquiv Y x).symm.toLinearMap
  let ey := (nativeAbsoluteDifferentialSheafStalkEquiv Y y).symm.toLinearMap
  have hm (v : (D).presheaf.stalk y) :
      ex (moduleStalkSpecializesSemilinear Y (D).val h v) =
        integerDifferentialSemilinear φ (ey v) := by
    have hn := nativeAbsoluteDifferentialSheafStalkEquiv_specializes Y h (ey v)
    have he : nativeAbsoluteDifferentialSheafStalkEquiv Y y (ey v) = v :=
      (nativeAbsoluteDifferentialSheafStalkEquiv Y y).apply_symm_apply v
    exact (congrArg ex ((congrArg (nativeAbsoluteDifferentialSpecializationMap Y h) he.symm).trans
      hn)).trans ((nativeAbsoluteDifferentialSheafStalkEquiv Y x).symm_apply_apply _)
  have hn := semilinearExteriorMap_natural (RingHom.id (Y.presheaf.stalk y)) φ
    (RingHom.id (Y.presheaf.stalk x)) φ φ n ey
      (moduleStalkSpecializesSemilinear Y (D).val h) ex (integerDifferentialSemilinear φ) hm
        (nativeExteriorStalkToExterior Y (D) y n ξ)
  rw [semilinearExteriorMap_linear, semilinearExteriorMap_linear] at hn
  exact (congrArg (exteriorPower.map n ex)
    (nativeExteriorStalkToExterior_specializes Y h n (D) ξ)).trans hn
end
end Red61

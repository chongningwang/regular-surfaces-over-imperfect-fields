import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Red61.AlgebraicGeometry.Modules

/-! # Stalks and restrictions of the sheaf of differentials

Formerly the modules `PresheafStalkDerivation`, `NativeDifferentialStalkCocone`, `NativeDifferentialStalkLinear`, `NativeDifferentialStalkEquiv`, `NativeAbsoluteSheafStalk`, `AffineNativeDifferentialMap`, `AffineNativeDifferentialStalk`, `AffineNativeDifferentialIso`, `NativeDifferentialRestrictionMap`, `NativeDifferentialRestrictionStalk`, `NativeDifferentialRestrictionIso`, `AffineOpenNativeDifferentials`, `NativeDifferentialSpecializes`.
-/

/-! An absolute module-presheaf derivation induces a genuine derivation on
the actual ring stalk. The Leibniz rule uses common neighborhood representatives
and the native stalk scalar action, and the germ formula is explicit. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (M : PresheafOfModulesOfCommRing.{0} Y.presheaf)
  (d : PresheafOfModulesOfCommRing.Derivation' M (schemeIntegerScalars Y))

def presheafAbsoluteStalkDerivation (x : Y) :
    letI := schemeModuleStalkModule Y M x
    Derivation ℤ (Y.presheaf.stalk x) ((modulePresheafAbPresheaf Y M).stalk x) := by
  letI := schemeModuleStalkModule Y M x
  let ds := presheafDerivationStalkAddHom Y M d x
  exact
  { toLinearMap := ds.toIntLinearMap
    map_one_eq_zero' := by
      change ds 1 = 0
      calc
        ds 1 = ds (Y.presheaf.germ ⊤ x (by trivial) (1 : Γ(Y, ⊤))) :=
          congrArg ds (map_one (Y.presheaf.germ ⊤ x (by trivial)).hom).symm
        _ = (modulePresheafAbPresheaf Y M).germ ⊤ x (by trivial) (d.d (1 : Γ(Y, ⊤))) :=
          presheafDerivationStalkAddHom_germ Y M d x ⊤ (by trivial) 1
        _ = (modulePresheafAbPresheaf Y M).germ ⊤ x (by trivial) 0 :=
          congrArg ((modulePresheafAbPresheaf Y M).germ ⊤ x (by trivial)) (d.d_one (op ⊤))
        _ = 0 := map_zero _
    leibniz' := by
      intro a b
      obtain ⟨U, hxU, s, hs⟩ := Y.presheaf.exists_germ_eq a
      obtain ⟨V, hVU, hxV, t, ht⟩ := Y.presheaf.exists_le_germ_eq b hxU
      let sV := Y.presheaf.map (homOfLE hVU).op s
      have hsV : Y.presheaf.germ V x hxV sV = a :=
        (Y.presheaf.germ_res_apply (homOfLE hVU) x hxV s).trans hs
      rw [← hsV, ← ht]
      change ds (Y.presheaf.germ V x hxV sV * Y.presheaf.germ V x hxV t) =
        Y.presheaf.germ V x hxV sV • ds (Y.presheaf.germ V x hxV t) +
          Y.presheaf.germ V x hxV t • ds (Y.presheaf.germ V x hxV sV)
      calc
        _ = ds (Y.presheaf.germ V x hxV (sV * t)) :=
          congrArg ds (map_mul (Y.presheaf.germ V x hxV).hom sV t).symm
        _ = (modulePresheafAbPresheaf Y M).germ V x hxV (d.d (sV * t)) :=
          presheafDerivationStalkAddHom_germ Y M d x V hxV (sV * t)
        _ = (modulePresheafAbPresheaf Y M).germ V x hxV (sV • d.d t + t • d.d sV) :=
          congrArg ((modulePresheafAbPresheaf Y M).germ V x hxV) (d.d_mul sV t)
        _ = _ :=
          (map_add ((modulePresheafAbPresheaf Y M).germ V x hxV).hom
            (sV • d.d t) (t • d.d sV)).trans
            ((congrArg₂ (fun u v ↦ u + v)
              (PresheafOfModules.germ_smul M x V hxV sV (d.d t))
              (PresheafOfModules.germ_smul M x V hxV t (d.d sV))).trans
                (congrArg₂ (fun u v ↦ u + v)
                  (congrArg (fun v ↦ Y.presheaf.germ V x hxV sV • v)
                    (presheafDerivationStalkAddHom_germ Y M d x V hxV t).symm)
                  (congrArg (fun v ↦ Y.presheaf.germ V x hxV t • v)
                    (presheafDerivationStalkAddHom_germ Y M d x V hxV sV).symm))) }

theorem presheafAbsoluteStalkDerivation_germ
    (x : Y) (U : Y.Opens) (hx : x ∈ U) (s : Γ(Y, U)) :
    letI := schemeModuleStalkModule Y M x
    presheafAbsoluteStalkDerivation Y M d x (Y.presheaf.germ U x hx s) =
      (modulePresheafAbPresheaf Y M).germ U x hx (d.d s) :=
  presheafDerivationStalkAddHom_germ Y M d x U hx s
end
end Red61

/-! Compatible native differential germ maps descend by the actual stalk
colimit to local-ring differentials. The resulting additive map preserves
the original germs and the induced universal stalk derivation. -/

namespace Red61
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
variable (Y : Scheme.{0}) (x : Y)
local notation "P" => nativeAbsoluteDifferentialPresheaf Y

def nativeAbsoluteDifferentialStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙ modulePresheafAbPresheaf Y (P)) where
  pt := AddCommGrpCat.of (KaehlerDifferential ℤ (Y.presheaf.stalk x))
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (nativeAbsoluteDifferentialGermMap Y x U.unop.val U.unop.property)
      naturality := by
        intro U V i
        ext ω
        change nativeAbsoluteDifferentialGermMap Y x V.unop.val V.unop.property
          ((P).map ((OpenNhds.inclusion x).map i.unop).op ω) =
          nativeAbsoluteDifferentialGermMap Y x U.unop.val U.unop.property ω
        exact nativeAbsoluteDifferentialGermMap_restrict Y x
          ((OpenNhds.inclusion x).map i.unop) V.unop.property ω }

def nativeAbsoluteDifferentialStalkToLocalMap :
    (modulePresheafAbPresheaf Y (P)).stalk x →+ KaehlerDifferential ℤ (Y.presheaf.stalk x) :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ modulePresheafAbPresheaf Y (P))
    (nativeAbsoluteDifferentialStalkCocone Y x)).hom

theorem nativeAbsoluteDifferentialStalkToLocalMap_germ
    (U : Y.Opens) (hx : x ∈ U) (ω : (P).obj (op U)) :
    nativeAbsoluteDifferentialStalkToLocalMap Y x
        ((modulePresheafAbPresheaf Y (P)).germ U x hx ω) =
      nativeAbsoluteDifferentialGermMap Y x U hx ω :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (nativeAbsoluteDifferentialStalkCocone Y x) (op ⟨U, hx⟩)) ω

theorem nativeAbsoluteDifferentialStalkToLocalMap_derivation (a : Y.presheaf.stalk x) :
    letI := schemeModuleStalkModule Y (P) x
    nativeAbsoluteDifferentialStalkToLocalMap Y x
        (presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x a) =
      KaehlerDifferential.D ℤ (Y.presheaf.stalk x) a := by
  let := schemeModuleStalkModule Y (P) x
  obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  exact (congrArg (nativeAbsoluteDifferentialStalkToLocalMap Y x)
    (presheafAbsoluteStalkDerivation_germ Y (P) (nativeAbsolutePresheafDerivation Y)
      x U hx s)).trans
        ((nativeAbsoluteDifferentialStalkToLocalMap_germ Y x U hx
          ((nativeAbsolutePresheafDerivation Y).d s)).trans
            (nativeAbsoluteDifferentialGermMap_D Y x U hx s))
end
end Red61

/-! The native stalk comparison with local-ring differentials is linear
for the actual stalk ring action. The forward map is induced by the
universal stalk derivation, and one inverse identity holds on every derivative. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (x : Y)
local notation "P" => nativeAbsoluteDifferentialPresheaf Y
local notation "A" => modulePresheafAbPresheaf Y (nativeAbsoluteDifferentialPresheaf Y)

theorem nativeAbsoluteDifferentialStalkToLocalMap_smul
    (a : Y.presheaf.stalk x) (ω : (A).stalk x) :
    letI := schemeModuleStalkModule Y (P) x
    nativeAbsoluteDifferentialStalkToLocalMap Y x (a • ω) =
      a • nativeAbsoluteDifferentialStalkToLocalMap Y x ω := by
  let := schemeModuleStalkModule Y (P) x
  obtain ⟨U, hxU, r, hr⟩ := Y.presheaf.exists_germ_eq a
  obtain ⟨W, hWU, hxW, η, hη⟩ := (A).exists_le_germ_eq ω hxU
  let η₀ : (P).obj (op W) := η
  have hη₀ : (A).germ W x hxW η₀ = ω := hη
  let rW := Y.presheaf.map (homOfLE hWU).op r
  have hrW : Y.presheaf.germ W x hxW rW = a :=
    (Y.presheaf.germ_res_apply (homOfLE hWU) x hxW r).trans hr
  rw [← hrW, ← hη₀]
  calc
    _ = nativeAbsoluteDifferentialStalkToLocalMap Y x ((A).germ W x hxW (rW • η₀)) :=
      congrArg (nativeAbsoluteDifferentialStalkToLocalMap Y x)
        (PresheafOfModules.germ_smul (P) x W hxW rW η₀).symm
    _ = nativeAbsoluteDifferentialGermMap Y x W hxW (rW • η₀) :=
      nativeAbsoluteDifferentialStalkToLocalMap_germ Y x W hxW (rW • η₀)
    _ = Y.presheaf.germ W x hxW rW • nativeAbsoluteDifferentialGermMap Y x W hxW η₀ :=
      nativeAbsoluteDifferentialGermMap_smul Y x W hxW rW η₀
    _ = _ := congrArg (fun v ↦ Y.presheaf.germ W x hxW rW • v)
      (nativeAbsoluteDifferentialStalkToLocalMap_germ Y x W hxW η₀).symm

def nativeAbsoluteDifferentialStalkToLocalLinear :
    letI := schemeModuleStalkModule Y (P) x
    (A).stalk x →ₗ[Y.presheaf.stalk x] KaehlerDifferential ℤ (Y.presheaf.stalk x) := by
  letI := schemeModuleStalkModule Y (P) x
  exact
    { toFun := nativeAbsoluteDifferentialStalkToLocalMap Y x
      map_add' := map_add _
      map_smul' := nativeAbsoluteDifferentialStalkToLocalMap_smul Y x }

def nativeAbsoluteDifferentialLocalToStalkLinear :
    letI := schemeModuleStalkModule Y (P) x
    KaehlerDifferential ℤ (Y.presheaf.stalk x) →ₗ[Y.presheaf.stalk x] (A).stalk x := by
  letI := schemeModuleStalkModule Y (P) x
  exact Derivation.liftKaehlerDifferential
    (presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x)

theorem nativeAbsoluteDifferentialStalkToLocal_comp_localToStalk :
    letI := schemeModuleStalkModule Y (P) x
    (nativeAbsoluteDifferentialStalkToLocalLinear Y x).comp
        (nativeAbsoluteDifferentialLocalToStalkLinear Y x) = LinearMap.id := by
  let := schemeModuleStalkModule Y (P) x
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change nativeAbsoluteDifferentialStalkToLocalMap Y x
    (nativeAbsoluteDifferentialLocalToStalkLinear Y x
      (KaehlerDifferential.D ℤ (Y.presheaf.stalk x) a)) = KaehlerDifferential.D ℤ _ a
  exact (congrArg (nativeAbsoluteDifferentialStalkToLocalMap Y x)
    (Derivation.liftKaehlerDifferential_comp_D
      (presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x) a)).trans
        (nativeAbsoluteDifferentialStalkToLocalMap_derivation Y x a)
end
end Red61

/-! The native absolute differential presheaf stalk is canonically
isomorphic over the actual local ring to its ordinary Kähler module.
Both inverse identities, universal derivatives and inverse germ formulas are proved. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (x : Y)
local notation "P" => nativeAbsoluteDifferentialPresheaf Y
local notation "A" => modulePresheafAbPresheaf Y (nativeAbsoluteDifferentialPresheaf Y)

theorem nativeAbsoluteDifferentialLocalToStalk_germMap
    (U : Y.Opens) (hx : x ∈ U) (ω : (P).obj (op U)) :
    letI := schemeModuleStalkModule Y (P) x
    nativeAbsoluteDifferentialLocalToStalkLinear Y x
        (nativeAbsoluteDifferentialGermMap Y x U hx ω) = (A).germ U x hx ω := by
  let := schemeModuleStalkModule Y (P) x
  let := Module.compHom ((A).stalk x) (Y.presheaf.germ U x hx).hom
  let φ := nativeAbsoluteDifferentialLocalToStalkLinear Y x
  let f₁ : (P).obj (op U) →ₗ[Γ(Y, U)] (A).stalk x :=
    { toFun := fun η ↦ φ (nativeAbsoluteDifferentialGermMap Y x U hx η)
      map_add' := by
        intro η θ
        exact (congrArg φ (map_add (nativeAbsoluteDifferentialGermMap Y x U hx) η θ)).trans
          (φ.map_add _ _)
      map_smul' := by
        intro a η
        exact (congrArg φ (nativeAbsoluteDifferentialGermMap_smul Y x U hx a η)).trans
          (φ.map_smul _ _) }
  let f₂ : (P).obj (op U) →ₗ[Γ(Y, U)] (A).stalk x :=
    { toFun := (A).germ U x hx
      map_add' := (A).germ U x hx |>.hom.map_add
      map_smul' := PresheafOfModules.germ_smul (P) x U hx }
  have he : ModuleCat.ofHom f₁ = ModuleCat.ofHom f₂ := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change φ (nativeAbsoluteDifferentialGermMap Y x U hx
      (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a)) =
      (A).germ U x hx
        (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a)
    exact (congrArg φ (nativeAbsoluteDifferentialGermMap_D Y x U hx a)).trans
      ((Derivation.liftKaehlerDifferential_comp_D
        (presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x)
          (Y.presheaf.germ U x hx a)).trans
            (presheafAbsoluteStalkDerivation_germ Y (P) (nativeAbsolutePresheafDerivation Y)
              x U hx a))
  exact ConcreteCategory.congr_hom he ω

theorem nativeAbsoluteDifferentialLocalToStalk_comp_stalkToLocal :
    letI := schemeModuleStalkModule Y (P) x
    (nativeAbsoluteDifferentialLocalToStalkLinear Y x).comp
        (nativeAbsoluteDifferentialStalkToLocalLinear Y x) = LinearMap.id := by
  let := schemeModuleStalkModule Y (P) x
  apply LinearMap.ext
  intro ω
  obtain ⟨U, hx, η, rfl⟩ := (A).exists_germ_eq ω
  change nativeAbsoluteDifferentialLocalToStalkLinear Y x
    (nativeAbsoluteDifferentialStalkToLocalMap Y x ((A).germ U x hx η)) =
    (A).germ U x hx η
  exact (congrArg (nativeAbsoluteDifferentialLocalToStalkLinear Y x)
    (nativeAbsoluteDifferentialStalkToLocalMap_germ Y x U hx η)).trans
      (nativeAbsoluteDifferentialLocalToStalk_germMap Y x U hx η)

def nativeAbsoluteDifferentialPresheafStalkEquiv :
    letI := schemeModuleStalkModule Y (P) x
    KaehlerDifferential ℤ (Y.presheaf.stalk x) ≃ₗ[Y.presheaf.stalk x] (A).stalk x := by
  letI := schemeModuleStalkModule Y (P) x
  exact
    { nativeAbsoluteDifferentialLocalToStalkLinear Y x with
      invFun := nativeAbsoluteDifferentialStalkToLocalLinear Y x
      left_inv := fun ω ↦ DFunLike.congr_fun
        (nativeAbsoluteDifferentialStalkToLocal_comp_localToStalk Y x) ω
      right_inv := fun η ↦ DFunLike.congr_fun
        (nativeAbsoluteDifferentialLocalToStalk_comp_stalkToLocal Y x) η }

theorem nativeAbsoluteDifferentialPresheafStalkEquiv_D (a : Y.presheaf.stalk x) :
    letI := schemeModuleStalkModule Y (P) x
    nativeAbsoluteDifferentialPresheafStalkEquiv Y x
        (KaehlerDifferential.D ℤ (Y.presheaf.stalk x) a) =
      presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x a :=
  Derivation.liftKaehlerDifferential_comp_D
    (presheafAbsoluteStalkDerivation Y (P) (nativeAbsolutePresheafDerivation Y) x) a

end
end Red61

/-! The actual global absolute differential sheaf has the ordinary
local-ring Kähler module as every native stalk, with the native scalar action.
The equivalence preserves universal derivative germs and inverse unit germs. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (x : Y)
local notation "P" => nativeAbsoluteDifferentialPresheaf Y
local notation "N" => nativeAbsoluteDifferentialModule Y

def nativeAbsoluteDifferentialSheafStalkEquiv :
    letI := schemeModuleNativeStalkModule Y (N) x
    KaehlerDifferential ℤ (Y.presheaf.stalk x) ≃ₗ[Y.presheaf.stalk x] (N).presheaf.stalk x := by
  letI := schemeModuleStalkModule Y (P) x
  letI := schemeModuleNativeStalkModule Y (N) x
  exact (nativeAbsoluteDifferentialPresheafStalkEquiv Y x).trans
    (modulePresheafSheafificationStalkEquiv Y (P) x)

theorem nativeAbsoluteDifferentialSheafStalkEquiv_D_germ
    (U : Y.Opens) (hx : x ∈ U) (s : Γ(Y, U)) :
    letI := schemeModuleNativeStalkModule Y (N) x
    nativeAbsoluteDifferentialSheafStalkEquiv Y x
        (KaehlerDifferential.D ℤ (Y.presheaf.stalk x) (Y.presheaf.germ U x hx s)) =
      (N).presheaf.germ U x hx ((nativeAbsoluteSheafDerivation Y).d s) := by
  let := schemeModuleStalkModule Y (P) x
  let := schemeModuleNativeStalkModule Y (N) x
  let e₁ := modulePresheafSheafificationStalkEquiv Y (P) x
  change e₁ (nativeAbsoluteDifferentialPresheafStalkEquiv Y x
    (KaehlerDifferential.D ℤ (Y.presheaf.stalk x) (Y.presheaf.germ U x hx s))) = _
  exact (congrArg e₁ ((nativeAbsoluteDifferentialPresheafStalkEquiv_D Y x
    (Y.presheaf.germ U x hx s)).trans
      (presheafAbsoluteStalkDerivation_germ Y (P) (nativeAbsolutePresheafDerivation Y)
        x U hx s))).trans
          (modulePresheafSheafificationStalkEquiv_germ Y (P) x U hx
            ((nativeAbsolutePresheafDerivation Y).d s))

end
end Red61

/-! On an affine scheme the native global absolute differential sheaf receives
the tilde sheaf of the ordinary differential module. The map is defined using
the actual universal derivative and tilde-Gamma adjunction, with section formulas. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (A : CommRingCat.{0})
local notation "Y" => Spec A
local notation "N" => nativeAbsoluteDifferentialModule (Spec A)

def affineNativeAbsoluteDerivation :
    Derivation ℤ A (moduleSpecΓFunctor.obj (N)) where
  toLinearMap :=
    (((nativeAbsoluteSheafDerivation (Y)).d (X := op ⊤)).comp
      (Scheme.ΓSpecIso A).inv.hom.toAddMonoidHom).toIntLinearMap
  map_one_eq_zero' := by
    change (nativeAbsoluteSheafDerivation (Y)).d ((Scheme.ΓSpecIso A).inv.hom 1) = 0
    rw [map_one]
    exact (nativeAbsoluteSheafDerivation (Y)).d_one (op ⊤)
  leibniz' a b := by
    change (nativeAbsoluteSheafDerivation (Y)).d
      ((Scheme.ΓSpecIso A).inv.hom (a * b)) = _
    rw [map_mul]
    exact (nativeAbsoluteSheafDerivation (Y)).d_mul _ _

def affineNativeAbsoluteDifferentialMap :
    tilde (ModuleCat.of A (KaehlerDifferential ℤ A)) ⟶ (N) :=
  tilde.map (ModuleCat.ofHom (affineNativeAbsoluteDerivation A).liftKaehlerDifferential) ≫
    (N).fromTildeΓ

theorem affineNativeAbsoluteDifferentialMap_toOpen (U : (Y).Opens)
    (ω : KaehlerDifferential ℤ A) :
    (affineNativeAbsoluteDifferentialMap A).app U
        (tilde.toOpen (ModuleCat.of A (KaehlerDifferential ℤ A)) U ω) =
      (N).presheaf.map U.leTop.op
        ((affineNativeAbsoluteDerivation A).liftKaehlerDifferential ω) := by
  have hg := ConcreteCategory.congr_hom (tilde.toOpen_map_app
    (ModuleCat.ofHom (affineNativeAbsoluteDerivation A).liftKaehlerDifferential) U) ω
  have hc := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app (N) U)
      ((affineNativeAbsoluteDerivation A).liftKaehlerDifferential ω)
  exact (congrArg ((N).fromTildeΓ.app U) hg).trans hc

theorem affineNativeAbsoluteDifferentialMap_D (U : (Y).Opens) (a : A) :
    (affineNativeAbsoluteDifferentialMap A).app U
        (tilde.toOpen (ModuleCat.of A (KaehlerDifferential ℤ A)) U
          (KaehlerDifferential.D ℤ A a)) =
      (nativeAbsoluteSheafDerivation (Y)).d
        ((Y).presheaf.map U.leTop.op ((Scheme.ΓSpecIso A).inv a)) := by
  refine (affineNativeAbsoluteDifferentialMap_toOpen A U _).trans ?_
  have h := Derivation.liftKaehlerDifferential_comp_D (affineNativeAbsoluteDerivation A) a
  exact (congrArg ((N).presheaf.map U.leTop.op) h).trans
    ((nativeAbsoluteSheafDerivation (Y)).d_map U.leTop.op
      ((Scheme.ΓSpecIso A).inv a)).symm
end
end Red61

/-! The actual affine differential-sheaf comparison is bijective on every
native stalk. Under the derivative-preserving stalk equivalence it is the
ordinary localization map of Kähler modules, with the native affine stalk scalars. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : CommRingCat.{0}) (x : PrimeSpectrum.Top A)
local notation "Y" => Spec A
local notation "N" => nativeAbsoluteDifferentialModule (Spec A)
local notation "T" => tilde (ModuleCat.of A (KaehlerDifferential ℤ A))
set_option quotPrecheck false in
local notation "B" => ↑((Spec A).presheaf.stalk x)

local instance specStalkAlgebra : Algebra A (B) := (StructureSheaf.toStalk A x).hom.toAlgebra

def affineNativeAbsoluteDifferentialStalkMap :
    letI := schemeModuleNativeStalkModule (Y) (N) x
    letI : Module A ((N).presheaf.stalk x) :=
      Module.compHom (R := (B)) _ (StructureSheaf.toStalk A x).hom
    (T).presheaf.stalk x →ₗ[A] (N).presheaf.stalk x := by
  letI := schemeModuleNativeStalkModule (Y) (T) x
  letI := schemeModuleNativeStalkModule (Y) (N) x
  letI : Module A ((N).presheaf.stalk x) :=
    Module.compHom (R := (B)) _ (StructureSheaf.toStalk A x).hom
  exact
    { __ := modulePresheafStalkMapAddHom (Y) (T).val (N).val
        (affineNativeAbsoluteDifferentialMap A).val x
      map_smul' a m := (modulePresheafStalkLinearMap (Y) (T).val (N).val
        (affineNativeAbsoluteDifferentialMap A).val x).map_smul
          (StructureSheaf.toStalk A x a) m }

theorem affineNativeAbsoluteDifferentialStalkMap_D (a : A) :
    affineNativeAbsoluteDifferentialStalkMap A x
        (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x
          (KaehlerDifferential.D ℤ A a)) =
      (N).presheaf.germ ⊤ x (by simp)
        ((nativeAbsoluteSheafDerivation (Y)).d ((Scheme.ΓSpecIso A).inv a)) := by
  have hg := modulePresheafStalkMapAddHom_germ (Y) (T).val (N).val
    (affineNativeAbsoluteDifferentialMap A).val x ⊤ (by simp)
      (tilde.toOpen (ModuleCat.of A (KaehlerDifferential ℤ A)) ⊤
        (KaehlerDifferential.D ℤ A a))
  have hi : (⊤ : (Y).Opens).leTop.op = 𝟙 (op (⊤ : (Y).Opens)) :=
    Subsingleton.elim _ _
  have hd := affineNativeAbsoluteDifferentialMap_D A ⊤ a
  rw [hi] at hd
  have hm := ConcreteCategory.congr_hom ((Y).presheaf.map_id (op ⊤))
    ((Scheme.ΓSpecIso A).inv a)
  exact hg.trans (congrArg ((N).presheaf.germ ⊤ x (by simp))
    (hd.trans (congrArg (nativeAbsoluteSheafDerivation (Y)).d hm)))

def affineNativeAbsoluteDifferentialStalkToKaehler :
    (T).presheaf.stalk x →ₗ[A] KaehlerDifferential ℤ (B) := by
  letI := schemeModuleNativeStalkModule (Y) (N) x
  letI : Module A ((N).presheaf.stalk x) :=
    Module.compHom (R := (B)) _ (StructureSheaf.toStalk A x).hom
  letI : IsScalarTower A (B) ((N).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact ((nativeAbsoluteDifferentialSheafStalkEquiv (Y) x).symm.restrictScalars A).toLinearMap.comp
    (affineNativeAbsoluteDifferentialStalkMap A x)

theorem affineNativeAbsoluteDifferentialStalkToKaehler_D (a : A) :
    affineNativeAbsoluteDifferentialStalkToKaehler A x
        (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x
          (KaehlerDifferential.D ℤ A a)) =
      KaehlerDifferential.D ℤ (B) (algebraMap A (B) a) := by
  let := schemeModuleNativeStalkModule (Y) (N) x
  change (nativeAbsoluteDifferentialSheafStalkEquiv (Y) x).symm
    (affineNativeAbsoluteDifferentialStalkMap A x
      (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x
        (KaehlerDifferential.D ℤ A a))) = _
  rw [affineNativeAbsoluteDifferentialStalkMap_D]
  have hd := nativeAbsoluteDifferentialSheafStalkEquiv_D_germ (Y) x ⊤ (by simp)
    ((Scheme.ΓSpecIso A).inv a)
  exact (congrArg (nativeAbsoluteDifferentialSheafStalkEquiv (Y) x).symm hd.symm).trans
    ((nativeAbsoluteDifferentialSheafStalkEquiv (Y) x).symm_apply_apply _)

theorem affineNativeAbsoluteDifferentialStalkToKaehler_comp :
    (affineNativeAbsoluteDifferentialStalkToKaehler A x).comp
        (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x).hom =
      KaehlerDifferential.map ℤ ℤ A (B) := by
  ext a
  exact (affineNativeAbsoluteDifferentialStalkToKaehler_D A x a).trans
    (KaehlerDifferential.map_D ℤ ℤ A (B) a).symm

theorem affineNativeAbsoluteDifferentialStalkToKaehler_bijective :
    Function.Bijective (affineNativeAbsoluteDifferentialStalkToKaehler A x) := by
  let : IsLocalization.AtPrime (B) x.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((structurePresheafInCommRingCat A).stalk x) x.asIdeal)
  let f := affineNativeAbsoluteDifferentialStalkToKaehler A x
  let t := (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x).hom
  have : IsLocalizedModule x.asIdeal.primeCompl t := by
    exact inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ A (KaehlerDifferential ℤ A) x))
  have : IsLocalizedModule x.asIdeal.primeCompl (f.comp t) := by
    change IsLocalizedModule x.asIdeal.primeCompl
      ((affineNativeAbsoluteDifferentialStalkToKaehler A x).comp
        (tilde.toStalk (ModuleCat.of A (KaehlerDifferential ℤ A)) x).hom)
    rw [affineNativeAbsoluteDifferentialStalkToKaehler_comp]
    infer_instance
  have he := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp
    x.asIdeal.primeCompl t f
  have hb := (IsLocalizedModule.linearEquiv x.asIdeal.primeCompl t (f.comp t)).bijective
  change Function.Bijective (IsLocalizedModule.linearEquiv
    x.asIdeal.primeCompl t (f.comp t)).toLinearMap at hb
  rw [he] at hb
  exact hb

theorem affineNativeAbsoluteDifferentialStalkMap_bijective :
    Function.Bijective (affineNativeAbsoluteDifferentialStalkMap A x) := by
  let := schemeModuleNativeStalkModule (Y) (N) x
  exact Function.Bijective.of_comp_iff'
    (nativeAbsoluteDifferentialSheafStalkEquiv (Y) x).symm.bijective
    (affineNativeAbsoluteDifferentialStalkMap A x) |>.mp
      (affineNativeAbsoluteDifferentialStalkToKaehler_bijective A x)
end
end Red61

/-! The native absolute differential sheaf on an affine scheme is canonically
the tilde sheaf of its ordinary absolute differential module. The isomorphism
preserves derivative sections and proves native quasicoherence. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (A : CommRingCat.{0})

theorem affineNativeAbsoluteDifferentialMap_isIso :
    IsIso (affineNativeAbsoluteDifferentialMap A) :=
  schemeModule_isIso_of_stalk_bijective (Spec A)
    (affineNativeAbsoluteDifferentialMap A)
      (affineNativeAbsoluteDifferentialStalkMap_bijective A)

def affineNativeAbsoluteDifferentialIso :
    tilde (ModuleCat.of A (KaehlerDifferential ℤ A)) ≅
      nativeAbsoluteDifferentialModule (Spec A) := by
  have := affineNativeAbsoluteDifferentialMap_isIso A
  exact asIso (affineNativeAbsoluteDifferentialMap A)

end
end Red61

/-! Absolute sheaf derivations restrict along native open immersions.
The resulting actual map from absolute differentials to the restricted
absolute differential sheaf preserves every derivative section. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
  (M : Y.Modules)

def restrictAbsoluteSheafDerivation
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (schemeIntegerScalars Y)) :
    PresheafOfModulesOfCommRing.Derivation' (M.restrict f).val (schemeIntegerScalars X) where
  d {U} := (d.d (X := op (f ''ᵁ U.unop))).comp (f.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d ((f.appIso U.unop).inv.hom (a * b)) = _
    rw [map_mul]
    exact d.d_mul _ _
  d_map {U V} i a := by
    have h := ConcreteCategory.congr_hom (f.appIso_inv_naturality i) a
    change d.d ((f.appIso V.unop).inv.hom (X.presheaf.map i a)) = _
    exact (congrArg d.d h).trans (d.d_map (f.opensFunctor.op.map i) _)
  d_app {U} a := by
    change d.d ((f.appIso U.unop).inv.hom ((show ℤ from a) : Γ(X, U.unop))) = 0
    rw [map_intCast]
    exact d.d_app (X := op (f ''ᵁ U.unop)) a

def nativeAbsoluteDifferentialRestrictionMap :
    nativeAbsoluteDifferentialModule X ⟶ (nativeAbsoluteDifferentialModule Y).restrict f :=
  (nativeAbsoluteDifferentialHomEquiv X _).symm
    (restrictAbsoluteSheafDerivation f _ (nativeAbsoluteSheafDerivation Y))

theorem nativeAbsoluteDifferentialRestrictionMap_D
    (U : X.Opensᵒᵖ) (a : Γ(X, U.unop)) :
    (nativeAbsoluteDifferentialRestrictionMap f).val.app U
        ((nativeAbsoluteSheafDerivation X).d a) =
      (nativeAbsoluteSheafDerivation Y).d ((f.appIso U.unop).inv a) := by
  have h := (nativeAbsoluteDifferentialHomEquiv_apply X _
    (nativeAbsoluteDifferentialRestrictionMap f)).symm.trans
      (Equiv.apply_symm_apply (nativeAbsoluteDifferentialHomEquiv X _) _)
  exact PresheafOfModulesOfCommRing.Derivation.congr_d h a
end
end Red61

/-! Under native derivative-preserving stalk equivalences, the actual absolute
differential restriction map is the ordinary Kähler map induced by the inverse
stalk-ring isomorphism of the open immersion. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
local notation "NX" => nativeAbsoluteDifferentialModule X
local notation "NY" => nativeAbsoluteDifferentialModule Y
set_option quotPrecheck false in
local notation "A" => ↑(X.presheaf.stalk x)
set_option quotPrecheck false in
local notation "B" => ↑(Y.presheaf.stalk (f x))
local instance restrictionStalkAlgebra : Algebra (A) (B) := (inv (f.stalkMap x)).hom.toAlgebra

def nativeAbsoluteRestrictionStalkToKaehler :
    KaehlerDifferential ℤ (A) →ₗ[A] KaehlerDifferential ℤ (B) := by
  letI := schemeModuleNativeStalkModule X (NX) x
  letI := schemeModuleNativeStalkModule X ((NY).restrict f) x
  letI := schemeModuleNativeStalkModule Y (NY) (f x)
  letI := openImmersionTargetStalkModule f x (NY)
  letI : IsScalarTower (A) (B) ((NY).presheaf.stalk (f x)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact ((nativeAbsoluteDifferentialSheafStalkEquiv Y (f x)).symm.restrictScalars
    (A)).toLinearMap.comp
    ((restrictModuleStalkLinearEquiv f x (NY)).toLinearMap.comp
      ((modulePresheafStalkLinearMap X (NX).val ((NY).restrict f).val
        (nativeAbsoluteDifferentialRestrictionMap f).val x).comp
          (nativeAbsoluteDifferentialSheafStalkEquiv X x).toLinearMap))

theorem nativeAbsoluteRestrictionStalkToKaehler_D_germ
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    nativeAbsoluteRestrictionStalkToKaehler f x
        (KaehlerDifferential.D ℤ (A) (X.presheaf.germ U x hx a)) =
      KaehlerDifferential.D ℤ (B)
        (inv (f.stalkMap x) (X.presheaf.germ U x hx a)) := by
  let := schemeModuleNativeStalkModule X (NX) x
  let := schemeModuleNativeStalkModule X ((NY).restrict f) x
  let := schemeModuleNativeStalkModule Y (NY) (f x)
  let := openImmersionTargetStalkModule f x (NY)
  let eX := nativeAbsoluteDifferentialSheafStalkEquiv X x
  let eY := nativeAbsoluteDifferentialSheafStalkEquiv Y (f x)
  let eR := restrictModuleStalkLinearEquiv f x (NY)
  let m := modulePresheafStalkLinearMap X (NX).val ((NY).restrict f).val
    (nativeAbsoluteDifferentialRestrictionMap f).val x
  change eY.symm (eR (m (eX (KaehlerDifferential.D ℤ (A)
    (X.presheaf.germ U x hx a))))) = _
  have hX := nativeAbsoluteDifferentialSheafStalkEquiv_D_germ X x U hx a
  have hm := modulePresheafStalkLinearMap_germ X (NX).val ((NY).restrict f).val
    (nativeAbsoluteDifferentialRestrictionMap f).val x U hx
      ((nativeAbsoluteSheafDerivation X).d a)
  have hd := nativeAbsoluteDifferentialRestrictionMap_D f (op U) a
  have hR := restrictModuleStalkAddEquiv_germ f x (NY) U hx
    ((nativeAbsoluteSheafDerivation Y).d ((f.appIso U).inv a))
  have hY := nativeAbsoluteDifferentialSheafStalkEquiv_D_germ Y (f x)
    (f ''ᵁ U) ⟨x, hx, rfl⟩ ((f.appIso U).inv a)
  calc
    _ = eY.symm (eR (m ((NX).presheaf.germ U x hx
        ((nativeAbsoluteSheafDerivation X).d a)))) := congrArg (fun v ↦ eY.symm (eR (m v))) hX
    _ = eY.symm (eR (((NY).restrict f).presheaf.germ U x hx
        ((nativeAbsoluteDifferentialRestrictionMap f).val.app (op U)
          ((nativeAbsoluteSheafDerivation X).d a)))) := congrArg (fun v ↦ eY.symm (eR v)) hm
    _ = eY.symm (eR (((NY).restrict f).presheaf.germ U x hx
        ((nativeAbsoluteSheafDerivation Y).d ((f.appIso U).inv a)))) :=
      congrArg (fun v ↦ eY.symm (eR (((NY).restrict f).presheaf.germ U x hx v))) hd
    _ = eY.symm ((NY).presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩
        ((nativeAbsoluteSheafDerivation Y).d ((f.appIso U).inv a))) := congrArg eY.symm hR
    _ = KaehlerDifferential.D ℤ (B)
        (Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((f.appIso U).inv a)) :=
      (congrArg eY.symm hY.symm).trans (eY.symm_apply_apply _)
    _ = _ := congrArg (KaehlerDifferential.D ℤ (B))
      (openImmersion_inverseStalkMap_germ f x U hx a).symm

theorem nativeAbsoluteRestrictionStalkToKaehler_eq :
    nativeAbsoluteRestrictionStalkToKaehler f x = KaehlerDifferential.map ℤ ℤ (A) (B) := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  exact (nativeAbsoluteRestrictionStalkToKaehler_D_germ f x U hx s).trans
    (KaehlerDifferential.map_D ℤ ℤ (A) (B) _).symm
end
end Red61

/-! Absolute Kähler differential sheaves commute with restriction along
open immersions. The actual restriction morphism is an isomorphism by its
ordinary local-ring differential comparison, and preserves derivative sections. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem nativeAbsoluteDifferentialRestrictionStalk_bijective (x : X) :
    Function.Bijective (modulePresheafStalkMapAddHom X
      (nativeAbsoluteDifferentialModule X).val
      ((nativeAbsoluteDifferentialModule Y).restrict f).val
      (nativeAbsoluteDifferentialRestrictionMap f).val x) := by
  let := (inv (f.stalkMap x)).hom.toAlgebra
  let := schemeModuleNativeStalkModule X (nativeAbsoluteDifferentialModule X) x
  let := schemeModuleNativeStalkModule X
    ((nativeAbsoluteDifferentialModule Y).restrict f) x
  let := schemeModuleNativeStalkModule Y (nativeAbsoluteDifferentialModule Y) (f x)
  let := openImmersionTargetStalkModule f x (nativeAbsoluteDifferentialModule Y)
  let eX := nativeAbsoluteDifferentialSheafStalkEquiv X x
  let eY := nativeAbsoluteDifferentialSheafStalkEquiv Y (f x)
  let eR := restrictModuleStalkLinearEquiv f x (nativeAbsoluteDifferentialModule Y)
  let m := modulePresheafStalkLinearMap X (nativeAbsoluteDifferentialModule X).val
    ((nativeAbsoluteDifferentialModule Y).restrict f).val
      (nativeAbsoluteDifferentialRestrictionMap f).val x
  have hK : Function.Bijective (nativeAbsoluteRestrictionStalkToKaehler f x) := by
    rw [nativeAbsoluteRestrictionStalkToKaehler_eq]
    exact kaehlerMap_bijective_of_bijective_algebraMap ℤ
      (X.presheaf.stalk x) (Y.presheaf.stalk (f x))
        (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm.bijective
  have h : Function.Bijective (fun ω ↦ eY.symm (eR (m (eX ω)))) := hK
  have h₁ : Function.Bijective (fun ω ↦ eR (m (eX ω))) :=
    h.of_comp_left eY.symm.injective
  have h₂ : Function.Bijective (fun ω ↦ m (eX ω)) := h₁.of_comp_left eR.injective
  exact (Function.Bijective.of_comp_iff m eX.bijective).mp h₂

theorem nativeAbsoluteDifferentialRestrictionMap_isIso :
    IsIso (nativeAbsoluteDifferentialRestrictionMap f) :=
  schemeModule_isIso_of_stalk_bijective X (nativeAbsoluteDifferentialRestrictionMap f)
    (nativeAbsoluteDifferentialRestrictionStalk_bijective f)

def nativeAbsoluteDifferentialRestrictionIso :
    nativeAbsoluteDifferentialModule X ≅ (nativeAbsoluteDifferentialModule Y).restrict f := by
  have := nativeAbsoluteDifferentialRestrictionMap_isIso f
  exact asIso (nativeAbsoluteDifferentialRestrictionMap f)

end
end Red61

/-! On every affine open the genuine absolute differential sheaf is the
ordinary tilde differential sheaf. A displayed Kähler basis gives an actual
free sheaf frame, and the affine comparison preserves derivative sections. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
variable {Y : Scheme.{0}} {A : CommRingCat.{0}} (f : Spec A ⟶ Y) [IsOpenImmersion f]

def affineOpenNativeAbsoluteDifferentialIso :
    tilde (ModuleCat.of A (KaehlerDifferential ℤ A)) ≅
      (nativeAbsoluteDifferentialModule Y).restrict f :=
  affineNativeAbsoluteDifferentialIso A ≪≫ nativeAbsoluteDifferentialRestrictionIso f

def affineOpenNativeAbsoluteDifferentialFrame {I : Type}
    (b : Basis I A (KaehlerDifferential ℤ A)) :
    SheafOfModules.free (R := (Spec A).ringCatSheaf) I ≅
      (nativeAbsoluteDifferentialModule Y).restrict f :=
  (tildeFinsupp I).symm ≪≫ (tilde.functor A).mapIso b.repr.symm.toModuleIso ≪≫
    affineOpenNativeAbsoluteDifferentialIso f

end
end Red61

/-! Native absolute differential stalk comparisons commute with every
specialization. The square uses actual module and ring specialization maps,
and the ordinary integer differential of that ring homomorphism. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
variable (Y : Scheme.{0}) {x y : Y} (h : x ⤳ y)
local notation "N" => nativeAbsoluteDifferentialModule Y
private local instance (z : Y) : Module (Y.presheaf.stalk z) ((N).presheaf.stalk z) :=
  schemeModuleNativeStalkModule Y (N) z

/-- The actual specialization of the native absolute differential sheaf. -/
def nativeAbsoluteDifferentialSpecializationMap :
    (N).presheaf.stalk y →ₛₗ[(Y.presheaf.stalkSpecializes h).hom] (N).presheaf.stalk x :=
  moduleStalkSpecializesSemilinear Y (N).val h

/-- The native local-ring differential comparison commutes with specialization. -/
theorem nativeAbsoluteDifferentialSheafStalkEquiv_specializes
    (ω : KaehlerDifferential ℤ (Y.presheaf.stalk y)) :
    nativeAbsoluteDifferentialSpecializationMap Y h
        (nativeAbsoluteDifferentialSheafStalkEquiv Y y ω) =
      nativeAbsoluteDifferentialSheafStalkEquiv Y x
        (integerDifferentialSemilinear (Y.presheaf.stalkSpecializes h).hom ω) := by
  let f := (nativeAbsoluteDifferentialSpecializationMap Y h).comp
    (nativeAbsoluteDifferentialSheafStalkEquiv Y y).toLinearMap
  let g := (nativeAbsoluteDifferentialSheafStalkEquiv Y x).toLinearMap.comp
    (integerDifferentialSemilinear (Y.presheaf.stalkSpecializes h).hom)
  have he : f = g := by
    apply integerDifferential_semilinear_ext
    intro a
    obtain ⟨U, hy, r, rfl⟩ := Y.presheaf.exists_germ_eq a
    change nativeAbsoluteDifferentialSpecializationMap Y h
      (nativeAbsoluteDifferentialSheafStalkEquiv Y y
        (KaehlerDifferential.D ℤ (Y.presheaf.stalk y) (Y.presheaf.germ U y hy r))) = _
    have hyD := nativeAbsoluteDifferentialSheafStalkEquiv_D_germ Y y U hy r
    have hs := moduleStalkSpecializesSemilinear_germ Y (N).val h U hy
      ((nativeAbsoluteSheafDerivation Y).d r)
    have hr := ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hy h) r
    have hd := integerDifferentialSemilinear_D (Y.presheaf.stalkSpecializes h).hom
      (Y.presheaf.germ U y hy r)
    exact (congrArg (nativeAbsoluteDifferentialSpecializationMap Y h) hyD).trans
      (hs.trans ((nativeAbsoluteDifferentialSheafStalkEquiv_D_germ Y x U
        (h.mem_open U.isOpen hy) r).symm.trans
          (congrArg (nativeAbsoluteDifferentialSheafStalkEquiv Y x)
            ((congrArg (KaehlerDifferential.D ℤ (Y.presheaf.stalk x)) hr.symm).trans hd.symm))))
  exact LinearMap.congr_fun he ω
end
end Red61

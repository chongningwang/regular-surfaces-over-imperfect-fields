import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Red61.RingTheory.Kaehler

/-! # The sheaf of absolute differentials

Formerly the modules `NativeUniversalDifferentialSheaf`, `NativeAbsoluteDifferentialSheaf`, `NativeAbsoluteDifferentialSections`, `NativeDifferentialGermMap`, `NativeDifferentialGermNaturality`.
-/

/-! A morphism of ring presheaves on a scheme defines a genuine differential
module sheaf by mathlib’s native construction and sheafification. Its universal
property is the actual postcomposition bijection for derivations into sheaves. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
noncomputable section
variable (Y : Scheme.{0}) {T : Y.Opensᵒᵖ ⥤ CommRingCat} (φ : T ⟶ Y.presheaf)

def nativeDifferentialPresheaf : PresheafOfModulesOfCommRing Y.presheaf :=
  DifferentialsConstruction.relativeDifferentials' φ

def nativePresheafDerivation :
    (nativeDifferentialPresheaf Y φ).Derivation' φ :=
  DifferentialsConstruction.derivation' φ

def nativePresheafDerivationUniversal :
    (nativePresheafDerivation Y φ).Universal :=
  DifferentialsConstruction.isUniversal' φ

def nativeDifferentialModule : Y.Modules :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
    (nativeDifferentialPresheaf Y φ)

def nativeDifferentialHomEquiv (M : Y.Modules) :
    (nativeDifferentialModule Y φ ⟶ M) ≃ PresheafOfModulesOfCommRing.Derivation' M.val φ := by
  let e : (nativeDifferentialPresheaf Y φ ⟶ M.val) ≃
      PresheafOfModulesOfCommRing.Derivation' M.val φ :=
    { toFun := fun f ↦ (nativePresheafDerivation Y φ).postcomp f
      invFun := fun d ↦ (nativePresheafDerivationUniversal Y φ).desc d
      left_inv := by
        intro f
        apply (nativePresheafDerivationUniversal Y φ).postcomp_injective
        exact (nativePresheafDerivationUniversal Y φ).fac _
      right_inv := fun d ↦ (nativePresheafDerivationUniversal Y φ).fac d }
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    (nativeDifferentialPresheaf Y φ) M).trans e

end
end Red61

/-! The absolute differential sheaf from mathlib’s universal differential
presheaf and native module sheafification. Its Hom equivalence is proved to
be postcomposition with the universal derivation, with existence and uniqueness. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
noncomputable section
variable (Y : Scheme.{0})

def schemeIntegerScalars :
    (Functor.const Y.Opensᵒᵖ).obj (CommRingCat.of ℤ) ⟶ Y.presheaf where
  app U := CommRingCat.ofHom (Int.castRingHom Γ(Y, U.unop))
  naturality := by
    intro U V f
    apply CommRingCat.hom_ext
    exact RingHom.ext_int _ _

def nativeAbsoluteDifferentialPresheaf : PresheafOfModulesOfCommRing Y.presheaf :=
  DifferentialsConstruction.relativeDifferentials' (schemeIntegerScalars Y)

def nativeAbsolutePresheafDerivation :
    (nativeAbsoluteDifferentialPresheaf Y).Derivation' (schemeIntegerScalars Y) :=
  DifferentialsConstruction.derivation' (schemeIntegerScalars Y)

def nativeAbsoluteDifferentialModule : Y.Modules :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
    (nativeAbsoluteDifferentialPresheaf Y)

def nativeAbsoluteDifferentialUnit :
    nativeAbsoluteDifferentialPresheaf Y ⟶ (nativeAbsoluteDifferentialModule Y).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
    (nativeAbsoluteDifferentialPresheaf Y)

def nativeAbsoluteSheafDerivation :
    PresheafOfModulesOfCommRing.Derivation' (nativeAbsoluteDifferentialModule Y).val
      (schemeIntegerScalars Y) :=
  (nativeAbsolutePresheafDerivation Y).postcomp (nativeAbsoluteDifferentialUnit Y)

def nativeAbsoluteDifferentialHomEquiv (M : Y.Modules) :
    (nativeAbsoluteDifferentialModule Y ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' M.val (schemeIntegerScalars Y) :=
  nativeDifferentialHomEquiv Y (schemeIntegerScalars Y) M

theorem nativeAbsoluteDifferentialHomEquiv_apply (M : Y.Modules)
    (f : nativeAbsoluteDifferentialModule Y ⟶ M) :
    nativeAbsoluteDifferentialHomEquiv Y M f =
      (nativeAbsoluteSheafDerivation Y).postcomp f.val := by
  ext U b
  rfl

end
end Red61

/-! The native absolute differential presheaf has the ordinary integer-base
Kähler module on each open, with the prescribed integer algebra structure.
The comparison preserves universal derivatives and their native restrictions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0})

def nativeAbsoluteDifferentialSectionIso (U : Y.Opensᵒᵖ) :
    (nativeAbsoluteDifferentialPresheaf Y).obj U ≅
      ModuleCat.of Γ(Y, U.unop) (KaehlerDifferential ℤ Γ(Y, U.unop)) :=
  kaehlerDifferentialAlgebraIso
    ((schemeIntegerScalars Y).app U).hom.toAlgebra (Ring.toIntAlgebra Γ(Y, U.unop))
    (Subsingleton.elim (Int.castRingHom Γ(Y, U.unop)).toAlgebra
      (Ring.toIntAlgebra Γ(Y, U.unop)))

theorem nativeAbsoluteDifferentialSectionIso_D (U : Y.Opensᵒᵖ) (a : Γ(Y, U.unop)) :
    (nativeAbsoluteDifferentialSectionIso Y U).hom
        (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app U) a) =
      KaehlerDifferential.D ℤ Γ(Y, U.unop) a :=
  kaehlerDifferentialAlgebraIso_D
    ((schemeIntegerScalars Y).app U).hom.toAlgebra (Ring.toIntAlgebra Γ(Y, U.unop))
    (Subsingleton.elim (Int.castRingHom Γ(Y, U.unop)).toAlgebra
      (Ring.toIntAlgebra Γ(Y, U.unop))) a

end
end Red61

/-! Native absolute differential sections map to ordinary differentials of
the ring stalk through the actual ring germ. The derivative formula and
scalar compatibility hold for the prescribed canonical integer algebras. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (x : Y) (U : Y.Opens) (hx : x ∈ U)

def nativeAbsoluteDifferentialGermMap :
    (nativeAbsoluteDifferentialPresheaf Y).obj (op U) →+
      KaehlerDifferential ℤ (Y.presheaf.stalk x) := by
  letI := (Y.presheaf.germ U x hx).hom.toAlgebra
  have : IsScalarTower ℤ Γ(Y, U) (Y.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  exact (KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x)).toAddMonoidHom.comp
    (nativeAbsoluteDifferentialSectionIso Y (op U)).hom.hom.toAddMonoidHom

theorem nativeAbsoluteDifferentialGermMap_D (a : Γ(Y, U)) :
    nativeAbsoluteDifferentialGermMap Y x U hx
        (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a) =
      KaehlerDifferential.D ℤ (Y.presheaf.stalk x) (Y.presheaf.germ U x hx a) := by
  let := (Y.presheaf.germ U x hx).hom.toAlgebra
  have : IsScalarTower ℤ Γ(Y, U) (Y.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  change KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x)
    ((nativeAbsoluteDifferentialSectionIso Y (op U)).hom
      (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a)) = _
  exact (congrArg (KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x))
    (nativeAbsoluteDifferentialSectionIso_D Y (op U) a)).trans
      (KaehlerDifferential.map_D ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x) a)

theorem nativeAbsoluteDifferentialGermMap_smul
    (a : Γ(Y, U)) (ω : (nativeAbsoluteDifferentialPresheaf Y).obj (op U)) :
    nativeAbsoluteDifferentialGermMap Y x U hx (a • ω) =
      Y.presheaf.germ U x hx a • nativeAbsoluteDifferentialGermMap Y x U hx ω := by
  let := (Y.presheaf.germ U x hx).hom.toAlgebra
  have : IsScalarTower ℤ Γ(Y, U) (Y.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  change KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x)
    ((nativeAbsoluteDifferentialSectionIso Y (op U)).hom (a • ω)) = _
  calc
    _ = KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x)
        (a • (nativeAbsoluteDifferentialSectionIso Y (op U)).hom ω) :=
      congrArg (KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x))
        ((nativeAbsoluteDifferentialSectionIso Y (op U)).hom.hom.map_smul a ω)
    _ = a • KaehlerDifferential.map ℤ ℤ Γ(Y, U) (Y.presheaf.stalk x)
        ((nativeAbsoluteDifferentialSectionIso Y (op U)).hom ω) := map_smul _ _ _
    _ = _ := (algebraMap_smul (Y.presheaf.stalk x) a _).symm
end
end Red61

/-! The native maps from differential sections to local-ring differentials
commute with neighborhood restriction. Equality is proved by the actual
universal derivatives, retaining the germ-induced scalar actions. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
variable (Y : Scheme.{0}) (x : Y) {U W : Y.Opens} (i : W ⟶ U) (hx : x ∈ W)

theorem nativeAbsoluteDifferentialGermMap_restrict
    (ω : (nativeAbsoluteDifferentialPresheaf Y).obj (op U)) :
    nativeAbsoluteDifferentialGermMap Y x W hx
        ((nativeAbsoluteDifferentialPresheaf Y).map i.op ω) =
      nativeAbsoluteDifferentialGermMap Y x U (i.le hx) ω := by
  let := Module.compHom (KaehlerDifferential ℤ (Y.presheaf.stalk x))
    (Y.presheaf.germ U x (i.le hx)).hom
  let f₁ : (nativeAbsoluteDifferentialPresheaf Y).obj (op U) →ₗ[Γ(Y, U)]
      KaehlerDifferential ℤ (Y.presheaf.stalk x) :=
    { toFun := fun η ↦ nativeAbsoluteDifferentialGermMap Y x W hx
        ((nativeAbsoluteDifferentialPresheaf Y).map i.op η)
      map_add' := by
        intro η θ
        exact (congrArg (nativeAbsoluteDifferentialGermMap Y x W hx)
          (((nativeAbsoluteDifferentialPresheaf Y).map i.op).hom.map_add η θ)).trans
            (map_add _ _ _)
      map_smul' := by
        intro a η
        change nativeAbsoluteDifferentialGermMap Y x W hx
          ((nativeAbsoluteDifferentialPresheaf Y).map i.op (a • η)) =
          Y.presheaf.germ U x (i.le hx) a • nativeAbsoluteDifferentialGermMap Y x W hx
            ((nativeAbsoluteDifferentialPresheaf Y).map i.op η)
        exact (congrArg (nativeAbsoluteDifferentialGermMap Y x W hx)
          ((nativeAbsoluteDifferentialPresheaf Y).map_smul i.op a η)).trans
            ((nativeAbsoluteDifferentialGermMap_smul Y x W hx (Y.presheaf.map i.op a)
              ((nativeAbsoluteDifferentialPresheaf Y).map i.op η)).trans
                (congrArg (fun r ↦ r • nativeAbsoluteDifferentialGermMap Y x W hx
                  ((nativeAbsoluteDifferentialPresheaf Y).map i.op η))
                    (Y.presheaf.germ_res_apply i x hx a))) }
  let f₂ : (nativeAbsoluteDifferentialPresheaf Y).obj (op U) →ₗ[Γ(Y, U)]
      KaehlerDifferential ℤ (Y.presheaf.stalk x) :=
    { toFun := nativeAbsoluteDifferentialGermMap Y x U (i.le hx)
      map_add' := map_add _
      map_smul' := nativeAbsoluteDifferentialGermMap_smul Y x U (i.le hx) }
  have he : ModuleCat.ofHom f₁ = ModuleCat.ofHom f₂ := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change nativeAbsoluteDifferentialGermMap Y x W hx
      ((nativeAbsoluteDifferentialPresheaf Y).map i.op
        (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a)) =
      nativeAbsoluteDifferentialGermMap Y x U (i.le hx)
        (CommRingCat.KaehlerDifferential.d (f := (schemeIntegerScalars Y).app (op U)) a)
    have hm := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (schemeIntegerScalars Y) i.op a
    exact (congrArg (nativeAbsoluteDifferentialGermMap Y x W hx) hm).trans
      ((nativeAbsoluteDifferentialGermMap_D Y x W hx (Y.presheaf.map i.op a)).trans
        ((congrArg (KaehlerDifferential.D ℤ (Y.presheaf.stalk x))
          (Y.presheaf.germ_res_apply i x hx a)).trans
            (nativeAbsoluteDifferentialGermMap_D Y x U (i.le hx) a).symm))
  exact ConcreteCategory.congr_hom he ω
end
end Red61

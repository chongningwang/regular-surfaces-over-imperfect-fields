import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.LocallySurjective
import Red61.AlgebraicGeometry.Atlas

/-! # Rational lattices and orders of rational top forms

Formerly the modules `BirationalStalkFractions`, `BirationalRationalDifferentials`, `CoordinateJacobians`, `IntrinsicStalkValuation`, `RationalLatticeFunctions`, `RationalLatticeSheaf`, `RationalLatticeModule`, `RationalTopFormOrders`, `FiniteRationalFormOrders`, `RationalStalkTopForms`, `IntrinsicRationalFormOrders`.
-/

/-! A birational function-field map makes the actual target function field
a fraction field of the source stalk. The algebra is the composite of the
actual stalk map and the canonical embedding into the function field. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

variable {Y X : Scheme} [IsIntegral Y] (f : Y ⟶ X) (y : Y)

@[instance_reducible] def stalkSourceFractionAlgebra :
    Algebra (X.presheaf.stalk (f y)) Y.functionField :=
  ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (f.stalkMap y).hom).toAlgebra

end
end Red61

/-! Rational absolute differentials of scheme stalks, with a common target
in the differential module of the actual function field. For a birational
morphism, both rationalized stalk lattices identify with that module and
the actual differential map commutes with these identifications. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
noncomputable section

variable {Y X : Scheme} [IsIntegral Y] (f : Y ⟶ X) (y : Y)

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

private local instance : Module (Y.presheaf.stalk y) (PulledStalkDifferentials f y) :=
  let := (f.stalkMap y).hom.toAlgebra
  TensorProduct.leftModule

private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

def stalkRationalDifferentialEquiv :
    Y.functionField ⊗[Y.presheaf.stalk y] AbsoluteStalkDifferentials Y y ≃ₗ[Y.functionField]
      KaehlerDifferential ℤ Y.functionField :=
  fractionDifferentialEquiv (Y.presheaf.stalk y) Y.functionField

@[simp] theorem stalkRationalDifferentialEquiv_tmul_D (a : Y.presheaf.stalk y)
    (c : Y.functionField) :
    stalkRationalDifferentialEquiv y (c ⊗ₜ[Y.presheaf.stalk y]
      KaehlerDifferential.D ℤ (Y.presheaf.stalk y) a) =
      c • KaehlerDifferential.D ℤ Y.functionField
        (algebraMap (Y.presheaf.stalk y) Y.functionField a) :=
  fractionDifferentialEquiv_tmul_D _ _ _ _

variable [IsIntegral X]
  (hf : f (genericPoint Y) = genericPoint X)
  (hb : Function.Bijective (genericFieldMap f hf))

end
end Red61

/-! Direct Jacobian calculations for the two exceptional coordinate changes.
The only hypotheses are an actual differential basis and the coordinate
identities; no differential-length input is used. -/

namespace Red61

open Module
noncomputable section

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

def coordinateDifferentialMatrix (b : Basis (Fin 4) R (KaehlerDifferential A R))
    (w : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j ↦ b.repr (KaehlerDifferential.D A R (w j)) i

theorem coordinateDifferentialMatrix_det_eq_topForm
    (b : Basis (Fin 4) R (KaehlerDifferential A R)) (w : Fin 4 → R) :
    (coordinateDifferentialMatrix b w).det =
      b.det (fun i ↦ KaehlerDifferential.D A R (w i)) :=
  (b.det_apply _).symm

end
end Red61

/-! The intrinsic order at a codimension-one DVR stalk, with its zero value
restored to infinity, is an additive valuation on the actual function field.
It is nonnegative on the specified stalk and agrees with Scheme.ord away
from zero. -/

namespace Red61

open AlgebraicGeometry Order
noncomputable section

variable {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
  (y : Y) (hy : coheight y = 1) [IsDiscreteValuationRing (Y.presheaf.stalk y)]

def intrinsicStalkValuation : AddValuation Y.functionField (WithTop ℤ) := by
  classical
  let o : Y.functionField → WithTop ℤ := fun f ↦ if f = 0 then ⊤ else (Y.ord f y : WithTop ℤ)
  refine AddValuation.of o (by simp [o]) ?_ ?_ ?_
  · have h1 : Y.ord 1 y = 0 := (Scheme.ord_eq_iff hy one_ne_zero).mpr (map_one _)
    simp [o, h1]
  · intro f g
    by_cases hfg : f + g = 0
    · simp [o, hfg]
    by_cases hf : f = 0
    · simp [o, hf]
    by_cases hg : g = 0
    · simp [o, hg]
    simpa only [o, ite_eq_right hf, ite_eq_right hg, ite_eq_right hfg, ← WithTop.coe_min,
      WithTop.coe_le_coe] using Y.ord_add hfg
  · intro f g
    by_cases hf : f = 0
    · simp [o, hf]
    by_cases hg : g = 0
    · simp [o, hg]
    simpa only [o, ite_eq_right hf, ite_eq_right hg, ite_eq_right (mul_ne_zero hf hg),
      WithTop.coe_add] using
      congrArg (fun z : ℤ ↦ (z : WithTop ℤ)) (Y.ord_mul hf hg)

end
end Red61

section
/-! Intrinsic sections of rational lattices on an integral scheme. A section
is a locally constant function into a rational vector space whose value at
every point lies in the prescribed integral lattice. This condition is local
and therefore defines a genuine sheaf of types, independently of a volume. -/

universe u

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

variable (Y : Scheme.{u}) (V : Type u) (I : Y → Set V)

def pointwiseLatticePredicate : TopCat.LocalPredicate (fun _ : Y ↦ V) where
  pred {U} s := ∀ x : U, s x ∈ I x.val
  res i _ h x := by exact h (i x)
  locality {U} _ h (x : U) := by
    obtain ⟨W, hx, i, hs⟩ := h x
    exact hs ⟨x, hx⟩

def rationalLatticePredicate : TopCat.LocalPredicate (fun _ : Y ↦ V) :=
  letI : TopologicalSpace V := ⊥
  (TopCat.continuousLocal Y V).and (pointwiseLatticePredicate Y V I)

theorem rationalLatticePredicate_iff {U : Y.Opens} (s : U → V) :
    (rationalLatticePredicate Y V I).pred s ↔
      IsLocallyConstant s ∧ ∀ x : U, s x ∈ I x.val := by
  let : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  change Continuous s ∧ (∀ x : U, s x ∈ I x.val) ↔ _
  rw [← IsLocallyConstant.iff_continuous]

def rationalLatticeTypeSheaf : TopCat.Sheaf (Type u) Y :=
  TopCat.subsheafToTypes (rationalLatticePredicate Y V I)

variable [IsIntegral Y]

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

def sectionRationalValue (U : Y.Opens) (a : Γ(Y, U)) (x : U) : Y.functionField :=
  algebraMap (Y.presheaf.stalk x.val) Y.functionField (Y.presheaf.germ U x.val x.property a)

theorem sectionRationalValue_eq (U : Y.Opens) (a : Γ(Y, U)) (x y : U) :
    sectionRationalValue Y U a x = sectionRationalValue Y U a y := by
  have : Nonempty U := ⟨x⟩
  exact (Y.algebraMap_germ_eq_germToFunctionField x.property a).trans
    (Y.algebraMap_germ_eq_germToFunctionField y.property a).symm

theorem sectionRationalValue_restrict {U W : Y.Opens} (i : W ⟶ U)
    (a : Γ(Y, U)) (x : W) :
    sectionRationalValue Y W (Y.presheaf.map i.op a) x =
      sectionRationalValue Y U a (i x) := by
  unfold sectionRationalValue
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem sectionRationalValue_injective (U : Y.Opens) (a b : Γ(Y, U))
    (h : ∀ x : U, sectionRationalValue Y U a x = sectionRationalValue Y U b x) : a = b := by
  apply TopCat.Presheaf.section_ext Y.sheaf U a b
  intro x hx
  exact IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField (h ⟨x, hx⟩)

variable [AddCommGroup V] [Module Y.functionField V]

def sectionVolumeFunction (κ : V) (U : Y.Opens) (a : Γ(Y, U)) (x : U) : V :=
  sectionRationalValue Y U a x • κ

theorem sectionVolumeFunction_locallyConstant (κ : V) (U : Y.Opens) (a : Γ(Y, U)) :
    IsLocallyConstant (sectionVolumeFunction Y V κ U a) :=
  IsLocallyConstant.of_constant _ fun x y ↦
    congrArg (fun c : Y.functionField ↦ c • κ) (sectionRationalValue_eq Y U a x y)

theorem sectionVolumeFunction_injective (κ : V) (hκ : κ ≠ 0) (U : Y.Opens) :
    Function.Injective (sectionVolumeFunction Y V κ U) := by
  intro a b h
  apply sectionRationalValue_injective Y U a b
  intro x
  exact smul_left_injective Y.functionField hκ (congrFun h x)

end
end Red61
end

section
/-! A generating rational vector trivializes its intrinsic lattice sheaf.
The sheaf is defined independently of that vector. The proof constructs a
natural map from regular functions, proves sectionwise injectivity and local
surjectivity using actual stalk representatives, then obtains a sheaf isomorphism. -/

universe u

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
noncomputable section

variable (Y : Scheme.{u}) [IsIntegral Y]

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

variable (V : Type u) [AddCommGroup V] [Module Y.functionField V]
  (I : Y → Set V) (κ : V)
  (hI : ∀ (y : Y) (v : V), v ∈ I y ↔
    ∃ a : Y.presheaf.stalk y, v = algebraMap (Y.presheaf.stalk y) Y.functionField a • κ)

def scalarTypeSheaf : TopCat.Sheaf (Type u) Y :=
  (sheafCompose _ (forget CommRingCat)).obj Y.sheaf

def latticeVolumeSection (U : Y.Opens) (a : Γ(Y, U)) :
    (rationalLatticeTypeSheaf Y V I).obj.obj (op U) :=
  ⟨sectionVolumeFunction Y V κ U a,
    (rationalLatticePredicate_iff Y V I _).mpr
      ⟨sectionVolumeFunction_locallyConstant Y V κ U a,
        fun x ↦ (hI x.val _).mpr ⟨Y.presheaf.germ U x.val x.property a, rfl⟩⟩⟩

def latticeVolumeMorphism : scalarTypeSheaf Y ⟶ rationalLatticeTypeSheaf Y V I where
  hom :=
    { app := fun U ↦ ↾(latticeVolumeSection Y V I κ hI U.unop)
      naturality := by
        intro U W i
        ext a
        apply Subtype.ext
        funext x
        exact congrArg (fun c : Y.functionField ↦ c • κ)
          (sectionRationalValue_restrict Y i.unop a x) }

theorem latticeVolumeMorphism_injective (hκ : κ ≠ 0) (U : Y.Opens) :
    Function.Injective ((latticeVolumeMorphism Y V I κ hI).hom.app (op U)) := by
  intro a b he
  exact sectionVolumeFunction_injective Y V κ hκ U (congrArg Subtype.val he)

theorem latticeVolumeMorphism_locallySurjective :
    TopCat.Presheaf.IsLocallySurjective (latticeVolumeMorphism Y V I κ hI).hom := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t x hx
  have hl := (rationalLatticePredicate_iff Y V I t.val).mp t.property
  obtain ⟨a, ha⟩ := (hI x (t.val ⟨x, hx⟩)).mp (hl.2 ⟨x, hx⟩)
  obtain ⟨W, hWU, hxW, s, hs⟩ := Y.presheaf.exists_le_germ_eq a hx
  refine ⟨W, hWU, ⟨s, ?_⟩, hxW⟩
  apply Subtype.ext
  funext y
  change sectionVolumeFunction Y V κ W s y = t.val ((homOfLE hWU) y)
  have hcenter : sectionVolumeFunction Y V κ W s ⟨x, hxW⟩ = t.val ⟨x, hx⟩ := by
    change algebraMap (Y.presheaf.stalk x) Y.functionField
      (Y.presheaf.germ W x hxW s) • κ = _
    rw [hs]
    exact ha.symm
  have : PreirreducibleSpace U := U.isOpenEmbedding'.preirreducibleSpace
  have hpre : PreconnectedSpace U := PreirreducibleSpace.preconnectedSpace U
  calc
    sectionVolumeFunction Y V κ W s y =
        sectionVolumeFunction Y V κ W s ⟨x, hxW⟩ :=
      congrArg (fun c : Y.functionField ↦ c • κ) (sectionRationalValue_eq Y W s y ⟨x, hxW⟩)
    _ = t.val ⟨x, hx⟩ := hcenter
    _ = t.val ((homOfLE hWU) y) :=
      @IsLocallyConstant.apply_eq_of_preconnectedSpace U V _ hpre t.val hl.1 _ _

theorem latticeVolumeMorphism_isIso (hκ : κ ≠ 0) :
    IsIso (latticeVolumeMorphism Y V I κ hI) := by
  let : Balanced (TopCat.Sheaf (Type u) Y) :=
    CategoryTheory.SheafOfTypes.balanced (J := Opens.grothendieckTopology Y)
  let φ := latticeVolumeMorphism Y V I κ hI
  have : Mono φ := CategoryTheory.Sheaf.mono_of_injective _
    (fun U ↦ latticeVolumeMorphism_injective Y V I κ hI hκ U.unop)
  have : Epi φ := (TopCat.Sheaf.isLocallySurjective_iff_epi φ).mp
    (latticeVolumeMorphism_locallySurjective Y V I κ hI)
  exact isIso_of_mono_of_epi φ

def latticeVolumeTypeIso (hκ : κ ≠ 0) :
    scalarTypeSheaf Y ≅ rationalLatticeTypeSheaf Y V I := by
  have := latticeVolumeMorphism_isIso Y V I κ hI hκ
  exact asIso (latticeVolumeMorphism Y V I κ hI)

end
end Red61
end

section
/-! A rational volume gives the intrinsic lattice sheaf its genuine module
structure. Its sections are the previously defined integral rational sections,
and its restriction maps agree with their intrinsic restrictions. Multiplication
by the volume is an isomorphism of sheaves of modules. -/

universe u

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (Y : Scheme.{u}) [IsIntegral Y]

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

variable (V : Type u) [AddCommGroup V] [Module Y.functionField V]
  (I : Y → Set V) (κ : V)
  (hI : ∀ (y : Y) (v : V), v ∈ I y ↔
    ∃ a : Y.presheaf.stalk y, v = algebraMap (Y.presheaf.stalk y) Y.functionField a • κ)
  (hκ : κ ≠ 0)

def latticeSectionCoefficientEquiv (U : Y.Opensᵒᵖ) :
    (rationalLatticeTypeSheaf Y V I).obj.obj U ≃ (structureSheafModule Y).val.obj U :=
  (((sheafToPresheaf _ _).mapIso (latticeVolumeTypeIso Y V I κ hI hκ)).app U).toEquiv.symm

def rationalLatticeModule : Y.Modules :=
  transportedModuleSheaf Y.ringCatSheaf (structureSheafModule Y)
    (fun U ↦ (rationalLatticeTypeSheaf Y V I).obj.obj U)
    (latticeSectionCoefficientEquiv Y V I κ hI hκ)

def latticeVolumeModuleIso : structureSheafModule Y ≅ rationalLatticeModule Y V I κ hI hκ :=
  (transportedModuleSheafIso Y.ringCatSheaf (structureSheafModule Y)
    (fun U ↦ (rationalLatticeTypeSheaf Y V I).obj.obj U)
    (latticeSectionCoefficientEquiv Y V I κ hI hκ)).symm

@[simp] theorem latticeVolumeModuleIso_apply (U : Y.Opens) (a : Γ(Y, U)) :
    (latticeVolumeModuleIso Y V I κ hI hκ).hom.app U a =
      latticeVolumeSection Y V I κ hI U a := rfl

include hκ in
theorem latticeVolumeSection_surjective (U : Y.Opens) :
    Function.Surjective (latticeVolumeSection Y V I κ hI U) :=
  (latticeSectionCoefficientEquiv Y V I κ hI hκ (op U)).symm.surjective

theorem rationalLatticeModule_add_value (U : Y.Opens)
    (s t : Γ(rationalLatticeModule Y V I κ hI hκ, U)) (x : U) :
    (s + t).val x = s.val x + t.val x := by
  obtain ⟨a, rfl⟩ := latticeVolumeSection_surjective Y V I κ hI hκ U s
  obtain ⟨b, rfl⟩ := latticeVolumeSection_surjective Y V I κ hI hκ U t
  rw [← latticeVolumeModuleIso_apply Y V I κ hI hκ U a,
    ← latticeVolumeModuleIso_apply Y V I κ hI hκ U b,
    ← map_add]
  change sectionVolumeFunction Y V κ U (a + b) x =
    sectionVolumeFunction Y V κ U a x + sectionVolumeFunction Y V κ U b x
  simp [sectionVolumeFunction, sectionRationalValue, add_smul]

theorem rationalLatticeModule_smul_value (U : Y.Opens) (a : Γ(Y, U))
    (t : Γ(rationalLatticeModule Y V I κ hI hκ, U)) (x : U) :
    (a • t).val x = sectionRationalValue Y U a x • t.val x := by
  obtain ⟨b, rfl⟩ := latticeVolumeSection_surjective Y V I κ hI hκ U t
  rw [← latticeVolumeModuleIso_apply Y V I κ hI hκ U b,
    ← (latticeVolumeModuleIso Y V I κ hI hκ).hom.app_smul a b]
  change sectionRationalValue Y U (a * b) x • κ =
    sectionRationalValue Y U a x • (sectionRationalValue Y U b x • κ)
  simp [sectionRationalValue, mul_smul]

theorem rationalLatticeModule_restrict {U W : Y.Opens} (i : W ⟶ U)
    (t : Γ(rationalLatticeModule Y V I κ hI hκ, U)) :
    (rationalLatticeModule Y V I κ hI hκ).presheaf.map i.op t =
      (rationalLatticeTypeSheaf Y V I).obj.map i.op t := by
  let e := latticeVolumeTypeIso Y V I κ hI hκ
  change e.hom.hom.app (op W) (Y.presheaf.map i.op (e.inv.hom.app (op U) t)) = _
  have hn := ConcreteCategory.congr_hom (e.hom.hom.naturality i.op)
    (e.inv.hom.app (op U) t)
  change e.hom.hom.app (op W) (Y.presheaf.map i.op (e.inv.hom.app (op U) t)) =
    (rationalLatticeTypeSheaf Y V I).obj.map i.op
      (e.hom.hom.app (op U) (e.inv.hom.app (op U) t)) at hn
  have hc : e.hom.hom.app (op U) (e.inv.hom.app (op U) t) = t :=
    congrArg (fun φ ↦ φ.hom.app (op U) t) e.inv_hom_id
  rw [hc] at hn
  exact hn

end
end Red61
end

/-! Orders of rational top exterior forms in a free local lattice. Integral
basis changes preserve the order, and a linear map changes it by the order
of its genuine determinant. The zero form has order infinity. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable {R F M N : Type*} [CommRing R] [Field F] [Algebra R F]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}

def rationalTopFormOrder (v : AddValuation F (WithTop ℤ)) (b : Basis (Fin n) R M)
    (ω : ⋀[F]^n (F ⊗[R] M)) : WithTop ℤ :=
  v (topExteriorCoefficient (b.baseChange F) ω)

@[simp] theorem rationalTopFormOrder_zero (v : AddValuation F (WithTop ℤ))
    (b : Basis (Fin n) R M) : rationalTopFormOrder v b 0 = ⊤ := by
  simp [rationalTopFormOrder]

end
end Red61

/-! Rational top-form orders are finite exactly for nonzero forms. Their
integer values respect integral basis changes and determinant order shifts. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable {R F M N : Type*} [CommRing R] [Field F] [Algebra R F]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}

theorem rationalTopVolume_ne_zero (b : Basis (Fin n) R M) :
    exteriorPower.ιMulti F n (b.baseChange F) ≠ 0 := by
  intro h
  have he := topExteriorCoefficient_volume (b.baseChange F)
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem rationalTopFormOrder_ne_top_iff (v : AddValuation F (WithTop ℤ))
    (b : Basis (Fin n) R M) (ω : ⋀[F]^n (F ⊗[R] M)) :
    rationalTopFormOrder v b ω ≠ ⊤ ↔ ω ≠ 0 := by
  unfold rationalTopFormOrder
  rw [AddValuation.ne_top_iff]
  exact map_ne_zero_iff _ (topExteriorCoefficient_bijective (b.baseChange F)).injective

def rationalTopFormOrderInt (v : AddValuation F (WithTop ℤ))
    (b : Basis (Fin n) R M) (ω : ⋀[F]^n (F ⊗[R] M)) (hω : ω ≠ 0) : ℤ :=
  (rationalTopFormOrder v b ω).untop ((rationalTopFormOrder_ne_top_iff v b ω).mpr hω)

@[simp] theorem rationalTopFormOrderInt_coe (v : AddValuation F (WithTop ℤ))
    (b : Basis (Fin n) R M) (ω : ⋀[F]^n (F ⊗[R] M)) (hω : ω ≠ 0) :
    (rationalTopFormOrderInt v b ω hω : WithTop ℤ) = rationalTopFormOrder v b ω :=
  WithTop.coe_untop _ _

end
end Red61

/-! Rational exterior forms in one function-field differential module.
Source and target stalk lattices of a birational morphism are compared in
this common space through their actual localization maps. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open scoped TensorProduct
noncomputable section

variable {Y X : Scheme} [IsIntegral Y] (f : Y ⟶ X) (y : Y) (n : ℕ)

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

private local instance : Module (Y.presheaf.stalk y) (PulledStalkDifferentials f y) :=
  let := (f.stalkMap y).hom.toAlgebra
  TensorProduct.leftModule

private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

abbrev RationalSchemeForms (Y : Scheme) [IsIntegral Y] (n : ℕ) :=
  ⋀[Y.functionField]^n (KaehlerDifferential ℤ Y.functionField)

def stalkRationalTopEquiv :
    (⋀[Y.functionField]^n
      (Y.functionField ⊗[Y.presheaf.stalk y] AbsoluteStalkDifferentials Y y)) ≃ₗ[Y.functionField]
        RationalSchemeForms Y n :=
  exteriorLinearEquiv n (stalkRationalDifferentialEquiv y)

def stalkRationalFormOrder (v : AddValuation Y.functionField (WithTop ℤ))
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : RationalSchemeForms Y n) : WithTop ℤ :=
  rationalTopFormOrder v b ((stalkRationalTopEquiv y n).symm ω)

variable [IsIntegral X] (hf : f (genericPoint Y) = genericPoint X)
  (hb : Function.Bijective (genericFieldMap f hf))

end
end Red61

/-! Integer orders of nonzero rational forms in the common function-field
space. Integral stalk bases give the same order. Multiplying a form by a
nonzero rational function changes its order by the intrinsic scheme order. -/

namespace Red61

open AlgebraicGeometry Order Module
open scoped TensorProduct
noncomputable section

variable {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
  (y : Y) (hy : coheight y = 1) [IsDiscreteValuationRing (Y.presheaf.stalk y)] {n : ℕ}

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

private local instance : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y)
    (R' := Y.presheaf.stalk y)

omit [IsLocallyNoetherian Y] [IsDiscreteValuationRing (Y.presheaf.stalk y)] in
theorem stalkRationalTopEquiv_symm_ne_zero (ω : RationalSchemeForms Y n) (hω : ω ≠ 0) :
    (stalkRationalTopEquiv y n).symm ω ≠ 0 :=
  (map_ne_zero_iff _ (stalkRationalTopEquiv y n).symm.injective).mpr hω

def intrinsicRationalFormOrder
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : RationalSchemeForms Y n) (hω : ω ≠ 0) : ℤ :=
  rationalTopFormOrderInt (intrinsicStalkValuation y hy) b
    ((stalkRationalTopEquiv y n).symm ω) (stalkRationalTopEquiv_symm_ne_zero y ω hω)

@[simp] theorem intrinsicRationalFormOrder_coe
    (b : Basis (Fin n) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y))
    (ω : RationalSchemeForms Y n) (hω : ω ≠ 0) :
    (intrinsicRationalFormOrder y hy b ω hω : WithTop ℤ) =
      stalkRationalFormOrder y n (intrinsicStalkValuation y hy) b ω :=
  rationalTopFormOrderInt_coe _ _ _ _

end
end Red61

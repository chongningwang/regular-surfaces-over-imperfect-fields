import Red61.AlgebraicGeometry.ExteriorPower

/-! # Exterior differential sheaves and integral lattices

Formerly the modules `NativeAbsoluteExteriorRationalSections`, `NativeExteriorLatticeMap`, `NativeExteriorCoefficientStalk`, `NativeExteriorLatticeIso`.
-/

/-! Rational realization of genuine exterior differential sections is
independent of the point of evaluation. Specialization to the generic point
proves local constancy, and the construction commutes with restriction. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
variable (Y : Scheme.{0}) [IsIntegral Y] (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance (x : Y) : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x

/-- Rational stalk realization is the ordinary realization at the generic point. -/
theorem nativeAbsoluteExteriorStalkToRational_generic (x : Y) (ξ : (E).presheaf.stalk x) :
    nativeAbsoluteExteriorStalkToRational Y x n ξ =
      nativeAbsoluteExteriorStalkToOrdinary Y (genericPoint Y) n
        (moduleStalkSpecializesSemilinear Y (E).val
          ((genericPoint_spec Y).specializes (Set.mem_univ x)) ξ) :=
  (nativeAbsoluteExteriorStalkToOrdinary_specializes Y
    ((genericPoint_spec Y).specializes (Set.mem_univ x)) n ξ).symm

/-- The rational value of a genuine exterior differential section at a point. -/
def nativeAbsoluteExteriorSectionRationalValue (U : Y.Opens) (t : (E).val.obj (op U))
    (x : U) : RationalSchemeForms Y n :=
  nativeAbsoluteExteriorStalkToRational Y x.val n ((E).presheaf.germ U x.val x.property t)

/-- A section has the same rational value at every point of its open. -/
theorem nativeAbsoluteExteriorSectionRationalValue_eq (U : Y.Opens)
    (t : (E).val.obj (op U)) (x y : U) :
    nativeAbsoluteExteriorSectionRationalValue Y n U t x =
      nativeAbsoluteExteriorSectionRationalValue Y n U t y := by
  let h (z : Y) := (genericPoint_spec Y).specializes (Set.mem_univ z)
  have hx := nativeAbsoluteExteriorStalkToRational_generic Y n x.val
    ((E).presheaf.germ U x.val x.property t)
  have hy := nativeAbsoluteExteriorStalkToRational_generic Y n y.val
    ((E).presheaf.germ U y.val y.property t)
  have hxs := moduleStalkSpecializesSemilinear_germ Y (E).val (h x.val) U x.property t
  have hys := moduleStalkSpecializesSemilinear_germ Y (E).val (h y.val) U y.property t
  exact hx.trans ((congrArg (nativeAbsoluteExteriorStalkToOrdinary Y (genericPoint Y) n)
    hxs).trans ((congrArg (nativeAbsoluteExteriorStalkToOrdinary Y (genericPoint Y) n)
      hys).symm.trans hy.symm))

/-- Rational values of genuine exterior sections are locally constant. -/
theorem nativeAbsoluteExteriorSectionRationalValue_locallyConstant (U : Y.Opens)
    (t : (E).val.obj (op U)) :
    IsLocallyConstant (nativeAbsoluteExteriorSectionRationalValue Y n U t) :=
  IsLocallyConstant.of_constant _ (nativeAbsoluteExteriorSectionRationalValue_eq Y n U t)

/-- Rational section values commute with actual open restriction. -/
theorem nativeAbsoluteExteriorSectionRationalValue_restrict {U W : Y.Opens} (i : W ⟶ U)
    (t : (E).val.obj (op U)) (x : W) :
    nativeAbsoluteExteriorSectionRationalValue Y n W ((E).val.map i.op t) x =
      nativeAbsoluteExteriorSectionRationalValue Y n U t (i x) :=
  congrArg (nativeAbsoluteExteriorStalkToRational Y x.val n)
    (TopCat.Presheaf.germ_res_apply (E).presheaf i x.val x.property t)
end
end Red61

/-! The genuine top exterior differential sheaf maps to the intrinsic
integral differential lattice. The actual stalk rational values are locally
constant, integral, additive, scalar-compatible, and commute on all opens. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (Y : Scheme.{0}) [IsIntegral Y] (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance (x : Y) : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x

/-- Rational section realization preserves addition. -/
theorem nativeAbsoluteExteriorSectionRationalValue_add (U : Y.Opens)
    (s t : (E).val.obj (op U)) (x : U) :
    nativeAbsoluteExteriorSectionRationalValue Y n U (s + t) x =
      nativeAbsoluteExteriorSectionRationalValue Y n U s x +
        nativeAbsoluteExteriorSectionRationalValue Y n U t x := by
  simp only [nativeAbsoluteExteriorSectionRationalValue, map_add]

/-- Rational section realization preserves the actual scalar action. -/
theorem nativeAbsoluteExteriorSectionRationalValue_smul (U : Y.Opens)
    (a : Γ(Y, U)) (t : (E).val.obj (op U)) (x : U) :
    nativeAbsoluteExteriorSectionRationalValue Y n U (a • t) x =
      sectionRationalValue Y U a x • nativeAbsoluteExteriorSectionRationalValue Y n U t x := by
  exact (congrArg (nativeAbsoluteExteriorStalkToRational Y x.val n)
    (PresheafOfModules.germ_smul (E).val x.val U x.property a t)).trans
      (map_smulₛₗ (nativeAbsoluteExteriorStalkToRational Y x.val n)
        (Y.presheaf.germ U x.val x.property a) ((E).presheaf.germ U x.val x.property t))

variable (κ : RationalSchemeForms Y n) (hκ : κ ≠ 0)
  (generates : ∀ x : Y, GeneratesStalkDifferentialLattice x κ)
  (b : ∀ x : Y, Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))
local notation "L" => integralDifferentialModule Y n κ hκ generates

/-- A genuine exterior section defines its intrinsic integral rational section. -/
def nativeAbsoluteExteriorLatticeSection (U : Y.Opens) (t : (E).val.obj (op U)) :
    (L).val.obj (op U) :=
  ⟨nativeAbsoluteExteriorSectionRationalValue Y n U t,
    (rationalLatticePredicate_iff Y (RationalSchemeForms Y n)
      (integralDifferentialLattice Y n) _).mpr
        ⟨nativeAbsoluteExteriorSectionRationalValue_locallyConstant Y n U t,
          fun x ↦ nativeAbsoluteExteriorStalkToRational_integral Y x.val n (b x.val)
            ((E).presheaf.germ U x.val x.property t)⟩⟩

/-- The actual volume-compatible morphism from genuine exterior to integral lattice. -/
def nativeAbsoluteExteriorLatticeMap : (E) ⟶ (L) where
  val :=
    { app := fun U ↦ @ModuleCat.ofHom _ _ ((E).val.obj U) ((L).val.obj U)
        ((E).val.obj U).isAddCommGroup ((E).val.obj U).isModule
        ((L).val.obj U).isAddCommGroup ((L).val.obj U).isModule
        { toFun := nativeAbsoluteExteriorLatticeSection Y n κ hκ generates b U.unop
          map_add' := by
            intro s t
            apply Subtype.ext
            funext x
            exact (nativeAbsoluteExteriorSectionRationalValue_add Y n U.unop s t x).trans
              (rationalLatticeModule_add_value Y (RationalSchemeForms Y n)
                (integralDifferentialLattice Y n) κ
                (integralDifferentialLattice_iff Y n κ generates) hκ U.unop
                  (nativeAbsoluteExteriorLatticeSection Y n κ hκ generates b U.unop s)
                  (nativeAbsoluteExteriorLatticeSection Y n κ hκ generates b U.unop t) x).symm
          map_smul' := by
            intro a t
            apply Subtype.ext
            funext x
            exact (nativeAbsoluteExteriorSectionRationalValue_smul Y n U.unop a t x).trans
              (rationalLatticeModule_smul_value Y (RationalSchemeForms Y n)
                (integralDifferentialLattice Y n) κ
                (integralDifferentialLattice_iff Y n κ generates) hκ U.unop a
                  (nativeAbsoluteExteriorLatticeSection Y n κ hκ generates b U.unop t) x).symm }
      naturality := by
        intro U W i
        ext t
        apply Subtype.ext
        funext x
        have h := rationalLatticeModule_restrict Y (RationalSchemeForms Y n)
          (integralDifferentialLattice Y n) κ
          (integralDifferentialLattice_iff Y n κ generates) hκ i.unop
            (nativeAbsoluteExteriorLatticeSection Y n κ hκ generates b U.unop t)
        exact (nativeAbsoluteExteriorSectionRationalValue_restrict Y n i.unop t x).trans
          (congrArg (fun v : (L).val.obj W ↦ v.val x) h).symm }

end
end Red61

/-! Coefficients of genuine exterior sections relative to a generating
integral rational volume. The native sheaf coefficient map and its linear
stalk map preserve the actual rational values of every original germ. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
variable (Y : Scheme.{0}) [IsIntegral Y] (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance (x : Y) : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x
private local instance (x : Y) :
    Module (Y.presheaf.stalk x) ((structureSheafModule Y).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (structureSheafModule Y) x
variable (κ : RationalSchemeForms Y n) (hκ : κ ≠ 0)
  (generates : ∀ x : Y, GeneratesStalkDifferentialLattice x κ)
  (b : ∀ x : Y, Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))

/-- Coefficients of the actual exterior-to-lattice morphism. -/
def nativeAbsoluteExteriorCoefficientMap : (E) ⟶ structureSheafModule Y :=
  nativeAbsoluteExteriorLatticeMap Y n κ hκ generates b ≫
    (integralDifferentialVolumeIso Y n κ hκ generates).inv

/-- The coefficient map on the original native local-ring module. -/
def nativeAbsoluteExteriorCoefficientStalk (x : Y) :
    (E).presheaf.stalk x →ₗ[Y.presheaf.stalk x] Y.presheaf.stalk x :=
  (structureSheafModuleStalkEquiv Y x).toLinearMap.comp
    (schemeModuleStalkMap Y x (nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b))

/-- The coefficient stalk map retains original section germs. -/
theorem nativeAbsoluteExteriorCoefficientStalk_germ (x : Y) (U : Y.Opens) (hx : x ∈ U)
    (t : (E).val.obj (op U)) :
    nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x
        ((E).presheaf.germ U x hx t) =
      Y.presheaf.germ U x hx
        ((nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b).val.app (op U) t) := by
  have h := presheafModuleStalkMap_germ Y.presheaf
    (nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b).val x U hx t
  exact (congrArg (structureSheafModuleStalkEquiv Y x) h).trans
    (structureSheafModuleStalkEquiv_germ Y x U hx _)

/-- Multiplying the coefficient by the volume recovers the lattice morphism. -/
theorem nativeAbsoluteExteriorCoefficientMap_volume (U : Y.Opens) (t : (E).val.obj (op U)) :
    (integralDifferentialVolumeIso Y n κ hκ generates).hom.val.app (op U)
        ((nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b).val.app (op U) t) =
      (nativeAbsoluteExteriorLatticeMap Y n κ hκ generates b).val.app (op U) t := by
  have hc : nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b ≫
      (integralDifferentialVolumeIso Y n κ hκ generates).hom =
        nativeAbsoluteExteriorLatticeMap Y n κ hκ generates b := by
    simp [nativeAbsoluteExteriorCoefficientMap]
  exact congrArg (fun f : (E) ⟶ integralDifferentialModule Y n κ hκ generates ↦
    f.val.app (op U) t) hc

/-- Every realized rational stalk value is its actual coefficient times the volume. -/
theorem nativeAbsoluteExteriorCoefficientStalk_rational (x : Y) (ξ : (E).presheaf.stalk x) :
    nativeAbsoluteExteriorStalkToRational Y x n ξ =
      algebraMap (Y.presheaf.stalk x) Y.functionField
        (nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x ξ) • κ := by
  obtain ⟨U, hx, t, rfl⟩ := (E).presheaf.exists_germ_eq ξ
  have hv := congrArg
    (fun s : (integralDifferentialModule Y n κ hκ generates).val.obj (op U) ↦ s.val ⟨x, hx⟩)
      (nativeAbsoluteExteriorCoefficientMap_volume Y n κ hκ generates b U t)
  have hc := nativeAbsoluteExteriorCoefficientStalk_germ Y n κ hκ generates b x U hx t
  change sectionRationalValue Y U
    ((nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b).val.app (op U) t) ⟨x, hx⟩ • κ =
      nativeAbsoluteExteriorStalkToRational Y x n ((E).presheaf.germ U x hx t) at hv
  exact hv.symm.trans (congrArg (fun a ↦ algebraMap (Y.presheaf.stalk x) Y.functionField a • κ)
    hc.symm)
end
end Red61

/-! A generating rational differential volume trivializes the genuine
exterior sheaf when its actual stalks have rank-one frames. The coefficient
maps are surjective by the exact integral rational image; rank-one finite
module endomorphisms then prove bijectivity and the native stalk criterion
gives the actual volume-preserving sheaf isomorphism. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Opposite Module
noncomputable section
variable (Y : Scheme.{0}) [IsIntegral Y] (n : ℕ)
local notation "D" => nativeAbsoluteDifferentialModule Y
local notation "E" => nativeExteriorModule Y (D) n
private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance (x : Y) : Module (Y.presheaf.stalk x) ((E).presheaf.stalk x) :=
  schemeModuleNativeStalkModule Y (E) x
variable (κ : RationalSchemeForms Y n) (hκ : κ ≠ 0)
  (generates : ∀ x : Y, GeneratesStalkDifferentialLattice x κ)
  (b : ∀ x : Y, Basis (Fin n) (Y.presheaf.stalk x) (KaehlerDifferential ℤ (Y.presheaf.stalk x)))

/-- Every actual local-ring coefficient occurs in the genuine exterior stalk. -/
theorem nativeAbsoluteExteriorCoefficientStalk_surjective (x : Y) :
    Function.Surjective (nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x) := by
  have hk : IsIntegralStalkTopForm x κ :=
    (integralDifferentialLattice_iff Y n κ generates x κ).mpr ⟨1, by simp⟩
  obtain ⟨ξ, hξ⟩ := (nativeAbsoluteExteriorStalkToRational_range Y x n (b x) κ).mpr hk
  have hc : nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x ξ = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    apply smul_left_injective Y.functionField hκ
    exact (nativeAbsoluteExteriorCoefficientStalk_rational Y n κ hκ generates b x ξ).symm.trans
      (hξ.trans (by simp only [map_one, one_smul]))
  intro a
  refine ⟨a • ξ, ?_⟩
  rw [map_smul, hc, smul_eq_mul, mul_one]

/-- Rank-one frame data for the actual native exterior stalk module. -/
def nativeAbsoluteExteriorStalkFrameType (x : Y) : Type :=
  Y.presheaf.stalk x ≃ₗ[Y.presheaf.stalk x] (E).presheaf.stalk x

variable (frames : ∀ x : Y, Nonempty (nativeAbsoluteExteriorStalkFrameType Y n x))

include frames

/-- Rank-one stalk frames make the coefficient map bijective. -/
theorem nativeAbsoluteExteriorCoefficientStalk_bijective (x : Y) :
    Function.Bijective (nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x) := by
  let e : Y.presheaf.stalk x ≃ₗ[Y.presheaf.stalk x] (E).presheaf.stalk x :=
    Classical.choice (frames x)
  let c : (E).presheaf.stalk x →ₗ[Y.presheaf.stalk x] Y.presheaf.stalk x :=
    nativeAbsoluteExteriorCoefficientStalk Y n κ hκ generates b x
  have hs : Function.Surjective c := nativeAbsoluteExteriorCoefficientStalk_surjective
    Y n κ hκ generates b x
  let f : Module.End (Y.presheaf.stalk x) (Y.presheaf.stalk x) := c.comp e.toLinearMap
  have hi : Function.Injective f :=
    Module.End.injective_of_surjective (Y.presheaf.stalk x) (Y.presheaf.stalk x)
      (f := f) (hs.comp e.surjective)
  refine ⟨?_, hs⟩
  intro v w hvw
  obtain ⟨a, rfl⟩ := e.surjective v
  obtain ⟨b, rfl⟩ := e.surjective w
  exact congrArg e (hi hvw)

/-- The actual coefficient sheaf morphism is an isomorphism. -/
theorem nativeAbsoluteExteriorCoefficientMap_isIso :
    IsIso (nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b) := by
  apply schemeModule_isIso_of_stalk_bijective Y
  intro x
  let e := structureSheafModuleStalkEquiv Y x
  have hc := nativeAbsoluteExteriorCoefficientStalk_bijective Y n κ hκ generates b frames x
  refine ⟨fun v w hvw ↦ hc.injective (congrArg e hvw), ?_⟩
  intro ζ
  obtain ⟨ξ, hξ⟩ := hc.surjective (e ζ)
  exact ⟨ξ, e.injective hξ⟩

/-- The invariant rational volume trivializes the genuine exterior sheaf. -/
def nativeAbsoluteExteriorVolumeIso : SheafOfModules.unit Y.ringCatSheaf ≅ (E) := by
  have := nativeAbsoluteExteriorCoefficientMap_isIso Y n κ hκ generates b frames
  exact (asIso (nativeAbsoluteExteriorCoefficientMap Y n κ hκ generates b)).symm

end
end Red61

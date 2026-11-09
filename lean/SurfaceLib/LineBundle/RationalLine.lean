import Red61.AlgebraicGeometry.RationalForms.ExteriorLattice
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! # Line bundles on an integral scheme through their rational realization

A `RationalLine` on a presheaf of modules records additive maps from its stalks to the function
field, compatible with germs. A generator at a point is a stalk element generating the whole
stalk, with nonzero rational value. This is a concrete form of a Cartier divisor. It is stable
under tensor product and sheafification, and it detects triviality of tensor powers.
-/

namespace SurfaceLib.LineBundle

open Red61 AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped MonoidalCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Y : Scheme.{0}} [IsIntegral Y]

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

theorem tmul_smul_smul {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] (r s : R) (a : A) (b : B) :
    (r • a) ⊗ₜ[R] (s • b) = (r * s) • (a ⊗ₜ[R] b) := by
  rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]

/-- Sections of a presheaf of modules, regarded through the underlying additive presheaf. -/
abbrev germOf (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) (U : Y.Opens) (x : Y) (hx : x ∈ U)
    (t : M.obj (op U)) : (modulePresheafAbPresheaf Y M).stalk x :=
  (modulePresheafAbPresheaf Y M).germ U x hx t

/-- The rational realization of a presheaf of modules on an integral scheme. -/
structure RationalLine (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) where
  ev (x : Y) : (modulePresheafAbPresheaf Y M).stalk x →+ Y.functionField
  ev_smul (x : Y) (a : Y.presheaf.stalk x) (ξ : (modulePresheafAbPresheaf Y M).stalk x) :
    letI := schemeModuleStalkModule Y M x
    ev x (a • ξ) = algebraMap (Y.presheaf.stalk x) Y.functionField a * ev x ξ
  ev_germ (U : Y.Opens) (x z : Y) (hx : x ∈ U) (hz : z ∈ U) (t : M.obj (op U)) :
    ev x (germOf M U x hx t) = ev z (germOf M U z hz t)

namespace RationalLine

variable {M N : PresheafOfModulesOfCommRing.{0} Y.presheaf}

/-- `c` is the rational value of a generator of the stalk at `x`. -/
def IsGenerator (F : RationalLine M) (x : Y) (c : Y.functionField) : Prop :=
  letI := schemeModuleStalkModule Y M x
  c ≠ 0 ∧ ∃ g : (modulePresheafAbPresheaf Y M).stalk x, F.ev x g = c ∧ ∀ ξ, ∃ a : Y.presheaf.stalk x, ξ = a • g


open PresheafOfModulesOfCommRing.Monoidal

theorem germ_smul' (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) (U : Y.Opens) (x : Y)
    (hx : x ∈ U) (r : Y.presheaf.obj (op U)) (t : M.obj (op U)) :
    letI := schemeModuleStalkModule Y M x
    germOf M U x hx (r • t) = Y.presheaf.germ U x hx r • germOf M U x hx t :=
  PresheafOfModules.germ_smul M x U hx r t

theorem germ_res' (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) {U V : Y.Opens} (i : V ⟶ U)
    (x : Y) (hx : x ∈ V) (t : M.obj (op U)) :
    germOf M V x hx (M.map i.op t) = germOf M U x (i.le hx) t :=
  (modulePresheafAbPresheaf Y M).germ_res_apply i x hx t

variable (F : RationalLine M) (G : RationalLine N)

/-- The value on sections of the tensor product presheaf. -/
def tensorSectionEv (x : Y) (U : Y.Opens) (hx : x ∈ U) :
    (tensorObj M N).obj (op U) →+ Y.functionField :=
  TensorProduct.liftAddHom
    { toFun := fun t ↦
        { toFun := fun s ↦ F.ev x (germOf M U x hx t) * G.ev x (germOf N U x hx s)
          map_zero' := by simp [germOf]
          map_add' := fun s s' ↦ by simp [germOf, mul_add] }
      map_zero' := by ext; simp [germOf]
      map_add' := fun t t' ↦ by ext; simp [germOf, add_mul] }
    (fun r t s ↦ by
      change F.ev x (germOf M U x hx (r • t)) * G.ev x (germOf N U x hx s) =
        F.ev x (germOf M U x hx t) * G.ev x (germOf N U x hx (r • s))
      rw [germ_smul', germ_smul', F.ev_smul, G.ev_smul]
      ring)

theorem tensorSectionEv_tmul (x : Y) (U : Y.Opens) (hx : x ∈ U) (t : M.obj (op U))
    (s : N.obj (op U)) :
    tensorSectionEv F G x U hx (t ⊗ₜ[Y.presheaf.obj (op U)] s) =
      F.ev x (germOf M U x hx t) * G.ev x (germOf N U x hx s) := rfl

theorem tensorSectionEv_restrict (x : Y) {U V : Y.Opens} (i : V ⟶ U) (hx : x ∈ V)
    (τ : (tensorObj M N).obj (op U)) :
    tensorSectionEv F G x V hx ((tensorObj M N).map i.op τ) =
      tensorSectionEv F G x U (i.le hx) τ := by
  induction τ using TensorProduct.inductionOn with
  | tmul t s =>
    rw [show (tensorObj M N).map i.op (t ⊗ₜ[Y.presheaf.obj (op U)] s) =
      (M.map i.op t) ⊗ₜ[Y.presheaf.obj (op V)] (N.map i.op s) from rfl,
      tensorSectionEv_tmul, tensorSectionEv_tmul, germ_res', germ_res']
  | add a b ha hb =>
    have hm : (tensorObj M N).map i.op (a + b) =
        (tensorObj M N).map i.op a + (tensorObj M N).map i.op b :=
      map_add ((tensorObj M N).map i.op).hom a b
    rw [hm, map_add, map_add, ha, hb]

/-- The compatible section values, as a cocone over the neighbourhoods of `x`. -/
def tensorCocone (x : Y) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ modulePresheafAbPresheaf Y (tensorObj M N)) where
  pt := AddCommGrpCat.of Y.functionField
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom (tensorSectionEv F G x U.unop.val U.unop.property)
      naturality := by
        intro U V i
        ext τ
        exact tensorSectionEv_restrict F G x ((OpenNhds.inclusion x).map i.unop) V.unop.property τ }

/-- The rational value on stalks of the tensor product presheaf. -/
def tensorEv (x : Y) : (modulePresheafAbPresheaf Y (tensorObj M N)).stalk x →+ Y.functionField :=
  (Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ modulePresheafAbPresheaf Y (tensorObj M N))
    (tensorCocone F G x)).hom

theorem tensorEv_germ (x : Y) (U : Y.Opens) (hx : x ∈ U) (τ : (tensorObj M N).obj (op U)) :
    tensorEv F G x (germOf (tensorObj M N) U x hx τ) = tensorSectionEv F G x U hx τ :=
  ConcreteCategory.congr_hom (Limits.colimit.ι_desc (tensorCocone F G x) (op ⟨U, hx⟩)) τ

/-- The rational realization of a tensor product. -/
def tensor : RationalLine (tensorObj M N) where
  ev := tensorEv F G
  ev_smul x a ξ := by
    let := schemeModuleStalkModule Y (tensorObj M N) x
    obtain ⟨U, hU, r, rfl⟩ := Y.presheaf.exists_germ_eq a
    obtain ⟨V, hVU, hV, τ, rfl⟩ := (modulePresheafAbPresheaf Y (tensorObj M N)).exists_le_germ_eq ξ hU
    have hr : Y.presheaf.germ U x hU r = Y.presheaf.germ V x hV (Y.presheaf.map (homOfLE hVU).op r) :=
      (Y.presheaf.germ_res_apply (homOfLE hVU) x hV r).symm
    change tensorEv F G x (Y.presheaf.germ U x hU r • germOf (tensorObj M N) V x hV τ) =
      algebraMap _ _ (Y.presheaf.germ U x hU r) * tensorEv F G x (germOf (tensorObj M N) V x hV τ)
    rw [hr, ← germ_smul', tensorEv_germ, tensorEv_germ]
    generalize Y.presheaf.map (homOfLE hVU).op r = r'
    induction τ using TensorProduct.inductionOn with
    | tmul t s =>
      rw [TensorProduct.smul_tmul', tensorSectionEv_tmul, tensorSectionEv_tmul, germ_smul',
        F.ev_smul]
      ring
    | add p q hp hq =>
      rw [smul_add, map_add, map_add, hp, hq]
      ring
  ev_germ U x z hx hz τ := by
    rw [tensorEv_germ, tensorEv_germ]
    induction τ using TensorProduct.inductionOn with
    | tmul t s =>
      rw [tensorSectionEv_tmul, tensorSectionEv_tmul, F.ev_germ U x z hx hz, G.ev_germ U x z hx hz]
    | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem map_map (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) {U V W : Y.Opens} (i : V ⟶ U)
    (j : W ⟶ V) (t : M.obj (op U)) : M.map j.op (M.map i.op t) = M.map (j ≫ i).op t := by
  rw [op_comp]
  exact (ConcreteCategory.congr_hom (M.presheaf.map_comp i.op j.op) t).symm

/-- A relation between germs is realized on a small neighbourhood. -/
theorem exists_nhd_smul (M : PresheafOfModulesOfCommRing.{0} Y.presheaf) (x : Y) {V U : Y.Opens}
    (hxV : x ∈ V) (hxU : x ∈ U) (t : M.obj (op V)) (t₀ : M.obj (op U)) (a : Y.presheaf.stalk x)
    (h : letI := schemeModuleStalkModule Y M x; germOf M V x hxV t = a • germOf M U x hxU t₀) :
    ∃ (W : Y.Opens) (hW : x ∈ W) (iV : W ⟶ V) (iU : W ⟶ U) (r : Y.presheaf.obj (op W)),
      M.map iV.op t = r • M.map iU.op t₀ ∧ Y.presheaf.germ W x hW r = a := by
  let := schemeModuleStalkModule Y M x
  obtain ⟨W₀, hW₀, r₀, rfl⟩ := Y.presheaf.exists_germ_eq a
  let W₁ : Y.Opens := W₀ ⊓ U
  have hW₁ : x ∈ W₁ := ⟨hW₀, hxU⟩
  let i₀ : W₁ ⟶ W₀ := homOfLE inf_le_left
  let i₁ : W₁ ⟶ U := homOfLE inf_le_right
  let r₁ : Y.presheaf.obj (op W₁) := Y.presheaf.map i₀.op r₀
  have hr₁ : Y.presheaf.germ W₁ x hW₁ r₁ = Y.presheaf.germ W₀ x hW₀ r₀ :=
    Y.presheaf.germ_res_apply i₀ x hW₁ r₀
  have he : germOf M V x hxV t = germOf M W₁ x hW₁ (r₁ • M.map i₁.op t₀) := by
    rw [h, germ_smul', germ_res', hr₁]
  obtain ⟨W, hW, iV, iW, hres⟩ := (modulePresheafAbPresheaf Y M).germ_eq x hxV hW₁ t _ he
  refine ⟨W, hW, iV, iW ≫ i₁, Y.presheaf.map iW.op r₁, ?_, ?_⟩
  · have hm : M.map iW.op (r₁ • M.map i₁.op t₀) =
        Y.presheaf.map iW.op r₁ • M.map iW.op (M.map i₁.op t₀) := M.map_smul iW.op r₁ _
    rw [← map_map, ← hm]
    exact hres
  · rw [← hr₁]
    exact Y.presheaf.germ_res_apply iW x hW r₁

theorem germ_tmul_restrict (x : Y) {U V : Y.Opens} (i : V ⟶ U) (hx : x ∈ V) (t : M.obj (op U))
    (s : N.obj (op U)) :
    germOf (tensorObj M N) V x hx ((M.map i.op t) ⊗ₜ[Y.presheaf.obj (op V)] (N.map i.op s)) =
      germOf (tensorObj M N) U x (i.le hx) (t ⊗ₜ[Y.presheaf.obj (op U)] s) :=
  germ_res' (tensorObj M N) i x hx (t ⊗ₜ[Y.presheaf.obj (op U)] s)

/-- A tensor product of generators is a generator. -/
theorem tensor_isGenerator {x : Y} {c c' : Y.functionField} (hF : F.IsGenerator x c)
    (hG : G.IsGenerator x c') : (tensor F G).IsGenerator x (c * c') := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y N x
  let := schemeModuleStalkModule Y (tensorObj M N) x
  obtain ⟨hc, g, hg, cg⟩ := hF
  obtain ⟨hc', g', hg', cg'⟩ := hG
  obtain ⟨U₁, hU₁, t₁, rfl⟩ := (modulePresheafAbPresheaf Y M).exists_germ_eq g
  obtain ⟨U₂, hU₂, s₁, rfl⟩ := (modulePresheafAbPresheaf Y N).exists_germ_eq g'
  let U₀ : Y.Opens := U₁ ⊓ U₂
  have hU₀ : x ∈ U₀ := ⟨hU₁, hU₂⟩
  let t₀ : M.obj (op U₀) := M.map (homOfLE inf_le_left : U₀ ⟶ U₁).op t₁
  let s₀ : N.obj (op U₀) := N.map (homOfLE inf_le_right : U₀ ⟶ U₂).op s₁
  have ht₀ : germOf M U₀ x hU₀ t₀ = germOf M U₁ x hU₁ t₁ := germ_res' M _ x hU₀ t₁
  have hs₀ : germOf N U₀ x hU₀ s₀ = germOf N U₂ x hU₂ s₁ := germ_res' N _ x hU₀ s₁
  refine ⟨mul_ne_zero hc hc', germOf (tensorObj M N) U₀ x hU₀ (t₀ ⊗ₜ[Y.presheaf.obj (op U₀)] s₀), ?_, ?_⟩
  · change tensorEv F G x _ = _
    rw [tensorEv_germ, tensorSectionEv_tmul, ht₀, hs₀]
    exact congrArg₂ _ hg hg'
  · intro ξ
    obtain ⟨V, hV, τ, rfl⟩ := (modulePresheafAbPresheaf Y (tensorObj M N)).exists_germ_eq ξ
    induction τ using TensorProduct.inductionOn with
    | tmul t s =>
      obtain ⟨a, ha⟩ := cg (germOf M V x hV t)
      obtain ⟨b, hb⟩ := cg' (germOf N V x hV s)
      have ha' : germOf M V x hV t = a • germOf M U₀ x hU₀ t₀ := by rw [ht₀]; exact ha
      have hb' : germOf N V x hV s = b • germOf N U₀ x hU₀ s₀ := by rw [hs₀]; exact hb
      obtain ⟨W₁, hW₁, iV₁, iU₁, r₁, h₁, hr₁⟩ := exists_nhd_smul M x hV hU₀ t t₀ a ha'
      obtain ⟨W₂, hW₂, iV₂, iU₂, r₂, h₂, hr₂⟩ := exists_nhd_smul N x hV hU₀ s s₀ b hb'
      let W : Y.Opens := W₁ ⊓ W₂
      have hW : x ∈ W := ⟨hW₁, hW₂⟩
      let j₁ : W ⟶ W₁ := homOfLE inf_le_left
      let j₂ : W ⟶ W₂ := homOfLE inf_le_right
      let iV : W ⟶ V := j₁ ≫ iV₁
      let iU : W ⟶ U₀ := j₁ ≫ iU₁
      let ρ₁ := Y.presheaf.map j₁.op r₁
      let ρ₂ := Y.presheaf.map j₂.op r₂
      have ht : M.map iV.op t = ρ₁ • M.map iU.op t₀ := by
        have h := congrArg (M.map j₁.op) h₁
        rw [map_map] at h
        rw [show iV = j₁ ≫ iV₁ from rfl, h, show iU = j₁ ≫ iU₁ from rfl, ← map_map]
        exact M.map_smul j₁.op r₁ _
      have hs : N.map iV.op s = ρ₂ • N.map iU.op s₀ := by
        have h := congrArg (N.map j₂.op) h₂
        rw [map_map] at h
        rw [show iV = j₂ ≫ iV₂ from Subsingleton.elim _ _, h,
          show iU = j₂ ≫ iU₂ from Subsingleton.elim _ _, ← map_map]
        exact N.map_smul j₂.op r₂ _
      have hρ₁ : Y.presheaf.germ W x hW ρ₁ = a := by
        rw [← hr₁]; exact Y.presheaf.germ_res_apply j₁ x hW r₁
      have hρ₂ : Y.presheaf.germ W x hW ρ₂ = b := by
        rw [← hr₂]; exact Y.presheaf.germ_res_apply j₂ x hW r₂
      refine ⟨a * b, ?_⟩
      have h1 := germ_tmul_restrict (M := M) (N := N) x iV hW t s
      have h2 := germ_tmul_restrict (M := M) (N := N) x iU hW t₀ s₀
      refine h1.symm.trans ?_
      let A₀ : M.obj (op W) := M.map iU.op t₀
      let B₀ : N.obj (op W) := N.map iU.op s₀
      have hA : (M.map iV.op t) = ρ₁ • A₀ := ht
      have hB : (N.map iV.op s) = ρ₂ • B₀ := hs
      have hτ : (M.map iV.op t) ⊗ₜ[Y.presheaf.obj (op W)] (N.map iV.op s) =
          (ρ₁ * ρ₂) • (A₀ ⊗ₜ[Y.presheaf.obj (op W)] B₀) := by
        rw [hA, hB]
        exact tmul_smul_smul _ _ _ _
      have h3 : germOf (tensorObj M N) W x hW ((ρ₁ * ρ₂) • (A₀ ⊗ₜ[Y.presheaf.obj (op W)] B₀)) =
          Y.presheaf.germ W x hW (ρ₁ * ρ₂) •
            germOf (tensorObj M N) W x hW (A₀ ⊗ₜ[Y.presheaf.obj (op W)] B₀) :=
        germ_smul' (tensorObj M N) W x hW _ _
      exact (congrArg (germOf (tensorObj M N) W x hW) hτ).trans (h3.trans (by
        rw [show germOf (tensorObj M N) W x hW (A₀ ⊗ₜ[Y.presheaf.obj (op W)] B₀) = _ from h2,
          map_mul, hρ₁, hρ₂]))
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [add_smul, ← ha, ← hb]; exact map_add _ _ _⟩

theorem generic_mem (U : Y.Opens) {x : Y} (hx : x ∈ U) : genericPoint Y ∈ U :=
  ((genericPoint_spec Y).specializes (Set.mem_univ x)).mem_open U.isOpen hx

/-- The rational value of the sheafification, computed through the presheaf stalk. -/
def sheafifyEv (F : RationalLine M) (x : Y) :
    (modulePresheafAbPresheaf Y (modulePresheafSheafification Y M).val).stalk x →+ Y.functionField :=
  letI := schemeModuleStalkModule Y M x
  letI := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
  { toFun := fun ξ ↦ F.ev x ((modulePresheafSheafificationStalkEquiv Y M x).symm ξ)
    map_zero' := by simp
    map_add' := fun a b ↦ by simp }

theorem sheafifyEv_symm (F : RationalLine M) (x : Y) (ξ) :
    letI := schemeModuleStalkModule Y M x
    letI := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
    sheafifyEv F x (modulePresheafSheafificationStalkEquiv Y M x ξ) = F.ev x ξ := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
  change F.ev x ((modulePresheafSheafificationStalkEquiv Y M x).symm
    (modulePresheafSheafificationStalkEquiv Y M x ξ)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem sheafifyEv_generic (F : RationalLine M) (U : Y.Opens) (x : Y) (hx : x ∈ U)
    (t : (modulePresheafSheafification Y M).val.obj (op U)) :
    sheafifyEv F x (germOf _ U x hx t) =
      sheafifyEv F (genericPoint Y) (germOf _ U _ (generic_mem U hx) t) := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
  let S : PresheafOfModulesOfCommRing.{0} Y.presheaf := (modulePresheafSheafification Y M).val
  obtain ⟨ξ, hξ⟩ := (modulePresheafSheafificationStalkEquiv Y M x).surjective (germOf S U x hx t)
  obtain ⟨V, hV, τ, rfl⟩ := (modulePresheafAbPresheaf Y M).exists_germ_eq ξ
  have hg : germOf S V x hV ((modulePresheafSheafificationUnit Y M).app (op V) τ) = germOf S U x hx t :=
    (modulePresheafSheafificationStalkEquiv_germ Y M x V hV τ).symm.trans hξ
  obtain ⟨W, hW, iV, iU, hres⟩ := (modulePresheafAbPresheaf Y S).germ_eq x hV hx _ t hg
  have hη : genericPoint Y ∈ W := generic_mem W hW
  have h1 : germOf S U _ (generic_mem U hx) t =
      modulePresheafSheafificationStalkEquiv Y M (genericPoint Y)
        (germOf M V _ (iV.le hη) τ) := by
    have e1 := germ_res' S iU _ hη t
    have e2 := germ_res' S iV _ hη ((modulePresheafSheafificationUnit Y M).app (op V) τ)
    refine Eq.trans ?_ (modulePresheafSheafificationStalkEquiv_germ Y M _ V (iV.le hη) τ).symm
    exact e1.symm.trans ((congrArg (germOf S W _ hη) hres.symm).trans e2)
  rw [← hξ, h1, sheafifyEv_symm, sheafifyEv_symm]
  exact F.ev_germ V _ _ _ _ τ

variable (M) in
/-- Sheafification preserves stalks, hence the rational realization. -/
def sheafify (F : RationalLine M) : RationalLine (modulePresheafSheafification Y M).val where
  ev := sheafifyEv F
  ev_smul x a ξ := by
    let := schemeModuleStalkModule Y M x
    let := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
    change F.ev x ((modulePresheafSheafificationStalkEquiv Y M x).symm (a • ξ)) =
      _ * F.ev x ((modulePresheafSheafificationStalkEquiv Y M x).symm ξ)
    rw [map_smul, F.ev_smul]
  ev_germ U x z hx hz t := (sheafifyEv_generic F U x hx t).trans (sheafifyEv_generic F U z hz t).symm

theorem sheafify_isGenerator (F : RationalLine M) {x : Y} {c : Y.functionField}
    (h : F.IsGenerator x c) : (sheafify M F).IsGenerator x c := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y (modulePresheafSheafification Y M).val x
  obtain ⟨hc, g, hg, cg⟩ := h
  refine ⟨hc, modulePresheafSheafificationStalkEquiv Y M x g, ?_, ?_⟩
  · exact (sheafifyEv_symm F x g).trans hg
  · intro ξ
    obtain ⟨a, ha⟩ := cg ((modulePresheafSheafificationStalkEquiv Y M x).symm ξ)
    refine ⟨a, ?_⟩
    rw [← map_smul, ← ha, LinearEquiv.apply_symm_apply]

theorem ev_injective (F : RationalLine M) {x : Y} {c : Y.functionField} (h : F.IsGenerator x c) :
    Function.Injective (F.ev x) := by
  let := schemeModuleStalkModule Y M x
  obtain ⟨hc, g, hg, cg⟩ := h
  intro ξ ξ' he
  obtain ⟨a, rfl⟩ := cg ξ
  obtain ⟨a', rfl⟩ := cg ξ'
  rw [F.ev_smul, F.ev_smul, hg] at he
  have ha := IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    (mul_right_cancel₀ hc he)
  rw [ha]

/-- A rational realization transported along an isomorphism of presheaves. -/
def ofHom (f : M ⟶ N) (F : RationalLine N) : RationalLine M where
  ev x := (F.ev x).comp (modulePresheafStalkMapAddHom Y M N f x)
  ev_smul x a ξ := by
    let := schemeModuleStalkModule Y M x
    let := schemeModuleStalkModule Y N x
    change F.ev x (modulePresheafStalkMapAddHom Y M N f x (a • ξ)) =
      _ * F.ev x (modulePresheafStalkMapAddHom Y M N f x ξ)
    rw [modulePresheafStalkMapAddHom_smul, F.ev_smul]
  ev_germ U x z hx hz t := by
    change F.ev x (modulePresheafStalkMapAddHom Y M N f x (germOf M U x hx t)) =
      F.ev z (modulePresheafStalkMapAddHom Y M N f z (germOf M U z hz t))
    rw [show modulePresheafStalkMapAddHom Y M N f x (germOf M U x hx t) = germOf N U x hx _ from
        modulePresheafStalkMapAddHom_germ Y M N f x U hx t,
      show modulePresheafStalkMapAddHom Y M N f z (germOf M U z hz t) = germOf N U z hz _ from
        modulePresheafStalkMapAddHom_germ Y M N f z U hz t]
    exact F.ev_germ U x z hx hz _

theorem ofHom_isGenerator (f : M ⟶ N) [IsIso f] (F : RationalLine N) {x : Y} {c : Y.functionField}
    (h : F.IsGenerator x c) : (ofHom f F).IsGenerator x c := by
  let := schemeModuleStalkModule Y M x
  let := schemeModuleStalkModule Y N x
  obtain ⟨hc, g, hg, cg⟩ := h
  have hb : Function.Bijective (modulePresheafStalkMapAddHom Y M N f x) := by
    have h2 : IsIso ((PresheafOfModules.toPresheaf
        (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map f) := Functor.map_isIso _ _
    have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map f)) :=
      Functor.map_isIso _ _
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨g', rfl⟩ := hb.2 g
  refine ⟨hc, g', hg, fun ξ ↦ ?_⟩
  obtain ⟨a, ha⟩ := cg (modulePresheafStalkMapAddHom Y M N f x ξ)
  refine ⟨a, hb.1 ?_⟩
  rw [ha, modulePresheafStalkMapAddHom_smul]

end RationalLine

/-- The `n`-th tensor power, sheafifying the presheaf tensor product at each step. -/
def tensorPower (𝓛 : Y.Modules) : ℕ → Y.Modules
  | 0 => structureSheafModule Y
  | n + 1 => modulePresheafSheafification Y
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tensorPower 𝓛 n).val 𝓛.val)

theorem unitStalk_smul (x : Y) (a : Y.presheaf.stalk x)
    (ξ : (modulePresheafAbPresheaf Y (structureSheafModule Y).val).stalk x) :
    letI := schemeModuleStalkModule Y (structureSheafModule Y).val x
    structureSheafModuleStalkEquiv Y x (a • ξ) = a * structureSheafModuleStalkEquiv Y x ξ :=
  (structureSheafModuleStalkEquiv Y x).map_smul a ξ

theorem unitStalk_germ (x : Y) (U : Y.Opens) (hx : x ∈ U) (t : (structureSheafModule Y).val.obj (op U)) :
    structureSheafModuleStalkEquiv Y x (germOf (structureSheafModule Y).val U x hx t) =
      Y.presheaf.germ U x hx t :=
  structureSheafModuleStalkEquiv_germ Y x U hx t

/-- The structure sheaf, through the inclusion of each stalk in the function field. -/
def unitLine : RationalLine (Y := Y) (structureSheafModule Y).val where
  ev x :=
    { toFun := fun ξ ↦ algebraMap (Y.presheaf.stalk x) Y.functionField
        (structureSheafModuleStalkEquiv Y x ξ)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  ev_smul x a ξ := by
    change algebraMap (Y.presheaf.stalk x) Y.functionField
      (structureSheafModuleStalkEquiv Y x _) = _
    rw [unitStalk_smul, map_mul]
    rfl
  ev_germ U x z hx hz t := by
    change algebraMap (Y.presheaf.stalk x) Y.functionField
        (structureSheafModuleStalkEquiv Y x (germOf _ U x hx t)) =
      algebraMap (Y.presheaf.stalk z) Y.functionField
        (structureSheafModuleStalkEquiv Y z (germOf _ U z hz t))
    rw [unitStalk_germ, unitStalk_germ]
    exact sectionRationalValue_eq Y U t ⟨x, hx⟩ ⟨z, hz⟩

theorem unitLine_isGenerator (x : Y) : (unitLine (Y := Y)).IsGenerator x 1 := by
  let := schemeModuleStalkModule Y (structureSheafModule Y).val x
  let E := structureSheafModuleStalkEquiv Y x
  refine ⟨one_ne_zero, E.symm 1, ?_, ?_⟩
  · change algebraMap (Y.presheaf.stalk x) Y.functionField (E (E.symm 1)) = 1
    rw [LinearEquiv.apply_symm_apply, map_one]
  · intro ξ
    refine ⟨E ξ, ?_⟩
    apply E.injective
    refine Eq.trans ?_ (unitStalk_smul x (E ξ) (E.symm 1)).symm
    rw [LinearEquiv.apply_symm_apply, mul_one]

/-- The rational realization of a tensor power. -/
def powerLine {𝓛 : Y.Modules} (F : RationalLine 𝓛.val) : (n : ℕ) → RationalLine (tensorPower 𝓛 n).val
  | 0 => unitLine
  | n + 1 => RationalLine.sheafify _ (RationalLine.tensor (powerLine F n) F)

theorem powerLine_isGenerator {𝓛 : Y.Modules} (F : RationalLine 𝓛.val) {x : Y}
    {c : Y.functionField} (h : F.IsGenerator x c) (n : ℕ) :
    (powerLine F n).IsGenerator x (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact unitLine_isGenerator x
  | succ n ih =>
    rw [pow_succ]
    exact RationalLine.sheafify_isGenerator _
      (RationalLine.tensor_isGenerator _ _ ih h)

section Trivial

variable {𝓛 : Y.Modules}

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The stalk map of a morphism from the structure sheaf multiplies by its global value. -/
theorem unitHom_stalk (f : structureSheafModule Y ⟶ 𝓛) (x : Y)
    (ξ : (modulePresheafAbPresheaf Y (structureSheafModule Y).val).stalk x) :
    letI := schemeModuleStalkModule Y 𝓛.val x
    modulePresheafStalkMapAddHom Y (structureSheafModule Y).val 𝓛.val f.val x ξ =
      structureSheafModuleStalkEquiv Y x ξ •
        germOf 𝓛.val ⊤ x trivial (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))) := by
  let := schemeModuleStalkModule Y 𝓛.val x
  obtain ⟨U, hU, a, rfl⟩ :=
    (modulePresheafAbPresheaf Y (structureSheafModule Y).val).exists_germ_eq ξ
  rw [modulePresheafStalkMapAddHom_germ]
  have hE := unitStalk_germ x U hU a
  have hsec : 𝓛.val.map (homOfLE (le_top : U ≤ ⊤)).op (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))) =
      f.val.app (op U) (1 : Y.presheaf.obj (op U)) :=
    PresheafOfModules.sections_property (𝓛.unitHomEquiv f) (homOfLE (le_top : U ≤ ⊤)).op
  have hlin : f.val.app (op U) a = (a : Y.presheaf.obj (op U)) •
      f.val.app (op U) (1 : Y.presheaf.obj (op U)) := by
    have := (f.val.app (op U)).hom.map_smul (a : Y.presheaf.obj (op U)) (1 : Y.presheaf.obj (op U))
    simpa using this
  have h1 := RationalLine.germ_smul' 𝓛.val U x hU a (f.val.app (op U) (1 : Y.presheaf.obj (op U)))
  have h2 := RationalLine.germ_res' 𝓛.val (homOfLE (le_top : U ≤ ⊤)) x hU
    (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤)))
  have h2' : germOf 𝓛.val U x hU (f.val.app (op U) (1 : Y.presheaf.obj (op U))) =
      germOf 𝓛.val ⊤ x trivial (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))) :=
    (congrArg (germOf 𝓛.val U x hU) hsec.symm).trans h2
  refine (congrArg (germOf 𝓛.val U x hU) hlin).trans (h1.trans ?_)
  rw [h2']
  exact congrArg (fun z : Y.presheaf.stalk x ↦ z • germOf 𝓛.val ⊤ x trivial
    (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤)))) hE.symm

/-- A trivialization produces one rational function comparable to all local generators. -/
theorem generators_of_trivial (ψ : structureSheafModule Y ≅ 𝓛) (F : RationalLine 𝓛.val) :
    ∃ h : Y.functionField, ∀ (x : Y) (c : Y.functionField), F.IsGenerator x c →
      ∃ u : Y.presheaf.stalk x, IsUnit u ∧
        h = algebraMap (Y.presheaf.stalk x) Y.functionField u * c := by
  let t := ψ.hom.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))
  refine ⟨F.ev (genericPoint Y) (germOf 𝓛.val ⊤ _ trivial t), fun x c hg ↦ ?_⟩
  let := schemeModuleStalkModule Y 𝓛.val x
  obtain ⟨hc, g, hgv, cg⟩ := hg
  have hsurj : Function.Surjective
      (modulePresheafStalkMapAddHom Y (structureSheafModule Y).val 𝓛.val ψ.hom.val x) := by
    have h1 : IsIso ψ.hom.val := inferInstanceAs (IsIso ((SheafOfModules.forget _).map ψ.hom))
    have h2 : IsIso ((PresheafOfModules.toPresheaf
        (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map ψ.hom.val) := Functor.map_isIso _ _
    have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map ψ.hom.val)) :=
      Functor.map_isIso _ _
    exact (ConcreteCategory.bijective_of_isIso _).2
  obtain ⟨a, ha⟩ := cg (germOf 𝓛.val ⊤ x trivial t)
  obtain ⟨ξ, hξ⟩ := hsurj g
  have hb : g = structureSheafModuleStalkEquiv Y x ξ • germOf 𝓛.val ⊤ x trivial t :=
    hξ.symm.trans (unitHom_stalk ψ.hom x ξ)
  let b := structureSheafModuleStalkEquiv Y x ξ
  have hvx : F.ev x (germOf 𝓛.val ⊤ x trivial t) =
      algebraMap (Y.presheaf.stalk x) Y.functionField a * c := by
    rw [ha, F.ev_smul, hgv]
  have hcb : c = algebraMap (Y.presheaf.stalk x) Y.functionField b *
      (algebraMap (Y.presheaf.stalk x) Y.functionField a * c) := by
    rw [← hvx, ← F.ev_smul, ← hgv]
    exact congrArg (F.ev x) hb
  have hba : b * a = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    rw [map_mul, map_one]
    apply mul_right_cancel₀ hc
    rw [one_mul, mul_assoc]
    exact hcb.symm
  refine ⟨a, IsUnit.of_mul_eq_one b (by rw [mul_comm, hba]), ?_⟩
  rw [← hvx]
  exact F.ev_germ ⊤ _ _ trivial trivial t

/-- Compatible generators with a common rational value glue to a trivialization. -/
theorem trivial_of_generators (F : RationalLine 𝓛.val) (h : Y.functionField)
    (H : ∀ x : Y, ∃ (c : Y.functionField) (u : Y.presheaf.stalk x), F.IsGenerator x c ∧ IsUnit u ∧
      h = algebraMap (Y.presheaf.stalk x) Y.functionField u * c) :
    Nonempty (structureSheafModule Y ≅ 𝓛) := by
  have hinj (x : Y) : Function.Injective (F.ev x) := by
    obtain ⟨c, u, hg, -, -⟩ := H x
    exact RationalLine.ev_injective F hg
  -- Local sections with rational value `h`.
  have hloc (x : Y) : ∃ (W : Y.Opens) (hW : x ∈ W) (t : 𝓛.val.obj (op W)),
      F.ev x (germOf 𝓛.val W x hW t) = h := by
    let := schemeModuleStalkModule Y 𝓛.val x
    obtain ⟨c, u, ⟨hc, g, hgv, cg⟩, hu, he⟩ := H x
    obtain ⟨W, hW, t, ht⟩ := (modulePresheafAbPresheaf Y 𝓛.val).exists_germ_eq (u • g)
    refine ⟨W, hW, t, ?_⟩
    change F.ev x ((modulePresheafAbPresheaf Y 𝓛.val).germ W x hW t) = h
    rw [ht, F.ev_smul, hgv, he]
  choose W hW t ht using hloc
  have hval (x z : Y) (hz : z ∈ W x) : F.ev z (germOf 𝓛.val (W x) z hz (t x)) = h :=
    (F.ev_germ (W x) z x hz (hW x) (t x)).trans (ht x)
  let G : TopCat.Sheaf Ab Y := (SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝓛
  have hcompat : TopCat.Presheaf.IsCompatible G.1 W t := by
    intro x z
    apply TopCat.Presheaf.section_ext G
    intro p hp
    have e1 := RationalLine.germ_res' 𝓛.val (Opens.infLELeft (W x) (W z)) p hp (t x)
    have e2 := RationalLine.germ_res' 𝓛.val (Opens.infLERight (W x) (W z)) p hp (t z)
    apply hinj p
    exact (congrArg (F.ev p) e1).trans ((hval x p hp.1).trans
      ((hval z p hp.2).symm.trans (congrArg (F.ev p) e2).symm))
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' W ⊤ (fun x ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hW x⟩) t hcompat
  let sec : 𝓛.val.sections := PresheafOfModules.sectionsMk
    (fun X ↦ 𝓛.val.map (homOfLE le_top : X.unop ⟶ ⊤).op s) (fun X X' g ↦ by
      refine (RationalLine.map_map 𝓛.val (homOfLE le_top : X.unop ⟶ ⊤) g.unop s).trans ?_
      congr 2)
  let f : structureSheafModule Y ⟶ 𝓛 := 𝓛.unitHomEquiv.symm sec
  have hf : f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤)) =
      𝓛.val.map (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤).op s := by
    have := SheafOfModules.unitHomEquiv_apply_coe 𝓛 f (op ⊤)
    rw [show 𝓛.unitHomEquiv f = sec from Equiv.apply_symm_apply _ _] at this
    exact this.symm
  have hgerm (x : Y) : F.ev x (germOf 𝓛.val ⊤ x trivial
      (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤)))) = h := by
    have e0 : germOf 𝓛.val ⊤ x trivial (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))) =
        germOf 𝓛.val ⊤ x trivial s :=
      (congrArg (germOf 𝓛.val ⊤ x trivial) hf).trans
        (RationalLine.germ_res' 𝓛.val (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) x trivial s)
    have e1 : germOf 𝓛.val ⊤ x trivial s = germOf 𝓛.val (W x) x (hW x) (t x) :=
      (RationalLine.germ_res' 𝓛.val (homOfLE le_top : W x ⟶ ⊤) x (hW x) s).symm.trans
        (congrArg (germOf 𝓛.val (W x) x (hW x)) (hs x))
    rw [e0, e1]
    exact ht x
  have hbij (x : Y) : Function.Bijective
      (modulePresheafStalkMapAddHom Y (structureSheafModule Y).val 𝓛.val f.val x) := by
    let := schemeModuleStalkModule Y 𝓛.val x
    obtain ⟨c, u, ⟨hc, g, hgv, cg⟩, hu, he⟩ := H x
    have hγ : germOf 𝓛.val ⊤ x trivial (f.val.app (op ⊤) (1 : Y.presheaf.obj (op ⊤))) = u • g := by
      apply hinj x
      rw [hgerm, F.ev_smul, hgv, he]
    have hmap (ξ) : modulePresheafStalkMapAddHom Y (structureSheafModule Y).val 𝓛.val f.val x ξ =
        (structureSheafModuleStalkEquiv Y x ξ * u) • g := by
      rw [unitHom_stalk, hγ, smul_smul]
    constructor
    · intro ξ ξ' hee
      rw [hmap, hmap] at hee
      have hev := congrArg (F.ev x) hee
      rw [F.ev_smul, F.ev_smul, hgv] at hev
      have h1 := mul_right_cancel₀ hc hev
      have h2 := IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField h1
      have h3 := hu.mul_left_inj.mp h2
      exact (structureSheafModuleStalkEquiv Y x).injective h3
    · intro ζ
      obtain ⟨a, rfl⟩ := cg ζ
      obtain ⟨v, rfl⟩ := hu
      refine ⟨(structureSheafModuleStalkEquiv Y x).symm (a * ↑v⁻¹), ?_⟩
      rw [hmap, LinearEquiv.apply_symm_apply]
      congr 1
      simp [mul_assoc]
  have := schemeModule_isIso_of_stalk_bijective Y f hbij
  exact ⟨asIso f⟩

end Trivial

end
end SurfaceLib.LineBundle

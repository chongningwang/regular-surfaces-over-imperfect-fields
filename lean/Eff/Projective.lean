import Eff.Quotient
import SurfaceLib.Projective.AtlasModel

/-! # The invariant quotients are projective

`S` and `Y` are the `Proj` of the homogeneous elements of the monomial coordinate ring of `X` whose
values lie in their function fields. Powers by `5ⁿ` lie in this subring. This gives the charts, the
cover of `Proj` and, through the Artin-Tate lemma, finite generation. No ample line bundle or norm
construction is used.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.AffineGluing
  AlgebraicGeometry CategoryTheory HomogeneousLocalization SurfaceLib.Projective TopologicalSpace
open scoped DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false

local notation "PD" => (ProjectiveModel.data)

abbrev HRing := MonomialProjectiveModel.homogeneousRing PD
abbrev 𝒢 : ℕ → Submodule k HRing := MonomialProjectiveModel.grading PD
abbrev evH : HRing →ₐ[k] K := MonomialProjectiveModel.evaluate PD

instance : CharP HRing 5 := charP_of_injective_algebraMap (algebraMap k HRing).injective 5

instance : ExpChar HRing 5 := .prime (by norm_num)

/-- The monomial coordinates of the vertices. -/
abbrev xVertex (i : Fin 4) : HRing := MonomialProjectiveModel.vertexElement PD i

theorem evH_xVertex_ne (i : Fin 4) : evH (xVertex i) ≠ 0 :=
  MonomialProjectiveModel.evaluate_generator_nonzero PD _

theorem xVertex_mem (i : Fin 4) : xVertex i ∈ 𝒢 1 :=
  MonomialProjectiveModel.generator_homogeneous PD _

theorem pow_mem_degree (q : ℕ) {a : HRing} (ha : a ∈ 𝒢 1) : a ^ q ∈ 𝒢 q := by
  simpa using SetLike.pow_mem_graded q ha

theorem ell_k_finite : Module.Finite ell k := Module.Finite.of_basis pBasis

section Invariant

variable {F : Type} [Field F] [Algebra ell F] (ι : F →ₐ[ell] K)

/-- The function field inside `K`. -/
abbrev fieldImage : Subfield K := (ι : F →+* K).fieldRange

/-- Elements all of whose homogeneous components have values in the function field. -/
def homAdd : AddSubmonoid HRing where
  carrier := {a | ∀ m, evH (DirectSum.decompose 𝒢 a m : HRing) ∈ fieldImage ι}
  zero_mem' m := by simp
  add_mem' {a b} ha hb m := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, map_add]
    exact add_mem (ha m) (hb m)

theorem homog_mem {m : ℕ} {a : HRing} (ha : a ∈ 𝒢 m) (he : evH a ∈ fieldImage ι) :
    a ∈ homAdd ι := by
  intro l
  by_cases h : l = m
  · subst h
    rw [DirectSum.decompose_of_mem_same 𝒢 ha]
    exact he
  · rw [DirectSum.decompose_of_mem_ne 𝒢 ha (Ne.symm h), map_zero]
    exact zero_mem _

theorem homAdd_mul {a b : HRing} (ha : a ∈ homAdd ι) (hb : b ∈ homAdd ι) : a * b ∈ homAdd ι := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒢 a, ← DirectSum.sum_support_decompose 𝒢 b,
    Finset.sum_mul_sum]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ homog_mem ι
    (SetLike.mul_mem_graded (DirectSum.decompose 𝒢 a i).property
      (DirectSum.decompose 𝒢 b j).property) ?_
  rw [map_mul]
  exact mul_mem (ha i) (hb j)

/-- The homogeneous coordinate ring of the quotient. -/
def homRing : Subalgebra ell HRing where
  __ := homAdd ι
  mul_mem' := homAdd_mul ι
  one_mem' := homog_mem ι SetLike.GradedOne.one_mem (by rw [map_one]; exact one_mem _)
  algebraMap_mem' c := by
    refine homog_mem ι (m := 0) (SetLike.algebraMap_mem_graded 𝒢 (c : k)) ?_
    change evH (algebraMap k HRing (c : k)) ∈ fieldImage ι
    rw [evH.commutes]
    exact ⟨algebraMap ell F c, ι.commutes c⟩

theorem homRing_homogeneous :
    ∀ a ∈ homRing ι, ∀ m, (DirectSum.decompose 𝒢 a m : HRing) ∈ homRing ι :=
  fun a ha m ↦ homog_mem ι (DirectSum.decompose 𝒢 a m).property (ha m)

/-- The grading of the homogeneous coordinate ring. -/
abbrev homGrading : ℕ → Submodule ell (homRing ι) := gradedPart 𝒢 (homRing ι)

instance : GradedAlgebra (homGrading ι) :=
  gradedAlgebraOfHomogeneous 𝒢 (homRing ι) (homRing_homogeneous ι)

theorem evH_mem_image (a : homRing ι) : evH a ∈ fieldImage ι := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒢 (a : HRing), map_sum]
  exact sum_mem fun i _ ↦ a.property i

/-- The value of an element of the coordinate ring in the function field. -/
def homEvFun (a : homRing ι) : F := (evH_mem_image ι a).choose

theorem ι_homEvFun (a : homRing ι) : ι (homEvFun ι a) = evH a := (evH_mem_image ι a).choose_spec

/-- Evaluation of the coordinate ring in the function field. -/
def homEv : homRing ι →ₐ[ell] F where
  toFun := homEvFun ι
  map_one' := (ι : F →+* K).injective (by simp [ι_homEvFun])
  map_zero' := (ι : F →+* K).injective (by simp [ι_homEvFun])
  map_mul' a b := (ι : F →+* K).injective (by simp [ι_homEvFun])
  map_add' a b := (ι : F →+* K).injective (by simp [ι_homEvFun])
  commutes' c := (ι : F →+* K).injective (by
    change ι (homEvFun ι (algebraMap ell (homRing ι) c)) = ι (algebraMap ell F c)
    rw [ι_homEvFun, ι.commutes]
    exact evH.commutes (c : k))

theorem ι_homEv (a : homRing ι) : ι (homEv ι a) = evH a := ι_homEvFun ι a

theorem homGrading_zero_bijective (hL : ∀ y, ι y ∈ L) :
    Function.Bijective (algebraMap ell (homGrading ι 0)) := by
  constructor
  · intro a b h
    have h' : algebraMap k HRing (a : k) = algebraMap k HRing (b : k) :=
      congrArg (fun z : homGrading ι 0 ↦ ((z : homRing ι) : HRing)) h
    exact Subtype.ext ((algebraMap k HRing).injective h')
  · intro a
    obtain ⟨r, hr⟩ := MonomialProjectiveModel.zeroGrade_surjective PD
      ⟨((a : homRing ι) : HRing), a.property⟩
    have hr' : algebraMap k HRing r = ((a : homRing ι) : HRing) := congrArg Subtype.val hr
    obtain ⟨y, hy⟩ := evH_mem_image ι (a : homRing ι)
    have hval : includeK r ∈ L := by
      have h := hL y
      rw [show ι y = evH ((a : homRing ι) : HRing) from hy, ← hr', evH.commutes] at h
      exact h
    exact ⟨⟨r, (invariant_constant_iff r).mp hval⟩, Subtype.ext (Subtype.ext hr')⟩

variable (n : ℕ)

/-- An iterate of Frobenius on the coordinate ring of `X`. -/
def frobH : HRing →+* HRing := iterateFrobenius HRing 5 n

theorem frobH_apply (x : HRing) : frobH n x = x ^ 5 ^ n := by
  rw [frobH, iterateFrobenius_def]

variable (hq : ∀ x : K, x ^ 5 ^ n ∈ fieldImage ι)

include hq in
theorem frobH_mem (b : HRing) : frobH n b ∈ homRing ι := by
  classical
  have hsum : frobH n b = ∑ j ∈ (DirectSum.decompose 𝒢 b).support,
      frobH n (DirectSum.decompose 𝒢 b j : HRing) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒢 b]
    exact map_sum _ _ _
  rw [hsum]
  refine sum_mem fun j _ ↦ ?_
  rw [frobH_apply]
  refine homog_mem ι (SetLike.pow_mem_graded (5 ^ n) (DirectSum.decompose 𝒢 b j).property) ?_
  rw [map_pow]
  exact hq _

/-- Frobenius sends the coordinate ring of `X` to that of the quotient. -/
def homFrob : HRing →+* homRing ι := (frobH n).codRestrict (homRing ι) (frobH_mem ι n hq)

theorem coe_homFrob (b : HRing) : (homFrob ι n hq b : HRing) = b ^ 5 ^ n := frobH_apply n b

theorem homCover (p : ProjectiveSpectrum (homGrading ι)) :
    ∃ i : Fin 4, homFrob ι n hq (xVertex i) ∉ p.asHomogeneousIdeal := by
  refine exists_not_mem_of_powerMap 𝒢 (homRing ι) (homFrob ι n hq) (by positivity)
    (coe_homFrob ι n hq) xVertex (fun p₀ ↦ ?_) p
  have hP : p₀ ∈ ⨆ i : Fin 4, Proj.basicOpen 𝒢 (xVertex i) := by
    rw [MonomialProjectiveModel.vertices_cover PD]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hP
  exact ⟨i, hi⟩

theorem homVertex_mem (i : Fin 4) : homFrob ι n hq (xVertex i) ∈ homGrading ι (5 ^ n) := by
  rw [mem_gradedPart, coe_homFrob]
  exact pow_mem_degree _ (xVertex_mem i)

theorem ι_homEv_frob (b : HRing) : ι (homEv ι (homFrob ι n hq b)) = evH b ^ 5 ^ n := by
  rw [ι_homEv, coe_homFrob, map_pow]

variable (D : PrincipalAtlas ell F) (idx : D.Index → Fin 4) (hidx : Function.Surjective idx)
  (hD : ∀ i y, y ∈ D.ring i ↔ ι y ∈ Red61.Contraction.ring (idx i))

include hD in
theorem hom_away_mem (i : D.Index) (m : ℕ) (a : homRing ι) (ha : a ∈ homGrading ι (m • 5 ^ n)) :
    homEv ι a / homEv ι (homFrob ι n hq (xVertex (idx i))) ^ m ∈ D.ring i := by
  rw [hD]
  have ha' : (a : HRing) ∈ 𝒢 ((5 ^ n * m) • 1) := by
    have h : (a : HRing) ∈ 𝒢 (m • 5 ^ n) := ha
    convert h using 2
    simp [mul_comm]
  have hmem := MonomialProjectiveModel.vertexEvaluation_mem PD (idx i)
    (Away.mk 𝒢 (xVertex_mem (idx i)) (5 ^ n * m) (a : HRing) ha')
  rw [MonomialProjectiveModel.vertexEvaluation, MonomialProjectiveModel.awayEvaluation_mk] at hmem
  have he : ι (homEv ι a / homEv ι (homFrob ι n hq (xVertex (idx i))) ^ m) =
      evH a / evH (xVertex (idx i)) ^ (5 ^ n * m) := by
    rw [map_div₀, map_pow, ι_homEv, ι_homEv_frob, pow_mul]
  rw [he]
  exact hmem

include hD in
theorem hom_away_surj (i : D.Index) (y : F) (hy : y ∈ D.ring i) :
    ∃ (m : ℕ) (a : homRing ι), a ∈ homGrading ι (m • 5 ^ n) ∧
      y = homEv ι a / homEv ι (homFrob ι n hq (xVertex (idx i))) ^ m := by
  rw [hD] at hy
  rw [← show _ = Red61.Contraction.ring (idx i) from
    MonomialProjectiveModel.vertexEvaluation_range PD (idx i)] at hy
  obtain ⟨z, hz⟩ := hy
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒢 (xVertex_mem (idx i)) z
  change MonomialProjectiveModel.vertexEvaluation PD (idx i) _ = _ at hz
  rw [MonomialProjectiveModel.vertexEvaluation, MonomialProjectiveModel.awayEvaluation_mk] at hz
  have hne := evH_xVertex_ne (idx i)
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero n (by norm_num : (5 : ℕ) ≠ 0))
  have hmem : a * xVertex (idx i) ^ (r * m) ∈ 𝒢 (m • 5 ^ n) := by
    have h := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded (r * m) (xVertex_mem (idx i)))
    convert h using 2
    simp only [smul_eq_mul, hr]
    ring
  have hval : evH (a * xVertex (idx i) ^ (r * m)) = ι y * (evH (xVertex (idx i)) ^ 5 ^ n) ^ m := by
    rw [map_mul, map_pow, ← hz, hr]
    field_simp
    ring
  have hy' : a * xVertex (idx i) ^ (r * m) ∈ homRing ι :=
    homog_mem ι (m := m • 5 ^ n) hmem (by
      rw [hval]
      exact mul_mem ⟨y, rfl⟩ (pow_mem (hq _) m))
  refine ⟨m, ⟨_, hy'⟩, hmem, (ι : F →+* K).injective ?_⟩
  change ι y = ι (_ / _)
  rw [map_div₀, map_pow, ι_homEv, ι_homEv_frob]
  change ι y = evH (a * xVertex (idx i) ^ (r * m)) / _
  rw [hval, mul_div_cancel_right₀]
  exact pow_ne_zero _ (pow_ne_zero _ hne)

/-- The vertices of `X` in degree one give vertices of the quotient in degree `5ⁿ`. -/
def homModel : AtlasModel (R := ell) (F := F) (A := homRing ι) D (homGrading ι) where
  ev := homEv ι
  ev_injective {m a b} ha hb h := Subtype.ext
    (MonomialProjectiveModel.evaluate_injective_homogeneous PD ha hb
      (by rw [← ι_homEv ι a, ← ι_homEv ι b, h]))
  d := 5 ^ n
  d_pos := by positivity
  x i := homFrob ι n hq (xVertex (idx i))
  x_mem i := homVertex_mem ι n hq (idx i)
  x_ne i h := pow_ne_zero (5 ^ n) (evH_xVertex_ne (idx i)) (by
    rw [← ι_homEv_frob ι n hq, h, map_zero])
  away_mem := hom_away_mem ι n hq D idx hD
  away_surj := hom_away_surj ι n hq D idx hD
  cover p := by
    obtain ⟨i, hi⟩ := homCover ι n hq p
    obtain ⟨j, rfl⟩ := hidx i
    exact ⟨j, hi⟩

include hq hidx hD in
/-- A principal atlas of invariants of the charts of `X`, in a function field containing all
`5ⁿ`-th powers, is projective over `ell`. -/
theorem isProjectiveOver_of_invariant (hL : ∀ y, ι y ∈ L) : IsProjectiveOver ell D.toBase := by
  have := ell_k_finite
  have h : Algebra.FiniteType ell HRing :=
    Algebra.FiniteType.trans (S := k) inferInstance inferInstance
  exact ⟨homRing ι, inferInstance, inferInstance, homGrading ι, inferInstance,
    (homModel ι n hq D idx hidx hD).iso,
    finiteType_of_pow_mem (homRing ι) (homFrob ι n hq) (by positivity) (coe_homFrob ι n hq),
    homGrading_zero_bijective ι hL, (homModel ι n hq D idx hidx hD).iso_over_base⟩

end Invariant

/-- `Y` is projective over `ell`, with no classical input. -/
theorem y_projective : IsProjectiveOver ell yToBase :=
  isProjectiveOver_of_invariant ((IsScalarTower.toAlgHom ell L K).comp (IsScalarTower.toAlgHom ell M L))
    2 (fun x ↦ ⟨⟨_, fifth_power_in_M ⟨x ^ 5, field_fifth_power_invariant x⟩⟩, by
      change (x ^ 5) ^ 5 = x ^ 5 ^ 2
      ring⟩) yAtlas id Function.surjective_id (fun _ _ ↦ Iff.rfl) (fun y ↦ (y : L).property)

/-- `S` is projective over `ell`, with no classical input. -/
theorem s_projective : IsProjectiveOver ell sToBase :=
  isProjectiveOver_of_invariant (IsScalarTower.toAlgHom ell L K) 1
    (fun x ↦ ⟨⟨x ^ 5, field_fifth_power_invariant x⟩, by
      change x ^ 5 = x ^ 5 ^ 1
      rw [pow_one]⟩) quotientAtlas id Function.surjective_id (fun _ _ ↦ Iff.rfl) (fun y ↦ y.property)

end
end Eff

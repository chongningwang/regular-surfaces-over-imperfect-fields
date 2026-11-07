import Eff.Quotient
import SurfaceLib.Projective.AtlasModel

/-! # The second quotient is projective

`Y` is the `Proj` of the homogeneous elements of the monomial coordinate ring of `X` whose values
lie in the function field `M` of `Y`. Twenty-fifth powers lie in this subring. This gives the charts,
the cover of `Proj` and, through the Artin-Tate lemma, finite generation. No ample line bundle or
norm construction is used.
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

/-- The function field of `Y` inside `K`. -/
def MK : Subfield K := M.map L.subtype

theorem pow25_mem_MK (x : K) : x ^ 25 ∈ MK :=
  ⟨_, fifth_power_in_M ⟨x ^ 5, field_fifth_power_invariant x⟩, by
    change (x ^ 5) ^ 5 = x ^ 25
    ring⟩

theorem coe_mem_MK (y : M) : ((y : L) : K) ∈ MK := ⟨y, y.property, rfl⟩

theorem mem_L_of_mem_MK {x : K} (hx : x ∈ MK) : x ∈ L := by
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

theorem mem_M_of_mem_MK {x : K} (hx : x ∈ MK) : (⟨x, mem_L_of_mem_MK hx⟩ : L) ∈ M := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact hy

def toM {x : K} (hx : x ∈ MK) : M := ⟨⟨x, mem_L_of_mem_MK hx⟩, mem_M_of_mem_MK hx⟩

/-- Elements all of whose homogeneous components have values in `M`. -/
def yAdd : AddSubmonoid HRing where
  carrier := {a | ∀ n, evH (DirectSum.decompose 𝒢 a n : HRing) ∈ MK}
  zero_mem' n := by simp
  add_mem' {a b} ha hb n := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, map_add]
    exact add_mem (ha n) (hb n)

theorem homog_mem {n : ℕ} {a : HRing} (ha : a ∈ 𝒢 n) (he : evH a ∈ MK) : a ∈ yAdd := by
  intro m
  by_cases h : m = n
  · subst h
    rw [DirectSum.decompose_of_mem_same 𝒢 ha]
    exact he
  · rw [DirectSum.decompose_of_mem_ne 𝒢 ha (Ne.symm h), map_zero]
    exact zero_mem _

theorem yAdd_mul {a b : HRing} (ha : a ∈ yAdd) (hb : b ∈ yAdd) : a * b ∈ yAdd := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒢 a, ← DirectSum.sum_support_decompose 𝒢 b,
    Finset.sum_mul_sum]
  refine sum_mem fun i _ ↦ sum_mem fun j _ ↦ homog_mem
    (SetLike.mul_mem_graded (DirectSum.decompose 𝒢 a i).property
      (DirectSum.decompose 𝒢 b j).property) ?_
  rw [map_mul]
  exact mul_mem (ha i) (hb j)

/-- The homogeneous coordinate ring of `Y`. -/
def yRing : Subalgebra ell HRing where
  __ := yAdd
  mul_mem' := yAdd_mul
  one_mem' := homog_mem SetLike.GradedOne.one_mem (by rw [map_one]; exact one_mem _)
  algebraMap_mem' c := by
    refine homog_mem (n := 0) (SetLike.algebraMap_mem_graded 𝒢 (c : k)) ?_
    change evH (algebraMap k HRing (c : k)) ∈ MK
    rw [evH.commutes]
    exact coe_mem_MK (algebraMap ell M c)

theorem yRing_homogeneous : ∀ a ∈ yRing, ∀ n, (DirectSum.decompose 𝒢 a n : HRing) ∈ yRing :=
  fun a ha n ↦ homog_mem (DirectSum.decompose 𝒢 a n).property (ha n)

/-- The grading of the homogeneous coordinate ring. -/
abbrev yGrading : ℕ → Submodule ell yRing := gradedPart 𝒢 yRing

instance : GradedAlgebra yGrading := gradedAlgebraOfHomogeneous 𝒢 yRing yRing_homogeneous

instance : CharP HRing 5 := charP_of_injective_algebraMap (algebraMap k HRing).injective 5

instance : ExpChar HRing 5 := .prime (by norm_num)

/-- The second Frobenius of the coordinate ring of `X`. -/
def yPhiFull : HRing →+* HRing := iterateFrobenius HRing 5 2

theorem yPhiFull_apply (x : HRing) : yPhiFull x = x ^ 25 := by
  have h : (5 : ℕ) ^ 2 = 25 := by norm_num
  rw [yPhiFull, iterateFrobenius_def, h]

theorem yPhiFull_mem (b : HRing) : yPhiFull b ∈ yRing := by
  classical
  have hsum : yPhiFull b = ∑ j ∈ (DirectSum.decompose 𝒢 b).support,
      yPhiFull (DirectSum.decompose 𝒢 b j : HRing) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒢 b]
    exact map_sum _ _ _
  rw [hsum]
  refine sum_mem fun j _ ↦ ?_
  rw [yPhiFull_apply]
  refine homog_mem (SetLike.pow_mem_graded 25 (DirectSum.decompose 𝒢 b j).property) ?_
  rw [map_pow]
  exact pow25_mem_MK _

theorem pow25_mem (b : HRing) : b ^ 25 ∈ yRing := yPhiFull_apply b ▸ yPhiFull_mem b

/-- The second Frobenius sends the coordinate ring of `X` to that of `Y`. -/
def yCoordFrob : HRing →+* yRing := yPhiFull.codRestrict yRing yPhiFull_mem

theorem coe_yCoordFrob (b : HRing) : (yCoordFrob b : HRing) = b ^ 25 := yPhiFull_apply b

/-- The monomial coordinates of the vertices. -/
abbrev xVertex (i : Fin 4) : HRing := MonomialProjectiveModel.vertexElement ProjectiveModel.data i

theorem yCover (p : ProjectiveSpectrum yGrading) :
    ∃ i : Fin 4, yCoordFrob (xVertex i) ∉ p.asHomogeneousIdeal := by
  refine exists_not_mem_of_powerMap 𝒢 yRing yCoordFrob (by norm_num) coe_yCoordFrob xVertex (fun p₀ ↦ ?_) p
  have hP : p₀ ∈ ⨆ i : Fin 4, Proj.basicOpen 𝒢 (xVertex i) := by
    rw [MonomialProjectiveModel.vertices_cover PD]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hP
  exact ⟨i, hi⟩

theorem evH_mem_MK (a : yRing) : evH a ∈ MK := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒢 (a : HRing), map_sum]
  exact sum_mem fun i _ ↦ a.property i

/-- Evaluation of the coordinate ring of `Y` in its function field. -/
def yEv : yRing →ₐ[ell] M where
  toFun a := toM (evH_mem_MK a)
  map_one' := Subtype.ext (Subtype.ext (map_one evH))
  map_zero' := Subtype.ext (Subtype.ext (map_zero evH))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul evH (a : HRing) b))
  map_add' a b := Subtype.ext (Subtype.ext (map_add evH (a : HRing) b))
  commutes' c := Subtype.ext (Subtype.ext (evH.commutes (c : k)))

theorem coe_yEv (a : yRing) : ((yEv a : L) : K) = evH a := rfl

theorem mem_yAtlas_ring (i : Fin 4) (y : M) :
    y ∈ yAtlas.ring i ↔ ((y : L) : K) ∈ Red61.Contraction.ring i := Iff.rfl

theorem evH_xVertex_ne (i : Fin 4) : evH (xVertex i) ≠ 0 :=
  MonomialProjectiveModel.evaluate_generator_nonzero PD _

theorem xVertex_mem (i : Fin 4) : xVertex i ∈ 𝒢 1 :=
  MonomialProjectiveModel.generator_homogeneous PD _

theorem coe_yEv_frob (b : HRing) : ((yEv (yCoordFrob b) : L) : K) = evH b ^ 25 := by
  rw [coe_yEv, coe_yCoordFrob, map_pow]

theorem pow_mem_degree (q : ℕ) {a : HRing} (ha : a ∈ 𝒢 1) : a ^ q ∈ 𝒢 q := by
  simpa using SetLike.pow_mem_graded q ha

theorem yVertex_mem (i : Fin 4) : yCoordFrob (xVertex i) ∈ yGrading 25 := by
  rw [mem_gradedPart, coe_yCoordFrob]
  exact pow_mem_degree 25 (xVertex_mem i)

/-- The vertices of `X` in degree one give vertices of `Y` in degree 25. -/
def yModel : AtlasModel (R := ell) (F := M) (A := yRing) yAtlas yGrading where
  ev := yEv
  ev_injective {n a b} ha hb h := Subtype.ext
    (MonomialProjectiveModel.evaluate_injective_homogeneous PD ha hb
      (congrArg (fun y : M ↦ ((y : L) : K)) h))
  d := 25
  d_pos := by norm_num
  x i := yCoordFrob (xVertex i)
  x_mem := yVertex_mem
  x_ne i h := by
    have h' := congrArg (fun y : M ↦ ((y : L) : K)) h
    simp only [coe_yEv_frob] at h'
    exact pow_ne_zero 25 (evH_xVertex_ne i) h'
  away_mem i n a ha := by
    rw [mem_yAtlas_ring]
    have ha' : (a : HRing) ∈ 𝒢 ((25 * n) • 1) := by
      have h : (a : HRing) ∈ 𝒢 (n • 25) := ha
      convert h using 2
      simp [mul_comm]
    have hmem := MonomialProjectiveModel.vertexEvaluation_mem PD i
      (Away.mk 𝒢 (xVertex_mem i) (25 * n) (a : HRing) ha')
    rw [MonomialProjectiveModel.vertexEvaluation, MonomialProjectiveModel.awayEvaluation_mk] at hmem
    have he : (((yEv a / yEv (yCoordFrob (xVertex i)) ^ n : M) : L) : K) =
        evH a / evH (xVertex i) ^ (25 * n) := by
      push_cast
      rw [coe_yEv, coe_yEv_frob, pow_mul]
    rw [he]
    exact hmem
  away_surj i y hy := by
    rw [mem_yAtlas_ring] at hy
    rw [← show _ = Red61.Contraction.ring i from
      MonomialProjectiveModel.vertexEvaluation_range PD i] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒢 (xVertex_mem i) z
    change MonomialProjectiveModel.vertexEvaluation PD i _ = _ at hz
    rw [MonomialProjectiveModel.vertexEvaluation, MonomialProjectiveModel.awayEvaluation_mk] at hz
    have hne := evH_xVertex_ne i
    have hmem : a * xVertex i ^ (24 * n) ∈ 𝒢 (n * 25) := by
      have h := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded (24 * n) (xVertex_mem i))
      convert h using 2
      simp only [smul_eq_mul]
      ring
    have hval : evH (a * xVertex i ^ (24 * n)) = ((y : L) : K) * (evH (xVertex i) ^ 25) ^ n := by
      rw [map_mul, map_pow, ← hz]
      field_simp
      ring
    have hy' : a * xVertex i ^ (24 * n) ∈ yRing :=
      homog_mem hmem (by
        rw [hval]
        exact mul_mem (coe_mem_MK y) (pow_mem (pow25_mem_MK _) n))
    have hmem' : a * xVertex i ^ (24 * n) ∈ 𝒢 (n • 25) := by simpa [smul_eq_mul] using hmem
    refine ⟨n, ⟨_, hy'⟩, hmem', ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have he : (((yEv ⟨_, hy'⟩ / yEv (yCoordFrob (xVertex i)) ^ n : M) : L) : K) =
        evH (a * xVertex i ^ (24 * n)) / (evH (xVertex i) ^ 25) ^ n := by
      push_cast
      rw [coe_yEv, coe_yEv_frob]
    refine Eq.trans ?_ he.symm
    rw [hval]
    field_simp
  cover p := yCover p

theorem ell_k_finite : Module.Finite ell k := Module.Finite.of_basis pBasis

theorem yRing_finiteType : Algebra.FiniteType ell yRing := by
  have := ell_k_finite
  have h : Algebra.FiniteType ell HRing :=
    Algebra.FiniteType.trans (S := k) inferInstance inferInstance
  exact finiteType_of_pow_mem yRing yCoordFrob (by norm_num) coe_yCoordFrob

theorem yGrading_zero_bijective : Function.Bijective (algebraMap ell (yGrading 0)) := by
  constructor
  · intro a b h
    have h' : algebraMap k HRing (a : k) = algebraMap k HRing (b : k) :=
      congrArg (fun z : yGrading 0 ↦ ((z : yRing) : HRing)) h
    exact Subtype.ext ((algebraMap k HRing).injective h')
  · intro a
    obtain ⟨r, hr⟩ := MonomialProjectiveModel.zeroGrade_surjective PD
      ⟨((a : yRing) : HRing), a.property⟩
    have hr' : algebraMap k HRing r = ((a : yRing) : HRing) := congrArg Subtype.val hr
    have hval : includeK r ∈ MK := by
      have h := evH_mem_MK (a : yRing)
      rw [← hr', evH.commutes] at h
      exact h
    have hell : r ∈ ell := (invariant_constant_iff r).mp (mem_L_of_mem_MK hval)
    refine ⟨⟨r, hell⟩, Subtype.ext (Subtype.ext hr')⟩

/-- `Y` is projective over `ell`, with no classical input. -/
theorem y_projective : IsProjectiveOver ell yToBase :=
  ⟨yRing, inferInstance, inferInstance, yGrading, inferInstance, yModel.iso, yRing_finiteType,
    yGrading_zero_bijective, yModel.iso_over_base⟩

end
end Eff

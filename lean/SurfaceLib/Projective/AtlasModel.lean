import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Red61.AlgebraicGeometry.Atlas

/-! # Identifying a principal atlas with a Proj

A homogeneous subalgebra of a graded ring is graded. A graded algebra evaluated in the ambient field
of a principal atlas, with one homogeneous element for each chart, identifies the glued scheme with
its `Proj` as soon as the degree-zero localizations are the chart rings and the elements cover `Proj`.
The argument is the one in `Red61/Surface/Projective.lean`, without the monomial hypotheses.
-/

namespace SurfaceLib.Projective

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  HomogeneousLocalization TopologicalSpace
open scoped DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Homogeneous

variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
  [Algebra R A] [IsScalarTower R S A] (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
  (B : Subalgebra R A)

/-- The grading induced on a subalgebra. -/
def gradedPart (n : ℕ) : Submodule R B :=
  ((𝒜 n).restrictScalars R).comap B.val.toLinearMap

theorem mem_gradedPart {n : ℕ} {a : B} : a ∈ gradedPart 𝒜 B n ↔ (a : A) ∈ 𝒜 n := Iff.rfl

instance : SetLike.GradedMonoid (gradedPart 𝒜 B) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem _ _ _ _ ha hb := SetLike.mul_mem_graded (A := 𝒜) ha hb

/-- The inclusion of graded pieces. -/
def partToGrade (n : ℕ) : gradedPart 𝒜 B n →+ 𝒜 n where
  toFun x := ⟨((x : B) : A), x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_partToGrade (x : ⨁ n, gradedPart 𝒜 B n) :
    DirectSum.coeAddMonoidHom 𝒜 (DirectSum.map (partToGrade 𝒜 B) x) =
      ((DirectSum.coeAddMonoidHom (gradedPart 𝒜 B) x : B) : A) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [partToGrade]
  | add a b ha hb => simp [map_add, ha, hb]

variable (hB : ∀ a ∈ B, ∀ n, (DirectSum.decompose 𝒜 a n : A) ∈ B)

include hB in
theorem isInternal_gradedPart : DirectSum.IsInternal (gradedPart 𝒜 B) := by
  classical
  constructor
  · intro x y hxy
    have hi : Function.Injective (DirectSum.coeAddMonoidHom 𝒜) :=
      (DirectSum.Decomposition.isInternal 𝒜).injective
    have hm : DirectSum.map (partToGrade 𝒜 B) x = DirectSum.map (partToGrade 𝒜 B) y := by
      apply hi
      rw [coe_partToGrade, coe_partToGrade, hxy]
    ext n
    have := congrArg (fun z : ⨁ n, 𝒜 n ↦ ((z n : 𝒜 n) : A)) hm
    simpa [partToGrade] using this
  · intro a
    let z : ⨁ n, gradedPart 𝒜 B n :=
      ∑ n ∈ (DirectSum.decompose 𝒜 (a : A)).support,
        DirectSum.of (fun n ↦ gradedPart 𝒜 B n) n
          ⟨⟨DirectSum.decompose 𝒜 (a : A) n, hB a a.property n⟩,
            (DirectSum.decompose 𝒜 (a : A) n).property⟩
    refine ⟨z, Subtype.ext ?_⟩
    simp only [z, map_sum, DirectSum.coeAddMonoidHom_of, AddSubmonoidClass.coe_finset_sum]
    exact DirectSum.sum_support_decompose 𝒜 (a : A)

/-- A homogeneous subalgebra of a graded algebra is graded. -/
@[reducible] def gradedAlgebraOfHomogeneous : GradedAlgebra (gradedPart 𝒜 B) :=
  { (inferInstance : SetLike.GradedMonoid (gradedPart 𝒜 B)),
    (isInternal_gradedPart 𝒜 B hB).chooseDecomposition with }

theorem coe_decompose_gradedPart [GradedAlgebra (gradedPart 𝒜 B)] (a : B) (n : ℕ) :
    (((DirectSum.decompose (gradedPart 𝒜 B) a n : gradedPart 𝒜 B n) : B) : A) =
      DirectSum.decompose 𝒜 (a : A) n := by
  have h : DirectSum.map (partToGrade 𝒜 B) (DirectSum.decompose (gradedPart 𝒜 B) a) =
      DirectSum.decompose 𝒜 (a : A) := by
    apply (DirectSum.Decomposition.isInternal 𝒜).injective
    rw [coe_partToGrade]
    change (((DirectSum.decompose (gradedPart 𝒜 B)).symm
        (DirectSum.decompose (gradedPart 𝒜 B) a) : B) : A) =
      (DirectSum.decompose 𝒜).symm (DirectSum.decompose 𝒜 (a : A))
    simp
  rw [← h]
  rfl

/-- A power map that is a ring homomorphism commutes with homogeneous components. -/
theorem decompose_powerMap (φ : A →+* A) {q : ℕ} (hq : 0 < q) (hφ : ∀ a, φ a = a ^ q)
    (r : A) (i : ℕ) :
    (DirectSum.decompose 𝒜 (φ r) (q * i) : A) = φ (DirectSum.decompose 𝒜 r i : A) := by
  classical
  have hmem (j : ℕ) : φ (DirectSum.decompose 𝒜 r j : A) ∈ 𝒜 (q * j) := by
    rw [hφ]
    simpa [smul_eq_mul] using SetLike.pow_mem_graded q (DirectSum.decompose 𝒜 r j).property
  have hsum : φ r = ∑ j ∈ (DirectSum.decompose 𝒜 r).support, φ (DirectSum.decompose 𝒜 r j : A) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 r]
    exact map_sum _ _ _
  rw [hsum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same 𝒜 (hmem i)
  · intro j _ hj
    exact DirectSum.decompose_of_mem_ne 𝒜 (hmem j)
      fun h ↦ hj (Nat.eq_of_mul_eq_mul_left hq h)
  · intro hi
    have h0 : (DirectSum.decompose 𝒜 r i : A) = 0 := by simpa using hi
    rw [h0, map_zero]
    simp

/-- A cover of `Proj` by principal opens descends along a power map into a homogeneous subalgebra. -/
theorem exists_not_mem_of_powerMap [GradedAlgebra (gradedPart 𝒜 B)] (φ : A →+* B) {q : ℕ}
    (hq : 0 < q) (hφ : ∀ a, (φ a : A) = a ^ q) {ι : Type*} (x : ι → A)
    (hx : ∀ p : ProjectiveSpectrum 𝒜, ∃ i, x i ∉ p.asHomogeneousIdeal)
    (p : ProjectiveSpectrum (gradedPart 𝒜 B)) : ∃ i, φ (x i) ∉ p.asHomogeneousIdeal := by
  let I := p.asHomogeneousIdeal.toIdeal
  let J : Ideal A := I.comap φ
  have hJ : Ideal.IsHomogeneous 𝒜 J := by
    intro i r hr
    have h := p.asHomogeneousIdeal.isHomogeneous (q * i) (show φ r ∈ I from hr)
    have he : (DirectSum.decompose (gradedPart 𝒜 B) (φ r) (q * i) : B) =
        φ (DirectSum.decompose 𝒜 r i : A) := by
      apply Subtype.ext
      rw [coe_decompose_gradedPart]
      exact decompose_powerMap 𝒜 ((B.val : B →+* A).comp φ) hq hφ r i
    change φ (DirectSum.decompose 𝒜 r i : A) ∈ I
    rw [← he]
    exact h
  have hprime : J.IsPrime := Ideal.comap_isPrime φ I
  have hnot : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (⟨J, hJ⟩ : HomogeneousIdeal 𝒜) := by
    intro hle
    apply p.not_irrelevant_le
    intro a ha
    have ha0 : (a : A) ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply, ← coe_decompose_gradedPart 𝒜 B]
      have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp ha
      rw [GradedRing.proj_apply] at h0
      rw [h0]
      rfl
    have hm : φ (a : A) ∈ I := hle ha0
    have heq : φ (a : A) = a ^ q := Subtype.ext (by simp [hφ])
    rw [heq] at hm
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance q hm
  obtain ⟨i, hi⟩ := hx ⟨⟨J, hJ⟩, hprime, hnot⟩
  exact ⟨i, hi⟩

end Homogeneous

/-- A subalgebra containing a fixed power of every element inherits finite generation. -/
theorem finiteType_of_pow_mem {R A : Type} [CommRing R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (B : Subalgebra R A) (φ : A → B) {q : ℕ} (hq : 0 < q)
    (hφ : ∀ a, (φ a : A) = a ^ q) : Algebra.FiniteType R B := by
  have hint : Algebra.IsIntegral B A :=
    ⟨fun a ↦ IsIntegral.of_pow hq (hφ a ▸ isIntegral_algebraMap (x := φ a))⟩
  have hft : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType R B A
  have hfin : Module.Finite B A := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg (A := R) (B := B) (C := A) Algebra.FiniteType.out hfin.1
    Subtype.val_injective⟩

/-- The structure morphism of `Proj` over the field in degree zero. -/
def projBase {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] : Proj 𝒜 ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

/-- A scheme over a field is projective when it is the `Proj` of a finitely generated graded
algebra whose degree-zero part is the field. -/
def IsProjectiveOver (R : Type) [Field R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (𝒜 : ℕ → Submodule R A) (_ : GradedAlgebra 𝒜)
    (e : X ≅ Proj 𝒜), Algebra.FiniteType R A ∧ Function.Bijective (algebraMap R (𝒜 0)) ∧
      e.hom ≫ projBase 𝒜 = f

variable {R F A : Type} [Field R] [Field F] [Algebra R F] [CommRing A] [Algebra R A]

/-- A graded algebra realizing a principal atlas. -/
structure AtlasModel (D : PrincipalAtlas R F) (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] where
  ev : A →ₐ[R] F
  ev_injective : ∀ {n : ℕ} {a b : A}, a ∈ 𝒜 n → b ∈ 𝒜 n → ev a = ev b → a = b
  d : ℕ
  d_pos : 0 < d
  x : D.Index → A
  x_mem : ∀ i, x i ∈ 𝒜 d
  x_ne : ∀ i, ev (x i) ≠ 0
  away_mem : ∀ i n a, a ∈ 𝒜 (n • d) → ev a / ev (x i) ^ n ∈ D.ring i
  away_surj : ∀ i, ∀ y ∈ D.ring i, ∃ n a, a ∈ 𝒜 (n • d) ∧ y = ev a / ev (x i) ^ n
  cover : ∀ p : ProjectiveSpectrum 𝒜, ∃ i, x i ∉ p.asHomogeneousIdeal

namespace AtlasModel

variable {D : PrincipalAtlas R F} {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (Q : AtlasModel D 𝒜)

def awayEval (f : A) (hf : Q.ev f ≠ 0) : Away 𝒜 f →+* F :=
  (Localization.awayLift Q.ev.toRingHom f (isUnit_iff_ne_zero.mpr hf)).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

theorem awayEval_mk {f : A} (hf : Q.ev f ≠ 0) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    Q.awayEval f hf (Away.mk 𝒜 hd n a ha) = Q.ev a / Q.ev f ^ n := by
  change Localization.awayLift Q.ev.toRingHom f (isUnit_iff_ne_zero.mpr hf)
    (Localization.mk a ⟨f ^ n, n, rfl⟩) = _
  simpa only [div_eq_mul_inv, inv_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    Localization.awayLift_mk Q.ev.toRingHom f a (Q.ev f)⁻¹ (mul_inv_cancel₀ hf) n

theorem awayEval_algebraMap (f : A) (hf : Q.ev f ≠ 0) (c : R) :
    Q.awayEval f hf (fromZeroRingHom 𝒜 (Submonoid.powers f) (algebraMap R (𝒜 0) c)) =
      algebraMap R F c := by
  change Localization.awayLift Q.ev.toRingHom f (isUnit_iff_ne_zero.mpr hf)
    (Localization.mk (algebraMap R A c) 1) = _
  rw [Localization.mk_one_eq_algebraMap, Localization.awayLift, IsLocalization.Away.lift_eq]
  exact Q.ev.commutes c

theorem awayEval_injective {f : A} (hf : Q.ev f ≠ 0) {d : ℕ} (hd : f ∈ 𝒜 d) :
    Function.Injective (Q.awayEval f hf) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd x
  rw [Q.awayEval_mk] at hx
  have he : a = 0 := Q.ev_injective ha (zero_mem _) (by
    rw [map_zero]
    exact (div_eq_zero_iff.mp hx).resolve_right (pow_ne_zero _ hf))
  subst a
  exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl

theorem awayEval_awayMap {f g x : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (hf0 : Q.ev f ≠ 0) (hx0 : Q.ev x ≠ 0) (a : Away 𝒜 f) :
    Q.awayEval x hx0 (awayMap 𝒜 hg hx a) = Q.awayEval f hf0 a := by
  have hg0 : Q.ev g ≠ 0 := by
    intro h
    apply hx0
    rw [hx, map_mul, h, mul_zero]
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf a
  rw [awayMap_mk, Q.awayEval_mk, Q.awayEval_mk, hx, map_mul, map_mul, map_pow, mul_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero n hg0)

abbrev vertexRing (i : D.Index) := Away 𝒜 (Q.x i)

def vertexEval (i : D.Index) : Q.vertexRing i →+* F := Q.awayEval (Q.x i) (Q.x_ne i)

theorem vertexEval_mem (i : D.Index) (y : Q.vertexRing i) : Q.vertexEval i y ∈ D.ring i := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (Q.x_mem i) y
  rw [vertexEval, Q.awayEval_mk]
  exact Q.away_mem i n a ha

theorem vertexEval_surj (i : D.Index) (y : F) (hy : y ∈ D.ring i) :
    ∃ z : Q.vertexRing i, Q.vertexEval i z = y := by
  obtain ⟨n, a, ha, rfl⟩ := Q.away_surj i y hy
  exact ⟨Away.mk 𝒜 (Q.x_mem i) n a ha, Q.awayEval_mk _ _ _ _ _⟩

def vertexEquiv (i : D.Index) : Q.vertexRing i ≃+* D.ring i :=
  RingEquiv.ofBijective ((Q.vertexEval i).codRestrict (D.ring i) (Q.vertexEval_mem i))
    ⟨fun _ _ h ↦ Q.awayEval_injective (Q.x_ne i) (Q.x_mem i) (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨z, hz⟩ := Q.vertexEval_surj i y y.property
      exact ⟨z, Subtype.ext hz⟩⟩

abbrev pairElement (i j : D.Index) := Q.x i * Q.x j
abbrev pairRing (i j : D.Index) := Away 𝒜 (Q.pairElement i j)

theorem pair_ne (i j : D.Index) : Q.ev (Q.pairElement i j) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero (Q.x_ne i) (Q.x_ne j)

def pairEval (i j : D.Index) : Q.pairRing i j →+* F := Q.awayEval _ (Q.pair_ne i j)

def pairLeft (i j : D.Index) : Q.vertexRing i →+* Q.pairRing i j :=
  awayMap 𝒜 (Q.x_mem j) rfl

def pairRight (i j : D.Index) : Q.vertexRing j →+* Q.pairRing i j :=
  awayMap 𝒜 (Q.x_mem i) (mul_comm _ _)

@[simp] theorem pairEval_left (i j : D.Index) (a : Q.vertexRing i) :
    Q.pairEval i j (Q.pairLeft i j a) = Q.vertexEval i a :=
  Q.awayEval_awayMap (Q.x_mem _) (Q.x_mem _) rfl _ _ a

@[simp] theorem pairEval_right (i j : D.Index) (a : Q.vertexRing j) :
    Q.pairEval i j (Q.pairRight i j a) = Q.vertexEval j a :=
  Q.awayEval_awayMap (Q.x_mem _) (Q.x_mem _) (mul_comm _ _) _ _ a

theorem ratio_mem (i j : D.Index) : Q.ev (Q.x j) / Q.ev (Q.x i) ∈ D.ring i := by
  have h := Q.away_mem i 1 (Q.x j) (by simpa using Q.x_mem j)
  simpa using h

theorem pairEval_mem (i j : D.Index) (z : Q.pairRing i j) :
    Q.pairEval i j z ∈ D.ring i ⊔ D.ring j := by
  let := (Q.pairLeft i j).toAlgebra
  let t : Q.vertexRing i := Away.isLocalizationElem (Q.x_mem i) (Q.x_mem j)
  have : IsLocalization.Away t (Q.pairRing i j) :=
    Away.isLocalization_mul (Q.x_mem _) (Q.x_mem _) rfl Q.d_pos.ne'
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj t z
  have he := congrArg (Q.pairEval i j) ha
  change Q.pairEval i j (z * Q.pairLeft i j t ^ n) = Q.pairEval i j (Q.pairLeft i j a) at he
  rw [map_mul] at he
  have hp : Q.pairEval i j (Q.pairLeft i j t ^ n) = Q.pairEval i j (Q.pairLeft i j t) ^ n :=
    (Q.pairEval i j).map_pow _ n
  rw [hp, Q.pairEval_left, Q.pairEval_left] at he
  have hd : Q.vertexEval i t = (Q.ev (Q.x j) / Q.ev (Q.x i)) ^ Q.d := by
    dsimp [t, Away.isLocalizationElem, vertexEval]
    rw [Q.awayEval_mk, map_pow, div_pow]
  rw [hd] at he
  have hne : (Q.ev (Q.x j) / Q.ev (Q.x i)) ^ Q.d ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (Q.x_ne j) (Q.x_ne i))
  have hz : Q.pairEval i j z = Q.vertexEval i a *
      ((Q.ev (Q.x i) / Q.ev (Q.x j)) ^ Q.d) ^ n := by
    calc
      _ = Q.vertexEval i a / ((Q.ev (Q.x j) / Q.ev (Q.x i)) ^ Q.d) ^ n :=
        (eq_div_iff (pow_ne_zero n hne)).mpr he
      _ = _ := by rw [div_eq_mul_inv, ← inv_pow, ← inv_pow, inv_div]
  rw [hz]
  apply (D.ring i ⊔ D.ring j).mul_mem
  · exact (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left) (Q.vertexEval_mem i a)
  · apply (D.ring i ⊔ D.ring j).pow_mem
    apply (D.ring i ⊔ D.ring j).pow_mem
    exact (show D.ring j ≤ D.ring i ⊔ D.ring j from le_sup_right) (Q.ratio_mem j i)

theorem pairEval_surj (i j : D.Index) (y : F) (hy : y ∈ D.ring i ⊔ D.ring j) :
    ∃ z : Q.pairRing i j, Q.pairEval i j z = y := by
  have hle : D.ring i ⊔ D.ring j ≤
      { RingHom.range (Q.pairEval i j) with
        algebraMap_mem' := fun c ↦ ⟨_, Q.awayEval_algebraMap _ _ c⟩ } := by
    apply sup_le
    · intro w hw
      obtain ⟨a, ha⟩ := Q.vertexEval_surj i w hw
      exact ⟨Q.pairLeft i j a, (Q.pairEval_left i j a).trans ha⟩
    · intro w hw
      obtain ⟨a, ha⟩ := Q.vertexEval_surj j w hw
      exact ⟨Q.pairRight i j a, (Q.pairEval_right i j a).trans ha⟩
  exact hle hy

def pairEquiv (i j : D.Index) : Q.pairRing i j ≃+* ↥(D.ring i ⊔ D.ring j) :=
  RingEquiv.ofBijective ((Q.pairEval i j).codRestrict (D.ring i ⊔ D.ring j) (Q.pairEval_mem i j))
    ⟨fun _ _ h ↦ Q.awayEval_injective (Q.pair_ne i j)
      (SetLike.mul_mem_graded (Q.x_mem _) (Q.x_mem _)) (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨z, hz⟩ := Q.pairEval_surj i j y y.property
      exact ⟨z, Subtype.ext hz⟩⟩

theorem pairEquiv_left (i j : D.Index) (x : Q.vertexRing i) :
    Q.pairEquiv i j (Q.pairLeft i j x) = Subalgebra.inclusion le_sup_left (Q.vertexEquiv i x) :=
  Subtype.ext (Q.pairEval_left i j x)

theorem pairEquiv_right (i j : D.Index) (x : Q.vertexRing j) :
    Q.pairEquiv i j (Q.pairRight i j x) = Subalgebra.inclusion le_sup_right (Q.vertexEquiv j x) :=
  Subtype.ext (Q.pairEval_right i j x)

def vertexOpen (i : D.Index) : Spec (CommRingCat.of (Q.vertexRing i)) ⟶ Proj 𝒜 :=
  Proj.awayι 𝒜 (Q.x i) (Q.x_mem i) Q.d_pos

instance vertexOpen_open (i : D.Index) : IsOpenImmersion (Q.vertexOpen i) := by
  unfold vertexOpen
  infer_instance

theorem vertexOpen_cover (p : Proj 𝒜) : ∃ i y, Q.vertexOpen i y = p := by
  obtain ⟨i, hi⟩ := Q.cover p
  have hmem : p ∈ Proj.basicOpen 𝒜 (Q.x i) := hi
  rw [← Proj.opensRange_awayι 𝒜 (Q.x i) (Q.x_mem i) Q.d_pos] at hmem
  exact ⟨i, hmem⟩

def vertexIso (i : D.Index) : D.chart i ≅ Spec (CommRingCat.of (Q.vertexRing i)) :=
  Scheme.Spec.mapIso (Q.vertexEquiv i).toCommRingCatIso.op

def pairIso (i j : D.Index) : D.overlap i j ≅ Spec (CommRingCat.of (Q.pairRing i j)) :=
  Scheme.Spec.mapIso (Q.pairEquiv i j).toCommRingCatIso.op

@[reassoc] theorem vertexIso_left (i j : D.Index) :
    D.left i j ≫ (Q.vertexIso i).hom =
      (Q.pairIso i j).hom ≫ Spec.map (CommRingCat.ofHom (Q.pairLeft i j)) := by
  change Spec.map (CommRingCat.ofHom (Subalgebra.inclusion le_sup_left).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Q.vertexEquiv i).toRingHom) =
    Spec.map (CommRingCat.ofHom (Q.pairEquiv i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Q.pairLeft i j))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (Q.pairEquiv_left i j x).symm

@[reassoc] theorem vertexIso_right (i j : D.Index) :
    D.transition i j ≫ D.left j i ≫ (Q.vertexIso j).hom =
      (Q.pairIso i j).hom ≫ Spec.map (CommRingCat.ofHom (Q.pairRight i j)) := by
  change D.transition i j ≫ D.left j i ≫
    Spec.map (CommRingCat.ofHom (Q.vertexEquiv j).toRingHom) =
    Spec.map (CommRingCat.ofHom (Q.pairEquiv i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Q.pairRight i j))
  simp only [PrincipalAtlas.transition, PrincipalAtlas.left, specMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (Q.pairEquiv_right i j x).symm

def pairOpen (i j : D.Index) : Spec (CommRingCat.of (Q.pairRing i j)) ⟶ Proj 𝒜 :=
  Proj.awayι 𝒜 (Q.pairElement i j) (SetLike.mul_mem_graded (Q.x_mem _) (Q.x_mem _))
    (add_pos Q.d_pos Q.d_pos)

@[reassoc] theorem pairLeft_open (i j : D.Index) :
    Spec.map (CommRingCat.ofHom (Q.pairLeft i j)) ≫ Q.vertexOpen i = Q.pairOpen i j :=
  Proj.SpecMap_awayMap_awayι 𝒜 (Q.x_mem _) Q.d_pos (Q.x_mem _) rfl

@[reassoc] theorem pairRight_open (i j : D.Index) :
    Spec.map (CommRingCat.ofHom (Q.pairRight i j)) ≫ Q.vertexOpen j = Q.pairOpen i j :=
  Proj.SpecMap_awayMap_awayι 𝒜 (Q.x_mem _) Q.d_pos (Q.x_mem _) (mul_comm _ _)

theorem comparison_compatible (i j : D.Index) :
    D.left i j ≫ (Q.vertexIso i).hom ≫ Q.vertexOpen i =
      D.transition i j ≫ D.left j i ≫ (Q.vertexIso j).hom ≫ Q.vertexOpen j := by
  rw [Q.vertexIso_left_assoc, Q.vertexIso_right_assoc, Q.pairLeft_open, Q.pairRight_open]

def toProjective : D.glued ⟶ Proj 𝒜 :=
  Multicoequalizer.desc D.glueData.toGlueData.diagram _
    (fun i ↦ (Q.vertexIso i).hom ≫ Q.vertexOpen i) (fun ⟨i, j⟩ ↦ by
      change D.left i j ≫ ((Q.vertexIso i).hom ≫ Q.vertexOpen i) =
        (D.transition i j ≫ D.left j i) ≫ ((Q.vertexIso j).hom ≫ Q.vertexOpen j)
      simpa only [Category.assoc] using Q.comparison_compatible i j)

@[simp, reassoc] theorem chartInclusion_toProjective (i : D.Index) :
    D.chartInclusion i ≫ Q.toProjective = (Q.vertexIso i).hom ≫ Q.vertexOpen i := by
  apply Multicoequalizer.π_desc

def vertexCover : (Proj 𝒜).OpenCover :=
  Scheme.Cover.mkOfCovers D.Index (fun i ↦ Spec (CommRingCat.of (Q.vertexRing i)))
    Q.vertexOpen Q.vertexOpen_cover

def pairPullbackIso (i j : D.Index) :
    pullback (Q.vertexOpen i) (Q.vertexOpen j) ≅ Spec (CommRingCat.of (Q.pairRing i j)) :=
  Proj.pullbackAwayιIso 𝒜 (Q.x_mem _) Q.d_pos (Q.x_mem _) Q.d_pos rfl

@[simp, reassoc] theorem pairPullbackIso_inv_fst (i j : D.Index) :
    (Q.pairPullbackIso i j).inv ≫ pullback.fst (Q.vertexOpen i) (Q.vertexOpen j) =
      Spec.map (CommRingCat.ofHom (Q.pairLeft i j)) :=
  Proj.pullbackAwayιIso_inv_fst 𝒜 (Q.x_mem _) Q.d_pos (Q.x_mem _) Q.d_pos rfl

@[simp, reassoc] theorem pairPullbackIso_inv_snd (i j : D.Index) :
    (Q.pairPullbackIso i j).inv ≫ pullback.snd (Q.vertexOpen i) (Q.vertexOpen j) =
      Spec.map (CommRingCat.ofHom (Q.pairRight i j)) :=
  Proj.pullbackAwayιIso_inv_snd 𝒜 (Q.x_mem _) Q.d_pos (Q.x_mem _) Q.d_pos rfl

@[reassoc] theorem inverse_left (i j : D.Index) :
    Spec.map (CommRingCat.ofHom (Q.pairLeft i j)) ≫ (Q.vertexIso i).inv =
      (Q.pairIso i j).inv ≫ D.left i j := by
  rw [← cancel_epi (Q.pairIso i j).hom, ← Q.vertexIso_left_assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc] theorem inverse_right (i j : D.Index) :
    Spec.map (CommRingCat.ofHom (Q.pairRight i j)) ≫ (Q.vertexIso j).inv =
      (Q.pairIso i j).inv ≫ D.transition i j ≫ D.left j i := by
  rw [← cancel_epi (Q.pairIso i j).hom, ← Q.vertexIso_right_assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem inverse_compatible (i j : D.Index) :
    pullback.fst (Q.vertexOpen i) (Q.vertexOpen j) ≫ (Q.vertexIso i).inv ≫ D.chartInclusion i =
      pullback.snd (Q.vertexOpen i) (Q.vertexOpen j) ≫ (Q.vertexIso j).inv ≫
        D.chartInclusion j := by
  rw [← cancel_epi (Q.pairPullbackIso i j).inv]
  rw [Q.pairPullbackIso_inv_fst_assoc i j, Q.pairPullbackIso_inv_snd_assoc i j,
    Q.inverse_left_assoc i j, Q.inverse_right_assoc i j]
  exact congrArg (fun f ↦ (Q.pairIso i j).inv ≫ f) (D.glueData.glue_condition i j).symm

def fromProjective : Proj 𝒜 ⟶ D.glued :=
  Q.vertexCover.glueMorphisms (fun i ↦ (Q.vertexIso i).inv ≫ D.chartInclusion i)
    Q.inverse_compatible

@[simp, reassoc] theorem vertexOpen_fromProjective (i : D.Index) :
    Q.vertexOpen i ≫ Q.fromProjective = (Q.vertexIso i).inv ≫ D.chartInclusion i := by
  apply Scheme.Cover.ι_glueMorphisms

/-- The atlas and the `Proj` are isomorphic. -/
def iso : D.glued ≅ Proj 𝒜 where
  hom := Q.toProjective
  inv := Q.fromProjective
  hom_inv_id := by
    apply D.glueData.openCover.hom_ext
    intro i
    change D.Index at i
    change D.chartInclusion i ≫ _ = D.chartInclusion i ≫ _
    simp only [Q.chartInclusion_toProjective_assoc, Q.vertexOpen_fromProjective,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply Q.vertexCover.hom_ext
    intro i
    change D.Index at i
    change Q.vertexOpen i ≫ _ = Q.vertexOpen i ≫ _
    simp only [Q.vertexOpen_fromProjective_assoc, Q.chartInclusion_toProjective,
      Iso.inv_hom_id_assoc, Category.comp_id]

theorem iso_over_base : Q.iso.hom ≫ projBase 𝒜 = D.toBase := by
  apply D.glueData.openCover.hom_ext
  intro i
  change D.chartInclusion i ≫ Q.toProjective ≫ projBase 𝒜 = D.chartInclusion i ≫ D.toBase
  rw [Q.chartInclusion_toProjective_assoc, PrincipalAtlas.chartInclusion_toBase]
  change Spec.map (CommRingCat.ofHom (Q.vertexEquiv i).toRingHom) ≫
    Q.vertexOpen i ≫ projBase 𝒜 = D.chartToBase i
  simp only [projBase, vertexOpen, Proj.awayι_toSpecZero_assoc,
    PrincipalAtlas.chartToBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact Q.awayEval_algebraMap _ _ c

end AtlasModel
end
end SurfaceLib.Projective

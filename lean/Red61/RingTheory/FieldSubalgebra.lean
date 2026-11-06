import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic

/-! # Subalgebras of fields: localization, gluing and Frobenius descent

Formerly the modules `SubalgebraLocalization`, `SubalgebraGluing`, `FrobeniusDescent`.
-/

namespace Red61

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Elements whose denominators can be cleared by a power of a fixed element. -/
def powerDenominators (A : Subalgebra k F) (d : A) : Subalgebra k F where
  carrier := {x | ∃ n : ℕ, x * (d : F)^n ∈ A}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  algebraMap_mem' x := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m, ?_⟩
    have he : (x+y)*(d : F)^(n+m) =
        (x*(d : F)^n)*(d : F)^m + (y*(d : F)^m)*(d : F)^n := by rw [pow_add]; ring
    rw [he]
    exact A.add_mem (A.mul_mem hn (A.pow_mem d.property _))
      (A.mul_mem hm (A.pow_mem d.property _))
  mul_mem' := by
    rintro x y ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m, ?_⟩
    have he : (x*y)*(d : F)^(n+m) = (x*(d : F)^n)*(y*(d : F)^m) := by rw [pow_add]; ring
    rw [he]
    exact A.mul_mem hn hm

theorem adjoin_inverse_denominators (A : Subalgebra k F) (d : A) (hd : (d : F) ≠ 0) :
    A ⊔ Algebra.adjoin k ({(d : F)⁻¹} : Set F) ≤ powerDenominators A d := by
  apply sup_le
  · intro x hx
    exact ⟨0, by simpa using hx⟩
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨1, by simp [hd]⟩

/-- A subalgebra obtained by adjoining an inverse is the corresponding localization. -/
theorem subalgebra_isLocalizationAway (A B : Subalgebra k F) (hAB : A ≤ B) (d : A)
    (hd : (d : F) ≠ 0) (hinv : (d : F)⁻¹ ∈ B)
    (hgen : B ≤ A ⊔ Algebra.adjoin k ({(d : F)⁻¹} : Set F)) :
    letI : Algebra A B := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
    IsLocalization.Away d B := by
  let : Algebra A B := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  apply IsLocalization.Away.mk
  · refine ⟨⟨algebraMap A B d, ⟨(d : F)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hd
    · apply Subtype.ext
      exact inv_mul_cancel₀ hd
  · intro x
    obtain ⟨n,hn⟩ := (hgen.trans (adjoin_inverse_denominators A d hd)) x.property
    refine ⟨n, ⟨(x : F)*(d : F)^n, hn⟩, ?_⟩
    rfl
  · intro a b hab
    have he : a = b := Subtype.ext (congrArg (fun z : B => (z : F)) hab)
    exact ⟨0, by rw [he]⟩

end Red61

/-! Gluing affine subalgebras of a field along principal localizations.

The hypotheses concern rings and localization maps. The resulting object is a
mathlib `Scheme`, with its actual open cover and fiber-product intersections.
-/

namespace Red61.AffineGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]

@[instance_reducible] def inclusionAlgebra {A B : Subalgebra k F} (h : A ≤ B) : Algebra A B :=
  (Subalgebra.inclusion h).toRingHom.toAlgebra

def specMap {A B : Subalgebra k F} (h : A ≤ B) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

@[simp] theorem specMap_refl (A : Subalgebra k F) : specMap (le_refl A) = 𝟙 _ := by
  rw [specMap, ← Spec.map_id]
  congr 1

@[simp, reassoc] theorem specMap_comp {A B C : Subalgebra k F} (h : A ≤ B) (h' : B ≤ C) :
    specMap h' ≫ specMap h = specMap (h.trans h') := by
  rw [specMap, specMap, ← Spec.map_comp]
  rfl

theorem localization_description {A B : Subalgebra k F} (h : A ≤ B) (d : A)
    (hloc : letI := inclusionAlgebra h; IsLocalization.Away d B) :
    (d : F) ≠ 0 ∧ B = A ⊔ Algebra.adjoin k ({(d : F)⁻¹} : Set F) := by
  let := inclusionAlgebra h
  let := hloc
  let v : B := IsLocalization.Away.invSelf d
  have hv : (d : F) * (v : F) = 1 :=
    congrArg (fun x : B ↦ (x : F)) (IsLocalization.Away.mul_invSelf d)
  have hd : (d : F) ≠ 0 := left_ne_zero_of_mul_eq_one hv
  have he : (v : F) = (d : F)⁻¹ := by
    apply mul_left_cancel₀ hd
    rw [hv, mul_inv_cancel₀ hd]
  refine ⟨hd, le_antisymm ?_ (sup_le h ?_)⟩
  · intro b hb
    obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj d (⟨b,hb⟩ : B)
    have ha' : b * (d : F)^n = (a : F) := congrArg (fun x : B ↦ (x : F)) ha
    have hb' : b = (a : F) * ((d : F)⁻¹)^n := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (eq_div_iff (pow_ne_zero n hd)).mpr ha'
    rw [hb']
    exact (A ⊔ Algebra.adjoin k _).mul_mem
      ((show A ≤ A ⊔ Algebra.adjoin k _ from le_sup_left) a.property)
      ((A ⊔ Algebra.adjoin k _).pow_mem
        ((show Algebra.adjoin k _ ≤ A ⊔ Algebra.adjoin k _ from le_sup_right)
          (Algebra.subset_adjoin (by simp))) _)
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, ← he]
    exact v.property

/-- Adjoining a second subalgebra commutes with the principal localization. -/
theorem join_isLocalization {A B C : Subalgebra k F} (hAB : A ≤ B) (hAC : A ≤ C)
    (d : A) (hloc : letI := inclusionAlgebra hAB; IsLocalization.Away d B) :
    letI := inclusionAlgebra (show C ≤ B ⊔ C from le_sup_right)
    IsLocalization.Away (Subalgebra.inclusion hAC d) ↥(B ⊔ C) := by
  obtain ⟨hd, he⟩ := localization_description hAB d hloc
  apply subalgebra_isLocalizationAway
  · exact hd
  · apply (show B ≤ B ⊔ C from le_sup_left)
    rw [he]
    exact (show Algebra.adjoin k _ ≤ A ⊔ Algebra.adjoin k _ from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  · change B ⊔ C ≤ C ⊔ Algebra.adjoin k ({(d : F)⁻¹} : Set F)
    rw [he]
    exact sup_le (sup_le (hAC.trans le_sup_left) le_sup_right) le_sup_left

/-- The union of coordinate subalgebras represents the geometric intersection. -/
theorem join_isPullback {A B C : Subalgebra k F} (hAB : A ≤ B) (hAC : A ≤ C)
    (d : A) (hloc : letI := inclusionAlgebra hAB; IsLocalization.Away d B) :
    IsPullback (specMap (show B ≤ B ⊔ C from le_sup_left))
      (specMap (show C ≤ B ⊔ C from le_sup_right)) (specMap hAB) (specMap hAC) := by
  let := inclusionAlgebra hAB
  let := inclusionAlgebra (show C ≤ B ⊔ C from le_sup_right)
  let := hloc
  have := join_isLocalization hAB hAC d hloc
  have : IsLocalization ((Submonoid.powers d).map (Subalgebra.inclusion hAC).toRingHom)
      ↥(B ⊔ C) := by
    rw [Submonoid.map_powers]
    exact join_isLocalization hAB hAC d hloc
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Subalgebra.inclusion hAC).toRingHom
      (Subalgebra.inclusion (show B ≤ B ⊔ C from le_sup_left)).toRingHom
      (by rfl) (Submonoid.powers d))).flip

end
end Red61.AffineGluing

/-! Descent of principal affine intersections to a subfield containing all p-th powers.

The subfield need not contain the coefficient field of the original surface;
all subalgebras here are over the smaller, common base field.
-/

namespace Red61.FrobeniusDescent

open AffineGluing
noncomputable section

variable {R F : Type} [Field R] [Field F] [Algebra R F]
variable (M : Subfield F) [Algebra R M] [IsScalarTower R M F]

theorem localization_congr {A B C : Subalgebra R F} (hAB : A ≤ B) (hAC : A ≤ C)
    (hBC : B = C) (d : A)
    (hloc : letI := inclusionAlgebra hAB; IsLocalization.Away d B) :
    letI := inclusionAlgebra hAC; IsLocalization.Away d C := by
  subst C
  exact hloc

/-- Intersection with the subfield, retaining the common base algebra structure. -/
def fixed (A : Subalgebra R F) : Subalgebra R M :=
  A.comap (IsScalarTower.toAlgHom R M F)

@[simp] theorem mem_fixed (A : Subalgebra R F) (x : M) :
    x ∈ fixed M A ↔ (x : F) ∈ A := Iff.rfl

theorem fixed_mono {A B : Subalgebra R F} (h : A ≤ B) : fixed M A ≤ fixed M B :=
  fun _ hx ↦ h hx

def embed (A : Subalgebra R F) : fixed M A →ₐ[R] A where
  toFun x := ⟨(x.val : F), x.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := Subtype.ext (IsScalarTower.algebraMap_apply R M F r).symm

variable (p : ℕ) [Fact p.Prime] [CharP F p] (hp : ∀ x : F, x ^ p ∈ M)

/-- Frobenius with its codomain restricted to the subfield. -/
def powerMap : F →+* M :=
  (frobenius F p).codRestrict M.toSubring hp

@[simp] theorem powerMap_coe (x : F) : (powerMap M p hp x : F) = x ^ p := rfl

def powerElement (A : Subalgebra R F) (d : A) : fixed M A :=
  ⟨powerMap M p hp d, A.pow_mem d.property p⟩

/-- Clear an overlap denominator by a multiple of p, so that it is invariant. -/
theorem fixed_isLocalization {A B : Subalgebra R F} (hAB : A ≤ B) (d : A)
    (hloc : letI := inclusionAlgebra hAB; IsLocalization.Away d B) :
    letI := inclusionAlgebra (fixed_mono M hAB)
    IsLocalization.Away (powerElement M p hp A d) (fixed M B) := by
  let := inclusionAlgebra hAB
  have := hloc
  let := inclusionAlgebra (fixed_mono M hAB)
  obtain ⟨hd, hB⟩ := localization_description hAB d hloc
  have hinv : (d : F)⁻¹ ∈ B := by
    rw [hB]
    exact (show Algebra.adjoin R _ ≤ A ⊔ Algebra.adjoin R _ from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  let v : fixed M B := ⟨powerMap M p hp ((d : F)⁻¹), B.pow_mem hinv p⟩
  apply IsLocalization.Away.mk
  · refine ⟨⟨algebraMap (fixed M A) (fixed M B) (powerElement M p hp A d),
      v, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; apply Subtype.ext
      change (d : F)^p * ((d : F)⁻¹)^p = 1
      rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
    · apply Subtype.ext; apply Subtype.ext
      change ((d : F)⁻¹)^p * (d : F)^p = 1
      rw [← mul_pow, inv_mul_cancel₀ hd, one_pow]
  · intro x
    obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj d (embed M B x)
    have ha' : (x.val : F) * (d : F)^n = (a : F) :=
      congrArg (fun z : B ↦ (z : F)) ha
    have hn : p * n = n + n * (p - 1) := by
      calc
        p * n = ((p - 1) + 1) * n := by rw [Nat.sub_add_cancel (Nat.Prime.one_le Fact.out)]
        _ = n + n * (p - 1) := by ring
    have hnum : (x.val : F) * ((d : F)^p)^n ∈ A := by
      rw [← pow_mul, hn, pow_add, ← mul_assoc, ha']
      exact A.mul_mem a.property (A.pow_mem d.property _)
    exact ⟨n, ⟨x.val * (powerMap M p hp d)^n, hnum⟩, rfl⟩
  · intro a b hab
    have he : a = b := Subtype.ext (congrArg (fun z : fixed M B ↦ z.val) hab)
    exact ⟨0, by rw [he]⟩

/-- Frobenius sends a join into the join of the intersections with M. -/
theorem power_mem_fixed_sup (A B : Subalgebra R F) {x : F} (hx : x ∈ A ⊔ B) :
    powerMap M p hp x ∈ fixed M A ⊔ fixed M B := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact (show fixed M A ≤ fixed M A ⊔ fixed M B from le_sup_left) (A.pow_mem hx p)
    · exact (show fixed M B ≤ fixed M A ⊔ fixed M B from le_sup_right) (B.pow_mem hx p)
  | algebraMap r =>
    have he : powerMap M p hp (algebraMap R F r) = algebraMap R M (r^p) := by
      apply Subtype.ext
      change (algebraMap R F r)^p = algebraMap M F (algebraMap R M (r^p))
      rw [← IsScalarTower.algebraMap_apply, map_pow]
    rw [he]
    exact (fixed M A ⊔ fixed M B).algebraMap_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (fixed M A ⊔ fixed M B).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [map_mul]
    exact (fixed M A ⊔ fixed M B).mul_mem ihx ihy

include p hp in
/-- For a principal overlap, intersection with M does preserve this join. -/
theorem fixed_sup (A B : Subalgebra R F) (d : A)
    (hloc : letI := inclusionAlgebra (show A ≤ A ⊔ B from le_sup_left)
      IsLocalization.Away d ↥(A ⊔ B)) :
    fixed M (A ⊔ B) = fixed M A ⊔ fixed M B := by
  obtain ⟨hd,hdesc⟩ := localization_description le_sup_left d hloc
  have hinv : (d : F)⁻¹ ∈ A ⊔ B := by
    rw [hdesc]
    exact (show Algebra.adjoin R _ ≤ A ⊔ Algebra.adjoin R _ from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  have hpow := power_mem_fixed_sup M p hp A B hinv
  obtain ⟨_,hfixed⟩ := localization_description (fixed_mono M le_sup_left)
    (powerElement M p hp A d) (fixed_isLocalization M p hp le_sup_left d hloc)
  apply le_antisymm
  · rw [hfixed]
    refine sup_le le_sup_left (Algebra.adjoin_le ?_)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change (powerMap M p hp (d : F))⁻¹ ∈ fixed M A ⊔ fixed M B
    rw [← map_inv₀]
    exact hpow
  · exact sup_le (fixed_mono M le_sup_left) (fixed_mono M le_sup_right)

include p hp in
/-- The fraction field also descends by clearing denominators with p-th powers. -/
theorem fixed_isFractionRing (A : Subalgebra R F) [IsFractionRing A F] :
    IsFractionRing (fixed M A) M := by
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a,b,hb,he⟩ := IsFractionRing.div_surjective A (x : F)
  have hb' : (b : F) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have hmul : (x : F) * (b : F) = (a : F) := by
    rw [← he]
    exact div_mul_cancel₀ _ hb'
  have hnum : (x : F) * (b : F)^p ∈ A := by
    rw [← Nat.sub_add_cancel (Nat.Prime.one_le (Fact.out : p.Prime)), pow_succ', ← mul_assoc,
      hmul]
    exact A.mul_mem a.property (A.pow_mem b.property _)
  refine ⟨⟨x * powerMap M p hp b, hnum⟩, powerElement M p hp A b, ?_⟩
  apply Subtype.ext
  change (x : F) = ((x : F) * (b : F)^p) / (b : F)^p
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hb')]

/-- Restricting the base of two subalgebras preserves their join. -/
theorem restrictScalars_sup {S : Type} [Field S] [Algebra R S] [Algebra S F]
    [IsScalarTower R S F] (A B : Subalgebra S F) :
    (A ⊔ B).restrictScalars R = A.restrictScalars R ⊔ B.restrictScalars R := by
  apply Subalgebra.toSubsemiring_injective
  change (A ⊔ B).toSubsemiring =
    (A.restrictScalars R ⊔ B.restrictScalars R).toSubsemiring
  rw [Algebra.sup_toSubsemiring, Algebra.sup_toSubsemiring]
  rfl

end
end Red61.FrobeniusDescent

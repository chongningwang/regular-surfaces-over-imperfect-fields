import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Red61.RingTheory.FieldSubalgebra
import Red61.RingTheory.Localization

/-! # Regularity, regular pairs and regular sequences under localization

Formerly the modules `InvariantNormality`, `RegularLocalization`, `NormalLocalizationHull`, `RegularLocalizationBounds`, `RegularPairConormal`, `RegularSequenceLocalization`, `LocalizedRegularQuotient`, `Retraction`, `ShiftedPolynomialKernel`, `ShiftedPolynomialPair`, `ShiftedBivariateRegular`, `UniformRegularLocalization`, `RegularPairPrincipalOpen`, `RegularPairKernelPrincipalOpen`, `RegularPairUnitMultipliers`, `RegularPairNumerators`, `PrincipalRegularPresentation`, `PrincipalRegularPairModel`.
-/

/-! Intersecting an integrally closed subalgebra of a field with a subfield
preserves integral closedness, when the stated fields are fraction fields. -/

namespace Red61.FrobeniusDescent

noncomputable section

variable {R F : Type} [Field R] [Field F] [Algebra R F]
variable (M : Subfield F) [Algebra R M] [IsScalarTower R M F]

theorem fixed_isIntegrallyClosed (A : Subalgebra R F) [IsIntegrallyClosed A]
    [IsFractionRing A F] [IsFractionRing (fixed M A) M] :
    IsIntegrallyClosed (fixed M A) := by
  apply (isIntegrallyClosed_iff M).mpr
  intro x hx
  have hxF : IsIntegral A (x : F) :=
    hx.map_of_comp_eq (embed M A).toRingHom M.subtype rfl
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxF
  have hxA : (x : F) ∈ A := ha ▸ a.property
  exact ⟨⟨x,hxA⟩,rfl⟩

end
end Red61.FrobeniusDescent

/-! Regularity of localizations, and a denominator criterion inside a field. -/

namespace Red61

noncomputable section

theorem atPrime_regular_of_away {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (d : R) [IsLocalization.Away d A] [IsRegularRing A]
    (p : PrimeSpectrum R) (hd : d ∉ p.asIdeal) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
    rw [PrimeSpectrum.localization_away_comap_range A d]
    exact hd
  obtain ⟨q,rfl⟩ := hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers d) (Localization.AtPrime q.asIdeal) q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.asIdeal.comap (algebraMap R A)).primeCompl
      (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime (q.asIdeal.comap (algebraMap R A)))).toRingEquiv

theorem atPrime_regular_of_equiv {R A : Type*} [CommRing R] [CommRing A]
    (e : R ≃+* A) (h : ∀ p : PrimeSpectrum R,
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)) (p : PrimeSpectrum A) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  have : IsRegularLocalRing (Localization.AtPrime (p.asIdeal.comap e)) :=
    h (PrimeSpectrum.comap e.toRingHom p)
  exact IsRegularLocalRing.of_ringEquiv <| IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.asIdeal.comap e)) (Localization.AtPrime p.asIdeal) e
    (e.map_primeCompl_comap_eq p.asIdeal)

theorem regularRing_of_isLocalization {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A] [IsRegularRing R] :
    IsRegularRing A := by
  have := IsLocalization.isNoetherianRing M A inferInstance
  constructor
  intro p hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    M (Localization.AtPrime p) p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (p.comap (algebraMap R A)).primeCompl
      (Localization.AtPrime (p.comap (algebraMap R A))) (Localization.AtPrime p)).toRingEquiv

namespace FieldLocalization

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The part of the fraction field of P obtainable with denominators invertible in A. -/
def hull (P A : Subalgebra F K) : Subalgebra F K where
  carrier := {x | ∃ b ∈ P, b ≠ 0 ∧ b⁻¹ ∈ A ∧ x * b ∈ P}
  zero_mem' := ⟨1, P.one_mem, one_ne_zero, by simp, by simp⟩
  one_mem' := ⟨1, P.one_mem, one_ne_zero, by simp, by simp⟩
  algebraMap_mem' a := ⟨1, P.one_mem, one_ne_zero, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨b,hb,hb0,hbi,hx⟩ ⟨c,hc,hc0,hci,hy⟩
    refine ⟨b*c, P.mul_mem hb hc, mul_ne_zero hb0 hc0, ?_, ?_⟩
    · simpa only [mul_inv] using A.mul_mem hbi hci
    · have he : (x+y)*(b*c) = (x*b)*c + (y*c)*b := by ring
      rw [he]
      exact P.add_mem (P.mul_mem hx hc) (P.mul_mem hy hb)
  mul_mem' := by
    rintro x y ⟨b,hb,hb0,hbi,hx⟩ ⟨c,hc,hc0,hci,hy⟩
    refine ⟨b*c, P.mul_mem hb hc, mul_ne_zero hb0 hc0, ?_, ?_⟩
    · simpa only [mul_inv] using A.mul_mem hbi hci
    · have he : (x*y)*(b*c) = (x*b)*(y*c) := by ring
      rw [he]
      exact P.mul_mem hx hy

theorem le_hull (P A : Subalgebra F K) : P ≤ hull P A :=
  fun x hx ↦ ⟨1, P.one_mem, one_ne_zero, by simp, by simpa using hx⟩

theorem hull_inv {P A : Subalgebra F K} (_h : P ≤ A) {x : K}
    (hx : x ∈ hull P A) (hi : x⁻¹ ∈ A) : x⁻¹ ∈ hull P A := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨b,hb,hb0,hbi,hxb⟩ := hx
  refine ⟨x*b, hxb, mul_ne_zero hx0 hb0, ?_, ?_⟩
  · simpa only [mul_inv] using A.mul_mem hi hbi
  · simpa [← mul_assoc, hx0] using hb

/-- The denominator monoid is specified by actual units in the target ring. -/
def denominators {P A : Subalgebra F K} (h : P ≤ A) : Submonoid P :=
  (IsUnit.submonoid A).comap (Subalgebra.inclusion h).toMonoidHom

theorem isUnit_inclusion_iff {P A : Subalgebra F K} (h : P ≤ A) (b : P) :
    IsUnit (Subalgebra.inclusion h b) ↔ (b : K) ≠ 0 ∧ (b : K)⁻¹ ∈ A := by
  constructor
  · rintro ⟨u,hu⟩
    have hb : (b : K) ≠ 0 := by
      intro hb
      apply Units.ne_zero u
      rw [hu]
      exact Subtype.ext hb
    refine ⟨hb, ?_⟩
    have he : ((↑u⁻¹ : A) : K) = (b : K)⁻¹ := by
      apply mul_left_cancel₀ hb
      rw [mul_inv_cancel₀ hb]
      have hh := congrArg (fun z : A ↦ (z : K)) u.val_inv
      rw [hu] at hh
      exact hh
    rw [← he]
    exact (↑u⁻¹ : A).property
  · rintro ⟨hb,hi⟩
    exact ⟨⟨Subalgebra.inclusion h b, ⟨(b : K)⁻¹, hi⟩,
      Subtype.ext (mul_inv_cancel₀ hb), Subtype.ext (inv_mul_cancel₀ hb)⟩, rfl⟩

theorem isLocalization {P A : Subalgebra F K} (h : P ≤ A) (hh : A ≤ hull P A) :
    letI := AffineGluing.inclusionAlgebra h
    IsLocalization (denominators h) A := by
  let := AffineGluing.inclusionAlgebra h
  refine ⟨?_⟩
  constructor
  · intro b
    exact b.property
  · intro x
    obtain ⟨b,hb,hb0,hbi,hxb⟩ := hh x.property
    refine ⟨⟨⟨(x : K)*b,hxb⟩,
      ⟨⟨b,hb⟩, (isUnit_inclusion_iff h _).mpr ⟨hb0,hbi⟩⟩⟩, ?_⟩
    rfl
  · intro x y hxy
    have he : x = y := (Subalgebra.inclusion_injective h) hxy
    exact ⟨1, by simp [he]⟩

theorem regular {P A : Subalgebra F K} (h : P ≤ A) (hh : A ≤ hull P A)
    [IsRegularRing P] : IsRegularRing A := by
  let := AffineGluing.inclusionAlgebra h
  let := isLocalization h hh
  exact regularRing_of_isLocalization (denominators h)

end FieldLocalization
end
end Red61

/-! A localization hull of an integrally closed subring in its fraction
field is closed under taking roots that lie in that fraction field.
This uses integral closedness of the localization, not a completion. -/

namespace Red61.FieldLocalization

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem hull_idempotent_le (P A : Subalgebra F K) : hull P A ≤ hull P (hull P A) := by
  rintro x ⟨b, hb, hb0, hbi, hxb⟩
  refine ⟨b, hb, hb0, ?_, hxb⟩
  exact ⟨b, hb, hb0, hbi, by simp [hb0]⟩

theorem hull_denominators_nonZeroDivisors (P A : Subalgebra F K) :
    denominators (le_hull P A) ≤ nonZeroDivisors P := by
  intro b hb
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hz
  have hu : IsUnit (Subalgebra.inclusion (le_hull P A) b) := hb
  rw [hz, map_zero] at hu
  exact not_isUnit_zero hu

theorem hull_isIntegrallyClosed (P A : Subalgebra F K) [IsIntegrallyClosed P] :
    IsIntegrallyClosed (hull P A) := by
  let := AffineGluing.inclusionAlgebra (le_hull P A)
  have := isLocalization (le_hull P A) (hull_idempotent_le P A)
  exact isIntegrallyClosed_of_isLocalization (hull P A) (denominators (le_hull P A))
    (hull_denominators_nonZeroDivisors P A)

theorem hull_isFractionRing (P A : Subalgebra F K) [IsFractionRing P K] :
    IsFractionRing (hull P A) K := by
  let := AffineGluing.inclusionAlgebra (le_hull P A)
  have : IsScalarTower P (hull P A) K := IsScalarTower.of_algebraMap_eq' rfl
  have := isLocalization (le_hull P A) (hull_idempotent_le P A)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (denominators (le_hull P A)) (hull P A) K

theorem mem_hull_of_pow_mem (P A : Subalgebra F K) [IsIntegrallyClosed P]
    [IsFractionRing P K] {x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ hull P A) :
    x ∈ hull P A := by
  have := hull_isIntegrallyClosed P A
  have := hull_isFractionRing P A
  have hi : IsIntegral (hull P A) (x ^ n) := by
    exact isIntegral_algebraMap (x := (⟨x ^ n, hx⟩ : hull P A))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn hi
  exact hy ▸ y.property

theorem fractionMap_mem_hull {D T : Type*} [Field D] [CommRing T] [Algebra T D]
    [IsFractionRing T D] {P A : Subalgebra F K} (hPA : P ≤ A) (φ : D →+* K)
    (hpoly : ∀ t : T, φ (algebraMap T D t) ∈ hull P A)
    (himage : ∀ d : D, φ d ∈ A) (d : D) : φ d ∈ hull P A := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective T d
  rw [map_div₀, div_eq_mul_inv]
  apply (hull P A).mul_mem (hpoly a)
  apply hull_inv hPA (hpoly b)
  rw [← map_inv₀]
  exact himage _

theorem localizationMap_mem_hull {T S : Type*} [CommRing T] [CommRing S]
    [Algebra T S] (M : Submonoid T) [IsLocalization M S]
    {P A : Subalgebra F K} (hPA : P ≤ A) (φ : S →+* K)
    (hpoly : ∀ t : T, φ (algebraMap T S t) ∈ hull P A)
    (himage : ∀ s : S, φ s ∈ A) (s : S) : φ s ∈ hull P A := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective M s
  have hs : φ (IsLocalization.mk' S 1 b) * φ (algebraMap T S b) = 1 := by
    simpa only [map_mul, map_one] using congrArg φ (IsLocalization.mk'_spec S 1 b)
  have hb : φ (algebraMap T S b) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hs
    exact zero_ne_one hs
  have hi : (φ (algebraMap T S b))⁻¹ ∈ A := by
    have hinv : φ (IsLocalization.mk' S 1 b) = (φ (algebraMap T S b))⁻¹ := by
      apply mul_right_cancel₀ hb
      rw [hs, inv_mul_cancel₀ hb]
    rw [← hinv]
    exact himage _
  have he : φ (IsLocalization.mk' S a b) =
      φ (algebraMap T S a) / φ (algebraMap T S b) := by
    apply (eq_div_iff hb).mpr
    simpa only [map_mul] using congrArg φ (IsLocalization.mk'_spec S a b)
  rw [he, div_eq_mul_inv]
  exact (hull P A).mul_mem (hpoly a) (hull_inv hPA (hpoly b) hi)

end
end Red61.FieldLocalization

/-! Noetherian annihilator and colon ideals allow one denominator to
uniformly detect regularity on a localization and on a localized ideal
quotient. These bounds will descend regular defining pairs to principal opens. -/

namespace Red61
noncomputable section
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] [IsNoetherianRing R]

theorem exists_uniform_annihilator_multiplier (a : R)
    (ha : IsSMulRegular B (algebraMap R B a)) :
    ∃ v : S, ∀ r : R, r * a = 0 → (v : R) * r = 0 := by
  let N : Ideal R := Submodule.comap (LinearMap.mulLeft R a) ⊥
  have hN : N.FG := (inferInstance : IsNoetherianRing R).noetherian N
  have hle : N.map (algebraMap R B) ≤ (⊥ : Ideal R).map (algebraMap R B) := by
    rw [Ideal.map_bot]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change algebraMap R B r = 0
    have har : a * r = 0 := hr
    apply ha
    change algebraMap R B a * algebraMap R B r = algebraMap R B a * 0
    rw [mul_zero, ← map_mul, har, map_zero]
  obtain ⟨v, hv⟩ := exists_uniform_multiplier_of_localized_ideal_le S hN hle
  refine ⟨v, fun r hr ↦ hv r ?_⟩
  change a * r = 0
  simpa only [mul_comm a r] using hr

theorem exists_uniform_quotient_multiplier (I : Ideal R) (a : R)
    (ha : IsSMulRegular (B ⧸ I.map (algebraMap R B)) (algebraMap R B a)) :
    ∃ v : S, ∀ r : R, r * a ∈ I → (v : R) * r ∈ I := by
  let N : Ideal R := Submodule.comap (LinearMap.mulLeft R a) I
  have hN : N.FG := (inferInstance : IsNoetherianRing R).noetherian N
  have hle : N.map (algebraMap R B) ≤ I.map (algebraMap R B) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    have har : a * r ∈ I := hr
    apply mem_of_isSMulRegular_quotient_of_smul_mem ha
    change algebraMap R B a * algebraMap R B r ∈ I.map (algebraMap R B)
    rw [← map_mul]
    exact Ideal.mem_map_of_mem (algebraMap R B) har
  obtain ⟨v, hv⟩ := exists_uniform_multiplier_of_localized_ideal_le S hN hle
  refine ⟨v, fun r hr ↦ hv r ?_⟩
  change a * r ∈ I
  simpa only [mul_comm a r] using hr
end
end Red61

/-! The two classes of a weakly regular pair form a basis of its
actual ideal conormal module. The proof descends the Koszul coefficient
map through its kernel and then through the ideal square. -/

namespace Red61
open RingTheory.Sequence Module
noncomputable section
variable {R : Type*} [CommRing R] (a b : R)
local notation "I" => Ideal.ofList [a, b]
local notation "Q" => R ⧸ I

end
end Red61

/-! Weak regularity survives localization by flat base change. A map to a
nonzero ring that kills the localized sequence supplies the required proper
ideal condition for a regular sequence. -/

namespace Red61

open RingTheory.Sequence
open scoped TensorProduct
noncomputable section

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M in
theorem weaklyRegular_localization {rs : List R} (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  have : Module.Flat R S := IsLocalization.flat S M
  have ht := h.isWeaklyRegular_lTensor (M₂ := S)
  have hs : IsWeaklyRegular S rs := (TensorProduct.rid R S).isWeaklyRegular_congr rs |>.mp ht
  exact (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hs

theorem regular_of_weaklyRegular_of_killed [Nontrivial A] {rs : List S}
    (h : IsWeaklyRegular S rs) (f : S →+* A) (hf : ∀ x ∈ rs, f x = 0) :
    IsRegular S rs where
  toIsWeaklyRegular := h
  top_ne_smul := by
    intro ht
    have htop : (⊤ : Ideal S) = Ideal.ofList rs := by
      simpa only [smul_eq_mul, Ideal.mul_top] using ht
    have hker : Ideal.ofList rs ≤ RingHom.ker f := by
      apply Ideal.span_le.mpr
      intro x hx
      exact hf x hx
    have hone : (1 : S) ∈ Ideal.ofList rs :=
      htop ▸ (show (1 : S) ∈ (⊤ : Ideal S) from trivial)
    have hz : f 1 = 0 := hker hone
    exact one_ne_zero (by simpa only [map_one] using hz)

include M in
theorem regular_localization_of_killed [Nontrivial A] {rs : List R}
    (h : IsWeaklyRegular R rs) (f : S →+* A)
    (hf : ∀ x ∈ rs, f (algebraMap R S x) = 0) :
    IsRegular S (rs.map (algebraMap R S)) :=
  regular_of_weaklyRegular_of_killed (weaklyRegular_localization M h) f
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hf x hx)

end
end Red61

/-! Principal localization preserves the actual quotient map of a
regular pair: surjectivity, mapped kernel, and proper regularity all
use the native localization maps. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {F R Q : Type*} [CommRing F] [CommRing R] [CommRing Q]
  [Algebra F R] [Algebra F Q]

theorem localizedRegularQuotient_surjective (f : R →ₐ[F] Q)
    (hf : Function.Surjective f) (c : R) :
    Function.Surjective (Localization.awayMapₐ f c) :=
  IsLocalization.Away.mapₐ_surjective_of_surjective c hf

theorem localizedRegularQuotient_kernel (f : R →ₐ[F] Q) (a b c : R)
    (hk : RingHom.ker f = Ideal.ofList [a, b]) :
    RingHom.ker (Localization.awayMapₐ f c) =
      Ideal.ofList [algebraMap R (Localization.Away c) a,
        algebraMap R (Localization.Away c) b] := by
  have he := IsLocalization.ker_map (S := Localization.Away c)
    (M := Submonoid.powers c) (T := Submonoid.powers (f c))
    (Localization.Away (f c)) f.toRingHom (by rw [Submonoid.map_powers]; rfl)
  change RingHom.ker (Localization.awayMapₐ f c) =
    (RingHom.ker f.toRingHom).map (algebraMap R (Localization.Away c)) at he
  change RingHom.ker f.toRingHom = Ideal.ofList [a, b] at hk
  rw [hk] at he
  simpa only [Ideal.map_ofList, List.map_cons, List.map_nil] using he

theorem localizedRegularQuotient_regular (f : R →ₐ[F] Q) (a b c : R)
    [Nontrivial (Localization.Away (f c))]
    (hk : RingHom.ker f = Ideal.ofList [a, b]) (hr : IsRegular R [a, b]) :
    IsRegular (Localization.Away c)
      [algebraMap R (Localization.Away c) a, algebraMap R (Localization.Away c) b] := by
  have hz : ∀ x ∈ [a, b], f x = 0 := by
    intro x hx
    have hm : x ∈ Ideal.ofList [a, b] := Ideal.subset_span hx
    rw [← hk] at hm
    exact RingHom.mem_ker.mp hm
  simpa only [List.map_cons, List.map_nil] using
    regular_localization_of_killed (Submonoid.powers c) hr.toIsWeaklyRegular
      (Localization.awayMapₐ f c).toRingHom (by
        intro x hx
        change (IsLocalization.Away.map (Localization.Away c)
          (Localization.Away (f c)) f.toRingHom c) (algebraMap R _ x) = 0
        simp only [IsLocalization.Away.map, IsLocalization.map_eq]
        change algebraMap Q (Localization.Away (f c)) (f x) = 0
        rw [hz x hx, map_zero])
end
end Red61

namespace Red61

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

/-- Extension followed by contraction is the identity for an algebra with
an S-linear retraction. Applied to the Reynolds projection, this is the
missing ideal-theoretic part of the separation argument. -/
theorem ideal_map_comap_of_retraction (P : R →ₗ[S] S) (hP : P 1 = 1) (I : Ideal S) :
    (I.map (algebraMap S R)).comap (algebraMap S R) = I := by
  apply le_antisymm _ Ideal.le_comap_map
  have hmem : ∀ y ∈ I.map (algebraMap S R), ∀ r : R, P (r * y) ∈ I := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro r
      have he : P (r * algebraMap S R a) = a * P r := by
        rw [mul_comm, ← Algebra.smul_def, map_smul]
        rfl
      rw [he]
      exact I.mul_mem_right (P r) ha
    | zero => intro r; simp
    | add y z _ _ ihy ihz =>
      intro r
      simpa only [mul_add, map_add] using I.add_mem (ihy r) (ihz r)
    | smul a y _ ih =>
      intro r
      simpa only [smul_eq_mul, mul_assoc] using ih (r * a)
  intro x hx
  have h := hmem (algebraMap S R x) hx 1
  have he : P (algebraMap S R x) = x := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hP, smul_eq_mul, mul_one]
  simpa [he] using h

/-- Noetherianity descends along a linear retraction; no finiteness of R/S is needed. -/
theorem noetherian_of_retraction [IsNoetherianRing R] (P : R →ₗ[S] S)
    (hP : P 1 = 1) : IsNoetherianRing S := by
  let e : Ideal S ↪o Ideal R :=
    { toFun := Ideal.map (algebraMap S R)
      inj' := by
        intro I J h
        have hc := congrArg (Ideal.comap (algebraMap S R)) h
        simpa only [ideal_map_comap_of_retraction P hP] using hc
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          have hc := Ideal.comap_mono (f := algebraMap S R) h
          change (I.map (algebraMap S R)).comap (algebraMap S R) ≤
            (J.map (algebraMap S R)).comap (algebraMap S R) at hc
          simpa only [ideal_map_comap_of_retraction P hP] using hc
        · exact Ideal.map_mono }
  exact isNoetherianRing_iff.mpr (isNoetherian_mk e.dual.wellFoundedLT)

end Red61

/-! The evaluation kernel in a polynomial algebra is generated by its
shifted variables. The proof is an explicit polynomial induction, valid over
any commutative coefficient ring and for any index type. -/

namespace Red61

noncomputable section

variable {A σ : Type*} [CommRing A] (a : σ → A)

def shiftedVariablesIdeal : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range (fun i ↦ MvPolynomial.X i - MvPolynomial.C (a i)))

theorem sub_eval_mem_shiftedVariablesIdeal (p : MvPolynomial σ A) :
    p - MvPolynomial.C (MvPolynomial.aeval a p) ∈ shiftedVariablesIdeal a := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    have he : p + q - MvPolynomial.C (MvPolynomial.aeval a (p + q)) =
        (p - MvPolynomial.C (MvPolynomial.aeval a p)) +
          (q - MvPolynomial.C (MvPolynomial.aeval a q)) := by
      simp only [map_add]
      ring
    rw [he]
    exact (shiftedVariablesIdeal a).add_mem hp hq
  | mul_X p i hp =>
    have hi : MvPolynomial.X i - MvPolynomial.C (a i) ∈ shiftedVariablesIdeal a :=
      Ideal.subset_span (Set.mem_range_self i)
    have he : p * MvPolynomial.X i - MvPolynomial.C (MvPolynomial.aeval a
        (p * MvPolynomial.X i)) =
          p * (MvPolynomial.X i - MvPolynomial.C (a i)) +
            (p - MvPolynomial.C (MvPolynomial.aeval a p)) * MvPolynomial.C (a i) := by
      simp only [map_mul, MvPolynomial.aeval_X]
      ring
    rw [he]
    exact (shiftedVariablesIdeal a).add_mem
      ((shiftedVariablesIdeal a).mul_mem_left p hi)
      ((shiftedVariablesIdeal a).mul_mem_right (MvPolynomial.C (a i)) hp)

theorem ker_aeval_eq_shiftedVariablesIdeal :
    RingHom.ker (MvPolynomial.aeval a).toRingHom = shiftedVariablesIdeal a := by
  apply le_antisymm
  · intro p hp
    have he := sub_eval_mem_shiftedVariablesIdeal a p
    have hz : MvPolynomial.aeval a p = 0 := hp
    simpa only [hz, map_zero, sub_zero] using he
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    simp

end
end Red61

/-! The two shifted coordinates of a polynomial plane form a regular
sequence. Monicity proves regularity of the first element; evaluation
identifies its quotient with a polynomial ring for the second element. -/

namespace Red61

open Polynomial Submodule RingTheory.Sequence
noncomputable section

def quotSMulTopSelfEquiv (R : Type*) [CommRing R] (r : R) :
    QuotSMulTop r R ≃ₗ[R] R ⧸ Ideal.span {r} :=
  (QuotSMulTop.equivQuotTensor r R).trans (TensorProduct.rid R (R ⧸ Ideal.span {r}))

variable {A : Type*} [CommRing A]

abbrev shiftedPairOuter (a : A) : A[X][X] := X - C (C a)
abbrev shiftedPairInner (a : A) : A[X][X] := C (X - C a)

theorem shiftedPair_weaklyRegular (a₀ a₁ : A) :
    IsWeaklyRegular A[X][X] [shiftedPairOuter a₀, shiftedPairInner a₁] := by
  have h₀ : IsSMulRegular A[X][X] (shiftedPairOuter a₀) :=
    (Polynomial.monic_X_sub_C (C a₀)).isRegular.1
  let e₀ := quotSMulTopSelfEquiv A[X][X] (shiftedPairOuter a₀)
  let e₁ := Polynomial.quotientSpanXSubCAlgEquiv (C a₀)
  let e := e₀.toAddEquiv.trans e₁.toAddEquiv
  have he (x : QuotSMulTop (shiftedPairOuter a₀) A[X][X]) :
      e (shiftedPairInner a₁ • x) = (X - C a₁ : A[X]) • e x := by
    change e₁ (e₀ (shiftedPairInner a₁ • x)) =
      (X - C a₁ : A[X]) * e₁ (e₀ x)
    rw [e₀.map_smul]
    generalize e₀ x = y
    induction y using Quotient.inductionOn with
    | h p =>
      change Polynomial.eval (C a₀) (shiftedPairInner a₁ * p) =
        (X - C a₁) * Polynomial.eval (C a₀) p
      simp [shiftedPairInner]
  have h₁ : IsSMulRegular A[X] (X - C a₁) :=
    (Polynomial.monic_X_sub_C a₁).isRegular.1
  have hq : IsSMulRegular (QuotSMulTop (shiftedPairOuter a₀) A[X][X])
      (shiftedPairInner a₁) := (e.toEquiv.isSMulRegular_congr he).mpr h₁
  exact IsWeaklyRegular.cons h₀
    (IsWeaklyRegular.cons hq (IsWeaklyRegular.nil A[X][X] _))

def shiftedPairEvaluation (a₀ a₁ : A) : A[X][X] →+* A :=
  (Polynomial.evalRingHom a₁).comp (Polynomial.evalRingHom (C a₀))

theorem shiftedPair_regular [Nontrivial A] (a₀ a₁ : A) :
    IsRegular A[X][X] [shiftedPairOuter a₀, shiftedPairInner a₁] := by
  apply regular_of_weaklyRegular_of_killed (shiftedPair_weaklyRegular a₀ a₁)
    (shiftedPairEvaluation a₀ a₁)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp [shiftedPairEvaluation, shiftedPairOuter, shiftedPairInner]

end
end Red61

/-! The shifted variables in a bivariate polynomial algebra form a regular
sequence, by comparison with the iterated univariate polynomial algebra. -/

namespace Red61

open Polynomial RingTheory.Sequence
noncomputable section

variable (A : Type*) [CommRing A]

def bivariateToIterated : MvPolynomial (Fin 2) A ≃ₐ[A] A[X][X] :=
  (MvPolynomial.finSuccEquiv A 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))

@[simp] theorem bivariateToIterated_C (a : A) :
    bivariateToIterated A (MvPolynomial.C a) = C (C a) :=
  (bivariateToIterated A).commutes a

@[simp] theorem bivariateToIterated_X_zero :
    bivariateToIterated A (MvPolynomial.X 0) = X := by
  simp [bivariateToIterated, MvPolynomial.finSuccEquiv_X_zero, Polynomial.coe_mapAlgEquiv]

@[simp] theorem bivariateToIterated_X_one :
    bivariateToIterated A (MvPolynomial.X 1) = C X := by
  change Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1))
    (MvPolynomial.finSuccEquiv A 1 (MvPolynomial.X (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.coe_mapAlgEquiv, MvPolynomial.uniqueAlgEquiv]

theorem shiftedBivariate_regular [Nontrivial A] (a₀ a₁ : A) :
    IsRegular (MvPolynomial (Fin 2) A)
      [MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a₀,
        MvPolynomial.X (1 : Fin 2) - MvPolynomial.C a₁] := by
  let e := bivariateToIterated A
  have hc : IsRegular (MvPolynomial (Fin 2) A)
        [MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a₀,
          MvPolynomial.X (1 : Fin 2) - MvPolynomial.C a₁] ↔
      IsRegular A[X][X]
        [e (MvPolynomial.X 0 - MvPolynomial.C a₀),
          e (MvPolynomial.X 1 - MvPolynomial.C a₁)] := by
    apply e.toAddEquiv.isRegular_congr
    apply List.Forall₂.cons
    · intro x
      exact map_mul e _ x
    · apply List.Forall₂.cons
      · intro x
        exact map_mul e _ x
      · exact List.Forall₂.nil
  apply hc.mpr
  simpa only [e, map_sub, bivariateToIterated_C, bivariateToIterated_X_zero,
    bivariateToIterated_X_one, shiftedPairOuter, shiftedPairInner] using
      shiftedPair_regular a₀ a₁

end
end Red61

/-! Uniform annihilator bounds imply regularity after localization,
including regularity on an ideal quotient. The denominators remain in
the original monoid, and no Noetherian or domain hypothesis is required. -/

namespace Red61
noncomputable section
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B]

theorem isSMulRegular_localization_of_uniform (a : R) (v : S)
    (hv : ∀ r : R, r * a = 0 → (v : R) * r = 0) :
    IsSMulRegular B (algebraMap R B a) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  obtain ⟨⟨n, t⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  change algebraMap R B a * IsLocalization.mk' B n t = 0 at hx
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hx
  obtain ⟨u, hu⟩ := (IsLocalization.mk'_eq_zero_iff (M := S) (S := B) (a * n) t).mp hx
  have hn : ((u : R) * n) * a = 0 := by simpa only [mul_assoc, mul_comm n a] using hu
  exact (IsLocalization.mk'_eq_zero_iff (M := S) (S := B) n t).mpr
    ⟨v * u, by simpa only [Submonoid.coe_mul, mul_assoc] using hv ((u : R) * n) hn⟩

theorem isSMulRegular_quotient_localization_of_uniform (I : Ideal R) (a : R) (v : S)
    (hv : ∀ r : R, r * a ∈ I → (v : R) * r ∈ I) :
    IsSMulRegular (B ⧸ I.map (algebraMap R B)) (algebraMap R B a) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (I.map (algebraMap R B))
    (algebraMap R B a)).mpr
  intro x hx
  obtain ⟨⟨n, t⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  change algebraMap R B a * IsLocalization.mk' B n t ∈ I.map (algebraMap R B) at hx
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hx
  obtain ⟨u, hu, hun⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff S B I (a * n) t).mp hx
  have hn : (u * n) * a ∈ I := by simpa only [mul_assoc, mul_comm n a] using hun
  exact (IsLocalization.mk'_mem_map_algebraMap_iff S B I n t).mpr
    ⟨(v : R) * u, S.mul_mem v.property hu, by simpa only [mul_assoc] using hv (u * n) hn⟩
end
end Red61

/-! A weakly regular pair over an arbitrary localization of a
Noetherian ring is already weakly regular after inverting one original
denominator. Both the defining equations and the denominator are retained. -/

namespace Red61
noncomputable section
open RingTheory.Sequence
open scoped Pointwise
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B]

theorem isWeaklyRegular_pair_iff (a b : R) :
    IsWeaklyRegular R [a, b] ↔
      IsSMulRegular R a ∧ IsSMulRegular (R ⧸ Ideal.span {a}) b := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  have h : a • (⊤ : Submodule R R) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul]
    change Ideal.span {a} * ⊤ = Ideal.span {a}
    exact Ideal.mul_top _
  change IsSMulRegular R a ∧ IsSMulRegular (R ⧸ a • (⊤ : Submodule R R)) b ↔ _
  rw [h]

variable [IsNoetherianRing R]

end
end Red61

/-! A single principal localization of a Noetherian source
simultaneously preserves a given regular pair and its generation of
a localized ideal. All source equations and denominators are retained. -/

namespace Red61
noncomputable section
open RingTheory.Sequence
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] [IsNoetherianRing R]
include S in
theorem exists_away_regular_pair_ideal (I : Ideal R) (a b : R)
    (hJI : Ideal.ofList [a, b] ≤ I)
    (hI : I.map (algebraMap R B) = (Ideal.ofList [a, b]).map (algebraMap R B))
    (hreg : IsWeaklyRegular B [algebraMap R B a, algebraMap R B b]) :
    ∃ d : S,
      IsWeaklyRegular (Localization.Away (d : R))
        [algebraMap R (Localization.Away (d : R)) a,
          algebraMap R (Localization.Away (d : R)) b] ∧
      I.map (algebraMap R (Localization.Away (d : R))) =
        Ideal.ofList [algebraMap R (Localization.Away (d : R)) a,
          algebraMap R (Localization.Away (d : R)) b] := by
  obtain ⟨ha, hb⟩ := (isWeaklyRegular_pair_iff _ _).mp hreg
  have hi : (Ideal.span {a}).map (algebraMap R B) = Ideal.span {algebraMap R B a} := by
    simp only [Ideal.map_span, Set.image_singleton]
  rw [← hi] at hb
  obtain ⟨v, hv⟩ := exists_uniform_annihilator_multiplier S a ha
  obtain ⟨w, hw⟩ := exists_uniform_quotient_multiplier S (Ideal.span {a}) b hb
  have hfg : I.FG := (inferInstance : IsNoetherianRing R).noetherian I
  obtain ⟨u, hu⟩ := exists_uniform_multiplier_of_localized_ideal_le S hfg hI.le
  let d : S := u * v * w
  have hda (r : R) (hr : r * a = 0) : (d : R) * r = 0 := by
    calc
      (d : R) * r = ((u : R) * (w : R)) * ((v : R) * r) := by
        simp only [d, Submonoid.coe_mul]
        ring
      _ = 0 := by rw [hv r hr, mul_zero]
  have hdb (r : R) (hr : r * b ∈ Ideal.span {a}) : (d : R) * r ∈ Ideal.span {a} := by
    simpa only [d, Submonoid.coe_mul, mul_assoc] using
      (Ideal.span {a}).mul_mem_left ((u : R) * (v : R)) (hw r hr)
  have hdi (r : R) (hr : r ∈ I) : (d : R) * r ∈ Ideal.ofList [a, b] := by
    convert (Ideal.ofList [a, b]).mul_mem_left ((v : R) * (w : R)) (hu r hr) using 1
    simp only [d, Submonoid.coe_mul]
    ring
  refine ⟨d, (isWeaklyRegular_pair_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact isSMulRegular_localization_of_uniform (Submonoid.powers (d : R)) a
      ⟨d, Submonoid.mem_powers _⟩ hda
  · have hj : (Ideal.span {a}).map (algebraMap R (Localization.Away (d : R))) =
        Ideal.span {algebraMap R (Localization.Away (d : R)) a} := by
      simp only [Ideal.map_span, Set.image_singleton]
    rw [← hj]
    exact isSMulRegular_quotient_localization_of_uniform (Submonoid.powers (d : R))
      (Ideal.span {a}) b ⟨d, Submonoid.mem_powers _⟩ hdb
  · have he : I.map (algebraMap R (Localization.Away (d : R))) =
        (Ideal.ofList [a, b]).map (algebraMap R (Localization.Away (d : R))) := by
      apply le_antisymm ?_ (Ideal.map_mono hJI)
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change algebraMap R (Localization.Away (d : R)) r ∈
        (Ideal.ofList [a, b]).map (algebraMap R (Localization.Away (d : R)))
      exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (d : R))
        (Localization.Away (d : R)) (Ideal.ofList [a, b]) r).mpr
        ⟨d, Submonoid.mem_powers _, hdi r hr⟩
    simpa only [Ideal.map_ofList, List.map_cons, List.map_nil] using he
end
end Red61

/-! Multiplying each member of a regular pair by an arbitrary
unit preserves weak regularity. The quotient ideal is compared using
mathlib unit invariance of principal ideals. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {R : Type*} [CommRing R]
theorem weaklyRegular_pair_mul_units {a b u v : R} (hu : IsUnit u) (hv : IsUnit v)
    (h : IsWeaklyRegular R [a, b]) : IsWeaklyRegular R [u * a, v * b] := by
  obtain ⟨ha, hb⟩ := (isWeaklyRegular_pair_iff _ _).mp h
  apply (isWeaklyRegular_pair_iff _ _).mpr
  refine ⟨(hu.isSMulRegular R).mul ha, ?_⟩
  rw [Ideal.span_singleton_mul_left_unit hu]
  exact (hv.isSMulRegular (R ⧸ Ideal.span {a})).mul hb
end
end Red61

/-! A regular generating pair in a localization has regular
source numerators. They lie in the restricted kernel and generate its
localized ideal; denominator units are tracked in the calculation. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B]

include S in
theorem regular_pair_numerators (g : B →+* A) (x y : B)
    (hker : RingHom.ker g = Ideal.ofList [x, y]) (hreg : IsWeaklyRegular B [x, y]) :
    ∃ a b : R, Ideal.ofList [a, b] ≤ RingHom.ker (g.comp (algebraMap R B)) ∧
      (RingHom.ker (g.comp (algebraMap R B))).map (algebraMap R B) =
        (Ideal.ofList [a, b]).map (algebraMap R B) ∧
      IsWeaklyRegular B [algebraMap R B a, algebraMap R B b] := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj S x
  obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj S y
  have hx : g x = 0 := by
    apply hker.ge
    exact Ideal.subset_span (by simp)
  have hy : g y = 0 := by
    apply hker.ge
    exact Ideal.subset_span (by simp)
  have hga : g (algebraMap R B a) = 0 := by rw [← ha, map_mul, hx, zero_mul]
  have hgb : g (algebraMap R B b) = 0 := by rw [← hb, map_mul, hy, zero_mul]
  have hs := IsLocalization.map_units B s
  have ht := IsLocalization.map_units B t
  have hspan : (Ideal.ofList [a, b]).map (algebraMap R B) = RingHom.ker g := by
    rw [Ideal.map_ofList, hker]
    simp only [List.map_cons, List.map_nil, ← ha, ← hb, Ideal.ofList_cons, Ideal.ofList_nil,
      sup_bot_eq, Ideal.span_singleton_mul_right_unit hs,
      Ideal.span_singleton_mul_right_unit ht]
  refine ⟨a, b, ?_, ?_, ?_⟩
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hz
    rcases hz with rfl | rfl
    · exact hga
    · exact hgb
  · exact (kernel_of_localization_map S g).symm.trans hspan.symm
  · have hn := weaklyRegular_pair_mul_units hs ht hreg
    simpa only [mul_comm (algebraMap R B (s : R)) x,
      mul_comm (algebraMap R B (t : R)) y, ha, hb] using hn
end
end Red61

/-! A regular-pair kernel over a localization of a Noetherian
source descends to one principal localization. The target is kept fixed,
the restricted source map commutes, and the two equations remain regular. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] [IsNoetherianRing R] [Nontrivial A]

theorem exists_principal_regular_presentation (g : B →+* A) (x y : B)
    (hker : RingHom.ker g = Ideal.ofList [x, y]) (hreg : IsWeaklyRegular B [x, y]) :
    ∃ d : S, ∃ f : Localization.Away (d : R) →+* A, ∃ a b : R,
      f.comp (algebraMap R (Localization.Away (d : R))) = g.comp (algebraMap R B) ∧
      IsRegular (Localization.Away (d : R))
        [algebraMap R (Localization.Away (d : R)) a,
          algebraMap R (Localization.Away (d : R)) b] ∧
      RingHom.ker f = Ideal.ofList
        [algebraMap R (Localization.Away (d : R)) a,
          algebraMap R (Localization.Away (d : R)) b] := by
  obtain ⟨a, b, hJ, hI, hab⟩ := regular_pair_numerators S g x y hker hreg
  obtain ⟨d, hdreg, hdker⟩ := exists_away_regular_pair_ideal S
    (RingHom.ker (g.comp (algebraMap R B))) a b hJ hI hab
  have hu : IsUnit ((g.comp (algebraMap R B)) (d : R)) :=
    (IsLocalization.map_units B d).map g
  let f : Localization.Away (d : R) →+* A := IsLocalization.Away.lift (d : R) hu
  have he : f.comp (algebraMap R (Localization.Away (d : R))) =
      g.comp (algebraMap R B) := IsLocalization.Away.lift_comp (d : R) hu
  have hk : RingHom.ker f = Ideal.ofList
      [algebraMap R (Localization.Away (d : R)) a,
        algebraMap R (Localization.Away (d : R)) b] := by
    rw [kernel_of_localization_map (Submonoid.powers (d : R)) f, he]
    exact hdker
  refine ⟨d, f, a, b, he, ?_, hk⟩
  apply regular_of_weaklyRegular_of_killed hdreg f
  intro z hz
  exact hk.ge (Ideal.subset_span hz)
end
end Red61

/-! Principal-open regular-pair models retain their equations and
the actual quotient map. A surjective localized presentation makes its
original target a localization of this quotient, and a local target is
the native prime-localization ring of that finite-type model. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] (g : B →+* A)

structure PrincipalRegularPairModel where
  denominator : S
  left : R
  right : R
  regular : IsRegular (Localization.Away (denominator : R))
    [algebraMap R (Localization.Away (denominator : R)) left,
      algebraMap R (Localization.Away (denominator : R)) right]
  kernel : RingHom.ker
      (g.comp (awayLocalizationComparison (B := B) S denominator).toRingHom) =
    Ideal.ofList [algebraMap R (Localization.Away (denominator : R)) left,
      algebraMap R (Localization.Away (denominator : R)) right]

section Existence
variable [IsNoetherianRing R] [Nontrivial A]

theorem principalRegularPairModel_exists (x y : B)
    (hker : RingHom.ker g = Ideal.ofList [x, y]) (hreg : IsWeaklyRegular B [x, y]) :
    Nonempty (PrincipalRegularPairModel S g) := by
  obtain ⟨d, f, a, b, he, hr, hk⟩ :=
    exists_principal_regular_presentation S g x y hker hreg
  have hf : g.comp (awayLocalizationComparison (B := B) S d).toRingHom = f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (d : R))
    ext r
    change g (awayLocalizationComparison S d (algebraMap R (Localization.Away (d : R)) r)) =
      f (algebraMap R (Localization.Away (d : R)) r)
    exact (congrArg g ((awayLocalizationComparison (B := B) S d).commutes r)).trans
      (RingHom.congr_fun he r).symm
  exact ⟨{ denominator := d, left := a, right := b, regular := hr, kernel := hf ▸ hk }⟩
end Existence

namespace PrincipalRegularPairModel
variable (P : PrincipalRegularPairModel S g)

abbrev ambient := Localization.Away (P.denominator : R)

def map : P.ambient →+* A :=
  g.comp (awayLocalizationComparison (B := B) S P.denominator).toRingHom

abbrev quotient := P.ambient ⧸ RingHom.ker P.map

def denominators : Submonoid P.quotient :=
  (S.map (algebraMap R P.ambient)).map (Ideal.Quotient.mk (RingHom.ker P.map))

@[instance_reducible] def quotientAlgebra : Algebra P.quotient A := by
  let := awayLocalizationComparisonAlgebra (B := B) S P.denominator
  exact restrictedKernelQuotientAlgebra (R := P.ambient) g

theorem quotientMap_injective :
    letI := P.quotientAlgebra
    Function.Injective (algebraMap P.quotient A) := by
  let := P.quotientAlgebra
  exact RingHom.kerLift_injective P.map

include S in
theorem quotient_isLocalization (hg : Function.Surjective g) :
    letI := P.quotientAlgebra
    IsLocalization P.denominators A := by
  let := awayLocalizationComparisonAlgebra (B := B) S P.denominator
  have := awayLocalizationComparison_isLocalization (B := B) S P.denominator
  let := P.quotientAlgebra
  exact quotient_of_localization_isLocalization (R := P.ambient)
    (S.map (algebraMap R P.ambient)) g hg
variable [IsLocalRing A]

def quotientPrime : PrimeSpectrum P.quotient := by
  let := P.quotientAlgebra
  exact ⟨(IsLocalRing.maximalIdeal A).comap (algebraMap P.quotient A), inferInstance⟩

theorem quotient_isLocalization_atPrime (hg : Function.Surjective g) :
    letI := P.quotientAlgebra
    IsLocalization P.quotientPrime.asIdeal.primeCompl A := by
  let := P.quotientAlgebra
  have := quotient_isLocalization (R := R) (B := B) (A := A) S g P hg
  exact isLocalization_atPrime_of_local_target P.denominators

end PrincipalRegularPairModel
end
end Red61

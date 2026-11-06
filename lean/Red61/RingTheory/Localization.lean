import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Comparisons of localizations

Formerly the modules `AwayLocalizationComparison`, `FiniteIdealLocalization`, `FiniteTypeLocalizedRange`, `AwayLiftInjective`, `KernelLocalizationComparison`, `LocalTargetPrimeLocalization`, `PrincipalOpenInverse`, `CommonPrincipalOpen`, `CommonLocalizationNeighborhood`, `QuotientLocalizationModel`.
-/

/-! One original denominator gives a scalar-compatible principal
localization inside the full localization. The full target remains a
localization for the specified image denominator monoid. -/

namespace Red61
noncomputable section
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] (d : S)

def awayLocalizationComparison : Localization.Away (d : R) →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (A := R) (f := Algebra.ofId R B)
    (d : R) (IsLocalization.map_units B d)

@[instance_reducible] def awayLocalizationComparisonAlgebra :
    Algebra (Localization.Away (d : R)) B :=
  (awayLocalizationComparison (B := B) S d).toAlgebra

theorem awayLocalizationComparison_isLocalization :
    letI := awayLocalizationComparisonAlgebra (B := B) S d
    IsLocalization (S.map (algebraMap R (Localization.Away (d : R)))) B := by
  let := awayLocalizationComparisonAlgebra (B := B) S d
  have : IsScalarTower R (Localization.Away (d : R)) B :=
    IsScalarTower.of_algebraMap_eq' (awayLocalizationComparison (B := B) S d).comp_algebraMap.symm
  exact IsLocalization.isLocalization_of_submonoid_le (Localization.Away (d : R)) B
    (Submonoid.powers (d : R)) S (Submonoid.powers_le.mpr d.property)
end
end Red61

/-! A finitely generated ideal inclusion after localization can be
cleared by one element of the denominator monoid, uniformly for every
element of the ideal. No Noetherian hypothesis is required. -/

namespace Red61
noncomputable section
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] {I J : Ideal R}

theorem exists_uniform_multiplier_of_localized_ideal_le (hI : I.FG)
    (h : I.map (algebraMap R B) ≤ J.map (algebraMap R B)) :
    ∃ d : S, ∀ x ∈ I, (d : R) * x ∈ J := by
  classical
  have hc : ∀ t : Finset R, (∀ a ∈ t, ∃ d : S, (d : R) * a ∈ J) →
      ∃ d : S, ∀ a ∈ t, (d : R) * a ∈ J := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨1, by simp⟩
    | @insert a t ha ih =>
      intro hg
      obtain ⟨u, hu⟩ := hg a (Finset.mem_insert_self a t)
      obtain ⟨v, hv⟩ := ih (fun b hb ↦ hg b (Finset.mem_insert_of_mem hb))
      refine ⟨u * v, fun b hb ↦ ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · convert J.mul_mem_left (v : R) hu using 1
        simp only [Submonoid.coe_mul]
        ring
      · simpa only [Submonoid.coe_mul, mul_assoc] using J.mul_mem_left (u : R) (hv b hb)
  obtain ⟨t, ht⟩ := hI
  have hg : ∀ a ∈ t, ∃ d : S, (d : R) * a ∈ J := by
    intro a ha
    have haI : a ∈ I := ht ▸ Submodule.subset_span ha
    obtain ⟨d, hd, hda⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff S B J a).mp
      (h (Ideal.mem_map_of_mem (algebraMap R B) haI))
    exact ⟨⟨d, hd⟩, hda⟩
  obtain ⟨d, hd⟩ := hc t hg
  have hi : I ≤ Submodule.comap (LinearMap.mulLeft R (d : R)) J := by
    rw [← ht]
    exact Submodule.span_le.mpr (fun a ha ↦ hd a ha)
  exact ⟨d, fun x hx ↦ hi hx⟩
end
end Red61

/-! Finite algebra generators have a common original denominator. If the
original localization map is injective, this gives a scalar-compatible
factorization through a single principal localization. -/

namespace Red61
noncomputable section
variable (F : Type*) [CommRing F] {R A : Type*} [CommRing R] [CommRing A]
  [Algebra F R] [Algebra F A] [Algebra R A] [IsScalarTower F R A]
  (S : Submonoid R) [IsLocalization S A]

def awayLocalizationBaseMap (d : S) : Localization.Away (d : R) →ₐ[F] A :=
  (awayLocalizationComparison (B := A) S d).restrictScalars F

variable {Q : Type*} [CommRing Q] [Algebra F Q] [Algebra.FiniteType F Q]

theorem exists_away_range_contains (f : Q →ₐ[F] A) :
    ∃ d : S, f.range ≤ (awayLocalizationBaseMap (A := A) F S d).range := by
  classical
  obtain ⟨t, ht⟩ := (inferInstance : Algebra.FiniteType F Q).out
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples S t f
  let β := awayLocalizationComparison (B := A) S d
  have hu : IsUnit (algebraMap R A (d : R)) := IsLocalization.map_units A d
  have hsub : Algebra.adjoin F (t : Set Q) ≤
      Subalgebra.comap f (awayLocalizationBaseMap (A := A) F S d).range := by
    apply Algebra.adjoin_le
    intro a ha
    obtain ⟨n, hn⟩ := hd a ha
    let q : Localization.Away (d : R) :=
      IsLocalization.mk' _ n ⟨(d : R), Submonoid.mem_powers (d : R)⟩
    have hq : algebraMap R A (d : R) * β q = algebraMap R A n := by
      have h := congrArg β (IsLocalization.mk'_spec' (Localization.Away (d : R)) n
        ⟨(d : R), Submonoid.mem_powers (d : R)⟩)
      simpa only [map_mul, AlgHom.commutes] using h
    have hn' : algebraMap R A n = algebraMap R A (d : R) * f a := by
      simpa only [Algebra.smul_def] using hn
    refine ⟨q, (IsUnit.mul_left_inj hu).mp ?_⟩
    exact (mul_comm (β q) (algebraMap R A (d : R))).trans
      ((hq.trans hn').trans (mul_comm (algebraMap R A (d : R)) (f a)))
  rw [ht] at hsub
  refine ⟨d, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := hz
  exact hsub (show a ∈ (⊤ : Subalgebra F Q) from trivial)
theorem awayLocalizationBaseMap_injective (hinj : Function.Injective (algebraMap R A))
    (d : S) : Function.Injective (awayLocalizationBaseMap (A := A) F S d) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (d : R))
    (awayLocalizationBaseMap (A := A) F S d).toRingHom).mpr
  intro x y
  constructor
  · exact congrArg (awayLocalizationBaseMap (A := A) F S d)
  · intro hxy
    let β := awayLocalizationComparison (B := A) S d
    have he : algebraMap R A x = algebraMap R A y :=
      ((β.commutes x).symm.trans hxy).trans (β.commutes y)
    exact congrArg (algebraMap R (Localization.Away (d : R))) (hinj he)

theorem exists_away_factorization (hinj : Function.Injective (algebraMap R A))
    (f : Q →ₐ[F] A) :
    ∃ d : S, ∃ g : Q →ₐ[F] Localization.Away (d : R),
      (awayLocalizationBaseMap (A := A) F S d).comp g = f := by
  obtain ⟨d, hd⟩ := exists_away_range_contains F S f
  let β := awayLocalizationBaseMap (A := A) F S d
  let e := AlgEquiv.ofInjective β (awayLocalizationBaseMap_injective F S hinj d)
  let f' := f.codRestrict β.range (fun x ↦ hd (f.mem_range_self x))
  refine ⟨d, e.symm.toAlgHom.comp f', ?_⟩
  ext x
  exact congrArg (fun z : β.range ↦ (z : A)) (e.apply_symm_apply (f' x))

end
end Red61

/-! The principal localization lift of an injective algebra map stays
injective whenever the inverted element maps to a unit. -/

namespace Red61
noncomputable section
variable {F R A : Type*} [CommRing F] [CommRing R] [CommRing A]
  [Algebra F R] [Algebra F A]

theorem awayLiftAlgHom_injective (f : R →ₐ[F] A) (d : R) (hu : IsUnit (f d))
    (hf : Function.Injective f) :
    Function.Injective (IsLocalization.Away.liftAlgHom (A := F) (f := f) d hu :
      Localization.Away d →ₐ[F] A) := by
  let g : Localization.Away d →ₐ[F] A := IsLocalization.Away.liftAlgHom d hu
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d)
    g.toRingHom).mpr
  intro x y
  constructor
  · exact congrArg g
  · intro hxy
    have he : f x = f y :=
      (IsLocalization.Away.lift_eq d hu x).symm.trans
        (hxy.trans (IsLocalization.Away.lift_eq d hu y))
    exact congrArg (algebraMap R (Localization.Away d)) (hf he)
end
end Red61

/-! The kernel of any map out of a localization is the localized
kernel of its restriction. The proof reuses mathlib kernel localization
with the image denominator monoid, whose elements are actual target units. -/

namespace Red61
noncomputable section
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B]

include S in
theorem kernel_of_localization_map (g : B →+* A) :
    RingHom.ker g = (RingHom.ker (g.comp (algebraMap R B))).map (algebraMap R B) := by
  let f : R →+* A := g.comp (algebraMap R B)
  have ht : S.map f ≤ IsUnit.submonoid A := by
    rintro x ⟨r, hr, rfl⟩
    exact (IsLocalization.map_units B ⟨r, hr⟩).map g
  have : IsLocalization (S.map f) A := IsLocalization.of_le_isUnit ht
  have he : (IsLocalization.map A f S.le_comap_map : B →+* A) = g := by
    apply IsLocalization.ringHom_ext S
    rw [IsLocalization.map_comp]
    rfl
  have hk := IsLocalization.ker_map (S := B) (M := S) (T := S.map f) A f rfl
  rw [he] at hk
  exact hk
end
end Red61

/-! A localization that is a local ring is a prime localization
at the preimage of its maximal ideal. The denominator enlargement
uses actual target units. -/

namespace Red61
noncomputable section
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (M : Submonoid R) [IsLocalization M A] [IsLocalRing A]
include M in
theorem isLocalization_atPrime_of_local_target :
    IsLocalization ((IsLocalRing.maximalIdeal A).comap (algebraMap R A)).primeCompl A := by
  apply IsLocalization.of_le (M := M)
    ((IsLocalRing.maximalIdeal A).comap (algebraMap R A)).primeCompl
  · intro r hr
    change algebraMap R A r ∉ IsLocalRing.maximalIdeal A
    exact IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units A ⟨r, hr⟩)
  · intro r hr
    exact IsLocalRing.notMem_maximalIdeal.mp hr
end
end Red61

/-! Compatible inverse maps on original generators extend uniquely to
an algebra isomorphism between the corresponding principal localizations. -/

namespace Red61
noncomputable section
variable {F Q R : Type*} [CommRing F] [CommRing Q] [CommRing R]
  [Algebra F Q] [Algebra F R]
  (f : Q →ₐ[F] R) (e : Q) (h : R →ₐ[F] Localization.Away e)
  (hh : h.comp f = (IsScalarTower.toAlgHom F Q (Localization.Away e)))
  (hj : (Localization.awayMapₐ f e).comp h =
    IsScalarTower.toAlgHom F R (Localization.Away (f e)))

def principalOpenInverse : Localization.Away e ≃ₐ[F] Localization.Away (f e) := by
  have hu : IsUnit (h (f e)) := by
    rw [← AlgHom.comp_apply, hh]
    exact IsLocalization.Away.algebraMap_isUnit e
  let k : Localization.Away (f e) →ₐ[F] Localization.Away e :=
    IsLocalization.Away.liftAlgHom (A := F) (f := h) (f e) hu
  let j := Localization.awayMapₐ f e
  apply AlgEquiv.ofAlgHom j k
  · apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (f e))
    ext r
    change j (k (algebraMap R (Localization.Away (f e)) r)) =
      algebraMap R (Localization.Away (f e)) r
    rw [show k (algebraMap R (Localization.Away (f e)) r) = h r from
      IsLocalization.Away.lift_eq (f e) hu r]
    exact AlgHom.congr_fun hj r
  · apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers e)
    ext q
    change k (j (algebraMap Q (Localization.Away e) q)) =
      algebraMap Q (Localization.Away e) q
    have he : j (algebraMap Q (Localization.Away e) q) =
        algebraMap R (Localization.Away (f e)) (f q) := by
      simp only [j, Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply,
        IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    rw [he]
    rw [show k (algebraMap R (Localization.Away (f e)) (f q)) = h (f q) from
      IsLocalization.Away.lift_eq (f e) hu (f q)]
    exact AlgHom.congr_fun hh q
end
end Red61

/-! Two injective finite-model maps into a common algebra determine
an isomorphism of principal opens when their factorizations commute. -/

namespace Red61
noncomputable section
variable {F Q R A : Type*} [CommRing F] [CommRing Q] [CommRing R] [CommRing A]
  [Algebra F Q] [Algebra F R] [Algebra F A]
  (u : Q →ₐ[F] A) (v : R →ₐ[F] A)
  (f : Q →ₐ[F] R) (hvf : v.comp f = u)
  (e : Q) (hu : IsUnit (u e))
  (h : R →ₐ[F] Localization.Away e)
  (hf : (IsLocalization.Away.liftAlgHom (A := F) (f := u) e hu :
    Localization.Away e →ₐ[F] A).comp h = v)
  (hiu : Function.Injective u) (hiv : Function.Injective v)

def commonPrincipalOpenEquiv : Localization.Away e ≃ₐ[F] Localization.Away (f e) := by
  let α : Localization.Away e →ₐ[F] A := IsLocalization.Away.liftAlgHom e hu
  have hα : Function.Injective α := awayLiftAlgHom_injective u e hu hiu
  have hv : IsUnit (v (f e)) := by rw [← AlgHom.comp_apply, hvf]; exact hu
  let β : Localization.Away (f e) →ₐ[F] A := IsLocalization.Away.liftAlgHom (f e) hv
  have hβ : Function.Injective β := awayLiftAlgHom_injective v (f e) hv hiv
  let j := Localization.awayMapₐ f e
  have hβα : β.comp j = α := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers e)
    ext q
    change β (j (algebraMap Q (Localization.Away e) q)) =
      α (algebraMap Q (Localization.Away e) q)
    have hj : j (algebraMap Q (Localization.Away e) q) =
        algebraMap R (Localization.Away (f e)) (f q) := by
      simp only [j, Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply,
        IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    rw [hj]
    change (IsLocalization.Away.lift (f e) hv) (algebraMap R _ (f q)) =
      (IsLocalization.Away.lift e hu) (algebraMap Q _ q)
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    exact AlgHom.congr_fun hvf q
  apply principalOpenInverse f e h
  · ext q
    apply hα
    change α (h (f q)) = α (algebraMap Q (Localization.Away e) q)
    calc
      α (h (f q)) = v (f q) := AlgHom.congr_fun hf (f q)
      _ = u q := AlgHom.congr_fun hvf q
      _ = α (algebraMap Q (Localization.Away e) q) :=
        (IsLocalization.Away.lift_eq e hu q).symm
  · ext r
    apply hβ
    change β (j (h r)) = β (algebraMap R (Localization.Away (f e)) r)
    calc
      β (j (h r)) = α (h r) := AlgHom.congr_fun hβα (h r)
      _ = v r := AlgHom.congr_fun hf r
      _ = β (algebraMap R (Localization.Away (f e)) r) :=
        (IsLocalization.Away.lift_eq (f e) hv r).symm
end
end Red61

/-! Two finite-type algebras with injective maps into the same
localization have isomorphic principal-open refinements. Original
denominator membership records the neighborhoods of the original point. -/

namespace Red61
noncomputable section
variable (F : Type*) [CommRing F] {R Q A : Type*}
  [CommRing R] [CommRing Q] [CommRing A]
  [Algebra F R] [Algebra F Q] [Algebra F A]
  [Algebra R A] [Algebra Q A] [IsScalarTower F R A] [IsScalarTower F Q A]
  [Algebra.FiniteType F R] [Algebra.FiniteType F Q]
  (S : Submonoid R) (T : Submonoid Q) [IsLocalization S A] [IsLocalization T A]

theorem exists_common_principal_open
    (hinjR : Function.Injective (algebraMap R A))
    (hinjQ : Function.Injective (algebraMap Q A)) :
    ∃ d : S, ∃ e : T, ∃ f : Q →ₐ[F] Localization.Away (d : R),
      (awayLocalizationBaseMap (A := A) F S d).comp f = IsScalarTower.toAlgHom F Q A ∧
      Nonempty (Localization.Away (e : Q) ≃ₐ[F] Localization.Away (f (e : Q))) := by
  let u := IsScalarTower.toAlgHom F Q A
  obtain ⟨d, f, hf⟩ := exists_away_factorization F S hinjR u
  let v := awayLocalizationBaseMap (A := A) F S d
  have hv : Function.Injective v := awayLocalizationBaseMap_injective F S hinjR d
  obtain ⟨e, h, hh⟩ := exists_away_factorization F T hinjQ v
  have hu : IsUnit (u (e : Q)) := IsLocalization.map_units A e
  have hα : (IsLocalization.Away.liftAlgHom (A := F) (f := u) (e : Q) hu :
      Localization.Away (e : Q) →ₐ[F] A) = awayLocalizationBaseMap (A := A) F T e := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (e : Q))
    ext q
    change (IsLocalization.Away.lift (e : Q) hu) (algebraMap Q _ q) =
      awayLocalizationComparison T e (algebraMap Q (Localization.Away (e : Q)) q)
    rw [IsLocalization.Away.lift_eq, (awayLocalizationComparison (B := A) T e).commutes]
    rfl
  refine ⟨d, e, f, hf, ?_⟩
  apply Nonempty.intro
  apply commonPrincipalOpenEquiv u v f hf (e : Q) hu h
  · rw [hα]
    exact hh
  · exact hinjQ
  · exact hv
end
end Red61

/-! A surjective quotient of a localization is the localization of
the restricted kernel quotient. The coefficient algebra is the actual
quotient lift, and mathlib supplies the localization diagram. -/

namespace Red61
noncomputable section
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B]
  (S : Submonoid R) [IsLocalization S B] (g : B →+* A) (hg : Function.Surjective g)

def restrictedKernelQuotientMap :
    (R ⧸ RingHom.ker (g.comp (algebraMap R B))) →+* A :=
  Ideal.Quotient.lift _ (g.comp (algebraMap R B)) (fun _ hx ↦ hx)

@[instance_reducible] def restrictedKernelQuotientAlgebra :
    Algebra (R ⧸ RingHom.ker (g.comp (algebraMap R B))) A :=
  (restrictedKernelQuotientMap (R := R) g).toAlgebra

include S hg in
theorem quotient_of_localization_isLocalization :
    letI := restrictedKernelQuotientAlgebra (R := R) g
    IsLocalization (S.map (Ideal.Quotient.mk (RingHom.ker (g.comp (algebraMap R B))))) A := by
  let := restrictedKernelQuotientAlgebra (R := R) g
  apply IsLocalization.of_surjective (M := S) B
    (Ideal.Quotient.mk (RingHom.ker (g.comp (algebraMap R B))))
    Ideal.Quotient.mk_surjective g hg
  · ext r
    rfl
  · rw [Ideal.mk_ker]
    exact (kernel_of_localization_map S g).le
end
end Red61

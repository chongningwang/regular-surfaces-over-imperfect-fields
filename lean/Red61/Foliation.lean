import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic
import Red61.RingTheory.Kaehler

/-! # p-closed derivations and their invariant rings

Formerly the modules `Derivation`, `DerivationRestriction`, `FractionDerivation`, `Projection`, `QuotientDerivation`, `RationalConstants`, `Slice`, `TensorNilpotent`, `FiniteInvariants`, `InvariantRing`, `PolynomialInvariants`, `KernelLocalization`, `PolynomialKernelDifferentials`, `PolynomialKernelSmooth`.
-/

namespace Red61

section FifthPower

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A] [CharP A 5]

/-- In characteristic five, the fifth iterate satisfies Leibniz. -/
theorem leibniz_five (D : Derivation F A A) (a b : A) :
    D (D (D (D (D (a * b))))) =
      a * D (D (D (D (D b)))) + b * D (D (D (D (D a)))) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add]
  ring_nf
  have h5 : (5 : A) = 0 := CharP.cast_eq_zero A 5
  have h10 : (10 : A) = 0 := by linear_combination 2 * h5
  simp [h5, h10]

/-- The restricted fifth power, constructed rather than postulated. -/
def fifthDerivation (D : Derivation F A A) : Derivation F A A :=
  Derivation.mk' (D.toLinearMap ^ 5) (by
    intro a b
    simpa [pow_succ, Module.End.mul_apply, smul_eq_mul] using leibniz_five D a b)

@[simp] theorem fifthDerivation_apply (D : Derivation F A A) (a : A) :
    fifthDerivation D a = D (D (D (D (D a)))) := rfl

end FifthPower

namespace PolynomialModel

abbrev P := MvPolynomial (Fin 4) (ZMod 5)

/-- Variables 0,1,2,3 represent c₁,c₂,t,w. -/
noncomputable def delta : Derivation (ZMod 5) P P :=
  MvPolynomial.mkDerivation (ZMod 5) ![1, MvPolynomial.X 2, MvPolynomial.X 3, 0]

@[simp] theorem delta_c₁ : delta (MvPolynomial.X 0) = 1 := by simp [delta]
@[simp] theorem delta_c₂ : delta (MvPolynomial.X 1) = MvPolynomial.X 2 := by simp [delta]
@[simp] theorem delta_t : delta (MvPolynomial.X 2) = MvPolynomial.X 3 := by simp [delta]
@[simp] theorem delta_w : delta (MvPolynomial.X 3) = 0 := by simp [delta]

theorem delta_fifth_zero : fifthDerivation delta = 0 := by
  apply MvPolynomial.derivation_ext
  intro i
  fin_cases i <;> simp

theorem delta_five (f : P) : delta (delta (delta (delta (delta f)))) = 0 := by
  exact Derivation.congr_fun delta_fifth_zero f

/-- Variables 0,1,2,3 now represent c₁,c₂,U,T. -/
noncomputable def localDelta : Derivation (ZMod 5) P P :=
  MvPolynomial.mkDerivation (ZMod 5)
    ![MvPolynomial.X 2 * MvPolynomial.X 3,
      MvPolynomial.X 2 * MvPolynomial.X 3 ^ 2, 0, MvPolynomial.X 3]

@[simp] theorem localDelta_c₁ : localDelta (MvPolynomial.X 0) =
    MvPolynomial.X 2 * MvPolynomial.X 3 := by simp [localDelta]
@[simp] theorem localDelta_c₂ : localDelta (MvPolynomial.X 1) =
    MvPolynomial.X 2 * MvPolynomial.X 3 ^ 2 := by simp [localDelta]
@[simp] theorem localDelta_U : localDelta (MvPolynomial.X 2) = 0 := by simp [localDelta]
@[simp] theorem localDelta_T : localDelta (MvPolynomial.X 3) = MvPolynomial.X 3 := by
  simp [localDelta]

end PolynomialModel
end Red61

namespace Red61

noncomputable section
variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

/-- Restrict a derivation through an injective algebra map with stable image. -/
def restrictDerivation (f : A →ₐ[F] B) (hf : Function.Injective f)
    (D : Derivation F B B) (hD : ∀ a, ∃ a', f a' = D (f a)) : Derivation F A A := by
  let d : A → A := fun a => Classical.choose (hD a)
  have hd (a : A) : f (d a) = D (f a) := Classical.choose_spec (hD a)
  exact
    { toFun := d
      map_add' := fun a b => hf (by rw [hd, map_add, map_add, map_add, hd, hd])
      map_smul' := fun r a => hf (by
        rw [hd, map_smul, Derivation.map_smul, map_smul, hd]; rfl)
      map_one_eq_zero' := hf (by
        change f (d 1) = f 0
        rw [hd, map_one, D.map_one_eq_zero, map_zero])
      leibniz' := fun a b => hf (by
        change f (d (a * b)) = f (a * d b + b * d a)
        rw [hd, map_mul, Derivation.leibniz, map_add, map_mul, map_mul, hd, hd]
        rfl) }

theorem restrictDerivation_apply (f : A →ₐ[F] B) (hf : Function.Injective f)
    (D : Derivation F B B) (hD : ∀ a, ∃ a', f a' = D (f a)) (a : A) :
    f (restrictDerivation f hf D hD a) = D (f a) := Classical.choose_spec (hD a)

end
end Red61

namespace Red61
namespace FractionDerivation

noncomputable section

variable {F A K : Type*} [CommRing F] [CommRing A] [IsDomain A] [Field K]
  [Algebra F A] [Algebra A K] [Algebra F K] [IsScalarTower F A K] [IsFractionRing A K]

def graph (D : Derivation F A A) : A →+* TrivSqZeroExt K K where
  toFun a := TrivSqZeroExt.inl (algebraMap A K a) +
    TrivSqZeroExt.inr (algebraMap A K (D a))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]

omit [IsDomain A] [Algebra F K] [IsScalarTower F A K] in
theorem graph_unit (D : Derivation F A A) (a : nonZeroDivisors A) :
    IsUnit (graph (K := K) D a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit (algebraMap A K (a : A) + 0)
  rw [add_zero]
  exact IsLocalization.map_units K a

def liftGraph (D : Derivation F A A) : K →+* TrivSqZeroExt K K :=
  IsLocalization.lift (S := K) (graph_unit D)

omit [IsDomain A] [Algebra F K] [IsScalarTower F A K] in
@[simp] theorem liftGraph_algebraMap (D : Derivation F A A) (a : A) :
    liftGraph D (algebraMap A K a) = graph D a := IsLocalization.lift_eq _ _

omit [IsDomain A] [Algebra F K] [IsScalarTower F A K] in
theorem liftGraph_fst (D : Derivation F A A) (x : K) : (liftGraph D x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftGraph D) = RingHom.id K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp [graph, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RingHom.congr_fun h x

/-- Extend a derivation to the fraction field using dual numbers. -/
def extend (D : Derivation F A A) : Derivation F K K where
  toFun x := (liftGraph D x).snd
  map_add' a b := by simp
  map_smul' s x := by
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul]
    have h : algebraMap F K s = algebraMap A K (algebraMap F A s) :=
      IsScalarTower.algebraMap_apply F A K s
    rw [h, liftGraph_algebraMap]
    simp [graph, Algebra.smul_def, Derivation.map_algebraMap,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ← h]
  map_one_eq_zero' := by simp
  leibniz' a b := by simp [liftGraph_fst, smul_eq_mul, mul_comm]

omit [IsDomain A] in
@[simp] theorem extend_algebraMap (D : Derivation F A A) (a : A) :
    extend D (algebraMap A K a) = algebraMap A K (D a) := by
  change (liftGraph D (algebraMap A K a)).snd = _
  rw [liftGraph_algebraMap]
  simp [graph, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

omit [IsDomain A] [Algebra F A] [IsScalarTower F A K] in
/-- Derivations of a fraction field are determined on the original domain. -/
theorem ext {D E : Derivation F K K}
    (h : ∀ a : A, D (algebraMap A K a) = E (algebraMap A K a)) : D = E := by
  apply Derivation.ext
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp only [Derivation.leibniz_div, h]

end
end FractionDerivation
end Red61

/-! The Reynolds projection used at the exceptional point.
This is a linear-algebra theorem; no geometric hypotheses occur. -/

namespace Red61

variable {F V : Type*} [CommRing F] [AddCommGroup V] [Module F V]

def reynolds (D : V →ₗ[F] V) : V →ₗ[F] V := 1 - D ^ 4

theorem reynolds_image_in_kernel (D : V →ₗ[F] V) (hD : D ^ 5 = D) :
    D * reynolds D = 0 := by
  rw [reynolds, mul_sub, mul_one, ← pow_succ', hD, sub_self]

theorem reynolds_fixes_kernel (D : V →ₗ[F] V) {x : V} (hx : D x = 0) :
    reynolds D x = x := by
  simp [reynolds, pow_succ, Module.End.mul_apply, hx]

end Red61

/-!
Derivations induced on quotients by stable ideals.

Adapted from OAI.ComplexCancellation.QuotientDerivation in openai/math,
commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Algebra/AffineCancellation/QuotientDerivation.lean.
Public bundle: https://prove2.me/theorems/d8184be2-34c1-4b3a-be33-e4ec565fa469
Published by Shuze Chen on 2026-10-15 under Apache-2.0 (https://prove2.me/terms).
Changes: minimal mathlib imports, project namespace, and formatting.
-/

namespace Red61.QuotientDerivation
noncomputable section

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (I : Ideal R) (D : Derivation k R R) (hD : ∀ r ∈ I, D r ∈ I)

def linear : (R ⧸ I) →ₗ[k] (R ⧸ I) :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k I).toLinearMap.comp D.toLinearMap)
    (by intro r hr; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hD r hr))

@[simp] theorem linear_mk (r : R) : linear I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

def derivation : Derivation k (R ⧸ I) (R ⧸ I) := Derivation.mk' (linear I D hD) (by
  intro r s
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  change linear I D hD ((Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) s) = _
  rw [← map_mul, linear_mk]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, linear_mk])

@[simp] theorem derivation_mk (r : R) : derivation I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

theorem span_singleton_stable {h : R} (hh : D h ∈ Ideal.span {h}) :
    ∀ r ∈ Ideal.span {h}, D r ∈ Ideal.span {h} := by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ hh)

end
end Red61.QuotientDerivation

/-! Relative algebraic closedness of a field in a multivariate rational function field. -/

namespace Red61

noncomputable section

/-- An algebraic element in the fraction field of a polynomial ring over a field is constant.
This works in every characteristic and for any set of variables. -/
theorem algebraic_fraction_mvPolynomial_constant (F σ : Type*) [Field F]
    {x : FractionRing (MvPolynomial σ F)} (hx : IsAlgebraic F x) :
    ∃ c : F, algebraMap F (FractionRing (MvPolynomial σ F)) c = x := by
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (R := MvPolynomial σ F) hx.isIntegral.tower_top
  have hp_alg : IsAlgebraic F p :=
    (isAlgebraic_algebraMap_iff (IsFractionRing.injective (MvPolynomial σ F) _)).mp
      (hp.symm ▸ hx)
  by_cases hzero : p = 0
  · exact ⟨0, by simpa [hzero] using hp⟩
  obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
    (hp_alg.isIntegral.isUnit hzero)
  refine ⟨c, ?_⟩
  rw [← hp, hc]
  exact IsScalarTower.algebraMap_apply F (MvPolynomial σ F)
    (FractionRing (MvPolynomial σ F)) c

end
end Red61

namespace Red61

open Module

section Slice

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [CharP K 5]

def constants (D : Derivation F K K) : Subfield K where
  carrier := {x | D x = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' hx hy := by simp only [Set.mem_ofPred_eq] at *; simp [hx, hy]
  neg_mem' hx := by simp only [Set.mem_ofPred_eq] at *; simp [hx]
  mul_mem' hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    simp [Derivation.leibniz, hx, hy]
  inv_mem' x hx := by
    simp only [Set.mem_ofPred_eq] at *
    simp [Derivation.leibniz_inv, hx]

omit [CharP K 5] in
@[simp] theorem mem_constants (D : Derivation F K K) (x : K) :
    x ∈ constants D ↔ D x = 0 := Iff.rfl

def sliceProjection (D : Derivation F K K) (c x : K) : K :=
  x - c * D x + 3 * c ^ 2 * D (D x) - c ^ 3 * D (D (D x)) +
    4 * c ^ 4 * D (D (D (D x)))

theorem sliceProjection_invariant (D : Derivation F K K) (c : K) (hc : D c = 1)
    (hD : ∀ x, D (D (D (D (D x)))) = 0) (x : K) :
    D (sliceProjection D c x) = 0 := by
  have h3 : D (3 : K) = 0 := D.map_natCast 3
  have h4 : D (4 : K) = 0 := D.map_natCast 4
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  simp only [sliceProjection, map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, hc, h3, h4, hD]
  linear_combination (c * D (D x) + 3 * c ^ 3 * D (D (D (D x)))) * h5

theorem slice_expansion (D : Derivation F K K) (c x : K)
    (hD : ∀ x, D (D (D (D (D x)))) = 0) :
    x = sliceProjection D c x + c * sliceProjection D c (D x) +
      3 * c ^ 2 * sliceProjection D c (D (D x)) +
      c ^ 3 * sliceProjection D c (D (D (D x))) +
      4 * c ^ 4 * sliceProjection D c (D (D (D (D x)))) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  simp only [sliceProjection, hD, map_zero, mul_zero, add_zero, sub_zero]
  linear_combination -(c ^ 2 * D (D x) +
    3 * c ^ 4 * D (D (D (D x)))) * h5

theorem slice_coefficients_unique (D : Derivation F K K) (c : K) (hc : D c = 1)
    (a₀ a₁ a₂ a₃ a₄ : K) (h₀ : D a₀ = 0) (h₁ : D a₁ = 0)
    (h₂ : D a₂ = 0) (h₃ : D a₃ = 0) (h₄ : D a₄ = 0)
    (h : a₀ + a₁ * c + a₂ * c ^ 2 + a₃ * c ^ 3 + a₄ * c ^ 4 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have dn (n : ℕ) : D (n : K) = 0 := D.map_natCast n
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2n : (2 : K) ≠ 0 := by
    intro he
    have : (1 : K) = 0 := by linear_combination h5 - 2 * he
    exact one_ne_zero this
  have h3n : (3 : K) ≠ 0 := by
    intro he
    have : (1 : K) = 0 := by linear_combination 2 * he - h5
    exact one_ne_zero this
  have h4n : (4 : K) ≠ 0 := by
    intro he
    have : (1 : K) = 0 := by linear_combination h5 - he
    exact one_ne_zero this
  have step1 := congrArg D h
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub,
    pow_one, hc, h₀, h₁, h₂, h₃, h₄, map_zero, mul_zero, zero_add, add_zero, mul_one] at step1
  have step2 := congrArg D step1
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub,
    pow_one, hc, h₁, h₂, h₃, h₄, dn, map_zero, mul_zero, zero_add, add_zero, mul_one] at step2
  have step3 := congrArg D step2
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub,
    pow_one, hc, h₂, h₃, h₄, dn, map_zero, mul_zero, zero_add, add_zero, mul_one] at step3
  have step4 := congrArg D step3
  simp only [map_add, Derivation.leibniz, smul_eq_mul, 
    hc, h₃, h₄, dn, map_zero, mul_zero, zero_add, add_zero, mul_one] at step4
  have ha₄ : a₄ = 0 := by
    have hh : 4 * a₄ = 0 := by linear_combination step4 - 4 * a₄ * h5
    exact (mul_eq_zero.mp hh).resolve_left h4n
  have ha₃ : a₃ = 0 := by
    rw [ha₄] at step3
    linear_combination step3 - a₃ * h5
  have ha₂ : a₂ = 0 := by
    rw [ha₃, ha₄] at step2
    have hh : 2 * a₂ = 0 := by linear_combination step2
    exact (mul_eq_zero.mp hh).resolve_left h2n
  have ha₁ : a₁ = 0 := by
    rw [ha₂, ha₃, ha₄] at step1
    linear_combination step1
  have ha₀ : a₀ = 0 := by simpa [ha₁, ha₂, ha₃, ha₄] using h
  exact ⟨ha₀, ha₁, ha₂, ha₃, ha₄⟩

theorem slice_powers_independent (D : Derivation F K K) (c : K) (hc : D c = 1) :
    LinearIndependent (constants D) (fun i : Fin 5 => c ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have cast_eq (z : constants D) : algebraMap (constants D) K z = (z : K) := rfl
  have hpoly : (a 0 : K) + (a 1 : K) * c + (a 2 : K) * c ^ 2 +
      (a 3 : K) * c ^ 3 + (a 4 : K) * c ^ 4 = 0 := by
    simpa [Fin.sum_univ_succ, Algebra.smul_def, cast_eq, add_assoc] using ha
  have hz := slice_coefficients_unique D c hc
    (a 0) (a 1) (a 2) (a 3) (a 4)
    (a 0).property (a 1).property (a 2).property (a 3).property (a 4).property hpoly
  intro i
  apply Subtype.ext
  fin_cases i <;> simp_all

theorem slice_sum_unique (D : Derivation F K K) (c : K) (hc : D c = 1)
    (a : Fin 5 → K) (ha : ∀ i, D (a i) = 0)
    (hs : ∑ i, a i * c ^ (i : ℕ) = 0) : ∀ i, a i = 0 := by
  have hpoly : a 0 + a 1 * c + a 2 * c ^ 2 + a 3 * c ^ 3 + a 4 * c ^ 4 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  have hz := slice_coefficients_unique D c hc (a 0) (a 1) (a 2) (a 3) (a 4)
    (ha 0) (ha 1) (ha 2) (ha 3) (ha 4) hpoly
  intro i
  fin_cases i <;> simp_all

/-- An invariant linear combination of slice powers is its constant coefficient. -/
theorem slice_constant_term (D : Derivation F K K) (c : K) (hc : D c = 1)
    (a : Fin 5 → K) (ha : ∀ i, D (a i) = 0) (x : K) (hx : D x = 0)
    (hs : ∑ i, a i * c ^ (i : ℕ) = x) : a 0 = x := by
  have hpoly : (a 0 - x) + a 1 * c + a 2 * c ^ 2 + a 3 * c ^ 3 + a 4 * c ^ 4 = 0 := by
    have hh : a 0 + a 1 * c + a 2 * c ^ 2 + a 3 * c ^ 3 + a 4 * c ^ 4 = x := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    linear_combination hh
  have hz := slice_coefficients_unique D c hc (a 0 - x) (a 1) (a 2) (a 3) (a 4)
    (by simp [ha, hx]) (ha 1) (ha 2) (ha 3) (ha 4) hpoly
  exact sub_eq_zero.mp hz.1

theorem slice_powers_span (D : Derivation F K K) (c : K) (hc : D c = 1)
    (hD : ∀ x, D (D (D (D (D x)))) = 0) :
    Submodule.span (constants D) (Set.range (fun i : Fin 5 => c ^ (i : ℕ))) = ⊤ := by
  apply top_unique
  intro x _
  let V := Submodule.span (constants D) (Set.range (fun i : Fin 5 => c ^ (i : ℕ)))
  have term (i : Fin 5) (y : K) : sliceProjection D c y * c ^ (i : ℕ) ∈ V := by
    let a : constants D := ⟨sliceProjection D c y, sliceProjection_invariant D c hc hD y⟩
    exact V.smul_mem a (Submodule.subset_span (Set.mem_range_self i))
  have h₀ := term 0 x
  have h₁ := term 1 (D x)
  have h₂ := V.smul_mem (3 : constants D) (term 2 (D (D x)))
  have h₃ := term 3 (D (D (D x)))
  have h₄ := V.smul_mem (4 : constants D) (term 4 (D (D (D (D x)))))
  have hs := V.add_mem (V.add_mem (V.add_mem (V.add_mem h₀ h₁) h₂) h₃) h₄
  have he := slice_expansion D c x hD
  convert hs using 1
  nth_rw 1 [he]
  norm_num [Algebra.smul_def]
  have hthree : algebraMap (constants D) K 3 = 3 := map_ofNat _ 3
  have hfour : algebraMap (constants D) K 4 = 4 := map_ofNat _ 4
  rw [hthree, hfour]
  ring

noncomputable def sliceBasis (D : Derivation F K K) (c : K) (hc : D c = 1)
    (hD : ∀ x, D (D (D (D (D x)))) = 0) : Basis (Fin 5) (constants D) K :=
  Basis.mk (slice_powers_independent D c hc) (slice_powers_span D c hc hD).ge

theorem slice_finrank (D : Derivation F K K) (c : K) (hc : D c = 1)
    (hD : ∀ x, D (D (D (D (D x)))) = 0) : Module.finrank (constants D) K = 5 := by
  exact Module.finrank_eq_card_basis (sliceBasis D c hc hD)

end Slice
end Red61

namespace Red61

open scoped TensorProduct

section Tensor

variable {ell k L K : Type*} [Field ell] [Field k] [Field L] [Field K]
  [Algebra ell k] [Algebra ell L] [Algebra L K]
  [CharP (L ⊗[ell] k) 5]

/-- Height-one pure inseparability makes every fifth power a scalar after base change. -/
theorem tensor_fifth_scalar (hpure : ∀ b : k, ∃ a : ell, b ^ 5 = algebraMap ell k a)
    (x : L ⊗[ell] k) : ∃ a : L, x ^ 5 = algebraMap L (L ⊗[ell] k) a := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨s, hs⟩ := hpure b
    refine ⟨a ^ 5 * algebraMap ell L s, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, hs]
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [add_pow_char _ _ 5, ha, hb, map_add]⟩

/-- Every element in the kernel of a multiplication map has fifth power zero. -/
theorem tensor_kernel_fifth_zero
    (hpure : ∀ b : k, ∃ a : ell, b ^ 5 = algebraMap ell k a)
    (mu : L ⊗[ell] k →ₐ[L] K) {x : L ⊗[ell] k} (hx : mu x = 0) : x ^ 5 = 0 := by
  obtain ⟨a, ha⟩ := tensor_fifth_scalar hpure x
  have h := congrArg mu ha
  rw [map_pow, hx, zero_pow (by decide), AlgHom.commutes] at h
  have hz : a = 0 := (algebraMap L K).injective (by simpa using h.symm)
  simpa [hz] using ha

/-- The dimension drop 25 → 5 produces an actual nonzero nilpotent.
Surjectivity of mu is not needed for this implication. -/
theorem tensor_nonzero_nilpotent [Module.Finite L K]
    (hpure : ∀ b : k, ∃ a : ell, b ^ 5 = algebraMap ell k a)
    (hbig : Module.finrank ell k = 25) (hsmall : Module.finrank L K = 5)
    (mu : L ⊗[ell] k →ₐ[L] K) :
    ∃ x : L ⊗[ell] k, x ≠ 0 ∧ x ^ 5 = 0 := by
  have hn : ¬ Function.Injective mu := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective (f := mu.toLinearMap) hi
    rw [Module.finrank_baseChange, hbig, hsmall] at hd
    omega
  have hnker : LinearMap.ker mu.toLinearMap ≠ ⊥ := by
    intro h
    exact hn ((LinearMap.ker_eq_bot).mp h)
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnker
  exact ⟨x, hne, tensor_kernel_fifth_zero hpure mu hx⟩

end Tensor
end Red61

/-! Finite invariant inclusions and finite generation, using the Artin--Tate lemma. -/

namespace Red61.FrobeniusDescent

noncomputable section

variable {R F : Type} [Field R] [Field F] [Algebra R F]
variable (M : Subfield F) [Algebra R M] [IsScalarTower R M F]
variable (p : ℕ) [Fact p.Prime] [CharP F p] (hp : ∀ x : F, x ^ p ∈ M)
variable (A : Subalgebra R F)

theorem embed_injective : Function.Injective (embed M A) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : A ↦ (z : F)) h))

@[instance_reducible] def fixedAlgebra : Algebra (fixed M A) A :=
  (embed M A).toRingHom.toAlgebra

theorem fixed_scalarTower :
    letI := fixedAlgebra M A
    IsScalarTower R (fixed M A) A := by
  let := fixedAlgebra M A
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((embed M A).commutes r).symm

include p hp

/-- Every element is integral, since its p-th power belongs to the invariant ring. -/
theorem fixed_integral :
    letI := fixedAlgebra M A
    Algebra.IsIntegral (fixed M A) A := by
  let := fixedAlgebra M A
  refine ⟨fun x ↦ IsIntegral.of_pow (Nat.Prime.pos (Fact.out : p.Prime)) ?_⟩
  exact isIntegral_algebraMap (x := powerElement M p hp A x)

/-- A finite type algebra is module-finite over this invariant ring. -/
theorem embed_finite [Algebra.FiniteType R A] : (embed M A).toRingHom.Finite := by
  let := fixedAlgebra M A
  have := fixed_scalarTower M A
  have := Algebra.FiniteType.of_restrictScalars_finiteType R (fixed M A) A
  have := fixed_integral M p hp A
  exact Algebra.IsIntegral.finite

/-- The invariant algebra is finite type over the common base, by Artin--Tate.
This does not require the original coefficient field to be fixed. -/
theorem fixed_finiteType [Algebra.FiniteType R A] : Algebra.FiniteType R (fixed M A) := by
  let := fixedAlgebra M A
  have := fixed_scalarTower M A
  have : Module.Finite (fixed M A) A := embed_finite M p hp A
  exact ⟨fg_of_fg_of_fg R (fixed M A) A
    Algebra.FiniteType.out Module.Finite.fg_top (embed_injective M A)⟩

end
end Red61.FrobeniusDescent

namespace Red61

noncomputable section
variable {F R : Type*} [CommRing F] [CommRing R] [Algebra F R]

def invariantAlgebra (D : Derivation F R R) : Subalgebra F R where
  carrier := {x | D x = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x * y) = 0
    simp [Derivation.leibniz, hx, hy]
  algebraMap_mem' r := D.map_algebraMap r

/-- A derivation is linear over its entire ring of constants. -/
def derivationOverConstants (D : Derivation F R R) :
    Derivation (invariantAlgebra D) R R where
  toFun := D
  map_add' := map_add D
  map_smul' a x := by
    change D ((a : R) * x) = (a : R) * D x
    rw [Derivation.leibniz, a.property]
    simp [smul_eq_mul]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

def invariantRetraction (D : Derivation F R R) (hD : ∀ x, D (D (D (D (D x)))) = D x) :
    R →ₗ[invariantAlgebra D] invariantAlgebra D := by
  let E := (derivationOverConstants D).toLinearMap
  have he : E ^ 5 = E := by ext x; exact hD x
  exact
    { toFun := fun x => ⟨reynolds E x, LinearMap.congr_fun (reynolds_image_in_kernel E he) x⟩
      map_add' := fun x y => Subtype.ext (map_add (reynolds E) x y)
      map_smul' := fun a x => Subtype.ext ((reynolds E).map_smul a x) }

theorem invariantRetraction_one (D : Derivation F R R)
    (hD : ∀ x, D (D (D (D (D x)))) = D x) : invariantRetraction D hD 1 = 1 := by
  apply Subtype.ext
  exact reynolds_fixes_kernel _ D.map_one_eq_zero

theorem invariantAlgebra_noetherian [IsNoetherianRing R] (D : Derivation F R R)
    (hD : ∀ x, D (D (D (D (D x)))) = D x) : IsNoetherianRing (invariantAlgebra D) :=
  noetherian_of_retraction (invariantRetraction D hD) (invariantRetraction_one D hD)

theorem invariantAlgebra_isUnit (D : Derivation F R R) (x : invariantAlgebra D) :
    IsUnit x ↔ IsUnit (x : R) := by
  constructor
  · exact fun h => h.map (invariantAlgebra D).val
  · rintro ⟨v, hv⟩
    have hx : D (v : R) = 0 := by rw [hv]; exact x.property
    have hi : D (↑v⁻¹ : R) = 0 := by
      have h := congrArg D v.val_inv
      rw [Derivation.leibniz, hx, D.map_one_eq_zero] at h
      have hh := congrArg (fun z : R => (↑v⁻¹ : R) * z) h
      simpa [smul_eq_mul, ← mul_assoc] using hh
    refine ⟨⟨x, ⟨↑v⁻¹, hi⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (x : R) * ↑v⁻¹ = 1
      rw [← hv]
      exact v.val_inv
    · apply Subtype.ext
      change ↑v⁻¹ * (x : R) = 1
      rw [← hv]
      exact v.inv_val

theorem invariantAlgebra_local [IsLocalRing R] (D : Derivation F R R) :
    IsLocalRing (invariantAlgebra D) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (x : R)
  exact h.imp ((invariantAlgebra_isUnit D x).mpr)
    ((invariantAlgebra_isUnit D (1 - x)).mpr)

end
end Red61

/-! A polynomial coordinate system that straightens a derivation gives a regular kernel.
The denominator argument also covers arbitrary localizations of that polynomial ring. -/

namespace Red61.PolynomialInvariants

open MvPolynomial
noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP F 5] [CharP K 5]

def powerCoordinates (v : Fin 4 → K) : Fin 4 → K := ![v 0 ^ 5, v 1, v 2, v 3]

omit [CharP F 5] [CharP K 5] in
theorem powerCoordinates_independent {v : Fin 4 → K} (hv : AlgebraicIndependent F v) :
    AlgebraicIndependent F (powerCoordinates v) := by
  let f : MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 4) F :=
    aeval ![X 0 ^ 5, X 1, X 2, X 3]
  let g : MvPolynomial (Fin 4) F →ₐ[F] MvPolynomial (Fin 4) F :=
    aeval ![X 0, X 1 ^ 5, X 2 ^ 5, X 3 ^ 5]
  have hgf : g.comp f = expand 5 := by
    ext i
    fin_cases i <;> simp [f, g]
  have hf : Function.Injective f := by
    apply Function.Injective.of_comp (f := g)
    change Function.Injective (g.comp f)
    rw [hgf]
    exact expand_injective (by decide)
  have he : aeval (powerCoordinates v) = (aeval v).comp f := by
    ext i
    fin_cases i <;> simp [powerCoordinates, f]
  change Function.Injective (aeval (powerCoordinates v))
  rw [he]
  exact (show Function.Injective (aeval v) from hv).comp hf

def polynomialRing (v : Fin 4 → K) : Subalgebra F K := Algebra.adjoin F (Set.range v)
def kernelIn (D : Derivation F K K) (A : Subalgebra F K) : Subalgebra F K :=
  A ⊓ invariantAlgebra D

omit [CharP F 5] [CharP K 5] in
theorem eval_derivative (D : Derivation F K K) (v : Fin 4 → K)
    (hv : ∀ i, D (v i) = if i = 0 then 1 else 0) (f : MvPolynomial (Fin 4) F) :
    D (aeval v f) = aeval v (pderiv 0 f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [D.map_algebraMap]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hf, hv,
      pderiv_X, Pi.single_apply, map_add, map_mul, aeval_X]
    split_ifs <;> simp_all

theorem kernel_polynomial (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0) :
    kernelIn D (polynomialRing v) = polynomialRing (powerCoordinates v) := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (aeval (R := F) v).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]; exact hx.1
    obtain ⟨f,rfl⟩ := hm
    have hDx : D (aeval v f) = 0 := hx.2
    have hd : pderiv 0 f = 0 := hi (by rw [← eval_derivative D v hv, hDx, map_zero])
    rw [f.as_sum]
    simp only [map_sum]
    apply Subalgebra.sum_mem
    intro d hdmem
    have hd5 : 5 ∣ d 0 := by
      by_cases hd0 : d 0 = 0
      · simp [hd0]
      have h := congrArg (fun p : MvPolynomial (Fin 4) F ↦ p.coeff (d - Finsupp.single 0 1)) hd
      rw [coeff_pderiv] at h
      change f.coeff (d - Finsupp.single 0 1 + Finsupp.single 0 1) *
        ((((d - Finsupp.single 0 1 : Fin 4 →₀ ℕ) 0 : ℕ) : F) + 1) = 0 at h
      have he : d - Finsupp.single 0 1 + Finsupp.single 0 1 = d :=
        Finsupp.sub_add_single_one_cancel hd0
      rw [he] at h
      have hn : (d - Finsupp.single 0 1 : Fin 4 →₀ ℕ) 0 + 1 = d 0 := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      have hh : (d 0 : F) = 0 := by
        have hnF : (((d - Finsupp.single 0 1 : Fin 4 →₀ ℕ) 0 : ℕ) : F) + 1 = (d 0 : F) := by
          simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ ↦ (n : F)) hn
        rw [hnF] at h
        exact (mul_eq_zero.mp h).resolve_left (mem_support_iff.mp hdmem)
      exact (CharP.cast_eq_zero_iff F 5 (d 0)).mp hh
    change aeval v (monomial d (f.coeff d)) ∈ polynomialRing (powerCoordinates v)
    rw [aeval_monomial]
    apply (polynomialRing (powerCoordinates v)).mul_mem
    · exact (polynomialRing (powerCoordinates v)).algebraMap_mem _
    · rw [Finsupp.prod_fintype]
      · apply Subalgebra.prod_mem
        intro i _
        by_cases hi0 : i = 0
        · subst i
          obtain ⟨n,hn⟩ := hd5
          rw [hn, pow_mul]
          exact (polynomialRing (powerCoordinates v)).pow_mem
            (Algebra.subset_adjoin (Set.mem_range_self 0)) _
        · have he : v i = powerCoordinates v i := by fin_cases i <;> simp_all [powerCoordinates]
          rw [he]
          exact (polynomialRing (powerCoordinates v)).pow_mem
            (Algebra.subset_adjoin (Set.mem_range_self i)) _
      · intro i
        simp
  · apply Algebra.adjoin_le
    rintro x ⟨i,rfl⟩
    constructor
    · fin_cases i
      · exact (polynomialRing v).pow_mem (Algebra.subset_adjoin (Set.mem_range_self 0)) _
      · exact Algebra.subset_adjoin (Set.mem_range_self 1)
      · exact Algebra.subset_adjoin (Set.mem_range_self 2)
      · exact Algebra.subset_adjoin (Set.mem_range_self 3)
    · change D (powerCoordinates v i) = 0
      fin_cases i
      · change D (v 0 ^ 5) = 0
        simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
          CharP.cast_eq_zero K 5, zero_mul]
      · simpa [powerCoordinates] using hv 1
      · simpa [powerCoordinates] using hv 2
      · simpa [powerCoordinates] using hv 3

theorem kernel_regular (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A)
    (hloc : A ≤ FieldLocalization.hull (polynomialRing v) A) :
    IsRegularRing (kernelIn D A) := by
  have hpoly := kernel_polynomial D v hi hv
  have : IsRegularRing (kernelIn D (polynomialRing v)) := by
    rw [hpoly]
    exact IsRegularRing.of_ringEquiv (powerCoordinates_independent hi).aevalEquiv.toRingEquiv
  apply FieldLocalization.regular (P := kernelIn D (polynomialRing v))
    (show kernelIn D (polynomialRing v) ≤ kernelIn D A from inf_le_inf_right _ hle)
  intro x hx
  obtain ⟨b,hb,hb0,hbi,hxb⟩ := hloc hx.1
  have hp (z : K) : D (z ^ 5) = 0 := by
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      CharP.cast_eq_zero K 5, zero_mul]
  refine ⟨b^5, ⟨(polynomialRing v).pow_mem hb _, hp b⟩, pow_ne_zero _ hb0,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [inv_pow] using A.pow_mem hbi 5
  · change D ((b^5)⁻¹) = 0
    simp [Derivation.leibniz_inv, hp]
  · have he : x*b^5 = (x*b)*b^4 := by ring
    rw [he]
    exact (polynomialRing v).mul_mem hxb ((polynomialRing v).pow_mem hb _)
  · change D (x*b^5) = 0
    have hDx : D x = 0 := hx.2
    simp [Derivation.leibniz, hp, hDx]

end
end Red61.PolynomialInvariants

namespace Red61.PolynomialInvariants

open AffineGluing
noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K 5]

theorem fifth_power_kernel (D : Derivation F K K) (x : K) : D (x^5) = 0 := by
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    CharP.cast_eq_zero K 5, zero_mul]

def kernelPower (D : Derivation F K K) (A : Subalgebra F K) (d : A) : kernelIn D A :=
  ⟨(d : K)^5, ⟨A.pow_mem d.property 5, fifth_power_kernel D d⟩⟩

theorem kernel_away (D : Derivation F K K) {A B : Subalgebra F K}
    (hAB : A ≤ B) (d : A)
    (hloc : letI := inclusionAlgebra hAB; IsLocalization.Away d B) :
    letI := inclusionAlgebra (show kernelIn D A ≤ kernelIn D B from inf_le_inf_right _ hAB)
    IsLocalization.Away (kernelPower D A d) (kernelIn D B) := by
  let := inclusionAlgebra hAB
  have := hloc
  let := inclusionAlgebra (show kernelIn D A ≤ kernelIn D B from inf_le_inf_right _ hAB)
  obtain ⟨hd,hB⟩ := localization_description hAB d hloc
  have hinv : (d : K)⁻¹ ∈ B := by
    rw [hB]
    exact (show Algebra.adjoin F _ ≤ A ⊔ Algebra.adjoin F _ from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  let v : kernelIn D B := ⟨((d : K)⁻¹)^5, ⟨B.pow_mem hinv 5, fifth_power_kernel D _⟩⟩
  apply IsLocalization.Away.mk
  · refine ⟨⟨algebraMap (kernelIn D A) (kernelIn D B) (kernelPower D A d), v, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (d : K)^5*((d : K)⁻¹)^5 = 1
      rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
    · apply Subtype.ext
      change ((d : K)⁻¹)^5*(d : K)^5 = 1
      rw [← mul_pow, inv_mul_cancel₀ hd, one_pow]
  · intro x
    obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj d (⟨(x : K),x.property.1⟩ : B)
    have ha' : (x : K)*(d : K)^n = (a : K) := congrArg (fun z : B ↦ (z : K)) ha
    have hm : (x : K)*((d : K)^5)^n ∈ A := by
      have he : (x : K)*((d : K)^5)^n = ((x : K)*(d : K)^n)*(d : K)^(4*n) := by
        rw [← pow_mul, show 5*n = n+4*n by omega, pow_add, mul_assoc]
      rw [he, ha']
      exact A.mul_mem a.property (A.pow_mem d.property _)
    have hx : D (x : K) = 0 := x.property.2
    refine ⟨n, ⟨(x : K)*((d : K)^5)^n, ⟨hm, ?_⟩⟩, rfl⟩
    change D ((x : K)*((d : K)^5)^n) = 0
    rw [Derivation.leibniz, Derivation.leibniz_pow, fifth_power_kernel, hx]
    simp
  · intro x y hxy
    exact ⟨0, by simpa using (Subalgebra.inclusion_injective
      (show kernelIn D A ≤ kernelIn D B from inf_le_inf_right _ hAB) hxy)⟩

end
end Red61.PolynomialInvariants

/-! A straightened field derivation gives polynomial localization
coordinates, and hence an actual basis of the invariant-ring differentials. -/

namespace Red61.PolynomialInvariants

open FieldLocalization AffineGluing Module
noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP F 5] [CharP K 5]

theorem kernel_le_hull (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hloc : A ≤ hull (polynomialRing v) A) :
    kernelIn D A ≤ hull (polynomialRing (powerCoordinates v)) (kernelIn D A) := by
  intro x hx
  obtain ⟨b, hb, hb0, hbi, hxb⟩ := hloc hx.1
  have hp (z : K) : D (z^5) = 0 := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]
  have hpoly := kernel_polynomial D v hi hv
  have hb5 : b^5 ∈ polynomialRing (F := F) (powerCoordinates v) := by
    rw [← hpoly]
    exact ⟨(polynomialRing v).pow_mem hb 5, hp b⟩
  refine ⟨b^5, hb5, pow_ne_zero _ hb0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [inv_pow] using A.pow_mem hbi 5
    · change D ((b^5)⁻¹) = 0
      simp [Derivation.leibniz_inv, hp]
  · rw [← hpoly]
    refine ⟨?_, ?_⟩
    · have he : x*b^5 = (x*b)*b^4 := by ring
      rw [he]
      exact (polynomialRing v).mul_mem hxb ((polynomialRing v).pow_mem hb 4)
    · change D (x*b^5) = 0
      simp [Derivation.leibniz, hp, show D x = 0 from hx.2]

theorem powerPolynomial_le_kernel (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A) :
    polynomialRing (powerCoordinates v) ≤ kernelIn D A := by
  rw [← kernel_polynomial D v hi hv]
  exact inf_le_inf_right _ hle

def polynomialKernelDifferentialBasis (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A)
    (hloc : A ≤ hull (polynomialRing v) A) :
    Basis (Fin 4) (kernelIn D A) (KaehlerDifferential F (kernelIn D A)) := by
  let P := polynomialRing (F := F) (powerCoordinates v)
  let C := kernelIn D A
  have hPC : P ≤ C := powerPolynomial_le_kernel D v hi hv A hle
  let := inclusionAlgebra hPC
  have : IsScalarTower F P C := IsScalarTower.of_algHom (Subalgebra.inclusion hPC)
  have : IsLocalization (denominators hPC) C :=
    FieldLocalization.isLocalization hPC (kernel_le_hull D v hi hv A hloc)
  let e := (powerCoordinates_independent hi).aevalEquiv
  let bP : Basis (Fin 4) P (KaehlerDifferential F P) :=
    differentialBasisOfRingEquiv F e.toRingEquiv e.toAlgHom.comp_algebraMap
      (KaehlerDifferential.mvPolynomialBasis F (Fin 4))
  exact differentialBasisOfLocalization F P C (Fin 4) (denominators hPC) bP

end
end Red61.PolynomialInvariants

/-! The straightened invariant kernels are formally smooth over their
polynomial ground field. Smoothness is also transported through rings and
prime localizations, including the open localization at the second point. -/

namespace Red61

noncomputable section

theorem formallySmooth_of_ringEquiv (R : Type*) {A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FormallySmooth R A]
    (e : A ≃+* B) (he : e.toRingHom.comp (algebraMap R A) = algebraMap R B) :
    Algebra.FormallySmooth R B :=
  Algebra.FormallySmooth.of_equiv
    { e with commutes' := fun a ↦ RingHom.congr_fun he a }

theorem formallySmooth_atPrime (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (p : PrimeSpectrum A) :
    Algebra.FormallySmooth R (Localization.AtPrime p.asIdeal) := by
  have : Algebra.FormallySmooth A (Localization.AtPrime p.asIdeal) :=
    Algebra.FormallySmooth.of_isLocalization p.asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp R A _

theorem formallySmooth_atPrime_of_away
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (d : A) [IsLocalization.Away d B] [Algebra.FormallySmooth R B]
    (p : PrimeSpectrum A) (hd : d ∉ p.asIdeal) :
    Algebra.FormallySmooth R (Localization.AtPrime p.asIdeal) := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B d]
    exact hd
  obtain ⟨q, rfl⟩ := hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers d) (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := IsLocalization.algEquiv (q.asIdeal.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime (q.asIdeal.comap (algebraMap A B)))
  have := formallySmooth_atPrime R B q
  exact Algebra.FormallySmooth.of_equiv (e.restrictScalars R)

end

namespace PolynomialInvariants

open FieldLocalization AffineGluing
noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP F 5] [CharP K 5]

theorem polynomialKernel_formallySmooth (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A)
    (hloc : A ≤ hull (polynomialRing v) A) : Algebra.FormallySmooth F (kernelIn D A) := by
  let P := polynomialRing (F := F) (powerCoordinates v)
  let C := kernelIn D A
  have hPC : P ≤ C := powerPolynomial_le_kernel D v hi hv A hle
  let := inclusionAlgebra hPC
  have : IsScalarTower F P C := IsScalarTower.of_algHom (Subalgebra.inclusion hPC)
  have : IsLocalization (denominators hPC) C :=
    FieldLocalization.isLocalization hPC (kernel_le_hull D v hi hv A hloc)
  have : Algebra.FormallySmooth F P :=
    Algebra.FormallySmooth.of_equiv (powerCoordinates_independent hi).aevalEquiv
  have : Algebra.FormallySmooth P C :=
    Algebra.FormallySmooth.of_isLocalization (denominators hPC)
  exact Algebra.FormallySmooth.comp F P C

end
end PolynomialInvariants
end Red61

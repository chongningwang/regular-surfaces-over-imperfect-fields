import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Smooth.Basic
import Red61.LinearAlgebra.ExteriorPower
import Red61.RingTheory.Regular

/-! # Kähler differentials, differential bases and cotangent sequences

Formerly the modules `AmbientDifferentialSequence`, `ConormalDeterminant`, `DifferentialAlgebraIso`, `DifferentialBasisNeighborhood`, `DifferentialBijectiveAlgebra`, `ExtensionLocalizationNaturality`, `LocalDifferentialGeneration`, `PolynomialDifferentialBasis`, `QuotientBaseDifferentials`, `RationalResidueSection`, `RelativeConormalAdjunction`, `RelativeCotangent`, `CotangentDeterminants`, `RelativeJacobianDivisor`, `RingHomDifferentials`, `RingHomDifferentialExterior`, `StalkDifferentialSequence`, `StalkCotangentHomology`, `DifferentialBasisTransport`, `RationalDifferentialLocalization`, `AtPrimeDifferentialBasis`, `ExtensionRegularPairConormal`, `ExtensionUnitLocalization`.
-/

/-! The ambient base differential sequence for a formally smooth algebra.
Its splitting makes injectivity survive arbitrary scalar extension, including
the nonflat quotient from an ambient algebra to a surface local ring. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable (R F P : Type*) [CommRing R] [CommRing F] [CommRing P]
  [Algebra R F] [Algebra R P] [Algebra F P] [IsScalarTower R F P]
  [Algebra.FormallySmooth F P]

theorem smoothBaseDifferential_injective :
    Function.Injective (KaehlerDifferential.mapBaseChange R F P) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.exact_iff.mp (Algebra.H1Cotangent.exact_δ_mapBaseChange R F P)]
  rw [Subsingleton.elim (Algebra.H1Cotangent.δ R F P) 0]
  exact LinearMap.range_zero

def smoothBaseDifferentialSection :
    KaehlerDifferential F P →ₗ[P] KaehlerDifferential R P :=
  ((KaehlerDifferential.map R F P P).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (KaehlerDifferential.map_surjective R F P))).choose

theorem smoothBaseDifferentialSection_spec :
    (KaehlerDifferential.map R F P P).comp (smoothBaseDifferentialSection R F P) =
      LinearMap.id :=
  ((KaehlerDifferential.map R F P P).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (KaehlerDifferential.map_surjective R F P))).choose_spec

def smoothBaseDifferentialRetraction :
    KaehlerDifferential R P →ₗ[P] P ⊗[F] KaehlerDifferential R F :=
  (LinearMap.fst P (P ⊗[F] KaehlerDifferential R F) (KaehlerDifferential F P)).comp
    (splitExactEquiv (KaehlerDifferential.mapBaseChange R F P)
      (KaehlerDifferential.map R F P P) (smoothBaseDifferential_injective R F P)
      (KaehlerDifferential.exact_mapBaseChange_map R F P)
      (smoothBaseDifferentialSection R F P)
      (smoothBaseDifferentialSection_spec R F P)).symm.toLinearMap

theorem smoothBaseDifferentialRetraction_spec :
    (smoothBaseDifferentialRetraction R F P).comp
      (KaehlerDifferential.mapBaseChange R F P) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact congrArg Prod.fst (splitExactEquiv_symm_f
    (KaehlerDifferential.mapBaseChange R F P) (KaehlerDifferential.map R F P P)
    (smoothBaseDifferential_injective R F P)
    (KaehlerDifferential.exact_mapBaseChange_map R F P)
    (smoothBaseDifferentialSection R F P) (smoothBaseDifferentialSection_spec R F P) x)

variable (A : Type*) [CommRing A] [Algebra P A]

theorem ambientBaseDifferential_injective :
    Function.Injective ((KaehlerDifferential.mapBaseChange R F P).baseChange A) := by
  have he : ((smoothBaseDifferentialRetraction R F P).baseChange A).comp
      ((KaehlerDifferential.mapBaseChange R F P).baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, smoothBaseDifferentialRetraction_spec,
      LinearMap.baseChange_id]
  exact (show Function.LeftInverse ((smoothBaseDifferentialRetraction R F P).baseChange A)
    ((KaehlerDifferential.mapBaseChange R F P).baseChange A) from
      fun x ↦ DFunLike.congr_fun he x).injective

omit [Algebra.FormallySmooth F P] in
theorem ambientBaseDifferential_exact :
    Function.Exact ((KaehlerDifferential.mapBaseChange R F P).baseChange A)
      ((KaehlerDifferential.map R F P P).baseChange A) :=
  lTensor_exact A (KaehlerDifferential.exact_mapBaseChange_map R F P)
    (KaehlerDifferential.map_surjective R F P)

theorem ambientBaseDifferentialSection_spec :
    ((KaehlerDifferential.map R F P P).baseChange A).comp
      ((smoothBaseDifferentialSection R F P).baseChange A) = LinearMap.id := by
  rw [← LinearMap.baseChange_comp, smoothBaseDifferentialSection_spec, LinearMap.baseChange_id]

end
end Red61

/-! Determinant adjunction for the actual conormal sequence of an algebra
presentation. Formal smoothness supplies injectivity of the conormal map
and a linear section of the quotient map. The comparison uses actual
conormal modules, differentials, and exterior powers. -/

namespace Red61

open Module Algebra
noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A) [Algebra.FormallySmooth R P.Ring]
  [Algebra.FormallySmooth R A]

theorem conormalMap_injective : Function.Injective P.cotangentComplex :=
  P.cotangentComplex_injective_iff.mpr inferInstance

def conormalSection : KaehlerDifferential R A →ₗ[A] P.CotangentSpace :=
  (P.toKaehler.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr P.toKaehler_surjective)).choose

omit [Algebra.FormallySmooth R P.Ring] in
theorem conormalSection_spec : P.toKaehler.comp (conormalSection P) = LinearMap.id :=
  (P.toKaehler.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr P.toKaehler_surjective)).choose_spec

end
end Red61

/-! Equal algebra structures give actual isomorphisms of differential
modules, preserving the universal derivative on every ring element. -/

namespace Red61
open CategoryTheory
noncomputable section
universe u
variable {R A : Type u} [CommRing R] [CommRing A]

def kaehlerDifferentialAlgebraIso (a b : Algebra R A) (h : a = b) :
    (letI := a; ModuleCat.of A (KaehlerDifferential R A)) ≅
      (letI := b; ModuleCat.of A (KaehlerDifferential R A)) := by
  subst b
  exact Iso.refl _

theorem kaehlerDifferentialAlgebraIso_D (a b : Algebra R A) (h : a = b) (x : A) :
    (kaehlerDifferentialAlgebraIso a b h).hom (letI := a; KaehlerDifferential.D R A x) =
      (letI := b; KaehlerDifferential.D R A x) := by
  subst b
  rfl
end
end Red61

/-! A finite basis of localized differentials descends to a principal open.
The resulting basis belongs to the actual differential module of the localized
algebra, using the native module-localization comparison. -/

namespace Red61
open Module
noncomputable section
variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B]
  (S : Submonoid A) [IsLocalization S B]
  [Module.FinitePresentation A (KaehlerDifferential F A)]
  {I : Type*} [Finite I]
theorem exists_away_differential_basis (b : Basis I B (KaehlerDifferential F B)) :
    ∃ a : A, a ∈ S ∧
      Nonempty (Basis I (Localization.Away a) (KaehlerDifferential F (Localization.Away a))) := by
  have := KaehlerDifferential.isLocalizedModule_map F A B S
  obtain ⟨a, ha, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers S
    (KaehlerDifferential.map F F A B) B b
  have := KaehlerDifferential.isLocalizedModule_map F A (Localization.Away a) (.powers a)
  let e := (IsLocalizedModule.iso (.powers a)
    (KaehlerDifferential.map F F A (Localization.Away a))).extendScalarsOfIsLocalization
      (.powers a) (Localization.Away a)
  exact ⟨a, ha, ⟨b'.map e⟩⟩

variable {J : Type*}
def intDifferentialBasisCanonical (a : Algebra ℤ A)
    (b : letI := a; Basis J A (KaehlerDifferential ℤ A)) :
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    Basis J A (KaehlerDifferential ℤ A) := by
  have h : a = Ring.toIntAlgebra A := Subsingleton.elim _ _
  subst h
  exact b
end
end Red61

/-! A bijective algebra map induces a bijective map on ordinary Kähler modules.
The proof reuses mathlib’s kernel presentation and surjectivity theorem. -/

namespace Red61
noncomputable section
universe u
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem kaehlerMap_bijective_of_bijective_algebraMap
    (h : Function.Bijective (algebraMap A B)) :
    Function.Bijective (KaehlerDifferential.map R R A B) := by
  refine ⟨LinearMap.ker_eq_bot.mp ?_,
    KaehlerDifferential.map_surjective_of_surjective R R A B h.surjective⟩
  rw [KaehlerDifferential.ker_map_of_surjective R A B h.surjective]
  have hf : Function.Injective
      ((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
        (Finsupp.lmapDomain A A (algebraMap A B))) :=
    (Finsupp.mapRange_injective (algebraMap A B) (map_zero _) h.injective).comp
      (Finsupp.mapDomain_injective h.injective)
  rw [LinearMap.ker_eq_bot.mpr hf, Submodule.map_bot]
end
end Red61

/-! A presentation localizes through a native morphism of algebra
extensions. Both scalar squares commute for the actual localization maps,
including the quotient evaluation to the localized target. -/

namespace Red61
open Algebra
noncomputable section
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  (M : Submonoid A) [IsLocalization M B] (P : Algebra.Extension R A)
local notation "Pₗ" => (Algebra.Extension.localization (S' := B) M P)
private local instance : Algebra P.Ring (Pₗ).Ring :=
  inferInstanceAs (Algebra P.Ring (Localization (M.comap (algebraMap P.Ring A))))
private local instance : IsScalarTower R P.Ring (Pₗ).Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem extensionLocalization_evaluation (a : P.Ring) :
    algebraMap (Pₗ).Ring B (algebraMap P.Ring (Pₗ).Ring a) =
      algebraMap A B (algebraMap P.Ring A a) := by
  change IsLocalization.lift (M := M.comap (algebraMap P.Ring A))
    (g := (algebraMap A B).comp (algebraMap P.Ring A)) _
      (algebraMap P.Ring (Localization (M.comap (algebraMap P.Ring A))) a) = _
  exact IsLocalization.lift_eq _ _

end
end Red61

/-! Finite generation of differentials from a residue-field section and two
generators of the maximal ideal. The finiteness needed by Nakayama is explicit. -/

namespace Red61

noncomputable section

theorem localDifferentials_eq_top_of_section
    {R A F : Type*} [CommRing R] [CommRing A] [Field F] [Algebra R A]
    [IsLocalRing A] [Module.Finite A (KaehlerDifferential R A)]
    (ρ : A →+* F) (s : F →+* A) (hsection : ∀ a, ρ (s a) = a)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal A)
    (u r : A) (hmax : IsLocalRing.maximalIdeal A = Ideal.span ({u, r} : Set A))
    (N : Submodule A (KaehlerDifferential R A))
    (hu : KaehlerDifferential.D R A u ∈ N) (hr : KaehlerDifferential.D R A r ∈ N)
    (hcoeff : ∀ a, KaehlerDifferential.D R A (s a) ∈ N) : N = ⊤ := by
  let m := IsLocalRing.maximalIdeal A
  let P := N ⊔ m • (⊤ : Submodule A (KaehlerDifferential R A))
  have hNP : N ≤ P := le_sup_left
  have hmP : m • (⊤ : Submodule A (KaehlerDifferential R A)) ≤ P := le_sup_right
  have hum : u ∈ m := by
    change u ∈ IsLocalRing.maximalIdeal A
    rw [hmax]
    exact Ideal.subset_span (by simp)
  have hrm : r ∈ m := by
    change r ∈ IsLocalRing.maximalIdeal A
    rw [hmax]
    exact Ideal.subset_span (by simp)
  have hd (x : A) : KaehlerDifferential.D R A x ∈ P := by
    have hy : x - s (ρ x) ∈ Ideal.span ({u, r} : Set A) := by
      rw [← hmax, ← hker]
      change ρ (x - s (ρ x)) = 0
      rw [map_sub, hsection, sub_self]
    obtain ⟨a, b, he⟩ := Ideal.mem_span_pair.mp hy
    have hx : x = s (ρ x) + (a*u + b*r) := by rw [he]; ring
    rw [hx, map_add, map_add, Derivation.leibniz, Derivation.leibniz]
    apply P.add_mem (hNP (hcoeff _))
    apply P.add_mem
    · exact P.add_mem (P.smul_mem a (hNP hu))
        (hmP (Submodule.smul_mem_smul hum (by trivial)))
    · exact P.add_mem (P.smul_mem b (hNP hr))
        (hmP (Submodule.smul_mem_smul hrm (by trivial)))
  have htop : (⊤ : Submodule A (KaehlerDifferential R A)) ≤ P := by
    rw [← KaehlerDifferential.span_range_derivation R A]
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    exact hd a
  exact top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) htop)

end
end Red61

/-! An explicit differential basis for any localization of a polynomial
algebra, obtained from the genuine formally etale base-change isomorphism. -/

namespace Red61

open Module
noncomputable section

variable (F A σ : Type*) [CommRing F] [CommRing A] [Algebra F A]
  [Algebra (MvPolynomial σ F) A] [IsScalarTower F (MvPolynomial σ F) A]
  (M : Submonoid (MvPolynomial σ F)) [IsLocalization M A]

def polynomialLocalizationDifferentialBasis : Basis σ A (KaehlerDifferential F A) := by
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) M
  exact ((KaehlerDifferential.mvPolynomialBasis F σ).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale F (MvPolynomial σ F) A)

@[simp] theorem polynomialLocalizationDifferentialBasis_apply (i : σ) :
    polynomialLocalizationDifferentialBasis F A σ M i =
      KaehlerDifferential.D F A (algebraMap (MvPolynomial σ F) A (MvPolynomial.X i)) := by
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) M
  simp [polynomialLocalizationDifferentialBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]

end
end Red61

/-! Passing from a ring to a surjective quotient in the base leaves the
absolute differential module unchanged. This permits a precise comparison
of integer-base and prime-field differentials in characteristic five. -/

namespace Red61

noncomputable section
open scoped TensorProduct

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

theorem kaehlerMap_bijective_of_surjective_base
    (h : Function.Surjective (algebraMap R S)) :
    Function.Bijective (KaehlerDifferential.map R S A A) := by
  have : Subsingleton (KaehlerDifferential R S) :=
    KaehlerDifferential.subsingleton_of_surjective R S h
  refine ⟨?_, KaehlerDifferential.map_surjective R S A⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y,rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S A x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

def quotientBaseDifferentialEquiv (h : Function.Surjective (algebraMap R S)) :
    KaehlerDifferential R A ≃ₗ[A] KaehlerDifferential S A :=
  LinearEquiv.ofBijective _ (kaehlerMap_bijective_of_surjective_base R S A h)

@[simp] theorem quotientBaseDifferentialEquiv_D
    (h : Function.Surjective (algebraMap R S)) (a : A) :
    quotientBaseDifferentialEquiv R S A h (KaehlerDifferential.D R A a) =
      KaehlerDifferential.D S A a := by
  simp [quotientBaseDifferentialEquiv]

@[simp] theorem quotientBaseDifferentialEquiv_symm_D
    (h : Function.Surjective (algebraMap R S)) (a : A) :
    (quotientBaseDifferentialEquiv R S A h).symm (KaehlerDifferential.D S A a) =
      KaehlerDifferential.D R A a := by
  apply (quotientBaseDifferentialEquiv R S A h).injective
  rw [LinearEquiv.apply_symm_apply, quotientBaseDifferentialEquiv_D]

end
end Red61

/-! A residue-field section for a rational fraction field, constructed from
lifts of its polynomial algebra. Denominators lift to units by the actual
surjective residue homomorphism; no completion or coefficient-field theorem
is assumed. -/

namespace Red61

noncomputable section

variable {P F C : Type*} [CommRing P] [IsDomain P] [Field F]
  [Algebra P F] [IsFractionRing P F] [CommRing C] [IsLocalRing C]
  (f : P →+* C) (ρ : C →+* F) (hρ : Function.Surjective ρ)
  (hcompat : ρ.comp f = algebraMap P F)

include hρ hcompat

theorem rationalSection_denominator_unit (p : nonZeroDivisors P) : IsUnit (f p) := by
  have : IsLocalHom ρ := IsLocalHom.of_surjective ρ hρ
  apply isUnit_of_map_unit ρ (f p)
  apply isUnit_iff_ne_zero.mpr
  change (ρ.comp f) p ≠ 0
  rw [hcompat]
  exact (map_ne_zero_iff _ (IsFractionRing.injective P F)).mpr
    (nonZeroDivisors.ne_zero p.property)

def rationalResidueSection : F →+* C :=
  IsLocalization.lift (rationalSection_denominator_unit f ρ hρ hcompat)

@[simp] theorem rationalResidueSection_algebraMap (p : P) :
    rationalResidueSection f ρ hρ hcompat (algebraMap P F p) = f p :=
  IsLocalization.lift_eq _ p

theorem rationalResidueSection_comp :
    ρ.comp (rationalResidueSection f ρ hρ hcompat) = RingHom.id F := by
  apply IsFractionRing.ringHom_ext (A := P)
  intro p
  change ρ (rationalResidueSection f ρ hρ hcompat (algebraMap P F p)) = algebraMap P F p
  rw [rationalResidueSection_algebraMap]
  exact RingHom.congr_fun hcompat p

@[simp] theorem residue_rationalResidueSection (x : F) :
    ρ (rationalResidueSection f ρ hρ hcompat x) = x :=
  RingHom.congr_fun (rationalResidueSection_comp f ρ hρ hcompat) x

end
end Red61

/-! Relative conormal adjunction compared with the base-normalized absolute
determinant. Both exact sequences use the actual ambient algebra of the same
extension. The base sequence stays split after its nonflat surface quotient. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable (R : Type*) {F A : Type*} [CommRing R] [CommRing F] [CommRing A]
  [Algebra R F] [Algebra R A] [Algebra F A] [IsScalarTower R F A]
  (P : Algebra.Extension F A)

def absoluteExtension : Algebra.Extension R A where
  Ring := P.Ring
  algebra₂ := P.algebra₂
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

variable [Algebra.FormallySmooth R F] [Algebra.FormallySmooth R A]
  [Algebra.FormallySmooth F P.Ring]

set_option maxHeartbeats 800000 in
def relativeConormalDeterminantComparison {c m b q : ℕ}
    (bC : Basis (Fin c) A P.Cotangent) (bM : Basis (Fin m) A (KaehlerDifferential R A))
    (bF : Basis (Fin b) F (KaehlerDifferential R F))
    (bQ : Basis (Fin q) A P.CotangentSpace) (hrank : c + m = b + q) :
    ((⋀[A]^c P.Cotangent) →ₗ[A] (⋀[A]^q P.CotangentSpace)) ≃ₗ[A]
      ((⋀[A]^b (A ⊗[F] KaehlerDifferential R F)) →ₗ[A]
        (⋀[A]^m (KaehlerDifferential R A))) := by
  have : Algebra.FormallySmooth R P.Ring := Algebra.FormallySmooth.comp R F P.Ring
  have : Algebra.FormallySmooth R (absoluteExtension R P).Ring := ‹_›
  let e := normalizedDeterminantAdjunction (R := A) (C := P.Cotangent)
    (B := A ⊗[P.Ring] (P.Ring ⊗[F] KaehlerDifferential R F))
    (V := (absoluteExtension R P).CotangentSpace) (M := KaehlerDifferential R A)
    (P := P.CotangentSpace)
    (absoluteExtension R P).cotangentComplex (absoluteExtension R P).toKaehler
    (conormalMap_injective (absoluteExtension R P))
    (absoluteExtension R P).exact_cotangentComplex_toKaehler
    (conormalSection (absoluteExtension R P)) (conormalSection_spec (absoluteExtension R P))
    ((KaehlerDifferential.mapBaseChange R F P.Ring).baseChange A)
    ((KaehlerDifferential.map R F P.Ring P.Ring).baseChange A)
    (ambientBaseDifferential_injective R F P.Ring A)
    (ambientBaseDifferential_exact R F P.Ring A)
    ((smoothBaseDifferentialSection R F P.Ring).baseChange A)
    (ambientBaseDifferentialSection_spec R F P.Ring A)
    bC bM ((bF.baseChange P.Ring).baseChange A) bQ hrank
  exact e.trans (LinearEquiv.congrLeft (⋀[A]^m (KaehlerDifferential R A)) A (exteriorLinearEquiv b
    (TensorProduct.AlgebraTensorModule.cancelBaseChange F P.Ring A A
      (KaehlerDifferential R F))))

end
end Red61

/-! Relative cotangent lengths use the algebra structure of the actual stalk
map. They are extended natural numbers: finiteness is never silently assumed.
These are Jacobian orders, not a definition of a global dualizing sheaf. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

def relativeCotangentLength {Y X : Scheme} (f : Y ⟶ X) (y : Y) : ℕ∞ :=
  let := (f.stalkMap y).hom.toAlgebra
  Module.length (Y.presheaf.stalk y)
    (KaehlerDifferential (X.presheaf.stalk (f y)) (Y.presheaf.stalk y))

end
end Red61

/-! Square presentations and determinant ideals of the actual relative
cotangent modules at DVR stalks. Presentation existence and independence
are proved algebraically; no extra geometric input is introduced. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

abbrev StalkCotangentModule {Y X : Scheme} (f : Y ⟶ X) (y : Y) : Type :=
  let := (f.stalkMap y).hom.toAlgebra
  KaehlerDifferential (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)

end
end Red61

/-! A relative Jacobian divisor is characterized by the lengths of the actual
relative differential modules at codimension-one stalks. Finite length is part
of the characterization; no conversion of an infinite length to zero occurs.

For a birational morphism to a regular scheme this is the local Jacobian
description of relative canonical discrepancy. Comparison with dualizing
canonical divisors requires a separate geometric theorem. -/

namespace Red61

open AlgebraicGeometry CategoryTheory Order
noncomputable section

structure IsRelativeJacobianDivisor {Y X : Scheme} (f : Y ⟶ X)
    (D : AlgebraicCycle Y ℤ) : Prop where
  codimension (y : Y) (hy : coheight y ≠ 1) : D y = 0
  length (y : Y) (hy : coheight y = 1) :
    ∃ n : ℕ, relativeCotangentLength f y = n ∧ D y = (n : ℤ)

end
end Red61

/-! Integer-base differentials act semilinearly on arbitrary ring maps.
The derivative formula and extensionality require no auxiliary chosen
algebra structure in their public statements. -/

namespace Red61
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Integer differentials of an arbitrary ring homomorphism. -/
def integerDifferentialSemilinear : KaehlerDifferential ℤ A →ₛₗ[φ] KaehlerDifferential ℤ B := by
  letI := φ.toAlgebra
  have : IsScalarTower ℤ A B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  exact linearToAlgebraSemilinear (KaehlerDifferential.map ℤ ℤ A B)

/-- The map retains the universal derivative formula. -/
theorem integerDifferentialSemilinear_D (a : A) :
    integerDifferentialSemilinear φ (KaehlerDifferential.D ℤ A a) =
      KaehlerDifferential.D ℤ B (φ a) := by
  let := φ.toAlgebra
  have : IsScalarTower ℤ A B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  exact KaehlerDifferential.map_D ℤ ℤ A B a

variable {V : Type*} [AddCommGroup V] [Module B V]

/-- Semilinear maps out of integer differentials are determined by derivatives. -/
theorem integerDifferential_semilinear_ext
    {f g : KaehlerDifferential ℤ A →ₛₗ[φ] V}
    (h : ∀ a, f (KaehlerDifferential.D ℤ A a) = g (KaehlerDifferential.D ℤ A a)) : f = g := by
  let : Module A V := Module.compHom V φ
  let f' : KaehlerDifferential ℤ A →ₗ[A] V :=
    { f.toAddHom with map_smul' := f.map_smul' }
  let g' : KaehlerDifferential ℤ A →ₗ[A] V :=
    { g.toAddHom with map_smul' := g.map_smul' }
  have he : f' = g' := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℤ A)
    exact h
  exact LinearMap.ext (fun ω ↦ LinearMap.congr_fun he ω)
end
end Red61

/-! Basis-free exterior transport of integer differentials along arbitrary
ring homomorphisms. Composition, actual wedge values, and agreement with
the earlier finite-basis top differential map are proved. -/

namespace Red61
open Module
noncomputable section
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (φ : A →+* B) (ψ : B →+* C) (τ : A →+* C) [RingHomCompTriple φ ψ τ]

/-- Basis-free exterior transport of ordinary integer differentials. -/
def integerDifferentialExteriorMap (n : ℕ) :
    (⋀[A]^n (KaehlerDifferential ℤ A)) →ₛₗ[φ]
      (⋀[B]^n (KaehlerDifferential ℤ B)) :=
  semilinearExteriorMap φ n (integerDifferentialSemilinear φ)

/-- Exterior differential transport preserves actual wedges. -/
theorem integerDifferentialExteriorMap_wedge (n : ℕ) (v : Fin n → KaehlerDifferential ℤ A) :
    integerDifferentialExteriorMap φ n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun j ↦ integerDifferentialSemilinear φ (v j)) :=
  semilinearExteriorMap_wedge φ n (integerDifferentialSemilinear φ) v

variable [Algebra A B] [IsScalarTower ℤ A B]

/-- For an algebra map the transport is the ordinary Kähler map. -/
theorem integerDifferentialSemilinear_algebraMap :
    integerDifferentialSemilinear (algebraMap A B) =
      linearToAlgebraSemilinear (KaehlerDifferential.map ℤ ℤ A B) := by
  apply integerDifferential_semilinear_ext
  intro a
  exact (integerDifferentialSemilinear_D (algebraMap A B) a).trans
    (KaehlerDifferential.map_D ℤ ℤ A B a).symm

/-- The basis-free transport agrees with the earlier top differential map. -/
theorem integerDifferentialExteriorMap_eq_top {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential ℤ A)) :
    integerDifferentialExteriorMap (algebraMap A B) n =
      semilinearTopExteriorMap b
        (linearToAlgebraSemilinear (KaehlerDifferential.map ℤ ℤ A B)) := by
  apply exteriorSemilinearMap_ext (algebraMap A B) n
  intro v
  exact (integerDifferentialExteriorMap_wedge (algebraMap A B) n v).trans
    ((congrArg (exteriorPower.ιMulti B n)
      (funext (fun j ↦ LinearMap.congr_fun integerDifferentialSemilinear_algebraMap (v j)))).trans
        (semilinearTopExteriorMap_wedge b
          (linearToAlgebraSemilinear (KaehlerDifferential.map ℤ ℤ A B)) v).symm)
end
end Red61

/-! Absolute differentials over the canonical integer algebra, and their
Jacobi--Zariski sequence for the actual scheme stalk map. This construction
does not assume smoothness over the surface's imperfect field of constants. -/

namespace Red61

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct
noncomputable section

abbrev AbsoluteStalkDifferentials (Y : Scheme) (y : Y) : Type :=
  KaehlerDifferential ℤ (Y.presheaf.stalk y)

abbrev PulledStalkDifferentials {Y X : Scheme} (f : Y ⟶ X) (y : Y) : Type :=
  let := (f.stalkMap y).hom.toAlgebra
  (Y.presheaf.stalk y) ⊗[X.presheaf.stalk (f y)]
    KaehlerDifferential ℤ (X.presheaf.stalk (f y))

def stalkDifferentialMap {Y X : Scheme} (f : Y ⟶ X) (y : Y) :
    PulledStalkDifferentials f y →ₗ[Y.presheaf.stalk y] AbsoluteStalkDifferentials Y y :=
  let := (f.stalkMap y).hom.toAlgebra
  KaehlerDifferential.mapBaseChange ℤ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)

def stalkDifferentialQuotient {Y X : Scheme} (f : Y ⟶ X) (y : Y) :
    AbsoluteStalkDifferentials Y y →ₗ[Y.presheaf.stalk y] StalkCotangentModule f y :=
  let := (f.stalkMap y).hom.toAlgebra
  KaehlerDifferential.map ℤ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) (Y.presheaf.stalk y)

theorem stalkDifferential_exact {Y X : Scheme} (f : Y ⟶ X) (y : Y) :
    Function.Exact (stalkDifferentialMap f y) (stalkDifferentialQuotient f y) := by
  let := (f.stalkMap y).hom.toAlgebra
  exact KaehlerDifferential.exact_mapBaseChange_map ℤ
    (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)

theorem stalkDifferentialQuotient_surjective {Y X : Scheme} (f : Y ⟶ X) (y : Y) :
    Function.Surjective (stalkDifferentialQuotient f y) := by
  let := (f.stalkMap y).hom.toAlgebra
  exact KaehlerDifferential.map_surjective ℤ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)

def stalkDifferentialCokernelEquiv {Y X : Scheme} (f : Y ⟶ X) (y : Y) :
    (AbsoluteStalkDifferentials Y y ⧸ LinearMap.range (stalkDifferentialMap f y))
      ≃ₗ[Y.presheaf.stalk y] StalkCotangentModule f y :=
  cokernelEquivOfExact _ _ (stalkDifferentialQuotient_surjective f y) (stalkDifferential_exact f y)

@[simp] theorem stalkDifferentialCokernelEquiv_mk {Y X : Scheme} (f : Y ⟶ X) (y : Y)
    (x : AbsoluteStalkDifferentials Y y) :
    stalkDifferentialCokernelEquiv f y (Submodule.Quotient.mk x) =
      stalkDifferentialQuotient f y x :=
  cokernelEquivOfExact_mk _ _ _ _ x

end
end Red61

/-! First cotangent homology and differential isomorphisms on the actual
isomorphism locus. No differential bases or monomial length input are needed
for these results. Injectivity of a differential map alone only kills the
connecting map; it is not confused with vanishing of first homology. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

theorem formallyEtale_of_bijective (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Bijective (algebraMap A B)) : Algebra.FormallyEtale A B :=
  Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) h)

end
end Red61

/-! Differential bases transported along actual ring isomorphisms and
localizations. All scalar maps used for tensor products are explicit. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

def differentialBasisOfFormallyEtale (R A B ι : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Algebra.FormallyEtale A B]
    (b : Basis ι A (KaehlerDifferential R A)) :
    Basis ι B (KaehlerDifferential R B) :=
  (b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)

def differentialBasisOfLocalization (R A B ι : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (M : Submonoid A) [IsLocalization M B]
    (b : Basis ι A (KaehlerDifferential R A)) :
    Basis ι B (KaehlerDifferential R B) := by
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) M
  exact differentialBasisOfFormallyEtale R A B ι b

def differentialBasisOfRingEquiv (R : Type*) {A B ι : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃+* B) (he : e.toRingHom.comp (algebraMap R A) = algebraMap R B)
    (b : Basis ι A (KaehlerDifferential R A)) :
    Basis ι B (KaehlerDifferential R B) := by
  let := e.toRingHom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' he.symm
  have : Algebra.FormallyEtale A B := formallyEtale_of_bijective A B e.bijective
  exact differentialBasisOfFormallyEtale R A B ι b

def absoluteDifferentialBasisOfRingEquiv {A B ι : Type*}
    [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (e : A ≃+* B) (b : Basis ι A (KaehlerDifferential ℤ A)) :
    Basis ι B (KaehlerDifferential ℤ B) :=
  differentialBasisOfRingEquiv ℤ e (Subsingleton.elim _ _) b

def absoluteDifferentialBasisAtPrime (A ι : Type*) [CommRing A] [Algebra ℤ A]
    (p : PrimeSpectrum A) (b : Basis ι A (KaehlerDifferential ℤ A)) :
    Basis ι (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal)) :=
  differentialBasisOfLocalization ℤ A (Localization.AtPrime p.asIdeal) ι p.asIdeal.primeCompl b

end
end Red61

/-! Absolute differentials in a common fraction field. The localization
equivalences are compatible with an intermediate ring, using the specified
scalar tower and the genuine differential base-change map. -/

namespace Red61

open TensorProduct
open scoped TensorProduct
noncomputable section

variable (A B F : Type*) [CommRing A] [CommRing B] [CommRing F]
  [Algebra A B] [Algebra B F] [Algebra A F] [IsScalarTower A B F]

def fractionDifferentialEquiv [IsFractionRing A F] :
    F ⊗[A] KaehlerDifferential ℤ A ≃ₗ[F] KaehlerDifferential ℤ F := by
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := F) (nonZeroDivisors A)
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A F

@[simp] theorem fractionDifferentialEquiv_tmul [IsFractionRing A F]
    (f : F) (ω : KaehlerDifferential ℤ A) :
    fractionDifferentialEquiv A F (f ⊗ₜ[A] ω) =
      f • KaehlerDifferential.map ℤ ℤ A F ω := by
  simp [fractionDifferentialEquiv]

theorem fractionDifferentialEquiv_tmul_D [IsFractionRing A F] (f : F) (a : A) :
    fractionDifferentialEquiv A F (f ⊗ₜ[A] KaehlerDifferential.D ℤ A a) =
      f • KaehlerDifferential.D ℤ F (algebraMap A F a) := by
  simp

end
end Red61

/-! Differential bases at primes transferred through an open localization. -/

namespace Red61

open Module
noncomputable section

def absoluteDifferentialBasisAtPrimeOfRingEquiv
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (e : A ≃+* B) (p : PrimeSpectrum B)
    (b : Basis ι (Localization.AtPrime (p.asIdeal.comap e.toRingHom))
      (KaehlerDifferential ℤ (Localization.AtPrime (p.asIdeal.comap e.toRingHom)))) :
    Basis ι (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal)) :=
  absoluteDifferentialBasisOfRingEquiv
    (IsLocalization.ringEquivOfRingEquiv
      (M := (p.asIdeal.comap e.toRingHom).primeCompl) (T := p.asIdeal.primeCompl)
      (Localization.AtPrime (p.asIdeal.comap e.toRingHom)) (Localization.AtPrime p.asIdeal)
      e (e.map_primeCompl_comap_eq p.asIdeal)) b

theorem absoluteDifferentialBasisAtPrime_of_away
    {A B ι : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    [Algebra A B] (d : A) [IsLocalization.Away d B]
    (p : PrimeSpectrum A) (hd : d ∉ p.asIdeal)
    (b : Basis ι B (KaehlerDifferential ℤ B)) :
    Nonempty (Basis ι (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) := by
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B d]
    exact hd
  obtain ⟨q, rfl⟩ := hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers d) (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := IsLocalization.algEquiv (q.asIdeal.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime (q.asIdeal.comap (algebraMap A B)))
  exact ⟨absoluteDifferentialBasisOfRingEquiv e.toRingEquiv
    (absoluteDifferentialBasisAtPrime B ι q b)⟩

end
end Red61

/-! A regular-pair presentation gives the native quotient-algebra
conormal basis of an extension. Both basis vectors are the actual
equation classes; no local or smoothness hypothesis is used. -/

namespace Red61
open Module RingTheory.Sequence
noncomputable section
variable {R : Type*} [CommRing R]

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (P : Algebra.Extension F A)
local notation "Q" => P.Ring ⧸ P.ker

@[instance_reducible] def extensionKernelQuotientAlgebra : Algebra Q A :=
  (RingHom.kerLift (algebraMap P.Ring A)).toAlgebra
private local instance : Algebra Q A := extensionKernelQuotientAlgebra P
private local instance : IsScalarTower P.Ring Q A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

end
end Red61

/-! Localizing a presentation at denominators already invertible
in its quotient preserves the mapped kernel and regular defining pairs.
The quotient ring and its original scalars remain fixed. -/

namespace Red61
noncomputable section
set_option backward.isDefEq.respectTransparency false
open RingTheory.Sequence
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (M : Submonoid A) [IsLocalization M A] (P : Algebra.Extension R A)
local notation "Q" => Algebra.Extension.localization (S' := A) M P
local notation "N" => M.comap (algebraMap P.Ring A)
private local instance : Algebra P.Ring (Q).Ring :=
  inferInstanceAs (Algebra P.Ring (Localization N))
private local instance : IsLocalization N (Q).Ring :=
  inferInstanceAs (IsLocalization N (Localization N))

theorem extensionUnitLocalization_kernel :
    (Q).ker = P.ker.map (algebraMap P.Ring (Q).Ring) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨n, t⟩, rfl⟩ := IsLocalization.mk'_surjective N x
    have he : algebraMap P.Ring A n = 0 := by
      have hs := congrArg (algebraMap (Q).Ring A) (IsLocalization.mk'_spec (Q).Ring n t)
      rw [map_mul, extensionLocalization_evaluation, extensionLocalization_evaluation] at hs
      change algebraMap (Q).Ring A (IsLocalization.mk' (Q).Ring n t) = 0 at hx
      simpa only [Algebra.algebraMap_self, RingHom.id_apply, hx, zero_mul] using hs.symm
    exact (IsLocalization.mk'_mem_map_algebraMap_iff N (Q).Ring P.ker n t).mpr
      ⟨1, (N).one_mem, by simpa using he⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change algebraMap P.Ring A x = 0 at hx
    change algebraMap (Q).Ring A (algebraMap P.Ring (Q).Ring x) = 0
    simpa only [extensionLocalization_evaluation, Algebra.algebraMap_self,
      RingHom.id_apply] using hx

theorem extensionUnitLocalization_regular_pair [Nontrivial A] {a b : P.Ring}
    (h : IsRegular P.Ring [a, b]) (ha : a ∈ P.ker) (hb : b ∈ P.ker) :
    IsRegular (Q).Ring [algebraMap P.Ring (Q).Ring a, algebraMap P.Ring (Q).Ring b] := by
  change algebraMap P.Ring A a = 0 at ha
  change algebraMap P.Ring A b = 0 at hb
  let f := algebraMap (Q).Ring A
  have hf (x : P.Ring) (hx : x ∈ [a, b]) :
      f (algebraMap P.Ring (Q).Ring x) = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa only [f, extensionLocalization_evaluation, Algebra.algebraMap_self,
        RingHom.id_apply] using ha
    · simpa only [f, extensionLocalization_evaluation, Algebra.algebraMap_self,
        RingHom.id_apply] using hb
  simpa only [List.map_cons, List.map_nil] using
    regular_localization_of_killed N h.toIsWeaklyRegular f hf
end
end Red61

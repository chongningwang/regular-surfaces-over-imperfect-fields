import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Red61.RingTheory.Regular

/-! # Polynomial-localization models

Formerly the modules `TensorGraphExtension`, `TensorPolynomialLocalization`, `PolynomialLocalizationModel`, `TensorGraphPolynomialKernel`, `TensorLeftPolynomialModel`.
-/

/-! A canonical relative ambient presentation from an absolute algebra.
The evaluation F tensor_R A -> A is surjective. Its relative ambient
differentials, restricted to A, are the absolute R-differentials of A. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable (R F A : Type*) [CommRing R] [CommRing F] [CommRing A]
  [Algebra R F] [Algebra R A] [Algebra F A] [IsScalarTower R F A]

def tensorGraphMap : F ⊗[R] A →ₐ[F] A :=
  AlgHom.liftEquiv R F A A (AlgHom.id R A)

@[simp] theorem tensorGraphMap_tmul (f : F) (a : A) :
    tensorGraphMap R F A (f ⊗ₜ a) = algebraMap F A f * a := by
  exact Algebra.smul_def f a

theorem tensorGraphMap_surjective : Function.Surjective (tensorGraphMap R F A) :=
  fun a ↦ ⟨1 ⊗ₜ a, by simp⟩

def tensorGraphExtension : Algebra.Extension F A :=
  Algebra.Extension.ofSurjective (tensorGraphMap R F A) (tensorGraphMap_surjective R F A)

end
end Red61

/-! Tensoring a polynomial localization is again a polynomial localization,
with an explicit coefficient algebra map and denominator monoid. This also
proves Noetherianity when the coefficient ring is Noetherian. -/

namespace Red61

open scoped TensorProduct
noncomputable section

variable (R F A σ : Type*) [CommRing R] [CommRing F] [CommRing A]
  [Algebra R F] [Algebra R A]

def tensorPolynomialRingEquiv :
    (MvPolynomial σ R ⊗[R] A) ≃+* MvPolynomial σ A :=
  (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv R A).toRingEquiv

@[simp] theorem tensorPolynomialRingEquiv_tmul (p : MvPolynomial σ R) (a : A) :
    tensorPolynomialRingEquiv R A σ (p ⊗ₜ a) =
      a • MvPolynomial.map (algebraMap R A) p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul R A a p

@[simp] theorem tensorPolynomialRingEquiv_symm_C (a : A) :
    (tensorPolynomialRingEquiv R A σ).symm (MvPolynomial.C a) =
      (1 : MvPolynomial σ R) ⊗ₜ a := by
  change (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).symm
    ((MvPolynomial.algebraTensorAlgEquiv R A).symm (algebraMap A (MvPolynomial σ A) a)) = _
  rw [AlgEquiv.commutes]
  rfl

@[simp] theorem tensorPolynomialRingEquiv_symm_X (i : σ) :
    (tensorPolynomialRingEquiv R A σ).symm (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ R) ⊗ₜ (1 : A) := by
  change (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).symm
    ((MvPolynomial.algebraTensorAlgEquiv R A).symm (MvPolynomial.X i)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X]
  rfl

variable [Algebra (MvPolynomial σ R) F] [IsScalarTower R (MvPolynomial σ R) F]

def tensorPolynomialBaseMap :
    (MvPolynomial σ R ⊗[R] A) →ₐ[R] (F ⊗[R] A) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPolynomial σ R) F) (AlgHom.id R A)

@[instance_reducible]
def tensorPolynomialAlgebra : Algebra (MvPolynomial σ A) (F ⊗[R] A) :=
  ((tensorPolynomialBaseMap R F A σ).toRingHom.comp
    (tensorPolynomialRingEquiv R A σ).symm.toRingHom).toAlgebra

@[simp] theorem tensorPolynomialAlgebra_C (a : A) :
    letI := tensorPolynomialAlgebra R F A σ
    algebraMap (MvPolynomial σ A) (F ⊗[R] A) (MvPolynomial.C a) = (1 : F) ⊗ₜ a := by
  let := tensorPolynomialAlgebra R F A σ
  change tensorPolynomialBaseMap R F A σ
    ((tensorPolynomialRingEquiv R A σ).symm (MvPolynomial.C a)) = _
  rw [tensorPolynomialRingEquiv_symm_C]
  simp [tensorPolynomialBaseMap]

@[simp] theorem tensorPolynomialAlgebra_X (i : σ) :
    letI := tensorPolynomialAlgebra R F A σ
    algebraMap (MvPolynomial σ A) (F ⊗[R] A) (MvPolynomial.X i) =
      algebraMap (MvPolynomial σ R) F (MvPolynomial.X i) ⊗ₜ (1 : A) := by
  let := tensorPolynomialAlgebra R F A σ
  change tensorPolynomialBaseMap R F A σ
    ((tensorPolynomialRingEquiv R A σ).symm (MvPolynomial.X i)) = _
  rw [tensorPolynomialRingEquiv_symm_X]
  simp [tensorPolynomialBaseMap]

def tensorPolynomialDenominators (M : Submonoid (MvPolynomial σ R)) :
    Submonoid (MvPolynomial σ A) :=
  (Algebra.algebraMapSubmonoid (MvPolynomial σ R ⊗[R] A) M).map
    (tensorPolynomialRingEquiv R A σ).toMonoidHom

theorem tensorPolynomial_isLocalization (M : Submonoid (MvPolynomial σ R))
    [IsLocalization M F] :
    letI := tensorPolynomialAlgebra R F A σ
    IsLocalization (tensorPolynomialDenominators R A σ M) (F ⊗[R] A) := by
  let := tensorPolynomialAlgebra R F A σ
  let T := MvPolynomial σ R ⊗[R] A
  let : Algebra T (F ⊗[R] A) := (tensorPolynomialBaseMap R F A σ).toAlgebra
  have : @IsScalarTower (MvPolynomial σ R) T (F ⊗[R] A)
      (Algebra.toSMul : SMul (MvPolynomial σ R) T)
      (Algebra.toSMul : SMul T (F ⊗[R] A))
      (Algebra.toSMul : SMul (MvPolynomial σ R) (F ⊗[R] A)) := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro p
    change algebraMap (MvPolynomial σ R) F p ⊗ₜ (1 : A) =
      tensorPolynomialBaseMap R F A σ (p ⊗ₜ (1 : A))
    simp [tensorPolynomialBaseMap]
  have : IsLocalization (Algebra.algebraMapSubmonoid T M) (F ⊗[R] A) :=
    IsLocalization.tensorProduct_tensorProduct R A M F (by
      ext a
      simp [RingHom.algebraMap_toAlgebra, tensorPolynomialBaseMap])
  exact IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid T M) (F ⊗[R] A)
    (tensorPolynomialRingEquiv R A σ)

end
end Red61

/-! Polynomial-localization models retain their actual coefficient
map and denominator monoid. They transport through scalar-compatible
ring isomorphisms, prime localizations, and principal-open neighborhoods. -/

namespace Red61
noncomputable section
variable (F A : Type) [Field F] [CommRing A] [Algebra F A] (ι : Type)
structure PolynomialLocalizationModel where
  map : MvPolynomial ι F →ₐ[F] A
  denominators : Submonoid (MvPolynomial ι F)
  isLocalization : letI := map.toAlgebra; IsLocalization denominators A
namespace PolynomialLocalizationModel
variable {F A ι} {B : Type} [CommRing B] [Algebra F B]

def transport (P : PolynomialLocalizationModel F A ι) (e : A ≃ₐ[F] B) :
    PolynomialLocalizationModel F B ι where
  map := e.toAlgHom.comp P.map
  denominators := P.denominators
  isLocalization := by
    let := P.map.toAlgebra
    let := (e.toAlgHom.comp P.map).toAlgebra
    have := P.isLocalization
    let E : A ≃ₐ[MvPolynomial ι F] B := { e.toRingEquiv with commutes' _ := rfl }
    exact IsLocalization.isLocalization_of_algEquiv P.denominators E

def atPrime (P : PolynomialLocalizationModel F A ι) (p : PrimeSpectrum A) :
    PolynomialLocalizationModel F (Localization.AtPrime p.asIdeal) ι where
  map := (IsScalarTower.toAlgHom F A (Localization.AtPrime p.asIdeal)).comp P.map
  denominators := p.asIdeal.primeCompl.comap P.map.toRingHom
  isLocalization := by
    let := P.map.toAlgebra
    let := ((IsScalarTower.toAlgHom F A (Localization.AtPrime p.asIdeal)).comp P.map).toAlgebra
    let : SMul (MvPolynomial ι F) A := Algebra.toSMul
    let : SMul A (Localization.AtPrime p.asIdeal) := Algebra.toSMul
    let : SMul (MvPolynomial ι F) (Localization.AtPrime p.asIdeal) := Algebra.toSMul
    have : IsScalarTower (MvPolynomial ι F) A (Localization.AtPrime p.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have := P.isLocalization
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      P.denominators (Localization.AtPrime p.asIdeal) p.asIdeal

def ofSubalgebra {K : Type} [Field K] [Algebra F K]
    (C D : Subalgebra F K) (h : C ≤ D) (hh : D ≤ FieldLocalization.hull C D)
    (e : MvPolynomial ι F ≃ₐ[F] C) : PolynomialLocalizationModel F D ι where
  map := (Subalgebra.inclusion h).comp e.toAlgHom
  denominators := (FieldLocalization.denominators h).map e.symm.toMonoidHom
  isLocalization := by
    let := AffineGluing.inclusionAlgebra h
    have := FieldLocalization.isLocalization h hh
    exact IsLocalization.isLocalization_of_base_ringEquiv
      (FieldLocalization.denominators h) D e.symm.toRingEquiv
def transportRingEquiv (P : PolynomialLocalizationModel F A ι) (e : A ≃+* B)
    (he : e.toRingHom.comp (algebraMap F A) = algebraMap F B) :
    PolynomialLocalizationModel F B ι :=
  P.transport { e with commutes' a := RingHom.congr_fun he a }

variable [Algebra A B] [IsScalarTower F A B]

def atPrimeOfAway (P : PolynomialLocalizationModel F B ι) (d : A)
    [IsLocalization.Away d B] (p : PrimeSpectrum A) (hd : d ∉ p.asIdeal) :
    PolynomialLocalizationModel F (Localization.AtPrime p.asIdeal) ι := by
  apply Classical.choice
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B d]
    exact hd
  obtain ⟨q, rfl⟩ := hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Submonoid.powers d) (Localization.AtPrime q.asIdeal) q.asIdeal
  let e := IsLocalization.algEquiv (q.asIdeal.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime (q.asIdeal.comap (algebraMap A B)))
  exact ⟨(P.atPrime q).transport (e.restrictScalars F)⟩
end PolynomialLocalizationModel
end
end Red61

/-! Equations of a tensor graph over a polynomial localization. The kernel
is the actual localization of the shifted-variable evaluation ideal; its
generators and their images in the tensor ambient are explicit. -/

namespace Red61

open scoped TensorProduct
noncomputable section

variable (R F A σ : Type*) [CommRing R] [CommRing F] [CommRing A]
  [Algebra R F] [Algebra R A] [Algebra F A] [IsScalarTower R F A]
  [Algebra (MvPolynomial σ R) F] [IsScalarTower R (MvPolynomial σ R) F]

def tensorGraphPolynomialValues (i : σ) : A :=
  algebraMap F A (algebraMap (MvPolynomial σ R) F (MvPolynomial.X i))

theorem tensorGraphPolynomial_eval :
    letI := tensorPolynomialAlgebra R F A σ
    (tensorGraphMap R F A).toRingHom.comp
      (algebraMap (MvPolynomial σ A) (F ⊗[R] A)) =
        (MvPolynomial.aeval (tensorGraphPolynomialValues R F A σ)).toRingHom := by
  let := tensorPolynomialAlgebra R F A σ
  apply MvPolynomial.ringHom_ext
  · intro a
    change tensorGraphMap R F A
      (algebraMap (MvPolynomial σ A) (F ⊗[R] A) (MvPolynomial.C a)) =
        MvPolynomial.aeval (tensorGraphPolynomialValues R F A σ) (MvPolynomial.C a)
    rw [tensorPolynomialAlgebra_C, tensorGraphMap_tmul, MvPolynomial.aeval_C]
    simp
  · intro i
    change tensorGraphMap R F A
      (algebraMap (MvPolynomial σ A) (F ⊗[R] A) (MvPolynomial.X i)) =
        MvPolynomial.aeval (tensorGraphPolynomialValues R F A σ) (MvPolynomial.X i)
    rw [tensorPolynomialAlgebra_X, tensorGraphMap_tmul, MvPolynomial.aeval_X, mul_one]
    rfl

theorem tensorGraphKernel_eq_map (M : Submonoid (MvPolynomial σ R)) [IsLocalization M F] :
    letI := tensorPolynomialAlgebra R F A σ
    RingHom.ker (tensorGraphMap R F A).toRingHom =
      Ideal.map (algebraMap (MvPolynomial σ A) (F ⊗[R] A))
        (shiftedVariablesIdeal (tensorGraphPolynomialValues R F A σ)) := by
  let := tensorPolynomialAlgebra R F A σ
  have := tensorPolynomial_isLocalization R F A σ M
  have he : (RingHom.ker (tensorGraphMap R F A).toRingHom).under (MvPolynomial σ A) =
      shiftedVariablesIdeal (tensorGraphPolynomialValues R F A σ) := by
    change (RingHom.ker (tensorGraphMap R F A).toRingHom).comap
      (algebraMap (MvPolynomial σ A) (F ⊗[R] A)) = _
    rw [RingHom.comap_ker, tensorGraphPolynomial_eval, ker_aeval_eq_shiftedVariablesIdeal]
  have h := IsLocalization.map_under (tensorPolynomialDenominators R A σ M)
    (F ⊗[R] A) (RingHom.ker (tensorGraphMap R F A).toRingHom)
  rw [he] at h
  exact h.symm

theorem tensorGraphKernel_eq_span (M : Submonoid (MvPolynomial σ R)) [IsLocalization M F] :
    RingHom.ker (tensorGraphMap R F A).toRingHom =
      Ideal.span (Set.range (fun i : σ ↦
        algebraMap (MvPolynomial σ R) F (MvPolynomial.X i) ⊗ₜ (1 : A) -
          (1 : F) ⊗ₜ tensorGraphPolynomialValues R F A σ i)) := by
  let := tensorPolynomialAlgebra R F A σ
  simpa only [shiftedVariablesIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def,
    map_sub, tensorPolynomialAlgebra_X, tensorPolynomialAlgebra_C] using
      tensorGraphKernel_eq_map R F A σ M

end
end Red61

/-! Base change on the left preserves the specified polynomial
localization model. The coefficient map uses the native left tensor
algebra, with no replacement of the original field scalars. -/

namespace Red61.PolynomialLocalizationModel
open scoped TensorProduct
noncomputable section
variable {R A : Type} [Field R] [CommRing A] [Algebra R A] {ι : Type}
variable (P : PolynomialLocalizationModel R A ι)
variable (F : Type) [Field F] [Algebra R F]

def tensorLeft : PolynomialLocalizationModel F (F ⊗[R] A) ι := by
  let := P.map.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq' P.map.comp_algebraMap.symm
  let := tensorPolynomialAlgebra R A F ι
  let f : MvPolynomial ι F →ₐ[F] F ⊗[R] A :=
    { toRingHom := (Algebra.TensorProduct.comm R A F).toRingHom.comp
        (algebraMap (MvPolynomial ι F) (A ⊗[R] F))
      commutes' a := by
        change (Algebra.TensorProduct.comm R A F)
          (algebraMap (MvPolynomial ι F) (A ⊗[R] F) (MvPolynomial.C a)) = _
        rw [tensorPolynomialAlgebra_C]
        rfl }
  refine {
    map := f
    denominators := tensorPolynomialDenominators R F ι P.denominators
    isLocalization := ?_ }
  let := f.toAlgebra
  have := P.isLocalization
  have := tensorPolynomial_isLocalization R A F ι P.denominators
  let e : (A ⊗[R] F) ≃ₐ[MvPolynomial ι F] (F ⊗[R] A) :=
    { (Algebra.TensorProduct.comm R A F).toRingEquiv with commutes' _ := rfl }
  exact IsLocalization.isLocalization_of_algEquiv
    (tensorPolynomialDenominators R F ι P.denominators) e
end
end Red61.PolynomialLocalizationModel

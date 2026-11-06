import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic
import Red61.AlgebraicGeometry.Atlas
import Red61.Surface.Charts

/-! # The cone point and its regularity

Formerly the modules `TruncatedCone`, `ConeRing`, `ConeChart`, `ConeInvariants`, `ConeQuotient`, `ConeSupport`, `ConeDimension`, `ConeRegularity`, `InvariantFractionField`, `LocalGeometry`.
-/

namespace Red61.TruncatedCone

variable {k E : Type*} [CommRing k] [CommRing E]

def NormalForm (f : k →+* E) (v z x : E) : Prop :=
  ∃ a₀ a₁ a₂ a₃ a₄ : k,
    x = f a₀ + f a₁ * v + f a₂ * z + f a₃ * v * z + f a₄ * z ^ 2

theorem normalForm_add (f : k →+* E) (v z : E) {x y : E}
    (hx : NormalForm f v z x) (hy : NormalForm f v z y) :
    NormalForm f v z (x + y) := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, rfl⟩ := hx
  obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl⟩ := hy
  refine ⟨a₀+b₀, a₁+b₁, a₂+b₂, a₃+b₃, a₄+b₄, ?_⟩
  simp only [map_add]
  ring

theorem normalForm_mul (f : k →+* E) (v z : E)
    (hv : v ^ 2 = 0) (hvz : v * z ^ 2 = 0) (hz : z ^ 3 = 0)
    {x y : E} (hx : NormalForm f v z x) (hy : NormalForm f v z y) :
    NormalForm f v z (x * y) := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, rfl⟩ := hx
  obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl⟩ := hy
  refine ⟨a₀*b₀, a₀*b₁+a₁*b₀, a₀*b₂+a₂*b₀,
    a₀*b₃+a₃*b₀+a₁*b₂+a₂*b₁, a₀*b₄+a₄*b₀+a₂*b₂, ?_⟩
  simp only [map_add, map_mul]
  linear_combination
    (f a₁ + f a₃ * z) * (f b₁ + f b₃ * z) * hv +
    (f a₂*f b₃+f a₄*f b₁+f a₁*f b₄+f a₃*f b₂+z*(f a₄*f b₃+f a₃*f b₄))*hvz +
    (f a₂*f b₄+f a₄*f b₂+z*f a₄*f b₄)*hz

theorem normalForm_adjoin [Algebra k E] (v z : E)
    (hv : v^2=0) (hvz : v*z^2=0) (hz : z^3=0) {x : E}
    (hx : x ∈ Algebra.adjoin k ({v,z} : Set E)) :
    NormalForm (algebraMap k E) v z x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨0,1,0,0,0,by simp⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨0,0,1,0,0,by simp⟩
  | algebraMap a => exact ⟨a,0,0,0,0,by simp⟩
  | add x y hx hy ihx ihy => exact normalForm_add _ _ _ ihx ihy
  | mul x y hx hy ihx ihy => exact normalForm_mul _ _ _ hv hvz hz ihx ihy

theorem subtype_generators_top [Algebra k E] {ι : Type*} (g : ι → E) :
    Algebra.adjoin k (Set.range (fun i : ι =>
      (⟨g i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : Algebra.adjoin k (Set.range g)))) = ⊤ := by
  convert Algebra.adjoin_adjoin_coe_preimage (R := k) (s := Set.range g) using 1
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i,hi⟩
    exact ⟨i, Subtype.ext hi⟩

section Derivation

variable {F : Type*} [CommRing F] [Algebra F E] [CharP E 5]
  (D : Derivation F E E) (f : k →+* E) (v z : E) (d₁ d₂ : k → k)
  (hc : ∀ a, D (f a) = v * f (d₁ a) + z * f (d₂ a))
  (hvD : D v = v) (hzD : D z = 2 * z)
  (hv : v ^ 2 = 0) (hvz : v * z ^ 2 = 0) (hz : z ^ 3 = 0)

include hc hvD hv in
omit [CharP E 5] in
theorem derivative_v (a : k) :
    D (f a * v) = f a * v + f (d₂ a) * v * z := by
  rw [Derivation.leibniz, hvD, hc]
  simp only [smul_eq_mul]
  linear_combination f (d₁ a) * hv

include hc hzD in
omit [CharP E 5] in
theorem derivative_z (a : k) :
    D (f a * z) = 2 * (f a * z) + f (d₁ a) * v * z + f (d₂ a) * z ^ 2 := by
  rw [Derivation.leibniz, hzD, hc]
  simp only [smul_eq_mul]
  ring

include hc hvD hzD hv hvz in
omit [CharP E 5] in
theorem derivative_vz (a : k) : D (f a * v * z) = 3 * (f a * v * z) := by
  simp only [Derivation.leibniz, hvD, hzD, hc, smul_eq_mul]
  linear_combination f (d₁ a) * z * hv + f (d₂ a) * hvz

include hc hzD hvz hz in
omit [CharP E 5] in
theorem derivative_zz (a : k) : D (f a * z ^ 2) = 4 * (f a * z ^ 2) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, hc, hzD,
    smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
  linear_combination f (d₁ a) * hvz + f (d₂ a) * hz

include hc hvD hzD hv hvz hz in
theorem fourth_on_positive (a : k) :
    D (D (D (D (f a * v)))) = f a * v ∧
    D (D (D (D (f a * z)))) = f a * z ∧
    D (D (D (D (f a * v * z)))) = f a * v * z ∧
    D (D (D (D (f a * z ^ 2)))) = f a * z ^ 2 := by
  have h₁ := derivative_v D f v z d₁ d₂ hc hvD hv
  have h₂ := derivative_z D f v z d₁ d₂ hc hzD
  have h₃ := derivative_vz D f v z d₁ d₂ hc hvD hzD hv hvz
  have h₄ := derivative_zz D f v z d₁ d₂ hc hzD hvz hz
  have hn (n : ℕ) (x : E) : D ((n : E) * x) = (n : E) * D x := by
    simp [Derivation.leibniz, smul_eq_mul]
  have htwo (x : E) : D (2*x) = 2*D x := hn 2 x
  have hthree (x : E) : D (3*x) = 3*D x := hn 3 x
  have hfour (x : E) : D (4*x) = 4*D x := hn 4 x
  have h5 : (5 : E) = 0 := CharP.cast_eq_zero E 5
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [h₁, h₃, map_add, hthree]
    linear_combination 8 * f (d₂ a) * v * z * h5
  · simp only [h₂, h₃, h₄, map_add, htwo, hthree, hfour]
    linear_combination (3*f a*z + 13*f (d₁ a)*v*z + 24*f (d₂ a)*z^2)*h5
  · simp only [h₃, hthree]
    linear_combination 16 * f a * v * z * h5
  · simp only [h₄, hfour]
    linear_combination 51 * f a * z^2 * h5

end Derivation
end Red61.TruncatedCone

namespace Red61.ConeRing


open Fields LocalCoordinates
noncomputable section

abbrev P := MvPolynomial (Fin 2) k
local instance : CommRing P := inferInstance
def mon (a b : ℕ) : P := MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b
def generator : Fin 4 → P := ![mon 1 0, mon 1 1, mon 1 2, mon 2 5]
def A : Subalgebra k P := Algebra.adjoin k (Set.range generator)
instance : CommRing A := inferInstance

theorem generator_mem (i : Fin 4) : generator i ∈ A :=
  Algebra.subset_adjoin (Set.mem_range_self i)

instance : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
instance : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A

def evaluate : P →ₐ[k] K := MvPolynomial.aeval coneCoordinates

theorem evaluate_injective : Function.Injective evaluate := coneCoordinates_independent

@[simp] theorem evaluate_mon (a b : ℕ) : evaluate (mon a b) = U ^ a * T ^ b := by
  simp [evaluate, mon, coneCoordinates, U, T]

def embed : A →ₐ[k] K := evaluate.comp A.val

theorem embed_injective : Function.Injective embed := evaluate_injective.comp Subtype.val_injective

def augmentation : P →ₐ[k] k := MvPolynomial.aeval (fun _ => 0)
def residue : A →ₐ[k] k := augmentation.comp A.val

theorem residue_surjective : Function.Surjective residue := by
  intro x
  exact ⟨algebraMap k A x, residue.commutes x⟩

/-- The torus-fixed maximal ideal, defined without an unproved presentation. -/
def maximal : Ideal A := RingHom.ker residue

instance : maximal.IsMaximal := RingHom.ker_isMaximal_of_surjective residue residue_surjective

abbrev R := Localization.AtPrime maximal
instance : CommRing R := inferInstance
instance : Module ell R := Algebra.toModule

instance : IsNoetherianRing R := IsLocalization.isNoetherianRing maximal.primeCompl R inferInstance

theorem generator_residue_zero (i : Fin 4) : residue ⟨generator i, generator_mem i⟩ = 0 := by
  fin_cases i <;> simp [residue, augmentation, generator, mon]

@[simp] theorem augmentation_generator (i : Fin 4) : augmentation (generator i) = 0 :=
  generator_residue_zero i

theorem image_stable (p : P) (hp : p ∈ A) :
    ∃ q : P, q ∈ A ∧ evaluate q = theta (evaluate p) ∧ augmentation q = 0 := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · exact ⟨0, A.zero_mem, by simp [generator], by simp⟩
    · exact ⟨generator 1, generator_mem 1,
        by simp [generator, Derivation.leibniz, smul_eq_mul], augmentation_generator 1⟩
    · refine ⟨2 * generator 2, A.mul_mem (A.natCast_mem 2) (generator_mem 2), ?_, by simp⟩
      have htwo : evaluate (2 : P) = (2 : K) := map_ofNat evaluate 2
      simp [generator, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
        nsmul_eq_mul, htwo]
      ring
    · refine ⟨0, A.zero_mem, ?_, by simp⟩
      simpa [generator, r] using theta_r.symm
  | algebraMap a =>
    refine ⟨generator 1 * MvPolynomial.C (coeffDeriv 0 a) +
      generator 2 * MvPolynomial.C (coeffDeriv 1 a), ?_, ?_, by simp⟩
    · exact A.add_mem (A.mul_mem (generator_mem 1) (A.algebraMap_mem _))
        (A.mul_mem (generator_mem 2) (A.algebraMap_mem _))
    · have heC (a : k) : evaluate (MvPolynomial.C a) = includeK a := evaluate.commutes a
      have hg₁ : evaluate (generator 1) = U * T := by simp [generator]
      have hg₂ : evaluate (generator 2) = U * T ^ 2 := by simp [generator]
      simp only [map_add, map_mul, MvPolynomial.algebraMap_eq, heC, hg₁, hg₂]
      change U * T * includeK (coeffDeriv 0 a) + U * T ^ 2 * includeK (coeffDeriv 1 a) =
        U * T * delta (includeK a)
      rw [delta_on_k]
      change _ = U * T * (includeK (coeffDeriv 0 a) + T * includeK (coeffDeriv 1 a))
      ring
  | add x y hx hy ihx ihy =>
    obtain ⟨x', hx', heqx, haugx⟩ := ihx
    obtain ⟨y', hy', heqy, haugy⟩ := ihy
    exact ⟨x' + y', A.add_mem hx' hy',
      by rw [map_add, heqx, heqy, map_add, map_add], by simp [haugx, haugy]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨x', hx', heqx, haugx⟩ := ihx
    obtain ⟨y', hy', heqy, haugy⟩ := ihy
    refine ⟨x * y' + y * x', A.add_mem (A.mul_mem hx hy') (A.mul_mem hy hx'),
      ?_, by simp [haugx, haugy]⟩
    simp only [map_add, map_mul, heqx, heqy, Derivation.leibniz, smul_eq_mul]

def embedEll : A →ₐ[ell] K where
  __ := embed.toRingHom
  commutes' a := by
    change evaluate (algebraMap k P (a : k)) = includeK (a : k)
    exact evaluate.commutes (a : k)

theorem image_stable_subtype (a : A) : ∃ a' : A, embedEll a' = theta (embedEll a) := by
  obtain ⟨q, hq, he, _⟩ := image_stable a a.property
  exact ⟨⟨q, hq⟩, he⟩

def D : Derivation ell A A :=
  restrictDerivation (F := ell) (A := A) (B := K)
    embedEll embed_injective theta image_stable_subtype

@[simp] theorem embed_D (a : A) : embedEll (D a) = theta (embedEll a) :=
  restrictDerivation_apply _ _ _ _ a

@[simp] theorem residue_D (a : A) : residue (D a) = 0 := by
  obtain ⟨q, hq, he, haug⟩ := image_stable a a.property
  have hd : D a = ⟨q, hq⟩ := embed_injective (by
    change embedEll (D a) = evaluate q
    rw [embed_D]
    exact he.symm)
  rw [hd]
  exact haug

theorem D_five (a : A) : D (D (D (D (D a)))) = D a := by
  apply embed_injective
  change embedEll (D (D (D (D (D a))))) = embedEll (D a)
  simp only [embed_D, theta_five]

theorem denominator_unit (a : maximal.primeCompl) : IsUnit (embedEll a) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hz : (a : A) = 0 := embed_injective (h.trans (map_zero embed).symm)
  exact a.property (hz ▸ maximal.zero_mem)

def localEmbed : R →ₐ[ell] K := IsLocalization.liftAlgHom denominator_unit

@[simp] theorem localEmbed_algebraMap (a : A) :
    localEmbed (algebraMap A R a) = embedEll a := IsLocalization.lift_eq _ _

theorem localEmbed_injective : Function.Injective localEmbed := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := maximal.primeCompl) R
    localEmbed.toRingHom
  intro a ha
  have hz : a = 0 := embed_injective (by
    change embedEll a = embedEll 0
    simpa using ha)
  rw [hz, map_zero]

@[simp] theorem localEmbed_mk (a : A) (b : maximal.primeCompl) :
    localEmbed (IsLocalization.mk' R a b) = embedEll a / embedEll b := by
  apply (IsLocalization.lift_mk'_spec denominator_unit a _ b).mpr
  field_simp [(isUnit_iff_ne_zero.mp (denominator_unit b))]
  change embedEll a * embedEll b = embedEll b * embedEll a
  ring

theorem local_image_stable (x : R) : ∃ x' : R, localEmbed x' = theta (localEmbed x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective maximal.primeCompl x
  refine ⟨IsLocalization.mk' R (D a * b - a * D b) (b ^ 2), ?_⟩
  rw [localEmbed_mk, localEmbed_mk, Derivation.leibniz_div]
  simp only [map_sub, map_mul, SubmonoidClass.coe_pow, map_pow,
    embed_D, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

def localD : Derivation ell R R :=
  restrictDerivation (F := ell) (A := R) (B := K)
    localEmbed localEmbed_injective theta local_image_stable

@[simp] theorem localEmbed_D (x : R) : localEmbed (localD x) = theta (localEmbed x) :=
  restrictDerivation_apply _ _ _ _ x

theorem localD_five (x : R) : localD (localD (localD (localD (localD x)))) = localD x := by
  apply localEmbed_injective
  simp only [localEmbed_D, theta_five]

@[simp] theorem localD_algebraMap (a : A) :
    localD (algebraMap A R a) = algebraMap A R (D a) := by
  apply localEmbed_injective
  simp

theorem residue_denominator_unit (a : maximal.primeCompl) : IsUnit (residue a) := by
  apply isUnit_iff_ne_zero.mpr
  exact a.property

def localResidue : R →ₐ[k] k := IsLocalization.liftAlgHom residue_denominator_unit

@[simp] theorem localResidue_algebraMap (a : A) :
    localResidue (algebraMap A R a) = residue a := IsLocalization.lift_eq _ _

theorem localResidue_surjective : Function.Surjective localResidue := by
  intro a
  exact ⟨algebraMap k R a, localResidue.commutes a⟩

@[simp] theorem localResidue_D (x : R) : localResidue (localD x) = 0 := by
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj maximal.primeCompl x
  have hd := congrArg localD hb
  rw [Derivation.leibniz, localD_algebraMap, localD_algebraMap] at hd
  have hr := congrArg localResidue hd
  simp only [smul_eq_mul, map_add, map_mul, localResidue_algebraMap, residue_D,
    mul_zero, zero_add] at hr
  exact (mul_eq_zero.mp hr).resolve_left
    (isUnit_iff_ne_zero.mp (residue_denominator_unit b))

end
end Red61.ConeRing

/-! The contracted cone chart inside the common rational function field. -/

namespace Red61.Contraction

open Fields Charts Fan
noncomputable section

def coneRing : Subalgebra k K := ConeRing.embed.range

def coneRingEquiv : ConeRing.A ≃ₐ[k] coneRing :=
  AlgEquiv.ofInjective ConeRing.embed ConeRing.embed_injective

@[simp] theorem coneRingEquiv_coe (a : ConeRing.A) :
    (coneRingEquiv a : K) = ConeRing.embed a := rfl

def coneExponent : Fin 4 → Lattice := ![(0,-1), (1,-1), (2,-1), (5,-2)]

theorem cone_generator_image (a : Fin 4) :
    ConeRing.evaluate (ConeRing.generator a) = monomial (coneExponent a) := by
  fin_cases a <;>
    simp [ConeRing.generator, ConeRing.evaluate_mon, coneExponent, monomial,
      LocalCoordinates.U, LocalCoordinates.T, mul_comm, inv_pow]

theorem cone_generator_mem (a : Fin 4) : monomial (coneExponent a) ∈ coneRing :=
  ⟨⟨ConeRing.generator a, ConeRing.generator_mem a⟩, cone_generator_image a⟩

theorem coneRing_le_iff (E : Subalgebra k K) :
    coneRing ≤ E ↔ ∀ a, monomial (coneExponent a) ∈ E := by
  constructor
  · exact fun h a ↦ h (cone_generator_mem a)
  · intro h x hx
    obtain ⟨a,rfl⟩ := hx
    have ha := a.property
    change ConeRing.evaluate (a : ConeRing.P) ∈ E
    generalize (a : ConeRing.P) = p at ha ⊢
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      rw [cone_generator_image]
      exact h j
    | algebraMap r => simp
    | add x y hx hy ihx ihy => simpa using E.add_mem ihx ihy
    | mul x y hx hy ihx ihy => simpa using E.mul_mem ihx ihy

def combination {n : ℕ} (v : Fin n → Lattice) (c : Fin n → ℕ) : Lattice :=
  ∑ a, (c a : ℤ) • v a

/-- A nonnegative lattice certificate gives membership in the monomial subalgebra. -/
theorem combination_mem {n : ℕ} (E : Subalgebra k K) (v : Fin n → Lattice)
    (c : Fin n → ℕ) (hv : ∀ a, monomial (v a) ∈ E) :
    monomial (combination v c) ∈ E := by
  have h (s : Finset (Fin n)) : monomial (∑ a ∈ s, (c a : ℤ) • v a) ∈ E := by
    induction s using Finset.induction_on with
    | empty => simp [monomial]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, monomial_mul, monomial_zsmul, zpow_natCast]
      exact E.mul_mem (E.pow_mem (hv a) _) ih
  exact h Finset.univ

/-- Charts V1,V4,V6 survive the deletion of the two exceptional rays. -/
def kept : Fin 3 → Fin 6 := ![0,3,5]

/-- The three resolved charts contained in the contracted cone. -/
def exceptional : Fin 3 → Fin 6 := ![1,2,4]

def refinementCoefficients : Fin 3 → Fin 4 → Fin 2 → ℕ :=
  ![![![0,1], ![1,1], ![2,1], ![5,2]],
    ![![3,1], ![2,1], ![1,1], ![1,2]],
    ![![5,3], ![3,2], ![1,1], ![0,1]]]

theorem refinement_certificate (i : Fin 3) (a : Fin 4) :
    coneExponent a = combination ![first (exceptional i), second (exceptional i)]
      (refinementCoefficients i a) := by
  fin_cases i <;> fin_cases a <;>
    norm_num [coneExponent, combination, refinementCoefficients, exceptional, first, second,
      Fin.sum_univ_succ, Prod.ext_iff]

theorem cone_le_exceptional (i : Fin 3) : coneRing ≤ chartRing (exceptional i) := by
  apply (coneRing_le_iff _).mpr
  intro a
  rw [refinement_certificate i a]
  apply combination_mem
  intro b
  fin_cases b
  · exact y₁_mem _
  · exact y₂_mem _

end
end Red61.Contraction

namespace Red61.ConeRing

set_option maxRecDepth 4096

open Fields LocalCoordinates
noncomputable section

/-- The actual invariant local ring at the contracted point. -/
def B : Subalgebra ell R := invariantAlgebra localD

instance : CommRing B := inferInstance
instance : IsLocalRing B := invariantAlgebra_local localD
instance : IsNoetherianRing B := invariantAlgebra_noetherian localD localD_five

def projection : R →ₗ[B] B := invariantRetraction localD localD_five

theorem projection_formula (x : R) :
    (projection x : R) = x - localD (localD (localD (localD x))) := rfl

theorem projection_one : projection 1 = 1 := invariantRetraction_one localD localD_five

theorem ideal_extension_contraction (I : Ideal B) :
    (I.map (algebraMap B R)).comap (algebraMap B R) = I :=
  ideal_map_comap_of_retraction projection projection_one I

def residueB : B →ₐ[ell] k := (localResidue.restrictScalars ell).comp B.val

theorem residue_projection (x : R) : residueB (projection x) = localResidue x := by
  change localResidue (projection x : R) = localResidue x
  rw [projection_formula, map_sub, localResidue_D, sub_zero]

theorem residueB_surjective : Function.Surjective residueB := by
  intro a
  obtain ⟨x, hx⟩ := localResidue_surjective a
  exact ⟨projection x, (residue_projection x).trans hx⟩

theorem maximal_eq_residue_kernel : IsLocalRing.maximalIdeal B = RingHom.ker residueB := by
  exact (IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective residueB residueB_surjective)).symm

theorem theta_kernel_in_L {x : K} (hx : theta x = 0) : x ∈ L := by
  change U * T * delta x = 0 at hx
  change delta x = 0
  exact (mul_eq_zero.mp hx).resolve_left
    (mul_ne_zero (inv_ne_zero (coord_nonzero 3)) (coord_nonzero 2))

/-- The invariant stalk embeds into the already constructed invariant function field. -/
def invariantEmbedding : B →+* L where
  toFun x := ⟨localEmbed x, theta_kernel_in_L (by
    rw [← localEmbed_D]
    rw [x.property, map_zero])⟩
  map_one' := by apply Subtype.ext; exact map_one localEmbed
  map_zero' := by apply Subtype.ext; exact map_zero localEmbed
  map_add' x y := by apply Subtype.ext; exact map_add localEmbed (x : R) (y : R)
  map_mul' x y := by apply Subtype.ext; exact map_mul localEmbed (x : R) (y : R)

theorem invariantEmbedding_injective : Function.Injective invariantEmbedding := by
  intro x y h
  apply Subtype.ext
  exact localEmbed_injective (congrArg (fun z : L => (z : K)) h)

def localGenerator (i : Fin 4) : R := algebraMap A R ⟨generator i, generator_mem i⟩

@[simp] theorem localGenerator_embedding (i : Fin 4) :
    localEmbed (localGenerator i) = ![U, U * T, U * T ^ 2, r] i := by
  rw [localGenerator, localEmbed_algebraMap]
  change evaluate (generator i) = _
  fin_cases i <;> simp [generator, r]

@[simp] theorem localGenerator_residue (i : Fin 4) : localResidue (localGenerator i) = 0 := by
  rw [localGenerator, localResidue_algebraMap, generator_residue_zero]

theorem parameter_invariance : localD (localGenerator 0) = 0 ∧ localD (localGenerator 3) = 0 := by
  constructor <;> apply localEmbed_injective <;> simp

def uB : B := ⟨localGenerator 0, parameter_invariance.1⟩
def rB : B := ⟨localGenerator 3, parameter_invariance.2⟩

theorem parameters_in_maximal : uB ∈ IsLocalRing.maximalIdeal B ∧
    rB ∈ IsLocalRing.maximalIdeal B := by
  rw [maximal_eq_residue_kernel]
  exact ⟨localGenerator_residue 0, localGenerator_residue 3⟩

theorem parameters_embedding : (invariantEmbedding uB : K) = u ∧
    (invariantEmbedding rB : K) = r := by
  exact ⟨localGenerator_embedding 0, localGenerator_embedding 3⟩

end
end Red61.ConeRing

namespace Red61.ConeRing

open Fields LocalCoordinates TruncatedCone
noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def ag (i : Fin 4) : A := ⟨generator i, generator_mem i⟩

@[simp] theorem embed_ag (i : Fin 4) :
    embedEll (ag i) = ![U, U*T, U*T^2, r] i := by
  change evaluate (generator i) = _
  fin_cases i <;> simp [generator, r]

theorem D_ag (i : Fin 4) : D (ag i) = ![0, ag 1, 2 * ag 2, 0] i := by
  have htwo : embedEll (2 : A) = 2 := map_ofNat embedEll 2
  apply embed_injective
  change embedEll (D (ag i)) = embedEll _
  rw [embed_D]
  fin_cases i <;> simp [embed_ag, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, htwo] ; ring

@[simp] theorem embed_coefficient (a : k) :
    embedEll (algebraMap k A a) = includeK a := by
  change evaluate (algebraMap k P a) = includeK a
  exact evaluate.commutes a

theorem D_coefficient (a : k) : D (algebraMap k A a) =
    ag 1 * algebraMap k A (coeffDeriv 0 a) + ag 2 * algebraMap k A (coeffDeriv 1 a) := by
  apply embed_injective
  change embedEll (D (algebraMap k A a)) = embedEll _
  have h₁ : embedEll (ag 1) = U*T := embed_ag 1
  have h₂ : embedEll (ag 2) = U*T^2 := embed_ag 2
  rw [embed_D, map_add, map_mul, map_mul, h₁, h₂, embed_coefficient,
    embed_coefficient, embed_coefficient]
  change U*T*delta (includeK a) =
    U*T*includeK (coeffDeriv 0 a) + U*T^2*includeK (coeffDeriv 1 a)
  rw [delta_on_k]
  change U*T*(includeK (coeffDeriv 0 a) + T*includeK (coeffDeriv 1 a)) = _
  ring

def parameterIdeal : Ideal A := Ideal.span ({ag 0, ag 3} : Set A)

theorem parameterIdeal_stable {a : A} (ha : a ∈ parameterIdeal) : D a ∈ parameterIdeal := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · simpa only [D_ag, Matrix.cons_val_zero] using parameterIdeal.zero_mem
    · have h : a = ag 3 := Set.mem_singleton_iff.mp ha
      rw [h, D_ag]
      exact parameterIdeal.zero_mem
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using parameterIdeal.add_mem ihx ihy
  | smul a x hx ih =>
    change D (a*x) ∈ parameterIdeal
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact parameterIdeal.add_mem (parameterIdeal.mul_mem_left a ih)
      (parameterIdeal.mul_mem_right (D a) hx)

abbrev Q := A ⧸ parameterIdeal
instance : CommRing Q := inferInstance
instance : Module ell Q := Algebra.toModule

theorem parameterIdeal_residue_zero {a : A} (ha : a ∈ parameterIdeal) : residue a = 0 := by
  have h : parameterIdeal ≤ RingHom.ker residue := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact generator_residue_zero 0
    · rw [Set.mem_singleton_iff.mp ha]
      exact generator_residue_zero 3
  exact h ha

def residueQ : Q →ₐ[k] k := Ideal.Quotient.liftₐ parameterIdeal residue
  (fun _ ha => parameterIdeal_residue_zero ha)

instance : Nontrivial Q := residueQ.toRingHom.domain_nontrivial
instance : CharP Q 5 := charP_of_injective_algebraMap (algebraMap k Q).injective 5

def qmap : A →ₐ[ell] Q := Ideal.Quotient.mkₐ ell parameterIdeal

theorem qmap_D_zero (a : A) (h : qmap a = 0) : qmap (D a) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (parameterIdeal_stable (Ideal.Quotient.eq_zero_iff_mem.mp h))

def DQ : Derivation ell Q Q := Derivation.liftOfSurjective
  (f := qmap) Ideal.Quotient.mk_surjective qmap_D_zero

@[simp] theorem DQ_qmap (a : A) : DQ (qmap a) = qmap (D a) :=
  Derivation.liftOfSurjective_apply (f := qmap) (d := D)
    Ideal.Quotient.mk_surjective qmap_D_zero a

def v : Q := qmap (ag 1)
def z : Q := qmap (ag 2)

@[simp] theorem qmap_u : qmap (ag 0) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

@[simp] theorem qmap_r : qmap (ag 3) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem ag_relations : ag 1 ^ 2 = ag 0 * ag 2 ∧
    ag 1 * ag 2 ^ 2 = ag 0 * ag 3 ∧ ag 2 ^ 3 = ag 1 * ag 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply embed_injective <;>
    change embedEll _ = embedEll _ <;> simp [embed_ag, r] <;> ring

theorem quotient_relations : v ^ 2 = 0 ∧ v*z^2 = 0 ∧ z^3 = 0 := by
  have h₁ := congrArg qmap ag_relations.1
  have h₂ := congrArg qmap ag_relations.2.1
  have h₃ := congrArg qmap ag_relations.2.2
  simpa [v, z] using And.intro h₁ (And.intro h₂ h₃)

@[simp] theorem DQ_v : DQ v = v := by simp [v, D_ag]
@[simp] theorem DQ_z : DQ z = 2*z := by
  have htwo : qmap (2 : A) = 2 := map_ofNat qmap 2
  simp [z, D_ag, htwo]

theorem DQ_coefficient (a : k) : DQ (algebraMap k Q a) =
    v * algebraMap k Q (coeffDeriv 0 a) + z * algebraMap k Q (coeffDeriv 1 a) := by
  change DQ (qmap (algebraMap k A a)) = _
  rw [DQ_qmap, D_coefficient, map_add, map_mul, map_mul]
  rfl

theorem quotient_generated : Algebra.adjoin k ({v,z} : Set Q) = ⊤ := by
  let S := Algebra.adjoin k ({v,z} : Set Q)
  let f := Ideal.Quotient.mkₐ k parameterIdeal
  have hA : Algebra.adjoin k (Set.range ag) = ⊤ := subtype_generators_top generator
  have hle : (⊤ : Subalgebra k A) ≤ S.comap f := by
    rw [← hA]
    apply Algebra.adjoin_le
    rintro a ⟨i,rfl⟩
    change qmap (ag i) ∈ S
    fin_cases i
    · change qmap (ag 0) ∈ S
      rw [qmap_u]
      exact S.zero_mem
    · exact Algebra.subset_adjoin (by simp [v])
    · exact Algebra.subset_adjoin (by simp [z])
    · change qmap (ag 3) ∈ S
      rw [qmap_r]
      exact S.zero_mem
  apply top_unique
  intro x hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hle (Set.mem_univ a)

theorem quotient_normalForm (x : Q) : NormalForm (algebraMap k Q) v z x := by
  apply normalForm_adjoin v z quotient_relations.1 quotient_relations.2.1 quotient_relations.2.2
  rw [quotient_generated]
  trivial

@[simp] theorem residueQ_qmap (a : A) : residueQ (qmap a) = residue a := rfl
@[simp] theorem residueQ_v : residueQ v = 0 := generator_residue_zero 1
@[simp] theorem residueQ_z : residueQ z = 0 := generator_residue_zero 2

theorem quotient_fourth_positive (a : k) :
    DQ (DQ (DQ (DQ (algebraMap k Q a * v)))) = algebraMap k Q a * v ∧
    DQ (DQ (DQ (DQ (algebraMap k Q a * z)))) = algebraMap k Q a * z ∧
    DQ (DQ (DQ (DQ (algebraMap k Q a * v * z)))) = algebraMap k Q a * v * z ∧
    DQ (DQ (DQ (DQ (algebraMap k Q a * z ^ 2)))) = algebraMap k Q a * z ^ 2 :=
  fourth_on_positive DQ (algebraMap k Q) v z (coeffDeriv 0) (coeffDeriv 1)
    DQ_coefficient DQ_v DQ_z quotient_relations.1 quotient_relations.2.1
      quotient_relations.2.2 a

/-- The finite filtration is separated on the quotient: an invariant with zero residue vanishes. -/
theorem quotient_invariant_zero (x : Q) (hx : DQ x = 0) (hres : residueQ x = 0) : x = 0 := by
  obtain ⟨a₀,a₁,a₂,a₃,a₄,he⟩ := quotient_normalForm x
  have h₀ : a₀ = 0 := by
    have h := congrArg residueQ he
    simpa only [hres, map_add, map_mul, map_pow, residueQ_v, residueQ_z,
      mul_zero, pow_succ, zero_mul, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using h.symm
  subst a₀
  simp only [map_zero, zero_add] at he
  have hf : DQ (DQ (DQ (DQ x))) = x := by
    rw [he]
    simp only [map_add, (quotient_fourth_positive a₁).1,
      (quotient_fourth_positive a₂).2.1, (quotient_fourth_positive a₃).2.2.1,
      (quotient_fourth_positive a₄).2.2.2]
  rw [hx, map_zero, map_zero, map_zero] at hf
  exact hf.symm

theorem invariant_polynomial_in_parameterIdeal (a : A) (ha : D a = 0) (hres : residue a = 0) :
    a ∈ parameterIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply quotient_invariant_zero (qmap a)
  · rw [DQ_qmap, ha, map_zero]
  · exact hres

end
end Red61.ConeRing

namespace Red61.ConeRing

open Fields
open scoped Pointwise
noncomputable section

abbrev Exponent := Fin 2 →₀ ℕ
def exponent (a b : ℕ) : Exponent := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem exponent_zero (a b : ℕ) : exponent a b 0 = a := by simp [exponent]
@[simp] theorem exponent_one (a b : ℕ) : exponent a b 1 = b := by simp [exponent]

theorem mon_eq_monomial (a b : ℕ) : mon a b = MvPolynomial.monomial (exponent a b) (1 : k) := by
  simp [mon, exponent, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial]

theorem support_of_mem_A {p : P} (hp : p ∈ A) :
    ∀ d ∈ p.support, 2 * d 1 ≤ 5 * d 0 := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    intro d hd
    fin_cases i <;>
      simp [generator, mon_eq_monomial] at hd <;>
      subst d <;> norm_num [exponent]
  | algebraMap a =>
    intro d hd
    have he : d = 0 := by
      by_cases ha : a = 0
      · simp [ha, MvPolynomial.algebraMap_eq] at hd
      · simpa [MvPolynomial.algebraMap_eq, MvPolynomial.support_C, ha] using hd
    subst d
    simp
  | add p q hp hq ihp ihq =>
    intro d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact ihp d h
    · exact ihq d h
  | mul p q hp hq ihp ihq =>
    intro d hd
    obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
    have h₁ := ihp e he
    have h₂ := ihq f hf
    simp only [Finsupp.add_apply]
    omega

theorem coefficient_outside_cone (p : A) (d : Exponent) (hd : 5 * d 0 < 2 * d 1) :
    (p : P).coeff d = 0 := by
  by_contra h
  have h' := support_of_mem_A p.property d (MvPolynomial.mem_support_iff.mpr h)
  omega

theorem mon_pow (a b n : ℕ) : mon a b ^ n = mon (a*n) (b*n) := by simp [mon, mul_pow, pow_mul]

theorem residue_eq_coefficient (p : A) : residue p = (p : P).coeff 0 := by
  simp [residue, augmentation, MvPolynomial.constantCoeff_eq]

/-- A denominator with nonzero residue cannot remove the pole along the second boundary ray. -/
theorem boundary_obstruction (a b : A) (hb : residue b ≠ 0) (n : ℕ) :
    mon 1 0 * (a : P) ≠ mon 2 5 ^ n * (b : P) := by
  intro h
  cases n with
  | zero =>
    have hh := congrArg augmentation h
    have hU : augmentation (mon 1 0) = 0 := augmentation_generator 0
    simp only [map_mul, hU, zero_mul, pow_zero, one_mul] at hh
    exact hb hh.symm
  | succ n =>
    have he : exponent (2*(n+1)) (5*(n+1)) =
        exponent 1 0 + exponent (2*(n+1)-1) (5*(n+1)) := by
      ext i
      fin_cases i <;> simp; omega
    have hl : (mon 1 0 * (a : P)).coeff (exponent (2*(n+1)) (5*(n+1))) = 0 := by
      rw [mon_eq_monomial, he, MvPolynomial.coeff_monomial_mul, one_mul]
      apply coefficient_outside_cone
      simp only [exponent_zero, exponent_one]
      omega
    have hr : (mon 2 5 ^ (n+1) * (b : P)).coeff (exponent (2*(n+1)) (5*(n+1))) =
        (b : P).coeff 0 := by
      rw [mon_pow, mon_eq_monomial]
      simpa only [add_zero, one_mul] using
        MvPolynomial.coeff_monomial_mul 0 (exponent (2*(n+1)) (5*(n+1))) (1 : k) (b : P)
    have hh := congrArg (fun p : P => p.coeff (exponent (2*(n+1)) (5*(n+1)))) h
    rw [hl, hr] at hh
    exact hb ((residue_eq_coefficient b).trans hh.symm)

end
end Red61.ConeRing

namespace Red61.ConeRing

open Fields LocalCoordinates
noncomputable section
set_option maxRecDepth 4096

theorem local_r_power_not_multiple_u (n : ℕ) (x : R) :
    (uB : R)*x ≠ (rB : R)^n := by
  intro h
  obtain ⟨⟨a,b⟩,rfl⟩ := IsLocalization.mk'_surjective maximal.primeCompl x
  have hh := congrArg localEmbed h
  have hu : localEmbed (uB : R) = U := localGenerator_embedding 0
  have hr : localEmbed (rB : R) = r := localGenerator_embedding 3
  rw [map_mul, map_pow, hu, hr, localEmbed_mk, ← mul_div_assoc] at hh
  have he := (div_eq_iff (isUnit_iff_ne_zero.mp (denominator_unit b))).mp hh
  change U * evaluate (a : P) = r ^ n * evaluate ((b : A) : P) at he
  have hp : mon 1 0 * (a : P) = mon 2 5 ^ n * (b : A) := by
    apply evaluate_injective
    rw [map_mul, map_mul, map_pow, evaluate_mon, evaluate_mon]
    simpa only [pow_one, pow_zero, mul_one, r] using he
  exact boundary_obstruction a b (isUnit_iff_ne_zero.mp (residue_denominator_unit b)) n hp

theorem rB_not_in_u_radical : rB ∉ (Ideal.span ({uB} : Set B)).radical := by
  rintro ⟨n, hn⟩
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hn
  apply local_r_power_not_multiple_u n (x : R)
  exact congrArg (fun a : B => (a : R)) hx.symm

instance : IsDomain B := Function.Injective.isDomain invariantEmbedding invariantEmbedding_injective

theorem uB_nonzero : uB ≠ 0 := by
  intro h
  have hh := congrArg (fun x : B => (invariantEmbedding x : K)) h
  rw [parameters_embedding.1] at hh
  exact (inv_ne_zero (coord_nonzero 3)) (by simpa [u, U, w] using hh)

theorem invariant_dimension_at_least_two : 2 ≤ ringKrullDim B :=
  two_le_dimension uB rB uB_nonzero parameters_in_maximal.2 rB_not_in_u_radical

end
end Red61.ConeRing

namespace Red61.ConeRing

open Fields LocalCoordinates
noncomputable section
set_option maxRecDepth 4096

def invariantParameterIdeal : Ideal B := Ideal.span ({uB, rB} : Set B)

theorem parameterIdeal_map :
    parameterIdeal.map (algebraMap A R) =
      invariantParameterIdeal.map (algebraMap B R) := by
  rw [parameterIdeal, invariantParameterIdeal, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem localD_fifth_power (x : R) : localD (x ^ 5) = 0 := by
  apply localEmbed_injective
  rw [localEmbed_D, map_pow, map_zero]
  simp only [Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]

theorem localization_injective : Function.Injective (algebraMap A R) := by
  intro a b h
  apply embed_injective
  change embedEll a = embedEll b
  have hh := congrArg localEmbed h
  simpa only [localEmbed_algebraMap] using hh

/-- Clearing a denominator by its fifth power preserves invariance. -/
theorem invariant_numerator (x : B) (a : A) (b : maximal.primeCompl)
    (h : (x : R) * algebraMap A R b = algebraMap A R a) :
    D (a * (b : A)^4) = 0 := by
  have he : algebraMap A R (a * (b : A)^4) = (x : R) * (algebraMap A R b)^5 := by
    rw [map_mul, map_pow, ← h]
    ring
  apply localization_injective
  rw [map_zero, ← localD_algebraMap, he, Derivation.leibniz]
  have hx : localD (x : R) = 0 := x.property
  simp only [localD_fifth_power, hx, smul_zero, zero_add]

/-- Actual finite lifting for the invariant local ring; no completion is used. -/
theorem maximalIdeal_eq_parameters :
    IsLocalRing.maximalIdeal B = invariantParameterIdeal := by
  apply le_antisymm
  · intro x hx
    have hres : localResidue (x : R) = 0 := by
      rw [maximal_eq_residue_kernel] at hx
      exact hx
    obtain ⟨⟨a,b⟩,h⟩ := IsLocalization.surj maximal.primeCompl (x : R)
    have he : algebraMap A R (a * (b : A)^4) = (x : R) * (algebraMap A R b)^5 := by
      rw [map_mul, map_pow, ← h]
      ring
    have hnres : residue (a * (b : A)^4) = 0 := by
      rw [← localResidue_algebraMap, he, map_mul, hres, zero_mul]
    have hn := invariant_polynomial_in_parameterIdeal _ (invariant_numerator x a b h) hnres
    have hmap : (x : R) * (algebraMap A R b)^5 ∈
        invariantParameterIdeal.map (algebraMap B R) := by
      rw [← he, ← parameterIdeal_map]
      exact Ideal.mem_map_of_mem _ hn
    have hxmap : (x : R) ∈ invariantParameterIdeal.map (algebraMap B R) := by
      apply (Submodule.smul_mem_iff_of_isUnit _
        ((IsLocalization.map_units R b).pow 5)).mp
      simpa only [smul_eq_mul, mul_comm] using hmap
    rw [← ideal_extension_contraction invariantParameterIdeal]
    exact hxmap
  · apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact parameters_in_maximal.1
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ parameters_in_maximal.2

theorem cotangent_generators_bound : (IsLocalRing.maximalIdeal B).spanFinrank ≤ 2 := by
  rw [maximalIdeal_eq_parameters, invariantParameterIdeal]
  have hb := Submodule.spanFinrank_span_le_ncard_of_finite (R := B)
    (Set.toFinite ({uB, rB} : Set B))
  have hc : Set.ncard ({uB, rB} : Set B) ≤ 2 := by simpa using Set.ncard_insert_le uB ({rB} : Set B)
  exact hb.trans hc

/-- The concrete invariant stalk at the contracted point is regular. -/
theorem invariant_local_ring_regular : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  exact (show ((IsLocalRing.maximalIdeal B).spanFinrank : WithBot ℕ∞) ≤ 2 by
    exact_mod_cast cotangent_generators_bound).trans invariant_dimension_at_least_two

theorem invariant_local_ring_dimension : ringKrullDim B = 2 := by
  apply le_antisymm _ invariant_dimension_at_least_two
  apply (ringKrullDim_le_spanFinrank_maximalIdeal B).trans
  exact_mod_cast cotangent_generators_bound

end
end Red61.ConeRing

namespace Red61.ConeRing

open Fields LocalCoordinates
noncomputable section
set_option maxRecDepth 4096

theorem cone_field_generation : IntermediateField.adjoin k (embed.range : Set K) = ⊤ := by
  let M := IntermediateField.adjoin k (embed.range : Set K)
  have hg (i : Fin 4) : evaluate (generator i) ∈ M :=
    IntermediateField.subset_adjoin k _ ⟨⟨generator i, generator_mem i⟩, rfl⟩
  have hU : U ∈ M := by simpa [generator] using hg 0
  have hUT : U * T ∈ M := by simpa [generator] using hg 1
  have hT : t ∈ M := by
    have h := M.div_mem hUT hU
    have he : U * T / U = T := by
      have hU : U ≠ 0 := inv_ne_zero (coord_nonzero 3)
      field_simp
    change T ∈ M
    rw [← he]
    exact h
  have hw : w ∈ M := by simpa [U] using M.inv_mem hU
  have hgen : IntermediateField.adjoin k ({t,w} : Set K) ≤ M := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hT
    · exact Set.mem_singleton_iff.mp hx ▸ hw
  rw [rational_generation] at hgen
  exact top_le_iff.mp hgen

/-- Every function in K is a quotient of elements of the concrete cone algebra. -/
theorem cone_fraction_representation (x : K) :
    ∃ a b : A, x = embed a / embed b := by
  have hx : x ∈ IntermediateField.adjoin k (embed.range : Set K) := by
    rw [cone_field_generation]
    trivial
  obtain ⟨a,ha,b,hb,he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  rw [Algebra.adjoin_eq] at ha hb
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  exact ⟨a,b,he⟩

@[instance_reducible] def invariantFieldAlgebra : Algebra B L := invariantEmbedding.toAlgebra

/-- Taking fifth powers of denominators identifies Frac(B) with the invariant field L. -/
theorem invariant_isFractionRing :
    letI := invariantFieldAlgebra
    IsFractionRing B L := by
  let := invariantFieldAlgebra
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr invariantEmbedding_injective
  apply IsFractionRing.of_field
  intro x
  by_cases hx : x = 0
  · exact ⟨0,1,by simp [hx]⟩
  obtain ⟨a,b,he⟩ := cone_fraction_representation (x : K)
  have hb : embed b ≠ 0 := by
    intro hb
    have hx' : (x : K) = 0 := by simpa [hb] using he
    exact hx (Subtype.ext hx')
  let aR : R := algebraMap A R a
  let bR : R := algebraMap A R b
  have har : localEmbed aR = embed a := localEmbed_algebraMap a
  have hbr : localEmbed bR = embed b := localEmbed_algebraMap b
  have hmul : (x : K) * localEmbed bR = localEmbed aR := by
    rw [har, hbr, he]
    exact div_mul_cancel₀ _ hb
  have htheta : theta (x : K) = 0 := by
    change U * T * delta (x : K) = 0
    rw [show delta (x : K) = 0 from x.property, mul_zero]
  have hnum : localD (aR * bR ^ 4) = 0 := by
    apply localEmbed_injective
    rw [localEmbed_D, map_zero, map_mul, map_pow, ← hmul]
    have hid : (x : K) * localEmbed bR * localEmbed bR ^ 4 =
        (x : K) * localEmbed bR ^ 5 := by ring
    rw [hid, Derivation.leibniz]
    simp only [htheta, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      CharP.cast_eq_zero K 5, zero_mul, mul_zero, add_zero]
  let aa : B := ⟨aR * bR ^ 4, hnum⟩
  let bb : B := ⟨bR ^ 5, localD_fifth_power bR⟩
  refine ⟨aa,bb,?_⟩
  apply Subtype.ext
  change (x : K) = localEmbed (aR * bR ^ 4) / localEmbed (bR ^ 5)
  rw [map_mul, map_pow, map_pow, ← hmul]
  have hb' : localEmbed bR ≠ 0 := hbr ▸ hb
  field_simp

end
end Red61.ConeRing

/-! Stalk and function-field identifications for the concrete local invariant ring. -/

namespace Red61.ConeRing

open Fields CategoryTheory AlgebraicGeometry
noncomputable section

def coneSpec : Scheme := Spec (CommRingCat.of A)

def vertex : PrimeSpectrum A := ⟨maximal, inferInstance⟩

end
end Red61.ConeRing

import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Red61.Canonical.InvariantCoordinates
import Red61.RingTheory.PolynomialModels
import Red61.Surface.SpecialPointStalk

/-! # Differential bases on the retained charts, at the special point and at the exceptional divisors

Formerly the modules `KeptDifferentialBases`, `KeptKernelCoordinates`, `KeptRationalCoordinates`, `LocalInvariantPolynomialCoordinates`, `LocalInvariantPolynomialLocalization`, `InvariantPolynomialModels`, `MonomialDiscrepancyInputs`, `SpecialPointCoefficientSection`, `LocalDifferentialIndependence`, `SpecialPointDifferentialBasis`, `ExceptionalPulledDifferentialBasis`, `ExceptionalTargetDifferentialBases`, `StalkCoordinateMatrices`.
-/

/-! Absolute differential bases at every prime of the three invariant
charts retained by the contraction. The middle chart uses its proved
principal-open cover; all polynomial-localization hypotheses are checked. -/

namespace Red61.Charts

open Fields PolynomialInvariants FieldLocalization AffineGluing Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

def firstKernelPrimeDifferentialBasis :
    Basis (Fin 4) (kernelIn (localGenerator 0) firstRing)
      (KaehlerDifferential F₅ (kernelIn (localGenerator 0) firstRing)) :=
  polynomialKernelDifferentialBasis (localGenerator 0) straightFirst first_independent
    first_derivatives firstRing first_polynomial_le first_localization

def firstKernelAbsoluteDifferentialBasis :
    Basis (Fin 4) (kernelIn (localGenerator 0) firstRing)
      (KaehlerDifferential ℤ (kernelIn (localGenerator 0) firstRing)) :=
  firstKernelPrimeDifferentialBasis.map
    (quotientBaseDifferentialEquiv ℤ F₅ (kernelIn (localGenerator 0) firstRing)
      ZMod.intCast_surjective).symm

def lastKernelPrimeDifferentialBasis :
    Basis (Fin 4) (kernelIn (localGenerator 5) lastRing)
      (KaehlerDifferential F₅ (kernelIn (localGenerator 5) lastRing)) :=
  polynomialKernelDifferentialBasis (localGenerator 5) straightLast last_independent
    last_derivatives lastRing last_polynomial_le last_localization

def lastKernelAbsoluteDifferentialBasis :
    Basis (Fin 4) (kernelIn (localGenerator 5) lastRing)
      (KaehlerDifferential ℤ (kernelIn (localGenerator 5) lastRing)) :=
  lastKernelPrimeDifferentialBasis.map
    (quotientBaseDifferentialEquiv ℤ F₅ (kernelIn (localGenerator 5) lastRing)
      ZMod.intCast_surjective).symm

def middleOpenKernelPrimeDifferentialBasis (a : F₅) :
    Basis (Fin 4) (kernelIn (localGenerator 3) (middleRing a))
      (KaehlerDifferential F₅ (kernelIn (localGenerator 3) (middleRing a))) :=
  polynomialKernelDifferentialBasis (localGenerator 3) (straightMiddle a) (middle_independent a)
    (middle_derivatives a) (middleRing a) (middle_polynomial_le a) (middle_localization a)

def middleOpenKernelAbsoluteDifferentialBasis (a : F₅) :
    Basis (Fin 4) (kernelIn (localGenerator 3) (middleRing a))
      (KaehlerDifferential ℤ (kernelIn (localGenerator 3) (middleRing a))) :=
  (middleOpenKernelPrimeDifferentialBasis a).map
    (quotientBaseDifferentialEquiv ℤ F₅ (kernelIn (localGenerator 3) (middleRing a))
      ZMod.intCast_surjective).symm

theorem middleKernelAtPrimeDifferentialBasis (p : PrimeSpectrum middleKernel) :
    Nonempty (Basis (Fin 4) (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) := by
  obtain ⟨a, ha⟩ := middle_kernel_cover p
  let := inclusionAlgebra
    (show middleKernel ≤ kernelIn (localGenerator 3) (middleRing a) from
      inf_le_inf_right _ le_sup_left)
  have := middle_kernel_localization a
  exact absoluteDifferentialBasisAtPrime_of_away
    (A := middleKernel) (B := kernelIn (localGenerator 3) (middleRing a))
    (middleKernelDenominator a) p ha (middleOpenKernelAbsoluteDifferentialBasis a)

theorem keptKernelAtPrimeDifferentialBasis (i : Fin 3)
    (p : PrimeSpectrum (kernelIn (localGenerator (Contraction.kept i))
      ((chartRing (Contraction.kept i)).restrictScalars F₅))) :
    Nonempty (Basis (Fin 4) (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) := by
  fin_cases i
  · exact ⟨absoluteDifferentialBasisAtPrime _ (Fin 4) p firstKernelAbsoluteDifferentialBasis⟩
  · exact middleKernelAtPrimeDifferentialBasis p
  · exact ⟨absoluteDifferentialBasisAtPrime _ (Fin 4) p lastKernelAbsoluteDifferentialBasis⟩

theorem keptInvariantAtPrimeDifferentialBasis (i : Fin 3)
    (p : PrimeSpectrum (invariantChartRing (Contraction.kept i))) :
    Nonempty (Basis (Fin 4) (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) := by
  obtain ⟨b⟩ := keptKernelAtPrimeDifferentialBasis i
    (PrimeSpectrum.comap (chartKernelInEquiv (Contraction.kept i)).toRingHom p)
  exact ⟨absoluteDifferentialBasisAtPrimeOfRingEquiv
    (chartKernelInEquiv (Contraction.kept i)) p b⟩

end
end Red61.Charts

/-! The differential bases of the retained invariant kernels are the
differentials of their explicit straightened coordinates. First and last
chart coordinates are also transferred to the actual invariant chart rings. -/

namespace Red61.Charts

open Fields PolynomialInvariants Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

def keptFirstKernelCoordinates : Fin 4 → kernelIn (localGenerator 0) firstRing :=
  powerKernelCoordinate (localGenerator 0) straightFirst first_independent first_derivatives
    firstRing first_polynomial_le

theorem keptFirstKernelCoordinates_coe (i : Fin 4) :
    (keptFirstKernelCoordinates i : K) = powerCoordinates straightFirst i := rfl

theorem firstKernelAbsoluteDifferentialBasis_apply (i : Fin 4) :
    firstKernelAbsoluteDifferentialBasis i =
      KaehlerDifferential.D ℤ (kernelIn (localGenerator 0) firstRing)
        (keptFirstKernelCoordinates i) := by
  simp [firstKernelAbsoluteDifferentialBasis, firstKernelPrimeDifferentialBasis,
    keptFirstKernelCoordinates, polynomialKernelDifferentialBasis_apply]

def keptLastKernelCoordinates : Fin 4 → kernelIn (localGenerator 5) lastRing :=
  powerKernelCoordinate (localGenerator 5) straightLast last_independent last_derivatives
    lastRing last_polynomial_le

theorem keptLastKernelCoordinates_coe (i : Fin 4) :
    (keptLastKernelCoordinates i : K) = powerCoordinates straightLast i := rfl

theorem lastKernelAbsoluteDifferentialBasis_apply (i : Fin 4) :
    lastKernelAbsoluteDifferentialBasis i =
      KaehlerDifferential.D ℤ (kernelIn (localGenerator 5) lastRing)
        (keptLastKernelCoordinates i) := by
  simp [lastKernelAbsoluteDifferentialBasis, lastKernelPrimeDifferentialBasis,
    keptLastKernelCoordinates, polynomialKernelDifferentialBasis_apply]

def keptMiddleOpenCoordinates (a : F₅) : Fin 4 → kernelIn (localGenerator 3) (middleRing a) :=
  powerKernelCoordinate (localGenerator 3) (straightMiddle a) (middle_independent a)
    (middle_derivatives a) (middleRing a) (middle_polynomial_le a)

theorem keptMiddleOpenCoordinates_coe (a : F₅) (i : Fin 4) :
    (keptMiddleOpenCoordinates a i : K) = powerCoordinates (straightMiddle a) i := rfl

theorem middleOpenKernelAbsoluteDifferentialBasis_apply (a : F₅) (i : Fin 4) :
    middleOpenKernelAbsoluteDifferentialBasis a i =
      KaehlerDifferential.D ℤ (kernelIn (localGenerator 3) (middleRing a))
        (keptMiddleOpenCoordinates a i) := by
  simp [middleOpenKernelAbsoluteDifferentialBasis, middleOpenKernelPrimeDifferentialBasis,
    keptMiddleOpenCoordinates, polynomialKernelDifferentialBasis_apply]

end
end Red61.Charts

/-! The fixed invariant coordinates q1,q2,u,r expressed in the rational
coordinates of the retained charts. These identities are in the fixed
ambient field and retain every inverse explicitly. -/

namespace Red61

noncomputable section

variable {F : Type*} [Field F] [CharP F 5]

theorem firstStraightInvariantCoordinates (a b t w : F) (hw : w ≠ 0) (i : Fin 4) :
    ![a - w⁻¹ * t, b - 3 * w⁻¹ * t ^ 2, w⁻¹, (w⁻¹) ^ 2 * t ^ 5] i =
      ![-(t - a * w) * w⁻¹,
        (b - a * t + 3 * a ^ 2 * w) - 3 * (t - a * w) ^ 2 * w⁻¹,
        w⁻¹, a ^ 5 * w ^ 3 + (t - a * w) ^ 5 * (w⁻¹) ^ 2] i := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  fin_cases i
  · dsimp; field_simp; ring
  · dsimp; field_simp; linear_combination -(a * t * w) * h5
  · rfl
  · dsimp
    rw [sub_pow_char (p := 5), mul_pow]
    field_simp
    ring

theorem lastStraightInvariantCoordinates (a b x y : F) (i : Fin 4) :
    ![b - x ^ 3 * y, a - 3 * x, x ^ 5 * y ^ 2, y⁻¹] i =
      ![(b - a * x ^ 2 * y + 2 * a ^ 2 * x * y + 2 * a ^ 3 * y) - (x - 2 * a) ^ 3 * y,
        2 * (x - 2 * a), ((x - 2 * a) ^ 5 + 2 * a ^ 5) * y ^ 2, y⁻¹] i := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  have h2 : (2 : F) ^ 5 = 2 := by linear_combination 6 * h5
  fin_cases i
  · dsimp
    linear_combination (-a * x ^ 2 * y + 2 * a ^ 2 * x * y - 2 * a ^ 3 * y) * h5
  · dsimp; linear_combination (a - x) * h5
  · dsimp
    rw [sub_pow_char (p := 5), mul_pow, h2]
    ring
  · rfl

theorem middleStraightInvariantCoordinates (a h b x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hH : 1 + 3 * h * y ≠ 0) (i : Fin 4) :
    let H := 1 + 3 * h * y
    let v : Fin 4 → F :=
      ![h, b - h * x + 2 * h ^ 2 * x * y + 2 * h ^ 3 * x * y ^ 2, x * H ^ 2, y / H]
    ![b - x / y, h + a - 3 / y, x ^ 2 / y, (x * y ^ 2)⁻¹] i =
      ![v 1 - v 2 * (v 3)⁻¹, a - 3 * (v 3)⁻¹,
        v 2 ^ 2 * ((v 3)⁻¹ - 3 * v 0 ^ 5 * v 3 ^ 4), (v 2)⁻¹ * ((v 3)⁻¹) ^ 2] i := by
  let H := 1 + 3 * h * y
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  have h3 : (3 : F) ^ 5 = 3 := by linear_combination 48 * h5
  have hH3 : H ^ 3 = 1 - h * y + 2 * h ^ 2 * y ^ 2 + 2 * h ^ 3 * y ^ 3 := by
    dsimp [H]
    linear_combination (2 * h * y + 5 * h ^ 2 * y ^ 2 + 5 * h ^ 3 * y ^ 3) * h5
  have hH5 : H ^ 5 = 1 + 3 * h ^ 5 * y ^ 5 := by
    dsimp [H]
    rw [add_pow_char (p := 5), one_pow, mul_pow, mul_pow, h3]
  have hz : (y / H)⁻¹ = H / y := inv_div _ _
  change ![b - x / y, h + a - 3 / y, x ^ 2 / y, (x * y ^ 2)⁻¹] i =
    ![(b - h * x + 2 * h ^ 2 * x * y + 2 * h ^ 3 * x * y ^ 2) - x * H ^ 2 * (y / H)⁻¹,
      a - 3 * (y / H)⁻¹,
      (x * H ^ 2) ^ 2 * ((y / H)⁻¹ - 3 * h ^ 5 * (y / H) ^ 4),
      (x * H ^ 2)⁻¹ * ((y / H)⁻¹) ^ 2] i
  fin_cases i
  · change b - x / y =
      (b - h * x + 2 * h ^ 2 * x * y + 2 * h ^ 3 * x * y ^ 2) - x * H ^ 2 * (y / H)⁻¹
    rw [hz]
    have he : x * H ^ 2 * (H / y) = x * H ^ 3 / y := by ring
    rw [he, hH3]
    field_simp
    ring
  · change h + a - 3 / y = a - 3 * (y / H)⁻¹
    rw [hz]
    dsimp [H]
    field_simp
    linear_combination 2 * h * y * h5
  · change x ^ 2 / y = (x * H ^ 2) ^ 2 * ((y / H)⁻¹ - 3 * h ^ 5 * (y / H) ^ 4)
    rw [hz]
    have he : (x * H ^ 2) ^ 2 * (H / y - 3 * h ^ 5 * (y / H) ^ 4) =
        x ^ 2 * (H ^ 5 - 3 * h ^ 5 * y ^ 5) / y := by
      field_simp [show H ≠ 0 from hH]
    rw [he, hH5]
    ring
  · change (x * y ^ 2)⁻¹ = (x * H ^ 2)⁻¹ * ((y / H)⁻¹) ^ 2
    rw [hz]
    field_simp [show H ≠ 0 from hH]

end
end Red61

namespace Red61.Charts

open Fields LocalCoordinates PolynomialInvariants
noncomputable section

theorem keptFirst_invariant_coordinates (i : Fin 4) :
    ![q₁, q₂, u, r] i =
      ![-straightFirst 2 * (straightFirst 3)⁻¹,
        straightFirst 1 - 3 * straightFirst 2 ^ 2 * (straightFirst 3)⁻¹,
        (straightFirst 3)⁻¹,
        straightFirst 0 ^ 5 * straightFirst 3 ^ 3 +
          straightFirst 2 ^ 5 * ((straightFirst 3)⁻¹) ^ 2] i := by
  simpa [straightFirst, q₁, q₂, u, r, U, T] using
    firstStraightInvariantCoordinates c₁ c₂ t w (coord_nonzero 3) i

theorem invariant_parameters_last_chart :
    u = (y₁ 5) ^ 5 * (y₂ 5) ^ 2 ∧ r = (y₂ 5)⁻¹ ∧
      q₁ = c₁ - (y₁ 5) ^ 3 * y₂ 5 ∧ q₂ = c₂ - 3 * y₁ 5 := by
  have ht : t ≠ 0 := coord_nonzero 2
  have hw : w ≠ 0 := coord_nonzero 3
  dsimp [u, r, q₁, q₂, U, T, y₁, y₂, first, second, monomial]
  norm_num only [zpow_neg, zpow_ofNat, zpow_one]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor <;> field_simp

theorem keptLast_invariant_coordinates (i : Fin 4) :
    ![q₁, q₂, u, r] i =
      ![straightLast 1 - straightLast 2 ^ 3 * straightLast 3,
        2 * straightLast 2,
        (straightLast 2 ^ 5 + 2 * straightLast 0 ^ 5) * straightLast 3 ^ 2,
        (straightLast 3)⁻¹] i := by
  have he := lastStraightInvariantCoordinates c₂ c₁ (y₁ 5) (y₂ 5) i
  simpa [straightLast, invariant_parameters_last_chart.1,
    invariant_parameters_last_chart.2.1, invariant_parameters_last_chart.2.2.1,
    invariant_parameters_last_chart.2.2.2] using he

theorem invariant_parameters_middle_chart :
    u = (y₁ 3) ^ 2 / y₂ 3 ∧ r = (y₁ 3 * (y₂ 3) ^ 2)⁻¹ ∧
      q₁ = c₁ - y₁ 3 / y₂ 3 ∧ q₂ = c₂ - 3 / y₂ 3 := by
  have ht : t ≠ 0 := coord_nonzero 2
  have hw : w ≠ 0 := coord_nonzero 3
  dsimp [u, r, q₁, q₂, U, T, y₁, y₂, first, second, monomial]
  norm_num only [zpow_neg, zpow_ofNat, zpow_one]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor <;> field_simp

theorem keptMiddle_invariant_coordinates (a : F₅) (i : Fin 4) :
    ![q₁, q₂, u, r] i =
      ![straightMiddle a 1 - straightMiddle a 2 * (straightMiddle a 3)⁻¹,
        algebraMap F₅ K a - 3 * (straightMiddle a 3)⁻¹,
        straightMiddle a 2 ^ 2 * ((straightMiddle a 3)⁻¹ -
          3 * straightMiddle a 0 ^ 5 * straightMiddle a 3 ^ 4),
        (straightMiddle a 2)⁻¹ * ((straightMiddle a 3)⁻¹) ^ 2] i := by
  have he := middleStraightInvariantCoordinates (algebraMap F₅ K a) (middleSlice a) c₁
    (y₁ 3) (y₂ 3) (monomial_nonzero (first 3)) (monomial_nonzero (second 3))
      (middle_denominator_nonzero a) i
  simpa [straightMiddle, middleSlice, middleDenominator, invariant_parameters_middle_chart.1,
    invariant_parameters_middle_chart.2.1, invariant_parameters_middle_chart.2.2.1,
    invariant_parameters_middle_chart.2.2.2] using he

end
end Red61.Charts

/-! Polynomial coordinates inside the actual special invariant local ring.
The original scalar field and the shifted residue section are kept distinct.
Fifth powers from the original cone local ring are mapped into the invariant
function field by an explicit ring homomorphism. -/

namespace Red61.ConeRing

open Fields LocalCoordinates PolynomialInvariants FieldLocalization
noncomputable section

private local instance : Algebra F₅ B := ZMod.algebra B 5

def invariantPrimeEmbedding : B →ₐ[F₅] L where
  __ := invariantEmbedding
  commutes' a := RingHom.congr_fun (Subsingleton.elim
    (invariantEmbedding.comp (algebraMap F₅ B)) (algebraMap F₅ L)) a

def invariantLocalImage : Subalgebra F₅ L := invariantPrimeEmbedding.range

def invariantCoordinatePolynomial : Subalgebra F₅ L :=
  polynomialRing invariantCoordinates

theorem invariantPolynomial_le_localImage :
    invariantCoordinatePolynomial ≤ invariantLocalImage := by
  apply Algebra.adjoin_le
  rintro x ⟨i, rfl⟩
  exact ⟨invariantCoordinatesB i, rfl⟩

def invariantCoordinateHull : Subalgebra F₅ L :=
  hull invariantCoordinatePolynomial invariantLocalImage

theorem invariantCoordinate_mem_hull (i : Fin 4) :
    invariantCoordinates i ∈ invariantCoordinateHull :=
  le_hull _ _ (Algebra.subset_adjoin (Set.mem_range_self i))

def localFrobeniusToInvariant : R →+* B :=
  (frobenius R 5).codRestrict B.toSubring localD_fifth_power

def localFrobeniusInField : R →+* L :=
  invariantEmbedding.comp localFrobeniusToInvariant

@[simp] theorem localFrobeniusInField_coe (a : R) :
    (localFrobeniusInField a : K) = localEmbed a ^ 5 := by
  unfold localFrobeniusInField localFrobeniusToInvariant
  exact map_pow localEmbed a 5

theorem localFrobenius_generator_hull (i : Fin 4) :
    localFrobeniusInField (localGenerator i) ∈ invariantCoordinateHull := by
  have he : localFrobeniusInField (localGenerator i) =
      ![invariantCoordinates 2 ^ 5,
        invariantCoordinates 2 ^ 3 * invariantCoordinates 3,
        invariantCoordinates 2 * invariantCoordinates 3 ^ 2,
        invariantCoordinates 3 ^ 5] i := by
    apply Subtype.ext
    simp only [localFrobeniusInField_coe, localGenerator_embedding]
    fin_cases i <;> simp [invariantCoordinates_coe, u, r] <;> ring
  rw [he]
  have h := invariantCoordinate_mem_hull
  fin_cases i
  · exact invariantCoordinateHull.pow_mem (h 2) 5
  · exact invariantCoordinateHull.mul_mem (invariantCoordinateHull.pow_mem (h 2) 3) (h 3)
  · exact invariantCoordinateHull.mul_mem (h 2) (invariantCoordinateHull.pow_mem (h 3) 2)
  · exact invariantCoordinateHull.pow_mem (h 3) 5

def invariantScalarFrobenius : k →+* L :=
  (algebraMap ell L).comp baseEquiv.toRingHom

@[simp] theorem invariantScalarFrobenius_coe (a : k) :
    (invariantScalarFrobenius a : K) = includeK (a ^ 5) := rfl

theorem localFrobenius_coefficient (a : k) :
    localFrobeniusInField (algebraMap k R a) = invariantScalarFrobenius a := by
  apply Subtype.ext
  rw [localFrobeniusInField_coe, localEmbed_coefficient, invariantScalarFrobenius_coe]
  exact (map_pow includeK a 5).symm

theorem scalarFrobenius_variable_hull (i : Fin 2) :
    invariantScalarFrobenius (c i) ∈ invariantCoordinateHull := by
  have he : invariantScalarFrobenius (c i) =
      ![invariantCoordinates 0 ^ 5 + invariantCoordinates 2 ^ 3 * invariantCoordinates 3,
        invariantCoordinates 1 ^ 5 + 3 * invariantCoordinates 2 * invariantCoordinates 3 ^ 2]
        i := by
    apply Subtype.ext
    rw [invariantScalarFrobenius_coe, map_pow]
    have h3 : ((3 : L) : K) = 3 := map_ofNat L.subtype 3
    fin_cases i <;>
      simp [includeK_c, invariantCoordinates_coe, q₁_fifth, q₂_fifth, h3]
  rw [he]
  have h := invariantCoordinate_mem_hull
  fin_cases i
  · exact invariantCoordinateHull.add_mem (invariantCoordinateHull.pow_mem (h 0) 5)
      (invariantCoordinateHull.mul_mem (invariantCoordinateHull.pow_mem (h 2) 3) (h 3))
  · exact invariantCoordinateHull.add_mem (invariantCoordinateHull.pow_mem (h 1) 5)
      (invariantCoordinateHull.mul_mem
        (invariantCoordinateHull.mul_mem (invariantCoordinateHull.natCast_mem 3) (h 2))
        (invariantCoordinateHull.pow_mem (h 3) 2))

theorem scalarFrobenius_polynomial_hull (p : P₂) :
    invariantScalarFrobenius (algebraMap P₂ k p) ∈ invariantCoordinateHull := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    change invariantScalarFrobenius
      (algebraMap P₂ k (algebraMap F₅ P₂ a)) ∈ invariantCoordinateHull
    rw [← IsScalarTower.algebraMap_apply F₅ P₂ k]
    have he : invariantScalarFrobenius.comp (algebraMap F₅ k) = algebraMap F₅ L :=
      Subsingleton.elim _ _
    rw [show invariantScalarFrobenius (algebraMap F₅ k a) = algebraMap F₅ L a from
      RingHom.congr_fun he a]
    exact invariantCoordinateHull.algebraMap_mem a
  | add p q hp hq =>
    simpa only [map_add] using invariantCoordinateHull.add_mem hp hq
  | mul_X p i hp =>
    simp only [map_mul]
    exact invariantCoordinateHull.mul_mem hp (scalarFrobenius_variable_hull i)

theorem scalarFrobenius_mem_hull (a : k) :
    invariantScalarFrobenius a ∈ invariantCoordinateHull := by
  apply fractionMap_mem_hull invariantPolynomial_le_localImage invariantScalarFrobenius
    scalarFrobenius_polynomial_hull
  intro x
  refine ⟨algebraMap ell B (baseEquiv x), ?_⟩
  apply Subtype.ext
  exact invariantEmbedding_scalar (baseEquiv x)

end
end Red61.ConeRing

/-! The special invariant local ring is a localization of the polynomial
ring in its four invariant coordinates over the prime field. Fifth powers
of elements lie in the localization hull; integral closedness in the fixed
function field then gives the elements themselves. -/

namespace Red61.ConeRing

open Fields LocalCoordinates PolynomialInvariants FieldLocalization AffineGluing
noncomputable section

private local instance : Algebra F₅ B := ZMod.algebra B 5

theorem invariantPolynomial_isIntegrallyClosed : IsIntegrallyClosed invariantCoordinatePolynomial :=
  IsIntegrallyClosed.of_equiv invariantCoordinates_independent.aevalEquiv.toRingEquiv

theorem invariantPolynomial_fractionField : IsFractionRing invariantCoordinatePolynomial L := by
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ IntermediateField.adjoin F₅ (Set.range invariantCoordinates) := by
    rw [invariantCoordinates_field_generation]
    trivial
  obtain ⟨a, ha, b, hb, he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he⟩

theorem coneFrobenius_mem_hull (a : A) :
    localFrobeniusInField (algebraMap A R a) ∈ invariantCoordinateHull := by
  let f := localFrobeniusInField.comp (algebraMap A R)
  let T : Subalgebra k A :=
    { carrier := {x | f x ∈ invariantCoordinateHull}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change f (x + y) ∈ invariantCoordinateHull
        rw [map_add]
        exact invariantCoordinateHull.add_mem hx hy
      mul_mem' := by
        intro x y hx hy
        change f (x * y) ∈ invariantCoordinateHull
        rw [map_mul]
        exact invariantCoordinateHull.mul_mem hx hy
      algebraMap_mem' := fun a ↦ by
        change f (algebraMap k A a) ∈ invariantCoordinateHull
        dsimp only [f, RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply k A R, localFrobenius_coefficient]
        exact scalarFrobenius_mem_hull a }
  have hgen : Algebra.adjoin k (Set.range ag) ≤ T := by
    apply Algebra.adjoin_le
    rintro x ⟨i, rfl⟩
    exact localFrobenius_generator_hull i
  rw [show Algebra.adjoin k (Set.range ag) = ⊤ from
    TruncatedCone.subtype_generators_top generator] at hgen
  exact hgen (Set.mem_univ a)

theorem localFrobenius_mem_hull (x : R) : localFrobeniusInField x ∈ invariantCoordinateHull :=
  localizationMap_mem_hull maximal.primeCompl invariantPolynomial_le_localImage
    localFrobeniusInField coneFrobenius_mem_hull (fun z ↦ ⟨localFrobeniusToInvariant z, rfl⟩) x

theorem invariantLocalImage_le_hull :
    invariantLocalImage ≤ hull invariantCoordinatePolynomial invariantLocalImage := by
  have := invariantPolynomial_isIntegrallyClosed
  have := invariantPolynomial_fractionField
  rintro x ⟨b, rfl⟩
  apply mem_hull_of_pow_mem invariantCoordinatePolynomial invariantLocalImage (n := 5) (by decide)
  have he : localFrobeniusInField (b : R) = invariantPrimeEmbedding.toRingHom b ^ 5 := by
    unfold localFrobeniusInField localFrobeniusToInvariant invariantPrimeEmbedding
    exact map_pow invariantEmbedding b 5
  rw [← he]
  exact localFrobenius_mem_hull b

theorem invariantLocalImage_isLocalization :
    letI := inclusionAlgebra invariantPolynomial_le_localImage
    IsLocalization (denominators invariantPolynomial_le_localImage) invariantLocalImage :=
  FieldLocalization.isLocalization invariantPolynomial_le_localImage invariantLocalImage_le_hull

theorem invariantLocalImage_formallySmooth : Algebra.FormallySmooth F₅ invariantLocalImage := by
  let := inclusionAlgebra invariantPolynomial_le_localImage
  have : IsScalarTower F₅ invariantCoordinatePolynomial invariantLocalImage :=
    IsScalarTower.of_algHom (Subalgebra.inclusion invariantPolynomial_le_localImage)
  have := invariantLocalImage_isLocalization
  have : Algebra.FormallySmooth F₅ invariantCoordinatePolynomial :=
    Algebra.FormallySmooth.of_equiv invariantCoordinates_independent.aevalEquiv
  have : Algebra.FormallySmooth invariantCoordinatePolynomial invariantLocalImage :=
    Algebra.FormallySmooth.of_isLocalization (denominators invariantPolynomial_le_localImage)
  exact Algebra.FormallySmooth.comp F₅ invariantCoordinatePolynomial invariantLocalImage

def invariantLocalImageEquiv : B ≃+* invariantLocalImage :=
  (AlgEquiv.ofInjective invariantPrimeEmbedding invariantEmbedding_injective).toRingEquiv

@[instance_reducible]
def invariantCoordinateAlgebraOnLocal : Algebra invariantCoordinatePolynomial B :=
  (invariantLocalImageEquiv.symm.toRingHom.comp
    (Subalgebra.inclusion invariantPolynomial_le_localImage).toRingHom).toAlgebra

theorem invariantLocal_formallySmooth [Algebra F₅ B] : Algebra.FormallySmooth F₅ B := by
  have := invariantLocalImage_formallySmooth
  exact formallySmooth_of_ringEquiv F₅ invariantLocalImageEquiv.symm (Subsingleton.elim _ _)

end
end Red61.ConeRing

/-! Explicit polynomial-localization models for straightened
invariant kernels and the special invariant local ring. -/

namespace Red61.PolynomialInvariants
open FieldLocalization
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP F 5] [CharP K 5]
def polynomialKernelLocalizationModel (D : Derivation F K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (A : Subalgebra F K) (hle : polynomialRing v ≤ A)
    (hloc : A ≤ hull (polynomialRing v) A) :
    PolynomialLocalizationModel F (kernelIn D A) (Fin 4) :=
  PolynomialLocalizationModel.ofSubalgebra (polynomialRing (F := F) (powerCoordinates v))
    (kernelIn D A) (powerPolynomial_le_kernel D v hi hv A hle)
    (kernel_le_hull D v hi hv A hloc) (powerCoordinates_independent hi).aevalEquiv
end
end Red61.PolynomialInvariants
namespace Red61.ConeRing
open Fields PolynomialInvariants
noncomputable section
private local instance : Algebra F₅ B := ZMod.algebra B 5

def invariantLocalPolynomialModel : PolynomialLocalizationModel F₅ B (Fin 4) := by
  let P := PolynomialLocalizationModel.ofSubalgebra invariantCoordinatePolynomial
    invariantLocalImage invariantPolynomial_le_localImage invariantLocalImage_le_hull
    invariantCoordinates_independent.aevalEquiv
  exact P.transportRingEquiv invariantLocalImageEquiv.symm (Subsingleton.elim _ _)
end
end Red61.ConeRing

/-! A general, explicitly quantified input for monomial Jacobian orders.
No field or scheme from the particular example occurs in the interface.
The input computes an actual module length, rather than assigning a name to
an arbitrary cycle. It is not proved or instantiated in this project.

The separate identification of this Jacobian divisor with the difference of
compatible dualizing canonical divisors is not supplied by this interface. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace Order IsLocalRing WeightedFiltration
noncomputable section

/-- A proper birational modification of normal integral surfaces over a field,
with regular target. Regularity means regular local rings, not smoothness. -/
structure IsRegularSurfaceModification (F : Type) [Field F]
    {Y X : Scheme} [IsIntegral Y] [IsIntegral X]
    (f : Y ⟶ X) (yToBase : Y ⟶ Spec (CommRingCat.of F))
    (xToBase : X ⟶ Spec (CommRingCat.of F)) : Prop where
  source_noetherian : IsNoetherian Y
  target_noetherian : IsNoetherian X
  source_finiteType : LocallyOfFiniteType yToBase
  target_finiteType : LocallyOfFiniteType xToBase
  over_base : f ≫ xToBase = yToBase
  proper : IsProper f
  source_dimension : topologicalKrullDim Y = 2
  target_dimension : topologicalKrullDim X = 2
  source_normal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)
  target_regular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  generic : f (genericPoint Y) = genericPoint X
  birational : Function.Bijective (genericFieldMap f generic)

/-- Full monomial ideal filtrations for the actual function-field pullback.
The exclusion of zero is necessary because `Scheme.ord` has value zero there. -/
def IsMonomialExceptionalOrder {Y X : Scheme} [IsIntegral Y] [IsIntegral X]
    [IsLocallyNoetherian Y] (f : Y ⟶ X)
    (hg : f (genericPoint Y) = genericPoint X) (y : Y) (x : X)
    (u v : X.presheaf.stalk x) (a b : ℕ) : Prop :=
  ∀ (n : ℕ) (z : X.presheaf.stalk x), z ≠ 0 →
    ((n : ℤ) ≤ Y.ord (genericFieldMap f hg
        (algebraMap (X.presheaf.stalk x) X.functionField z)) y ↔
      z ∈ monomialIdeal u v a b n)

/-- The general monomial-discrepancy theorem needed below, stated as the
finite length of relative differentials at the exceptional DVR. The weights
are arbitrary positive coprime integers. The target residue field need not
be the base field or separable over it. No smoothness assumption is made. -/
structure MonomialDiscrepancyInputs : Prop where
  monomial_length (F : Type) [Field F] (Y X : Scheme)
      [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y]
      (f : Y ⟶ X) (yToBase : Y ⟶ Spec (CommRingCat.of F))
      (xToBase : X ⟶ Spec (CommRingCat.of F))
      (h : IsRegularSurfaceModification F f yToBase xToBase)
      (y : Y) (x : X) (hy : coheight y = 1)
      (hdvr : IsDiscreteValuationRing (Y.presheaf.stalk y))
      (hcenter : f y = x) (hclosed : IsClosed ({x} : Set X))
      (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
      (u v : X.presheaf.stalk x)
      (hparams : maximalIdeal (X.presheaf.stalk x) = Ideal.span ({u,v} : Set _))
      (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcoprime : a.Coprime b)
      (hmonomial : IsMonomialExceptionalOrder f h.generic y x u v a b) :
    relativeCotangentLength f y = ((a + b - 1 : ℕ) : ℕ∞)

end
end Red61

/-! The explicit residue-field section on the actual special-point stalk,
with its function-field embedding and its prescribed ell-scalars tracked. -/

namespace Red61.Contraction

open Fields LocalCoordinates
noncomputable section

def specialCoefficientSection : k →+* SpecialLocalRing :=
  sSpecialStalkEquiv.symm.toRingHom.comp ConeRing.coefficientSection

@[simp] theorem specialCoefficientSection_stalkEquiv (a : k) :
    sSpecialStalkEquiv (specialCoefficientSection a) = ConeRing.coefficientSection a :=
  sSpecialStalkEquiv.apply_symm_apply _

@[simp] theorem specialResidue_coefficientSection (a : k) :
    specialResidue (specialCoefficientSection a) = a := by
  change ConeRing.residueB (sSpecialStalkEquiv (specialCoefficientSection a)) = a
  rw [specialCoefficientSection_stalkEquiv, ConeRing.residue_coefficientSection]

end
end Red61.Contraction

/-! Independence of the four actual local differentials follows from their
images in the fixed function field. Generation of the local differential
module is a separate condition and is not assumed or concluded here. -/

namespace Red61

noncomputable section

theorem differentialFamily_independent_of_fieldMap
    {R A F ι : Type*} [CommRing R] [CommRing A] [Field F] [Algebra R A] [Algebra R F]
    (f : A →+* F)
    (hf : Function.Injective f) (hbase : f.comp (algebraMap R A) = algebraMap R F)
    (v : ι → A)
    (h : LinearIndependent F (fun i ↦ KaehlerDifferential.D R F (f (v i)))) :
    LinearIndependent A (fun i ↦ KaehlerDifferential.D R A (v i)) := by
  let := f.toAlgebra
  have : IsScalarTower R A F := .of_algebraMap_eq' hbase.symm
  have : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hf
  apply LinearIndependent.of_comp (KaehlerDifferential.map R R A F)
  simpa only [Function.comp_def, KaehlerDifferential.map_D,
    RingHom.algebraMap_toAlgebra] using h.restrict_scalars' A

namespace ConeRing

open Fields

end ConeRing

namespace Contraction

open Fields ConeRing

def specialDifferentialCoordinates (i : Fin 4) : SpecialLocalRing :=
  sSpecialStalkEquiv.symm (invariantCoordinatesB i)

theorem specialDifferentialCoordinates_values :
    specialDifferentialCoordinates =
      ![specialCoefficientSection (c 0), specialCoefficientSection (c 1), specialU, specialR] := by
  funext i
  fin_cases i <;>
    simp [specialDifferentialCoordinates, invariantCoordinatesB,
      specialCoefficientSection, specialU, specialR]

theorem specialDifferentialCoordinates_embedding (i : Fin 4) :
    sFunctionFieldEquiv (algebraMap SpecialLocalRing S.functionField
      (specialDifferentialCoordinates i)) = invariantCoordinates i := by
  rw [sSpecialStalkEquiv_functionField]
  exact congrArg invariantEmbedding (sSpecialStalkEquiv.apply_symm_apply _)

theorem specialLocalDifferentials_independent :
    LinearIndependent SpecialLocalRing
      (fun i ↦ KaehlerDifferential.D ℤ SpecialLocalRing (specialDifferentialCoordinates i)) := by
  let := functionFieldAlgebra ell sToBase
  refine differentialFamily_independent_of_fieldMap (R := ℤ)
    (sFunctionFieldEquiv.toRingHom.comp (algebraMap SpecialLocalRing S.functionField))
    (sFunctionFieldEquiv.injective.comp (IsFractionRing.injective SpecialLocalRing S.functionField))
    (Subsingleton.elim _ _) specialDifferentialCoordinates ?_
  have he : (fun i ↦ KaehlerDifferential.D ℤ L
      (sFunctionFieldEquiv.toRingHom.comp (algebraMap SpecialLocalRing S.functionField)
        (specialDifferentialCoordinates i))) = invariantAbsoluteDifferentialBasis := by
    funext i
    change KaehlerDifferential.D ℤ L (sFunctionFieldEquiv
      (algebraMap SpecialLocalRing S.functionField (specialDifferentialCoordinates i))) = _
    rw [specialDifferentialCoordinates_embedding]
    exact (invariantAbsoluteDifferentialBasis_apply i).symm
  rw [he]
  exact invariantAbsoluteDifferentialBasis.linearIndependent

end Contraction
end
end Red61

/-! The four coordinate differentials form a constructed basis at the actual
special-point stalk of S. The residue section and the regular parameters are
the previously constructed elements of that stalk. -/

namespace Red61.Contraction

open Fields ConeRing Module
noncomputable section

theorem specialLocal_essFiniteType_int : Algebra.EssFiniteType ℤ SpecialLocalRing := by
  have h₀ := RingHom.essFiniteType_algebraMap.mpr invariantLocal_essFiniteType_int
  have h₁ := (RingHom.FiniteType.of_surjective sSpecialStalkEquiv.symm.toRingHom
    sSpecialStalkEquiv.symm.surjective).essFiniteType
  have h := h₀.comp h₁
  have he : sSpecialStalkEquiv.symm.toRingHom.comp (algebraMap ℤ B) =
      algebraMap ℤ SpecialLocalRing := Subsingleton.elim _ _
  rw [he] at h
  exact RingHom.essFiniteType_algebraMap.mp h

theorem specialLocal_differentials_finite :
    Module.Finite SpecialLocalRing (KaehlerDifferential ℤ SpecialLocalRing) := by
  have := specialLocal_essFiniteType_int
  infer_instance

theorem specialLocalDifferentials_span :
    Submodule.span SpecialLocalRing (Set.range (fun i ↦
      KaehlerDifferential.D ℤ SpecialLocalRing (specialDifferentialCoordinates i))) = ⊤ := by
  have := specialLocal_differentials_finite
  let N := Submodule.span SpecialLocalRing (Set.range (fun i ↦
    KaehlerDifferential.D ℤ SpecialLocalRing (specialDifferentialCoordinates i)))
  have hmem (i : Fin 4) :
      KaehlerDifferential.D ℤ SpecialLocalRing (specialDifferentialCoordinates i) ∈ N :=
    Submodule.subset_span (Set.mem_range_self i)
  have hu : KaehlerDifferential.D ℤ SpecialLocalRing specialU ∈ N := by
    simpa [specialDifferentialCoordinates_values] using hmem 2
  have hr : KaehlerDifferential.D ℤ SpecialLocalRing specialR ∈ N := by
    simpa [specialDifferentialCoordinates_values] using hmem 3
  change N = ⊤
  refine localDifferentials_eq_top_of_section (R := ℤ) specialResidue specialCoefficientSection
    specialResidue_coefficientSection special_maximal_eq_residue_kernel.symm
    specialU specialR special_parameters_generate N hu hr ?_
  intro a
  apply rationalCoefficient_differential_mem specialCoefficientSection N (a := a)
  intro i
  fin_cases i
  · simpa [specialDifferentialCoordinates_values] using hmem 0
  · simpa [specialDifferentialCoordinates_values] using hmem 1

def specialLocalDifferentialBasis :
    Basis (Fin 4) SpecialLocalRing (KaehlerDifferential ℤ SpecialLocalRing) :=
  Basis.mk specialLocalDifferentials_independent (by rw [specialLocalDifferentials_span])

@[simp] theorem specialLocalDifferentialBasis_apply (i : Fin 4) :
    specialLocalDifferentialBasis i =
      KaehlerDifferential.D ℤ SpecialLocalRing (specialDifferentialCoordinates i) :=
  Basis.mk_apply _ _ i

end
end Red61.Contraction

/-! The actual differential module pulled from the special stalk has a
constructed four-element basis at every point above s0. Matrix comparisons
therefore need only a basis of the target differential module. -/

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry Module
open scoped TensorProduct
noncomputable section

def specialDifferentialCoordinatesAt (x : S) (hx : x = s₀) : Fin 4 → S.presheaf.stalk x := by
  subst x
  exact specialDifferentialCoordinates

def specialLocalDifferentialBasisAt (x : S) (hx : x = s₀) :
    Basis (Fin 4) (S.presheaf.stalk x) (AbsoluteStalkDifferentials S x) := by
  subst x
  exact specialLocalDifferentialBasis

@[simp] theorem specialLocalDifferentialBasisAt_apply (x : S) (hx : x = s₀) (i : Fin 4) :
    specialLocalDifferentialBasisAt x hx i =
      KaehlerDifferential.D ℤ (S.presheaf.stalk x) (specialDifferentialCoordinatesAt x hx i) := by
  subst x
  exact specialLocalDifferentialBasis_apply i

def sigmaBarSpecialPulledDifferentialBasis (y : resolvedQuotient) (hy : sigmaBar y = s₀) :
    Basis (Fin 4) (resolvedQuotient.presheaf.stalk y) (PulledStalkDifferentials sigmaBar y) := by
  let := (sigmaBar.stalkMap y).hom.toAlgebra
  exact (specialLocalDifferentialBasisAt (sigmaBar y) hy).baseChange _

@[simp] theorem sigmaBarSpecialPulledDifferentialBasis_apply
    (y : resolvedQuotient) (hy : sigmaBar y = s₀) (i : Fin 4) :
    letI := (sigmaBar.stalkMap y).hom.toAlgebra
    sigmaBarSpecialPulledDifferentialBasis y hy i =
      1 ⊗ₜ[S.presheaf.stalk (sigmaBar y)]
        KaehlerDifferential.D ℤ (S.presheaf.stalk (sigmaBar y))
          (specialDifferentialCoordinatesAt (sigmaBar y) hy i) := by
  let := (sigmaBar.stalkMap y).hom.toAlgebra
  exact (Basis.baseChange_apply _ _ _).trans (congrArg (fun ω ↦ 1 ⊗ₜ ω)
    (specialLocalDifferentialBasisAt_apply (sigmaBar y) hy i))

end
end Red61.Contraction

/-! Constructed target differential bases at both actual exceptional generic
points. The second basis uses an open localization containing that point. -/

namespace Red61.Charts

open Fields PolynomialInvariants AffineGluing AlgebraicGeometry Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000

def exceptionalSecondQuotientPrime : PrimeSpectrum (invariantChartRing 2) :=
  chartQuotient 2 (coordinatePrime 2 0)

def exceptionalSecondKernelPrime : PrimeSpectrum exceptionalSecondKernel :=
  PrimeSpectrum.comap exceptionalSecondKernelEquiv.toRingHom exceptionalSecondQuotientPrime

local instance : Module (Localization.AtPrime exceptionalSecondKernelPrime.asIdeal)
    (KaehlerDifferential ℤ (Localization.AtPrime exceptionalSecondKernelPrime.asIdeal)) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ
    (Localization.AtPrime exceptionalSecondKernelPrime.asIdeal)
    (R' := Localization.AtPrime exceptionalSecondKernelPrime.asIdeal)

local instance : Module (Localization.AtPrime exceptionalSecondQuotientPrime.asIdeal)
    (KaehlerDifferential ℤ (Localization.AtPrime exceptionalSecondQuotientPrime.asIdeal)) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ
    (Localization.AtPrime exceptionalSecondQuotientPrime.asIdeal)
    (R' := Localization.AtPrime exceptionalSecondQuotientPrime.asIdeal)

end
end Red61.Charts

namespace Red61.Contraction

open Fields Charts AlgebraicGeometry Module
noncomputable section
set_option synthInstance.maxHeartbeats 80000

end
end Red61.Contraction

/-! Actual contraction coordinates and differential matrices, together with
the reverse passage from scheme order to local ring order. -/

namespace Red61

open AlgebraicGeometry CategoryTheory Module
noncomputable section

namespace Contraction

open Fields Charts

def resolvedStalkFieldMap (y : resolvedQuotient) : resolvedQuotient.presheaf.stalk y →+* L :=
  resolvedQuotientFunctionFieldEquiv.toRingHom.comp
    (algebraMap (resolvedQuotient.presheaf.stalk y) resolvedQuotient.functionField)

theorem resolvedStalkFieldMap_injective (y : resolvedQuotient) :
    Function.Injective (resolvedStalkFieldMap y) :=
  resolvedQuotientFunctionFieldEquiv.injective.comp
    (IsFractionRing.injective (resolvedQuotient.presheaf.stalk y) resolvedQuotient.functionField)

end Contraction
end
end Red61

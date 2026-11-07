import Eff.AtlasEuler
import Eff.InvariantCoordinates
import SurfaceLib.Derivation.FrobeniusCover

/-! # Homogeneous covering certificates on the four actual charts

Freeness can be checked without transferring a tangent-vector calculation through stalk
isomorphisms. The displayed invariants generate the unit ideal on each chart. Their
nonzero weights then give a cover by opens admitting a homogeneous unit.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
private local instance : Algebra F₅ ell := ZMod.algebra ell 5

def middleQ : K := c₁ - c₂ * y₁ 3 + 2 * c₂ ^ 2 * y₁ 3 * y₂ 3 +
  2 * c₂ ^ 3 * y₁ 3 * (y₂ 3) ^ 2
def middleH : K := y₁ 3 * (1 + 3 * c₂ * y₂ 3) ^ 2
def middleJ : K := y₁ 3 * (y₂ 3) ^ 2

def certificateValue : Fin 4 → Fin 3 → K :=
  ![![A, B, W], ![middleQ, middleH, middleJ],
    ![y₂ 5, LocalCoordinates.q₁, 0], ![LocalCoordinates.U, LocalCoordinates.q₁, 0]]

def certificateWeight : Fin 4 → Fin 3 → ℤ :=
  ![![2, 1, 3], ![-1, -2, -4], ![-4, -1, 1], ![-3, -1, 1]]

theorem certificateWeight_nonzero (i : Fin 4) (j : Fin 3) :
    (certificateWeight i j : ZMod 5) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide

theorem delta_special_coordinate : delta LocalCoordinates.q₁ = 0 := by
  simp [LocalCoordinates.q₁, LocalCoordinates.U, LocalCoordinates.T,
    Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul, coord_nonzero 3]

theorem middleQ_invariant : delta middleQ = 0 := by
  apply (field_chart_kernel 3 _).mp
  simpa [straightMiddle, middleSlice, middleQ] using middle_derivatives 0 1

theorem middleH_invariant : delta middleH = 0 := by
  apply (field_chart_kernel 3 _).mp
  simpa [straightMiddle, middleDenominator, middleSlice, middleH] using middle_derivatives 0 2

theorem middleJ_invariant : delta middleJ = 0 := by
  apply (field_chart_kernel 3 _).mp
  simp only [middleJ, Derivation.leibniz, Derivation.leibniz_pow,
    middle_values.2.2.1, middle_values.2.2.2, smul_eq_mul, nsmul_eq_mul]
  norm_num
  linear_combination y₁ 3 * (y₂ 3) ^ 3 * (CharP.cast_eq_zero K 5)

theorem certificate_invariant (i : Fin 4) (j : Fin 3) : delta (certificateValue i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [certificateValue, delta_A, delta_B, delta_W, middleQ_invariant,
      middleH_invariant, middleJ_invariant, delta_special_coordinate,
      LocalCoordinates.U, Derivation.leibniz_inv, smul_eq_mul]
  · have h := last_values.2.2.2
    exact (field_chart_kernel 5 _).mp h

theorem euler_middle_first : euler (y₁ 3) = -2 * y₁ 3 := by
  simpa [y₁, first, monomial] using euler_monomial (first 3)

theorem euler_middle_second : euler (y₂ 3) = -(y₂ 3) := by
  convert euler_monomial (second 3) using 1 <;> norm_num [y₂, second]

theorem euler_middleQ : euler middleQ = -middleQ := by
  have h2 : euler (2 : K) = 0 := euler.map_natCast 2
  simp only [middleQ, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    euler_c₁, euler_c₂, euler_middle_first, euler_middle_second, h2,
    smul_eq_mul, nsmul_eq_mul]
  ring

theorem euler_middleH : euler middleH = -2 * middleH := by
  have h3 : euler (3 : K) = 0 := euler.map_natCast 3
  simp only [middleH, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    euler_c₂, euler_middle_first, euler_middle_second, h3,
    Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
  ring

theorem euler_middleJ : euler middleJ = -4 * middleJ := by
  simp only [middleJ, Derivation.leibniz, Derivation.leibniz_pow,
    euler_middle_first, euler_middle_second, smul_eq_mul, nsmul_eq_mul]
  ring

theorem certificate_eigen (i : Fin 4) (j : Fin 3) :
    euler (certificateValue i j) = (certificateWeight i j : K) * certificateValue i j := by
  fin_cases i <;> fin_cases j <;>
    simp [certificateValue, certificateWeight, euler_A, euler_B, euler_W,
      euler_middleQ, euler_middleH, euler_middleJ, euler_special_coordinate]
  · convert euler_monomial (second 5) using 1 <;> norm_num [y₂, second]
  · simpa [LocalCoordinates.U] using euler_zpow w (coord_nonzero 3) 3 euler_w (-1)

private theorem includeK_c_zero : includeK (c 0) = c₁ := by
  norm_num [includeK_c]

private theorem includeK_c_one : includeK (c 1) = c₂ := by
  norm_num [includeK_c]

theorem contracted_c₁_mem (i : Fin 4) : c₁ ∈ contractedAtlas.ring i := by
  rw [← includeK_c_zero]
  exact (contractedAtlas.ring i).algebraMap_mem (c 0)

theorem contracted_c₂_mem (i : Fin 4) : c₂ ∈ contractedAtlas.ring i := by
  rw [← includeK_c_one]
  exact (contractedAtlas.ring i).algebraMap_mem (c 1)

theorem contracted_c₁_inv_mem (i : Fin 4) : c₁⁻¹ ∈ contractedAtlas.ring i := by
  rw [← includeK_c_zero, ← map_inv₀]
  exact (contractedAtlas.ring i).algebraMap_mem ((c 0)⁻¹)

theorem contracted_c₂_inv_mem (i : Fin 4) : c₂⁻¹ ∈ contractedAtlas.ring i := by
  rw [← includeK_c_one, ← map_inv₀]
  exact (contractedAtlas.ring i).algebraMap_mem ((c 1)⁻¹)

theorem certificate_mem (i : Fin 4) (j : Fin 3) :
    certificateValue i j ∈ contractedAtlas.ring i := by
  have hc₁ := contracted_c₁_mem i
  have hc₂ := contracted_c₂_mem i
  have hn (n : ℕ) : (n : K) ∈ contractedAtlas.ring i := by
    simpa only [map_natCast] using (contractedAtlas.ring i).algebraMap_mem (n : k)
  fin_cases i
  · have ht := y₁_mem (0 : Fin 6)
    have hw := y₂_mem (0 : Fin 6)
    have ht : t ∈ contractedAtlas.ring (0 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, y₁, first, monomial] using ht
    have hw : w ∈ contractedAtlas.ring (0 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, y₂, second, monomial] using hw
    fin_cases j
    · change t - c₁ * w ∈ contractedAtlas.ring (0 : Fin 4)
      exact (contractedAtlas.ring (0 : Fin 4)).sub_mem ht
        ((contractedAtlas.ring (0 : Fin 4)).mul_mem hc₁ hw)
    · change c₂ - c₁ * t + 3 * c₁ ^ 2 * w ∈ contractedAtlas.ring (0 : Fin 4)
      aesop (add safe apply [Subalgebra.add_mem, Subalgebra.mul_mem,
        Subalgebra.sub_mem, Subalgebra.pow_mem])
    · change w ∈ contractedAtlas.ring (0 : Fin 4)
      exact hw
  · have ht : y₁ 3 ∈ contractedAtlas.ring (1 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₁_mem 3
    have he : y₂ 3 ∈ contractedAtlas.ring (1 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₂_mem 3
    fin_cases j
    · change c₁ - c₂ * y₁ 3 + 2 * c₂ ^ 2 * y₁ 3 * y₂ 3 +
        2 * c₂ ^ 3 * y₁ 3 * (y₂ 3) ^ 2 ∈ contractedAtlas.ring (1 : Fin 4)
      aesop (add safe apply [Subalgebra.add_mem, Subalgebra.mul_mem,
        Subalgebra.sub_mem, Subalgebra.pow_mem])
    · change y₁ 3 * (1 + 3 * c₂ * y₂ 3) ^ 2 ∈ contractedAtlas.ring (1 : Fin 4)
      aesop (add safe apply [Subalgebra.add_mem, Subalgebra.mul_mem,
        Subalgebra.one_mem, Subalgebra.pow_mem])
    · change y₁ 3 * (y₂ 3) ^ 2 ∈ contractedAtlas.ring (1 : Fin 4)
      exact (contractedAtlas.ring (1 : Fin 4)).mul_mem ht
        ((contractedAtlas.ring (1 : Fin 4)).pow_mem he 2)
  · have hx : y₁ 5 ∈ contractedAtlas.ring (2 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₁_mem 5
    have ht : y₂ 5 ∈ contractedAtlas.ring (2 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₂_mem 5
    have hq : LocalCoordinates.q₁ = c₁ - (y₁ 5) ^ 3 * y₂ 5 := by
      dsimp [LocalCoordinates.q₁, LocalCoordinates.U, LocalCoordinates.T,
        y₁, y₂, monomial, first, second]
      norm_num
      field_simp [coord_nonzero 2, coord_nonzero 3]
    fin_cases j
    · exact ht
    · change LocalCoordinates.q₁ ∈ contractedAtlas.ring (2 : Fin 4)
      rw [hq]
      exact (contractedAtlas.ring (2 : Fin 4)).sub_mem hc₁
        ((contractedAtlas.ring (2 : Fin 4)).mul_mem
          ((contractedAtlas.ring (2 : Fin 4)).pow_mem hx 3) ht)
    · exact (contractedAtlas.ring (2 : Fin 4)).zero_mem
  · have hu : LocalCoordinates.U ∈ contractedAtlas.ring (3 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, coneExponent, monomial,
        LocalCoordinates.U] using cone_generator_mem 0
    have hv : LocalCoordinates.U * LocalCoordinates.T ∈ contractedAtlas.ring (3 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, coneExponent, monomial,
        LocalCoordinates.U, LocalCoordinates.T, mul_comm] using
        cone_generator_mem 1
    fin_cases j
    · exact hu
    · exact (contractedAtlas.ring (3 : Fin 4)).sub_mem hc₁ hv
    · exact (contractedAtlas.ring (3 : Fin 4)).zero_mem

/-- Actual invariant elements of the four affine coordinate rings of `S`. -/
def certificate (i : Fin 4) (j : Fin 3) : quotientAtlas.ring i :=
  ⟨⟨certificateValue i j, certificate_invariant i j⟩, certificate_mem i j⟩

theorem certificate_weight (i : Fin 4) (j : Fin 3) :
    sChartEuler i (certificate i j) = (certificateWeight i j : quotientAtlas.ring i) *
      certificate i j := by
  apply Subtype.ext
  apply Subtype.ext
  change euler (certificateValue i j) =
    algebraMap L K (algebraMap (quotientAtlas.ring i) L
      (certificateWeight i j : quotientAtlas.ring i)) * certificateValue i j
  simpa only [map_intCast] using certificate_eigen i j

/-- Coefficients of a unit-ideal certificate in the original toric chart ring. -/
def coverCoefficient : Fin 4 → Fin 3 → K :=
  ![![c₁ * c₂⁻¹, c₂⁻¹, -2 * c₁ ^ 2 * c₂⁻¹],
    ![c₁⁻¹, (c₂ - 3 * c₂ ^ 2 * y₂ 3) * c₁⁻¹,
      (-3 * c₂ ^ 3 - 3 * c₂ ^ 4 * y₂ 3) * c₁⁻¹],
    ![(y₁ 5) ^ 3 * c₁⁻¹, c₁⁻¹, 0],
    ![LocalCoordinates.U * LocalCoordinates.T ^ 2 * (c₁⁻¹) ^ 2,
      (LocalCoordinates.q₁ + 2 * LocalCoordinates.U * LocalCoordinates.T) * (c₁⁻¹) ^ 2, 0]]

theorem cover_identity (i : Fin 4) :
    ∑ j : Fin 3, coverCoefficient i j * certificateValue i j = 1 := by
  fin_cases i
  · simp [Fin.sum_univ_succ, coverCoefficient, certificateValue, A, B, W]
    field_simp [coord_nonzero 1]
    ring
  · simp only [Fin.sum_univ_succ, coverCoefficient, certificateValue,
      Fin.sum_univ_zero, add_zero]
    change c₁⁻¹ * middleQ +
      ((c₂ - 3 * c₂ ^ 2 * y₂ 3) * c₁⁻¹ * middleH +
        (-3 * c₂ ^ 3 - 3 * c₂ ^ 4 * y₂ 3) * c₁⁻¹ * middleJ) = 1
    field_simp [coord_nonzero 0]
    unfold middleQ middleH middleJ
    linear_combination (c₂ ^ 2 * y₁ 3 * y₂ 3 - 2 * c₂ ^ 3 * y₁ 3 * (y₂ 3) ^ 2 -
      6 * c₂ ^ 4 * y₁ 3 * (y₂ 3) ^ 3) * (CharP.cast_eq_zero K 5)
  · simp [Fin.sum_univ_succ, coverCoefficient, certificateValue,
      LocalCoordinates.q₁, LocalCoordinates.U, LocalCoordinates.T,
      y₁, y₂, monomial, first, second]
    field_simp [coord_nonzero 0, coord_nonzero 2, coord_nonzero 3]
    ring
  · simp [Fin.sum_univ_succ, coverCoefficient, certificateValue,
      LocalCoordinates.q₁]
    field_simp [coord_nonzero 0]
    ring

theorem coverCoefficient_mem (i : Fin 4) (j : Fin 3) :
    coverCoefficient i j ∈ contractedAtlas.ring i := by
  have hc₁ := contracted_c₁_mem i
  have hc₂ := contracted_c₂_mem i
  have hi₁ := contracted_c₁_inv_mem i
  have hi₂ := contracted_c₂_inv_mem i
  have hn (n : ℕ) : (n : K) ∈ contractedAtlas.ring i := by
    simpa only [map_natCast] using (contractedAtlas.ring i).algebraMap_mem (n : k)
  fin_cases i
  · fin_cases j <;> simp only [coverCoefficient]
    all_goals aesop (add safe apply [Subalgebra.mul_mem, Subalgebra.pow_mem, Subalgebra.neg_mem])
  · have he : y₂ 3 ∈ contractedAtlas.ring (1 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₂_mem 3
    fin_cases j <;> simp only [coverCoefficient]
    all_goals aesop (add safe apply [Subalgebra.mul_mem, Subalgebra.pow_mem,
      Subalgebra.sub_mem, Subalgebra.neg_mem])
  · have hx : y₁ 5 ∈ contractedAtlas.ring (2 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring] using y₁_mem 5
    fin_cases j <;> simp only [coverCoefficient]
    all_goals aesop (add safe apply [Subalgebra.mul_mem, Subalgebra.pow_mem, Subalgebra.zero_mem])
  · have hz : LocalCoordinates.U * LocalCoordinates.T ^ 2 ∈ contractedAtlas.ring (3 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, coneExponent, monomial,
        LocalCoordinates.U, LocalCoordinates.T, mul_comm] using
        cone_generator_mem 2
    have hv : LocalCoordinates.U * LocalCoordinates.T ∈ contractedAtlas.ring (3 : Fin 4) := by
      simpa [contractedAtlas, Red61.Contraction.ring, coneExponent, monomial,
        LocalCoordinates.U, LocalCoordinates.T, mul_comm] using
        cone_generator_mem 1
    have hq : LocalCoordinates.q₁ ∈ contractedAtlas.ring (3 : Fin 4) := certificate_mem 3 1
    fin_cases j <;> simp only [coverCoefficient]
    · exact (contractedAtlas.ring (3 : Fin 4)).mul_mem hz
        ((contractedAtlas.ring (3 : Fin 4)).pow_mem hi₁ 2)
    · apply (contractedAtlas.ring (3 : Fin 4)).mul_mem _
        ((contractedAtlas.ring (3 : Fin 4)).pow_mem hi₁ 2)
      apply (contractedAtlas.ring (3 : Fin 4)).add_mem hq
      have he : 2 * LocalCoordinates.U * LocalCoordinates.T =
          2 * (LocalCoordinates.U * LocalCoordinates.T) := by ring
      rw [he]
      exact (contractedAtlas.ring (3 : Fin 4)).mul_mem (hn 2) hv
    · exact (contractedAtlas.ring (3 : Fin 4)).zero_mem

/-- The invariant homogeneous functions generate the unit ideal in each actual chart of S. -/
theorem certificate_span_top (i : Fin 4) : Ideal.span (Set.range (certificate i)) = ⊤ := by
  let C := quotientAtlas.ring i
  let R := (contractedAtlas.ring i).restrictScalars ell
  have : CharP R 5 := (algebraMap R K).charP Subtype.val_injective 5
  let f : C →+* R := (FrobeniusDescent.embed L R).toRingHom
  have hf : Function.Injective f := FrobeniusDescent.embed_injective L R
  have hp (r : R) : ∃ c : C, f c = r ^ 5 :=
    ⟨FrobeniusDescent.powerElement L 5 field_fifth_power_invariant R r, rfl⟩
  let a : Fin 3 → R := fun j ↦ ⟨coverCoefficient i j, coverCoefficient_mem i j⟩
  apply SurfaceLib.span_top_of_fifth_power_lifts f hf hp (certificate i) a
  apply Subtype.ext
  exact cover_identity i

/-- Every prime of an actual affine chart is avoided by one of the certificates. -/
theorem certificate_cover (i : Fin 4) (p : PrimeSpectrum (quotientAtlas.ring i)) :
    ∃ j : Fin 3, certificate i j ∉ p.asIdeal := by
  by_contra! h
  have hle : Ideal.span (Set.range (certificate i)) ≤ p.asIdeal :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  rw [certificate_span_top] at hle
  exact p.isPrime.ne_top (top_unique hle)

theorem certificateWeight_isUnit (i : Fin 4) (j : Fin 3) :
    IsUnit (certificateWeight i j : quotientAtlas.ring i) := by
  let := ZMod.algebra (quotientAtlas.ring i) 5
  have h := (isUnit_iff_ne_zero.mpr (certificateWeight_nonzero i j)).map
    (algebraMap (ZMod 5) (quotientAtlas.ring i))
  simpa only [map_intCast] using h

/-- The chart derivation has a nonzero value modulo every prime, including the cone point. -/
theorem sChartEuler_nowhereVanishing (i : Fin 4)
    (p : PrimeSpectrum (quotientAtlas.ring i)) :
    ∃ a : quotientAtlas.ring i, sChartEuler i a ∉ p.asIdeal := by
  obtain ⟨j, hj⟩ := certificate_cover i p
  refine ⟨certificate i j, ?_⟩
  rw [certificate_weight, p.asIdeal.unit_mul_mem_iff_mem (certificateWeight_isUnit i j)]
  exact hj

end
end Eff

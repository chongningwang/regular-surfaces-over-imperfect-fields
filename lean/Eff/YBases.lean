import Eff.YCharts

/-! # The four coordinate systems on `S`, and the eigenfunction weights -/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent Red61.LocalCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A chart ring over `ell`, regarded over the prime field. -/
def toF₅ (C : Subalgebra ell L) : Subalgebra F₅ L where
  __ := C.toSubsemiring
  algebraMap_mem' a := by
    have h : algebraMap F₅ L a = (a.val : L) := by
      conv_lhs => rw [show a = ((a.val : ℕ) : F₅) from (ZMod.natCast_zmod_val a).symm, map_natCast]
    rw [h]
    exact C.natCast_mem _

@[simp] theorem mem_toF₅ (C : Subalgebra ell L) (x : L) : x ∈ toF₅ C ↔ x ∈ C := Iff.rfl

/-- `yAtlas` denominators equal to one, and the corresponding trivial clearing. -/
theorem one_coe (i : Fin 4) : (((1 : yAtlas.ring i) : M) : L) = 1 := rfl

theorem polynomialRing_coe (x : Fin 4 → L) :
    (polynomialRing (F := F₅) x).map ConeRing.invariantInclusion =
      polynomialRing (F := F₅) (fun i ↦ (x i : K)) := by
  unfold polynomialRing
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  rfl

/-- Transfer the Red61 localization of a straightened kernel from `K` to `L`. -/
theorem hull_of_straight (D : Derivation F₅ K K) (v : Fin 4 → K)
    (hi : AlgebraicIndependent F₅ v) (hv : ∀ i, D (v i) = if i = 0 then 1 else 0)
    (R : Subalgebra F₅ K) (hloc : R ≤ hull (polynomialRing v) R)
    (x : Fin 4 → L) (hx : ∀ i, (x i : K) = powerCoordinates v i)
    (A : Subalgebra F₅ L) (hA : ∀ a : L, a ∈ A ↔ (a : K) ∈ kernelIn D R) :
    A ≤ hull (polynomialRing x) A := by
  have hP : (polynomialRing (F := F₅) x).map ConeRing.invariantInclusion =
      polynomialRing (F := F₅) (powerCoordinates v) := by
    rw [polynomialRing_coe]
    congr 2
    funext i
    exact hx i
  intro a ha
  obtain ⟨b, hb, hb0, hbi, hab⟩ := kernel_le_hull D v hi hv R hloc ((hA a).mp ha)
  rw [← hP] at hb hab
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', hc⟩ := hab
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hb0 (map_zero _)
  refine ⟨b', hb', hb'0, ?_, ?_⟩
  · apply (hA _).mpr
    have : ((b'⁻¹ : L) : K) = (ConeRing.invariantInclusion b')⁻¹ := rfl
    rw [this]
    exact hbi
  · have he : a * b' = c' := by
      apply L.subtype_injective
      exact hc.symm
    rw [he]
    exact hc'

theorem field_top_of_invariantCoordinates (x : Fin 4 → L)
    (h : ∀ i, ConeRing.invariantCoordinates i ∈ IntermediateField.adjoin F₅ (Set.range x)) :
    IntermediateField.adjoin F₅ (Set.range x) = ⊤ := by
  apply top_unique
  rw [← ConeRing.invariantCoordinates_field_generation]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact h i

/-! ### Euler weights -/

theorem euler_U : euler U = -3 * U := by
  simpa [U] using euler_zpow w (coord_nonzero 3) 3 euler_w (-1)

theorem euler_special_second : euler q₂ = q₂ := by
  have h3 : euler (3 : K) = 0 := euler.map_natCast 3
  simp only [q₂, map_sub, Derivation.leibniz, Derivation.leibniz_pow, euler_c₂, euler_U, T,
    euler_t, h3, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one, mul_zero, add_zero]
  push_cast
  ring

theorem euler_r : euler r = 4 * r := by
  simp only [r, Derivation.leibniz, Derivation.leibniz_pow, euler_U, T, euler_t, smul_eq_mul,
    nsmul_eq_mul, Nat.reduceSub, pow_one]
  push_cast
  ring

theorem invariantEuler_of_K (x : L) (n : ℤ) (h : euler (x : K) = (n : K) * x) :
    invariantEuler x = (n : L) * x := by
  apply Subtype.ext
  rw [show ((invariantEuler x : L) : K) = euler (x : K) from rfl, h]
  simp

theorem chart_kernel_mem_L (k : Fin 6) {x : K} (h : localGenerator k x = 0) : x ∈ L :=
  (field_chart_kernel k x).mp h

/-- A straightened kernel coordinate, as an element of `L`. -/
def straightL (k : Fin 6) (v : Fin 4 → K) (hi : AlgebraicIndependent F₅ v)
    (hv : ∀ i, localGenerator k (v i) = if i = 0 then 1 else 0)
    (R : Subalgebra F₅ K) (hle : polynomialRing v ≤ R) (i : Fin 4) : L :=
  ⟨powerCoordinates v i, chart_kernel_mem_L k
    (powerPolynomial_le_kernel (localGenerator k) v hi hv R hle
      (Algebra.subset_adjoin (Set.mem_range_self i))).2⟩

@[simp] theorem straightL_coe (k : Fin 6) (v : Fin 4 → K) (hi) (hv) (R) (hle) (i : Fin 4) :
    (straightL k v hi hv R hle i : K) = powerCoordinates v i := rfl

/-! ### Chart `V₁`: coordinates `(s₁, B, A, W)` with weights `(0, 1, 2, 3)` -/

def x0 : Fin 4 → L :=
  straightL 0 straightFirst first_independent first_derivatives firstRing first_polynomial_le

theorem x0_coe : (fun i ↦ (x0 i : K)) = ![c₁ ^ 5, B, A, W] := by
  funext i
  fin_cases i <;> rfl

def wt0 : Fin 4 → ℤ := ![0, 1, 2, 3]

theorem x0_euler (i : Fin 4) : invariantEuler (x0 i) = (wt0 i : L) * x0 i := by
  apply invariantEuler_of_K
  have h : (x0 i : K) = ![c₁ ^ 5, B, A, W] i := congrFun x0_coe i
  rw [h]
  fin_cases i
  · have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    simp [wt0, h5]
  · simp [wt0]
  · simp [wt0]
  · simp [wt0]

theorem q₁_eq0 : q₁ = -A / W := by
  simp only [q₁, U, T, A, W]
  have := coord_nonzero 3
  field_simp
  ring

theorem q₂_eq0 : q₂ = B - 3 * A ^ 2 / W := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : q₂ - (B - 3 * A ^ 2 / W) = 5 * (-(c₁ * t)) := by
    simp only [q₂, U, T, A, B, W]
    have := coord_nonzero 3
    field_simp
    ring
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem u_eq0 : u = W⁻¹ := rfl

theorem r_eq0 : r = (c₁ ^ 5 - q₁ ^ 5) * W ^ 3 := by
  rw [q₁_fifth]
  simp only [r, u, U, T, W]
  have := coord_nonzero 3
  field_simp
  ring

theorem x0_field (i : Fin 4) :
    ConeRing.invariantCoordinates i ∈ IntermediateField.adjoin F₅ (Set.range x0) := by
  let E := IntermediateField.adjoin F₅ (Set.range x0)
  have hx (k : Fin 4) : x0 k ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_range_self k)
  have hc (k : Fin 4) : (x0 k : K) = ![c₁ ^ 5, B, A, W] k := congrFun x0_coe k
  have h0 : ConeRing.invariantCoordinates 0 = -x0 2 / x0 3 := by
    apply L.subtype_injective
    simpa [hc] using q₁_eq0
  have h1 : ConeRing.invariantCoordinates 1 = x0 1 - 3 * x0 2 ^ 2 / x0 3 := by
    apply L.subtype_injective
    have h3 : ((3 : L) : K) = 3 := map_ofNat L.subtype 3
    simpa [hc, h3] using q₂_eq0
  have h2 : ConeRing.invariantCoordinates 2 = (x0 3)⁻¹ := by
    apply L.subtype_injective
    simpa [hc] using u_eq0
  have h3 : ConeRing.invariantCoordinates 3 =
      (x0 0 - ConeRing.invariantCoordinates 0 ^ 5) * x0 3 ^ 3 := by
    apply L.subtype_injective
    simpa [hc] using r_eq0
  have m0 : ConeRing.invariantCoordinates 0 ∈ E := by
    rw [h0]
    exact E.div_mem (E.neg_mem (hx 2)) (hx 3)
  fin_cases i
  · exact m0
  · change ConeRing.invariantCoordinates 1 ∈ E
    rw [h1]
    exact E.sub_mem (hx 1) (E.div_mem (E.mul_mem (E.natCast_mem 3) (E.pow_mem (hx 2) 2)) (hx 3))
  · change ConeRing.invariantCoordinates 2 ∈ E
    rw [h2]
    exact E.inv_mem (hx 3)
  · change ConeRing.invariantCoordinates 3 ∈ E
    rw [h3]
    exact E.mul_mem (E.sub_mem (hx 0) (E.pow_mem m0 5)) (E.pow_mem (hx 3) 3)

def base0 : YBase 0 where
  A := toF₅ (quotientAtlas.ring (0 : Fin 4))
  d := 1
  x := x0
  wt := wt0
  d_ne := one_ne_zero
  d_inv := by
    rw [one_coe, inv_one]
    exact Subalgebra.one_mem _
  chart_le a := a.property
  clear c hc := ⟨0, by simpa using hc⟩
  euler_x := x0_euler
  poly_le := Algebra.adjoin_le (by
    rintro _ ⟨i, rfl⟩
    exact (powerPolynomial_le_kernel (localGenerator 0) straightFirst first_independent
      first_derivatives firstRing first_polynomial_le
      (Algebra.subset_adjoin (Set.mem_range_self i))).1)
  hull_le := hull_of_straight (localGenerator 0) straightFirst first_independent first_derivatives
    firstRing first_localization x0 (fun _ ↦ rfl) _ (fun a ↦
      ⟨fun h ↦ ⟨h, (field_chart_kernel 0 _).mpr a.property⟩, fun h ↦ h.1⟩)
  field_top := field_top_of_invariantCoordinates _ x0_field

/-! ### Chart `V₆`: coordinates `(s₂, Q₂, ζ, τ)` with weights `(0, -1, 1, -4)` -/

theorem y₁5_eq : y₁ 5 = t ^ 2 / w := by
  simp [y₁, first, monomial, div_eq_mul_inv]

theorem y₂5_eq : y₂ 5 = w ^ 2 / t ^ 5 := by
  simp only [y₂, second, monomial]
  norm_num
  rw [div_eq_mul_inv, mul_comm]

theorem euler_y₁5 : euler (y₁ 5) = y₁ 5 := by
  have := coord_nonzero 2
  have := coord_nonzero 3
  rw [y₁5_eq, Derivation.leibniz_div, Derivation.leibniz_pow]
  simp only [euler_t, euler_w, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
  push_cast
  field_simp
  norm_num

theorem euler_y₂5 : euler (y₂ 5) = -4 * y₂ 5 := by
  have := coord_nonzero 2
  have := coord_nonzero 3
  rw [y₂5_eq, Derivation.leibniz_div, Derivation.leibniz_pow, Derivation.leibniz_pow]
  simp only [euler_t, euler_w, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
  push_cast
  field_simp
  ring

def x2 : Fin 4 → L :=
  straightL 5 straightLast last_independent last_derivatives lastRing last_polynomial_le

abbrev lastQ : K := straightLast 1
abbrev lastZ : K := straightLast 2

theorem lastQ_eq : lastQ = c₁ - c₂ * (y₁ 5) ^ 2 * y₂ 5 + 2 * c₂ ^ 2 * y₁ 5 * y₂ 5 +
    2 * c₂ ^ 3 * y₂ 5 := rfl

theorem lastZ_eq : lastZ = y₁ 5 - 2 * c₂ := rfl

theorem x2_coe : (fun i ↦ (x2 i : K)) = ![c₂ ^ 5, lastQ, lastZ, y₂ 5] := by
  funext i
  fin_cases i <;> rfl

def wt2 : Fin 4 → ℤ := ![0, -1, 1, -4]

theorem x2_euler (i : Fin 4) : invariantEuler (x2 i) = (wt2 i : L) * x2 i := by
  apply invariantEuler_of_K
  have h : (x2 i : K) = ![c₂ ^ 5, lastQ, lastZ, y₂ 5] i := congrFun x2_coe i
  rw [h]
  have h2 : euler (2 : K) = 0 := euler.map_natCast 2
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  fin_cases i
  · simp [wt2, h5]
  · change euler lastQ = ((-1 : ℤ) : K) * lastQ
    rw [lastQ_eq]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, euler_c₁, euler_c₂,
      euler_y₁5, euler_y₂5, h2, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  · change euler lastZ = ((1 : ℤ) : K) * lastZ
    rw [lastZ_eq]
    simp only [map_sub, Derivation.leibniz, euler_c₂, euler_y₁5, h2, smul_eq_mul]
    push_cast
    ring
  · simp [wt2, euler_y₂5]

theorem q₂_eq2 : q₂ = 2 * lastZ := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : q₂ - 2 * lastZ = 5 * (c₂ - t ^ 2 / w) := by
    rw [lastZ_eq, y₁5_eq]
    simp only [q₂, U, T]
    have := coord_nonzero 3
    field_simp
    ring
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem r_eq2 : r = (y₂ 5)⁻¹ := by
  simp only [r, U, T, y₂5_eq]
  have := coord_nonzero 2
  have := coord_nonzero 3
  field_simp

theorem q₁_eq2 : q₁ = lastQ - y₂ 5 * lastZ ^ 3 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : q₁ - (lastQ - y₂ 5 * lastZ ^ 3) =
      5 * (-(y₂ 5 * (c₂ * (y₁ 5) ^ 2 - 2 * c₂ ^ 2 * y₁ 5 + 2 * c₂ ^ 3))) := by
    rw [lastQ_eq, lastZ_eq, y₁5_eq, y₂5_eq]
    simp only [q₁, U, T]
    have := coord_nonzero 2
    have := coord_nonzero 3
    field_simp
    ring
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem u_eq_of_r (hr : r = (y₂ 5)⁻¹) : u = 2 * (c₂ ^ 5 - q₂ ^ 5) * (y₂ 5) ^ 2 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hy : y₂ 5 ≠ 0 := monomial_nonzero _
  rw [q₂_fifth, hr]
  field_simp
  linear_combination -u * h5

theorem x2_field (i : Fin 4) :
    ConeRing.invariantCoordinates i ∈ IntermediateField.adjoin F₅ (Set.range x2) := by
  let E := IntermediateField.adjoin F₅ (Set.range x2)
  have hx (k : Fin 4) : x2 k ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_range_self k)
  have hc (k : Fin 4) : (x2 k : K) = ![c₂ ^ 5, lastQ, lastZ, y₂ 5] k := congrFun x2_coe k
  have h2c : ((2 : L) : K) = 2 := map_ofNat L.subtype 2
  have h1 : ConeRing.invariantCoordinates 1 = 2 * x2 2 := by
    apply L.subtype_injective
    simpa [hc, h2c] using q₂_eq2
  have h3 : ConeRing.invariantCoordinates 3 = (x2 3)⁻¹ := by
    apply L.subtype_injective
    simpa [hc] using r_eq2
  have h0 : ConeRing.invariantCoordinates 0 = x2 1 - x2 3 * x2 2 ^ 3 := by
    apply L.subtype_injective
    simpa [hc] using q₁_eq2
  have m1 : ConeRing.invariantCoordinates 1 ∈ E := by
    rw [h1]
    exact E.mul_mem (E.natCast_mem 2) (hx 2)
  have h2 : ConeRing.invariantCoordinates 2 =
      2 * (x2 0 - ConeRing.invariantCoordinates 1 ^ 5) * x2 3 ^ 2 := by
    apply L.subtype_injective
    simpa [hc, h2c] using u_eq_of_r r_eq2
  fin_cases i
  · change ConeRing.invariantCoordinates 0 ∈ E
    rw [h0]
    exact E.sub_mem (hx 1) (E.mul_mem (hx 3) (E.pow_mem (hx 2) 3))
  · exact m1
  · change ConeRing.invariantCoordinates 2 ∈ E
    rw [h2]
    exact E.mul_mem (E.mul_mem (E.natCast_mem 2) (E.sub_mem (hx 0) (E.pow_mem m1 5)))
      (E.pow_mem (hx 3) 2)
  · change ConeRing.invariantCoordinates 3 ∈ E
    rw [h3]
    exact E.inv_mem (hx 3)

def base2 : YBase 2 where
  A := toF₅ (quotientAtlas.ring (2 : Fin 4))
  d := 1
  x := x2
  wt := wt2
  d_ne := one_ne_zero
  d_inv := by
    rw [one_coe, inv_one]
    exact Subalgebra.one_mem _
  chart_le a := a.property
  clear c hc := ⟨0, by simpa using hc⟩
  euler_x := x2_euler
  poly_le := Algebra.adjoin_le (by
    rintro _ ⟨i, rfl⟩
    exact (powerPolynomial_le_kernel (localGenerator 5) straightLast last_independent
      last_derivatives lastRing last_polynomial_le
      (Algebra.subset_adjoin (Set.mem_range_self i))).1)
  hull_le := hull_of_straight (localGenerator 5) straightLast last_independent last_derivatives
    lastRing last_localization x2 (fun _ ↦ rfl) _ (fun a ↦
      ⟨fun h ↦ ⟨h, (field_chart_kernel 5 _).mpr a.property⟩, fun h ↦ h.1⟩)
  field_top := field_top_of_invariantCoordinates _ x2_field

/-! ### Chart `V₄`, away from `h = 0`: coordinates `(s₂, Q, H, y)`, weights `(0, -1, -2, -1)` -/

abbrev h₀ : K := middleDenominator 0

theorem middleSlice_zero : middleSlice 0 = c₂ := by simp [middleSlice]

theorem h₀_eq : h₀ = 1 + 3 * c₂ * y₂ 3 := by
  simp only [h₀, middleDenominator, middleSlice_zero]

theorem h₀_ne : h₀ ≠ 0 := middle_denominator_nonzero 0

theorem y₁3_eq : y₁ 3 = t⁻¹ := by simp [y₁, first, monomial]

theorem y₂3_eq : y₂ 3 = w / t ^ 2 := by
  simp only [y₂, second, monomial]
  norm_num
  rw [div_eq_mul_inv, mul_comm]

def x1 : Fin 4 → L :=
  straightL 3 (straightMiddle 0) (middle_independent 0) (middle_derivatives 0) (middleRing 0)
    (middle_polynomial_le 0)

abbrev middleY : K := y₂ 3 / h₀

theorem x1_apply (i : Fin 4) : (x1 i : K) = powerCoordinates (straightMiddle 0) i := rfl

theorem pc_zero (v : Fin 4 → K) : powerCoordinates v 0 = v 0 ^ 5 := rfl
theorem pc_one (v : Fin 4 → K) : powerCoordinates v 1 = v 1 := rfl
theorem pc_two (v : Fin 4 → K) : powerCoordinates v 2 = v 2 := rfl
theorem pc_three (v : Fin 4 → K) : powerCoordinates v 3 = v 3 := rfl

theorem sm_zero (a : F₅) : straightMiddle a 0 = middleSlice a := rfl
theorem sm_one (a : F₅) : straightMiddle a 1 = c₁ - middleSlice a * y₁ 3 +
    2 * (middleSlice a) ^ 2 * y₁ 3 * y₂ 3 + 2 * (middleSlice a) ^ 3 * y₁ 3 * (y₂ 3) ^ 2 := rfl
theorem sm_two (a : F₅) : straightMiddle a 2 = y₁ 3 * (middleDenominator a) ^ 2 := rfl
theorem sm_three (a : F₅) : straightMiddle a 3 = y₂ 3 / middleDenominator a := rfl

theorem x1_zero : (x1 0 : K) = c₂ ^ 5 := by rw [x1_apply, pc_zero, sm_zero, middleSlice_zero]
theorem x1_one : (x1 1 : K) = middleQ := by rw [x1_apply, pc_one, sm_one, middleSlice_zero, middleQ]
theorem x1_two : (x1 2 : K) = middleH := by
  rw [x1_apply, pc_two, sm_two, show middleDenominator 0 = 1 + 3 * c₂ * y₂ 3 from h₀_eq, middleH]
theorem x1_three : (x1 3 : K) = middleY := by rw [x1_apply, pc_three, sm_three]

theorem x1_coe (k : Fin 4) : (x1 k : K) = ![c₂ ^ 5, middleQ, middleH, middleY] k := by
  fin_cases k
  · exact x1_zero
  · exact x1_one
  · exact x1_two
  · exact x1_three

def wt1 : Fin 4 → ℤ := ![0, -1, -2, -1]

theorem euler_h₀ : euler h₀ = 0 := by
  have h3 : euler (3 : K) = 0 := euler.map_natCast 3
  rw [h₀_eq]
  simp only [map_add, Derivation.leibniz, euler_c₂, euler_middle_second, h3,
    Derivation.map_one_eq_zero, smul_eq_mul]
  ring

theorem euler_middleY : euler middleY = -middleY := by
  have := h₀_ne
  rw [middleY, Derivation.leibniz_div, euler_h₀, euler_middle_second]
  simp only [smul_eq_mul, smul_zero, sub_zero]
  field_simp
  ring

theorem x1_euler (i : Fin 4) : invariantEuler (x1 i) = (wt1 i : L) * x1 i := by
  apply invariantEuler_of_K
  rw [x1_coe i]
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  fin_cases i
  · simp [wt1, h5]
  · change euler middleQ = ((-1 : ℤ) : K) * middleQ
    rw [euler_middleQ]
    simp
  · change euler middleH = ((-2 : ℤ) : K) * middleH
    rw [euler_middleH]
    simp
  · change euler middleY = ((-1 : ℤ) : K) * middleY
    rw [euler_middleY]
    simp

theorem q₂_eq1 : q₂ = 2 / middleY := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hh := h₀_ne
  have hη : y₂ 3 ≠ 0 := monomial_nonzero _
  have h : q₂ - 2 / middleY = 5 * (-(c₂ + t ^ 2 / w)) := by
    rw [middleY, div_div_eq_mul_div, h₀_eq, y₂3_eq]
    simp only [q₂, U, T]
    have := coord_nonzero 2
    have := coord_nonzero 3
    field_simp
    ring
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem τ_eq1 : y₂ 5 = middleH * middleY ^ 2 := by
  have hh := h₀_ne
  rw [middleH, middleY, ← h₀_eq, y₁3_eq, y₂3_eq, y₂5_eq]
  have := coord_nonzero 2
  field_simp

theorem q₁_eq1 : q₁ = middleQ - 2 * q₂ ^ 3 * y₂ 5 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : q₁ - (middleQ - 2 * q₂ ^ 3 * y₂ 5) =
      5 * (-(-11 * c₂ * t⁻¹ + 4 * c₂ ^ 2 * t⁻¹ * (w / t ^ 2) + 11 * t⁻¹ * (t ^ 2 / w))) := by
    rw [middleQ, y₁3_eq, y₂3_eq, y₂5_eq]
    simp only [q₁, q₂, U, T]
    have := coord_nonzero 2
    have := coord_nonzero 3
    field_simp
    ring
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

theorem x1_field (i : Fin 4) :
    ConeRing.invariantCoordinates i ∈ IntermediateField.adjoin F₅ (Set.range x1) := by
  let E := IntermediateField.adjoin F₅ (Set.range x1)
  have hx (k : Fin 4) : x1 k ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_range_self k)
  have hc := x1_coe
  have h2c : ((2 : L) : K) = 2 := map_ofNat L.subtype 2
  have h1 : ConeRing.invariantCoordinates 1 = 2 / x1 3 := by
    apply L.subtype_injective
    simpa [hc, h2c] using q₂_eq1
  have m1 : ConeRing.invariantCoordinates 1 ∈ E := by
    rw [h1]
    exact E.div_mem (E.natCast_mem 2) (hx 3)
  have h0 : ConeRing.invariantCoordinates 0 = x1 1 -
      2 * ConeRing.invariantCoordinates 1 ^ 3 * (x1 2 * x1 3 ^ 2) := by
    apply L.subtype_injective
    have := q₁_eq1
    rw [τ_eq1] at this
    simpa [hc, h2c] using this
  have h3 : ConeRing.invariantCoordinates 3 = (x1 2 * x1 3 ^ 2)⁻¹ := by
    apply L.subtype_injective
    have := r_eq2
    rw [τ_eq1] at this
    simpa [hc] using this
  have h2 : ConeRing.invariantCoordinates 2 =
      2 * (x1 0 - ConeRing.invariantCoordinates 1 ^ 5) * (x1 2 * x1 3 ^ 2) ^ 2 := by
    apply L.subtype_injective
    have := u_eq_of_r r_eq2
    rw [τ_eq1] at this
    simpa [hc, h2c] using this
  have mτ : x1 2 * x1 3 ^ 2 ∈ E := E.mul_mem (hx 2) (E.pow_mem (hx 3) 2)
  fin_cases i
  · change ConeRing.invariantCoordinates 0 ∈ E
    rw [h0]
    exact E.sub_mem (hx 1) (E.mul_mem (E.mul_mem (E.natCast_mem 2) (E.pow_mem m1 3)) mτ)
  · exact m1
  · change ConeRing.invariantCoordinates 2 ∈ E
    rw [h2]
    exact E.mul_mem (E.mul_mem (E.natCast_mem 2) (E.sub_mem (hx 0) (E.pow_mem m1 5)))
      (E.pow_mem mτ 2)
  · change ConeRing.invariantCoordinates 3 ∈ E
    rw [h3]
    exact E.inv_mem mτ

theorem h₀_mem_chart : h₀ ∈ contractedAtlas.ring (1 : Fin 4) := middle_denominator_mem 0

/-- The invariant denominator `h⁵` on the middle chart. -/
def middleD : yAtlas.ring (1 : Fin 4) := yFrob 1 ⟨h₀, h₀_mem_chart⟩

theorem middleD_coe : (((middleD : yAtlas.ring (1 : Fin 4)) : M) : L).1 = h₀ ^ 5 := rfl

/-- The ring of the open `h ≠ 0`, as an `F₅`-subalgebra of `L`. -/
def middleOpen : Subalgebra F₅ L :=
  (kernelIn (localGenerator 3) (middleRing 0)).comap ConeRing.invariantInclusion

theorem mem_middleOpen (a : L) : a ∈ middleOpen ↔ (a : K) ∈ middleRing 0 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, (field_chart_kernel 3 _).mpr a.property⟩⟩

theorem h₀_inv_mem : h₀⁻¹ ∈ middleRing 0 :=
  (show Algebra.adjoin F₅ {(middleDenominator 0)⁻¹} ≤ middleRing 0 from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_singleton _))

theorem middle_clear (c : L) (hc : c ∈ middleOpen) :
    ∃ n : ℕ, c * (((middleD : yAtlas.ring (1 : Fin 4)) : M) : L) ^ n ∈
      quotientAtlas.ring (1 : Fin 4) := by
  have hc' : (c : K) ∈ middleRing 0 := (mem_middleOpen c).mp hc
  let d : middleOriginal := ⟨middleDenominator 0, middle_denominator_mem 0⟩
  obtain ⟨n, hn⟩ := adjoin_inverse_denominators middleOriginal d h₀_ne hc'
  refine ⟨n, ?_⟩
  change (c : K) * (h₀ ^ 5) ^ n ∈ chartRing 3
  have he : (c : K) * (h₀ ^ 5) ^ n = ((c : K) * h₀ ^ n) * h₀ ^ (4 * n) := by
    rw [← pow_mul, show 5 * n = n + 4 * n by omega, pow_add, mul_assoc]
  rw [he]
  exact (chartRing 3).mul_mem hn ((chartRing 3).pow_mem (middle_denominator_mem 0) _)

def base1 : YBase 1 where
  A := middleOpen
  d := middleD
  x := x1
  wt := wt1
  d_ne := by
    intro h
    exact pow_ne_zero 5 h₀_ne (congrArg Subtype.val h)
  d_inv := by
    apply (mem_middleOpen _).mpr
    change (h₀ ^ 5)⁻¹ ∈ middleRing 0
    rw [← inv_pow]
    exact (middleRing 0).pow_mem h₀_inv_mem 5
  chart_le a := (mem_middleOpen _).mpr
    ((show (chartRing 3).restrictScalars F₅ ≤ middleRing 0 from le_sup_left) a.property)
  clear := middle_clear
  euler_x := x1_euler
  poly_le := Algebra.adjoin_le (by
    rintro _ ⟨i, rfl⟩
    exact powerPolynomial_le_kernel (localGenerator 3) (straightMiddle 0) (middle_independent 0)
      (middle_derivatives 0) (middleRing 0) (middle_polynomial_le 0)
      (Algebra.subset_adjoin (Set.mem_range_self i)))
  hull_le := hull_of_straight (localGenerator 3) (straightMiddle 0) (middle_independent 0)
    (middle_derivatives 0) (middleRing 0) (middle_localization 0) x1 (fun _ ↦ rfl) _
    (fun _ ↦ Iff.rfl)
  field_top := field_top_of_invariantCoordinates _ x1_field

/-! ### The cone chart: coordinates `(q₁, q₂, u, r)` with weights `(-1, 1, -3, 4)` -/

abbrev x3 : Fin 4 → L := ConeRing.invariantCoordinates

def wt3 : Fin 4 → ℤ := ![-1, 1, -3, 4]

theorem x3_euler (i : Fin 4) : invariantEuler (x3 i) = (wt3 i : L) * x3 i := by
  apply invariantEuler_of_K
  rw [ConeRing.invariantCoordinates_coe i]
  fin_cases i
  · change euler q₁ = ((-1 : ℤ) : K) * q₁
    rw [euler_special_coordinate]
    simp
  · change euler q₂ = ((1 : ℤ) : K) * q₂
    rw [euler_special_second]
    simp
  · change euler u = ((-3 : ℤ) : K) * u
    rw [show u = U from rfl, euler_U]
    simp
  · change euler r = ((4 : ℤ) : K) * r
    rw [euler_r]
    simp

abbrev coneA₃ : Subalgebra F₅ L := toF₅ (quotientAtlas.ring (3 : Fin 4))

theorem mem_coneA₃ (a : L) : a ∈ coneA₃ ↔ (a : K) ∈ coneRing := Iff.rfl

theorem x3_mem (i : Fin 4) : x3 i ∈ coneA₃ := by
  apply (mem_coneA₃ _).mpr
  rw [ConeRing.invariantCoordinates_coe i]
  have hc : c₂ ∈ coneRing := contracted_c₂_mem (3 : Fin 4)
  fin_cases i
  · exact certificate_mem (3 : Fin 4) (1 : Fin 3)
  · change q₂ ∈ coneRing
    have hz : U * T ^ 2 ∈ coneRing := by
      simpa [coneExponent, monomial, U, T, mul_comm] using cone_generator_mem 2
    have he : q₂ = c₂ - 3 * (U * T ^ 2) := by simp only [q₂]; ring
    rw [he]
    exact coneRing.sub_mem hc (coneRing.mul_mem (coneRing.natCast_mem 3) hz)
  · exact certificate_mem (3 : Fin 4) (0 : Fin 3)
  · change r ∈ coneRing
    have hm : monomial (5, -2) ∈ coneRing := cone_generator_mem 3
    have he : r = monomial (5, -2) := by
      simp only [r, U, T, monomial]
      norm_num
      rw [mul_comm]
    rw [he]
    exact hm

theorem x3_poly_le : polynomialRing (F := F₅) x3 ≤ coneA₃ :=
  Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact x3_mem i)

abbrev coneHull : Subalgebra F₅ L := hull (polynomialRing (F := F₅) x3) coneA₃

theorem x3_mem_hull (i : Fin 4) : x3 i ∈ coneHull :=
  le_hull _ _ (Algebra.subset_adjoin (Set.mem_range_self i))

theorem cone_generator_hull (i : Fin 4) :
    ConeRing.localFrobeniusInField (ConeRing.localGenerator i) ∈ coneHull := by
  have he : ConeRing.localFrobeniusInField (ConeRing.localGenerator i) =
      ![x3 2 ^ 5, x3 2 ^ 3 * x3 3, x3 2 * x3 3 ^ 2, x3 3 ^ 5] i := by
    apply Subtype.ext
    simp only [ConeRing.localFrobeniusInField_coe, ConeRing.localGenerator_embedding]
    fin_cases i <;> simp [ConeRing.invariantCoordinates_coe, u, r] <;> ring
  rw [he]
  have h := x3_mem_hull
  fin_cases i
  · exact coneHull.pow_mem (h 2) 5
  · exact coneHull.mul_mem (coneHull.pow_mem (h 2) 3) (h 3)
  · exact coneHull.mul_mem (h 2) (coneHull.pow_mem (h 3) 2)
  · exact coneHull.pow_mem (h 3) 5

theorem scalar_variable_hull (i : Fin 2) :
    ConeRing.invariantScalarFrobenius (c i) ∈ coneHull := by
  have he : ConeRing.invariantScalarFrobenius (c i) =
      ![x3 0 ^ 5 + x3 2 ^ 3 * x3 3, x3 1 ^ 5 + 3 * x3 2 * x3 3 ^ 2] i := by
    apply Subtype.ext
    rw [ConeRing.invariantScalarFrobenius_coe, map_pow]
    have h3 : ((3 : L) : K) = 3 := map_ofNat L.subtype 3
    fin_cases i <;>
      simp [includeK_c, ConeRing.invariantCoordinates_coe, q₁_fifth, q₂_fifth, h3]
  rw [he]
  have h := x3_mem_hull
  fin_cases i
  · exact coneHull.add_mem (coneHull.pow_mem (h 0) 5)
      (coneHull.mul_mem (coneHull.pow_mem (h 2) 3) (h 3))
  · exact coneHull.add_mem (coneHull.pow_mem (h 1) 5)
      (coneHull.mul_mem (coneHull.mul_mem (coneHull.natCast_mem 3) (h 2))
        (coneHull.pow_mem (h 3) 2))

theorem scalar_polynomial_hull (p : P₂) :
    ConeRing.invariantScalarFrobenius (algebraMap P₂ k p) ∈ coneHull := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    change ConeRing.invariantScalarFrobenius
      (algebraMap P₂ k (algebraMap F₅ P₂ a)) ∈ coneHull
    rw [← IsScalarTower.algebraMap_apply F₅ P₂ k]
    have he : ConeRing.invariantScalarFrobenius.comp (algebraMap F₅ k) = algebraMap F₅ L :=
      Subsingleton.elim _ _
    rw [show ConeRing.invariantScalarFrobenius (algebraMap F₅ k a) = algebraMap F₅ L a from
      RingHom.congr_fun he a]
    exact coneHull.algebraMap_mem a
  | add p q hp hq =>
    simpa only [map_add] using coneHull.add_mem hp hq
  | mul_X p i hp =>
    simp only [map_mul]
    exact coneHull.mul_mem hp (scalar_variable_hull i)

theorem scalar_mem_hull (a : k) : ConeRing.invariantScalarFrobenius a ∈ coneHull := by
  apply fractionMap_mem_hull x3_poly_le ConeRing.invariantScalarFrobenius scalar_polynomial_hull
  intro x
  apply (mem_coneA₃ _).mpr
  rw [ConeRing.invariantScalarFrobenius_coe]
  exact coneRing.algebraMap_mem (x ^ 5)

theorem cone_frobenius_hull (a : ConeRing.A) :
    ConeRing.localFrobeniusInField (algebraMap ConeRing.A ConeRing.R a) ∈ coneHull := by
  let f := ConeRing.localFrobeniusInField.comp (algebraMap ConeRing.A ConeRing.R)
  let T : Subalgebra k ConeRing.A :=
    { carrier := {x | f x ∈ coneHull}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change f (x + y) ∈ coneHull
        rw [RingHom.map_add]
        exact coneHull.add_mem hx hy
      mul_mem' := by
        intro x y hx hy
        change f (x * y) ∈ coneHull
        rw [map_mul]
        exact coneHull.mul_mem hx hy
      algebraMap_mem' := fun a ↦ by
        change f (algebraMap k ConeRing.A a) ∈ coneHull
        dsimp only [f, RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply k ConeRing.A ConeRing.R,
          ConeRing.localFrobenius_coefficient]
        exact scalar_mem_hull a }
  have hgen : Algebra.adjoin k (Set.range ConeRing.ag) ≤ T := by
    apply Algebra.adjoin_le
    rintro x ⟨i, rfl⟩
    exact cone_generator_hull i
  rw [show Algebra.adjoin k (Set.range ConeRing.ag) = ⊤ from
    TruncatedCone.subtype_generators_top ConeRing.generator] at hgen
  exact hgen (Set.mem_univ a)

theorem coneA₃_le_hull : coneA₃ ≤ coneHull := by
  have : IsIntegrallyClosed (polynomialRing (F := F₅) x3) :=
    ConeRing.invariantPolynomial_isIntegrallyClosed
  have : IsFractionRing (polynomialRing (F := F₅) x3) L :=
    ConeRing.invariantPolynomial_fractionField
  intro x hx
  obtain ⟨a, ha⟩ := (mem_coneA₃ x).mp hx
  apply mem_hull_of_pow_mem (polynomialRing (F := F₅) x3) coneA₃ (n := 5) (by decide)
  have he : x ^ 5 = ConeRing.localFrobeniusInField (algebraMap ConeRing.A ConeRing.R a) := by
    apply Subtype.ext
    rw [ConeRing.localFrobeniusInField_coe, ConeRing.localEmbed_algebraMap]
    change (x : K) ^ 5 = (ConeRing.embed a) ^ 5
    rw [show ConeRing.embed a = (x : K) from ha]
  rw [he]
  exact cone_frobenius_hull a

def base3 : YBase 3 where
  A := coneA₃
  d := 1
  x := x3
  wt := wt3
  d_ne := one_ne_zero
  d_inv := by
    rw [one_coe, inv_one]
    exact Subalgebra.one_mem _
  chart_le a := a.property
  clear c hc := ⟨0, by simpa using hc⟩
  euler_x := x3_euler
  poly_le := x3_poly_le
  hull_le := coneA₃_le_hull
  field_top := ConeRing.invariantCoordinates_field_generation

end
end Eff

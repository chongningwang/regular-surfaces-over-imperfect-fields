import Geonormal.P11.Differentials

/-! # Differentials at the point `P₀`

The coordinates `ξ₀, ξ₁` of the chart `P` generate the maximal ideal at `P₀`, and the other
`ξ_n` lie in its square: the components of `x' = Σ ξ_n γ^n` satisfy
`(m+1)(m+2) ξ_{m+2} = 6 (Σ_{i+j=m} ξ_i ξ_j + c Σ_{i+j=m+11} ξ_i ξ_j)`, the `γ^m`-coefficient of
`D²x' = 6x'²`. So `dc, dξ₀, dξ₁` span `Ω ⊗ κ(P₀)`, and by Nakayama they span the differentials
on a principal open around `P₀`.

The volume: through `ι`, the bracket `det(dc, df, dg) / (da ∧ db ∧ dσ)` of `f, g ∈ L` becomes
half the Jacobian `∂(ιf, ιg)/∂(x', y')`; this is checked on `a, b, σ` and extended by the chain
rule. For `f, g = ξ₀, ξ₁` the Jacobian is `∂(r₀, r₁)/∂(x', y')`, which is `2` at `P₀`.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial Module IsLocalRing

noncomputable section

/-! ## Elements of the chart `P` -/

/-- The constant `c` in the chart `P`. -/
abbrev cPt : chartP := algebraMap k chartP c

theorem coe_cP : (cPt : L) = cL := algebraMap_c_L

theorem coe_ξP (n : Fin 11) : (ξP n : L) = ξ n := rfl

theorem coe_ofNat_P (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : chartP) : L) = OfNat.ofNat n :=
  map_ofNat chartP.val n

theorem isUnit_ofNat_P (n : ℕ) [n.AtLeastTwo] (h : ¬ 11 ∣ n) : IsUnit (OfNat.ofNat n : chartP) := by
  have hn : (n : F₁₁) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have : (OfNat.ofNat n : chartP) = algebraMap F₁₁ chartP (n : F₁₁) := by rw [map_natCast]; rfl
  rw [this]
  exact (Ne.isUnit hn).map _

theorem ξP_mem (n : Fin 11) : ξP n ∈ 𝔪₀ := by
  change constantCoeff (ιS (ξP n)) = 0
  rw [ιS_ξ]
  fin_cases n <;> simp [rK, rE, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]

theorem sqm (i j : Fin 11) : ξP i * ξP j ∈ 𝔪₀ ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (ξP_mem i) (ξP_mem j)

/-! ## The relations `E_m` -/

set_option maxHeartbeats 4000000 in
theorem E0 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (2 : R) * r2 g x y = 6 * (r0 g x y * r0 g x y + g ^ 11 * (r1 g x y * r10 g x y + r2 g x y * r9 g x y + r3 g x y * r8 g x y + r4 g x y * r7 g x y + r5 g x y * r6 g x y + r6 g x y * r5 g x y + r7 g x y * r4 g x y + r8 g x y * r3 g x y + r9 g x y * r2 g x y + r10 g x y * r1 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E1 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (6 : R) * r3 g x y = 6 * (r0 g x y * r1 g x y + r1 g x y * r0 g x y + g ^ 11 * (r2 g x y * r10 g x y + r3 g x y * r9 g x y + r4 g x y * r8 g x y + r5 g x y * r7 g x y + r6 g x y * r6 g x y + r7 g x y * r5 g x y + r8 g x y * r4 g x y + r9 g x y * r3 g x y + r10 g x y * r2 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E2 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (12 : R) * r4 g x y = 6 * (r0 g x y * r2 g x y + r1 g x y * r1 g x y + r2 g x y * r0 g x y + g ^ 11 * (r3 g x y * r10 g x y + r4 g x y * r9 g x y + r5 g x y * r8 g x y + r6 g x y * r7 g x y + r7 g x y * r6 g x y + r8 g x y * r5 g x y + r9 g x y * r4 g x y + r10 g x y * r3 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E3 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (20 : R) * r5 g x y = 6 * (r0 g x y * r3 g x y + r1 g x y * r2 g x y + r2 g x y * r1 g x y + r3 g x y * r0 g x y + g ^ 11 * (r4 g x y * r10 g x y + r5 g x y * r9 g x y + r6 g x y * r8 g x y + r7 g x y * r7 g x y + r8 g x y * r6 g x y + r9 g x y * r5 g x y + r10 g x y * r4 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E4 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (30 : R) * r6 g x y = 6 * (r0 g x y * r4 g x y + r1 g x y * r3 g x y + r2 g x y * r2 g x y + r3 g x y * r1 g x y + r4 g x y * r0 g x y + g ^ 11 * (r5 g x y * r10 g x y + r6 g x y * r9 g x y + r7 g x y * r8 g x y + r8 g x y * r7 g x y + r9 g x y * r6 g x y + r10 g x y * r5 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E5 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (42 : R) * r7 g x y = 6 * (r0 g x y * r5 g x y + r1 g x y * r4 g x y + r2 g x y * r3 g x y + r3 g x y * r2 g x y + r4 g x y * r1 g x y + r5 g x y * r0 g x y + g ^ 11 * (r6 g x y * r10 g x y + r7 g x y * r9 g x y + r8 g x y * r8 g x y + r9 g x y * r7 g x y + r10 g x y * r6 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E6 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (56 : R) * r8 g x y = 6 * (r0 g x y * r6 g x y + r1 g x y * r5 g x y + r2 g x y * r4 g x y + r3 g x y * r3 g x y + r4 g x y * r2 g x y + r5 g x y * r1 g x y + r6 g x y * r0 g x y + g ^ 11 * (r7 g x y * r10 g x y + r8 g x y * r9 g x y + r9 g x y * r8 g x y + r10 g x y * r7 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E7 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (72 : R) * r9 g x y = 6 * (r0 g x y * r7 g x y + r1 g x y * r6 g x y + r2 g x y * r5 g x y + r3 g x y * r4 g x y + r4 g x y * r3 g x y + r5 g x y * r2 g x y + r6 g x y * r1 g x y + r7 g x y * r0 g x y + g ^ 11 * (r8 g x y * r10 g x y + r9 g x y * r9 g x y + r10 g x y * r8 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

set_option maxHeartbeats 4000000 in
theorem E8 {R : Type*} [CommRing R] [CharP R 11] (g x y : R) :
    (90 : R) * r10 g x y = 6 * (r0 g x y * r8 g x y + r1 g x y * r7 g x y + r2 g x y * r6 g x y + r3 g x y * r5 g x y + r4 g x y * r4 g x y + r5 g x y * r3 g x y + r6 g x y * r2 g x y + r7 g x y * r1 g x y + r8 g x y * r0 g x y + g ^ 11 * (r9 g x y * r10 g x y + r10 g x y * r9 g x y)) := by
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  grind (ringSteps := 1000000)

theorem relL0 : (2 : L) * ξ 2 = 6 * (ξ 0 * ξ 0 + cL * (ξ 1 * ξ 10 + ξ 2 * ξ 9 + ξ 3 * ξ 8 + ξ 4 * ξ 7 + ξ 5 * ξ 6 + ξ 6 * ξ 5 + ξ 7 * ξ 4 + ξ 8 * ξ 3 + ξ 9 * ξ 2 + ξ 10 * ξ 1)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E0 γK xK yK

theorem ξsq2 : ξP 2 ∈ 𝔪₀ ^ 2 := by
  have hrel : (2 : chartP) * ξP 2 = 6 * (ξP 0 * ξP 0 + cPt * (ξP 1 * ξP 10 + ξP 2 * ξP 9 + ξP 3 * ξP 8 + ξP 4 * ξP 7 + ξP 5 * ξP 6 + ξP 6 * ξP 5 + ξP 7 * ξP 4 + ξP 8 * ξP 3 + ξP 9 * ξP 2 + ξP 10 * ξP 1)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL0)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 2 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (sqm 0 0) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 1 10) (sqm 2 9)) (sqm 3 8)) (sqm 4 7)) (sqm 5 6)) (sqm 6 5)) (sqm 7 4)) (sqm 8 3)) (sqm 9 2)) (sqm 10 1))))

theorem relL1 : (6 : L) * ξ 3 = 6 * (ξ 0 * ξ 1 + ξ 1 * ξ 0 + cL * (ξ 2 * ξ 10 + ξ 3 * ξ 9 + ξ 4 * ξ 8 + ξ 5 * ξ 7 + ξ 6 * ξ 6 + ξ 7 * ξ 5 + ξ 8 * ξ 4 + ξ 9 * ξ 3 + ξ 10 * ξ 2)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E1 γK xK yK

theorem ξsq3 : ξP 3 ∈ 𝔪₀ ^ 2 := by
  have hrel : (6 : chartP) * ξP 3 = 6 * (ξP 0 * ξP 1 + ξP 1 * ξP 0 + cPt * (ξP 2 * ξP 10 + ξP 3 * ξP 9 + ξP 4 * ξP 8 + ξP 5 * ξP 7 + ξP 6 * ξP 6 + ξP 7 * ξP 5 + ξP 8 * ξP 4 + ξP 9 * ξP 3 + ξP 10 * ξP 2)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL1)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 6 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 1) (sqm 1 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 2 10) (sqm 3 9)) (sqm 4 8)) (sqm 5 7)) (sqm 6 6)) (sqm 7 5)) (sqm 8 4)) (sqm 9 3)) (sqm 10 2))))

theorem relL2 : (12 : L) * ξ 4 = 6 * (ξ 0 * ξ 2 + ξ 1 * ξ 1 + ξ 2 * ξ 0 + cL * (ξ 3 * ξ 10 + ξ 4 * ξ 9 + ξ 5 * ξ 8 + ξ 6 * ξ 7 + ξ 7 * ξ 6 + ξ 8 * ξ 5 + ξ 9 * ξ 4 + ξ 10 * ξ 3)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E2 γK xK yK

theorem ξsq4 : ξP 4 ∈ 𝔪₀ ^ 2 := by
  have hrel : (12 : chartP) * ξP 4 = 6 * (ξP 0 * ξP 2 + ξP 1 * ξP 1 + ξP 2 * ξP 0 + cPt * (ξP 3 * ξP 10 + ξP 4 * ξP 9 + ξP 5 * ξP 8 + ξP 6 * ξP 7 + ξP 7 * ξP 6 + ξP 8 * ξP 5 + ξP 9 * ξP 4 + ξP 10 * ξP 3)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL2)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 12 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 2) (sqm 1 1)) (sqm 2 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 3 10) (sqm 4 9)) (sqm 5 8)) (sqm 6 7)) (sqm 7 6)) (sqm 8 5)) (sqm 9 4)) (sqm 10 3))))

theorem relL3 : (20 : L) * ξ 5 = 6 * (ξ 0 * ξ 3 + ξ 1 * ξ 2 + ξ 2 * ξ 1 + ξ 3 * ξ 0 + cL * (ξ 4 * ξ 10 + ξ 5 * ξ 9 + ξ 6 * ξ 8 + ξ 7 * ξ 7 + ξ 8 * ξ 6 + ξ 9 * ξ 5 + ξ 10 * ξ 4)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E3 γK xK yK

theorem ξsq5 : ξP 5 ∈ 𝔪₀ ^ 2 := by
  have hrel : (20 : chartP) * ξP 5 = 6 * (ξP 0 * ξP 3 + ξP 1 * ξP 2 + ξP 2 * ξP 1 + ξP 3 * ξP 0 + cPt * (ξP 4 * ξP 10 + ξP 5 * ξP 9 + ξP 6 * ξP 8 + ξP 7 * ξP 7 + ξP 8 * ξP 6 + ξP 9 * ξP 5 + ξP 10 * ξP 4)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL3)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 20 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 3) (sqm 1 2)) (sqm 2 1)) (sqm 3 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 4 10) (sqm 5 9)) (sqm 6 8)) (sqm 7 7)) (sqm 8 6)) (sqm 9 5)) (sqm 10 4))))

theorem relL4 : (30 : L) * ξ 6 = 6 * (ξ 0 * ξ 4 + ξ 1 * ξ 3 + ξ 2 * ξ 2 + ξ 3 * ξ 1 + ξ 4 * ξ 0 + cL * (ξ 5 * ξ 10 + ξ 6 * ξ 9 + ξ 7 * ξ 8 + ξ 8 * ξ 7 + ξ 9 * ξ 6 + ξ 10 * ξ 5)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E4 γK xK yK

theorem ξsq6 : ξP 6 ∈ 𝔪₀ ^ 2 := by
  have hrel : (30 : chartP) * ξP 6 = 6 * (ξP 0 * ξP 4 + ξP 1 * ξP 3 + ξP 2 * ξP 2 + ξP 3 * ξP 1 + ξP 4 * ξP 0 + cPt * (ξP 5 * ξP 10 + ξP 6 * ξP 9 + ξP 7 * ξP 8 + ξP 8 * ξP 7 + ξP 9 * ξP 6 + ξP 10 * ξP 5)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL4)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 30 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 4) (sqm 1 3)) (sqm 2 2)) (sqm 3 1)) (sqm 4 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 5 10) (sqm 6 9)) (sqm 7 8)) (sqm 8 7)) (sqm 9 6)) (sqm 10 5))))

theorem relL5 : (42 : L) * ξ 7 = 6 * (ξ 0 * ξ 5 + ξ 1 * ξ 4 + ξ 2 * ξ 3 + ξ 3 * ξ 2 + ξ 4 * ξ 1 + ξ 5 * ξ 0 + cL * (ξ 6 * ξ 10 + ξ 7 * ξ 9 + ξ 8 * ξ 8 + ξ 9 * ξ 7 + ξ 10 * ξ 6)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E5 γK xK yK

theorem ξsq7 : ξP 7 ∈ 𝔪₀ ^ 2 := by
  have hrel : (42 : chartP) * ξP 7 = 6 * (ξP 0 * ξP 5 + ξP 1 * ξP 4 + ξP 2 * ξP 3 + ξP 3 * ξP 2 + ξP 4 * ξP 1 + ξP 5 * ξP 0 + cPt * (ξP 6 * ξP 10 + ξP 7 * ξP 9 + ξP 8 * ξP 8 + ξP 9 * ξP 7 + ξP 10 * ξP 6)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL5)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 42 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 5) (sqm 1 4)) (sqm 2 3)) (sqm 3 2)) (sqm 4 1)) (sqm 5 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 6 10) (sqm 7 9)) (sqm 8 8)) (sqm 9 7)) (sqm 10 6))))

theorem relL6 : (56 : L) * ξ 8 = 6 * (ξ 0 * ξ 6 + ξ 1 * ξ 5 + ξ 2 * ξ 4 + ξ 3 * ξ 3 + ξ 4 * ξ 2 + ξ 5 * ξ 1 + ξ 6 * ξ 0 + cL * (ξ 7 * ξ 10 + ξ 8 * ξ 9 + ξ 9 * ξ 8 + ξ 10 * ξ 7)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E6 γK xK yK

theorem ξsq8 : ξP 8 ∈ 𝔪₀ ^ 2 := by
  have hrel : (56 : chartP) * ξP 8 = 6 * (ξP 0 * ξP 6 + ξP 1 * ξP 5 + ξP 2 * ξP 4 + ξP 3 * ξP 3 + ξP 4 * ξP 2 + ξP 5 * ξP 1 + ξP 6 * ξP 0 + cPt * (ξP 7 * ξP 10 + ξP 8 * ξP 9 + ξP 9 * ξP 8 + ξP 10 * ξP 7)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL6)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 56 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 6) (sqm 1 5)) (sqm 2 4)) (sqm 3 3)) (sqm 4 2)) (sqm 5 1)) (sqm 6 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 7 10) (sqm 8 9)) (sqm 9 8)) (sqm 10 7))))

theorem relL7 : (72 : L) * ξ 9 = 6 * (ξ 0 * ξ 7 + ξ 1 * ξ 6 + ξ 2 * ξ 5 + ξ 3 * ξ 4 + ξ 4 * ξ 3 + ξ 5 * ξ 2 + ξ 6 * ξ 1 + ξ 7 * ξ 0 + cL * (ξ 8 * ξ 10 + ξ 9 * ξ 9 + ξ 10 * ξ 8)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E7 γK xK yK

theorem ξsq9 : ξP 9 ∈ 𝔪₀ ^ 2 := by
  have hrel : (72 : chartP) * ξP 9 = 6 * (ξP 0 * ξP 7 + ξP 1 * ξP 6 + ξP 2 * ξP 5 + ξP 3 * ξP 4 + ξP 4 * ξP 3 + ξP 5 * ξP 2 + ξP 6 * ξP 1 + ξP 7 * ξP 0 + cPt * (ξP 8 * ξP 10 + ξP 9 * ξP 9 + ξP 10 * ξP 8)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL7)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 72 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 7) (sqm 1 6)) (sqm 2 5)) (sqm 3 4)) (sqm 4 3)) (sqm 5 2)) (sqm 6 1)) (sqm 7 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (Ideal.add_mem _ (sqm 8 10) (sqm 9 9)) (sqm 10 8))))

theorem relL8 : (90 : L) * ξ 10 = 6 * (ξ 0 * ξ 8 + ξ 1 * ξ 7 + ξ 2 * ξ 6 + ξ 3 * ξ 5 + ξ 4 * ξ 4 + ξ 5 * ξ 3 + ξ 6 * ξ 2 + ξ 7 * ξ 1 + ξ 8 * ξ 0 + cL * (ξ 9 * ξ 10 + ξ 10 * ξ 9)) := by
  apply ι.injective
  simp only [map_mul, map_add, map_ofNat, ι_ξ, algebraMap_rK, ι_cL, rE, Matrix.cons_val]
  linear_combination E8 γK xK yK

theorem ξsq10 : ξP 10 ∈ 𝔪₀ ^ 2 := by
  have hrel : (90 : chartP) * ξP 10 = 6 * (ξP 0 * ξP 8 + ξP 1 * ξP 7 + ξP 2 * ξP 6 + ξP 3 * ξP 5 + ξP 4 * ξP 4 + ξP 5 * ξP 3 + ξP 6 * ξP 2 + ξP 7 * ξP 1 + ξP 8 * ξP 0 + cPt * (ξP 9 * ξP 10 + ξP 10 * ξP 9)) := Subtype.ext (by
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_ofNat_P, coe_ξP, coe_cP]
    exact relL8)
  rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_ofNat_P 90 (by decide)), hrel]
  exact Ideal.mul_mem_left _ 6 (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (sqm 0 8) (sqm 1 7)) (sqm 2 6)) (sqm 3 5)) (sqm 4 4)) (sqm 5 3)) (sqm 6 2)) (sqm 7 1)) (sqm 8 0)) (Ideal.mul_mem_left _ cPt (Ideal.add_mem _ (sqm 9 10) (sqm 10 9))))

theorem ξsq (n : Fin 11) (hn : 2 ≤ (n : ℕ)) : ξP n ∈ 𝔪₀ ^ 2 := by
  fin_cases n <;> simp at hn
  exacts [ξsq2, ξsq3, ξsq4, ξsq5, ξsq6, ξsq7, ξsq8, ξsq9, ξsq10]

/-! ## Nakayama -/

set_option synthInstance.maxHeartbeats 400000 in
theorem D_mem_of_mem_sq {R : Type*} [CommRing R] [Algebra F₁₁ R] (I : Ideal R) {z : R}
    (hz : z ∈ I ^ 2) :
    KaehlerDifferential.D F₁₁ R z ∈ I • (⊤ : Submodule R (KaehlerDifferential F₁₁ R)) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
  · rw [Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul ha trivial)
      (Submodule.smul_mem_smul hb trivial)
  · rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- `Ω_{k/𝔽₁₁}` is free on `dc`. -/
def baseBasis : Basis (Fin 1) k (KaehlerDifferential F₁₁ k) :=
  polynomialLocalizationDifferentialBasis F₁₁ k (Fin 1) (nonZeroDivisors P₁)

theorem D_algebraMap_mem (T : Subalgebra k L) (μ : k) :
    KaehlerDifferential.D F₁₁ T (algebraMap k T μ) ∈
      Submodule.span T {KaehlerDifferential.D F₁₁ T (algebraMap k T c)} := by
  have hμ : KaehlerDifferential.D F₁₁ k μ =
      baseBasis.repr (KaehlerDifferential.D F₁₁ k μ) 0 • KaehlerDifferential.D F₁₁ k c := by
    conv_lhs => rw [← baseBasis.sum_repr (KaehlerDifferential.D F₁₁ k μ)]
    rw [Fin.sum_univ_one, baseBasis, polynomialLocalizationDifferentialBasis_apply]
    rfl
  have h := congrArg (KaehlerDifferential.map F₁₁ F₁₁ k T) hμ
  rw [KaehlerDifferential.map_D, LinearMap.map_smul, KaehlerDifferential.map_D] at h
  rw [h]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `dc` and the `dξ_n` span the differentials of the chart `P`. -/
def genSpan : Submodule chartP (KaehlerDifferential F₁₁ chartP) :=
  Submodule.span chartP ({KaehlerDifferential.D F₁₁ chartP cPt} ∪
    Set.range fun n ↦ KaehlerDifferential.D F₁₁ chartP (ξP n))

theorem genSpan_top : genSpan = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation F₁₁ chartP, Submodule.span_le]
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨n, rfl⟩ := hz
    exact Submodule.subset_span (Or.inr ⟨n, rfl⟩)
  | algebraMap μ =>
    exact Submodule.span_mono Set.subset_union_left (D_algebraMap_mem chartP μ)
  | add x y hx hy ihx ihy =>
    have : (⟨x + y, chartP.add_mem hx hy⟩ : chartP) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add]
    exact Submodule.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, chartP.mul_mem hx hy⟩ : chartP) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ihy) (Submodule.smul_mem _ _ ihx)

/-- The span of `dc, dξ₀, dξ₁`. -/
def N₀ : Submodule chartP (KaehlerDifferential F₁₁ chartP) :=
  Submodule.span chartP {KaehlerDifferential.D F₁₁ chartP cPt,
    KaehlerDifferential.D F₁₁ chartP (ξP 0), KaehlerDifferential.D F₁₁ chartP (ξP 1)}

set_option synthInstance.maxHeartbeats 400000 in
theorem top_le_N₀_sup : (⊤ : Submodule chartP (KaehlerDifferential F₁₁ chartP)) ≤
    N₀ ⊔ 𝔪₀ • ⊤ := by
  have hle : genSpan ≤ N₀ ⊔ 𝔪₀ • ⊤ := by
    rw [genSpan, Submodule.span_le]
    rintro _ (h | ⟨n, rfl⟩)
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · by_cases h0 : n = 0
      · subst h0
        exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
      by_cases h1 : n = 1
      · subst h1
        exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
      have hn : 2 ≤ (n : ℕ) := by
        have h0' : (n : ℕ) ≠ 0 := fun h ↦ h0 (Fin.ext h)
        have h1' : (n : ℕ) ≠ 1 := fun h ↦ h1 (Fin.ext h)
        omega
      exact Submodule.mem_sup_right (D_mem_of_mem_sq 𝔪₀ (ξsq n hn))
  rwa [genSpan_top] at hle

set_option synthInstance.maxHeartbeats 400000 in
theorem genSpan_fg : (⊤ : Submodule chartP (KaehlerDifferential F₁₁ chartP)).FG := by
  rw [← genSpan_top, genSpan]
  exact Submodule.fg_span ((Set.finite_singleton _).union (Set.finite_range _))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Nakayama: some `r ∉ 𝔪₀` multiplies all differentials into the span of `dc, dξ₀, dξ₁`. -/
theorem exists_nakayama : ∃ r : chartP, r ∉ 𝔪₀ ∧
    ∀ ω : KaehlerDifferential F₁₁ chartP, r • ω ∈ N₀ := by
  have : Module.Finite chartP (KaehlerDifferential F₁₁ chartP) := ⟨genSpan_fg⟩
  have hfg : (⊤ : Submodule chartP (KaehlerDifferential F₁₁ chartP ⧸ N₀)).FG :=
    Module.Finite.fg_top
  have hin : (⊤ : Submodule chartP (KaehlerDifferential F₁₁ chartP ⧸ N₀)) ≤ 𝔪₀ • ⊤ := by
    intro x _
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective N₀ x
    obtain ⟨n, hn, t, ht, rfl⟩ := Submodule.mem_sup.mp (top_le_N₀_sup (Submodule.mem_top (x := ω)))
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N₀).mpr hn, zero_add]
    have := Submodule.mem_map_of_mem (f := N₀.mkQ) ht
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪₀ ⊤ hfg hin
  refine ⟨r, fun hr0 ↦ ?_, fun ω ↦ ?_⟩
  · have h1 : (1 : chartP) ∈ 𝔪₀ := by simpa using 𝔪₀.sub_mem hr0 hr1
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h1)
  · have := hr (Submodule.Quotient.mk ω) Submodule.mem_top
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

/-! ## Derivations of `K'` -/

/-- `Ω_{K'/k'}` is free on `dx', dy'`. -/
def basisK' : Basis (Fin 2) K' (KaehlerDifferential k' K') :=
  polynomialLocalizationDifferentialBasis k' K' (Fin 2) (nonZeroDivisors S₂)

/-- The partial derivatives `∂/∂x', ∂/∂y'` on `K'`. -/
def px (j : Fin 2) : Derivation k' K' K' :=
  (basisK'.coord j).compDer (KaehlerDifferential.D k' K')

theorem px_X (j l : Fin 2) : px j (algebraMap S₂ K' (X l)) = if l = j then 1 else 0 := by
  change basisK'.repr (KaehlerDifferential.D k' K' (algebraMap S₂ K' (X l))) j = _
  rw [← polynomialLocalizationDifferentialBasis_apply k' K' (Fin 2) (nonZeroDivisors S₂) l]
  rw [show polynomialLocalizationDifferentialBasis k' K' (Fin 2) (nonZeroDivisors S₂) = basisK' from rfl,
    Basis.repr_self, Finsupp.single_apply]

@[simp] theorem px0x : px 0 xK = 1 := by rw [xK, px_X]; rfl
@[simp] theorem px1x : px 1 xK = 0 := by rw [xK, px_X]; rfl
@[simp] theorem px0y : px 0 yK = 0 := by rw [yK, px_X]; rfl
@[simp] theorem px1y : px 1 yK = 1 := by rw [yK, px_X]; rfl
@[simp] theorem pxγ (j : Fin 2) : px j γK = 0 := (px j).map_algebraMap γ
@[simp] theorem px_ofNat (j : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    px j (no_index (OfNat.ofNat n : K')) = 0 :=
  (px j).map_natCast (OfNat.ofNat n)

theorem px_algebraMap (j : Fin 2) (p : S₂) :
    px j (algebraMap S₂ K' p) = algebraMap S₂ K' (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [pderiv_C, map_zero, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p l hp =>
    rw [map_mul, Derivation.leibniz, hp, px_X, Derivation.leibniz, pderiv_X]
    simp only [smul_eq_mul, map_add, map_mul, Pi.single_apply]
    split_ifs <;> simp

/-- The Jacobian with respect to `x', y'`. -/
def jac (u v : K') : K' := px 0 u * px 1 v - px 1 u * px 0 v

/-! ## The chain rule along `ι` -/

theorem chain (E : Derivation F₁₁ K' K') (f : L) :
    E (ι f) = ι (pd 0 f) * E (ι aL) + ι (pd 1 f) * E (ι bL) + ι (pd 2 f) * E (ι σL) := by
  letI : Algebra L K' := ι.toAlgebra
  haveI : IsScalarTower F₁₁ L K' := IsScalarTower.of_algebraMap_eq fun r ↦
    RingHom.congr_fun (Subsingleton.elim (α := F₁₁ →+* K') (algebraMap F₁₁ K')
      ((algebraMap L K').comp (algebraMap F₁₁ L))) r
  have key (g : L) : E (ι g) = E.liftKaehlerDifferential
      (KaehlerDifferential.map F₁₁ F₁₁ L K' (KaehlerDifferential.D F₁₁ L g)) := by
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  have hz (j : Fin 3) : E.liftKaehlerDifferential (KaehlerDifferential.map F₁₁ F₁₁ L K'
      (fieldBasis j)) = E (ι (algebraMap P₃ L (X j))) := by
    rw [fieldBasis_apply, KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  rw [key f, ← fieldBasis.sum_repr (KaehlerDifferential.D F₁₁ L f), map_sum, map_sum,
    Fin.sum_univ_three]
  simp only [LinearMap.map_smul, LinearMap.map_smul_of_tower, hz, Algebra.smul_def]
  rfl

theorem chain_px (j : Fin 2) (f : L) :
    px j (ι f) = ι (pd 0 f) * px j (ι aL) + ι (pd 1 f) * px j (ι bL) +
      ι (pd 2 f) * px j (ι σL) :=
  chain ((px j).restrictScalars F₁₁) f

/-! ## The bracket on generators -/

theorem h11K : (11 : K') = 0 := by exact_mod_cast CharP.cast_eq_zero K' 11

theorem D_two {R F : Type*} [CommRing R] [Field F] [Algebra R F] (D : Derivation R F F) :
    D 2 = 0 := by
  simpa using D.map_natCast 2
theorem D_three {R F : Type*} [CommRing R] [Field F] [Algebra R F] (D : Derivation R F F) :
    D 3 = 0 := by
  simpa using D.map_natCast 3
section Gen
variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] [CharP F 11] (D₀ D₁ : Derivation R F F) (x y g : F)
  (h0x : D₀ x = 1) (h0y : D₀ y = 0) (h1x : D₁ x = 0) (h1y : D₁ y = 1) (h0g : D₀ g = 0)
  (h1g : D₁ g = 0) (hw : y ^ 2 - x ^ 3 ≠ 0)
include h0x h0y h1x h1y hw


theorem jac_ab_gen : D₀ (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) * D₁ (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) -
    D₁ (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) * D₀ (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) = 0 := by
  simp [Derivation.leibniz_div, Derivation.leibniz_pow, h0x, h0y, h1x, h1y, smul_eq_mul, D_two, D_three]
  field_simp
  grind (ringSteps := 1000000)

include h0g h1g in
theorem jac_as_gen : D₀ (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) *
    D₁ (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) -
    D₁ (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) * D₀ (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) =
    -2 * (18 * (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) * (y ^ 2 - x ^ 3)⁻¹) := by
  simp [Derivation.leibniz_div, Derivation.leibniz_pow, h0x, h0y, h1x, h1y, h0g, h1g, smul_eq_mul,
    D_two, D_three]
  field_simp
  grind (ringSteps := 1000000)

include h0g h1g in
theorem jac_bs_gen : D₀ (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) *
    D₁ (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) -
    D₁ (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) * D₀ (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) =
    2 * (6 * (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) * (y ^ 2 - x ^ 3)⁻¹) := by
  simp [Derivation.leibniz_div, Derivation.leibniz_pow, h0x, h0y, h1x, h1y, h0g, h1g, smul_eq_mul,
    D_two, D_three]
  field_simp
  grind (ringSteps := 1000000)
end Gen

@[simp] theorem pd_three (j : Fin 3) : pd j 3 = 0 := by simpa using (pd j).map_natCast 3
@[simp] theorem pd_six (j : Fin 3) : pd j 6 = 0 := by simpa using (pd j).map_natCast 6

theorem pd0c : pd 0 cL = 6 * bL * uL := by
  simp only [cL, uL, map_mul, map_sub, Derivation.leibniz, Derivation.leibniz_pow, pd_six,
    pd_three, pd0a, pd0b, pd0s, smul_eq_mul, nsmul_eq_mul]
  linear_combination (-6 * aL ^ 3 * bL) * h11L

theorem pd1c : pd 1 cL = 18 * aL * uL := by
  simp only [cL, uL, map_mul, map_sub, Derivation.leibniz, Derivation.leibniz_pow, pd_six,
    pd_three, pd1a, pd1b, pd1s, smul_eq_mul, nsmul_eq_mul]
  ring

theorem pd2c : pd 2 cL = 0 := by
  simp only [cL, map_mul, map_sub, Derivation.leibniz, Derivation.leibniz_pow, pd_six,
    pd_three, pd2a, pd2b, pd2s, smul_eq_mul, nsmul_eq_mul]
  linear_combination (-6 * σL ^ 10) * h11L

theorem jac_ab : jac (ι aL) (ι bL) = 0 := by
  rw [jac, ι_aL, ι_bL]
  exact jac_ab_gen (px 0) (px 1) xK yK px0x px0y px1x
    px1y wK_ne_zero

theorem jac_as : jac (ι aL) (ι σL) = -2 * ι (pd 1 cL) := by
  rw [pd1c, map_mul, map_mul, map_ofNat, ι_aL, ι_uL, jac, ι_σL]
  exact jac_as_gen (px 0) (px 1) xK yK γK px0x px0y
    px1x px1y (pxγ 0) (pxγ 1) wK_ne_zero

theorem jac_bs : jac (ι bL) (ι σL) = 2 * ι (pd 0 cL) := by
  rw [pd0c, map_mul, map_mul, map_ofNat, ι_bL, ι_uL, jac, ι_σL]
  exact jac_bs_gen (px 0) (px 1) xK yK γK px0x px0y
    px1x px1y (pxγ 0) (pxγ 1) wK_ne_zero

/-! ## The determinant `δ` of `dc, dξ₀, dξ₁` -/

/-- The coordinates `c, ξ₀, ξ₁` around `P₀`. -/
def vP : Fin 3 → L := ![(cPt : L), ξ 0, ξ 1]

/-- `dc ∧ dξ₀ ∧ dξ₁ = δ · da ∧ db ∧ dσ`. -/
def δP : L := fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (vP l))

/-- The Jacobian `∂(r₀, r₁)/∂(x', y')`. -/
def Jpoly : S₂ := pderiv 0 (rK 0) * pderiv 1 (rK 1) - pderiv 1 (rK 0) * pderiv 0 (rK 1)

set_option maxHeartbeats 2000000 in
theorem ι_δP : ι δP = algebraMap S₂ K' (6 * Jpoly) := by
  have hJ : algebraMap S₂ K' Jpoly = jac (ι (ξ 0)) (ι (ξ 1)) := by
    simp only [Jpoly, jac, ι_ξ, px_algebraMap, map_mul, map_sub]
  rw [map_mul, hJ, map_ofNat, δP, fieldDet_eq, Matrix.det_fin_three]
  simp only [Matrix.of_apply, vP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_mul, map_sub, map_add, coe_cP]
  have e00 := chain_px 0 (ξ 0)
  have e10 := chain_px 1 (ξ 0)
  have e01 := chain_px 0 (ξ 1)
  have e11 := chain_px 1 (ξ 1)
  have g01 := jac_ab
  have g02 := jac_as
  have g12 := jac_bs
  have c2 : ι (pd 2 cL) = 0 := by rw [pd2c, map_zero]
  simp only [jac] at g01 g02 g12 ⊢
  set A0 := ι (pd 0 (ξ 0))
  set A1 := ι (pd 1 (ξ 0))
  set A2 := ι (pd 2 (ξ 0))
  set B0 := ι (pd 0 (ξ 1))
  set B1 := ι (pd 1 (ξ 1))
  set B2 := ι (pd 2 (ξ 1))
  set C0 := ι (pd 0 cL)
  set C1 := ι (pd 1 cL)
  set C2 := ι (pd 2 cL)
  set X0 := px 0 (ι aL)
  set X1 := px 0 (ι bL)
  set X2 := px 0 (ι σL)
  set Y0 := px 1 (ι aL)
  set Y1 := px 1 (ι bL)
  set Y2 := px 1 (ι σL)
  set P00 := px 0 (ι (ξ 0))
  set P10 := px 1 (ι (ξ 0))
  set P01 := px 0 (ι (ξ 1))
  set P11 := px 1 (ι (ξ 1))
  linear_combination (-6 * P11) * e00 + (-6 * (A0 * X0 + A1 * X1 + A2 * X2)) * e11 +
    (6 * P01) * e10 + (6 * (A0 * Y0 + A1 * Y1 + A2 * Y2)) * e01 +
    (-6 * (A0 * B1 - A1 * B0)) * g01 + (-6 * (A0 * B2 - A2 * B0)) * g02 +
    (-6 * (A1 * B2 - A2 * B1)) * g12 + (A0 * B1 - A1 * B0) * c2 +
    (-C0 * (A1 * B2 - A2 * B1) + C1 * (A0 * B2 - A2 * B0)) * h11K

theorem δP_mem : δP ∈ chartP := mem_chartP_of_ι ι_δP

def δPP : chartP := ⟨δP, δP_mem⟩

theorem cc_Jpoly : constantCoeff Jpoly = 2 := by
  simp [Jpoly, rK, rE, r0, r1, pderiv_X, map_ofNat]

theorem δPP_not_mem : δPP ∉ 𝔪₀ := by
  change constantCoeff (ιS δPP) ≠ 0
  rw [ιS_eq (f := δPP) ι_δP, map_mul, cc_Jpoly, map_ofNat]
  intro h
  have h12 : (12 : k') = 0 := by linear_combination h
  have h' : ((12 : ℕ) : k') = 0 := by exact_mod_cast h12
  rw [CharP.cast_eq_zero_iff k' 11] at h'
  norm_num at h'

theorem δP_ne_zero : δP ≠ 0 := fun h ↦ δPP_not_mem (by
  rw [show δPP = 0 from Subtype.ext h]
  exact zero_mem _)

/-! ## The principal open around `P₀` -/

def rN : chartP := Classical.choose exists_nakayama

theorem rN_not_mem : rN ∉ 𝔪₀ := (Classical.choose_spec exists_nakayama).1

theorem rN_smul (ω : KaehlerDifferential F₁₁ chartP) : rN • ω ∈ N₀ :=
  (Classical.choose_spec exists_nakayama).2 ω

/-- The denominator of the principal open around `P₀`. -/
def eP : chartP := rN * δPP

theorem eP_not_mem : eP ∉ 𝔪₀ := fun h ↦
  ((Ideal.IsPrime.mem_or_mem inferInstance h).elim rN_not_mem δPP_not_mem)

theorem eP_ne_zero : (eP : L) ≠ 0 := fun h ↦ eP_not_mem (by
  rw [show eP = 0 from Subtype.ext h]
  exact zero_mem _)

/-- The principal open `D(e)` of the chart `P` around `P₀`, inside `L`. -/
def PChartP : Subalgebra k L := chartP ⊔ Algebra.adjoin k {(eP : L)⁻¹}

theorem chartP_le_PChartP : chartP ≤ PChartP := le_sup_left

theorem inv_mem_PChartP : (eP : L)⁻¹ ∈ PChartP :=
  le_sup_right (a := chartP) (Algebra.subset_adjoin (Set.mem_singleton _))

theorem vP_mem (l : Fin 3) : vP l ∈ PChartP := by
  fin_cases l
  · exact chartP_le_PChartP cPt.2
  · exact chartP_le_PChartP (ξ_mem 0)
  · exact chartP_le_PChartP (ξ_mem 1)

/-- The coordinates `c, ξ₀, ξ₁` on `D(e)`. -/
def zP (l : Fin 3) : PChartP := ⟨vP l, vP_mem l⟩

abbrev keptSpanP : Submodule PChartP (KaehlerDifferential F₁₁ PChartP) :=
  Submodule.span PChartP (Set.range fun l ↦ KaehlerDifferential.D F₁₁ PChartP (zP l))

/-- `e` as a unit of `D(e)`. -/
def eQ : PChartP := ⟨eP, chartP_le_PChartP eP.2⟩

theorem PChartP_isLocalization :
    letI := inclusionAlgebra chartP_le_PChartP
    IsLocalization.Away eP PChartP :=
  subalgebra_isLocalizationAway chartP PChartP chartP_le_PChartP eP eP_ne_zero inv_mem_PChartP le_rfl

theorem eQ_isUnit : IsUnit eQ := by
  letI := inclusionAlgebra chartP_le_PChartP
  have := PChartP_isLocalization
  exact IsLocalization.Away.algebraMap_isUnit eP

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem D_chartP_mem (y : chartP) :
    KaehlerDifferential.D F₁₁ PChartP ⟨y, chartP_le_PChartP y.2⟩ ∈ keptSpanP := by
  letI := inclusionAlgebra chartP_le_PChartP
  haveI : IsScalarTower F₁₁ chartP PChartP := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hN : ∀ ω ∈ N₀, KaehlerDifferential.map F₁₁ F₁₁ chartP PChartP ω ∈ keptSpanP := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · rw [KaehlerDifferential.map_D]; exact Submodule.subset_span ⟨0, rfl⟩
      · rw [KaehlerDifferential.map_D]; exact Submodule.subset_span ⟨1, rfl⟩
      · rw [KaehlerDifferential.map_D]; exact Submodule.subset_span ⟨2, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_of_tower_mem _ a hx
  have hmem := hN _ (N₀.smul_mem δPP (rN_smul (KaehlerDifferential.D F₁₁ chartP y)))
  have he : algebraMap chartP PChartP δPP * algebraMap chartP PChartP rN = eQ := Subtype.ext (by
    change δP * (rN : L) = (rN : L) * δP
    ring)
  have hrw : KaehlerDifferential.map F₁₁ F₁₁ chartP PChartP
      (δPP • rN • KaehlerDifferential.D F₁₁ chartP y) =
      eQ • KaehlerDifferential.D F₁₁ PChartP ⟨y, chartP_le_PChartP y.2⟩ := by
    rw [LinearMap.map_smul, LinearMap.map_smul, KaehlerDifferential.map_D,
      ← algebraMap_smul PChartP δPP, ← algebraMap_smul PChartP rN, smul_smul, he]
    rfl
  rw [hrw] at hmem
  exact (Submodule.smul_mem_iff_of_isUnit keptSpanP eQ_isUnit).mp hmem

theorem D_mem_of_mul_P {r v w : PChartP} (hv : IsUnit v)
    (he : v * r = w) (hw : KaehlerDifferential.D F₁₁ PChartP w ∈ keptSpanP)
    (hdv : KaehlerDifferential.D F₁₁ PChartP v ∈ keptSpanP) :
    KaehlerDifferential.D F₁₁ PChartP r ∈ keptSpanP := by
  obtain ⟨u, rfl⟩ := hv
  have hD := congrArg (KaehlerDifferential.D F₁₁ PChartP) he
  rw [Derivation.leibniz] at hD
  have hr : KaehlerDifferential.D F₁₁ PChartP r =
      u⁻¹ • (KaehlerDifferential.D F₁₁ PChartP w -
        r • KaehlerDifferential.D F₁₁ PChartP (u : PChartP)) := by
    rw [← hD, add_sub_cancel_right]
    exact (inv_smul_smul u (KaehlerDifferential.D F₁₁ PChartP r)).symm
  rw [hr]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hdv))

theorem keptSpanP_top : ⊤ ≤ keptSpanP := by
  rw [← KaehlerDifferential.span_range_derivation F₁₁ PChartP, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  have hden := adjoin_inverse_denominators chartP eP eP_ne_zero
  obtain ⟨n, hn⟩ := hden r.property
  have hdn : KaehlerDifferential.D F₁₁ PChartP (eQ ^ n) ∈ keptSpanP := by
    rw [Derivation.leibniz_pow]
    exact nsmul_mem (Submodule.smul_mem _ _ (D_chartP_mem eP)) n
  have hw := D_chartP_mem ⟨_, hn⟩
  refine D_mem_of_mul_P (eQ_isUnit.pow n) ?_ hw hdn
  exact Subtype.ext (by
    change (eP : L) ^ n * (r : L) = (r : L) * (eP : L) ^ n
    ring)

theorem det_zP :
    fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (((zP l : PChartP) : L))) = δP := rfl

theorem zP_independent :
    LinearIndependent PChartP (fun l ↦ KaehlerDifferential.D F₁₁ PChartP (zP l)) := by
  apply D_linearIndependent PChartP zP
  rw [det_zP]
  exact δP_ne_zero

/-- `dc, dξ₀, dξ₁` is a basis of the differentials on `D(e)`. -/
def localBasisP : Basis (Fin 3) PChartP (KaehlerDifferential F₁₁ PChartP) :=
  Basis.mk zP_independent keptSpanP_top

def localBasisPZ : Basis (Fin 3) PChartP (KaehlerDifferential ℤ PChartP) :=
  localBasisP.map (quotientBaseDifferentialEquiv ℤ F₁₁ PChartP ZMod.intCast_surjective).symm

theorem localBasisPZ_apply (l : Fin 3) :
    localBasisPZ l = KaehlerDifferential.D ℤ PChartP (zP l) := by
  rw [localBasisPZ, Basis.map_apply, localBasisP, Basis.mk_apply,
    quotientBaseDifferentialEquiv_symm_D]


end
end Geonormal.P11

import Eff.Euler
import Red61.Surface.Charts

/-! # Preservation of the six chart rings by the Euler derivation -/

namespace Eff

open Red61 Red61.Fields Red61.Charts
noncomputable section

theorem euler_on_k (x : k) :
    euler (includeK x) =
      includeK (-c 0 * coeffDeriv 0 x + c 1 * coeffDeriv 1 x) := by
  rw [derivation_on_k, euler_c₁, euler_c₂]
  simp only [map_add, map_mul, map_neg, includeK_c]
  rfl

theorem euler_zpow (x : K) (hx : x ≠ 0) (a : K) (ha : euler x = a * x) (n : ℤ) :
    euler (x ^ n) = (n : K) * a * x ^ n := by
  rw [Derivation.leibniz_zpow, ha, smul_eq_mul, zsmul_eq_mul]
  calc
    (n : K) * (x ^ (n - 1) * (a * x)) = (n : K) * a * (x ^ (n - 1) * x ^ (1 : ℤ)) := by
      rw [zpow_one]
      ring
    _ = (n : K) * a * x ^ n := by rw [← zpow_add₀ hx]; congr 2; omega

/-- Every toric monomial is an eigenvector. -/
theorem euler_monomial (v : Red61.Fan.Lattice) :
    euler (monomial v) = (2 * (v.1 : K) + 3 * (v.2 : K)) * monomial v := by
  rw [monomial, Derivation.leibniz, euler_zpow t (coord_nonzero 2) 2 euler_t,
    euler_zpow w (coord_nonzero 3) 3 euler_w]
  simp only [smul_eq_mul]
  ring

/-- The two chart-coordinate weights, in the order of the paper. -/
def firstWeight : Fin 6 → ZMod 5 := ![2, 2, 3, 3, 2, 1]
def secondWeight : Fin 6 → ZMod 5 := ![3, 2, 3, 4, 4, 1]

theorem euler_first_coordinate (i : Fin 6) :
    euler (y₁ i) = algebraMap F₅ K (firstWeight i) * y₁ i := by
  rw [y₁, euler_monomial]
  congr 1
  have h : (2 * ((first i).1 : F₅) + 3 * ((first i).2 : F₅)) = firstWeight i := by
    fin_cases i <;> decide
  have h' := congrArg (algebraMap F₅ K) h
  simpa [map_ofNat] using h'

theorem euler_second_coordinate (i : Fin 6) :
    euler (y₂ i) = algebraMap F₅ K (secondWeight i) * y₂ i := by
  rw [y₂, euler_monomial]
  congr 1
  have h : (2 * ((second i).1 : F₅) + 3 * ((second i).2 : F₅)) = secondWeight i := by
    fin_cases i <;> decide
  have h' := congrArg (algebraMap F₅ K) h
  simpa [map_ofNat] using h'

/-- The coefficient field is preserved, although it is not fixed pointwise. -/
theorem euler_coefficient_mem (i : Fin 6) (x : k) :
    euler (includeK x) ∈ chartRing i := by
  rw [euler_on_k]
  exact (chartRing i).algebraMap_mem _

theorem euler_preserves_chart (i : Fin 6) {x : K} (hx : x ∈ chartRing i) :
    euler x ∈ chartRing i := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · rw [euler_first_coordinate]
      exact (chartRing i).mul_mem
        (by
          simpa only [← IsScalarTower.algebraMap_apply F₅ k K] using
            (chartRing i).algebraMap_mem (algebraMap F₅ k (firstWeight i))) (y₁_mem i)
    · rw [Set.mem_singleton_iff.mp hx, euler_second_coordinate]
      exact (chartRing i).mul_mem
        (by
          simpa only [← IsScalarTower.algebraMap_apply F₅ k K] using
            (chartRing i).algebraMap_mem (algebraMap F₅ k (secondWeight i))) (y₂_mem i)
  | algebraMap a => exact euler_coefficient_mem i a
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (chartRing i).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact (chartRing i).add_mem ((chartRing i).mul_mem hx ihy)
      ((chartRing i).mul_mem hy ihx)

/-- A genuine derivation on each existing affine chart ring. -/
def chartEuler (i : Fin 6) : Derivation ell (chartRing i) (chartRing i) where
  toFun x := ⟨euler (x : K), euler_preserves_chart i x.property⟩
  map_add' x y := Subtype.ext (map_add euler (x : K) (y : K))
  map_smul' a x := by
    apply Subtype.ext
    change ellEuler (a • (x : K)) = a • ellEuler (x : K)
    exact ellEuler.map_smul a (x : K)
  map_one_eq_zero' := Subtype.ext euler.map_one_eq_zero
  leibniz' x y := Subtype.ext (ellEuler.leibniz (x : K) (y : K))

@[simp] theorem chartEuler_coe (i : Fin 6) (x : chartRing i) :
    (chartEuler i x : K) = euler (x : K) := rfl

theorem chartEuler_fifth (i : Fin 6) : fifthDerivation (chartEuler i) = chartEuler i := by
  apply Derivation.ext
  intro x
  apply Subtype.ext
  exact Derivation.congr_fun euler_fifth (x : K)

end
end Eff

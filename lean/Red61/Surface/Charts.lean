import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Tactic
import Red61.Surface.Field

/-! # The affine charts, their overlaps and straightening coordinates

Formerly the modules `Fan`, `Charts`, `ChartRings`, `ChartCoordinates`, `ChartCoefficientLocalization`, `ChartFractionFields`, `ChartOverlaps`, `ChartValues`, `ChartFoliation`, `LocalCoordinates`, `StraighteningCoordinates`, `StraighteningRings`, `TorusOverlaps`, `InvariantCharts`.
-/

namespace Red61.Fan

abbrev Lattice := ℤ × ℤ

def det (v w : Lattice) : ℤ := v.1 * w.2 - v.2 * w.1
/-- Ray order: F₀, C∞, G₁, G₂, E₂, E₁. -/
def ray : Fin 6 → Lattice := ![(1, 0), (0, 1), (-1, -2), (-2, -5), (-1, -3), (0, -1)]
def next (i : Fin 6) : Fin 6 := i + 1
abbrev Divisor := Fin 6 → ℤ
def boundary : Divisor := ![1, 1, 1, 1, 1, 1]
def e₁ : Divisor := ![0, 0, 0, 0, 0, 1]
def e₂ : Divisor := ![0, 0, 0, 0, 1, 0]
def fiber : Divisor := ![1, 0, 0, 0, 0, 0]
end Red61.Fan

namespace Red61.Charts

open Fan

/-- Chart order agrees with the paper: V₁,...,V₆. -/
def first : Fin 6 → Lattice := ![(1, 0), (1, 0), (-1, 0), (-1, 0), (-3, 1), (2, -1)]
def second : Fin 6 → Lattice := ![(0, 1), (0, -1), (3, -1), (-2, 1), (5, -2), (-5, 2)]
def scale : Fin 6 → Lattice := ![(0, 0), (0, -1), (1, -1), (-1, 0), (4, -2), (-1, 0)]
def leftRay : Fin 6 → Fin 6 := ![0, 5, 4, 1, 3, 2]

def inCoordinates (i : Fin 6) (v : Lattice) : Lattice :=
  v.1 • first i + v.2 • second i

def c₁Exponent : Fin 6 → Lattice := ![(0, 0), (0, 1), (2, 1), (1, 0), (2, 2), (2, 1)]
def c₂Exponent : Fin 6 → Lattice := ![(1, 0), (1, 1), (1, 1), (0, 0), (0, 1), (0, 0)]
def firstExponent : Fin 6 → Lattice := ![(0, 1), (0, 0), (1, 0), (1, 1), (0, 0), (0, 0)]
def secondExponent : Fin 6 → Lattice := ![(0, 0), (0, 0), (0, 1), (0, 2), (0, 0), (0, 0)]
def firstCoefficient : Fin 6 → ZMod 5 := ![1, 1, -1, -1, 2, 2]
def secondCoefficient : Fin 6 → ZMod 5 := ![0, 0, 3, 3, 0, 0]

theorem c₁_lattice (i : Fin 6) : scale i = inCoordinates i (c₁Exponent i) := by
  fin_cases i <;> norm_num [scale, inCoordinates, c₁Exponent, first, second, Prod.ext_iff]

theorem c₂_lattice (i : Fin 6) : scale i + (1, 0) = inCoordinates i (c₂Exponent i) := by
  fin_cases i <;> norm_num [scale, inCoordinates, c₂Exponent, first, second, Prod.ext_iff]

theorem first_lattice (i : Fin 6) :
    scale i + first i + (-1, 1) = inCoordinates i (firstExponent i) := by
  fin_cases i <;> norm_num [scale, inCoordinates, firstExponent, first, second, Prod.ext_iff]

theorem second_lattice (i : Fin 6) :
    secondCoefficient i = 0 ∨
      scale i + second i + (-1, 1) = inCoordinates i (secondExponent i) := by
  fin_cases i <;> norm_num [secondCoefficient, scale, inCoordinates, secondExponent,
    first, second, Prod.ext_iff]

theorem coefficient_first (i : Fin 6) : ((first i).1 : ZMod 5) = firstCoefficient i := by
  fin_cases i <;> decide

theorem coefficient_second (i : Fin 6) : ((second i).1 : ZMod 5) = secondCoefficient i := by
  fin_cases i <;> decide

/-- All nonzero entries of the derivative table are regular monomials. -/
theorem nonnegative_table (i : Fin 6) :
    0 ≤ (c₁Exponent i).1 ∧ 0 ≤ (c₁Exponent i).2 ∧
    0 ≤ (c₂Exponent i).1 ∧ 0 ≤ (c₂Exponent i).2 ∧
    0 ≤ (firstExponent i).1 ∧ 0 ≤ (firstExponent i).2 ∧
    0 ≤ (secondExponent i).1 ∧ 0 ≤ (secondExponent i).2 := by
  fin_cases i <;> norm_num [c₁Exponent, c₂Exponent, firstExponent, secondExponent]

/-- Chart labels in cyclic order around the fan. -/
def cyclicChart : Fin 6 → Fin 6 := ![0, 3, 5, 4, 2, 1]

noncomputable section
open Fields

def monomial (v : Lattice) : K := t ^ v.1 * w ^ v.2
def localGenerator (i : Fin 6) : Derivation F₅ K K := monomial (scale i) • delta
def y₁ (i : Fin 6) : K := monomial (first i)
def y₂ (i : Fin 6) : K := monomial (second i)

theorem monomial_mul (v z : Lattice) :
    monomial (v + z) = monomial v * monomial z := by
  dsimp [monomial]
  rw [zpow_add₀ (coord_nonzero 2), zpow_add₀ (coord_nonzero 3)]
  ring

theorem derivative_monomial (v : Lattice) :
    delta (monomial v) = (v.1 : K) * monomial (v + (-1, 1)) := by
  simp only [monomial, Derivation.leibniz, Derivation.leibniz_zpow,
    delta_t, delta_w, smul_eq_mul, smul_zero, mul_zero, zero_add]
  rw [zsmul_eq_mul]
  simp only [Prod.fst_add, Prod.snd_add, sub_eq_add_neg]
  rw [zpow_add₀ (coord_nonzero 3)]
  simp only [zpow_one]
  ring

theorem local_on_monomial (i : Fin 6) (v : Lattice) :
    localGenerator i (monomial v) = (v.1 : K) * monomial (scale i + v + (-1, 1)) := by
  simp only [localGenerator, Derivation.smul_apply, smul_eq_mul, derivative_monomial]
  simp only [monomial_mul]
  ring

theorem coefficient_first_K (i : Fin 6) :
    ((first i).1 : K) = algebraMap F₅ K (firstCoefficient i) := by
  have h := congrArg (algebraMap F₅ K) (coefficient_first i)
  simpa using h

theorem coefficient_second_K (i : Fin 6) :
    ((second i).1 : K) = algebraMap F₅ K (secondCoefficient i) := by
  have h := congrArg (algebraMap F₅ K) (coefficient_second i)
  simpa using h

/-- All twenty-four entries of the six-chart table, in the constructed field K. -/
theorem derivative_table (i : Fin 6) :
    localGenerator i c₁ = monomial (inCoordinates i (c₁Exponent i)) ∧
    localGenerator i c₂ = monomial (inCoordinates i (c₂Exponent i)) ∧
    localGenerator i (y₁ i) =
      algebraMap F₅ K (firstCoefficient i) * monomial (inCoordinates i (firstExponent i)) ∧
    localGenerator i (y₂ i) =
      algebraMap F₅ K (secondCoefficient i) * monomial (inCoordinates i (secondExponent i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [localGenerator, Derivation.smul_apply, smul_eq_mul, delta_c₁, mul_one]
    rw [c₁_lattice]
  · simp only [localGenerator, Derivation.smul_apply, smul_eq_mul, delta_c₂]
    rw [← c₂_lattice, monomial_mul]
    simp [monomial]
  · rw [y₁, local_on_monomial, first_lattice, coefficient_first_K]
  · rw [y₂, local_on_monomial, coefficient_second_K]
    rcases second_lattice i with h | h
    · simp [h]
    · rw [h]

theorem monomial_nonzero (v : Lattice) : monomial v ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (coord_nonzero 2)) (zpow_ne_zero _ (coord_nonzero 3))

end
end Red61.Charts

namespace Red61.Charts

noncomputable section
open Fan Fields

/-- Each affine coordinate ring is an actual subring of the common function field. -/
def chartRing (i : Fin 6) : Subalgebra k K := Algebra.adjoin k {y₁ i, y₂ i}

theorem y₁_mem (i : Fin 6) : y₁ i ∈ chartRing i :=
  Algebra.subset_adjoin (by simp)

theorem y₂_mem (i : Fin 6) : y₂ i ∈ chartRing i :=
  Algebra.subset_adjoin (by simp)

theorem monomial_zsmul (n : ℤ) (v : Lattice) :
    monomial (n • v) = monomial v ^ n := by
  rcases v with ⟨a, b⟩
  simp [monomial, mul_zpow, ← zpow_mul, mul_comm]

theorem monomial_in_coordinates (i : Fin 6) (v : Lattice) :
    monomial (inCoordinates i v) = y₁ i ^ v.1 * y₂ i ^ v.2 := by
  rw [inCoordinates, monomial_mul, monomial_zsmul, monomial_zsmul]
  rfl

theorem regular_monomial_mem (i : Fin 6) (v : Lattice)
    (h₁ : 0 ≤ v.1) (h₂ : 0 ≤ v.2) :
    monomial (inCoordinates i v) ∈ chartRing i := by
  rw [monomial_in_coordinates, ← Int.toNat_of_nonneg h₁, ← Int.toNat_of_nonneg h₂]
  simp only [zpow_natCast]
  exact (chartRing i).mul_mem ((chartRing i).pow_mem (y₁_mem i) _)
    ((chartRing i).pow_mem (y₂_mem i) _)

theorem derivative_generators_mem (i : Fin 6) :
    localGenerator i c₁ ∈ chartRing i ∧ localGenerator i c₂ ∈ chartRing i ∧
    localGenerator i (y₁ i) ∈ chartRing i ∧ localGenerator i (y₂ i) ∈ chartRing i := by
  have h := derivative_table i
  have hn := nonnegative_table i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.1]
    exact regular_monomial_mem i _ hn.1 hn.2.1
  · rw [h.2.1]
    exact regular_monomial_mem i _ hn.2.2.1 hn.2.2.2.1
  · rw [h.2.2.1]
    apply (chartRing i).mul_mem
    · simpa only [← IsScalarTower.algebraMap_apply F₅ k K] using
        (chartRing i).algebraMap_mem (algebraMap F₅ k (firstCoefficient i))
    · exact regular_monomial_mem i _ hn.2.2.2.2.1 hn.2.2.2.2.2.1
  · rw [h.2.2.2]
    apply (chartRing i).mul_mem
    · simpa only [← IsScalarTower.algebraMap_apply F₅ k K] using
        (chartRing i).algebraMap_mem (algebraMap F₅ k (secondCoefficient i))
    · exact regular_monomial_mem i _ hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2

theorem derivative_coefficient_mem (i : Fin 6) (x : k) :
    localGenerator i (includeK x) ∈ chartRing i := by
  rw [derivation_on_k]
  exact (chartRing i).add_mem
    ((chartRing i).mul_mem (derivative_generators_mem i).1
      ((chartRing i).algebraMap_mem _))
    ((chartRing i).mul_mem (derivative_generators_mem i).2.1
      ((chartRing i).algebraMap_mem _))

/-- Ring preservation includes differentiation of the coefficient field k. -/
theorem preserves_chartRing (i : Fin 6) {x : K} (hx : x ∈ chartRing i) :
    localGenerator i x ∈ chartRing i := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (derivative_generators_mem i).2.2.1
    · have hx' : x = y₂ i := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact (derivative_generators_mem i).2.2.2
  | algebraMap x => exact derivative_coefficient_mem i x
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (chartRing i).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact (chartRing i).add_mem ((chartRing i).mul_mem hx ihy)
      ((chartRing i).mul_mem hy ihx)

instance (i : Fin 6) : Algebra ell (chartRing i) :=
  ((algebraMap k (chartRing i)).comp (algebraMap ell k)).toAlgebra

instance (i : Fin 6) : IsScalarTower ell (chartRing i) K :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Local derivations have the intended ell-linear, rather than k-linear, type. -/
def chartDerivation (i : Fin 6) : Derivation ell (chartRing i) (chartRing i) where
  toFun x := ⟨localGenerator i x, preserves_chartRing i x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add (localGenerator i) (x : K) (y : K)
  map_smul' a x := by
    apply Subtype.ext
    change (monomial (scale i) • ellDelta) (a • (x : K)) =
      a • (monomial (scale i) • ellDelta) (x : K)
    exact (monomial (scale i) • ellDelta).map_smul a (x : K)
  map_one_eq_zero' := by
    apply Subtype.ext
    exact (localGenerator i).map_one_eq_zero
  leibniz' x y := by apply Subtype.ext; exact (localGenerator i).leibniz x y

/-- Subring generated by both charts on a consecutive overlap. -/
def overlapRing (j : Fin 6) : Subalgebra k K :=
  chartRing (cyclicChart j) ⊔ chartRing (cyclicChart (next j))

end
end Red61.Charts

namespace Red61.Charts

open Fan Fields
noncomputable section

def tExponent : Fin 6 → Lattice := ![(1,0), (1,0), (-1,0), (-1,0), (-2,-1), (-2,-1)]
def wExponent : Fin 6 → Lattice := ![(0,1), (0,-1), (-3,-1), (-2,1), (-5,-3), (-5,-2)]

theorem inverse_lattice (i : Fin 6) :
    inCoordinates i (tExponent i) = (1,0) ∧ inCoordinates i (wExponent i) = (0,1) := by
  fin_cases i <;> norm_num [inCoordinates, first, second, tExponent, wExponent, Prod.ext_iff]

theorem inverse_coordinates (i : Fin 6) :
    t = y₁ i ^ (tExponent i).1 * y₂ i ^ (tExponent i).2 ∧
    w = y₁ i ^ (wExponent i).1 * y₂ i ^ (wExponent i).2 := by
  have ht := monomial_in_coordinates i (tExponent i)
  have hw := monomial_in_coordinates i (wExponent i)
  rw [(inverse_lattice i).1] at ht
  rw [(inverse_lattice i).2] at hw
  simpa only [monomial, zpow_one, zpow_zero, mul_one, one_mul] using And.intro ht hw

theorem chart_field_generation (i : Fin 6) :
    IntermediateField.adjoin k {y₁ i, y₂ i} = ⊤ := by
  let M := IntermediateField.adjoin k ({y₁ i, y₂ i} : Set K)
  have h₁ : y₁ i ∈ M := IntermediateField.subset_adjoin k _ (by simp)
  have h₂ : y₂ i ∈ M := IntermediateField.subset_adjoin k _ (by simp)
  have ht : t ∈ M := by
    rw [(inverse_coordinates i).1]
    exact M.mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)
  have hw : w ∈ M := by
    rw [(inverse_coordinates i).2]
    exact M.mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)
  apply top_unique
  rw [← rational_generation]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ht
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hw

def chartCoordinates (i : Fin 6) : Fin 2 → K := ![y₁ i, y₂ i]

theorem chartCoordinates_range (i : Fin 6) :
    Set.range (chartCoordinates i) = {y₁ i, y₂ i} := by
  ext x
  simp [chartCoordinates, or_comm]

theorem chartCoordinates_independent (i : Fin 6) :
    AlgebraicIndependent k (chartCoordinates i) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (chartCoordinates i))) K := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, chartCoordinates_range,
      chart_field_generation]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k
    (chartCoordinates i) surfaceCoordinates_independent.cardinalMk_le_trdeg).1

/-- All six chart rings are genuinely polynomial rings over k. -/
def chartPolynomialEquiv (i : Fin 6) : MvPolynomial (Fin 2) k ≃ₐ[k] chartRing i :=
  (chartCoordinates_independent i).aevalEquiv.trans
    (Subalgebra.equivOfEq _ _ (by rw [chartCoordinates_range]; rfl))

@[simp] theorem chartPolynomialEquiv_X (i : Fin 6) (j : Fin 2) :
    (chartPolynomialEquiv i (MvPolynomial.X j) : K) = chartCoordinates i j := by
  simp [chartPolynomialEquiv, AlgebraicIndependent.aevalEquiv]

end
end Red61.Charts

namespace Red61.Charts

open Fields FieldLocalization MvPolynomial
noncomputable section

theorem coefficient_polynomial_mem (A : Subalgebra F₅ K)
    (h₁ : c₁ ∈ A) (h₂ : c₂ ∈ A) (p : P₂) :
    includeK (algebraMap P₂ k p) ∈ A := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : includeK (algebraMap P₂ k (C a)) = algebraMap F₅ K a := by
      rw [includeK_poly]
      change algebraMap P₄ K (MvPolynomial.rename _ (C a)) = _
      rw [MvPolynomial.rename_C]
      exact IsScalarTower.algebraMap_apply F₅ P₄ K a |>.symm
    rw [he]
    exact A.algebraMap_mem a
  | add p q hp hq => simpa only [map_add] using A.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    apply A.mul_mem hp
    change includeK (c i) ∈ A
    fin_cases i
    · simpa [includeK_c] using h₁
    · simpa [includeK_c] using h₂

theorem chart_generators_field (i : Fin 6) (M : IntermediateField F₅ K)
    (h₁ : c₁ ∈ M) (h₂ : c₂ ∈ M) (hx : y₁ i ∈ M) (hy : y₂ i ∈ M) : M = ⊤ := by
  have ht : t ∈ M := by
    rw [(inverse_coordinates i).1]
    exact M.mul_mem (zpow_mem hx _) (zpow_mem hy _)
  have hw : w ∈ M := by
    rw [(inverse_coordinates i).2]
    exact M.mul_mem (zpow_mem hx _) (zpow_mem hy _)
  have hc (i : Fin 4) : coord i ∈ M := by fin_cases i <;> assumption
  have hp (p : P₄) : algebraMap P₄ K p ∈ M := by
    induction p using MvPolynomial.induction_on with
    | C a => exact M.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using M.add_mem hp hq
    | mul_X p i hp => simpa only [map_mul, coord] using M.mul_mem hp (hc i)
  apply top_unique
  intro z _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (A := P₄) z
  exact M.div_mem (hp p) (hp q)

theorem coefficient_mem_hull {P A : Subalgebra F₅ K} (hPA : P ≤ A)
    (h₁ : c₁ ∈ hull P A) (h₂ : c₂ ∈ hull P A)
    (hk : ∀ a : k, includeK a ∈ A) (a : k) : includeK a ∈ hull P A := by
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (A := P₂) a
  rw [map_div₀, div_eq_mul_inv]
  apply (hull P A).mul_mem (coefficient_polynomial_mem _ h₁ h₂ p)
  apply hull_inv hPA (coefficient_polynomial_mem _ h₁ h₂ q)
  rw [← map_inv₀]
  exact hk _

theorem chart_le_hull (i : Fin 6) {P A : Subalgebra F₅ K} (hPA : P ≤ A)
    (hA : (chartRing i).restrictScalars F₅ ≤ A)
    (h₁ : c₁ ∈ hull P A) (h₂ : c₂ ∈ hull P A)
    (hx : y₁ i ∈ hull P A) (hy : y₂ i ∈ hull P A) :
    (chartRing i).restrictScalars F₅ ≤ hull P A := by
  intro x hxA
  change x ∈ Algebra.adjoin k {y₁ i, y₂ i} at hxA
  induction hxA using Algebra.adjoin_induction with
  | mem x hxA => rcases hxA with rfl | hxA; exact hx; simpa using hxA ▸ hy
  | algebraMap a =>
    exact coefficient_mem_hull hPA h₁ h₂ (fun a ↦ hA ((chartRing i).algebraMap_mem a)) a
  | add x y _ _ ihx ihy => exact (hull P A).add_mem ihx ihy
  | mul x y _ _ ihx ihy => exact (hull P A).mul_mem ihx ihy

end
end Red61.Charts

namespace Red61.Charts

open Fields
noncomputable section

/-- The common function field is the fraction field of every affine chart. -/
instance chart_isFractionRing (i : Fin 6) : IsFractionRing (chartRing i) K := by
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ IntermediateField.adjoin k ({y₁ i, y₂ i} : Set K) := by
    rw [chart_field_generation]
    trivial
  obtain ⟨a,ha,b,hb,he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  exact ⟨⟨a,ha⟩,⟨b,hb⟩,he⟩

def chartFractionEquiv (i : Fin 6) :
    FractionRing (MvPolynomial (Fin 2) k) ≃ₐ[k] K :=
  IsFractionRing.algEquivOfAlgEquiv (chartPolynomialEquiv i)

@[simp] theorem chartFractionEquiv_polynomial (i : Fin 6) (p : MvPolynomial (Fin 2) k) :
    chartFractionEquiv i (algebraMap _ (FractionRing (MvPolynomial (Fin 2) k)) p) =
      MvPolynomial.aeval (chartCoordinates i) p := by
  rw [chartFractionEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

theorem chartFractionEquiv_coordinate (i : Fin 6) (a : Fin 2) :
    chartFractionEquiv i (algebraMap (MvPolynomial (Fin 2) k) (FractionRing (MvPolynomial (Fin 2) k))
      (MvPolynomial.X a)) = chartCoordinates i a := by
  rw [chartFractionEquiv_polynomial, MvPolynomial.aeval_X]

end
end Red61.Charts

namespace Red61.Charts

open Fan Fields
noncomputable section

def overlapChart (j : Fin 6) : Fin 2 → Fin 6 :=
  ![cyclicChart j, cyclicChart (next j)]

def invertedIndex : Fin 6 → Fin 2 → Fin 2 :=
  ![![0,0], ![1,0], ![1,1], ![0,1], ![0,0], ![1,1]]

def coordinateVector (i : Fin 6) : Fin 2 → Lattice := ![first i, second i]

def transitionExponents : Fin 6 → Fin 2 → Fin 2 → Lattice :=
  ![![![(-1,0),(-2,1)], ![(-1,0),(-2,1)]],
    ![![(0,-1),(1,2)], ![(2,1),(-1,0)]],
    ![![(1,1),(0,-1)], ![(1,1),(0,-1)]],
    ![![(2,1),(-1,0)], ![(0,-1),(1,2)]],
    ![![(-1,0),(3,1)], ![(-1,0),(3,1)]],
    ![![(1,0),(0,-1)], ![(1,0),(0,-1)]]]

theorem transition_lattice (j : Fin 6) (s a : Fin 2) :
    coordinateVector (overlapChart j (1-s)) a =
      inCoordinates (overlapChart j s) (transitionExponents j s a) := by
  fin_cases j <;> fin_cases s <;> fin_cases a <;>
    norm_num [coordinateVector, overlapChart, cyclicChart, next, transitionExponents,
      inCoordinates, first, second, Prod.ext_iff]

theorem inverted_lattice (j : Fin 6) (s : Fin 2) :
    -coordinateVector (overlapChart j s) (invertedIndex j s) =
      coordinateVector (overlapChart j (1-s)) (invertedIndex j (1-s)) := by
  fin_cases j <;> fin_cases s <;>
    norm_num [coordinateVector, overlapChart, cyclicChart, next, invertedIndex,
      first, second, Prod.ext_iff]

theorem transition_denominators (j : Fin 6) (s a : Fin 2) :
    (0 ≤ (transitionExponents j s a).1 ∨ invertedIndex j s = 0) ∧
    (0 ≤ (transitionExponents j s a).2 ∨ invertedIndex j s = 1) := by
  fin_cases j <;> fin_cases s <;> fin_cases a <;>
    norm_num [transitionExponents, invertedIndex]

theorem chartCoordinate_monomial (i : Fin 6) (a : Fin 2) :
    chartCoordinates i a = monomial (coordinateVector i a) := by
  fin_cases a <;> rfl

theorem transition_coordinates (j : Fin 6) (s a : Fin 2) :
    chartCoordinates (overlapChart j (1-s)) a =
      y₁ (overlapChart j s) ^ (transitionExponents j s a).1 *
      y₂ (overlapChart j s) ^ (transitionExponents j s a).2 := by
  rw [chartCoordinate_monomial, transition_lattice, monomial_in_coordinates]

theorem inverted_coordinates (j : Fin 6) (s : Fin 2) :
    (chartCoordinates (overlapChart j s) (invertedIndex j s))⁻¹ =
      chartCoordinates (overlapChart j (1-s)) (invertedIndex j (1-s)) := by
  simp only [chartCoordinate_monomial]
  have hn (a : Lattice) : monomial (-a) = (monomial a)⁻¹ := by simpa using monomial_zsmul (-1) a
  rw [← hn, inverted_lattice]

def overlapDenominator (j : Fin 6) (s : Fin 2) : chartRing (overlapChart j s) :=
  ⟨chartCoordinates (overlapChart j s) (invertedIndex j s), by
    generalize invertedIndex j s = a
    fin_cases a
    · exact y₁_mem _
    · exact y₂_mem _⟩

theorem overlap_chart_le (j : Fin 6) (s : Fin 2) :
    chartRing (overlapChart j s) ≤ overlapRing j := by
  fin_cases s
  · exact le_sup_left
  · exact le_sup_right

theorem coordinate_mem_overlap (j : Fin 6) (s a : Fin 2) :
    chartCoordinates (overlapChart j s) a ∈ overlapRing j := by
  apply overlap_chart_le j s
  fin_cases a
  · exact y₁_mem _
  · exact y₂_mem _

theorem zpow_mem_of_inv_mem {E : Subalgebra k K} {x : K}
    (hx : x ∈ E) (hi : x⁻¹ ∈ E) (n : ℤ) : x^n ∈ E := by
  cases n with
  | ofNat n => exact E.pow_mem hx n
  | negSucc n => simpa only [zpow_negSucc, ← inv_pow] using E.pow_mem hi (n+1)

theorem overlap_adjoin_inverse (j : Fin 6) (s : Fin 2) :
    overlapRing j = chartRing (overlapChart j s) ⊔
      Algebra.adjoin k ({((overlapDenominator j s : chartRing _) : K)⁻¹} : Set K) := by
  let A := chartRing (overlapChart j s)
  let E := A ⊔ Algebra.adjoin k ({((overlapDenominator j s : chartRing _) : K)⁻¹} : Set K)
  have hA : A ≤ E := le_sup_left
  have h₁ : y₁ (overlapChart j s) ∈ E := hA (y₁_mem _)
  have h₂ : y₂ (overlapChart j s) ∈ E := hA (y₂_mem _)
  have hi : ((overlapDenominator j s : chartRing _) : K)⁻¹ ∈ E :=
    (show Algebra.adjoin k _ ≤ E from le_sup_right) (Algebra.subset_adjoin (by simp))
  have hcoords (a : Fin 2) : chartCoordinates (overlapChart j (1-s)) a ∈ E := by
    rw [transition_coordinates]
    apply E.mul_mem
    · rcases (transition_denominators j s a).1 with hn | he
      · rw [← Int.toNat_of_nonneg hn, zpow_natCast]
        exact E.pow_mem h₁ _
      · apply zpow_mem_of_inv_mem h₁
        simpa only [overlapDenominator, he, chartCoordinates, Matrix.cons_val_zero] using hi
    · rcases (transition_denominators j s a).2 with hn | he
      · rw [← Int.toNat_of_nonneg hn, zpow_natCast]
        exact E.pow_mem h₂ _
      · apply zpow_mem_of_inv_mem h₂
        simpa only [overlapDenominator, he, chartCoordinates, Matrix.cons_val_one,
          Matrix.cons_val_zero] using hi
  have hother : chartRing (overlapChart j (1-s)) ≤ E := by
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with rfl | hx
    · exact hcoords 0
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hcoords 1
  apply le_antisymm
  · fin_cases s
    · exact sup_le hA hother
    · exact sup_le hother hA
  · apply sup_le (overlap_chart_le j s)
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change (chartCoordinates (overlapChart j s) (invertedIndex j s))⁻¹ ∈ _
    rw [inverted_coordinates]
    exact coordinate_mem_overlap _ _ _

@[instance_reducible] def overlapAlgebra (j : Fin 6) (s : Fin 2) :
    Algebra (chartRing (overlapChart j s)) (overlapRing j) :=
  (Subalgebra.inclusion (overlap_chart_le j s)).toRingHom.toAlgebra

/-- Each overlap is the localization of either adjacent chart at the displayed coordinate. -/
theorem overlap_isLocalization (j : Fin 6) (s : Fin 2) :
    letI := overlapAlgebra j s
    IsLocalization.Away (overlapDenominator j s) (overlapRing j) := by
  apply subalgebra_isLocalizationAway
  · change chartCoordinates (overlapChart j s) (invertedIndex j s) ≠ 0
    rw [chartCoordinate_monomial]
    exact monomial_nonzero _
  · change (chartCoordinates (overlapChart j s) (invertedIndex j s))⁻¹ ∈ _
    rw [inverted_coordinates]
    exact coordinate_mem_overlap _ _ _
  · exact (overlap_adjoin_inverse j s).le

end
end Red61.Charts

namespace Red61.Charts

open Fan Fields MvPolynomial
noncomputable section

abbrev ChartPolynomial := MvPolynomial (Fin 2) k

def valuePolynomials : Fin 6 → Fin 4 → ChartPolynomial :=
  ![![1, X 0, X 1, 0],
    ![X 1, X 0 * X 1, 1, 0],
    ![X 0 ^ 2 * X 1, X 0 * X 1, -X 0, 3 * X 1],
    ![X 0, 1, -X 0 * X 1, 3 * X 1 ^ 2],
    ![X 0 ^ 2 * X 1 ^ 2, X 1, 2, 0],
    ![X 0 ^ 2 * X 1, 1, 2, 0]]

def inputs (i : Fin 6) : Fin 4 → K := ![c₁, c₂, y₁ i, y₂ i]

theorem inputs_mem (i : Fin 6) (a : Fin 4) : inputs i a ∈ chartRing i := by
  fin_cases a
  · change c₁ ∈ chartRing i
    have h : includeK (c 0) ∈ chartRing i := (chartRing i).algebraMap_mem (c 0)
    simpa [includeK_c] using h
  · change c₂ ∈ chartRing i
    have h : includeK (c 1) ∈ chartRing i := (chartRing i).algebraMap_mem (c 1)
    simpa [includeK_c] using h
  · exact y₁_mem i
  · exact y₂_mem i

theorem value_polynomial_formula (i : Fin 6) (a : Fin 4) :
    aeval (chartCoordinates i) (valuePolynomials i a) = localGenerator i (inputs i a) := by
  have ht := derivative_table i
  have h2 : algebraMap F₅ K (2 : F₅) = (2 : K) := map_ofNat _ 2
  have h3 : algebraMap F₅ K (3 : F₅) = (3 : K) := map_ofNat _ 3
  fin_cases a
  · change aeval (chartCoordinates i) (valuePolynomials i 0) = localGenerator i c₁
    rw [ht.1, monomial_in_coordinates]
    fin_cases i <;> norm_num [valuePolynomials, chartCoordinates, c₁Exponent]
  · change aeval (chartCoordinates i) (valuePolynomials i 1) = localGenerator i c₂
    rw [ht.2.1, monomial_in_coordinates]
    fin_cases i <;> norm_num [valuePolynomials, chartCoordinates, c₂Exponent]
  · change aeval (chartCoordinates i) (valuePolynomials i 2) = localGenerator i (y₁ i)
    rw [ht.2.2.1, monomial_in_coordinates]
    fin_cases i <;> norm_num [valuePolynomials, chartCoordinates, firstCoefficient, firstExponent, h2]
  · change aeval (chartCoordinates i) (valuePolynomials i 3) = localGenerator i (y₂ i)
    rw [ht.2.2.2, monomial_in_coordinates]
    fin_cases i <;> norm_num [valuePolynomials, chartCoordinates, secondCoefficient, secondExponent, h3]

end
end Red61.Charts

namespace Red61.Charts

open Fan Fields MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false

instance (i : Fin 6) : CharP (chartRing i) 5 :=
  (chartRing i).val.toRingHom.charP Subtype.val_injective 5

def exceptionalCoordinate : Fin 4 → Fin 6 × Fin 2 := ![(1,1), (2,1), (2,0), (4,1)]
def exceptionalMultiplier : Fin 4 → ℤ := ![0,3,-1,0]

def chartParameter (i : Fin 6) (a : Fin 2) : chartRing i :=
  chartPolynomialEquiv i (X a)

theorem exceptional_parameter_derivative (j : Fin 4) :
    chartDerivation (exceptionalCoordinate j).1
      (chartParameter (exceptionalCoordinate j).1 (exceptionalCoordinate j).2) =
    (exceptionalMultiplier j : chartRing (exceptionalCoordinate j).1) *
      chartParameter (exceptionalCoordinate j).1 (exceptionalCoordinate j).2 := by
  apply Subtype.ext
  change localGenerator _ (chartParameter _ _ : K) = _
  simp only [chartParameter, chartPolynomialEquiv_X, Subalgebra.coe_mul,
    SubringClass.coe_intCast]
  have h3 : algebraMap F₅ K (3 : F₅) = (3 : K) := map_ofNat _ 3
  fin_cases j
  · simpa [exceptionalCoordinate, exceptionalMultiplier, chartCoordinates,
      secondCoefficient, monomial] using (derivative_table 1).2.2.2
  · have ht := (derivative_table 2).2.2.2
    rw [monomial_in_coordinates] at ht
    simpa [exceptionalCoordinate, exceptionalMultiplier, chartCoordinates,
      secondCoefficient, secondExponent, h3] using ht
  · have ht := (derivative_table 2).2.2.1
    rw [monomial_in_coordinates] at ht
    simpa [exceptionalCoordinate, exceptionalMultiplier, chartCoordinates,
      firstCoefficient, firstExponent] using ht
  · simpa [exceptionalCoordinate, exceptionalMultiplier, chartCoordinates,
      secondCoefficient, monomial] using (derivative_table 4).2.2.2

theorem exceptional_ideal_invariant (j : Fin 4) :
    ∀ z ∈ Ideal.span ({chartParameter (exceptionalCoordinate j).1
        (exceptionalCoordinate j).2} : Set (chartRing (exceptionalCoordinate j).1)),
      chartDerivation (exceptionalCoordinate j).1 z ∈
        Ideal.span ({chartParameter (exceptionalCoordinate j).1
          (exceptionalCoordinate j).2} : Set (chartRing (exceptionalCoordinate j).1)) := by
  apply QuotientDerivation.span_singleton_stable
  rw [exceptional_parameter_derivative]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

abbrev exceptionalIdeal (j : Fin 4) : Ideal (chartRing (exceptionalCoordinate j).1) :=
  Ideal.span {chartParameter (exceptionalCoordinate j).1 (exceptionalCoordinate j).2}

/-- Restriction of the foliation generator to each exceptional divisor chart. -/
def exceptionalQuotientDerivation (j : Fin 4) :
    Derivation ell (chartRing (exceptionalCoordinate j).1 ⧸ exceptionalIdeal j)
      (chartRing (exceptionalCoordinate j).1 ⧸ exceptionalIdeal j) :=
  QuotientDerivation.derivation (exceptionalIdeal j)
    (chartDerivation (exceptionalCoordinate j).1) (exceptional_ideal_invariant j)

@[simp] theorem exceptionalQuotientDerivation_mk (j : Fin 4)
    (r : chartRing (exceptionalCoordinate j).1) :
    exceptionalQuotientDerivation j (Ideal.Quotient.mk (exceptionalIdeal j) r) =
      Ideal.Quotient.mk (exceptionalIdeal j) (chartDerivation (exceptionalCoordinate j).1 r) :=
  rfl

end
end Red61.Charts

namespace Red61.LocalCoordinates

open Fields
noncomputable section

def U : K := w⁻¹
def T : K := t
def theta : Derivation Fields.ell K K := (U * T) • ellDelta

@[simp] theorem theta_U : theta U = 0 := by
  change U * T * delta w⁻¹ = 0
  rw [Derivation.leibniz_inv, delta_w]
  simp

@[simp] theorem theta_T : theta T = T := by
  change U * T * delta t = T
  rw [delta_t]
  dsimp [U]
  field_simp [coord_nonzero 3]

@[simp] theorem theta_c₁ : theta c₁ = U * T := by
  change U * T * delta c₁ = U * T
  rw [delta_c₁, mul_one]

@[simp] theorem theta_c₂ : theta c₂ = U * T ^ 2 := by
  change U * T * delta c₂ = U * T ^ 2
  rw [delta_c₂]
  change U * T * T = U * T ^ 2
  ring

@[simp] theorem theta_w : theta w = 0 := by
  change U * T * delta w = 0
  rw [delta_w, mul_zero]

def thetaF₅ : Derivation F₅ K K := (U * T) • delta

set_option maxRecDepth 4096 in
theorem theta_five (x : K) : theta (theta (theta (theta (theta x)))) = theta x := by
  have he : fifthDerivation thetaF₅ = thetaF₅ := by
    apply FractionDerivation.ext (A := P₄)
    have hp : (fifthDerivation thetaF₅).compAlgebraMap (A := P₄) =
        thetaF₅.compAlgebraMap (A := P₄) := by
      apply MvPolynomial.derivation_ext
      intro i
      change theta (theta (theta (theta (theta (coord i))))) = theta (coord i)
      fin_cases i
      · change theta (theta (theta (theta (theta c₁)))) = theta c₁
        simp [Derivation.leibniz, smul_eq_mul]
      · change theta (theta (theta (theta (theta c₂)))) = theta c₂
        have hn (n : ℕ) : theta (n : K) = 0 := theta.map_natCast n
        have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
        simp only [theta_c₂, theta_U, theta_T, Derivation.leibniz,
          Derivation.leibniz_pow, map_add, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub,
          pow_one, hn, mul_zero, add_zero]
        linear_combination 3 * U * T ^ 2 * h5
      · change theta (theta (theta (theta (theta T)))) = theta T
        simp
      · change theta (theta (theta (theta (theta w)))) = theta w
        simp
    intro f
    exact Derivation.congr_fun hp f
  exact Derivation.congr_fun he x

def u : K := U
def r : K := U ^ 2 * T ^ 5
def q₁ : K := c₁ - U * T
def q₂ : K := c₂ - 3 * U * T ^ 2

@[simp] theorem theta_u : theta u = 0 := theta_U

@[simp] theorem theta_r : theta r = 0 := by
  simp only [r, Derivation.leibniz, Derivation.leibniz_pow, theta_U, theta_T,
    smul_eq_mul, smul_zero, mul_zero, add_zero]
  rw [nsmul_eq_mul, CharP.cast_eq_zero K 5]
  ring

@[simp] theorem theta_q₁ : theta q₁ = 0 := by
  simp [q₁, Derivation.leibniz, theta_U, theta_T, smul_eq_mul]

@[simp] theorem theta_q₂ : theta q₂ = 0 := by
  have h3 : theta (3 : K) = 0 := theta.map_natCast 3
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  simp only [q₂, map_sub, Derivation.leibniz, Derivation.leibniz_pow, theta_c₂,
    theta_U, theta_T, h3, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one,
    mul_zero, add_zero]
  linear_combination -(U * T ^ 2) * h5

theorem q₁_fifth : q₁ ^ 5 = c₁ ^ 5 - u ^ 3 * r := by
  rw [q₁, sub_pow_char (p := 5), mul_pow]
  dsimp [u, r]
  ring

theorem q₂_fifth : q₂ ^ 5 = c₂ ^ 5 - 3 * u * r ^ 2 := by
  have h3 : (3 : K) ^ 5 = 3 := by
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    linear_combination 48 * h5
  rw [q₂, sub_pow_char (p := 5), mul_pow, mul_pow, h3]
  dsimp [u, r]
  ring

end
end Red61.LocalCoordinates

/-! Explicit rational coordinates for the three charts retained in X.
The middle chart is covered by h(0) and h(1). All derivations here are over F₅. -/

namespace Red61.Charts

open Fields MvPolynomial PolynomialInvariants
noncomputable section

def straightFirst : Fin 4 → K :=
  ![c₁, c₂ - c₁*t + 3*c₁^2*w, t-c₁*w, w]

def straightLast : Fin 4 → K :=
  ![c₂, c₁-c₂*(y₁ 5)^2*y₂ 5 + 2*c₂^2*y₁ 5*y₂ 5 + 2*c₂^3*y₂ 5,
    y₁ 5-2*c₂, y₂ 5]

def middleSlice (a : F₅) : K := c₂ - algebraMap F₅ K a
def middleDenominator (a : F₅) : K := 1 + 3*middleSlice a*y₂ 3
def straightMiddle (a : F₅) : Fin 4 → K :=
  ![middleSlice a,
    c₁-middleSlice a*y₁ 3 + 2*(middleSlice a)^2*y₁ 3*y₂ 3 +
      2*(middleSlice a)^3*y₁ 3*(y₂ 3)^2,
    y₁ 3*(middleDenominator a)^2, y₂ 3 / middleDenominator a]

theorem localGenerator_values (i : Fin 6) (a : Fin 4) :
    localGenerator i (inputs i a) = aeval (chartCoordinates i) (valuePolynomials i a) :=
  (value_polynomial_formula i a).symm

theorem first_derivatives (i : Fin 4) :
    localGenerator 0 (straightFirst i) = if i = 0 then 1 else 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hn : delta (3 : K) = 0 := delta.map_natCast 3
  have he : localGenerator 0 = delta := by simp [localGenerator, scale, monomial]
  rw [he]
  fin_cases i <;> simp [straightFirst, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, hn] ; linear_combination c₁*w*h5

theorem last_values :
    localGenerator 5 c₁ = (y₁ 5)^2*y₂ 5 ∧ localGenerator 5 c₂ = 1 ∧
    localGenerator 5 (y₁ 5) = 2 ∧ localGenerator 5 (y₂ 5) = 0 := by
  exact ⟨by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 5 0,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 5 1,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 5 2,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 5 3⟩

theorem last_derivatives (i : Fin 4) :
    localGenerator 5 (straightLast i) = if i = 0 then 1 else 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hn : localGenerator 5 (2 : K) = 0 := (localGenerator 5).map_natCast 2
  fin_cases i <;> simp [straightLast, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, hn, last_values.1,
    last_values.2.1, last_values.2.2.1, last_values.2.2.2]
  linear_combination 2*c₂^2*y₂ 5*h5

theorem middle_values :
    localGenerator 3 c₁ = y₁ 3 ∧ localGenerator 3 c₂ = 1 ∧
    localGenerator 3 (y₁ 3) = -(y₁ 3*y₂ 3) ∧ localGenerator 3 (y₂ 3) = 3*(y₂ 3)^2 := by
  exact ⟨by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 3 0,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 3 1,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 3 2,
    by simpa [inputs, valuePolynomials, chartCoordinates] using localGenerator_values 3 3⟩

theorem middle_slice_derivative (a : F₅) : localGenerator 3 (middleSlice a) = 1 := by
  simp [middleSlice, middle_values.2.1]

theorem middle_denominator_derivative (a : F₅) :
    localGenerator 3 (middleDenominator a) = 3*y₂ 3*middleDenominator a := by
  have hn : localGenerator 3 (3 : K) = 0 := (localGenerator 3).map_natCast 3
  simp [middleDenominator, Derivation.leibniz, smul_eq_mul,
    hn, middle_slice_derivative, middle_values.2.2.2]
  ring

theorem middle_denominator_nonzero (a : F₅) : middleDenominator a ≠ 0 := by
  let q : k := c 1 - algebraMap F₅ k a
  have hq : algebraMap k K q = middleSlice a := by
    dsimp only [q, middleSlice]
    rw [map_sub]
    change includeK (c 1) - algebraMap k K (algebraMap F₅ k a) = _
    rw [includeK_c, ← IsScalarTower.algebraMap_apply F₅ k K]
    rfl
  have he : middleDenominator a =
      aeval (chartCoordinates 3) (1 + C (3*q) * X 1) := by
    simp [middleDenominator, hq, chartCoordinates, map_ofNat (algebraMap k K) 3]
  rw [he]
  intro hz
  have hp := (chartCoordinates_independent 3) (hz.trans (map_zero _).symm)
  have hh := congrArg (constantCoeff (σ := Fin 2) (R := k)) hp
  simp at hh

theorem middle_derivatives (a : F₅) (i : Fin 4) :
    localGenerator 3 (straightMiddle a i) = if i = 0 then 1 else 0 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  fin_cases i
  · exact middle_slice_derivative a
  · change localGenerator 3 (c₁-middleSlice a*y₁ 3 +
      2*(middleSlice a)^2*y₁ 3*y₂ 3 + 2*(middleSlice a)^3*y₁ 3*(y₂ 3)^2) = 0
    have hn : localGenerator 3 (2 : K) = 0 := (localGenerator 3).map_natCast 2
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, nsmul_eq_mul, hn, middle_slice_derivative,
      middle_values.1, middle_values.2.2.1, middle_values.2.2.2]
    norm_num
    linear_combination (middleSlice a*y₁ 3*y₂ 3 +
      2*(middleSlice a)^2*y₁ 3*(y₂ 3)^2 + 2*(middleSlice a)^3*y₁ 3*(y₂ 3)^3)*h5
  · change localGenerator 3 (y₁ 3 * middleDenominator a ^ 2) = 0
    rw [Derivation.leibniz, Derivation.leibniz_pow,
      middle_values.2.2.1, middle_denominator_derivative]
    simp only [smul_eq_mul, nsmul_eq_mul]
    linear_combination y₁ 3*y₂ 3*(middleDenominator a)^2*h5
  · change localGenerator 3 (y₂ 3 / middleDenominator a) = 0
    rw [Derivation.leibniz_div, middle_values.2.2.2, middle_denominator_derivative]
    simp only [smul_eq_mul]
    ring

theorem middle_inverse (a : F₅) :
    (middleDenominator a)⁻¹ = 1 - 3*straightMiddle a 0*straightMiddle a 3 ∧
    y₁ 3 = straightMiddle a 2*(1-3*straightMiddle a 0*straightMiddle a 3)^2 ∧
    y₂ 3 = straightMiddle a 3 / (1-3*straightMiddle a 0*straightMiddle a 3) ∧
    c₁ = straightMiddle a 1 + straightMiddle a 2 *
      (straightMiddle a 0 + 2*(straightMiddle a 0)^2*straightMiddle a 3 +
        3*(straightMiddle a 0)^3*(straightMiddle a 3)^2) := by
  have hn := middle_denominator_nonzero a
  have hh : (middleDenominator a)⁻¹ = 1 - 3*middleSlice a*(y₂ 3/middleDenominator a) := by
    field_simp
    simp only [middleDenominator]
    ring
  refine ⟨hh, ?_, ?_, ?_⟩
  · change y₁ 3 = (y₁ 3 * middleDenominator a ^ 2)*
      (1-3*middleSlice a*(y₂ 3/middleDenominator a))^2
    rw [← hh]
    field_simp
  · change y₂ 3 = (y₂ 3/middleDenominator a) /
      (1-3*middleSlice a*(y₂ 3/middleDenominator a))
    rw [← hh]
    simpa using (div_mul_cancel₀ (y₂ 3) hn).symm
  · dsimp [straightMiddle]
    field_simp
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    simp only [middleDenominator]
    linear_combination -(2*(middleSlice a)^2*y₁ 3*y₂ 3 +
      4*(middleSlice a)^3*y₁ 3*(y₂ 3)^2)*h5

end
end Red61.Charts

namespace Red61.Charts

open Fields PolynomialInvariants FieldLocalization MvPolynomial
noncomputable section

private theorem coordinate_mem (v : Fin 4 → K) (i : Fin 4) :
    v i ∈ polynomialRing (F := F₅) v := Algebra.subset_adjoin (Set.mem_range_self i)

theorem first_polynomials :
    c₁ ∈ polynomialRing (F := F₅) straightFirst ∧
    c₂ ∈ polynomialRing (F := F₅) straightFirst ∧
    y₁ 0 ∈ polynomialRing (F := F₅) straightFirst ∧
    y₂ 0 ∈ polynomialRing (F := F₅) straightFirst := by
  let P := polynomialRing (F := F₅) straightFirst
  have hv := coordinate_mem straightFirst
  have hc : c₁ ∈ P := hv 0
  have hw : w ∈ P := hv 3
  have ht : t ∈ P := by
    have he : t = straightFirst 2 + c₁*w := by dsimp [straightFirst]; ring
    rw [he]; exact P.add_mem (hv 2) (P.mul_mem hc hw)
  have hc₂ : c₂ ∈ P := by
    have he : c₂ = straightFirst 1 + c₁*t - 3*c₁^2*w := by dsimp [straightFirst]; ring
    rw [he]
    exact P.sub_mem (P.add_mem (hv 1) (P.mul_mem hc ht))
      (P.mul_mem (P.mul_mem (P.natCast_mem 3) (P.pow_mem hc 2)) hw)
  exact ⟨hc, hc₂, by simpa [y₁, first, monomial] using ht,
    by simpa [y₂, second, monomial] using hw⟩

theorem last_polynomials :
    c₁ ∈ polynomialRing (F := F₅) straightLast ∧
    c₂ ∈ polynomialRing (F := F₅) straightLast ∧
    y₁ 5 ∈ polynomialRing (F := F₅) straightLast ∧
    y₂ 5 ∈ polynomialRing (F := F₅) straightLast := by
  let P := polynomialRing (F := F₅) straightLast
  have hv := coordinate_mem straightLast
  have hc₂ : c₂ ∈ P := hv 0
  have hy : y₂ 5 ∈ P := hv 3
  have hx : y₁ 5 ∈ P := by
    have he : y₁ 5 = straightLast 2 + 2*c₂ := by dsimp [straightLast]; ring
    rw [he]; exact P.add_mem (hv 2) (P.mul_mem (P.natCast_mem 2) hc₂)
  refine ⟨?_, hc₂, hx, hy⟩
  have he : c₁ = straightLast 1 + c₂*(y₁ 5)^2*y₂ 5 -
      2*c₂^2*y₁ 5*y₂ 5 - 2*c₂^3*y₂ 5 := by dsimp [straightLast]; ring
  rw [he]
  aesop (add safe apply [P.sub_mem, P.add_mem, P.mul_mem, P.pow_mem, P.natCast_mem])

theorem middle_polynomials (a : F₅) :
    c₁ ∈ polynomialRing (F := F₅) (straightMiddle a) ∧
    c₂ ∈ polynomialRing (F := F₅) (straightMiddle a) ∧
    y₁ 3 ∈ polynomialRing (F := F₅) (straightMiddle a) ∧
    (middleDenominator a)⁻¹ ∈ polynomialRing (F := F₅) (straightMiddle a) := by
  let P := polynomialRing (F := F₅) (straightMiddle a)
  have hv := coordinate_mem (straightMiddle a)
  have he : c₂ = straightMiddle a 0 + algebraMap F₅ K a := by
    dsimp [straightMiddle, middleSlice]; ring
  have hq : c₂ ∈ P := by rw [he]; exact P.add_mem (hv 0) (P.algebraMap_mem a)
  refine ⟨?_, hq, ?_, ?_⟩
  · rw [(middle_inverse a).2.2.2]
    aesop (add safe apply [P.add_mem, P.mul_mem, P.pow_mem, P.natCast_mem])
  · rw [(middle_inverse a).2.1]
    aesop (add safe apply [P.sub_mem, P.mul_mem, P.pow_mem, P.natCast_mem, P.one_mem])
  · rw [(middle_inverse a).1]
    aesop (add safe apply [P.sub_mem, P.mul_mem, P.natCast_mem, P.one_mem])

private theorem polynomial_le_field (v : Fin 4 → K) :
    polynomialRing (F := F₅) v ≤ (IntermediateField.adjoin F₅ (Set.range v)).toSubalgebra :=
  Algebra.adjoin_le (IntermediateField.subset_adjoin _ _)

theorem independent_of_chart_recovery (i : Fin 6) (v : Fin 4 → K)
    (hc₁ : c₁ ∈ polynomialRing (F := F₅) v)
    (hc₂ : c₂ ∈ polynomialRing (F := F₅) v)
    (hx : y₁ i ∈ polynomialRing (F := F₅) v)
    (hy : y₂ i ∈ IntermediateField.adjoin F₅ (Set.range v)) :
    AlgebraicIndependent F₅ v := by
  have hle : polynomialRing (F := F₅) v ≤
      (IntermediateField.adjoin F₅ (Set.range v)).toSubalgebra := polynomial_le_field _
  have htop := chart_generators_field i (IntermediateField.adjoin F₅ (Set.range v))
    (hle hc₁) (hle hc₂) (hle hx) hy
  have : Algebra.IsAlgebraic (Algebra.adjoin F₅ (Set.range v)) K := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₅ v
    coordinates_independent.cardinalMk_le_trdeg).1

theorem first_independent : AlgebraicIndependent F₅ straightFirst :=
  independent_of_chart_recovery 0 straightFirst first_polynomials.1 first_polynomials.2.1
    first_polynomials.2.2.1 (polynomial_le_field _ first_polynomials.2.2.2)

theorem last_independent : AlgebraicIndependent F₅ straightLast :=
  independent_of_chart_recovery 5 straightLast last_polynomials.1 last_polynomials.2.1
    last_polynomials.2.2.1 (polynomial_le_field _ last_polynomials.2.2.2)

theorem middle_independent (a : F₅) : AlgebraicIndependent F₅ (straightMiddle a) := by
  apply independent_of_chart_recovery 3 _ (middle_polynomials a).1
    (middle_polynomials a).2.1 (middle_polynomials a).2.2.1
  let M := IntermediateField.adjoin F₅ (Set.range (straightMiddle a))
  have hinv : (middleDenominator a)⁻¹ ∈ M :=
    polynomial_le_field _ (middle_polynomials a).2.2.2
  have hy : straightMiddle a 3 ∈ M := IntermediateField.subset_adjoin _ _ (Set.mem_range_self 3)
  have he : y₂ 3 = straightMiddle a 3 * middleDenominator a := by
    dsimp [straightMiddle]
    exact (div_mul_cancel₀ _ (middle_denominator_nonzero a)).symm
  rw [he]
  exact M.mul_mem hy (by simpa using M.inv_mem hinv)

def firstRing : Subalgebra F₅ K := (chartRing 0).restrictScalars F₅
def lastRing : Subalgebra F₅ K := (chartRing 5).restrictScalars F₅
def middleRing (a : F₅) : Subalgebra F₅ K :=
  (chartRing 3).restrictScalars F₅ ⊔ Algebra.adjoin F₅ { (middleDenominator a)⁻¹ }

theorem constants_mem_chart (i : Fin 6) : c₁ ∈ chartRing i ∧ c₂ ∈ chartRing i :=
  ⟨inputs_mem i 0, inputs_mem i 1⟩

theorem first_polynomial_le : polynomialRing (F := F₅) straightFirst ≤ firstRing := by
  apply Algebra.adjoin_le
  rintro x ⟨i,rfl⟩
  have hc := (constants_mem_chart 0).1
  have hd := (constants_mem_chart 0).2
  have ht : t ∈ firstRing := by simpa [firstRing, y₁, first, monomial] using y₁_mem 0
  have hw : w ∈ firstRing := by simpa [firstRing, y₂, second, monomial] using y₂_mem 0
  change c₁ ∈ firstRing at hc
  change c₂ ∈ firstRing at hd
  fin_cases i <;> dsimp [straightFirst]
  all_goals aesop (add safe apply [firstRing.sub_mem, firstRing.add_mem, firstRing.mul_mem, firstRing.pow_mem, firstRing.natCast_mem])

theorem last_polynomial_le : polynomialRing (F := F₅) straightLast ≤ lastRing := by
  apply Algebra.adjoin_le
  rintro x ⟨i,rfl⟩
  have hc : c₁ ∈ lastRing := (constants_mem_chart 5).1
  have hd : c₂ ∈ lastRing := (constants_mem_chart 5).2
  have hx : y₁ 5 ∈ lastRing := y₁_mem 5
  have hy : y₂ 5 ∈ lastRing := y₂_mem 5
  fin_cases i <;> dsimp [straightLast]
  all_goals aesop (add safe apply [lastRing.sub_mem, lastRing.add_mem, lastRing.mul_mem, lastRing.pow_mem, lastRing.natCast_mem])

theorem middle_denominator_mem (a : F₅) : middleDenominator a ∈ chartRing 3 := by
  have hs : middleSlice a ∈ chartRing 3 :=
    (chartRing 3).sub_mem (constants_mem_chart 3).2 (by
      rw [IsScalarTower.algebraMap_apply F₅ k K]
      exact (chartRing 3).algebraMap_mem (algebraMap F₅ k a))
  exact (chartRing 3).add_mem (chartRing 3).one_mem
    ((chartRing 3).mul_mem ((chartRing 3).mul_mem ((chartRing 3).natCast_mem 3) hs) (y₂_mem 3))

theorem middle_polynomial_le (a : F₅) :
    polynomialRing (F := F₅) (straightMiddle a) ≤ middleRing a := by
  apply Algebra.adjoin_le
  rintro x ⟨i,rfl⟩
  let A := middleRing a
  have hle : (chartRing 3).restrictScalars F₅ ≤ A := le_sup_left
  have hc : c₁ ∈ A := hle (constants_mem_chart 3).1
  have hs : middleSlice a ∈ A := A.sub_mem (hle (constants_mem_chart 3).2) (A.algebraMap_mem a)
  have hx : y₁ 3 ∈ A := hle (y₁_mem 3)
  have hy : y₂ 3 ∈ A := hle (y₂_mem 3)
  have hh : middleDenominator a ∈ A := hle (middle_denominator_mem a)
  have hi : (middleDenominator a)⁻¹ ∈ A :=
    (show Algebra.adjoin F₅ _ ≤ A from le_sup_right) (Algebra.subset_adjoin (by simp))
  fin_cases i <;> dsimp [straightMiddle]
  all_goals try rw [div_eq_mul_inv]
  all_goals aesop (add safe apply [A.sub_mem, A.add_mem, A.mul_mem, A.pow_mem, A.natCast_mem])

theorem first_localization : firstRing ≤ hull (polynomialRing (F := F₅) straightFirst) firstRing :=
  chart_le_hull 0 first_polynomial_le le_rfl
    (le_hull _ _ first_polynomials.1) (le_hull _ _ first_polynomials.2.1)
    (le_hull _ _ first_polynomials.2.2.1) (le_hull _ _ first_polynomials.2.2.2)

theorem last_localization : lastRing ≤ hull (polynomialRing (F := F₅) straightLast) lastRing :=
  chart_le_hull 5 last_polynomial_le le_rfl
    (le_hull _ _ last_polynomials.1) (le_hull _ _ last_polynomials.2.1)
    (le_hull _ _ last_polynomials.2.2.1) (le_hull _ _ last_polynomials.2.2.2)

theorem middle_localization (a : F₅) :
    middleRing a ≤ hull (polynomialRing (F := F₅) (straightMiddle a)) (middleRing a) := by
  let P := polynomialRing (F := F₅) (straightMiddle a)
  let A := middleRing a
  have hle := le_hull P A
  have hy : y₂ 3 ∈ hull P A := by
    refine ⟨(middleDenominator a)⁻¹, (middle_polynomials a).2.2.2,
      inv_ne_zero (middle_denominator_nonzero a), ?_, ?_⟩
    · simpa using (show (chartRing 3).restrictScalars F₅ ≤ A from le_sup_left)
        (middle_denominator_mem a)
    · exact (show y₂ 3 / middleDenominator a ∈ P from coordinate_mem (straightMiddle a) 3)
  apply sup_le
  · exact chart_le_hull 3 (middle_polynomial_le a) le_sup_left
      (hle (middle_polynomials a).1) (hle (middle_polynomials a).2.1)
      (hle (middle_polynomials a).2.2.1) hy
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hle (middle_polynomials a).2.2.2

end
end Red61.Charts

namespace Red61.Charts

open Fan Fields
noncomputable section
set_option maxRecDepth 4096

/-- The common dense torus, as a subalgebra of the fixed function field. -/
def torusRing : Subalgebra k K := Algebra.adjoin k (Set.range monomial)

theorem monomial_mem_torus (v : Lattice) : monomial v ∈ torusRing :=
  Algebra.subset_adjoin ⟨v,rfl⟩

theorem chart_le_torus (i : Fin 6) : chartRing i ≤ torusRing := by
  apply Algebra.adjoin_le
  intro x hx
  rcases hx with rfl | hx
  · exact monomial_mem_torus _
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ monomial_mem_torus _

theorem monomial_neg (v : Lattice) : monomial (-v) = (monomial v)⁻¹ := by
  simpa using monomial_zsmul (-1) v

def expandInChart (i : Fin 6) (v : Lattice) : Lattice :=
  v.1 • tExponent i + v.2 • wExponent i

theorem expandInChart_spec (i : Fin 6) (v : Lattice) :
    inCoordinates i (expandInChart i v) = v := by
  rcases v with ⟨a,b⟩
  fin_cases i <;> ext <;>
    simp [expandInChart, inCoordinates, tExponent, wExponent, first, second] <;> ring

theorem torus_le_of_coordinates (i : Fin 6) (E : Subalgebra k K)
    (h₁ : y₁ i ∈ E) (h₂ : y₂ i ∈ E)
    (hi₁ : (y₁ i)⁻¹ ∈ E) (hi₂ : (y₂ i)⁻¹ ∈ E) : torusRing ≤ E := by
  apply Algebra.adjoin_le
  rintro x ⟨v,rfl⟩
  rw [← expandInChart_spec i v, monomial_in_coordinates]
  exact E.mul_mem (zpow_mem_of_inv_mem h₁ hi₁ _) (zpow_mem_of_inv_mem h₂ hi₂ _)

def torusDenominator (i : Fin 6) : chartRing i :=
  ⟨y₁ i * y₂ i, (chartRing i).mul_mem (y₁_mem i) (y₂_mem i)⟩

theorem torus_adjoin_inverse (i : Fin 6) :
    torusRing = chartRing i ⊔ Algebra.adjoin k ({(y₁ i * y₂ i)⁻¹} : Set K) := by
  let E := chartRing i ⊔ Algebra.adjoin k ({(y₁ i * y₂ i)⁻¹} : Set K)
  have h₁ : y₁ i ∈ E := (show chartRing i ≤ E from le_sup_left) (y₁_mem i)
  have h₂ : y₂ i ∈ E := (show chartRing i ≤ E from le_sup_left) (y₂_mem i)
  have hi : (y₁ i * y₂ i)⁻¹ ∈ E :=
    (show Algebra.adjoin k _ ≤ E from le_sup_right) (Algebra.subset_adjoin (by simp))
  have hn₁ : y₁ i ≠ 0 := monomial_nonzero _
  have hn₂ : y₂ i ≠ 0 := monomial_nonzero _
  apply le_antisymm
  · apply torus_le_of_coordinates i E h₁ h₂
    · have he : y₂ i * (y₁ i * y₂ i)⁻¹ = (y₁ i)⁻¹ := by field_simp
      exact he ▸ E.mul_mem h₂ hi
    · have he : y₁ i * (y₁ i * y₂ i)⁻¹ = (y₂ i)⁻¹ := by field_simp
      exact he ▸ E.mul_mem h₁ hi
  · apply sup_le (chart_le_torus i)
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [show y₁ i * y₂ i = monomial (first i + second i) from (monomial_mul _ _).symm,
      ← monomial_neg]
    exact monomial_mem_torus _

/-- Distinct maximal cones with no common ray. -/
def NonAdjacent (i j : Fin 6) : Prop :=
  i ≠ j ∧ next (leftRay i) ≠ leftRay j ∧ next (leftRay j) ≠ leftRay i

instance (i j : Fin 6) : Decidable (NonAdjacent i j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Nonnegative monomial certificates for the inverse of each chart-coordinate product.
The entries for coincident or adjacent charts are unused. -/
def inverseCertificate : Fin 6 → Fin 6 → Fin 4 → ℕ :=
  ![![![0,0,0,0], ![0,0,0,0], ![0,0,4,1], ![0,0,0,0], ![0,0,7,4], ![0,0,7,3]],
    ![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![1,0,0,1], ![2,0,1,0], ![2,0,1,1]],
    ![![2,0,0,1], ![0,0,0,0], ![0,0,0,0], ![0,0,0,1], ![0,0,0,0], ![0,1,0,1]],
    ![![0,0,0,0], ![0,0,3,1], ![0,0,0,1], ![0,0,0,0], ![0,1,0,1], ![0,0,0,0]],
    ![![1,0,1,0], ![1,0,1,0], ![0,0,0,0], ![0,0,0,1], ![0,0,0,0], ![0,0,0,0]],
    ![![1,0,1,0], ![1,0,1,0], ![0,0,0,1], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0]]]

theorem inverseCertificate_spec (i j : Fin 6) (h : NonAdjacent i j) :
    (inverseCertificate i j 0 : ℤ) • first i +
      (inverseCertificate i j 1 : ℤ) • second i +
      (inverseCertificate i j 2 : ℤ) • first j +
      (inverseCertificate i j 3 : ℤ) • second j = -(first i + second i) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [NonAdjacent, leftRay, next, inverseCertificate, first, second, Prod.ext_iff] at *

def pairRing (i j : Fin 6) : Subalgebra k K := chartRing i ⊔ chartRing j

theorem inverse_product_mem_pair (i j : Fin 6) (h : NonAdjacent i j) :
    (y₁ i * y₂ i)⁻¹ ∈ pairRing i j := by
  have h₁ : y₁ i ∈ pairRing i j := (show chartRing i ≤ pairRing i j from le_sup_left) (y₁_mem i)
  have h₂ : y₂ i ∈ pairRing i j := (show chartRing i ≤ pairRing i j from le_sup_left) (y₂_mem i)
  have h₃ : y₁ j ∈ pairRing i j := (show chartRing j ≤ pairRing i j from le_sup_right) (y₁_mem j)
  have h₄ : y₂ j ∈ pairRing i j := (show chartRing j ≤ pairRing i j from le_sup_right) (y₂_mem j)
  have he := congrArg monomial (inverseCertificate_spec i j h)
  simp only [monomial_mul, monomial_zsmul, zpow_natCast, monomial_neg] at he
  change y₁ i ^ _ * y₂ i ^ _ * y₁ j ^ _ * y₂ j ^ _ = (y₁ i * y₂ i)⁻¹ at he
  rw [← he]
  exact (pairRing i j).mul_mem
    ((pairRing i j).mul_mem ((pairRing i j).mul_mem
      ((pairRing i j).pow_mem h₁ _) ((pairRing i j).pow_mem h₂ _))
      ((pairRing i j).pow_mem h₃ _)) ((pairRing i j).pow_mem h₄ _)

theorem nonAdjacent_pair_eq_torus (i j : Fin 6) (h : NonAdjacent i j) :
    pairRing i j = torusRing := by
  apply le_antisymm (sup_le (chart_le_torus i) (chart_le_torus j))
  rw [torus_adjoin_inverse i]
  apply sup_le le_sup_left
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  exact hx ▸ inverse_product_mem_pair i j h

@[instance_reducible] def pairAlgebra (i j : Fin 6) : Algebra (chartRing i) (pairRing i j) :=
  (Subalgebra.inclusion (show chartRing i ≤ pairRing i j from le_sup_left)).toRingHom.toAlgebra

/-- For a nonadjacent pair, invert both coordinates; the reverse direction follows by symmetry. -/
theorem nonAdjacent_pair_isLocalization (i j : Fin 6) (h : NonAdjacent i j) :
    letI := pairAlgebra i j
    IsLocalization.Away (torusDenominator i) (pairRing i j) := by
  apply subalgebra_isLocalizationAway
  · exact mul_ne_zero (monomial_nonzero _) (monomial_nonzero _)
  · exact inverse_product_mem_pair i j h
  · change pairRing i j ≤ chartRing i ⊔ Algebra.adjoin k ({(y₁ i * y₂ i)⁻¹} : Set K)
    rw [nonAdjacent_pair_eq_torus i j h, torus_adjoin_inverse i]

theorem pair_cases (i j : Fin 6) :
    i = j ∨
    (∃ a : Fin 6, i = cyclicChart a ∧ j = cyclicChart (next a)) ∨
    (∃ a : Fin 6, j = cyclicChart a ∧ i = cyclicChart (next a)) ∨ NonAdjacent i j := by
  revert i j
  decide

theorem pair_localization_of_eq (i j : Fin 6) (d : chartRing i) (hd : (d : K) ≠ 0)
    (he : pairRing i j = chartRing i ⊔ Algebra.adjoin k ({(d : K)⁻¹} : Set K)) :
    letI := pairAlgebra i j
    IsLocalization.Away d (pairRing i j) := by
  apply subalgebra_isLocalizationAway
  · exact hd
  · rw [he]
    exact (show Algebra.adjoin k _ ≤ chartRing i ⊔ Algebra.adjoin k _ from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  · exact he.le

/-- Every ordered pair of charts has a principal affine overlap, including the diagonal. -/
theorem every_pair_isLocalization (i j : Fin 6) :
    letI := pairAlgebra i j
    ∃ d : chartRing i, IsLocalization.Away d (pairRing i j) := by
  rcases pair_cases i j with h | ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩ | h
  · subst j
    refine ⟨1, ?_⟩
    apply subalgebra_isLocalizationAway
    · exact one_ne_zero
    · simpa only [OneMemClass.coe_one, inv_one] using (pairRing i i).one_mem
    · change chartRing i ⊔ chartRing i ≤
        chartRing i ⊔ Algebra.adjoin k ({(1 : K)⁻¹} : Set K)
      exact sup_le le_sup_left le_sup_left
  · exact ⟨overlapDenominator a 0, overlap_isLocalization a 0⟩
  · refine ⟨overlapDenominator a 1, pair_localization_of_eq _ _ _ ?_ ?_⟩
    · change chartCoordinates (overlapChart a 1) (invertedIndex a 1) ≠ 0
      rw [chartCoordinate_monomial]
      exact monomial_nonzero _
    · change chartRing (cyclicChart (next a)) ⊔ chartRing (cyclicChart a) = _
      rw [sup_comm]
      exact overlap_adjoin_inverse a 1
  · exact ⟨torusDenominator i, nonAdjacent_pair_isLocalization i j h⟩

end
end Red61.Charts

/-! The six affine quotient rings and all their principal overlap localizations. -/

namespace Red61.Charts

open Fields AffineGluing FrobeniusDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false

instance ell_coefficient_tower : IsScalarTower ell k K :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

theorem field_fifth_power_invariant (x : K) : x^5 ∈ L := by
  change delta (x^5) = 0
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    CharP.cast_eq_zero K 5, zero_mul]

def ellChartRing (i : Fin 6) : Subalgebra ell K := (chartRing i).restrictScalars ell
def ellPairRing (i j : Fin 6) : Subalgebra ell K := (pairRing i j).restrictScalars ell

theorem ellChart_sup (i j : Fin 6) : ellChartRing i ⊔ ellChartRing j = ellPairRing i j :=
  (restrictScalars_sup (chartRing i) (chartRing j)).symm

theorem ellChart_le_pair (i j : Fin 6) : ellChartRing i ≤ ellPairRing i j :=
  fun _ hx ↦ (show chartRing i ≤ pairRing i j from le_sup_left) hx

def invariantChartRing (i : Fin 6) : Subalgebra ell L := fixed L (ellChartRing i)
def invariantPairRing (i j : Fin 6) : Subalgebra ell L := fixed L (ellPairRing i j)

theorem chart_kernel_iff (i : Fin 6) (x : chartRing i) :
    chartDerivation i x = 0 ↔ (x : K) ∈ L := by
  rw [Subtype.ext_iff]
  change monomial (scale i) * delta (x : K) = 0 ↔ delta (x : K) = 0
  simp only [mul_eq_zero, monomial_nonzero, false_or]

/-- The subalgebra in L is exactly the kernel of the previously constructed local derivation. -/
def invariantChartKernelEquiv (i : Fin 6) :
    invariantChartRing i ≃ₐ[ell] invariantAlgebra (chartDerivation i) where
  toFun x := ⟨⟨(x.val : K), x.property⟩, (chart_kernel_iff i _).mpr x.val.property⟩
  invFun x := ⟨⟨(x.val : K), (chart_kernel_iff i x.val).mp x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A proof for every ordered pair, including disjoint cones and self-intersections. -/
theorem invariant_pair_eq_sup (i j : Fin 6) :
    invariantPairRing i j = invariantChartRing i ⊔ invariantChartRing j := by
  obtain ⟨d,hd⟩ := every_pair_isLocalization i j
  let := inclusionAlgebra (show ellChartRing i ≤ ellChartRing i ⊔ ellChartRing j from le_sup_left)
  have hloc : IsLocalization.Away (show ellChartRing i from d)
      ↥(ellChartRing i ⊔ ellChartRing j) := by
    exact localization_congr (ellChart_le_pair i j)
      le_sup_left (ellChart_sup i j).symm d hd
  change fixed L (ellPairRing i j) = _
  rw [← ellChart_sup]
  exact fixed_sup L 5 field_fifth_power_invariant _ _ d hloc

theorem invariant_pair_isLocalization (i j : Fin 6) :
    letI := inclusionAlgebra
      (show invariantChartRing i ≤ invariantChartRing i ⊔ invariantChartRing j from le_sup_left)
    ∃ d : invariantChartRing i,
      IsLocalization.Away d ↥(invariantChartRing i ⊔ invariantChartRing j) := by
  obtain ⟨d,hd⟩ := every_pair_isLocalization i j
  refine ⟨powerElement L 5 field_fifth_power_invariant (ellChartRing i) d, ?_⟩
  exact localization_congr
    (fixed_mono L (ellChart_le_pair i j))
    le_sup_left (invariant_pair_eq_sup i j) _
    (fixed_isLocalization L 5 field_fifth_power_invariant
      (ellChart_le_pair i j) d hd)

instance invariantChart_isFractionRing (i : Fin 6) : IsFractionRing (invariantChartRing i) L := by
  have : IsFractionRing (ellChartRing i) K := chart_isFractionRing i
  exact fixed_isFractionRing L 5 field_fifth_power_invariant (ellChartRing i)

/-- Inclusion of the invariant functions into the original chart ring. -/
def invariantChartEmbedding (i : Fin 6) : invariantChartRing i →ₐ[ell] chartRing i :=
  embed L (ellChartRing i)

def invariantOverlapEmbedding (i j : Fin 6) :
    ↥(invariantChartRing i ⊔ invariantChartRing j) →ₐ[ell] ellPairRing i j :=
  (embed L (ellPairRing i j)).comp
    (Subalgebra.inclusion (le_of_eq (invariant_pair_eq_sup i j).symm))

end
end Red61.Charts

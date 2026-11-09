import Geonormal.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # The five charts of the characteristic-19 surface

The surface `X` is a double cover of the smooth projective toric surface of the lattice
polygon with vertices `(0,0)`, `(0,2)`, `(8,0)`, `(5,1)`, `(1,2)` in the exponents of
`(t, x)`. Each vertex gives toric coordinates `e₁, e₂`, Laurent monomials in `t, x`, and
the chart of `X` over it is `y_i² = g_i(e₁, e₂)` with `y_i = y · (monomial)`.
-/

namespace Geonormal

noncomputable section

abbrev Lattice := ℤ × ℤ

/-- The coordinate `t` of `E = k(x, t)`. -/
def tE : E := algebraMap R₂ E (MvPolynomial.X 1)
/-- The coordinate `x` of `E = k(x, t)`. -/
def xE : E := algebraMap R₂ E (MvPolynomial.X 0)
/-- The constant `c` in `E`. -/
def cE : E := algebraMap k E c

theorem tE_ne_zero : tE ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R₂ E)).mpr (MvPolynomial.X_ne_zero 1)

theorem xE_ne_zero : xE ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R₂ E)).mpr (MvPolynomial.X_ne_zero 0)

theorem gE_eq : gE = xE ^ 3 + cE ^ 2 * tE ^ 7 * xE + tE := by
  have hc : algebraMap R₂ E (MvPolynomial.C c) = cE :=
    (IsScalarTower.algebraMap_apply k R₂ E c).symm
  simp [gE, gPoly, xE, tE, hc]

/-- The Laurent monomial `t^a x^b` in `E`. -/
def monoE (v : Lattice) : E := tE ^ v.1 * xE ^ v.2

theorem monoE_ne_zero (v : Lattice) : monoE v ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ tE_ne_zero) (zpow_ne_zero _ xE_ne_zero)

theorem monoE_add (v w : Lattice) : monoE (v + w) = monoE v * monoE w := by
  simp only [monoE, Prod.fst_add, Prod.snd_add, zpow_add₀ tE_ne_zero, zpow_add₀ xE_ne_zero]
  ring

theorem monoE_zsmul (n : ℤ) (v : Lattice) : monoE (n • v) = monoE v ^ n := by
  simp only [monoE, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zpow, ← zpow_mul]
  ring_nf

theorem monoE_zero : monoE 0 = 1 := by simp [monoE]

/-- First toric coordinate of each chart, as an exponent of `(t, x)`. -/
def first : Fin 5 → Lattice := ![(1, 0), (1, 0), (-1, 0), (3, -1), (-1, 0)]
/-- Second toric coordinate of each chart. -/
def second : Fin 5 → Lattice := ![(0, 1), (0, -1), (-3, 1), (-4, 1), (4, -1)]
/-- The fibre coordinate of each chart is `y · t^a x^b` for these exponents. -/
def yScale : Fin 5 → Lattice := ![(0, 0), (0, -2), (-5, 0), (-2, -1), (2, -2)]
/-- `t` in the toric coordinates of each chart. -/
def tExponent : Fin 5 → Lattice := ![(1, 0), (1, 0), (-1, 0), (-1, -1), (-1, 0)]
/-- `x` in the toric coordinates of each chart. -/
def xExponent : Fin 5 → Lattice := ![(0, 1), (0, -1), (-3, 1), (-4, -3), (-4, -1)]

def inCoordinates (i : Fin 5) (v : Lattice) : Lattice := v.1 • first i + v.2 • second i

theorem inverse_lattice (i : Fin 5) :
    inCoordinates i (tExponent i) = (1, 0) ∧ inCoordinates i (xExponent i) = (0, 1) := by
  fin_cases i <;> decide

/-- The coordinates `(c, e₁, e₂)` of each chart in `E`. -/
def coordE (i : Fin 5) : Fin 3 → E := ![cE, monoE (first i), monoE (second i)]

theorem monoE_inCoordinates (i : Fin 5) (v : Lattice) :
    monoE (inCoordinates i v) = monoE (first i) ^ v.1 * monoE (second i) ^ v.2 := by
  rw [inCoordinates, monoE_add, monoE_zsmul, monoE_zsmul]

theorem tE_coordinates (i : Fin 5) :
    tE = monoE (first i) ^ (tExponent i).1 * monoE (second i) ^ (tExponent i).2 := by
  rw [← monoE_inCoordinates, (inverse_lattice i).1]
  simp [monoE]

theorem xE_coordinates (i : Fin 5) :
    xE = monoE (first i) ^ (xExponent i).1 * monoE (second i) ^ (xExponent i).2 := by
  rw [← monoE_inCoordinates, (inverse_lattice i).2]
  simp [monoE]

/-! ## Transcendence -/

theorem c_transcendental : Transcendental F₁₉ c := by
  have h := (MvPolynomial.algebraicIndependent_X (Fin 1) F₁₉).map'
    (f := IsScalarTower.toAlgHom F₁₉ P₁ k) (IsFractionRing.injective P₁ k)
  exact (algebraicIndependent_unique_type_iff.mp h : Transcendental F₁₉ _)

theorem standard_independent : AlgebraicIndependent F₁₉
    (Sum.elim ![xE, tE] (algebraMap k E ∘ ![c])) := by
  have hx : AlgebraicIndependent F₁₉ ![c] :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using c_transcendental)
  have hy : AlgebraicIndependent k ![xE, tE] := by
    have h := (MvPolynomial.algebraicIndependent_X (Fin 2) k).map'
      (f := IsScalarTower.toAlgHom k R₂ E) (IsFractionRing.injective R₂ E)
    convert h using 1
    ext j
    fin_cases j <;> rfl
  exact AlgebraicIndependent.sumElim_comp hx hy

theorem three_le_trdeg : (3 : Cardinal) ≤ Algebra.trdeg F₁₉ E := by
  have := standard_independent.cardinalMk_le_trdeg
  simpa using this

/-- `E` is generated as a field over `F₁₉` by `c`, `t`, `x`. -/
theorem standard_generation :
    IntermediateField.adjoin F₁₉ ({cE, tE, xE} : Set E) = ⊤ := by
  set M := IntermediateField.adjoin F₁₉ ({cE, tE, xE} : Set E)
  have hc : cE ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have ht : tE ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have hx : xE ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have hP₁ (a : P₁) : algebraMap k E (algebraMap P₁ k a) ∈ M := by
    induction a using MvPolynomial.induction_on with
    | C a =>
      have h := RingHom.congr_fun (Subsingleton.elim ((algebraMap P₁ E).comp MvPolynomial.C)
        (algebraMap F₁₉ E)) a
      rw [RingHom.comp_apply] at h
      rw [← IsScalarTower.algebraMap_apply, h]
      exact M.algebraMap_mem a
    | add a b ha hb => simpa only [map_add] using M.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul]
      refine M.mul_mem ha ?_
      rw [Subsingleton.elim j 0]
      exact hc
  have hk (a : k) : algebraMap k E a ∈ M := by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := P₁) a
    rw [map_div₀]
    exact M.div_mem (hP₁ u) (hP₁ v)
  have hR (a : R₂) : algebraMap R₂ E a ∈ M := by
    induction a using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hk a
    | add a b ha hb => simpa only [map_add] using M.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul]
      refine M.mul_mem ha ?_
      fin_cases j
      · exact hx
      · exact ht
  rw [eq_top_iff]
  intro z _
  obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := R₂) z
  exact M.div_mem (hR u) (hR v)

theorem chart_generation (i : Fin 5) :
    IntermediateField.adjoin F₁₉ (Set.range (coordE i)) = ⊤ := by
  set M := IntermediateField.adjoin F₁₉ (Set.range (coordE i))
  have h₁ : monoE (first i) ∈ M := IntermediateField.subset_adjoin _ _ ⟨1, rfl⟩
  have h₂ : monoE (second i) ∈ M := IntermediateField.subset_adjoin _ _ ⟨2, rfl⟩
  have hc : cE ∈ M := IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩
  have ht : tE ∈ M := by
    rw [tE_coordinates i]
    exact M.mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)
  have hx : xE ∈ M := by
    rw [xE_coordinates i]
    exact M.mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)
  rw [eq_top_iff, ← standard_generation, IntermediateField.adjoin_le_iff]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hc
  · exact ht
  · exact hx

/-- The chart coordinates `(c, e₁, e₂)` are algebraically independent over `F₁₉`. -/
theorem coordE_independent (i : Fin 5) : AlgebraicIndependent F₁₉ (coordE i) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin F₁₉ (Set.range (coordE i))) E := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, chart_generation]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₁₉ (coordE i)
    (by simpa using three_le_trdeg)).1

end
end Geonormal

namespace Geonormal

noncomputable section

/-! ## The chart rings in the function field -/

/-- The Laurent monomial `t^a x^b` in `F`. -/
def monoF (v : Lattice) : F := algebraMap E F (monoE v)

theorem monoF_ne_zero (v : Lattice) : monoF v ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap E F).injective).mpr (monoE_ne_zero v)

theorem monoF_add (v w : Lattice) : monoF (v + w) = monoF v * monoF w := by
  rw [monoF, monoE_add, map_mul]; rfl

theorem monoF_zero : monoF 0 = 1 := by rw [monoF, monoE_zero, map_one]

theorem monoF_neg (v : Lattice) : monoF (-v) = (monoF v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← monoF_add, neg_add_cancel, monoF_zero]

theorem monoF_nsmul (n : ℕ) (v : Lattice) : monoF (n • v) = monoF v ^ n := by
  induction n with
  | zero => simp [monoF_zero]
  | succ n ih => rw [succ_nsmul, monoF_add, ih, pow_succ]

/-- The fibre coordinate `y_i = y · t^a x^b` of chart `i`. -/
def yc (i : Fin 5) : F := y * monoF (yScale i)

theorem yc_eq (i j : Fin 5) : yc j = yc i * monoF (yScale j - yScale i) := by
  rw [yc, yc, mul_assoc, ← monoF_add, add_sub_cancel]

/-- The coordinate ring of chart `i`, a subalgebra of the function field. -/
def chartRing (i : Fin 5) : Subalgebra k F :=
  Algebra.adjoin k {monoF (first i), monoF (second i), yc i}

theorem first_mem (i : Fin 5) : monoF (first i) ∈ chartRing i :=
  Algebra.subset_adjoin (by simp)

theorem second_mem (i : Fin 5) : monoF (second i) ∈ chartRing i :=
  Algebra.subset_adjoin (by simp)

theorem yc_mem (i : Fin 5) : yc i ∈ chartRing i :=
  Algebra.subset_adjoin (by simp)

/-- Exponents of a monomial in the toric coordinates of chart `i`. -/
def chartExp (i : Fin 5) (v : Lattice) : Lattice := v.1 • tExponent i + v.2 • xExponent i

theorem inCoordinates_add (i : Fin 5) (v w : Lattice) :
    inCoordinates i (v + w) = inCoordinates i v + inCoordinates i w := by
  simp only [inCoordinates, Prod.fst_add, Prod.snd_add, add_smul]
  abel

theorem inCoordinates_smul (i : Fin 5) (n : ℤ) (v : Lattice) :
    inCoordinates i (n • v) = n • inCoordinates i v := by
  simp only [inCoordinates, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add]

theorem inCoordinates_chartExp (i : Fin 5) (v : Lattice) : inCoordinates i (chartExp i v) = v := by
  rw [chartExp, inCoordinates_add, inCoordinates_smul, inCoordinates_smul,
    (inverse_lattice i).1, (inverse_lattice i).2]
  ext <;> simp

/-- A monomial with nonnegative exponents in the toric coordinates lies in the chart ring. -/
theorem monoF_mem (i : Fin 5) (v : Lattice) (h₁ : 0 ≤ (chartExp i v).1)
    (h₂ : 0 ≤ (chartExp i v).2) : monoF v ∈ chartRing i := by
  have hv : monoF v = monoF (first i) ^ (chartExp i v).1.toNat *
      monoF (second i) ^ (chartExp i v).2.toNat := by
    rw [← monoF_nsmul, ← monoF_nsmul, ← monoF_add]
    congr 1
    conv_lhs => rw [← inCoordinates_chartExp i v]
    rw [inCoordinates]
    congr 1 <;> rw [← natCast_zsmul] <;> congr 1 <;> simp [h₁, h₂]
  rw [hv]
  exact (chartRing i).mul_mem ((chartRing i).pow_mem (first_mem i) _)
    ((chartRing i).pow_mem (second_mem i) _)

end
end Geonormal

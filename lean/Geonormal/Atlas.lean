import Geonormal.Charts
import Red61.AlgebraicGeometry.Atlas

/-! # The atlas of the characteristic-19 surface

The five chart rings are glued along principal localizations. Adjacent vertices of the
polygon overlap after inverting the coordinate along their common edge; the other pairs
overlap on the torus. Every condition is an integer inequality on monomial exponents.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry

noncomputable section

/-- The neighbouring vertex along the first, respectively second, toric coordinate. -/
def nbr₁ : Fin 5 → Fin 5 := ![2, 4, 0, 2, 1]
def nbr₂ : Fin 5 → Fin 5 := ![1, 0, 3, 4, 3]

/-- The exponent of the element inverted on the overlap of charts `i` and `j`. -/
def overlapExponent (i j : Fin 5) : Lattice :=
  if j = i then 0 else if j = nbr₁ i then first i else if j = nbr₂ i then second i
  else first i + second i

/-- Coefficients writing part of the inverse denominator in the coordinates of chart `j`. -/
def splitCoeff : Fin 5 → Fin 5 → ℤ × ℤ :=
  ![![(0, 0), (0, 1), (1, 0), (5, 4), (5, 1)],
    ![(0, 1), (0, 0), (0, 1), (0, 1), (1, 0)],
    ![(1, 0), (4, 1), (0, 0), (1, 0), (0, 1)],
    ![(0, 1), (1, 0), (0, 1), (0, 0), (0, 1)],
    ![(0, 1), (1, 0), (0, 1), (0, 1), (0, 0)]]

def splitExponent (i j : Fin 5) : Lattice :=
  (splitCoeff i j).1 • first j + (splitCoeff i j).2 • second j

/-- Nonnegative exponents in the toric coordinates of chart `i`. -/
def NonnegIn (i : Fin 5) (v : Lattice) : Prop := 0 ≤ (chartExp i v).1 ∧ 0 ≤ (chartExp i v).2

instance (i : Fin 5) (v : Lattice) : Decidable (NonnegIn i v) := by
  unfold NonnegIn; infer_instance

theorem overlap_table (i j : Fin 5) :
    NonnegIn i (overlapExponent i j) ∧
    NonnegIn i (first j + (20 : ℤ) • overlapExponent i j) ∧
    NonnegIn i (second j + (20 : ℤ) • overlapExponent i j) ∧
    NonnegIn i (yScale j - yScale i + (20 : ℤ) • overlapExponent i j) ∧
    NonnegIn i (-overlapExponent i j - splitExponent i j) ∧
    NonnegIn j (splitExponent i j) := by
  fin_cases i <;> fin_cases j <;> decide

theorem monoF_mem_of_nonneg {i : Fin 5} {v : Lattice} (h : NonnegIn i v) :
    monoF v ∈ chartRing i :=
  monoF_mem i v h.1 h.2

/-- The denominator of the overlap of charts `i` and `j`, inside chart `i`. -/
def overlapDenominator (i j : Fin 5) : chartRing i :=
  ⟨monoF (overlapExponent i j), monoF_mem_of_nonneg (overlap_table i j).1⟩

theorem monoF_mem_sup_adjoin {i j : Fin 5} {v : Lattice}
    (h : NonnegIn i (v + (20 : ℤ) • overlapExponent i j)) :
    monoF v ∈ chartRing i ⊔ Algebra.adjoin k ({(monoF (overlapExponent i j))⁻¹} : Set F) := by
  have he : monoF v = monoF (v + (20 : ℤ) • overlapExponent i j) *
      ((monoF (overlapExponent i j))⁻¹) ^ 20 := by
    have h20 : (20 : ℤ) • overlapExponent i j = (20 : ℕ) • overlapExponent i j := by
      rw [← natCast_zsmul]; norm_num
    rw [h20, monoF_add, monoF_nsmul, inv_pow, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (monoF_ne_zero _)), mul_one]
  rw [he]
  exact Subalgebra.mul_mem _ (le_sup_left (a := chartRing i) (monoF_mem_of_nonneg h))
    (Subalgebra.pow_mem _ (le_sup_right (a := chartRing i)
      (Algebra.subset_adjoin (Set.mem_singleton _))) _)

theorem chart_localization (i j : Fin 5) :
    letI := inclusionAlgebra (show chartRing i ≤ chartRing i ⊔ chartRing j from le_sup_left)
    IsLocalization.Away (overlapDenominator i j) ↥(chartRing i ⊔ chartRing j) := by
  obtain ⟨-, hf, hs, hy, hsplit, hsplit'⟩ := overlap_table i j
  apply subalgebra_isLocalizationAway
  · exact monoF_ne_zero _
  · have he : (monoF (overlapExponent i j))⁻¹ =
        monoF (-overlapExponent i j - splitExponent i j) * monoF (splitExponent i j) := by
      rw [← monoF_add, sub_add_cancel, monoF_neg]
    change (monoF (overlapExponent i j))⁻¹ ∈ chartRing i ⊔ chartRing j
    rw [he]
    exact Subalgebra.mul_mem _ (le_sup_left (a := chartRing i) (monoF_mem_of_nonneg hsplit))
      (le_sup_right (a := chartRing i) (monoF_mem_of_nonneg hsplit'))
  · apply sup_le le_sup_left
    apply Algebra.adjoin_le
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact monoF_mem_sup_adjoin hf
    · exact monoF_mem_sup_adjoin hs
    · rw [yc_eq i j]
      exact Subalgebra.mul_mem _ (le_sup_left (a := chartRing i) (yc_mem i))
        (monoF_mem_sup_adjoin hy)

/-- The principal atlas of the surface. -/
def atlas : PrincipalAtlas k F where
  Index := Fin 5
  ring := chartRing
  localization i j := ⟨overlapDenominator i j, chart_localization i j⟩

/-- The regular projective surface `X` of Example `ex:p19`. -/
abbrev X19 : Scheme := atlas.glued

/-- Its structure morphism to `Spec k`. -/
abbrev xToBase : X19 ⟶ Spec (CommRingCat.of k) := atlas.toBase

instance : Nonempty atlas.Index := ⟨(0 : Fin 5)⟩
instance : Finite atlas.Index := inferInstanceAs (Finite (Fin 5))

theorem x_integral : IsIntegral X19 := inferInstance

theorem x_separated : IsSeparated xToBase := inferInstance

theorem chartRing_finiteType (i : Fin 5) : Algebra.FiniteType k (chartRing i) := by
  exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)

end
end Geonormal

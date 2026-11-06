import Mathlib.RingTheory.MvPolynomial.Ideal
import Red61.Surface.SixChartModel

/-! # Overlap certificates for the contracted charts

Formerly the modules `ContractionOverlaps`, `WeightedParameters`.
-/

/-! Exact denominator certificates for the four affine charts of X. -/

namespace Red61.Contraction

open Fields Charts Fan AffineGluing
noncomputable section

def coneDenominatorExponent : Fin 3 → Lattice := ![(0,-1),(5,-3),(5,-2)]
def keptDenominatorExponent : Fin 3 → Lattice := ![(0,1),(-3,1),(-5,2)]
def coneDenominatorCoefficients : Fin 3 → Fin 4 → ℕ :=
  ![![1,0,0,0], ![1,0,0,1], ![0,0,0,1]]
def keptDenominatorCoefficients : Fin 3 → Fin 2 → ℕ := ![![0,1], ![1,1], ![0,1]]

def pairVector (i : Fin 3) : Fin 6 → Lattice :=
  ![coneExponent 0, coneExponent 1, coneExponent 2, coneExponent 3,
    first (kept i), second (kept i)]
def coneLocalizationVector (i : Fin 3) : Fin 5 → Lattice :=
  ![coneExponent 0, coneExponent 1, coneExponent 2, coneExponent 3, -coneDenominatorExponent i]
def keptLocalizationVector (i : Fin 3) : Fin 3 → Lattice :=
  ![first (kept i), second (kept i), -keptDenominatorExponent i]

def coneInverseCoefficients : Fin 3 → Fin 6 → ℕ :=
  ![![0,0,0,0,0,1], ![0,0,0,1,0,5], ![0,0,0,0,0,1]]
def keptInverseCoefficients : Fin 3 → Fin 6 → ℕ :=
  ![![1,0,0,0,0,0], ![0,0,0,1,0,1], ![0,0,0,1,0,0]]
def keptInConeCoefficients : Fin 3 → Fin 2 → Fin 5 → ℕ :=
  ![![![0,1,0,0,1], ![0,0,0,0,1]],
    ![![1,0,2,0,1], ![0,1,1,0,1]],
    ![![0,0,1,0,0], ![0,0,0,0,1]]]
def coneInKeptCoefficients : Fin 3 → Fin 4 → Fin 3 → ℕ :=
  ![![![0,0,1], ![1,0,1], ![2,0,1], ![5,0,2]],
    ![![3,0,1], ![2,0,1], ![1,0,1], ![1,0,2]],
    ![![5,2,0], ![3,1,0], ![1,0,0], ![0,0,1]]]

theorem denominator_certificates (i : Fin 3) :
    coneDenominatorExponent i = combination coneExponent (coneDenominatorCoefficients i) ∧
    keptDenominatorExponent i = combination ![first (kept i), second (kept i)]
      (keptDenominatorCoefficients i) ∧
    -coneDenominatorExponent i = combination (pairVector i) (coneInverseCoefficients i) ∧
    -keptDenominatorExponent i = combination (pairVector i) (keptInverseCoefficients i) := by
  fin_cases i <;> norm_num [coneDenominatorExponent, keptDenominatorExponent,
    coneDenominatorCoefficients, keptDenominatorCoefficients, coneInverseCoefficients,
    keptInverseCoefficients, pairVector, coneExponent, kept, first, second,
    combination, Fin.sum_univ_succ, Prod.ext_iff]

theorem keptInCone_certificate (i : Fin 3) (a : Fin 2) :
    (![first (kept i), second (kept i)] : Fin 2 → Lattice) a =
      combination (coneLocalizationVector i) (keptInConeCoefficients i a) := by
  fin_cases i <;> fin_cases a <;> norm_num [coneLocalizationVector, keptInConeCoefficients,
    coneDenominatorExponent, coneExponent, kept, first, second, combination,
    Fin.sum_univ_succ, Prod.ext_iff]

theorem coneInKept_certificate (i : Fin 3) (a : Fin 4) :
    coneExponent a = combination (keptLocalizationVector i) (coneInKeptCoefficients i a) := by
  fin_cases i <;> fin_cases a <;> norm_num [keptLocalizationVector, coneInKeptCoefficients,
    keptDenominatorExponent, coneExponent, kept, first, second, combination,
    Fin.sum_univ_succ, Prod.ext_iff]

def coneDenominator (i : Fin 3) : coneRing :=
  ⟨monomial (coneDenominatorExponent i), by
    rw [(denominator_certificates i).1]
    exact combination_mem _ _ _ cone_generator_mem⟩

def keptDenominator (i : Fin 3) : chartRing (kept i) :=
  ⟨monomial (keptDenominatorExponent i), by
    rw [(denominator_certificates i).2.1]
    apply combination_mem
    intro a
    fin_cases a
    · exact y₁_mem _
    · exact y₂_mem _⟩

theorem pairVector_mem (i : Fin 3) (a : Fin 6) :
    monomial (pairVector i a) ∈ coneRing ⊔ chartRing (kept i) := by
  fin_cases a
  · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 0)
  · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 1)
  · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 2)
  · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 3)
  · exact (show chartRing (kept i) ≤ _ from le_sup_right) (y₁_mem _)
  · exact (show chartRing (kept i) ≤ _ from le_sup_right) (y₂_mem _)

theorem cone_pair_localization (i : Fin 3) :
    letI := inclusionAlgebra (show coneRing ≤ coneRing ⊔ chartRing (kept i) from le_sup_left)
    IsLocalization.Away (coneDenominator i) ↥(coneRing ⊔ chartRing (kept i)) := by
  apply subalgebra_isLocalizationAway
  · exact monomial_nonzero _
  · change (monomial (coneDenominatorExponent i))⁻¹ ∈ _
    rw [← monomial_neg, (denominator_certificates i).2.2.1]
    exact combination_mem _ _ _ (pairVector_mem i)
  · apply sup_le le_sup_left
    apply Algebra.adjoin_le
    intro x hx
    have hm (a : Fin 2) : monomial ((![first (kept i), second (kept i)] : Fin 2 → Lattice) a) ∈
        coneRing ⊔ Algebra.adjoin k ({(coneDenominator i : K)⁻¹} : Set K) := by
      rw [keptInCone_certificate]
      apply combination_mem
      intro b
      fin_cases b
      · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 0)
      · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 1)
      · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 2)
      · exact (show coneRing ≤ _ from le_sup_left) (cone_generator_mem 3)
      · change monomial (-coneDenominatorExponent i) ∈ _
        rw [monomial_neg]
        exact (show Algebra.adjoin k _ ≤ _ from le_sup_right)
          (Algebra.subset_adjoin (Set.mem_singleton _))
    rcases hx with rfl | hx
    · exact hm 0
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hm 1

theorem kept_cone_localization (i : Fin 3) :
    letI := inclusionAlgebra (show chartRing (kept i) ≤ chartRing (kept i) ⊔ coneRing from le_sup_left)
    IsLocalization.Away (keptDenominator i) ↥(chartRing (kept i) ⊔ coneRing) := by
  apply subalgebra_isLocalizationAway
  · exact monomial_nonzero _
  · change (monomial (keptDenominatorExponent i))⁻¹ ∈ _
    rw [← monomial_neg, sup_comm, (denominator_certificates i).2.2.2]
    exact combination_mem _ _ _ (pairVector_mem i)
  · apply sup_le le_sup_left
    apply (coneRing_le_iff _).mpr
    intro a
    rw [coneInKept_certificate]
    apply combination_mem
    intro b
    fin_cases b
    · exact (show chartRing (kept i) ≤ _ from le_sup_left) (y₁_mem _)
    · exact (show chartRing (kept i) ≤ _ from le_sup_left) (y₂_mem _)
    · change monomial (-keptDenominatorExponent i) ∈ _
      rw [monomial_neg]
      exact (show Algebra.adjoin k _ ≤ _ from le_sup_right)
        (Algebra.subset_adjoin (Set.mem_singleton _))

/-- Cyclic order: V1, V4, V6, and the singular cone chart. -/
def ring : Fin 4 → Subalgebra k K := ![chartRing 0, chartRing 3, chartRing 5, coneRing]

theorem all_pairs_localization (i j : Fin 4) :
    letI := inclusionAlgebra (show ring i ≤ ring i ⊔ ring j from le_sup_left)
    ∃ d : ring i, IsLocalization.Away d ↥(ring i ⊔ ring j) := by
  fin_cases i <;> fin_cases j
  · exact every_pair_isLocalization 0 0
  · exact every_pair_isLocalization 0 3
  · exact every_pair_isLocalization 0 5
  · exact ⟨keptDenominator 0, kept_cone_localization 0⟩
  · exact every_pair_isLocalization 3 0
  · exact every_pair_isLocalization 3 3
  · exact every_pair_isLocalization 3 5
  · exact ⟨keptDenominator 1, kept_cone_localization 1⟩
  · exact every_pair_isLocalization 5 0
  · exact every_pair_isLocalization 5 3
  · exact every_pair_isLocalization 5 5
  · exact ⟨keptDenominator 2, kept_cone_localization 2⟩
  · exact ⟨coneDenominator 0, cone_pair_localization 0⟩
  · exact ⟨coneDenominator 1, cone_pair_localization 1⟩
  · exact ⟨coneDenominator 2, cone_pair_localization 2⟩
  · change ∃ d : coneRing, _
    refine ⟨1, ?_⟩
    apply subalgebra_isLocalizationAway
    · exact one_ne_zero
    · simp
    · exact sup_le le_sup_left le_sup_left

end
end Red61.Contraction

namespace Red61.Charts

open Fields LocalCoordinates MvPolynomial
noncomputable section
set_option maxRecDepth 4096

def exponentPair (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem exponentPair_zero (a b : ℕ) : exponentPair a b 0 = a := by simp [exponentPair]

@[simp] theorem exponentPair_one (a b : ℕ) : exponentPair a b 1 = b := by simp [exponentPair]

end
end Red61.Charts

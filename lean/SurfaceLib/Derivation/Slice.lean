import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-! # Residue-field comparison for a sliced derivation

This elementary lemma supplies the local proportionality argument in the last example of
`eff`. The power decomposition is explicit input, rather than an assumed geometric theorem.
-/

namespace SurfaceLib

variable {F A B κ : Type*} [CommRing F] [CommRing A] [CommRing B] [CommRing κ]
  [Algebra F B]

/-- If powers of a slice span over the invariant ring, vanishing on that ring forces
proportionality to the sliced derivation after applying any residue homomorphism. -/
theorem residue_derivation_eq_mul_of_slice (f : A →+* B) (res : B →+* κ)
    (D E : Derivation F B B) (g : B) (n : ℕ)
    (hD : ∀ a, D (f a) = 0) (hg : D g = 1)
    (hE : ∀ a, res (E (f a)) = 0)
    (hspan : ∀ x : B, ∃ a : Fin n → A, x = ∑ i, f (a i) * g ^ (i : ℕ))
    (x : B) : res (E x) = res (E g) * res (D x) := by
  obtain ⟨a, rfl⟩ := hspan x
  simp only [map_sum, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, map_add, map_mul, map_natCast, hD, hE, hg, map_zero, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SurfaceLib

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-! # Descending a finite unit-ideal certificate through Frobenius -/

namespace SurfaceLib

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {A B ι : Type*} [CommRing A] [CommRing B] [CharP B 5]
  [Fintype ι]

/-- If fifth powers in the larger ring lift to the subring, a unit-ideal certificate
for elements of the subring descends. The coefficients need not already lie in it. -/
theorem span_top_of_fifth_power_lifts (f : A →+* B) (hf : Function.Injective f)
    (hp : ∀ b : B, ∃ a : A, f a = b ^ 5) (v : ι → A) (a : ι → B)
    (ha : ∑ i, a i * f (v i) = 1) : Ideal.span (Set.range v) = ⊤ := by
  classical
  let c : ι → A := fun i ↦ Classical.choose (hp (a i))
  have hc (i : ι) : f (c i) = a i ^ 5 := Classical.choose_spec (hp (a i))
  have he : ∑ i, c i * v i ^ 5 = 1 := by
    apply hf
    simp only [map_sum, map_mul, map_pow, hc, map_one]
    have h := congrArg (fun b : B ↦ b ^ 5) ha
    simpa only [sum_pow_char, mul_pow, one_pow] using h
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← he]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_left
  exact (Ideal.span (Set.range v)).pow_mem_of_mem
    (Ideal.subset_span (Set.mem_range_self i)) 5 (by decide)

end SurfaceLib

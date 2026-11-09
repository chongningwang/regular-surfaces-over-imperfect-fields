import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime

/-! # The base field `k = F₁₉(c)` and the function field of the characteristic-19 example

The surface of Example `ex:p19` of the geonormal manuscript has generic fibre
`y² = x³ + c²t⁷x + t`. Its function field is the quadratic extension `F = E(y)` of the
rational function field `E = k(x, t)`, which is a field because `g = x³ + c²t⁷x + t` is not
a square in `E`: its degree in `x` is odd.
-/

namespace Geonormal

open Polynomial

noncomputable section

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

abbrev F₁₉ := ZMod 19
abbrev P₁ := MvPolynomial (Fin 1) F₁₉
/-- The base field `k = F₁₉(c)`. -/
abbrev k := FractionRing P₁

/-- The transcendental generator `c` of `k`. -/
def c : k := algebraMap P₁ k (MvPolynomial.X 0)

/-- The plane coordinate ring `k[x, t]`; variable `0` is `x` and variable `1` is `t`. -/
abbrev R₂ := MvPolynomial (Fin 2) k
/-- The rational function field `E = k(x, t)`. -/
abbrev E := FractionRing R₂

/-- The Weierstrass right-hand side `g = x³ + c²t⁷x + t`. -/
def gPoly : R₂ :=
  MvPolynomial.X 0 ^ 3 + MvPolynomial.C (c ^ 2) * MvPolynomial.X 1 ^ 7 * MvPolynomial.X 0 +
    MvPolynomial.X 1

def gE : E := algebraMap R₂ E gPoly

/-- The cubic `g`, viewed as a polynomial in `x` over `k[t]`. -/
theorem finSuccEquiv_gPoly :
    MvPolynomial.finSuccEquiv k 1 gPoly =
      X ^ 3 + C (MvPolynomial.C (c ^ 2) * MvPolynomial.X 0 ^ 7) * X + C (MvPolynomial.X 0) := by
  have h1 : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X 1) = C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have hc : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.C c) = C (MvPolynomial.C c) :=
    (MvPolynomial.finSuccEquiv k 1).commutes c
  simp only [gPoly, map_add, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero, h1, hc]

theorem natDegree_finSuccEquiv_gPoly : (MvPolynomial.finSuccEquiv k 1 gPoly).natDegree = 3 := by
  rw [finSuccEquiv_gPoly]
  compute_degree!

theorem gPoly_ne_zero : gPoly ≠ 0 := by
  intro h
  have := natDegree_finSuccEquiv_gPoly
  rw [h, map_zero, natDegree_zero] at this
  exact absurd this (by norm_num)

/-- `g` is not a square in `E = k(x, t)`, because its degree in `x` is odd. -/
theorem sq_ne_gE (r : E) : r ^ 2 ≠ gE := by
  intro h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R₂) r
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap R₂ E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R₂ E)).mpr hb0
  have hab : a ^ 2 = gPoly * b ^ 2 := by
    apply IsFractionRing.injective R₂ E
    rw [map_pow, map_mul, map_pow, ← gE, ← h, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hbE)]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_mul,
      pow_eq_zero_iff] at hab
    exact hab.elim gPoly_ne_zero hb0
  set φ := MvPolynomial.finSuccEquiv k 1
  have hφa : φ a ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr ha0
  have hφb : φ b ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hb0
  have hφg : φ gPoly ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr gPoly_ne_zero
  have hdeg := congrArg (fun p ↦ (φ p).natDegree) hab
  simp only [map_pow, map_mul] at hdeg
  rw [natDegree_pow, natDegree_mul hφg (pow_ne_zero 2 hφb), natDegree_pow,
    natDegree_finSuccEquiv_gPoly] at hdeg
  omega

/-- The defining quadratic `Y² - g` of the function field over `E`. -/
def quad : E[X] := X ^ 2 - C gE

theorem quad_natDegree : quad.natDegree = 2 := by
  unfold quad
  compute_degree!

theorem quad_monic : quad.Monic := by
  unfold quad
  monicity!

theorem quad_irreducible : Irreducible quad := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_natDegree]
    decide
  · intro r hr
    apply sq_ne_gE r
    simpa [quad, sub_eq_zero] using hr

instance : Fact (Irreducible quad) := ⟨quad_irreducible⟩

/-- The function field `F = E(y)` of the surface. -/
abbrev F := AdjoinRoot quad

def x : F := algebraMap E F (algebraMap R₂ E (MvPolynomial.X 0))
def t : F := algebraMap E F (algebraMap R₂ E (MvPolynomial.X 1))
def y : F := AdjoinRoot.root quad

theorem algebraMap_gE : algebraMap E F gE = x ^ 3 + algebraMap k F c ^ 2 * t ^ 7 * x + t := by
  have hc : algebraMap E F (algebraMap R₂ E (MvPolynomial.C c)) = algebraMap k F c := by
    rw [IsScalarTower.algebraMap_apply k E F, IsScalarTower.algebraMap_apply k R₂ E]
    rfl
  simp only [gE, gPoly, map_add, map_mul, map_pow, x, t, hc]

/-- The Weierstrass equation of the generic fibre. -/
theorem y_sq : y ^ 2 = x ^ 3 + algebraMap k F c ^ 2 * t ^ 7 * x + t := by
  have h := AdjoinRoot.eval₂_root quad
  rw [quad, eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← algebraMap_gE, ← sub_eq_zero]
  exact h

end
end Geonormal

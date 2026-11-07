import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-! # Explicit weight projections in characteristic five

No finite-dimensionality assumption is needed. The five projectors are the expanded
Lagrange polynomials `1 - (D - i)^4`, with coefficients in the prime field.
-/

namespace SurfaceLib.WeightFive

variable {M : Type*} [AddCommGroup M] [Module (ZMod 5) M]

/-- The five Lagrange projectors for a linear operator with `D^5 = D`. -/
def component (D : Module.End (ZMod 5) M) (i : Fin 5) : Module.End (ZMod 5) M :=
  ![(1 : ZMod 5) • 1 + (4 : ZMod 5) • D ^ 4,
    (4 : ZMod 5) • D + (4 : ZMod 5) • D ^ 2 + (4 : ZMod 5) • D ^ 3 +
      (4 : ZMod 5) • D ^ 4,
    (2 : ZMod 5) • D + (1 : ZMod 5) • D ^ 2 + (3 : ZMod 5) • D ^ 3 +
      (4 : ZMod 5) • D ^ 4,
    (3 : ZMod 5) • D + (1 : ZMod 5) • D ^ 2 + (2 : ZMod 5) • D ^ 3 +
      (4 : ZMod 5) • D ^ 4,
    (1 : ZMod 5) • D + (4 : ZMod 5) • D ^ 2 + (1 : ZMod 5) • D ^ 3 +
      (4 : ZMod 5) • D ^ 4] i

theorem sum_component (D : Module.End (ZMod 5) M) (x : M) :
    ∑ i : Fin 5, component D i x = x := by
  simp only [Fin.sum_univ_succ, component, Matrix.cons_val_zero, Matrix.cons_val_succ,
    LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Fin.sum_univ_zero, add_zero]
  match_scalars <;> decide

theorem component_weight (D : Module.End (ZMod 5) M)
    (hD : ∀ x, D (D (D (D (D x)))) = D x) (i : Fin 5) (x : M) :
    D (component D i x) = (i.val : ZMod 5) • component D i x := by
  fin_cases i <;>
    simp [component, pow_succ, Module.End.mul_apply, hD] <;>
    match_scalars <;> decide

/-- The eigenspace decomposition, stated without any choice of a basis. -/
theorem exists_weight_decomposition (D : Module.End (ZMod 5) M)
    (hD : ∀ x, D (D (D (D (D x)))) = D x) (x : M) :
    ∃ v : Fin 5 → M, (∀ i, D (v i) = (i.val : ZMod 5) • v i) ∧ ∑ i, v i = x :=
  ⟨fun i ↦ component D i x, fun i ↦ component_weight D hD i x, sum_component D x⟩

/-- A projector selects exactly the matching weight. -/
theorem component_on_weight (D : Module.End (ZMod 5) M) (i j : Fin 5) (x : M)
    (hx : D x = (j.val : ZMod 5) • x) :
    component D i x = if i = j then x else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [component, pow_succ, Module.End.mul_apply, hx, smul_smul] <;>
    match_scalars <;> decide

/-- Uniqueness of the finite weight decomposition. -/
theorem weight_decomposition_unique (D : Module.End (ZMod 5) M)
    (v : Fin 5 → M) (hv : ∀ i, D (v i) = (i.val : ZMod 5) • v i)
    (x : M) (hsum : ∑ i, v i = x) (i : Fin 5) : v i = component D i x := by
  rw [← hsum, map_sum]
  simp [component_on_weight D i _ _ (hv _)]

section Algebra

variable {R : Type*} [CommRing R] [Algebra (ZMod 5) R]

/-- Multiplication adds weights, as required for the multiplicative group-scheme grading. -/
theorem mul_weight (D : Derivation (ZMod 5) R R) (a b : R) (i j : ZMod 5)
    (ha : D a = i • a) (hb : D b = j • b) : D (a * b) = (i + j) • (a * b) := by
  simp only [Derivation.leibniz, ha, hb, Algebra.smul_def, map_add,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end Algebra
end SurfaceLib.WeightFive

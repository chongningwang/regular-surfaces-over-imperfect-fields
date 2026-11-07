import Mathlib.RingTheory.Derivation.Basic

/-! # Testing stability on algebra generators

The coefficient ring need only be preserved by the derivation, rather than fixed pointwise.
-/

namespace SurfaceLib

variable {F k R : Type*} [CommRing F] [CommRing k] [CommRing R]
  [Algebra F R] [Algebra k R]

/-- Elements of a subalgebra whose derivatives remain in the subalgebra. -/
def stableCore (D : Derivation F R R) (A : Subalgebra k R)
    (hcoeff : ∀ a : k, D (algebraMap k R a) ∈ A) : Subalgebra k R where
  carrier := {x | x ∈ A ∧ D x ∈ A}
  zero_mem' := ⟨A.zero_mem, by simp⟩
  one_mem' := ⟨A.one_mem, by simp⟩
  add_mem' hx hy := ⟨A.add_mem hx.1 hy.1, by simpa using A.add_mem hx.2 hy.2⟩
  mul_mem' hx hy := ⟨A.mul_mem hx.1 hy.1, by
    simpa only [Derivation.leibniz, smul_eq_mul] using
      A.add_mem (A.mul_mem hx.1 hy.2) (A.mul_mem hy.1 hx.2)⟩
  algebraMap_mem' a := ⟨A.algebraMap_mem a, hcoeff a⟩

end SurfaceLib

import SurfaceLib.GroupScheme.MuFive
import Red61.Foliation
import Red61.AlgebraicGeometry.Atlas

/-! # Explicit classical diagonalizable-quotient input

This interface packages the SGA 3 graded-algebra torsor theorem and gluing. It is
general, supplies no global instance, and does not assume freeness of any example.
Its input is an actual unit-ideal cover by eigenfunctions of nonzero weights.
-/

namespace SurfaceLib.MuFive

open Red61 AlgebraicGeometry CategoryTheory
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {F L : Type} [Field F] [Field L] [Algebra F L] [CharP L 5]

/-- An explicit homogeneous cover, independent of the group-scheme torsor predicate. -/
structure HomogeneousCover (E : Derivation F L L) (A : Subalgebra F L) where
  size : ℕ
  value : Fin size → A
  weight : Fin size → ℤ
  eigen : ∀ j, E (value j : L) = (weight j : L) * (value j : L)
  nonzero : ∀ j, (weight j : ZMod 5) ≠ 0
  spans : Ideal.span (Set.range value) = ⊤

/-- The regular function on an affine chart associated to a ring element. -/
def chartSection (P : Red61.AffineGluing.PrincipalAtlas F L)
    (i : P.Index) (x : P.ring i) : Γ(P.chart i, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (P.ring i))).inv x

/-- A torsor for the actual quotient whose action realizes the given Euler weights.
The chart lift and weight formula are required for all test schemes, including
nonreduced ones. Thus later character calculations refer to this same action. -/
structure GradedTorsor (P : Red61.AffineGluing.PrincipalAtlas F L)
    (E : Derivation F L L) (M : Subfield L) [Algebra F M] [IsScalarTower F M L]
    (hp : ∀ x : L, x ^ 5 ∈ M) where
  toTorsor : Torsor (AtlasDescent.quotientMap (R := F) P M 5 hp)
  weights : ∀ (i : P.Index) (T : Scheme) (a : group T) (s : T ⟶ P.chart i),
    ∃ t : T ⟶ P.chart i,
      t ≫ P.chartInclusion i =
        (toTorsor.act T ((s ≫ P.chartInclusion i) ≫
          AtlasDescent.quotientMap (R := F) P M 5 hp) a
          ⟨s ≫ P.chartInclusion i, rfl⟩).val ∧
      ∀ (x : P.ring i) (n : ℤ), E (x : L) = (n : L) * (x : L) →
        t.appTop.hom (chartSection P i x) =
          ↑((a : (Γ(T, ⊤))ˣ) ^ n) * s.appTop.hom (chartSection P i x)

/-- The classical free diagonalizable quotient theorem specialized to mu-five.
The record is an explicit hypothesis; no inhabitant is provided by this library. -/
structure ClassicalDiagonalizableQuotient : Prop where
  torsor : ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [CharP L 5]
    (P : Red61.AffineGluing.PrincipalAtlas F L) (E : Derivation F L L)
    (M : Subfield L) [Algebra F M] [IsScalarTower F M L]
    (_hkernel : ∀ x : L, x ∈ M ↔ E x = 0)
    (hp : ∀ x : L, x ^ 5 ∈ M),
    fifthDerivation E = E →
    (∀ i (x : P.ring i), E (x : L) ∈ P.ring i) →
    (∀ i, Nonempty (HomogeneousCover E (P.ring i))) →
    Nonempty (GradedTorsor P E M hp)

end
end SurfaceLib.MuFive

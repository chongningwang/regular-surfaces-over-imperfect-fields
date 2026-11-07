import Eff.ContractedWeights
import Eff.Quotient

/-! # The Euler derivations on the actual four-chart surface and its overlaps

Every ring is a subalgebra of the existing invariant function field. Thus the two
overlap restrictions agree as actual derivations, not merely on a chosen list of generators.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem euler_preserves_contracted (i : Fin 4) {x : K} (hx : x ∈ contractedAtlas.ring i) :
    euler x ∈ contractedAtlas.ring i := by
  fin_cases i
  · exact euler_preserves_chart 0 hx
  · exact euler_preserves_chart 3 hx
  · exact euler_preserves_chart 5 hx
  · exact euler_preserves_cone hx

theorem invariantEuler_preserves_sChart (i : Fin 4) (x : quotientAtlas.ring i) :
    invariantEuler (x : L) ∈ quotientAtlas.ring i :=
  euler_preserves_contracted i x.property

def sChartEuler (i : Fin 4) :
    Derivation ell (quotientAtlas.ring i) (quotientAtlas.ring i) :=
  invariantRingEuler (quotientAtlas.ring i) (invariantEuler_preserves_sChart i)

@[simp] theorem sChartEuler_coe (i : Fin 4) (x : quotientAtlas.ring i) :
    (sChartEuler i x : L) = invariantEuler (x : L) := rfl

instance sChartCharP (i : Fin 4) : CharP (quotientAtlas.ring i) 5 :=
  (algebraMap (quotientAtlas.ring i) L).charP Subtype.val_injective 5

theorem sChartEuler_fifth (i : Fin 4) : fifthDerivation (sChartEuler i) = sChartEuler i := by
  apply Derivation.ext
  intro x
  apply Subtype.ext
  exact Derivation.congr_fun invariantEuler_fifth (x : L)

theorem invariantEuler_preserves_overlap (i j : Fin 4)
    (x : ↥(quotientAtlas.ring i ⊔ quotientAtlas.ring j)) :
    invariantEuler (x : L) ∈ quotientAtlas.ring i ⊔ quotientAtlas.ring j := by
  let C : Subalgebra ell L := quotientAtlas.ring i ⊔ quotientAtlas.ring j
  have hc (a : ell) : invariantEuler (algebraMap ell L a) ∈ C := by simp [C]
  let core := SurfaceLib.stableCore invariantEuler C hc
  have hle : C ≤ core := by
    apply sup_le
    · intro y hy
      exact ⟨(show quotientAtlas.ring i ≤ C from le_sup_left) hy,
        (show quotientAtlas.ring i ≤ C from le_sup_left)
          (invariantEuler_preserves_sChart i ⟨y, hy⟩)⟩
    · intro y hy
      exact ⟨(show quotientAtlas.ring j ≤ C from le_sup_right) hy,
        (show quotientAtlas.ring j ≤ C from le_sup_right)
          (invariantEuler_preserves_sChart j ⟨y, hy⟩)⟩
  exact (hle x.property).2

def sOverlapEuler (i j : Fin 4) :
    Derivation ell ↥(quotientAtlas.ring i ⊔ quotientAtlas.ring j)
      ↥(quotientAtlas.ring i ⊔ quotientAtlas.ring j) :=
  invariantRingEuler _ (invariantEuler_preserves_overlap i j)

theorem sChartEuler_overlap_left (i j : Fin 4) (x : quotientAtlas.ring i) :
    sOverlapEuler i j (Subalgebra.inclusion
      (show quotientAtlas.ring i ≤ quotientAtlas.ring i ⊔ quotientAtlas.ring j
        from le_sup_left) x) =
      Subalgebra.inclusion
      (show quotientAtlas.ring i ≤ quotientAtlas.ring i ⊔ quotientAtlas.ring j
        from le_sup_left) (sChartEuler i x) := rfl

theorem sChartEuler_overlap_right (i j : Fin 4) (x : quotientAtlas.ring j) :
    sOverlapEuler i j (Subalgebra.inclusion
      (show quotientAtlas.ring j ≤ quotientAtlas.ring i ⊔ quotientAtlas.ring j
        from le_sup_right) x) =
      Subalgebra.inclusion
      (show quotientAtlas.ring j ≤ quotientAtlas.ring i ⊔ quotientAtlas.ring j
        from le_sup_right) (sChartEuler j x) := rfl

end
end Eff

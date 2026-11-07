import Eff.ChartWeights
import Red61.Surface.ContractionCharts
import SurfaceLib.Derivation.StableSubalgebra

/-! # Euler derivations on the contracted affine rings

In addition to the six resolved charts, preservation is checked on the singular cone chart
of `X`. The restrictions to the original foliation-invariant rings are actual derivations.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction
noncomputable section

theorem euler_preserves_cone {x : K} (hx : x ∈ coneRing) : euler x ∈ coneRing := by
  have hc (a : k) : euler (algebraMap k K a) ∈ coneRing := by
    rw [show algebraMap k K a = includeK a from rfl, euler_on_k]
    exact coneRing.algebraMap_mem _
  let core := SurfaceLib.stableCore euler coneRing hc
  have hle : coneRing ≤ core := by
    apply (coneRing_le_iff core).mpr
    intro i
    refine ⟨cone_generator_mem i, ?_⟩
    rw [euler_monomial]
    apply coneRing.mul_mem _ (cone_generator_mem i)
    have h := coneRing.algebraMap_mem
      (2 * ((coneExponent i).1 : k) + 3 * ((coneExponent i).2 : k))
    simpa [map_ofNat] using h
  exact (hle hx).2

/-- The special invariant used at the cone point has weight minus one. -/
theorem euler_special_coordinate : euler LocalCoordinates.q₁ = -LocalCoordinates.q₁ := by
  have hU : euler LocalCoordinates.U = -3 * LocalCoordinates.U := by
    simpa [LocalCoordinates.U] using euler_zpow w (coord_nonzero 3) 3 euler_w (-1)
  simp only [LocalCoordinates.q₁, map_sub, Derivation.leibniz, euler_c₁,
    LocalCoordinates.T, euler_t, hU, smul_eq_mul]
  ring

/-- Restriction of the invariant-field Euler derivation to a preserved subalgebra. -/
def invariantRingEuler (C : Subalgebra ell L)
    (hC : ∀ x : C, invariantEuler (x : L) ∈ C) : Derivation ell C C where
  toFun x := ⟨invariantEuler (x : L), hC x⟩
  map_add' x y := Subtype.ext (map_add invariantEuler (x : L) (y : L))
  map_smul' a x := Subtype.ext (invariantEuler.map_smul a (x : L))
  map_one_eq_zero' := Subtype.ext invariantEuler.map_one_eq_zero
  leibniz' x y := Subtype.ext (invariantEuler.leibniz (x : L) (y : L))

/-- The Euler derivation on each of the six original invariant chart rings. -/
def invariantChartEuler (i : Fin 6) :
    Derivation ell (invariantChartRing i) (invariantChartRing i) :=
  invariantRingEuler (invariantChartRing i) (fun x ↦
    euler_preserves_chart i x.property)

end
end Eff

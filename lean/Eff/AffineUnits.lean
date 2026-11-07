import Eff.InvariantCoordinates
import Red61.Surface.Charts

/-! # Units on the invariant affine charts

Every unit is a scalar in the actual base field. This will allow a local adjunction generator
to be compared with a global canonical generator without an intersection-theoretic argument.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Units on any of the six invariant charts are nonzero base-field scalars. -/
theorem invariant_chart_unit_constant (i : Fin 6) (u : invariantChartRing i) (hu : IsUnit u) :
    ∃ a : ell, a ≠ 0 ∧ algebraMap ell (invariantChartRing i) a = u := by
  let v : chartRing i := invariantChartEmbedding i u
  let p : MvPolynomial (Fin 2) k := (chartPolynomialEquiv i).symm v
  have hp : IsUnit p := (hu.map (invariantChartEmbedding i).toRingHom).map
    (chartPolynomialEquiv i).symm.toRingHom
  obtain ⟨c, hc, hpc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hp
  have hv : v = algebraMap k (chartRing i) c := by
    calc
      v = chartPolynomialEquiv i p := ((chartPolynomialEquiv i).apply_symm_apply v).symm
      _ = chartPolynomialEquiv i (MvPolynomial.C c) := congrArg (chartPolynomialEquiv i) hpc
      _ = algebraMap k (chartRing i) c := (chartPolynomialEquiv i).commutes c
  have hK : ((u : L) : K) = includeK c :=
    congrArg (fun z : chartRing i ↦ (z : K)) hv
  have hcℓ : c ∈ ell := (invariant_constant_iff c).mp (hK ▸ (u : L).property)
  refine ⟨⟨c, hcℓ⟩, ?_, ?_⟩
  · intro h
    exact hc.ne_zero (congrArg (fun a : ell ↦ (a : k)) h)
  · apply Subtype.ext
    apply Subtype.ext
    exact hK.symm

end
end Eff

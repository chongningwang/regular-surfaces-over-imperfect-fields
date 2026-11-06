import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Red61.Surface.Cone

/-! # The six-chart model

Formerly the modules `Constants`, `AffineGeometry`, `BoundaryValuations`, `GluedSurface`.
-/

/-! Algebraic constants in the concrete function fields, with the specified embeddings. -/

namespace Red61.Fields

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The coefficient field is relatively algebraically closed in K = k(t,w). -/
theorem coefficientField_relative_algebraic_closed {x : K} (hx : IsAlgebraic k x) :
    ∃ c : k, includeK c = x := by
  have h := hx.algHom (Charts.chartFractionEquiv 0).symm.toAlgHom
  obtain ⟨c, hc⟩ := algebraic_fraction_mvPolynomial_constant k (Fin 2) h
  refine ⟨c, ?_⟩
  calc
    includeK c = Charts.chartFractionEquiv 0 (algebraMap k _ c) :=
      (Charts.chartFractionEquiv 0).commutes c |>.symm
    _ = Charts.chartFractionEquiv 0 ((Charts.chartFractionEquiv 0).symm x) :=
      congrArg (Charts.chartFractionEquiv 0) hc
    _ = x := (Charts.chartFractionEquiv 0).apply_symm_apply x

/-- Every element of L algebraic over ell lies in the explicitly embedded copy of ell. -/
theorem invariant_algebraic_constant (x : L) (hx : IsAlgebraic ell x) :
    ∃ c : ell, algebraMap ell L c = x := by
  have : IsScalarTower ell k K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hK : IsAlgebraic ell (x : K) := hx.algebraMap
  obtain ⟨c, hc⟩ := coefficientField_relative_algebraic_closed (hK.tower_top k)
  have hcell : c ∈ ell := (invariant_constant_iff c).mp (hc.symm ▸ x.property)
  refine ⟨⟨c, hcell⟩, ?_⟩
  apply Subtype.ext
  exact hc

instance invariant_constants_integrallyClosed : IsIntegrallyClosedIn ell L := by
  apply isIntegrallyClosedIn_iff.mpr
  exact ⟨(algebraMap ell L).injective, fun hx ↦ invariant_algebraic_constant _ hx.isAlgebraic⟩

end
end Red61.Fields

/-! The six verified coordinate rings, interpreted as actual affine schemes. -/

namespace Red61.Charts

open Fields CategoryTheory AlgebraicGeometry
noncomputable section

abbrev chartSpec (i : Fin 6) : Scheme := Spec (CommRingCat.of (chartRing i))

def pairSpec (i j : Fin 6) : Scheme := Spec (CommRingCat.of (pairRing i j))

def pairToChart (i j : Fin 6) : pairSpec i j ⟶ chartSpec i :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion
    (show chartRing i ≤ pairRing i j from le_sup_left)).toRingHom)

instance pairToChart_isOpenImmersion (i j : Fin 6) : IsOpenImmersion (pairToChart i j) := by
  let := pairAlgebra i j
  obtain ⟨d, hd⟩ := every_pair_isLocalization i j
  let := hd
  exact IsOpenImmersion.of_isLocalization d

def chartStalkEquiv (i : Fin 6) (x : PrimeSpectrum (chartRing i)) :
    (chartSpec i).presheaf.stalk x ≃+* Localization.AtPrime x.asIdeal :=
  (Spec.stalkIso (CommRingCat.of (chartRing i)) x).commRingCatIsoToRingEquiv

instance chartRing_regular (i : Fin 6) : IsRegularRing (chartRing i) :=
  IsRegularRing.of_ringEquiv (chartPolynomialEquiv i).toRingEquiv

def chartFunctionFieldEquiv (i : Fin 6) : (chartSpec i).functionField ≃+* K :=
  affineFunctionFieldEquiv (CommRingCat.of (chartRing i)) K

end
end Red61.Charts

namespace Red61.Charts

open Fields MvPolynomial LocalCoordinates
noncomputable section
set_option maxRecDepth 4096

abbrev ValuationPolynomial := MvPolynomial (Fin 2) k

/-- Boundary order at one polynomial coordinate of an affine toric chart. -/
def boundaryOrder (i : Fin 6) (a : Fin 2) : AddValuation K (WithTop ℤ) :=
  (fractionPrimeOrder (X_prime (R := k) (i := a))).comap (chartFractionEquiv i).symm.toRingHom

theorem boundaryOrder_polynomial (i : Fin 6) (a : Fin 2) (p : ValuationPolynomial) :
    boundaryOrder i a (aeval (chartCoordinates i) p) = primeOrder (X_prime (i := a)) p := by
  rw [← chartFractionEquiv_polynomial]
  change fractionPrimeOrder _ ((chartFractionEquiv i).symm (chartFractionEquiv i _)) = _
  rw [AlgEquiv.symm_apply_apply, fractionPrimeOrder_algebraMap]

@[simp] theorem boundaryOrder_coordinate (i : Fin 6) (a b : Fin 2) :
    boundaryOrder i a (chartCoordinates i b) = if a = b then 1 else 0 := by
  rw [← aeval_X (R := k) (chartCoordinates i) b, boundaryOrder_polynomial]
  split_ifs with h
  · subst b
    exact primeOrder_self _
  · exact primeOrder_of_not_dvd _ (by simpa only [X_dvd_X] using h)

theorem parameters_in_boundary_charts :
    u = y₂ 1 ∧ r = y₁ 1 ^ 5 * y₂ 1 ^ 2 ∧
    u = y₁ 2 ^ 3 * y₂ 2 ∧ r = y₁ 2 * y₂ 2 ^ 2 := by
  have ht : t ≠ 0 := coord_nonzero 2
  have hw : w ≠ 0 := coord_nonzero 3
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [u, r, U, T, y₁, y₂, monomial, first, second] <;>
    field_simp

end
end Red61.Charts

/-! The actual regular integral scheme obtained by gluing the six affine charts.

The invariant quotient is constructed in GluedQuotient. ContractedModels constructs the
maps to the four-chart models; projectivity remains a separate step.
-/

namespace Red61.Charts

open Fields CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section

def sixChartAtlas : AffineGluing.PrincipalAtlas k K where
  Index := Fin 6
  ring := chartRing
  localization := every_pair_isLocalization

instance : Nonempty sixChartAtlas.Index := ⟨(0 : Fin 6)⟩

abbrev resolvedScheme : Scheme := sixChartAtlas.glued

abbrev chartInclusion (i : Fin 6) : chartSpec i ⟶ resolvedScheme :=
  sixChartAtlas.chartInclusion i

def resolvedToBase : resolvedScheme ⟶ Spec (CommRingCat.of k) := sixChartAtlas.toBase

theorem resolved_chart_cover (x : resolvedScheme) : ∃ i y, chartInclusion i y = x :=
  sixChartAtlas.chartInclusion_cover x

instance resolved_integral : IsIntegral resolvedScheme :=
  sixChartAtlas.glued_integral

instance resolved_noetherian : IsNoetherian resolvedScheme := by
  have : Finite sixChartAtlas.glueData.openCover.I₀ :=
    inferInstanceAs (Finite (Fin 6))
  have : ∀ i : sixChartAtlas.glueData.openCover.I₀,
      IsAffine (sixChartAtlas.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (chartRing i))))
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := sixChartAtlas.glueData.openCover)).mpr
  intro i
  have : IsNoetherianRing (chartRing i) :=
    isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 2) k)
      (chartPolynomialEquiv i).toRingEquiv
  change IsNoetherianRing Γ(Spec (CommRingCat.of (chartRing i)), ⊤)
  exact isNoetherianRing_of_ringEquiv (chartRing i)
    (Scheme.ΓSpecIso (CommRingCat.of (chartRing i))).symm.commRingCatIsoToRingEquiv

def resolvedFunctionFieldEquiv : resolvedScheme.functionField ≃+* K :=
  (sixChartAtlas.functionFieldChartEquiv (0 : Fin 6)).trans (chartFunctionFieldEquiv 0)

end
end Red61.Charts

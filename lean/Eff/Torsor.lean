import Eff.FreenessCertificates
import SurfaceLib.GroupScheme.DiagonalizableQuotient

/-! # The second quotient as a mu-five torsor

The homogeneous covers and nowhere-vanishing calculations are proved in this project.
Only the general graded-algebra group-scheme construction and gluing are passed as an
explicit classical input. No inhabitant of that input is declared here.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction AlgebraicGeometry CategoryTheory
  SurfaceLib.MuFive
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sChartHomogeneousCover (i : Fin 4) :
    HomogeneousCover invariantEuler (quotientAtlas.ring i) where
  size := 3
  value := certificate i
  weight := certificateWeight i
  eigen j := by
    have h := congrArg (fun a : quotientAtlas.ring i ↦ (a : L)) (certificate_weight i j)
    change invariantEuler (certificate i j : L) =
      algebraMap (quotientAtlas.ring i) L (certificateWeight i j : quotientAtlas.ring i) *
        (certificate i j : L) at h
    simpa only [map_intCast] using h
  nonzero := certificateWeight_nonzero i
  spans := certificate_span_top i

/-- The quotient is a mu-five torsor, conditional only on the stated general classical
diagonalizable quotient theorem. Its example-specific cover is proved above. -/
theorem rho_has_gradedTorsor (descent : ClassicalDiagonalizableQuotient) :
    Nonempty (GradedTorsor quotientAtlas invariantEuler M fifth_power_in_M) :=
  descent.torsor ell L quotientAtlas invariantEuler M (fun _ ↦ Iff.rfl)
    fifth_power_in_M invariantEuler_fifth invariantEuler_preserves_sChart
    (fun i ↦ ⟨sChartHomogeneousCover i⟩)

def rhoGradedTorsor (descent : ClassicalDiagonalizableQuotient) :
    GradedTorsor quotientAtlas invariantEuler M fifth_power_in_M :=
  Classical.choice (rho_has_gradedTorsor descent)

theorem rho_is_muFiveTorsor (descent : ClassicalDiagonalizableQuotient) :
    Nonempty (Torsor rho) := ⟨(rhoGradedTorsor descent).toTorsor⟩

def rhoTorsor (descent : ClassicalDiagonalizableQuotient) : Torsor rho :=
  (rhoGradedTorsor descent).toTorsor

/-- The chosen torsor action has the Euler weights on all homogeneous chart functions. -/
theorem rho_action_weights (descent : ClassicalDiagonalizableQuotient)
    (i : Fin 4) (T : Scheme) (a : group T) (s : T ⟶ quotientAtlas.chart i) :
    ∃ t : T ⟶ quotientAtlas.chart i,
      t ≫ quotientAtlas.chartInclusion i =
        ((rhoTorsor descent).act T ((s ≫ quotientAtlas.chartInclusion i) ≫ rho) a
          ⟨s ≫ quotientAtlas.chartInclusion i, rfl⟩).val ∧
      ∀ (x : quotientAtlas.ring i) (n : ℤ),
        invariantEuler (x : L) = (n : L) * (x : L) →
        t.appTop.hom (chartSection quotientAtlas i x) =
          ↑((a : (Γ(T, ⊤))ˣ) ^ n) * s.appTop.hom (chartSection quotientAtlas i x) :=
  (rhoGradedTorsor descent).weights i T a s

theorem rho_flat (descent : ClassicalDiagonalizableQuotient) : Flat rho :=
  (rhoTorsor descent).flat

theorem rho_rankFive (descent : ClassicalDiagonalizableQuotient) (y : Y) :
    letI := (Red61.globalScalarMap (Y.residueField y)
      (rho.fiberToSpecResidueField y)).toAlgebra
    Module.finrank (Y.residueField y) Γ(rho.fiber y, ⊤) = 5 :=
  (rhoTorsor descent).rankFive y

end
end Eff

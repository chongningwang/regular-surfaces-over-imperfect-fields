import Geonormal.P11.Volume
import Geonormal.P11.Nonnormal
import SurfaceLib.Canonical.GeneralAdjunction

/-! # Proposition `prop:p11` of the geonormal manuscript, at `p = 11`

`Geonormal.P11.p11_example` collects what is proved without any classical input: `X` is a regular
projective integral surface over `k = 𝔽₁₁(c)` with `H⁰(X, O_X) = k`, it is not geometrically
normal, its absolute differentials are locally free of rank three, and its normalized
differential line `xOmega` is trivial. `Geonormal.P11.p11_canonical` adds the canonical sheaf,
using the explicit general classical parameter `GeneralClassicalAdjunction`.
-/

namespace Geonormal.P11

open Red61 AlgebraicGeometry CategoryTheory Module SurfaceLib.Canonical SurfaceLib.Projective

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-! ## The base field -/

/-- `Ω_{k/ℤ}` is free on `dc`. -/
def baseDifferentialBasis : Basis (Fin 1) k (KaehlerDifferential ℤ k) :=
  (polynomialLocalizationDifferentialBasis F₁₁ k (Fin 1) (nonZeroDivisors P₁)).map
    (quotientBaseDifferentialEquiv ℤ F₁₁ k ZMod.intCast_surjective).symm

theorem baseDifferentialBasis_apply :
    baseDifferentialBasis 0 = KaehlerDifferential.D ℤ k c := by
  rw [baseDifferentialBasis, Basis.map_apply, polynomialLocalizationDifferentialBasis_apply,
    quotientBaseDifferentialEquiv_symm_D]
  rfl

instance k_essFiniteType : Algebra.EssFiniteType F₁₁ k := by
  have : Algebra.EssFiniteType P₁ k := .of_isLocalization k (nonZeroDivisors P₁)
  exact .comp F₁₁ P₁ k

instance x_isProper : IsProper xToBase := x_proper

instance x_isNoetherian : IsNoetherian X11 := by
  have : Finite atlas.glueData.openCover.I₀ := inferInstanceAs (Finite (Fin 4))
  have : ∀ i : atlas.glueData.openCover.I₀, IsAffine (atlas.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (chartRing i))))
  apply (isNoetherian_iff_of_finite_affine_openCover (𝒰 := atlas.glueData.openCover)).mpr
  intro i
  have := chartRing_finiteType i
  have : IsNoetherianRing (chartRing i) := Algebra.FiniteType.isNoetherianRing k (chartRing i)
  change IsNoetherianRing Γ(Spec (CommRingCat.of (chartRing i)), ⊤)
  exact isNoetherianRing_of_ringEquiv (chartRing i)
    (Scheme.ΓSpecIso (CommRingCat.of (chartRing i))).symm.commRingCatIsoToRingEquiv

/-! ## The canonical line -/

/-- The normalized differential line `Hom(O_X ⊗_k Ω_{k/ℤ}, ⋀³ Ω_{X/ℤ})` of `X`. -/
abbrev xOmega : X11.Modules := omegaR k xToBase 1 baseDifferentialBasis

/-- The volume `da ∧ db ∧ dσ` trivializes the differential line of `X`. -/
def xOmegaIsoStructureSheaf : xOmega ≅ structureSheafModule X11 :=
  omegaREvaluationIso k xToBase 1 baseDifferentialBasis ≪≫ xVolumeIso.symm

/-- The only use of the external classical input: normalized duality for the differential line. -/
def xDifferentialLineDuality (adjunction : GeneralClassicalAdjunction) :
    TopDuality k xToBase 2 xOmega :=
  Classical.choice (adjunction.normalizedDuality 11 1 k xToBase baseDifferentialBasis
    x_dimension x_stalk_regular x_differentials_locallyFree)

/-- Every canonical sheaf of `X` is trivial. -/
theorem canonicalSheaf_trivial (adjunction : GeneralClassicalAdjunction) (K : X11.Modules)
    (DK : TopDuality k xToBase 2 K) : Nonempty (K ≅ structureSheafModule X11) :=
  ⟨comparisonIso DK (xDifferentialLineDuality adjunction) ≪≫ xOmegaIsoStructureSheaf⟩

/-! ## The example -/

/-- Proposition `prop:p11`: `X` is a regular projective integral surface over `k = 𝔽₁₁(c)` with
`H⁰(X, O_X) = k`, and it is not geometrically normal. Its absolute differentials are locally free
of rank three, and its normalized differential line is trivial. -/
theorem p11_example :
    IsProjectiveOver k xToBase ∧ IsProper xToBase ∧ IsIntegral X11 ∧
      topologicalKrullDim X11 = 2 ∧
      (∀ x : X11, IsRegularLocalRing (X11.presheaf.stalk x)) ∧
      Function.Bijective (globalScalarMap k xToBase) ∧
      ¬ geometrically SurfaceLib.IsNormalScheme xToBase ∧
      IsLocallyFreeOfRank 3 (nativeAbsoluteDifferentialModule X11) ∧
      Nonempty (xOmega ≅ structureSheafModule X11) :=
  ⟨x_projective, x_proper, x_integral, x_dimension, x_stalk_regular, x_globalScalarMap_bijective,
    x_not_geometrically_normal, x_differentials_locallyFree, ⟨xOmegaIsoStructureSheaf⟩⟩

/-- Proposition `prop:p11` at `p = 11`: `X` has a canonical sheaf, and every canonical sheaf of `X`
is trivial. -/
theorem p11_canonical (adjunction : GeneralClassicalAdjunction) :
    (∃ K : X11.Modules, Nonempty (TopDuality k xToBase 2 K)) ∧
      ∀ (K : X11.Modules), TopDuality k xToBase 2 K → Nonempty (K ≅ structureSheafModule X11) :=
  ⟨⟨xOmega, ⟨xDifferentialLineDuality adjunction⟩⟩,
    fun K DK ↦ canonicalSheaf_trivial adjunction K DK⟩

end
end Geonormal.P11

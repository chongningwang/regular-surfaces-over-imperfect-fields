import Geonormal.Volume
import SurfaceLib.Canonical.GeneralAdjunction

/-! # Example `ex:p19` of the geonormal manuscript, at `p = 19`

`Geonormal.p19_example` collects what is proved without any classical input: `X` is a regular
projective integral surface over `k = 𝔽₁₉(c)` with `H⁰(X, O_X) = k`, it is not smooth over `k`,
its absolute differentials are locally free of rank three, and its normalized differential line
`xOmega` is trivial. `Geonormal.p19_canonical` adds the canonical sheaf, using the explicit
general classical parameter `GeneralClassicalAdjunction`.
-/

namespace Geonormal

open Red61 AlgebraicGeometry CategoryTheory Module SurfaceLib.Canonical SurfaceLib.Projective

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-! ## The base field -/

/-- `Ω_{k/ℤ}` is free on `dc`. -/
def baseDifferentialBasis : Basis (Fin 1) k (KaehlerDifferential ℤ k) :=
  (polynomialLocalizationDifferentialBasis F₁₉ k (Fin 1) (nonZeroDivisors P₁)).map
    (quotientBaseDifferentialEquiv ℤ F₁₉ k ZMod.intCast_surjective).symm

theorem baseDifferentialBasis_apply :
    baseDifferentialBasis 0 = KaehlerDifferential.D ℤ k c := by
  rw [baseDifferentialBasis, Basis.map_apply, polynomialLocalizationDifferentialBasis_apply,
    quotientBaseDifferentialEquiv_symm_D]
  rfl

instance k_essFiniteType : Algebra.EssFiniteType F₁₉ k := by
  have : Algebra.EssFiniteType P₁ k := .of_isLocalization k (nonZeroDivisors P₁)
  exact .comp F₁₉ P₁ k

instance k_charP : CharP k 19 :=
  charP_of_injective_algebraMap (algebraMap F₁₉ k).injective 19

instance x_isProper : IsProper xToBase := x_proper

instance x_isNoetherian : IsNoetherian X19 := by
  have : Finite atlas.glueData.openCover.I₀ := inferInstanceAs (Finite (Fin 5))
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
abbrev xOmega : X19.Modules := omegaR k xToBase 1 baseDifferentialBasis

/-- The volume `dc ∧ dt ∧ dx / (2y)` trivializes the differential line of `X`. -/
def xOmegaIsoStructureSheaf : xOmega ≅ structureSheafModule X19 :=
  omegaREvaluationIso k xToBase 1 baseDifferentialBasis ≪≫ xVolumeIso.symm

/-- The only use of the external classical input: normalized duality for the differential line. -/
def xDifferentialLineDuality (adjunction : GeneralClassicalAdjunction) :
    TopDuality k xToBase 2 xOmega :=
  Classical.choice (adjunction.normalizedDuality 19 1 k xToBase baseDifferentialBasis
    x_dimension x_stalk_regular x_differentials_locallyFree)

/-- Every canonical sheaf of `X` is trivial. -/
theorem canonicalSheaf_trivial (adjunction : GeneralClassicalAdjunction) (K : X19.Modules)
    (DK : TopDuality k xToBase 2 K) : Nonempty (K ≅ structureSheafModule X19) :=
  ⟨comparisonIso DK (xDifferentialLineDuality adjunction) ≪≫ xOmegaIsoStructureSheaf⟩

/-! ## The example -/

/-- `X` is a regular projective integral surface over `k = 𝔽₁₉(c)` with `H⁰(X, O_X) = k`.
It is not smooth over `k`. Its absolute differentials are locally free of rank three, and its
normalized differential line is trivial. -/
theorem p19_example :
    IsProjectiveOver k xToBase ∧ IsProper xToBase ∧ IsIntegral X19 ∧
      topologicalKrullDim X19 = 2 ∧
      (∀ x : X19, IsRegularLocalRing (X19.presheaf.stalk x)) ∧
      Function.Bijective (globalScalarMap k xToBase) ∧
      ¬ Smooth xToBase ∧
      IsLocallyFreeOfRank 3 (nativeAbsoluteDifferentialModule X19) ∧
      Nonempty (xOmega ≅ structureSheafModule X19) :=
  ⟨x_projective, x_proper, x_integral, x_dimension, x_stalk_regular, x_globalScalarMap_bijective,
    x_not_smooth, x_differentials_locallyFree, ⟨xOmegaIsoStructureSheaf⟩⟩

/-- Example `ex:p19` at `p = 19`: `X` has a canonical sheaf, and every canonical sheaf of `X` is
trivial. -/
theorem p19_canonical (adjunction : GeneralClassicalAdjunction) :
    (∃ K : X19.Modules, Nonempty (TopDuality k xToBase 2 K)) ∧
      ∀ (K : X19.Modules), TopDuality k xToBase 2 K → Nonempty (K ≅ structureSheafModule X19) :=
  ⟨⟨xOmega, ⟨xDifferentialLineDuality adjunction⟩⟩,
    fun K DK ↦ canonicalSheaf_trivial adjunction K DK⟩

end
end Geonormal

import Eff.Euler
import Red61.Surface.Properties

/-! # The actual second invariant quotient

The existing principal-atlas descent machinery constructs a scheme and a finite surjective
map from `S`. No geometric assumptions are used here. Flatness, regularity and the torsor
property are additional obligations; they do not follow merely from this construction.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.AffineGluing
  CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The function field fixed by the second derivation. -/
def M : Subfield L := constants invariantEuler

def ellToM : ell →+* M where
  toFun a := ⟨algebraMap ell L a, invariantEuler.map_algebraMap a⟩
  map_one' := Subtype.ext (map_one (algebraMap ell L))
  map_zero' := Subtype.ext (map_zero (algebraMap ell L))
  map_add' a b := Subtype.ext (map_add (algebraMap ell L) a b)
  map_mul' a b := Subtype.ext (map_mul (algebraMap ell L) a b)

instance : Algebra ell M := ellToM.toAlgebra

instance : IsScalarTower ell M L :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

theorem fifth_power_in_M (x : L) : x ^ 5 ∈ M := by
  change invariantEuler (x ^ 5) = 0
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    CharP.cast_eq_zero L 5, zero_mul]

/-- The four affine invariant rings, with proved principal-localization overlaps. -/
def yAtlas : PrincipalAtlas ell M :=
  AtlasDescent.atlas (R := ell) quotientAtlas M 5 fifth_power_in_M

instance : Nonempty yAtlas.Index := ⟨(0 : Fin 4)⟩

abbrev Y : Scheme := yAtlas.glued

def yToBase : Y ⟶ Spec (CommRingCat.of ell) := yAtlas.toBase

/-- The actual scheme morphism, obtained by gluing the inclusions of invariant rings. -/
def rho : S ⟶ Y :=
  AtlasDescent.quotientMap (R := ell) quotientAtlas M 5 fifth_power_in_M

theorem rho_over_ell : rho ≫ yToBase = sToBase := by
  have h := AtlasDescent.quotientMap_over_base (R := ell)
    quotientAtlas M 5 fifth_power_in_M
  simpa [rho, yToBase, sToBase, yAtlas] using h

instance y_integral : IsIntegral Y := yAtlas.glued_integral

theorem rho_homeomorph : IsHomeomorph rho :=
  AtlasDescent.quotientMap_homeomorph (R := ell) quotientAtlas M 5 fifth_power_in_M

theorem y_dimension : topologicalKrullDim Y = 2 := by
  rw [← IsHomeomorph.topologicalKrullDim_eq rho rho_homeomorph]
  exact s_dimension

instance rho_surjective : Surjective rho := ⟨rho_homeomorph.surjective⟩

instance rho_finite : IsFinite rho := by
  apply AtlasDescent.quotientMap_finite (R := ell) quotientAtlas M 5 fifth_power_in_M
  intro i
  change Algebra.FiniteType ell (quotientAtlas.ring i)
  exact quotient_chart_finiteType i

theorem y_chart_finiteType (i : Fin 4) : Algebra.FiniteType ell (yAtlas.ring i) := by
  have : Algebra.FiniteType ell ((quotientAtlas.ring i).restrictScalars ell) := by
    change Algebra.FiniteType ell (quotientAtlas.ring i)
    exact quotient_chart_finiteType i
  exact FrobeniusDescent.fixed_finiteType M 5 fifth_power_in_M
    ((quotientAtlas.ring i).restrictScalars ell)

instance y_separated : IsSeparated yToBase := yAtlas.toBase_separated

instance y_finiteType : LocallyOfFiniteType yToBase :=
  yAtlas.toBase_locallyOfFiniteType y_chart_finiteType

instance y_quasiCompact : QuasiCompact yToBase := by
  have : Finite yAtlas.Index := inferInstanceAs (Finite (Fin 4))
  exact yAtlas.toBase_quasiCompact

instance y_noetherian : IsNoetherian Y := by
  have : Finite yAtlas.glueData.openCover.I₀ := inferInstanceAs (Finite (Fin 4))
  have : ∀ i : yAtlas.glueData.openCover.I₀, IsAffine (yAtlas.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (yAtlas.ring i))))
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := yAtlas.glueData.openCover)).mpr
  intro i
  have := y_chart_finiteType i
  have : IsNoetherianRing (yAtlas.ring i) := Algebra.FiniteType.isNoetherianRing ell _
  change IsNoetherianRing Γ(Spec (CommRingCat.of (yAtlas.ring i)), ⊤)
  exact isNoetherianRing_of_ringEquiv (yAtlas.ring i)
    (Scheme.ΓSpecIso (CommRingCat.of (yAtlas.ring i))).symm.commRingCatIsoToRingEquiv

/-- Properness descends along the proved finite surjection from the existing surface. -/
instance y_proper : IsProper yToBase := by
  have : UniversallyClosed (rho ≫ yToBase) := by rw [rho_over_ell]; infer_instance
  have : UniversallyClosed yToBase := UniversallyClosed.of_comp_surjective rho yToBase
  exact ⟨⟩

theorem M_algebraic_constant (x : M) (hx : IsAlgebraic ell x) :
    ∃ a : ell, algebraMap ell M a = x := by
  have hL : IsAlgebraic ell (x : L) := hx.algebraMap
  obtain ⟨a, ha⟩ := invariant_algebraic_constant (x : L) hL
  exact ⟨a, Subtype.ext ha⟩

instance y_chart_zero_fractionRing : IsFractionRing (yAtlas.ring (0 : Fin 4)) M := by
  have hfrac : IsFractionRing ((quotientAtlas.ring (0 : Fin 4)).restrictScalars ell) L := by
    change IsFractionRing (quotientAtlas.ring (0 : Fin 4)) L
    exact invariantChart_isFractionRing 0
  exact FrobeniusDescent.fixed_isFractionRing M 5 fifth_power_in_M
    ((quotientAtlas.ring (0 : Fin 4)).restrictScalars ell)

/-- The global constants are exactly the specified field, not a finite extension of it. -/
theorem y_globalScalarMap_bijective : Function.Bijective (globalScalarMap ell yToBase) := by
  let := (globalScalarMap ell yToBase).toAlgebra
  exact (globalSectionsEquivOfFunctionField ell M yToBase M_algebraic_constant
    (yAtlas.functionFieldAlgEquiv (0 : Fin 4))).bijective

/-- The established geometric construction, without any classical geometric inputs.
Regularity, projectivity, canonical order and geometric nonnormality are not asserted here. -/
theorem quotient_properties :
    IsProper yToBase ∧ IsIntegral Y ∧ IsNoetherian Y ∧ topologicalKrullDim Y = 2 ∧
      IsFinite rho ∧ Surjective rho ∧ rho ≫ yToBase = sToBase ∧
      Function.Bijective (globalScalarMap ell yToBase) :=
  ⟨y_proper, y_integral, y_noetherian, y_dimension, rho_finite, rho_surjective,
    rho_over_ell, y_globalScalarMap_bijective⟩

end
end Eff

import Eff.Quotient
import Red61.Surface.SpecialPointStalk
import SurfaceLib.Abelian.Rigidity

/-! # The Albanese variety of the second quotient is trivial

The chart `V₁ = 𝔸²_k` maps dominantly to `Y`. Classical rigidity makes the composite with any map
to a para-abelian variety constant. Since `Y` is irreducible and `Γ(Y, O_Y) = ell`, the original
map factors uniquely through `Spec ell`. Thus `Spec ell` has the universal property of `Alb_Y`.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.AffineGluing
  AlgebraicGeometry CategoryTheory SurfaceLib.Abelian
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The inclusion of the coordinate ring of the first chart of `Y` in that of `V₁`. -/
def yChartToChart : yAtlas.ring (0 : Fin 4) →+* chartRing 0 where
  toFun x := ⟨((x : M) : L), x.property⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The same inclusion, with `V₁` written as a polynomial ring. -/
def yChartToPoly : yAtlas.ring (0 : Fin 4) →+* MvPolynomial (Fin 2) k :=
  (chartPolynomialEquiv 0).symm.toRingHom.comp yChartToChart

theorem yChartToPoly_injective : Function.Injective yChartToPoly := by
  apply (chartPolynomialEquiv 0).symm.injective.comp
  intro x y h
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  exact congrArg (fun z : chartRing 0 ↦ (z : K)) h

theorem yChartToPoly_scalar (a : ell) :
    yChartToPoly (algebraMap ell (yAtlas.ring (0 : Fin 4)) a) =
      algebraMap ell (MvPolynomial (Fin 2) k) a := by
  change (chartPolynomialEquiv 0).symm _ = _
  apply (chartPolynomialEquiv 0).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  have h : chartPolynomialEquiv 0 (MvPolynomial.C (a : k)) =
      algebraMap k (chartRing 0) (a : k) := (chartPolynomialEquiv 0).commutes _
  rw [show algebraMap ell (MvPolynomial (Fin 2) k) a = MvPolynomial.C (a : k) from rfl, h]
  rfl

/-- The dominant map from the affine plane over `k`. -/
def planeToY : Spec (.of (MvPolynomial (Fin 2) k)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom yChartToPoly) ≫ yAtlas.chartInclusion (0 : Fin 4)

theorem planeToY_over_base : planeToY ≫ yToBase =
    Spec.map (CommRingCat.ofHom (algebraMap ell (MvPolynomial (Fin 2) k))) := by
  have h : yAtlas.chartInclusion (0 : Fin 4) ≫ yToBase =
      Spec.map (CommRingCat.ofHom (algebraMap ell (yAtlas.ring (0 : Fin 4)))) :=
    yAtlas.chartInclusion_toBase (0 : Fin 4)
  simp only [planeToY, Category.assoc]
  rw [h, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact yChartToPoly_scalar a

theorem planeToY_generic : planeToY (⊥ : PrimeSpectrum (MvPolynomial (Fin 2) k)) =
    yAtlas.chartInclusion (0 : Fin 4) (⊥ : PrimeSpectrum (yAtlas.ring (0 : Fin 4))) := by
  change yAtlas.chartInclusion (0 : Fin 4) (PrimeSpectrum.comap yChartToPoly ⊥) = _
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap yChartToPoly ⊥ = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp yChartToPoly_injective

theorem spec_ell_unique (x z : Spec (.of ell)) : x = z := by
  have : Subsingleton (PrimeSpectrum ell) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum ell) x z

theorem spec_k_unique (x z : PrimeSpectrum k) : x = z :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime x.asIdeal).trans (Ideal.eq_bot_of_prime z.asIdeal).symm)

theorem toSpecΓ_map {R : CommRingCat} {X : Scheme} (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  simp

instance : Module.Finite ell k := Module.Finite.of_basis pBasis

/-- The morphism from `Y` to its Stein factor is the structure morphism, up to isomorphism. -/
def yScalarIso : IsIso (Spec.map (CommRingCat.ofHom (globalScalarMap ell yToBase))) := by
  have : IsIso (CommRingCat.ofHom (globalScalarMap ell yToBase)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr y_globalScalarMap_bijective
  infer_instance

/-- Morphisms out of `Spec ell` are determined by their composite with the structure morphism. -/
theorem yToBase_cancel {P : Scheme} (φ₁ φ₂ : Spec (.of ell) ⟶ P)
    (h : yToBase ≫ φ₁ = yToBase ≫ φ₂) : φ₁ = φ₂ := by
  let pt : Spec (.of ell) := (⊥ : PrimeSpectrum ell)
  have hsurj : Function.Surjective yToBase := by
    intro x
    obtain ⟨y⟩ : Nonempty Y := inferInstance
    exact ⟨y, spec_ell_unique _ _⟩
  have hpt : φ₁ pt = φ₂ pt := by
    obtain ⟨y, hy⟩ := hsurj pt
    have := congrArg (fun f : Y ⟶ P ↦ f y) h
    simpa [hy] using this
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := φ₁ pt) (U := ⊤) trivial
  have hrange (φ : Spec (.of ell) ⟶ P) (hφ : φ pt = φ₁ pt) :
      Set.range φ ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [spec_ell_unique x pt, hφ]
    exact hmem
  let ψ₁ := IsOpenImmersion.lift hU.fromSpec φ₁ (hrange φ₁ rfl)
  let ψ₂ := IsOpenImmersion.lift hU.fromSpec φ₂ (hrange φ₂ hpt.symm)
  have hψ₁ : ψ₁ ≫ hU.fromSpec = φ₁ := IsOpenImmersion.lift_fac _ _ _
  have hψ₂ : ψ₂ ≫ hU.fromSpec = φ₂ := IsOpenImmersion.lift_fac _ _ _
  have hcomp : yToBase ≫ ψ₁ = yToBase ≫ ψ₂ := by
    rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, hψ₁, hψ₂, h]
  have hinj : Function.Injective yToBase.appTop.hom := by
    intro a b hab
    let e := (Scheme.ΓSpecIso (.of ell)).commRingCatIsoToRingEquiv
    apply e.injective
    apply y_globalScalarMap_bijective.injective
    have hg (z : Γ(Spec (.of ell), ⊤)) : globalScalarMap ell yToBase (e z) = yToBase.appTop.hom z := by
      change yToBase.appTop.hom ((Scheme.ΓSpecIso (.of ell)).inv.hom
        ((Scheme.ΓSpecIso (.of ell)).hom.hom z)) = _
      simp
    rw [hg, hg, hab]
  have hψ : ψ₁ = ψ₂ := by
    have hc := congrArg (fun f : Y ⟶ Spec Γ(P, U) ↦ f.appTop) hcomp
    simp only [Scheme.Hom.comp_appTop] at hc
    have happ : ψ₁.appTop = ψ₂.appTop := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact hinj (ConcreteCategory.congr_hom hc a)
    have htop (ψ : Spec (.of ell) ⟶ Spec Γ(P, U)) : ψ =
        (Spec (.of ell)).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso Γ(P, U)).inv ≫ ψ.appTop) :=
      (toSpecΓ_map ψ).symm
    rw [htop ψ₁, htop ψ₂, happ]
  rw [← hψ₁, ← hψ₂, hψ]

set_option maxHeartbeats 600000 in
/-- The Albanese variety of `Y` is trivial: every map to a para-abelian variety factors uniquely
through `Spec ell`, which is the universal property of the Albanese morphism in that case. -/
theorem y_albanese_trivial (rigidity : ClassicalRationalRigidity) {P : Scheme.{0}}
    (π : P ⟶ Spec (.of ell)) (hP : IsParaAbelianVariety ell π) (g : Y ⟶ P) (hg : g ≫ π = yToBase) :
    ∃! φ : Spec (.of ell) ⟶ P, yToBase ≫ φ = g := by
  have hprop : IsProper π := hP.1
  -- Rigidity on the affine plane.
  have hφ₀ : (planeToY ≫ g) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap ell (MvPolynomial (Fin 2) k))) := by
    rw [Category.assoc, hg, planeToY_over_base]
  obtain ⟨p, hp⟩ := rigidity.constant ell π hP k (planeToY ≫ g) hφ₀
  -- The constant value is a closed point.
  let s : MvPolynomial (Fin 2) k →+* k := (MvPolynomial.aeval fun _ ↦ (0 : k)).toRingHom
  have hsC : Spec.map (CommRingCat.ofHom s) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    simp [s]
  have hpπ : p ≫ π = Spec.map (CommRingCat.ofHom (algebraMap ell k)) := by
    have h1 : Spec.map (CommRingCat.ofHom s) ≫ (planeToY ≫ g) ≫ π = p ≫ π := by
      rw [hp, Category.assoc, ← Category.assoc, hsC, Category.id_comp]
    rw [← h1, hφ₀, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change s (MvPolynomial.C (algebraMap ell k a)) = _
    simp [s]
  have hfin : IsFinite (p ≫ π) := by
    rw [hpπ, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hpproper : IsProper p := IsProper.of_comp p π
  let pt : Spec (.of k) := (⊥ : PrimeSpectrum k)
  let a₀ : P := p pt
  have hclosed : IsClosed ({a₀} : Set P) := by
    have hset : ({a₀} : Set P) = p '' {pt} := by simp [a₀]
    rw [hset]
    exact p.isClosedMap _ (isClosed_discrete _)
  -- The image of `g` is this point.
  have hgen : g (yAtlas.chartInclusion (0 : Fin 4) (⊥ : PrimeSpectrum (yAtlas.ring (0 : Fin 4)))) =
      a₀ := by
    rw [← planeToY_generic]
    have h := congrArg (fun f : Spec (.of (MvPolynomial (Fin 2) k)) ⟶ P ↦
      f (⊥ : PrimeSpectrum (MvPolynomial (Fin 2) k))) hp
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact congrArg p (spec_k_unique _ _)
  have himage (y : Y) : g y = a₀ := by
    have hsp : yAtlas.chartInclusion (0 : Fin 4) (⊥ : PrimeSpectrum (yAtlas.ring (0 : Fin 4))) ⤳ y :=
      (yAtlas.chart_genericPoint (0 : Fin 4)).specializes (Set.mem_univ y)
    have hs' := hsp.map g.continuous
    rw [hgen] at hs'
    exact hs'.mem_closed hclosed (Set.mem_singleton a₀)
  -- Factor through an affine neighbourhood and use the global sections of `Y`.
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := a₀) (U := ⊤) trivial
  have hrange : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rw [himage y]
    exact hmem
  let g' := IsOpenImmersion.lift hU.fromSpec g hrange
  have hg' : g' ≫ hU.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  have hι := yScalarIso
  let ι := Spec.map (CommRingCat.ofHom (globalScalarMap ell yToBase))
  have hbase : Y.toSpecΓ ≫ ι = yToBase := schemeToSpec_globalScalar ell yToBase
  let φ : Spec (.of ell) ⟶ P :=
    inv ι ≫ Spec.map ((Scheme.ΓSpecIso _).inv ≫ g'.appTop) ≫ hU.fromSpec
  have hφ : yToBase ≫ φ = g := by
    rw [← hbase]
    simp only [φ, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, toSpecΓ_map, hg']
  exact ⟨φ, hφ, fun ψ hψ ↦ yToBase_cancel ψ φ (hψ.trans hφ.symm)⟩

/-- The factorization through `Spec ell` is a section of the structure morphism. -/
theorem y_albanese_section {P : Scheme.{0}} (π : P ⟶ Spec (.of ell)) (g : Y ⟶ P)
    (hg : g ≫ π = yToBase) (φ : Spec (.of ell) ⟶ P) (hφ : yToBase ≫ φ = g) : φ ≫ π = 𝟙 _ := by
  apply yToBase_cancel
  rw [← Category.assoc, hφ, hg, Category.comp_id]

/-- The Albanese morphism of `Y` is the structure morphism to `Spec ell`. -/
theorem y_albanese_is_base (rigidity : ClassicalRationalRigidity) :
    IsAlbaneseMorphism yToBase (𝟙 _) yToBase where
  target := isParaAbelianVariety_id ell
  overBase := Category.comp_id _
  universal ρ hρ g hg := by
    obtain ⟨φ, hφ, huniq⟩ := y_albanese_trivial rigidity ρ hρ g hg
    exact ⟨φ, ⟨y_albanese_section ρ g hg φ hφ, hφ⟩, fun ψ hψ ↦ huniq ψ hψ.2⟩

end
end Eff

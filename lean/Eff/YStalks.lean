import Eff.YDifferentials

/-! # Coordinate data on the stalks of the second quotient -/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent
  AlgebraicGeometry CategoryTheory Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance : Algebra ell Y.functionField := functionFieldAlgebra ell yToBase

/-- If one chart ring of a principal atlas has fraction field `F`, then so has every other. -/
theorem atlas_chart_isFractionRing {k F : Type} [Field k] [Field F] [Algebra k F]
    (D : PrincipalAtlas k F) (i j : D.Index) [IsFractionRing (D.ring i) F] :
    IsFractionRing (D.ring j) F := by
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D.ring i) x
  obtain ⟨d, hd⟩ := D.localization j i
  obtain ⟨hd0, he⟩ := localization_description
    (show D.ring j ≤ D.ring j ⊔ D.ring i from le_sup_left) d hd
  have hb0 : (b : F) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hmem (z : D.ring i) : ∃ n : ℕ, (z : F) * (d : F) ^ n ∈ D.ring j := by
    have hz : (z : F) ∈ D.ring j ⊔ D.ring i :=
      (show D.ring i ≤ D.ring j ⊔ D.ring i from le_sup_right) z.property
    rw [he] at hz
    exact adjoin_inverse_denominators (D.ring j) d hd0 hz
  obtain ⟨n, hn⟩ := hmem a
  obtain ⟨m, hm⟩ := hmem b
  refine ⟨⟨_, (D.ring j).mul_mem hn ((D.ring j).pow_mem d.property m)⟩,
    ⟨_, (D.ring j).mul_mem hm ((D.ring j).pow_mem d.property n)⟩, ?_⟩
  change (a : F) / (b : F) = ((a : F) * (d : F) ^ n * (d : F) ^ m) / ((b : F) * (d : F) ^ m * (d : F) ^ n)
  have hdn : (d : F) ≠ 0 := hd0
  field_simp

instance yChart_isFractionRing (i : yAtlas.Index) : IsFractionRing (yAtlas.ring i) M :=
  atlas_chart_isFractionRing yAtlas (0 : Fin 4) i

def yFunctionFieldEquiv : Y.functionField ≃ₐ[ell] M :=
  yAtlas.functionFieldAlgEquiv (0 : Fin 4)

def yFieldAmbientMap : Y.functionField →+* K :=
  L.subtype.comp (M.subtype.comp yFunctionFieldEquiv.toRingHom)

def yStalkAmbientMap (y : Y) : Y.presheaf.stalk y →+* K :=
  yFieldAmbientMap.comp (algebraMap (Y.presheaf.stalk y) Y.functionField)

theorem yFieldAmbientMap_injective : Function.Injective yFieldAmbientMap :=
  L.subtype_injective.comp (M.subtype_injective.comp yFunctionFieldEquiv.injective)

theorem yStalkAmbientMap_algebraMap (y : Y) (a : Y.presheaf.stalk y) :
    yFieldAmbientMap (algebraMap (Y.presheaf.stalk y) Y.functionField a) =
      yStalkAmbientMap y a := rfl

structure YStalkCoordinateData (y : Y) (v : Fin 4 → K) where
  coordinates : Fin 4 → Y.presheaf.stalk y
  basis : Basis (Fin 4) (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y)
  differential (k : Fin 4) : basis k = KaehlerDifferential.D ℤ (Y.presheaf.stalk y) (coordinates k)
  embedding (k : Fin 4) : yStalkAmbientMap y (coordinates k) = v k

theorem y_chart_field_identification (i : yAtlas.Index) :
    (yAtlas.functionFieldChartEquiv i).trans
      (affineFunctionFieldEquiv (CommRingCat.of (yAtlas.ring i)) M) =
        yFunctionFieldEquiv.toRingEquiv :=
  yAtlas.functionField_identification_independent i (0 : Fin 4)

theorem yChartToStalk_ambient (i : yAtlas.Index) (p : PrimeSpectrum (yAtlas.ring i)) (y : Y)
    (hy : y = yAtlas.chartInclusion i p) (a : yAtlas.ring i) :
    yStalkAmbientMap y (yAtlas.chartToStalkAt i p y hy a) = (((a : M) : L) : K) :=
  congrArg (fun z : M ↦ ((z : L) : K))
    (yAtlas.chartToStalkAt_embedding i p y hy yFunctionFieldEquiv.toRingEquiv
      (y_chart_field_identification i) a)

/-- The coordinates of a principal open give coordinate data at each of its stalks. -/
theorem YOpen.stalkCoordinateData {i : Fin 4} (U : YOpen i)
    (p : PrimeSpectrum (yAtlas.ring i)) (hd : U.d ∉ p.asIdeal) (y : Y)
    (hy : y = yAtlas.chartInclusion i p) :
    Nonempty (YStalkCoordinateData y (fun k ↦ (U.coordinates k : K))) := by
  let := U.algebra
  have := U.isLocalization
  let e : Localization.AtPrime p.asIdeal ≃+* Y.presheaf.stalk y :=
    yAtlas.chartLocalizationEquivAt i p y hy
  have hA (x : yAtlas.ring i) :
      yStalkAmbientMap y (e (algebraMap (yAtlas.ring i) (Localization.AtPrime p.asIdeal) x)) =
        (ConeRing.invariantInclusion.toRingHom.comp U.kernel.val.toRingHom)
          (algebraMap (yAtlas.ring i) U.kernel x) :=
    (congrArg (yStalkAmbientMap y) (yAtlas.chartLocalizationEquivAt_algebraMap i p y hy x)).trans
      (yChartToStalk_ambient i p y hy x)
  obtain ⟨f, b, hb, hf⟩ := differentialCoordinatesAtPrime_transport
    (A := yAtlas.ring i) (B := U.kernel) (R := Y.presheaf.stalk y) (F := K) (ι := Fin 4)
    U.d p hd U.absBasis U.coordinates U.absBasis_apply e (yStalkAmbientMap y)
    (ConeRing.invariantInclusion.toRingHom.comp U.kernel.val.toRingHom) hA
  exact ⟨⟨fun k ↦ f (U.coordinates k), b, hb, fun k ↦ hf _⟩⟩

/-- The coordinate ring of a principal open maps to its stalks, compatibly with the field. -/
theorem YOpen.exists_stalkMap {i : Fin 4} (U : YOpen i)
    (p : PrimeSpectrum (yAtlas.ring i)) (hd : U.d ∉ p.asIdeal) (y : Y)
    (hy : y = yAtlas.chartInclusion i p) :
    ∃ f : U.kernel →+* Y.presheaf.stalk y, ∀ x : U.kernel, yStalkAmbientMap y (f x) = (x : K) := by
  let := U.algebra
  have := U.isLocalization
  let e : Localization.AtPrime p.asIdeal ≃+* Y.presheaf.stalk y :=
    yAtlas.chartLocalizationEquivAt i p y hy
  have hA (x : yAtlas.ring i) :
      yStalkAmbientMap y (e (algebraMap (yAtlas.ring i) (Localization.AtPrime p.asIdeal) x)) =
        (ConeRing.invariantInclusion.toRingHom.comp U.kernel.val.toRingHom)
          (algebraMap (yAtlas.ring i) U.kernel x) :=
    (congrArg (yStalkAmbientMap y) (yAtlas.chartLocalizationEquivAt_algebraMap i p y hy x)).trans
      (yChartToStalk_ambient i p y hy x)
  obtain ⟨f, b, -, hf⟩ := differentialCoordinatesAtPrime_transport
    (A := yAtlas.ring i) (B := U.kernel) (R := Y.presheaf.stalk y) (F := K) (ι := Fin 4)
    U.d p hd U.absBasis U.coordinates U.absBasis_apply e (yStalkAmbientMap y)
    (ConeRing.invariantInclusion.toRingHom.comp U.kernel.val.toRingHom) hA
  exact ⟨f, hf⟩

/-- Every stalk element is a fraction of chart elements, with denominator outside the prime. -/
theorem stalk_fraction (i : Fin 4) (p : PrimeSpectrum (yAtlas.ring i)) (y : Y)
    (hy : y = yAtlas.chartInclusion i p) (v : Y.presheaf.stalk y) :
    ∃ (r s : yAtlas.ring i), s ∉ p.asIdeal ∧
      yStalkAmbientMap y v * (((s : M) : L) : K) = (((r : M) : L) : K) := by
  let := (yAtlas.chartToStalkAt i p y hy).toAlgebra
  have := yAtlas.chartToStalkAt_isLocalization i p y hy
  obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl v
  refine ⟨r, s, s.property, ?_⟩
  have h := congrArg (yStalkAmbientMap y) he
  rw [map_mul] at h
  have h1 := yChartToStalk_ambient i p y hy (s : yAtlas.ring i)
  have h2 := yChartToStalk_ambient i p y hy r
  change yStalkAmbientMap y v * yStalkAmbientMap y (yAtlas.chartToStalkAt i p y hy s) =
    yStalkAmbientMap y (yAtlas.chartToStalkAt i p y hy r) at h
  rw [h1, h2] at h
  exact h

end
end Eff

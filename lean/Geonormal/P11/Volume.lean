import Geonormal.P11.PointP0
import Red61.AlgebraicGeometry.RationalForms.ExteriorLattice
import Red61.AlgebraicGeometry.StalkCoordinates

/-! # Differentials and the volume form of the characteristic-11 surface

Every point of `X` lies on a principal open of the charts `A`, `B`, `D`, or on the principal open
`D(e)` of the chart `P` around `P₀`; on each of these the absolute differentials have an explicit
basis, so they are locally free of rank three. The rational form `da ∧ db ∧ dσ` is the
determinant of these bases up to a unit (`±∂h/∂X_m` on the charts `A`, `B`, `D`, and `δ` on
`D(e)`), so it trivializes the third exterior power of the absolute differentials.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial Module

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-- A chart index of the atlas. -/
abbrev ix (i : Fin 4) : atlas.Index := i

/-! ## The principal open around `P₀` as an open subscheme -/

/-- The inclusion of `D(e)` into the chart `P`. -/
def pchartInclP : Spec (CommRingCat.of PChartP) ⟶ Spec (CommRingCat.of chartP) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion chartP_le_PChartP).toRingHom)

/-- `D(e)` as an open subscheme of `X`. -/
def pchartMapP : Spec (CommRingCat.of PChartP) ⟶ X11 :=
  pchartInclP ≫ atlas.chartInclusion (ix 3)

instance pchartMapP_isOpenImmersion : IsOpenImmersion pchartMapP := by
  let := inclusionAlgebra chartP_le_PChartP
  have := PChartP_isLocalization
  have h1 : IsOpenImmersion pchartInclP :=
    IsOpenImmersion.of_isLocalization (R := chartP) (S := PChartP) eP
  exact @IsOpenImmersion.comp _ _ _ pchartInclP (atlas.chartInclusion (ix 3)) h1
    (atlas.chartInclusion_open (ix 3))

theorem mem_range_pchartMapP (p : PrimeSpectrum (atlas.ring (ix 3)))
    (hp : (eP : atlas.ring (ix 3)) ∉ p.asIdeal) :
    atlas.chartInclusion (ix 3) p ∈ Set.range pchartMapP := by
  let := inclusionAlgebra chartP_le_PChartP
  have := PChartP_isLocalization
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap chartP PChartP)) := by
    rw [PrimeSpectrum.localization_away_comap_range PChartP eP]
    exact hp
  obtain ⟨z, rfl⟩ := hq
  exact ⟨z, rfl⟩

/-- Every point lies on one of the charts `A`, `B`, `D`, or on `D(e)`. -/
theorem point_cases (x : X11) :
    (∃ (i : Fin 3) (p : PrimeSpectrum (atlas.ring (ix i.castSucc))),
      atlas.chartInclusion (ix i.castSucc) p = x) ∨
    (∃ p : PrimeSpectrum (atlas.ring (ix 3)), (eP : atlas.ring (ix 3)) ∉ p.asIdeal ∧
      atlas.chartInclusion (ix 3) p = x) := by
  have key : ∀ (j : Fin 4) (p : PrimeSpectrum (atlas.ring (ix j))),
      (∃ (i : Fin 3) (q : PrimeSpectrum (atlas.ring (ix i.castSucc))),
        atlas.chartInclusion (ix i.castSucc) q = atlas.chartInclusion (ix j) p) ∨
      (∃ q : PrimeSpectrum (atlas.ring (ix 3)), (eP : atlas.ring (ix 3)) ∉ q.asIdeal ∧
        atlas.chartInclusion (ix 3) q = atlas.chartInclusion (ix j) p) := by
    intro j p
    fin_cases j
    · exact Or.inl ⟨0, p, rfl⟩
    · exact Or.inl ⟨1, p, rfl⟩
    · exact Or.inl ⟨2, p, rfl⟩
    · by_cases he : (eP : atlas.ring (ix 3)) ∈ p.asIdeal
      · left
        have hne : p.asIdeal ≠ 𝔪₀ := fun h ↦ eP_not_mem (h ▸ he)
        by_cases hw : (wP : atlas.ring (ix 3)) ∈ p.asIdeal
        · by_cases ha : (aPP : atlas.ring (ix 3)) ∈ p.asIdeal
          · exact absurd (@eq_𝔪₀ p.asIdeal p.isPrime hw ha) hne
          · obtain ⟨q, hq⟩ := exists_chart_of_away (3 : Fin 4) (2 : Fin 4) aPP away_PD p ha
            exact ⟨2, q, hq⟩
        · obtain ⟨q, hq⟩ := exists_chart_of_away (3 : Fin 4) (0 : Fin 4) wP away_PA p hw
          exact ⟨0, q, hq⟩
      · exact Or.inr ⟨p, he, rfl⟩
  obtain ⟨j, p, rfl⟩ := atlas.chartInclusion_cover x
  exact key j p

/-! ## Local freeness -/

/-- The absolute differentials of `X` are locally free of rank three. -/
theorem x_differentials_locallyFree :
    IsLocallyFreeOfRank 3 (nativeAbsoluteDifferentialModule X11) := fun x ↦ by
  rcases point_cases x with ⟨i, p, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨m, ha, hx⟩ := exists_pchart i p
    have := pchartMap_isOpenImmersion i m ha
    exact ⟨{
      U := _
      j := pchartMap i m
      mem := hx
      frame := affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of (PChart i m))
        (pchartMap i m) (localBasisZ i m ha) }⟩
  · exact ⟨{
      U := _
      j := pchartMapP
      mem := mem_range_pchartMapP p hp
      frame := affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of PChartP)
        pchartMapP localBasisPZ }⟩

/-! ## The function field of `X` -/

private local instance : CommRing X11.functionField :=
  (inferInstance : Field X11.functionField).toCommRing
private local instance : Algebra k X11.functionField := functionFieldAlgebra k xToBase

/-- The function field of `X` is `L`. -/
def xFunctionFieldEquiv : X11.functionField ≃ₐ[k] L := atlas.functionFieldAlgEquiv (ix 0)

/-- The same identification as a ring isomorphism. -/
abbrev eK : X11.functionField ≃+* L := xFunctionFieldEquiv.toRingEquiv

theorem chart_field_identification (i : Fin 4) :
    (atlas.functionFieldChartEquiv (ix i)).trans
      (affineFunctionFieldEquiv (CommRingCat.of (atlas.ring (ix i))) L) = eK :=
  atlas.functionField_identification_independent (ix i) (ix 0)

/-- The local ring of a point, inside `L`. -/
def xStalkAmbientMap (z : X11) : X11.presheaf.stalk z →+* L :=
  eK.toRingHom.comp (algebraMap (X11.presheaf.stalk z) X11.functionField)

theorem chartToStalk_ambient (i : Fin 4) (p : PrimeSpectrum (atlas.ring (ix i))) (z : X11)
    (hz : z = atlas.chartInclusion (ix i) p) (a : atlas.ring (ix i)) :
    xStalkAmbientMap z (atlas.chartToStalkAt (ix i) p z hz a) = (a : L) :=
  atlas.chartToStalkAt_embedding (ix i) p z hz eK (chart_field_identification i) a

/-! ## The rational volume -/

/-- The basis `da, db, dσ` of the absolute differentials of the function field of `X`. -/
def rationalBasis : Basis (Fin 3) X11.functionField (KaehlerDifferential ℤ X11.functionField) :=
  absoluteDifferentialBasisOfRingEquiv eK.symm fieldBasisZ

theorem rationalBasis_repr_D (a : L) (n : Fin 3) :
    rationalBasis.repr (KaehlerDifferential.D ℤ X11.functionField (eK.symm a)) n =
      eK.symm (fieldBasisZ.repr (KaehlerDifferential.D ℤ L a) n) := by
  let := eK.symm.toRingHom.toAlgebra
  have : @IsScalarTower ℤ L X11.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.FormallyEtale L X11.functionField :=
    formallyEtale_of_bijective L X11.functionField eK.symm.bijective
  change (differentialBasisOfFormallyEtale ℤ L X11.functionField (Fin 3) fieldBasisZ).repr
    (KaehlerDifferential.D ℤ X11.functionField (algebraMap L X11.functionField a)) n = _
  rw [differentialBasisOfFormallyEtale, Basis.map_repr, LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

theorem rationalBasis_det (f : Fin 3 → L) :
    rationalBasis.det (fun l ↦ KaehlerDifferential.D ℤ X11.functionField (eK.symm (f l))) =
      eK.symm (fieldBasisZ.det (fun l ↦ KaehlerDifferential.D ℤ L (f l))) := by
  rw [Basis.det_apply, Basis.det_apply]
  change _ = eK.symm.toRingHom _
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    rationalBasis_repr_D]
  rfl

/-- The rational volume `da ∧ db ∧ dσ` of `X`. -/
def xRationalVolume : RationalSchemeForms X11 3 :=
  exteriorPower.ιMulti X11.functionField 3 rationalBasis

-- Unifying exterior powers of the base-changed stalk differentials is slow.
set_option maxHeartbeats 1000000 in
/-- A stalk basis of exact differentials, the first rescaled by a unit, has the rational volume
if the volume identity holds in `L`. -/
theorem generates_of_coordinates (z : X11) (s : Fin 3 → X11.presheaf.stalk z)
    (b : Basis (Fin 3) (X11.presheaf.stalk z) (AbsoluteStalkDifferentials X11 z))
    (hb : ∀ l, b l = KaehlerDifferential.D ℤ (X11.presheaf.stalk z) (s l))
    (u : (X11.presheaf.stalk z)ˣ)
    (hu : xStalkAmbientMap z u * fieldBasisZ.det
      (fun l ↦ KaehlerDifferential.D ℤ L (xStalkAmbientMap z (s l))) = 1) :
    GeneratesStalkDifferentialLattice z xRationalVolume := by
  refine ⟨b.unitsSMul (Pi.mulSingle 0 u), ?_⟩
  have hvec (l : Fin 3) : stalkRationalDifferentialEquiv z
      (((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X11.functionField) l) =
      algebraMap (X11.presheaf.stalk z) X11.functionField
          (((Pi.mulSingle 0 u : Fin 3 → (X11.presheaf.stalk z)ˣ) l : (X11.presheaf.stalk z)ˣ) :
            X11.presheaf.stalk z) •
        KaehlerDifferential.D ℤ X11.functionField (eK.symm (xStalkAmbientMap z (s l))) := by
    rw [Basis.baseChange_apply, Basis.unitsSMul_apply, hb, Units.smul_def,
      ← TensorProduct.smul_tmul, stalkRationalDifferentialEquiv_tmul_D, Algebra.smul_def, mul_one]
    congr 2
    exact (eK.symm_apply_apply _).symm
  change xRationalVolume = exteriorPower.map 3 (stalkRationalDifferentialEquiv z).toLinearMap
    (exteriorPower.ιMulti X11.functionField 3
      ((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X11.functionField))
  have hfun : (⇑(stalkRationalDifferentialEquiv z).toLinearMap ∘
      ⇑((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X11.functionField)) = fun l ↦
        algebraMap (X11.presheaf.stalk z) X11.functionField
            (((Pi.mulSingle 0 u : Fin 3 → (X11.presheaf.stalk z)ˣ) l : (X11.presheaf.stalk z)ˣ) :
            X11.presheaf.stalk z) •
          KaehlerDifferential.D ℤ X11.functionField (eK.symm (xStalkAmbientMap z (s l))) :=
    funext hvec
  rw [exteriorPower.map_apply_ιMulti]
  apply (topExteriorCoefficient_bijective rationalBasis).injective
  rw [topExteriorCoefficient_wedge, hfun, AlternatingMap.map_smul_univ, rationalBasis_det,
    smul_eq_mul, xRationalVolume, topExteriorCoefficient_volume, Fin.prod_univ_three]
  simp only [Pi.mulSingle_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    not_false_eq_true, Pi.mulSingle_eq_of_ne, Units.val_one, map_one, mul_one,
    show (2 : Fin 3) ≠ 0 by decide]
  rw [← map_one eK.symm, ← hu, map_mul]
  congr 1
  exact eK.symm_apply_apply _

theorem val_algebraMap_inclusion {A B : Subalgebra k L} (h : A ≤ B) (a : A) :
    letI := inclusionAlgebra h
    B.val.toRingHom (algebraMap A B a) = (a : L) := rfl

theorem ambient_chartLocalization (i : Fin 4) (p : PrimeSpectrum (atlas.ring (ix i)))
    (a : atlas.ring (ix i)) :
    xStalkAmbientMap _ (atlas.chartLocalizationEquivAt (ix i) p _ rfl
      (algebraMap (atlas.ring (ix i)) (Localization.AtPrime p.asIdeal) a)) = (a : L) :=
  (congrArg (xStalkAmbientMap _)
    (atlas.chartLocalizationEquivAt_algebraMap (ix i) p _ rfl a)).trans
      (chartToStalk_ambient i p _ rfl a)

/-- Stalk coordinates at a point of a principal open of a chart, compatible with `L`. -/
theorem stalk_coordinates (j : Fin 4) (B : Subalgebra k L) (hB : atlas.ring (ix j) ≤ B)
    (d : atlas.ring (ix j))
    (hloc : letI := inclusionAlgebra hB
      IsLocalization.Away d B)
    (p : PrimeSpectrum (atlas.ring (ix j))) (hd : d ∉ p.asIdeal)
    (b : Basis (Fin 3) B (KaehlerDifferential ℤ B)) (v : Fin 3 → B)
    (hb : ∀ l, b l = KaehlerDifferential.D ℤ B (v l)) :
    ∃ (f : B →+* X11.presheaf.stalk (atlas.chartInclusion (ix j) p))
      (b' : Basis (Fin 3) (X11.presheaf.stalk (atlas.chartInclusion (ix j) p))
        (AbsoluteStalkDifferentials X11 (atlas.chartInclusion (ix j) p))),
      (∀ l, b' l = KaehlerDifferential.D ℤ _ (f (v l))) ∧
        ∀ a, xStalkAmbientMap _ (f a) = (a : L) := by
  let := inclusionAlgebra hB
  have := hloc
  have hA (a : atlas.ring (ix j)) : xStalkAmbientMap _ (atlas.chartLocalizationEquivAt (ix j) p _ rfl
      (algebraMap (atlas.ring (ix j)) (Localization.AtPrime p.asIdeal) a)) =
        B.val.toRingHom (algebraMap (atlas.ring (ix j)) B a) := by
    rw [ambient_chartLocalization, val_algebraMap_inclusion]
  exact differentialCoordinatesAtPrime_transport
    (A := atlas.ring (ix j)) (B := B) (R := X11.presheaf.stalk (atlas.chartInclusion (ix j) p))
    (F := L) (ι := Fin 3) d p hd b v hb
    (atlas.chartLocalizationEquivAt (ix j) p _ rfl) (xStalkAmbientMap _) B.val.toRingHom hA

theorem fieldBasisZ_det (f : Fin 3 → L) :
    fieldBasisZ.det (fun l ↦ KaehlerDifferential.D ℤ L (f l)) =
      fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (f l)) := by
  rw [fieldBasisZ, Basis.det_map]
  congr 1
  funext l
  simp [quotientBaseDifferentialEquiv_D]

theorem keptSign_mul_self (i : Fin 3) (m : Fin 4) : keptSign i m * keptSign i m = 1 := by
  fin_cases i <;> fin_cases m <;> simp [keptSign]

theorem keptSign_mem (T : Subalgebra k L) (i : Fin 3) (m : Fin 4) : keptSign i m ∈ T := by
  fin_cases i <;> fin_cases m <;> simp [keptSign, T.one_mem, T.neg_mem T.one_mem]

/-- The rational volume generates the differential lattice at every point of `A`, `B`, `D`. -/
theorem generates_ABD (i : Fin 3) (p : PrimeSpectrum (atlas.ring (ix i.castSucc))) :
    GeneratesStalkDifferentialLattice (atlas.chartInclusion (ix i.castSucc) p) xRationalVolume := by
  obtain ⟨m, hm⟩ := @exists_partial_not_mem i p.asIdeal p.isPrime
  have ha : partialVal i m ≠ 0 := fun h0 ↦ hm (by
    rw [show (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc) = 0 from Subtype.ext h0]
    exact zero_mem _)
  obtain ⟨f, b, hb, hf⟩ := stalk_coordinates (i.castSucc) (PChart i m) (chartRing_le_PChart i m)
    ⟨partialVal i m, partialVal_mem i _⟩ (PChart_isLocalization i m ha) p hm (localBasisZ i m ha)
    (fun l ↦ zloc i m (kept m l)) (localBasisZ_apply i m ha)
  let u₀ : PChart i m := ⟨keptSign i m * (partialVal i m)⁻¹,
    Subalgebra.mul_mem _ (keptSign_mem _ i m) (inv_mem_PChart i m)⟩
  let v₀ : PChart i m := ⟨keptSign i m * partialVal i m,
    Subalgebra.mul_mem _ (keptSign_mem _ i m) (chartRing_le_PChart i m (partialVal_mem i _))⟩
  have huv : u₀ * v₀ = 1 := Subtype.ext (by
    change keptSign i m * (partialVal i m)⁻¹ * (keptSign i m * partialVal i m) = 1
    rw [show keptSign i m * (partialVal i m)⁻¹ * (keptSign i m * partialVal i m) =
      (keptSign i m * keptSign i m) * ((partialVal i m)⁻¹ * partialVal i m) by ring,
      inv_mul_cancel₀ ha, mul_one, keptSign_mul_self])
  refine generates_of_coordinates _ (fun l ↦ f (zloc i m (kept m l))) b hb
    (Units.map f.toMonoidHom (Units.mkOfMulEqOne u₀ v₀ huv)) ?_
  simp only [Units.coe_map, Units.val_mkOfMulEqOne, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, hf]
  change (keptSign i m * (partialVal i m)⁻¹ : L) * fieldBasisZ.det
    (fun l ↦ KaehlerDifferential.D ℤ L (chartVals i (kept m l))) = 1
  rw [fieldBasisZ_det, det_kept i m ha]
  rw [show keptSign i m * (partialVal i m)⁻¹ * (keptSign i m * partialVal i m) =
    (keptSign i m * keptSign i m) * ((partialVal i m)⁻¹ * partialVal i m) by ring,
    inv_mul_cancel₀ ha, mul_one, keptSign_mul_self]

theorem δP_inv_mem : δP⁻¹ ∈ PChartP := by
  have h : δP⁻¹ = (rN : L) * (eP : L)⁻¹ := by
    have hδ := δP_ne_zero
    have hr : (rN : L) ≠ 0 := fun h0 ↦ rN_not_mem (by
      rw [show rN = 0 from Subtype.ext h0]
      exact zero_mem _)
    change δP⁻¹ = (rN : L) * ((rN : L) * δP)⁻¹
    field_simp
  rw [h]
  exact Subalgebra.mul_mem _ (chartP_le_PChartP rN.2) inv_mem_PChartP

/-- The rational volume generates the differential lattice at every point of `D(e)`. -/
theorem generates_P (p : PrimeSpectrum (atlas.ring (ix 3))) (hp : (eP : atlas.ring (ix 3)) ∉ p.asIdeal) :
    GeneratesStalkDifferentialLattice (atlas.chartInclusion (ix 3) p) xRationalVolume := by
  obtain ⟨f, b, hb, hf⟩ := stalk_coordinates 3 PChartP chartP_le_PChartP eP PChartP_isLocalization p
    hp localBasisPZ zP localBasisPZ_apply
  let u₀ : PChartP := ⟨δP⁻¹, δP_inv_mem⟩
  let v₀ : PChartP := ⟨δP, chartP_le_PChartP δP_mem⟩
  have huv : u₀ * v₀ = 1 := Subtype.ext (inv_mul_cancel₀ δP_ne_zero)
  refine generates_of_coordinates _ (fun l ↦ f (zP l)) b hb
    (Units.map f.toMonoidHom (Units.mkOfMulEqOne u₀ v₀ huv)) ?_
  simp only [Units.coe_map, Units.val_mkOfMulEqOne, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, hf]
  change δP⁻¹ * fieldBasisZ.det (fun l ↦ KaehlerDifferential.D ℤ L ((zP l : PChartP) : L)) = 1
  rw [fieldBasisZ_det, det_zP]
  exact inv_mul_cancel₀ δP_ne_zero

/-- The rational volume generates the absolute differential lattice at every point. -/
theorem xRationalVolume_generates (z : X11) :
    GeneratesStalkDifferentialLattice z xRationalVolume := by
  rcases point_cases z with ⟨i, p, rfl⟩ | ⟨p, hp, rfl⟩
  · exact generates_ABD i p
  · exact generates_P p hp

/-! ## Frames of the top exterior power -/

/-- On a principal open with a differential basis, the third exterior power is free of rank one. -/
def topFrameOf {B : Type} [CommRing B] (j : Spec (CommRingCat.of B) ⟶ X11) [IsOpenImmersion j]
    (b : Basis (Fin 3) B (KaehlerDifferential ℤ B)) :
    structureSheafModule (Spec (CommRingCat.of B)) ≅
      (nativeExteriorModule X11 (nativeAbsoluteDifferentialModule X11) 3).restrict j :=
  (nativeFiniteFreeTopExteriorIso (Spec (CommRingCat.of B)) 3).symm ≪≫
    (nativeExteriorFunctor (Spec (CommRingCat.of B)) 3).mapIso
      (affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of B) j b) ≪≫
        nativeExteriorRestrictionIso j (nativeAbsoluteDifferentialModule X11) 3

theorem xTopFrames (z : X11) : Nonempty (nativeAbsoluteExteriorStalkFrameType X11 3 z) := by
  rcases point_cases z with ⟨i, p, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨m, ha, q, hq⟩ := exists_pchart i p
    have := pchartMap_isOpenImmersion i m ha
    rw [← hq]
    exact ⟨openImmersionStalkFrameEquiv (pchartMap i m) q _ (topFrameOf (pchartMap i m)
      (localBasisZ i m ha))⟩
  · obtain ⟨q, hq⟩ := mem_range_pchartMapP p hp
    rw [← hq]
    exact ⟨openImmersionStalkFrameEquiv pchartMapP q _ (topFrameOf pchartMapP localBasisPZ)⟩

/-- The rational volume `da ∧ db ∧ dσ` trivializes the third exterior power of the absolute
differentials of `X`. -/
def xVolumeIso : structureSheafModule X11 ≅
    nativeExteriorModule X11 (nativeAbsoluteDifferentialModule X11) 3 :=
  nativeAbsoluteExteriorVolumeIso X11 3 xRationalVolume
    (GeneratesStalkDifferentialLattice.ne_zero _ (xRationalVolume_generates (genericPoint X11)))
    xRationalVolume_generates (fun z ↦ Classical.choose (xRationalVolume_generates z)) xTopFrames

end
end Geonormal.P11

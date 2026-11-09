import Geonormal.Differentials
import Red61.AlgebraicGeometry.RationalForms.ExteriorLattice
import Red61.AlgebraicGeometry.StalkCoordinates

/-! # The volume form of the characteristic-19 surface

`dc ∧ dt ∧ dx / (2y)` is a rational top form of `X`. On the principal open of a chart where
`∂h/∂X_{m+1}` is a unit, the differentials of the kept coordinates, the first one rescaled by a
unit, have exactly this volume. So the form generates the absolute differential lattice at every
point, and it trivializes the third exterior power of the absolute differentials.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial Module

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-! ## Jacobians in the function field -/

theorem t_ne_zero : t ≠ 0 := (map_ne_zero _).mpr tE_ne_zero

theorem x_ne_zero : x ≠ 0 := (map_ne_zero _).mpr xE_ne_zero

theorem monoF_eq (v : Lattice) : monoF v = t ^ v.1 * x ^ v.2 := by
  rw [monoF, monoE, map_mul, map_zpow₀, map_zpow₀]
  rfl

theorem D_zpow (a : F) (n : ℤ) (ha : a ≠ 0) :
    KaehlerDifferential.D F₁₉ F (a ^ n) =
      (n * a ^ n * a⁻¹ : F) • KaehlerDifferential.D F₁₉ F a := by
  rw [Derivation.leibniz_zpow, zpow_sub_one₀ ha, ← Int.cast_smul_eq_zsmul F, smul_smul]
  congr 1
  ring

theorem D_monoF (v : Lattice) : KaehlerDifferential.D F₁₉ F (monoF v) =
    (monoF v * v.1 * t⁻¹) • KaehlerDifferential.D F₁₉ F t +
      (monoF v * v.2 * x⁻¹) • KaehlerDifferential.D F₁₉ F x := by
  rw [monoF_eq, Derivation.leibniz, D_zpow _ _ t_ne_zero, D_zpow _ _ x_ne_zero, smul_smul,
    smul_smul, add_comm]
  congr 2 <;> ring

theorem fieldBasisF_zero_one : fieldBasisF 0 1 = KaehlerDifferential.D F₁₉ F t := by
  rw [fieldBasisF_apply]
  change KaehlerDifferential.D F₁₉ F (monoF (first 0)) = _
  rw [monoF_eq]
  simp [first]

theorem fieldBasisF_zero_two : fieldBasisF 0 2 = KaehlerDifferential.D F₁₉ F x := by
  rw [fieldBasisF_apply]
  change KaehlerDifferential.D F₁₉ F (monoF (second 0)) = _
  rw [monoF_eq]
  simp [second]

theorem repr_Z_D (i : Fin 5) (a : F) (n : Fin 3) :
    (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F a) n =
      (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F a) n := by
  rw [fieldBasisZ, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    quotientBaseDifferentialEquiv_D]

theorem repr_zero_D_monoF (v : Lattice) (n : Fin 3) :
    (fieldBasisZ 0).repr (KaehlerDifferential.D ℤ F (monoF v)) n =
      (Finsupp.single 1 (monoF v * v.1 * t⁻¹) + Finsupp.single 2 (monoF v * v.2 * x⁻¹) :
        Fin 3 →₀ F) n := by
  rw [repr_Z_D, D_monoF, ← fieldBasisF_zero_one, ← fieldBasisF_zero_two, map_add, map_smul,
    map_smul, Basis.repr_self, Basis.repr_self, Finsupp.smul_single, Finsupp.smul_single,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/-- The orientation of the lattice basis of chart `i`; it is `±1`. -/
def chartSign (i : Fin 5) : ℤ := (first i).1 * (second i).2 - (second i).1 * (first i).2

theorem first_add_second (i : Fin 5) : first i + second i = yScale i + (1, 1) := by
  fin_cases i <;> rfl

theorem monoF_one_one : monoF (1, 1) = t * x := by
  rw [monoF_eq]
  simp

/-- The Jacobian of the chart coordinates `c, e₁, e₂` with respect to `c, t, x`. -/
theorem det_chart (i : Fin 5) :
    (fieldBasisZ 0).det (fieldBasisZ i) = chartSign i * monoF (yScale i) := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp only [Basis.toMatrix_apply, fieldBasisZ_apply]
  have h0 : coordF i 0 = coordF 0 0 := rfl
  have h1 : coordF i 1 = monoF (first i) := rfl
  have h2 : coordF i 2 = monoF (second i) := rfl
  rw [h0, h1, h2, ← fieldBasisZ_apply 0 0, Basis.repr_self]
  simp only [repr_zero_D_monoF, Finsupp.add_apply, Finsupp.single_apply]
  simp
  have hm : monoF (first i) * monoF (second i) = monoF (yScale i) * (t * x) := by
    rw [← monoF_add, first_add_second, monoF_add, monoF_one_one]
  have ht := t_ne_zero
  have hx := x_ne_zero
  rw [chartSign]
  push_cast
  field_simp
  linear_combination ((first i).1 * (second i).2 - (second i).1 * (first i).2 : F) * hm

/-- The orientation of the kept coordinates on the principal open of the `m`-th partial. -/
def keptSign : Fin 3 → ℤ := ![1, -1, 1]

theorem det_kept (i : Fin 5) (m : Fin 3) :
    (fieldBasisZ i).det (fun l ↦ KaehlerDifferential.D ℤ F (chartVals i (kept m l))) =
      keptSign m * (-(2 * yc i)⁻¹ * partialVal i m.succ) := by
  have hy (n : Fin 3) : (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F (chartVals i 0)) n =
      -(2 * yc i)⁻¹ * partialVal i n.succ := by
    rw [repr_Z_D]
    exact repr_D_yc i n
  have hz (j n : Fin 3) :
      (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F (chartVals i j.succ)) n =
        if j = n then 1 else 0 := by
    rw [chartVals_succ, ← fieldBasisZ_apply, Basis.repr_self, Finsupp.single_apply]
  have h1 (n : Fin 3) : (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F (chartVals i 1)) n =
      if (0 : Fin 3) = n then 1 else 0 := hz 0 n
  have h2 (n : Fin 3) : (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F (chartVals i 2)) n =
      if (1 : Fin 3) = n then 1 else 0 := hz 1 n
  have h3 (n : Fin 3) : (fieldBasisZ i).repr (KaehlerDifferential.D ℤ F (chartVals i 3)) n =
      if (2 : Fin 3) = n then 1 else 0 := hz 2 n
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp only [Basis.toMatrix_apply]
  fin_cases m <;> simp [kept, keptSign, hy, h1, h2, h3] <;> ring

/-- The volume of the kept coordinates against `dc ∧ dt ∧ dx`. -/
theorem det_zero_kept (i : Fin 5) (m : Fin 3) :
    (fieldBasisZ 0).det (fun l ↦ KaehlerDifferential.D ℤ F (chartVals i (kept m l))) =
      -(chartSign i * keptSign m) * (2 * y)⁻¹ * partialVal i m.succ := by
  conv_lhs => rw [AlternatingMap.eq_smul_basis_det (fieldBasisZ i) (fieldBasisZ 0).det]
  rw [smul_apply, smul_eq_mul, det_chart, det_kept, yc]
  have hm := monoF_ne_zero (yScale i)
  have hy := y_ne_zero
  have h2 := two_ne_zero_F
  field_simp


/-! ## The function field of `X` -/

private local instance : CommRing X19.functionField :=
  (inferInstance : Field X19.functionField).toCommRing
private local instance : Algebra k X19.functionField := functionFieldAlgebra k xToBase

/-- If one chart ring of a principal atlas has fraction field `F`, then so has every other. -/
theorem atlas_chart_isFractionRing {k F : Type} [Field k] [Field F] [Algebra k F]
    (D : PrincipalAtlas k F) (i j : D.Index) [IsFractionRing (D.ring i) F] :
    IsFractionRing (D.ring j) F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D.ring i) z
  obtain ⟨d, hd⟩ := D.localization j i
  obtain ⟨hd0, he⟩ := localization_description
    (show D.ring j ≤ D.ring j ⊔ D.ring i from le_sup_left) d hd
  have hmem (w : D.ring i) : ∃ n : ℕ, (w : F) * (d : F) ^ n ∈ D.ring j := by
    have hw : (w : F) ∈ D.ring j ⊔ D.ring i :=
      (show D.ring i ≤ D.ring j ⊔ D.ring i from le_sup_right) w.property
    rw [he] at hw
    exact adjoin_inverse_denominators (D.ring j) d hd0 hw
  obtain ⟨n, hn⟩ := hmem a
  obtain ⟨m, hm⟩ := hmem b
  refine ⟨⟨_, (D.ring j).mul_mem hn ((D.ring j).pow_mem d.property m)⟩,
    ⟨_, (D.ring j).mul_mem hm ((D.ring j).pow_mem d.property n)⟩, ?_⟩
  change (a : F) / (b : F) =
    ((a : F) * (d : F) ^ n * (d : F) ^ m) / ((b : F) * (d : F) ^ m * (d : F) ^ n)
  have hdn : (d : F) ≠ 0 := hd0
  field_simp

instance chartRing_isFractionRing (i : atlas.Index) : IsFractionRing (atlas.ring i) F :=
  @atlas_chart_isFractionRing k F _ _ _ atlas (ix 0) i chartRing_zero_isFractionRing

/-- The function field of `X` is `F`. -/
def xFunctionFieldEquiv : X19.functionField ≃ₐ[k] F := atlas.functionFieldAlgEquiv (ix 0)

/-- The same identification as a ring isomorphism. -/
abbrev eK : X19.functionField ≃+* F := xFunctionFieldEquiv.toRingEquiv

theorem chart_field_identification (i : Fin 5) :
    (atlas.functionFieldChartEquiv (ix i)).trans
      (affineFunctionFieldEquiv (CommRingCat.of (atlas.ring (ix i))) F) = eK :=
  atlas.functionField_identification_independent (ix i) (ix 0)

/-- The local ring of a point, inside `F`. -/
def xStalkAmbientMap (z : X19) : X19.presheaf.stalk z →+* F :=
  eK.toRingHom.comp (algebraMap (X19.presheaf.stalk z) X19.functionField)

theorem chartToStalk_ambient (i : Fin 5) (p : PrimeSpectrum (atlas.ring (ix i))) (z : X19)
    (hz : z = atlas.chartInclusion (ix i) p) (a : atlas.ring (ix i)) :
    xStalkAmbientMap z (atlas.chartToStalkAt (ix i) p z hz a) = (a : F) :=
  atlas.chartToStalkAt_embedding (ix i) p z hz eK (chart_field_identification i) a

/-! ## The rational volume -/

/-- The basis `dc, dt, dx` of the absolute differentials of the function field of `X`. -/
def rationalBasis : Basis (Fin 3) X19.functionField (KaehlerDifferential ℤ X19.functionField) :=
  absoluteDifferentialBasisOfRingEquiv eK.symm (fieldBasisZ 0)

theorem rationalBasis_repr_D (a : F) (n : Fin 3) :
    rationalBasis.repr (KaehlerDifferential.D ℤ X19.functionField (eK.symm a)) n =
      eK.symm ((fieldBasisZ 0).repr (KaehlerDifferential.D ℤ F a) n) := by
  let := eK.symm.toRingHom.toAlgebra
  have : @IsScalarTower ℤ F X19.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.FormallyEtale F X19.functionField :=
    formallyEtale_of_bijective F X19.functionField eK.symm.bijective
  change (differentialBasisOfFormallyEtale ℤ F X19.functionField (Fin 3) (fieldBasisZ 0)).repr
    (KaehlerDifferential.D ℤ X19.functionField (algebraMap F X19.functionField a)) n = _
  rw [differentialBasisOfFormallyEtale, Basis.map_repr, LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

theorem rationalBasis_det (f : Fin 3 → F) :
    rationalBasis.det (fun l ↦ KaehlerDifferential.D ℤ X19.functionField (eK.symm (f l))) =
      eK.symm ((fieldBasisZ 0).det (fun l ↦ KaehlerDifferential.D ℤ F (f l))) := by
  rw [Basis.det_apply, Basis.det_apply]
  change _ = eK.symm.toRingHom _
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    rationalBasis_repr_D]
  rfl

/-- The rational volume `dc ∧ dt ∧ dx / (2y)` of `X`. -/
def xRationalVolume : RationalSchemeForms X19 3 :=
  eK.symm (2 * y)⁻¹ • exteriorPower.ιMulti X19.functionField 3 rationalBasis

-- Unifying exterior powers of the base-changed stalk differentials is slow.
set_option maxHeartbeats 1000000 in
/-- A stalk basis of exact differentials, the first rescaled by a unit, has the rational volume
if the volume identity holds in `F`. -/
theorem generates_of_coordinates (z : X19) (s : Fin 3 → X19.presheaf.stalk z)
    (b : Basis (Fin 3) (X19.presheaf.stalk z) (AbsoluteStalkDifferentials X19 z))
    (hb : ∀ l, b l = KaehlerDifferential.D ℤ (X19.presheaf.stalk z) (s l))
    (u : (X19.presheaf.stalk z)ˣ)
    (hu : xStalkAmbientMap z u * (fieldBasisZ 0).det
      (fun l ↦ KaehlerDifferential.D ℤ F (xStalkAmbientMap z (s l))) = (2 * y)⁻¹) :
    GeneratesStalkDifferentialLattice z xRationalVolume := by
  refine ⟨b.unitsSMul (Pi.mulSingle 0 u), ?_⟩
  have hvec (l : Fin 3) : stalkRationalDifferentialEquiv z
      (((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X19.functionField) l) =
      algebraMap (X19.presheaf.stalk z) X19.functionField
          (((Pi.mulSingle 0 u : Fin 3 → (X19.presheaf.stalk z)ˣ) l : (X19.presheaf.stalk z)ˣ) :
            X19.presheaf.stalk z) •
        KaehlerDifferential.D ℤ X19.functionField (eK.symm (xStalkAmbientMap z (s l))) := by
    rw [Basis.baseChange_apply, Basis.unitsSMul_apply, hb, Units.smul_def,
      ← TensorProduct.smul_tmul, stalkRationalDifferentialEquiv_tmul_D, Algebra.smul_def, mul_one]
    congr 2
    exact (eK.symm_apply_apply _).symm
  change xRationalVolume = exteriorPower.map 3 (stalkRationalDifferentialEquiv z).toLinearMap
    (exteriorPower.ιMulti X19.functionField 3
      ((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X19.functionField))
  have hfun : (⇑(stalkRationalDifferentialEquiv z).toLinearMap ∘
      ⇑((b.unitsSMul (Pi.mulSingle 0 u)).baseChange X19.functionField)) = fun l ↦
        algebraMap (X19.presheaf.stalk z) X19.functionField
            (((Pi.mulSingle 0 u : Fin 3 → (X19.presheaf.stalk z)ˣ) l : (X19.presheaf.stalk z)ˣ) :
            X19.presheaf.stalk z) •
          KaehlerDifferential.D ℤ X19.functionField (eK.symm (xStalkAmbientMap z (s l))) :=
    funext hvec
  rw [exteriorPower.map_apply_ιMulti]
  apply (topExteriorCoefficient_bijective rationalBasis).injective
  rw [topExteriorCoefficient_wedge, hfun, AlternatingMap.map_smul_univ, rationalBasis_det,
    smul_eq_mul, xRationalVolume, map_smul, topExteriorCoefficient_volume, smul_eq_mul, mul_one,
    Fin.prod_univ_three]
  simp only [Pi.mulSingle_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    not_false_eq_true, Pi.mulSingle_eq_of_ne, Units.val_one, map_one, mul_one,
    show (2 : Fin 3) ≠ 0 by decide]
  rw [← hu, map_mul]
  congr 1
  exact eK.symm_apply_apply _


theorem sign_mul_self (i : Fin 5) (m : Fin 3) :
    ((chartSign i * keptSign m : ℤ) : F) * ((chartSign i * keptSign m : ℤ) : F) = 1 := by
  rw [← Int.cast_mul]
  have h : (chartSign i * keptSign m) * (chartSign i * keptSign m) = 1 := by
    fin_cases i <;> fin_cases m <;> rfl
  rw [h, Int.cast_one]

/-- The chart ring of `X`, as the atlas sees it. -/
abbrev AR (i : Fin 5) : Subalgebra k F := atlas.ring (ix i)

theorem AR_le_PChart (i : Fin 5) (m : Fin 3) : AR i ≤ PChart i m := chartRing_le_PChart i m

/-- The partial `∂h/∂X_{m+1}` as an element of the chart ring. -/
def arPartial (i : Fin 5) (m : Fin 3) : AR i := ⟨partialVal i m.succ, partialVal_mem i _⟩

theorem AR_isLocalization (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    letI := inclusionAlgebra (AR_le_PChart i m)
    IsLocalization.Away (arPartial i m) (PChart i m) :=
  subalgebra_isLocalizationAway (AR i) (PChart i m) (AR_le_PChart i m) _ ha
    (inv_mem_PChart i m) le_rfl

theorem exists_arPartial_not_mem (i : Fin 5) (𝔭 : Ideal (AR i)) [h𝔭 : 𝔭.IsPrime] :
    ∃ m : Fin 3, arPartial i m ∉ 𝔭 :=
  @exists_partial_not_mem i 𝔭 h𝔭

theorem val_algebraMap_inclusion {A B : Subalgebra k F} (h : A ≤ B) (a : A) :
    letI := inclusionAlgebra h
    B.val.toRingHom (algebraMap A B a) = (a : F) := rfl

theorem ambient_chartLocalization (i : Fin 5) (p : PrimeSpectrum (AR i)) (a : AR i) :
    xStalkAmbientMap _ (atlas.chartLocalizationEquivAt (ix i) p _ rfl
      (algebraMap (AR i) (Localization.AtPrime p.asIdeal) a)) = (a : F) :=
  (congrArg (xStalkAmbientMap _)
    (atlas.chartLocalizationEquivAt_algebraMap (ix i) p _ rfl a)).trans
      (chartToStalk_ambient i p _ rfl a)

/-- Stalk coordinates at a point of a good principal open, compatible with `F`. -/
theorem stalk_coordinates (i : Fin 5) (p : PrimeSpectrum (AR i)) (m : Fin 3)
    (ha : partialVal i m.succ ≠ 0) (hm : arPartial i m ∉ p.asIdeal) :
    ∃ (f : PChart i m →+* X19.presheaf.stalk (atlas.chartInclusion (ix i) p))
      (b : Basis (Fin 3) (X19.presheaf.stalk (atlas.chartInclusion (ix i) p))
        (AbsoluteStalkDifferentials X19 (atlas.chartInclusion (ix i) p))),
      (∀ l, b l = KaehlerDifferential.D ℤ _ (f (zloc i m (kept m l)))) ∧
        ∀ a, xStalkAmbientMap _ (f a) = (a : F) := by
  let := inclusionAlgebra (AR_le_PChart i m)
  have := AR_isLocalization i m ha
  have hA (a : AR i) : xStalkAmbientMap _ (atlas.chartLocalizationEquivAt (ix i) p _ rfl
      (algebraMap (AR i) (Localization.AtPrime p.asIdeal) a)) =
        (PChart i m).val.toRingHom (algebraMap (AR i) (PChart i m) a) := by
    rw [ambient_chartLocalization, val_algebraMap_inclusion]
  exact differentialCoordinatesAtPrime_transport
    (A := AR i) (B := PChart i m) (R := X19.presheaf.stalk (atlas.chartInclusion (ix i) p))
    (F := F) (ι := Fin 3) (arPartial i m) p hm
    (localBasisZ i m ha) (fun l ↦ zloc i m (kept m l)) (localBasisZ_apply i m ha)
    (atlas.chartLocalizationEquivAt (ix i) p _ rfl) (xStalkAmbientMap _) (PChart i m).val.toRingHom
    hA

/-- The rational volume generates the absolute differential lattice at every point of a chart. -/
theorem generates_at_chart (i : Fin 5) (p : PrimeSpectrum (AR i)) :
    GeneratesStalkDifferentialLattice (atlas.chartInclusion (ix i) p) xRationalVolume := by
  obtain ⟨m, hm⟩ := exists_arPartial_not_mem i p.asIdeal
  have ha : partialVal i m.succ ≠ 0 := fun h0 ↦ hm (by
    rw [show arPartial i m = 0 from Subtype.ext h0]
    exact zero_mem _)
  obtain ⟨f, b, hb, hf⟩ := stalk_coordinates i p m ha hm
  let ε : ℤ := -(chartSign i * keptSign m)
  have hε : (ε : F) * ε = 1 := by
    simp only [ε, Int.cast_neg, neg_mul_neg]
    exact sign_mul_self i m
  have hεmem (w : F) (hw : w ∈ PChart i m) : (ε : F) * w ∈ PChart i m :=
    Subalgebra.mul_mem _ (intCast_mem _ ε) hw
  let u₀ : PChart i m := ⟨ε * (partialVal i m.succ)⁻¹, hεmem _ (inv_mem_PChart i m)⟩
  let v₀ : PChart i m :=
    ⟨ε * partialVal i m.succ, hεmem _ (chartRing_le_PChart i m (partialVal_mem i _))⟩
  have huv : u₀ * v₀ = 1 := Subtype.ext (by
    change (ε : F) * (partialVal i m.succ)⁻¹ * (ε * partialVal i m.succ) = 1
    rw [show (ε : F) * (partialVal i m.succ)⁻¹ * (ε * partialVal i m.succ) =
      (ε * ε) * ((partialVal i m.succ)⁻¹ * partialVal i m.succ) by ring, inv_mul_cancel₀ ha,
      mul_one, hε])
  refine generates_of_coordinates _ (fun l ↦ f (zloc i m (kept m l))) b hb
    (Units.map f.toMonoidHom (Units.mkOfMulEqOne u₀ v₀ huv)) ?_
  simp only [Units.coe_map, Units.val_mkOfMulEqOne, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, hf]
  change (ε * (partialVal i m.succ)⁻¹ : F) * (fieldBasisZ 0).det
    (fun l ↦ KaehlerDifferential.D ℤ F (chartVals i (kept m l))) = (2 * y)⁻¹
  rw [det_zero_kept]
  have hs := sign_mul_self i m
  have hP : (partialVal i m.succ)⁻¹ * partialVal i m.succ = 1 := inv_mul_cancel₀ ha
  simp only [ε]
  push_cast at hs ⊢
  linear_combination ((chartSign i : F) * keptSign m) ^ 2 * (2 * y)⁻¹ * hP + (2 * y)⁻¹ * hs

/-- The rational volume generates the absolute differential lattice at every point. -/
theorem xRationalVolume_generates (z : X19) :
    GeneratesStalkDifferentialLattice z xRationalVolume := by
  obtain ⟨i, p, rfl⟩ := atlas.chartInclusion_cover z
  exact generates_at_chart i p

/-! ## Frames of the top exterior power -/

/-- On a good principal open, the third exterior power of the differentials is free of rank one. -/
def topFrame (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0)
    [IsOpenImmersion (pchartMap i m)] :
    structureSheafModule (Spec (CommRingCat.of (PChart i m))) ≅
      (nativeExteriorModule X19 (nativeAbsoluteDifferentialModule X19) 3).restrict
        (pchartMap i m) :=
  (nativeFiniteFreeTopExteriorIso (Spec (CommRingCat.of (PChart i m))) 3).symm ≪≫
    (nativeExteriorFunctor (Spec (CommRingCat.of (PChart i m))) 3).mapIso
      (affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of (PChart i m))
        (pchartMap i m) (localBasisZ i m ha)) ≪≫
        nativeExteriorRestrictionIso (pchartMap i m) (nativeAbsoluteDifferentialModule X19) 3

theorem xTopFrames (z : X19) : Nonempty (nativeAbsoluteExteriorStalkFrameType X19 3 z) := by
  obtain ⟨i, m, ha, q, rfl⟩ := exists_pchart z
  have := pchartMap_isOpenImmersion i m ha
  exact ⟨openImmersionStalkFrameEquiv (pchartMap i m) q _ (topFrame i m ha)⟩

/-- The rational volume `dc ∧ dt ∧ dx / (2y)` trivializes the third exterior power of the
absolute differentials of `X`. -/
def xVolumeIso : structureSheafModule X19 ≅
    nativeExteriorModule X19 (nativeAbsoluteDifferentialModule X19) 3 :=
  nativeAbsoluteExteriorVolumeIso X19 3 xRationalVolume
    (GeneratesStalkDifferentialLattice.ne_zero _ (xRationalVolume_generates (genericPoint X19)))
    xRationalVolume_generates (fun z ↦ Classical.choose (xRationalVolume_generates z)) xTopFrames

end
end Geonormal

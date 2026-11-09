import Geonormal.P11.Regular
import Red61.AlgebraicGeometry.Differentials.Stalks

/-! # Differentials of the charts `A`, `B`, `D`

`Ω_{L/𝔽₁₁}` is free on `da, db, dσ`. On the principal open of chart `A`, `B` or `D` where the
partial `∂h/∂X_m` of the chart equation is a unit, the differentials of the other three ambient
coordinates form a basis of the differentials: they span by the chain rule, and they are
independent because their determinant in `L` is `±∂h/∂X_m`.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial Module

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-! ## The function field -/

/-- `Ω_{L/𝔽₁₁}` is free on `da, db, dσ`. -/
def fieldBasis : Basis (Fin 3) L (KaehlerDifferential F₁₁ L) :=
  polynomialLocalizationDifferentialBasis F₁₁ L (Fin 3) (nonZeroDivisors P₃)

theorem fieldBasis_apply (j : Fin 3) :
    fieldBasis j = KaehlerDifferential.D F₁₁ L (algebraMap P₃ L (X j)) :=
  polynomialLocalizationDifferentialBasis_apply _ _ _ _ j

/-- The same basis of the absolute differentials. -/
def fieldBasisZ : Basis (Fin 3) L (KaehlerDifferential ℤ L) :=
  fieldBasis.map (quotientBaseDifferentialEquiv ℤ F₁₁ L ZMod.intCast_surjective).symm

theorem fieldBasisZ_apply (j : Fin 3) :
    fieldBasisZ j = KaehlerDifferential.D ℤ L (algebraMap P₃ L (X j)) := by
  rw [fieldBasisZ, Basis.map_apply, fieldBasis_apply, quotientBaseDifferentialEquiv_symm_D]

/-- The partial derivatives `∂/∂a, ∂/∂b, ∂/∂σ` on `L`. -/
def pd (j : Fin 3) : Derivation F₁₁ L L :=
  (fieldBasis.coord j).compDer (KaehlerDifferential.D F₁₁ L)

theorem pd_apply (j : Fin 3) (z : L) :
    pd j z = fieldBasis.repr (KaehlerDifferential.D F₁₁ L z) j := rfl

theorem pd_X (j l : Fin 3) : pd j (algebraMap P₃ L (X l)) = if l = j then 1 else 0 := by
  rw [pd_apply, ← fieldBasis_apply, Basis.repr_self, Finsupp.single_apply]

@[simp] theorem pd_two (j : Fin 3) : pd j 2 = 0 := by
  simpa using (pd j).map_natCast 2

@[simp] theorem pd0a : pd 0 aL = 1 := by rw [aL, pd_X]; rfl
@[simp] theorem pd1a : pd 1 aL = 0 := by rw [aL, pd_X]; rfl
@[simp] theorem pd2a : pd 2 aL = 0 := by rw [aL, pd_X]; rfl
@[simp] theorem pd0b : pd 0 bL = 0 := by rw [bL, pd_X]; rfl
@[simp] theorem pd1b : pd 1 bL = 1 := by rw [bL, pd_X]; rfl
@[simp] theorem pd2b : pd 2 bL = 0 := by rw [bL, pd_X]; rfl
@[simp] theorem pd0s : pd 0 σL = 0 := by rw [σL, pd_X]; rfl
@[simp] theorem pd1s : pd 1 σL = 0 := by rw [σL, pd_X]; rfl
@[simp] theorem pd2s : pd 2 σL = 1 := by rw [σL, pd_X]; rfl

theorem fieldDet_eq (f : Fin 3 → L) :
    fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (f l)) =
      Matrix.det (Matrix.of fun i l ↦ pd i (f l)) := by
  rw [Basis.det_apply]
  rfl

/-- A derivation on `L` is determined by its values on `a, b, σ`. -/
theorem derivation_ext_L {M : Type*} [AddCommGroup M] [Module L M] [Module F₁₁ M]
    [IsScalarTower F₁₁ L M] {D₁ D₂ : Derivation F₁₁ L M}
    (h : ∀ j : Fin 3, D₁ (algebraMap P₃ L (X j)) = D₂ (algebraMap P₃ L (X j))) : D₁ = D₂ := by
  have hlift : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential :=
    fieldBasis.ext fun j ↦ by
      rw [fieldBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D, h j]
  ext x
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x, ← Derivation.liftKaehlerDifferential_comp_D D₂ x,
    hlift]

/-- Elements of a subalgebra whose differentials have nonzero determinant in `L` have
independent differentials. -/
theorem D_linearIndependent (R : Subalgebra k L) (s : Fin 3 → R)
    (hdet : fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (s l : L)) ≠ 0) :
    LinearIndependent R (fun l ↦ KaehlerDifferential.D F₁₁ R (s l)) := by
  have hL : LinearIndependent L (fun l ↦ KaehlerDifferential.D F₁₁ L (s l : L)) :=
    ((Basis.is_basis_iff_det fieldBasis).mpr (Ne.isUnit hdet)).1
  rw [Fintype.linearIndependent_iff] at hL ⊢
  intro g hg
  have hmap := congrArg (KaehlerDifferential.map F₁₁ F₁₁ R L) hg
  simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, map_zero] at hmap
  have h0 := hL (fun l ↦ (g l : L)) (by
    rw [← hmap]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    exact algebraMap_smul L (g l) _)
  intro l
  exact Subtype.ext (h0 l)

/-! ## Bases on the principal opens of the charts `A`, `B`, `D` -/

/-- `∂h/∂X_j` on chart `i`, as an element of `L`. -/
def partialVal (i : Fin 3) (j : Fin 4) : L := chartEval i (pderiv j (hPoly i))

theorem partialVal_mem (i : Fin 3) (j : Fin 4) : partialVal i j ∈ chartRing i.castSucc :=
  chartEval_mem i _

/-- The principal open of chart `i` on which `∂h/∂X_m` is a unit, inside `L`. -/
def PChart (i : Fin 3) (m : Fin 4) : Subalgebra k L :=
  chartRing i.castSucc ⊔ Algebra.adjoin k {(partialVal i m)⁻¹}

theorem chartRing_le_PChart (i : Fin 3) (m : Fin 4) : chartRing i.castSucc ≤ PChart i m :=
  le_sup_left

theorem inv_mem_PChart (i : Fin 3) (m : Fin 4) : (partialVal i m)⁻¹ ∈ PChart i m :=
  le_sup_right (a := chartRing i.castSucc) (Algebra.subset_adjoin (Set.mem_singleton _))

/-- The coordinates kept on the principal open where `∂h/∂X_m` is a unit. -/
def kept : Fin 4 → Fin 3 → Fin 4 := ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem kept_cover (m : Fin 4) (l : Fin 4) (h : l ≠ m) : ∃ n, kept m n = l := by
  revert m l
  decide

/-- The chart coordinates on the principal open. -/
def zloc (i : Fin 3) (m : Fin 4) (l : Fin 4) : PChart i m :=
  ⟨chartVals i l, chartRing_le_PChart i m (chartVals_mem i l)⟩

theorem coe_aeval_zloc (i : Fin 3) (m : Fin 4) (p : P₄) :
    ((aeval (zloc i m) p : PChart i m) : L) = chartEval i p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, chartEval, aeval_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, Subalgebra.coe_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, Subalgebra.coe_mul, hp, aeval_X, chartEval, aeval_X]
    rfl

/-- Span of the kept differentials. -/
abbrev keptSpan (i : Fin 3) (m : Fin 4) :
    Submodule (PChart i m) (KaehlerDifferential F₁₁ (PChart i m)) :=
  Submodule.span (PChart i m)
    (Set.range fun l : Fin 3 ↦ KaehlerDifferential.D F₁₁ (PChart i m) (zloc i m (kept m l)))

theorem hPoly_zloc (i : Fin 3) (m : Fin 4) : aeval (zloc i m) (hPoly i) = 0 :=
  Subtype.ext (by rw [coe_aeval_zloc, chartEval_hPoly]; rfl)

theorem partialVal_isUnit (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    IsUnit (aeval (zloc i m) (pderiv m (hPoly i))) := by
  refine IsUnit.of_mul_eq_one (⟨(partialVal i m)⁻¹, inv_mem_PChart i m⟩ : PChart i m)
    (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, coe_aeval_zloc]
  exact mul_inv_cancel₀ ha

theorem D_zloc_mem (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) (l : Fin 4) :
    KaehlerDifferential.D F₁₁ (PChart i m) (zloc i m l) ∈ keptSpan i m := by
  have hkept (l : Fin 4) (h : l ≠ m) :
      KaehlerDifferential.D F₁₁ (PChart i m) (zloc i m l) ∈ keptSpan i m := by
    obtain ⟨n, rfl⟩ := kept_cover m l h
    exact Submodule.subset_span ⟨n, rfl⟩
  rcases eq_or_ne l m with rfl | h
  · let f : Fin 4 → KaehlerDifferential F₁₁ (PChart i l) := fun j ↦
      aeval (zloc i l) (pderiv j (hPoly i)) • KaehlerDifferential.D F₁₁ (PChart i l) (zloc i l j)
    have hrel : ∑ j, f j = 0 :=
      (SurfaceLib.derivation_aeval (KaehlerDifferential.D F₁₁ (PChart i l)) (zloc i l)
        (hPoly i)).symm.trans (by rw [hPoly_zloc, map_zero])
    have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ l)
    rw [hrel] at h1
    have hrest : ∑ j ∈ Finset.univ.erase l, f j ∈ keptSpan i l :=
      Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ (hkept j (Finset.ne_of_mem_erase hj))
    have hf : f l ∈ keptSpan i l := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact Submodule.neg_mem _ hrest
    obtain ⟨u, hu⟩ := partialVal_isUnit i l ha
    have he : KaehlerDifferential.D F₁₁ (PChart i l) (zloc i l l) = (↑u⁻¹ : PChart i l) • f l := by
      change _ = (↑u⁻¹ : PChart i l) • (aeval (zloc i l) (pderiv l (hPoly i)) • _)
      rw [← hu]
      exact (inv_smul_smul u (KaehlerDifferential.D F₁₁ (PChart i l) (zloc i l l))).symm
    rw [he]
    exact Submodule.smul_mem _ _ hf
  · exact hkept l h

theorem D_aeval_mem (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) (p : P₄) :
    KaehlerDifferential.D F₁₁ (PChart i m) (aeval (zloc i m) p) ∈ keptSpan i m := by
  rw [SurfaceLib.derivation_aeval]
  exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (D_zloc_mem i m ha l)

theorem D_mem_of_mul (i : Fin 3) (m : Fin 4) {r v w : PChart i m} (hv : IsUnit v)
    (he : v * r = w) (hw : KaehlerDifferential.D F₁₁ (PChart i m) w ∈ keptSpan i m)
    (hdv : KaehlerDifferential.D F₁₁ (PChart i m) v ∈ keptSpan i m) :
    KaehlerDifferential.D F₁₁ (PChart i m) r ∈ keptSpan i m := by
  obtain ⟨u, rfl⟩ := hv
  have hD := congrArg (KaehlerDifferential.D F₁₁ (PChart i m)) he
  rw [Derivation.leibniz] at hD
  have hr : KaehlerDifferential.D F₁₁ (PChart i m) r =
      u⁻¹ • (KaehlerDifferential.D F₁₁ (PChart i m) w -
        r • KaehlerDifferential.D F₁₁ (PChart i m) (u : PChart i m)) := by
    rw [← hD, add_sub_cancel_right]
    exact (inv_smul_smul u (KaehlerDifferential.D F₁₁ (PChart i m) r)).symm
  rw [hr]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hdv))

theorem cPoly_zloc (i : Fin 3) (m : Fin 4) (q : P₁) :
    ((aeval (zloc i m) (cPoly i q) : PChart i m) : L) = algebraMap k L (algebraMap P₁ k q) := by
  rw [coe_aeval_zloc, chartEval_cPoly]

theorem D_chartRing_mem (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) (x : L)
    (hx : x ∈ chartRing i.castSucc) :
    KaehlerDifferential.D F₁₁ (PChart i m) ⟨x, chartRing_le_PChart i m hx⟩ ∈ keptSpan i m := by
  obtain ⟨p, q, hq, hpq⟩ := chartRing_frac i x hx
  have hq0 : algebraMap k L (algebraMap P₁ k q) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k L).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective P₁ k)).mpr hq)
  apply D_mem_of_mul i m (v := aeval (zloc i m) (cPoly i q)) (w := aeval (zloc i m) p)
  · refine IsUnit.of_mul_eq_one (⟨(algebraMap k L (algebraMap P₁ k q))⁻¹,
      by rw [← map_inv₀]; exact (PChart i m).algebraMap_mem _⟩ : PChart i m) (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, cPoly_zloc]
    exact mul_inv_cancel₀ hq0
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, cPoly_zloc, coe_aeval_zloc]
    exact hpq
  · exact D_aeval_mem i m ha p
  · exact D_aeval_mem i m ha _

/-- The element `∂h/∂X_m` of the principal open. -/
def dPC (i : Fin 3) (m : Fin 4) : PChart i m :=
  ⟨partialVal i m, chartRing_le_PChart i m (partialVal_mem i _)⟩

theorem dPC_isUnit (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) : IsUnit (dPC i m) :=
  IsUnit.of_mul_eq_one (⟨(partialVal i m)⁻¹, inv_mem_PChart i m⟩ : PChart i m)
    (Subtype.ext (mul_inv_cancel₀ ha))

theorem keptSpan_top (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    ⊤ ≤ keptSpan i m := by
  rw [← KaehlerDifferential.span_range_derivation F₁₁ (PChart i m), Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  have hden := adjoin_inverse_denominators (chartRing i.castSucc)
    ⟨partialVal i m, partialVal_mem i _⟩ ha
  obtain ⟨n, hn⟩ := hden r.property
  have hdn : KaehlerDifferential.D F₁₁ (PChart i m) (dPC i m ^ n) ∈ keptSpan i m := by
    rw [Derivation.leibniz_pow]
    exact nsmul_mem (Submodule.smul_mem _ _ (D_chartRing_mem i m ha _ (partialVal_mem i _))) n
  have hw := D_chartRing_mem i m ha _ hn
  refine D_mem_of_mul i m ((dPC_isUnit i m ha).pow n) ?_ hw hdn
  exact Subtype.ext (by
    change (partialVal i m) ^ n * (r : L) = (r : L) * partialVal i m ^ n
    ring)

/-! ### Independence, through the function field -/

/-- The sign in `det(kept coordinates) = ±∂h/∂X_m`. -/
def keptSign : Fin 3 → Fin 4 → L := ![![1, 1, 1, 1], ![1, -1, 1, 1], ![-1, 1, -1, 1]]

theorem partialVal_eq_zero (i : Fin 3) (m : Fin 4)
    (h : (i = 0 ∧ m ≠ 0) ∨ (i = 1 ∧ m = 3) ∨ (i = 2 ∧ (m = 1 ∨ m = 3))) : partialVal i m = 0 := by
  fin_cases i <;> fin_cases m <;> simp at h <;>
    simp [partialVal, hPoly, pderiv_X, chartEval, map_ofNat, h11L]

theorem det_kept (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (chartVals i (kept m l))) =
      keptSign i m * partialVal i m := by
  have ha0 := aL_ne_zero
  have hu0 : bL ^ 2 - aL ^ 3 ≠ 0 := uL_ne_zero
  rw [fieldDet_eq, Matrix.det_fin_three]
  fin_cases i <;> fin_cases m
  all_goals first
    | exact absurd (partialVal_eq_zero _ _ (by decide)) ha
    | (simp [kept, keptSign, partialVal, hPoly, pderiv_X, chartEval, coordV, yV, βL, αL, ρL, βD,
        αD, wL, uL, Derivation.leibniz_div, Derivation.leibniz_inv, Derivation.leibniz_pow,
        smul_eq_mul]
       try field_simp
       try ring)

theorem kept_independent (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    LinearIndependent (PChart i m)
      (fun l : Fin 3 ↦ KaehlerDifferential.D F₁₁ (PChart i m) (zloc i m (kept m l))) := by
  apply D_linearIndependent (PChart i m) (fun l ↦ zloc i m (kept m l))
  change fieldBasis.det (fun l ↦ KaehlerDifferential.D F₁₁ L (chartVals i (kept m l))) ≠ 0
  rw [det_kept i m ha]
  refine mul_ne_zero ?_ ha
  fin_cases i <;> fin_cases m <;> simp [keptSign]

/-- On the principal open where `∂h/∂X_m` is a unit, the kept differentials form a basis. -/
def localBasis (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    Basis (Fin 3) (PChart i m) (KaehlerDifferential F₁₁ (PChart i m)) :=
  Basis.mk (kept_independent i m ha) (keptSpan_top i m ha)

/-- The same basis of the absolute differentials. -/
def localBasisZ (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    Basis (Fin 3) (PChart i m) (KaehlerDifferential ℤ (PChart i m)) :=
  (localBasis i m ha).map
    (quotientBaseDifferentialEquiv ℤ F₁₁ (PChart i m) ZMod.intCast_surjective).symm

theorem localBasisZ_apply (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) (l : Fin 3) :
    localBasisZ i m ha l = KaehlerDifferential.D ℤ (PChart i m) (zloc i m (kept m l)) := by
  rw [localBasisZ, Basis.map_apply, localBasis, Basis.mk_apply, quotientBaseDifferentialEquiv_symm_D]

/-! ## The principal opens as open subschemes -/

theorem PChart_isLocalization (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    letI := inclusionAlgebra (chartRing_le_PChart i m)
    IsLocalization.Away (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc) (PChart i m) :=
  subalgebra_isLocalizationAway (chartRing i.castSucc) (PChart i m) (chartRing_le_PChart i m) _ ha
    (inv_mem_PChart i m) le_rfl

/-- The inclusion of the principal open into its chart. -/
def pchartIncl (i : Fin 3) (m : Fin 4) :
    Spec (CommRingCat.of (PChart i m)) ⟶ Spec (CommRingCat.of (chartRing i.castSucc)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (chartRing_le_PChart i m)).toRingHom)

/-- The principal open as an open subscheme of `X`. -/
def pchartMap (i : Fin 3) (m : Fin 4) : Spec (CommRingCat.of (PChart i m)) ⟶ X11 :=
  pchartIncl i m ≫ atlas.chartInclusion (i.castSucc : Fin 4)

theorem pchartMap_isOpenImmersion (i : Fin 3) (m : Fin 4) (ha : partialVal i m ≠ 0) :
    IsOpenImmersion (pchartMap i m) := by
  let := inclusionAlgebra (chartRing_le_PChart i m)
  have := PChart_isLocalization i m ha
  have h1 : IsOpenImmersion (pchartIncl i m) :=
    IsOpenImmersion.of_isLocalization (R := chartRing i.castSucc) (S := PChart i m)
      (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc)
  exact @IsOpenImmersion.comp _ _ _ (pchartIncl i m) (atlas.chartInclusion (i.castSucc : Fin 4)) h1
    (atlas.chartInclusion_open (i.castSucc : Fin 4))

/-- At every point of a chart some partial `∂h/∂X_m` is a unit. -/
theorem exists_partial_not_mem (i : Fin 3) (𝔭 : Ideal (chartRing i.castSucc)) [𝔭.IsPrime] :
    ∃ m : Fin 4, (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc) ∉ 𝔭 := by
  by_contra h
  push Not at h
  have hQ : ∀ j : Fin 4, pderiv j (hPoly i) ∈ 𝔭.comap (chartHom i) := fun j ↦ h j
  have hh : hPoly i ∈ 𝔭.comap (chartHom i) := by
    change chartHom i (hPoly i) ∈ 𝔭
    rw [show chartHom i (hPoly i) = 0 from Subtype.ext (chartEval_hPoly i)]
    exact zero_mem _
  exact (Ideal.IsPrime.ne_top inferInstance)
    ((Ideal.eq_top_iff_one _).mpr (one_mem_of_pderiv i _ hh hQ))

/-- Every point of the charts `A`, `B`, `D` lies on a principal open with a nonzero partial. -/
theorem exists_pchart (i : Fin 3) (p : PrimeSpectrum (atlas.ring (i.castSucc : Fin 4))) :
    ∃ (m : Fin 4) (_ : partialVal i m ≠ 0),
      atlas.chartInclusion (i.castSucc : Fin 4) p ∈ Set.range (pchartMap i m) := by
  obtain ⟨m, hm⟩ := @exists_partial_not_mem i p.asIdeal p.isPrime
  have ha : partialVal i m ≠ 0 := fun h0 ↦ hm (by
    rw [show (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc) = 0 from Subtype.ext h0]
    exact zero_mem _)
  refine ⟨m, ha, ?_⟩
  let := inclusionAlgebra (chartRing_le_PChart i m)
  have := PChart_isLocalization i m ha
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap (chartRing i.castSucc) (PChart i m))) := by
    rw [PrimeSpectrum.localization_away_comap_range (PChart i m)
      (⟨partialVal i m, partialVal_mem i _⟩ : chartRing i.castSucc)]
    exact hm
  obtain ⟨z, rfl⟩ := hq
  exact ⟨z, rfl⟩

end
end Geonormal.P11

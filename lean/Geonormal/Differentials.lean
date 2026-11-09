import Geonormal.NotSmooth
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Red61.AlgebraicGeometry.Differentials.Stalks

/-! # Differentials of the characteristic-19 surface

On every chart the coordinates `c, e₁, e₂` give a basis of the absolute differentials of the
function field, because `E = F₁₉(c, e₁, e₂)` and `F/E` is separable. On the principal open of a
chart where `∂h/∂z_j` is a unit, the differentials of the other three chart coordinates form a
basis of the absolute differentials: they span by the chain rule, and they are independent
because their images in the function field have nonzero determinant.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial Module

noncomputable section

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

/-! ## The function field -/

/-- `F₁₉[c, e₁, e₂] → E` on chart `i`. -/
def chartPolyE (i : Fin 5) : MvPolynomial (Fin 3) F₁₉ →ₐ[F₁₉] E := aeval (coordE i)

theorem chartPolyE_ratio (i : Fin 5) (z : E) :
    ∃ a b, chartPolyE i b ≠ 0 ∧ z * chartPolyE i b = chartPolyE i a := by
  have hz : z ∈ IntermediateField.adjoin F₁₉ (Set.range (coordE i)) := by
    rw [chart_generation]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hz
  obtain ⟨r, hr, s, hs, rfl⟩ := hz
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := hs
  by_cases hb : (aeval (coordE i)) b = 0
  · exact ⟨0, 1, by simp, by simp [hb]⟩
  · exact ⟨a, b, hb, div_mul_cancel₀ _ hb⟩

/-- The coordinate subalgebra `F₁₉[c, e₁, e₂]` of `E` on chart `i`. -/
abbrev coordSubalg (i : Fin 5) : Subalgebra F₁₉ E := Algebra.adjoin F₁₉ (Set.range (coordE i))

def coordEquiv (i : Fin 5) : MvPolynomial (Fin 3) F₁₉ ≃ₐ[F₁₉] coordSubalg i :=
  (coordE_independent i).aevalEquiv

instance coordSubalg_isFractionRing (i : Fin 5) : IsFractionRing (coordSubalg i) E := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, he⟩ := chartPolyE_ratio i z
  refine ⟨coordEquiv i a, coordEquiv i b, ?_⟩
  show z = chartPolyE i a / chartPolyE i b
  rw [eq_div_iff hb]
  exact he

/-- `dc, de₁, de₂` on the coordinate subalgebra. -/
def coordBasis (i : Fin 5) :
    Basis (Fin 3) (coordSubalg i) (KaehlerDifferential F₁₉ (coordSubalg i)) :=
  differentialBasisOfRingEquiv F₁₉ (coordEquiv i).toRingEquiv
    (RingHom.ext fun r ↦ (coordEquiv i).commutes r) (KaehlerDifferential.mvPolynomialBasis F₁₉ (Fin 3))

theorem derivation_aeval_mem_span {A M : Type*} [CommRing A] [Algebra F₁₉ A] [AddCommGroup M]
    [Module A M] [Module F₁₉ M] (δ : Derivation F₁₉ A M) {σ : Type*} [Fintype σ] [DecidableEq σ]
    (x : σ → A) (p : MvPolynomial σ F₁₉) :
    δ (aeval x p) ∈ Submodule.span A (Set.range fun l ↦ δ (x l)) := by
  rw [SurfaceLib.derivation_aeval]
  exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem finrank_E : Module.finrank E (KaehlerDifferential F₁₉ E) = 3 := by
  rw [Module.finrank_eq_card_basis
    (differentialBasisOfLocalization F₁₉ (coordSubalg 0) E (Fin 3) (nonZeroDivisors _) (coordBasis 0))]
  rfl

theorem span_E (i : Fin 5) :
    ⊤ ≤ Submodule.span E (Set.range fun l ↦ KaehlerDifferential.D F₁₉ E (coordE i l)) := by
  rw [← KaehlerDifferential.span_range_derivation F₁₉ E, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨a, b, hb, he⟩ := chartPolyE_ratio i z
  have hD := congrArg (KaehlerDifferential.D F₁₉ E) he
  rw [Derivation.leibniz] at hD
  have hz : KaehlerDifferential.D F₁₉ E z = (chartPolyE i b)⁻¹ •
      (KaehlerDifferential.D F₁₉ E (chartPolyE i a) - z • KaehlerDifferential.D F₁₉ E (chartPolyE i b)) := by
    rw [← hD, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (derivation_aeval_mem_span _ _ _)
    (Submodule.smul_mem _ _ (derivation_aeval_mem_span _ _ _)))

/-- On each chart, `dc, de₁, de₂` form a basis of `Ω_{E/F₁₉}`. -/
def fieldBasisE (i : Fin 5) : Basis (Fin 3) E (KaehlerDifferential F₁₉ E) :=
  basisOfTopLeSpanOfCardEqFinrank _ (span_E i) (by rw [finrank_E]; rfl)

/-! ## `F/E` is separable -/

theorem two_ne_zero_E : (2 : E) ≠ 0 := by
  have h : (2 : E) = algebraMap F₁₉ E 2 := (map_ofNat (algebraMap F₁₉ E) 2).symm
  rw [h, map_ne_zero_iff _ (algebraMap F₁₉ E).injective]
  decide

theorem gE_ne_zero : gE ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R₂ E)).mpr gPoly_ne_zero

theorem quad_separable : quad.Separable := by
  have h2 := two_ne_zero_E
  have hg := gE_ne_zero
  refine ⟨-Polynomial.C gE⁻¹, Polynomial.C (2 * gE)⁻¹ * Polynomial.X, ?_⟩
  have e1 : Polynomial.C gE⁻¹ * Polynomial.C gE = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hg, map_one]
  have e2 : Polynomial.C (2 * gE)⁻¹ * Polynomial.C 2 = Polynomial.C gE⁻¹ := by
    rw [← map_mul]
    congr 1
    field_simp
  simp only [quad, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  linear_combination e1 + Polynomial.X ^ 2 * e2


theorem y_separable : IsSeparable E y := by
  have hmin : quad = minpoly E y := minpoly.eq_of_irreducible_of_monic quad_irreducible
    (by
      show Polynomial.aeval (AdjoinRoot.root quad) quad = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) quad_monic
  rw [IsSeparable, ← hmin]
  exact quad_separable

instance : Algebra.IsSeparable E F := by
  have : Algebra.IsSeparable E (IntermediateField.adjoin E {y}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable E F).mpr y_separable
  have htop : IntermediateField.adjoin E {y} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra E {y} (AdjoinRoot.adjoinRoot_eq_top)
  exact ⟨fun z ↦ IntermediateField.isSeparable_of_mem_isSeparable E F
    (L := IntermediateField.adjoin E {y}) (by rw [htop]; trivial)⟩

instance : Algebra.FormallyEtale E F := Algebra.FormallyEtale.of_isSeparable E F

theorem finrank_F : Module.finrank F (KaehlerDifferential F₁₉ F) = 3 := by
  rw [Module.finrank_eq_card_basis (differentialBasisOfFormallyEtale F₁₉ E F (Fin 3) (fieldBasisE 0))]
  rfl

/-- The chart coordinates `c, e₁, e₂` in `F`. -/
abbrev coordF (i : Fin 5) (l : Fin 3) : F := algebraMap E F (coordE i l)

theorem D_mem_span_of_ratio (i : Fin 5) {z : F} {a b : MvPolynomial (Fin 3) F₁₉}
    (hb : aeval (coordF i) b ≠ 0) (he : z * aeval (coordF i) b = aeval (coordF i) a) :
    KaehlerDifferential.D F₁₉ F z ∈
      Submodule.span F (Set.range fun l ↦ KaehlerDifferential.D F₁₉ F (coordF i l)) := by
  have hD := congrArg (KaehlerDifferential.D F₁₉ F) he
  rw [Derivation.leibniz] at hD
  have hz : KaehlerDifferential.D F₁₉ F z = (aeval (coordF i) b)⁻¹ •
      (KaehlerDifferential.D F₁₉ F (aeval (coordF i) a) -
        z • KaehlerDifferential.D F₁₉ F (aeval (coordF i) b)) := by
    rw [← hD, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (derivation_aeval_mem_span _ _ _)
    (Submodule.smul_mem _ _ (derivation_aeval_mem_span _ _ _)))

theorem aeval_coordF (i : Fin 5) (p : MvPolynomial (Fin 3) F₁₉) :
    aeval (coordF i) p = algebraMap E F (aeval (coordE i) p) :=
  MvPolynomial.aeval_algebraMap_apply F (coordE i) p

theorem D_algebraMap_mem_span (i : Fin 5) (α : E) :
    KaehlerDifferential.D F₁₉ F (algebraMap E F α) ∈
      Submodule.span F (Set.range fun l ↦ KaehlerDifferential.D F₁₉ F (coordF i l)) := by
  obtain ⟨a, b, hb, he⟩ := chartPolyE_ratio i α
  apply D_mem_span_of_ratio i (a := a) (b := b)
  · rw [aeval_coordF]
    exact (map_ne_zero_iff _ (algebraMap E F).injective).mpr hb
  · rw [aeval_coordF, aeval_coordF, ← map_mul]
    exact congrArg _ he

theorem y_ne_zero : y ≠ 0 := by
  intro h
  have h2 : algebraMap E F gE = 0 := by rw [algebraMap_gE, ← y_sq, h, zero_pow two_ne_zero]
  exact gE_ne_zero ((map_eq_zero_iff _ (algebraMap E F).injective).mp h2)

theorem yc_ne_zero (i : Fin 5) : yc i ≠ 0 := mul_ne_zero y_ne_zero (monoF_ne_zero _)

theorem span_F (i : Fin 5) :
    ⊤ ≤ Submodule.span F (Set.range fun l ↦ KaehlerDifferential.D F₁₉ F (coordF i l)) := by
  set S := Submodule.span F (Set.range fun l ↦ KaehlerDifferential.D F₁₉ F (coordF i l))
  have hyc : KaehlerDifferential.D F₁₉ F (yc i) ∈ S := by
    have h2 : (2 : F) * yc i ≠ 0 := mul_ne_zero two_ne_zero_F (yc_ne_zero i)
    have hsq : KaehlerDifferential.D F₁₉ F (yc i ^ 2) ∈ S := by
      rw [yc_sq_eq i, coeffEval_eq, ← aeval_coordF]
      exact derivation_aeval_mem_span _ _ _
    have he : KaehlerDifferential.D F₁₉ F (yc i) =
        ((2 : F) * yc i)⁻¹ • KaehlerDifferential.D F₁₉ F (yc i ^ 2) := by
      rw [pow_two, Derivation.leibniz, ← two_smul F (yc i • _), smul_smul, smul_smul,
        mul_assoc, inv_mul_cancel₀ h2, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hsq
  have hy : KaehlerDifferential.D F₁₉ F y ∈ S := by
    have hm : algebraMap E F (monoE (yScale i)) ≠ 0 := monoF_ne_zero _
    have hyy : y = yc i * algebraMap E F (monoE (yScale i))⁻¹ := by
      rw [yc, monoF, map_inv₀, mul_assoc, mul_inv_cancel₀ hm, mul_one]
    rw [hyy, Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (D_algebraMap_mem_span i _))
      (Submodule.smul_mem _ _ hyc)
  rw [← KaehlerDifferential.span_range_derivation F₁₉ F, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨α, β, rfl⟩ := F_decomp z
  rw [map_add, Derivation.leibniz]
  exact Submodule.add_mem _ (D_algebraMap_mem_span i α) (Submodule.add_mem _
    (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ (D_algebraMap_mem_span i β)))

/-- On each chart, `dc, de₁, de₂` form a basis of `Ω_{F/F₁₉}`. -/
def fieldBasisF (i : Fin 5) : Basis (Fin 3) F (KaehlerDifferential F₁₉ F) :=
  basisOfTopLeSpanOfCardEqFinrank _ (span_F i) (by rw [finrank_F]; rfl)

theorem fieldBasisF_apply (i : Fin 5) (l : Fin 3) :
    fieldBasisF i l = KaehlerDifferential.D F₁₉ F (coordF i l) := by
  simp [fieldBasisF]

/-- The same basis of the absolute differentials `Ω_{F/ℤ}`. -/
def fieldBasisZ (i : Fin 5) : Basis (Fin 3) F (KaehlerDifferential ℤ F) :=
  (fieldBasisF i).map (quotientBaseDifferentialEquiv ℤ F₁₉ F ZMod.intCast_surjective).symm

theorem fieldBasisZ_apply (i : Fin 5) (l : Fin 3) :
    fieldBasisZ i l = KaehlerDifferential.D ℤ F (coordF i l) := by
  rw [fieldBasisZ, Basis.map_apply, fieldBasisF_apply, quotientBaseDifferentialEquiv_symm_D]


/-! ## Bases on the principal opens of the charts -/

/-- `∂h/∂X_j` on chart `i`, as an element of `F`. -/
def partialVal (i : Fin 5) (j : Fin 4) : F := chartEval i (pderiv j (hPoly i))

theorem partialVal_mem (i : Fin 5) (j : Fin 4) : partialVal i j ∈ chartRing i := chartEval_mem i _

/-- The principal open of chart `i` on which `∂h/∂X_{m+1}` is a unit, inside `F`. -/
def PChart (i : Fin 5) (m : Fin 3) : Subalgebra k F :=
  chartRing i ⊔ Algebra.adjoin k {(partialVal i m.succ)⁻¹}

theorem chartRing_le_PChart (i : Fin 5) (m : Fin 3) : chartRing i ≤ PChart i m := le_sup_left

theorem inv_mem_PChart (i : Fin 5) (m : Fin 3) : (partialVal i m.succ)⁻¹ ∈ PChart i m :=
  le_sup_right (a := chartRing i) (Algebra.subset_adjoin (Set.mem_singleton _))

/-- The coordinates kept on the principal open where `∂h/∂X_{m+1}` is a unit. -/
def kept : Fin 3 → Fin 3 → Fin 4 := ![![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem kept_cover (m : Fin 3) (l : Fin 4) (h : l ≠ m.succ) : ∃ n, kept m n = l := by
  revert m l
  decide

/-- The chart coordinates `Y, c, e₁, e₂` on the principal open. -/
def zloc (i : Fin 5) (m : Fin 3) (l : Fin 4) : PChart i m :=
  ⟨chartVals i l, chartRing_le_PChart i m (chartVals_mem i l)⟩

theorem coe_aeval_zloc (i : Fin 5) (m : Fin 3) (p : P₄) :
    ((aeval (zloc i m) p : PChart i m) : F) = chartEval i p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, chartEval, aeval_C]
    rfl
  | add p q hp hq => rw [map_add, map_add, Subalgebra.coe_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, Subalgebra.coe_mul, hp, aeval_X, chartEval, aeval_X]
    rfl

/-- Span of the kept differentials. -/
abbrev keptSpan (i : Fin 5) (m : Fin 3) : Submodule (PChart i m) (KaehlerDifferential F₁₉ (PChart i m)) :=
  Submodule.span (PChart i m)
    (Set.range fun l : Fin 3 ↦ KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m (kept m l)))


theorem hPoly_zloc (i : Fin 5) (m : Fin 3) : aeval (zloc i m) (hPoly i) = 0 :=
  Subtype.ext (by rw [coe_aeval_zloc, chartEval_hPoly]; rfl)

theorem partialVal_isUnit (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    IsUnit (aeval (zloc i m) (pderiv m.succ (hPoly i))) := by
  refine IsUnit.of_mul_eq_one (⟨(partialVal i m.succ)⁻¹, inv_mem_PChart i m⟩ : PChart i m) (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, coe_aeval_zloc]
  exact mul_inv_cancel₀ ha

theorem D_zloc_mem (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) (l : Fin 4) :
    KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m l) ∈ keptSpan i m := by
  have hkept (l : Fin 4) (h : l ≠ m.succ) :
      KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m l) ∈ keptSpan i m := by
    obtain ⟨n, rfl⟩ := kept_cover m l h
    exact Submodule.subset_span ⟨n, rfl⟩
  rcases eq_or_ne l m.succ with rfl | h
  · let f : Fin 4 → KaehlerDifferential F₁₉ (PChart i m) := fun l ↦
      aeval (zloc i m) (pderiv l (hPoly i)) • KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m l)
    have hrel : ∑ l, f l = 0 := (SurfaceLib.derivation_aeval (KaehlerDifferential.D F₁₉ (PChart i m))
      (zloc i m) (hPoly i)).symm.trans (by rw [hPoly_zloc, map_zero])
    have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ m.succ)
    rw [hrel] at h1
    have hrest : ∑ l ∈ Finset.univ.erase m.succ, f l ∈ keptSpan i m :=
      Submodule.sum_mem _ fun l hl ↦ Submodule.smul_mem _ _ (hkept l (Finset.ne_of_mem_erase hl))
    have hf : f m.succ ∈ keptSpan i m := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact Submodule.neg_mem _ hrest
    obtain ⟨u, hu⟩ := partialVal_isUnit i m ha
    have he : KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m m.succ) = (↑u⁻¹ : PChart i m) • f m.succ := by
      change _ = (↑u⁻¹ : PChart i m) • (aeval (zloc i m) (pderiv m.succ (hPoly i)) • _)
      rw [← hu]
      exact (inv_smul_smul u (KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m m.succ))).symm
    rw [he]
    exact Submodule.smul_mem _ _ hf
  · exact hkept l h


theorem D_aeval_mem (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) (p : P₄) :
    KaehlerDifferential.D F₁₉ (PChart i m) (aeval (zloc i m) p) ∈ keptSpan i m := by
  rw [SurfaceLib.derivation_aeval]
  exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (D_zloc_mem i m ha l)

theorem D_mem_of_mul (i : Fin 5) (m : Fin 3) {r v w : PChart i m} (hv : IsUnit v)
    (he : v * r = w) (hw : KaehlerDifferential.D F₁₉ (PChart i m) w ∈ keptSpan i m)
    (hdv : KaehlerDifferential.D F₁₉ (PChart i m) v ∈ keptSpan i m) :
    KaehlerDifferential.D F₁₉ (PChart i m) r ∈ keptSpan i m := by
  obtain ⟨u, rfl⟩ := hv
  have hD := congrArg (KaehlerDifferential.D F₁₉ (PChart i m)) he
  rw [Derivation.leibniz] at hD
  have hr : KaehlerDifferential.D F₁₉ (PChart i m) r =
      u⁻¹ • (KaehlerDifferential.D F₁₉ (PChart i m) w - r • KaehlerDifferential.D F₁₉ (PChart i m) (u : PChart i m)) := by
    rw [← hD, add_sub_cancel_right]
    exact (inv_smul_smul u (KaehlerDifferential.D F₁₉ (PChart i m) r)).symm
  rw [hr]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hdv))

theorem cPoly_zloc (i : Fin 5) (m : Fin 3) (q : P₁) :
    ((aeval (zloc i m) (cPoly q) : PChart i m) : F) = algebraMap k F (algebraMap P₁ k q) := by
  rw [coe_aeval_zloc, chartEval_cPoly]

theorem D_chartRing_mem (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) (x : F)
    (hx : x ∈ chartRing i) :
    KaehlerDifferential.D F₁₉ (PChart i m) ⟨x, chartRing_le_PChart i m hx⟩ ∈ keptSpan i m := by
  obtain ⟨p, q, hq, hpq⟩ := chartRing_frac i x hx
  have hq0 : algebraMap k F (algebraMap P₁ k q) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k F).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective P₁ k)).mpr hq)
  apply D_mem_of_mul i m (v := aeval (zloc i m) (cPoly q)) (w := aeval (zloc i m) p)
  · refine IsUnit.of_mul_eq_one (⟨(algebraMap k F (algebraMap P₁ k q))⁻¹,
      by rw [← map_inv₀]; exact (PChart i m).algebraMap_mem _⟩ : PChart i m) (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, cPoly_zloc]
    exact mul_inv_cancel₀ hq0
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, cPoly_zloc, coe_aeval_zloc]
    exact hpq
  · exact D_aeval_mem i m ha p
  · exact D_aeval_mem i m ha _

/-- The element `∂h/∂X_{m+1}` of the principal open. -/
def dPC (i : Fin 5) (m : Fin 3) : PChart i m :=
  ⟨partialVal i m.succ, chartRing_le_PChart i m (partialVal_mem i _)⟩

theorem dPC_isUnit (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) : IsUnit (dPC i m) :=
  IsUnit.of_mul_eq_one (⟨(partialVal i m.succ)⁻¹, inv_mem_PChart i m⟩ : PChart i m)
    (Subtype.ext (mul_inv_cancel₀ ha))

theorem keptSpan_top (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    ⊤ ≤ keptSpan i m := by
  rw [← KaehlerDifferential.span_range_derivation F₁₉ (PChart i m), Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  have hden := adjoin_inverse_denominators (chartRing i) ⟨partialVal i m.succ, partialVal_mem i _⟩ ha
  obtain ⟨n, hn⟩ := hden r.property
  have hdn : KaehlerDifferential.D F₁₉ (PChart i m) (dPC i m ^ n) ∈ keptSpan i m := by
    rw [Derivation.leibniz_pow]
    exact nsmul_mem (Submodule.smul_mem _ _ (D_chartRing_mem i m ha _ (partialVal_mem i _))) n
  have hw := D_chartRing_mem i m ha _ hn
  refine D_mem_of_mul i m ((dPC_isUnit i m ha).pow n) ?_ hw hdn
  exact Subtype.ext (by
    change (partialVal i m.succ) ^ n * (r : F) = (r : F) * partialVal i m.succ ^ n
    ring)


/-! ### Independence, through the function field -/

theorem D_chartVals_succ (i : Fin 5) (n : Fin 3) :
    KaehlerDifferential.D F₁₉ F (chartVals i n.succ) = fieldBasisF i n := by
  rw [fieldBasisF_apply, chartVals_succ]

theorem pderiv_zero_hPoly (i : Fin 5) : pderiv 0 (hPoly i) = 2 * X 0 := by
  fin_cases i <;> simp [hPoly, pderiv_X] <;> ring

theorem chartEval_pderiv_zero (i : Fin 5) : chartEval i (pderiv 0 (hPoly i)) = 2 * yc i := by
  rw [pderiv_zero_hPoly]
  simp [chartEval, chartVals]

theorem D_yc_F (i : Fin 5) : KaehlerDifferential.D F₁₉ F (yc i) =
    -(2 * yc i)⁻¹ • ∑ n : Fin 3, chartEval i (pderiv n.succ (hPoly i)) • fieldBasisF i n := by
  have hrel := (SurfaceLib.derivation_aeval (KaehlerDifferential.D F₁₉ F) (chartVals i)
    (hPoly i)).symm.trans (by
      rw [show aeval (chartVals i) (hPoly i) = chartEval i (hPoly i) from rfl, chartEval_hPoly,
        map_zero])
  rw [Fin.sum_univ_succ] at hrel
  have h0 : aeval (chartVals i) (pderiv 0 (hPoly i)) = 2 * yc i := chartEval_pderiv_zero i
  have h2 : (2 : F) * yc i ≠ 0 := mul_ne_zero two_ne_zero_F (yc_ne_zero i)
  simp only [h0, D_chartVals_succ] at hrel
  have hy : chartVals i 0 = yc i := rfl
  rw [hy] at hrel
  have h3 := eq_neg_of_add_eq_zero_left hrel
  calc KaehlerDifferential.D F₁₉ F (yc i)
      = (2 * yc i)⁻¹ • ((2 * yc i) • KaehlerDifferential.D F₁₉ F (yc i)) := by
        rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = _ := by rw [h3, smul_neg, neg_smul]; rfl


theorem repr_D_yc (i : Fin 5) (n : Fin 3) :
    (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (yc i)) n =
      -(2 * yc i)⁻¹ * chartEval i (pderiv n.succ (hPoly i)) := by
  rw [D_yc_F, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [Basis.repr_sum_self]

theorem repr_D_chartVals_succ (i : Fin 5) (n n' : Fin 3) :
    (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i n'.succ)) n =
      if n' = n then 1 else 0 := by
  rw [D_chartVals_succ, Basis.repr_self, Finsupp.single_apply]

/-- The field coordinate of the second and third kept coordinates. -/
def keptIdx : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![0, 0, 2], ![0, 0, 1]]

theorem kept_table (m : Fin 3) : kept m 0 = 0 ∧ kept m 1 = (keptIdx m 1).succ ∧
    kept m 2 = (keptIdx m 2).succ ∧ keptIdx m 1 ≠ m ∧ keptIdx m 2 ≠ m ∧ keptIdx m 1 ≠ keptIdx m 2 := by
  fin_cases m <;> decide

theorem kept_independent (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    LinearIndependent (PChart i m)
      (fun l : Fin 3 ↦ KaehlerDifferential.D F₁₉ (PChart i m) (zloc i m (kept m l))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmap := congrArg (KaehlerDifferential.map F₁₉ F₁₉ (PChart i m) F) hg
  simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, map_zero] at hmap
  have hco (n : Fin 3) : ∑ l, (g l : F) *
      (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i (kept m l))) n = 0 := by
    have := congrArg (fun ω ↦ (fieldBasisF i).repr ω n) hmap
    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hs : (g l • KaehlerDifferential.D F₁₉ F ((algebraMap (PChart i m) F) (zloc i m (kept m l))) :
        KaehlerDifferential F₁₉ F) = (g l : F) • KaehlerDifferential.D F₁₉ F (chartVals i (kept m l)) :=
      (algebraMap_smul F (g l) _).symm
    calc (g l : F) * (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i (kept m l))) n
        = (fieldBasisF i).repr ((g l : F) • KaehlerDifferential.D F₁₉ F (chartVals i (kept m l))) n := by
          rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      _ = _ := (congrArg (fun ω ↦ (fieldBasisF i).repr ω n) hs).symm
  have hy0 : (2 : F) * yc i ≠ 0 := mul_ne_zero two_ne_zero_F (yc_ne_zero i)
  have hinv : -(2 * yc i)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hy0)
  obtain ⟨k0, k1, k2, n1, n2, n12⟩ := kept_table m
  have r0 (n : Fin 3) : (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i (kept m 0))) n =
      -(2 * yc i)⁻¹ * chartEval i (pderiv n.succ (hPoly i)) := by
    rw [k0]; exact repr_D_yc i n
  have r1 (n : Fin 3) : (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i (kept m 1))) n =
      if keptIdx m 1 = n then 1 else 0 := by
    rw [k1]; exact repr_D_chartVals_succ i n _
  have r2 (n : Fin 3) : (fieldBasisF i).repr (KaehlerDifferential.D F₁₉ F (chartVals i (kept m 2))) n =
      if keptIdx m 2 = n then 1 else 0 := by
    rw [k2]; exact repr_D_chartVals_succ i n _
  have heq (n : Fin 3) := hco n
  simp only [Fin.sum_univ_three, r0, r1, r2] at heq
  have hP : chartEval i (pderiv m.succ (hPoly i)) ≠ 0 := ha
  have g0 : (g 0 : F) = 0 := by
    have h := heq m
    simp only [n1, n2, ite_false, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hinv hP)
  have g1 : (g 1 : F) = 0 := by
    have h := heq (keptIdx m 1)
    simp only [g0, zero_mul, zero_add, ite_true, mul_one, Ne.symm n12, ite_false, mul_zero,
      add_zero] at h
    exact h
  have g2 : (g 2 : F) = 0 := by
    have h := heq (keptIdx m 2)
    simp only [g0, g1, zero_mul, zero_add, n12, ite_false, mul_zero, ite_true, mul_one] at h
    exact h
  have hsuff : ∀ l, (g l : F) = 0 := by
    intro l
    fin_cases l
    · exact g0
    · exact g1
    · exact g2
  intro l
  exact Subtype.ext (hsuff l)


/-- On the principal open where `∂h/∂X_{m+1}` is a unit, the kept differentials form a basis. -/
def localBasis (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    Basis (Fin 3) (PChart i m) (KaehlerDifferential F₁₉ (PChart i m)) :=
  Basis.mk (kept_independent i m ha) (keptSpan_top i m ha)

/-- The same basis of the absolute differentials. -/
def localBasisZ (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    Basis (Fin 3) (PChart i m) (KaehlerDifferential ℤ (PChart i m)) :=
  (localBasis i m ha).map
    (quotientBaseDifferentialEquiv ℤ F₁₉ (PChart i m) ZMod.intCast_surjective).symm

theorem localBasisZ_apply (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) (l : Fin 3) :
    localBasisZ i m ha l = KaehlerDifferential.D ℤ (PChart i m) (zloc i m (kept m l)) := by
  rw [localBasisZ, Basis.map_apply, localBasis, Basis.mk_apply, quotientBaseDifferentialEquiv_symm_D]

/-! ## Local freeness -/

theorem PChart_isLocalization (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    letI := inclusionAlgebra (chartRing_le_PChart i m)
    IsLocalization.Away (⟨partialVal i m.succ, partialVal_mem i _⟩ : chartRing i) (PChart i m) :=
  subalgebra_isLocalizationAway (chartRing i) (PChart i m) (chartRing_le_PChart i m) _ ha
    (inv_mem_PChart i m) le_rfl

/-- A chart index of the atlas. -/
def ix (i : Fin 5) : atlas.Index := i

/-- The inclusion of the principal open into its chart. -/
def pchartIncl (i : Fin 5) (m : Fin 3) :
    Spec (CommRingCat.of (PChart i m)) ⟶ Spec (CommRingCat.of (chartRing i)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (chartRing_le_PChart i m)).toRingHom)

/-- The principal open as an open subscheme of `X`. -/
def pchartMap (i : Fin 5) (m : Fin 3) : Spec (CommRingCat.of (PChart i m)) ⟶ X19 :=
  pchartIncl i m ≫ atlas.chartInclusion (ix i)

theorem pchartMap_isOpenImmersion (i : Fin 5) (m : Fin 3) (ha : partialVal i m.succ ≠ 0) :
    IsOpenImmersion (pchartMap i m) := by
  let := inclusionAlgebra (chartRing_le_PChart i m)
  have := PChart_isLocalization i m ha
  have h1 : IsOpenImmersion (pchartIncl i m) :=
    IsOpenImmersion.of_isLocalization (R := chartRing i) (S := PChart i m)
      (⟨partialVal i m.succ, partialVal_mem i _⟩ : chartRing i)
  exact @IsOpenImmersion.comp _ _ _ (pchartIncl i m) (atlas.chartInclusion (ix i)) h1
    (atlas.chartInclusion_open (ix i))

/-- At every point of a chart one of the three partials `∂h/∂X_{m+1}` is a unit. -/
theorem exists_partial_not_mem (i : Fin 5) (𝔭 : Ideal (chartRing i)) [𝔭.IsPrime] :
    ∃ m : Fin 3, (⟨partialVal i m.succ, partialVal_mem i _⟩ : chartRing i) ∉ 𝔭 := by
  by_contra h
  push Not at h
  obtain ⟨N, hN⟩ := pow_c_mem i (𝔭.comap (chartHom i)) fun j ↦ h j
  have hc : chartHom i (X 1) ∈ 𝔭 :=
    Ideal.IsPrime.mem_of_pow_mem inferInstance N (by rw [← map_pow]; exact hN)
  rw [chartHom_X_one] at hc
  exact (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.eq_top_of_isUnit_mem _ hc ((Ne.isUnit c_ne_zero).map _))

/-- Every point of `X` lies on a principal open of a chart with a nonzero partial. -/
theorem exists_pchart (x : X19) : ∃ (i : Fin 5) (m : Fin 3) (_ : partialVal i m.succ ≠ 0),
    x ∈ Set.range (pchartMap i m) := by
  obtain ⟨i, p, rfl⟩ := atlas.chartInclusion_cover x
  obtain ⟨m, hm⟩ := @exists_partial_not_mem (i : Fin 5) p.asIdeal p.isPrime
  have ha : partialVal i m.succ ≠ 0 := fun h0 ↦ hm (by
    rw [show (⟨partialVal i m.succ, partialVal_mem i _⟩ : chartRing i) = 0 from Subtype.ext h0]
    exact zero_mem _)
  refine ⟨i, m, ha, ?_⟩
  let := inclusionAlgebra (chartRing_le_PChart i m)
  have := PChart_isLocalization i m ha
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap (chartRing i) (PChart i m))) := by
    rw [PrimeSpectrum.localization_away_comap_range (PChart i m)
      (⟨partialVal i m.succ, partialVal_mem i _⟩ : chartRing i)]
    exact hm
  obtain ⟨z, rfl⟩ := hq
  exact ⟨z, rfl⟩

/-- The absolute differentials of `X` are locally free of rank three. -/
theorem x_differentials_locallyFree :
    IsLocallyFreeOfRank 3 (nativeAbsoluteDifferentialModule X19) := fun x ↦ by
  obtain ⟨i, m, ha, hx⟩ := exists_pchart x
  have := pchartMap_isOpenImmersion i m ha
  exact ⟨{
    U := _
    j := pchartMap i m
    mem := hx
    frame := affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of (PChart i m))
      (pchartMap i m) (localBasisZ i m ha) }⟩

end
end Geonormal

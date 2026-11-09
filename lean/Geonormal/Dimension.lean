import Geonormal.Regular
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! # The characteristic-19 surface is two-dimensional

Each chart ring is integral over the polynomial ring `k[e₁, e₂]` of its toric coordinates,
because `y_i² = g_i(e₁, e₂)`. Incomparability bounds the dimension by two, and going up lifts
the chain `0 ⊂ (t) ⊂ (t, x)` of `k[t, x]` to chart `0`.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry IsLocalRing

noncomputable section

/-! ## The toric coordinates are independent over `k` -/

set_option synthInstance.maxHeartbeats 400000 in
theorem toricE_independent (i : Fin 5) :
    AlgebraicIndependent k ![monoE (first i), monoE (second i)] := by
  let σ : Fin 2 ⊕ Fin 1 → Fin 3 := Sum.elim ![1, 2] ![0]
  have hσ : Function.Injective σ := by decide
  have hcomb : AlgebraicIndependent F₁₉ (Sum.elim ![monoE (first i), monoE (second i)] ![cE]) := by
    convert (coordE_independent i).comp σ hσ using 1
    funext z
    rcases z with z | z <;> fin_cases z <;> rfl
  obtain ⟨hc, hy⟩ := AlgebraicIndependent.sumElim_iff.mp hcomb
  have : IsScalarTower P₁ k E := inferInstance
  have hP : AlgebraicIndependent P₁ ![monoE (first i), monoE (second i)] := by
    apply hy.of_ringHom_of_comp_eq hc.aevalEquiv (RingHom.id E) hc.aevalEquiv.injective
    apply RingHom.ext
    intro f
    change (MvPolynomial.aeval ![cE] f : E) = algebraMap k E (algebraMap P₁ k f)
    rw [← IsScalarTower.algebraMap_apply P₁ k E]
    have he : (MvPolynomial.aeval ![cE] : P₁ →ₐ[F₁₉] E) =
        (IsScalarTower.toAlgHom F₁₉ P₁ E) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [Subsingleton.elim j 0]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, IsScalarTower.coe_toAlgHom']
      rfl
    rw [he]
    rfl
  have : Algebra.IsAlgebraic P₁ k :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic k k)
  exact hP.extendScalars k

theorem toric_independent (i : Fin 5) :
    AlgebraicIndependent k ![monoF (first i), monoF (second i)] := by
  convert (toricE_independent i).map' (f := IsScalarTower.toAlgHom k E F)
    (algebraMap E F).injective using 1
  funext j
  fin_cases j <;> rfl

/-- The toric chart ring `k[e₁, e₂]`. -/
def toricRing (i : Fin 5) : Subalgebra k F := Algebra.adjoin k {monoF (first i), monoF (second i)}

theorem toricRing_le (i : Fin 5) : toricRing i ≤ chartRing i :=
  Algebra.adjoin_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)

def toricEquiv (i : Fin 5) : MvPolynomial (Fin 2) k ≃ₐ[k] toricRing i :=
  (toric_independent i).aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by
    rw [toricRing]
    congr 1
    ext z
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto))

theorem toricRing_dimension (i : Fin 5) : ringKrullDim (toricRing i) = 2 := by
  rw [← ringKrullDim_eq_of_ringEquiv (toricEquiv i).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field k]
  norm_num


/-! ## Charts are integral over their toric rings -/

theorem coeffEval_mem_toric (i : Fin 5) (q : MvPolynomial (Fin 3) F₁₉) :
    coeffEval i q ∈ toricRing i := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    rw [coeffEval_eq, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply F₁₉ k F]
    exact (toricRing i).algebraMap_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [coeffEval_eq, MvPolynomial.aeval_X]
    fin_cases j
    · simp only [coordE, Fin.zero_eta, Matrix.cons_val_zero]
      rw [algebraMap_cE]
      exact (toricRing i).algebraMap_mem c
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem yc_isIntegral (i : Fin 5) : IsIntegral (toricRing i) (yc i) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨_, coeffEval_mem_toric i (gChart3 i)⟩, ?_, ?_⟩
  · unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff_X_pow_sub_C (by norm_num)]
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, yc_sq_eq]
    exact sub_self _

instance (i : Fin 5) : Algebra (toricRing i) (chartRing i) := inclusionAlgebra (toricRing_le i)

instance chart_isIntegral (i : Fin 5) : Algebra.IsIntegral (toricRing i) (chartRing i) := by
  have hle : chartRing i ≤ (integralClosure (toricRing i) F).restrictScalars k := by
    apply Algebra.adjoin_le
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact isIntegral_algebraMap
        (x := (⟨_, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ : toricRing i))
    · exact isIntegral_algebraMap
        (x := (⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ :
          toricRing i))
    · exact yc_isIntegral i
  let φ : chartRing i →ₐ[toricRing i] F :=
    { (chartRing i).val with commutes' := fun r ↦ Subalgebra.coe_inclusion (toricRing_le i) r }
  exact ⟨fun z ↦ (isIntegral_algHom_iff φ Subtype.val_injective).mp (hle z.property)⟩

/-! ## Dimension bounds -/

theorem chartRing_dimension_le (i : Fin 5) : ringKrullDim (chartRing i) ≤ 2 := by
  rw [← toricRing_dimension i]
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum (chartRing i) ↦ p.comap (algebraMap (toricRing i) (chartRing i))) ?_
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := toricRing i) hpq


/-- Chart `0` has a prime of height two, over the chain `0 ⊂ (t) ⊂ (t, x)`. -/
theorem exists_height_two : ∃ Q : Ideal (chartRing 0), Q.IsPrime ∧ 2 ≤ Q.height := by
  let e := (toricEquiv 0).symm.toRingEquiv
  let f₀ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 1) k :=
    MvPolynomial.aeval ![0, MvPolynomial.X 0]
  let f₁ : MvPolynomial (Fin 1) k →ₐ[k] k := MvPolynomial.aeval ![0]
  let P₀ : Ideal (toricRing 0) := RingHom.ker (f₀.toRingHom.comp e.toRingHom)
  let P₁ : Ideal (toricRing 0) := RingHom.ker ((f₁.comp f₀).toRingHom.comp e.toRingHom)
  have hP₀ : P₀.IsPrime := RingHom.ker_isPrime _
  have hP₁ : P₁.IsPrime := RingHom.ker_isPrime _
  set a : toricRing 0 := e.symm (MvPolynomial.X 0)
  set b : toricRing 0 := e.symm (MvPolynomial.X 1)
  have hea : e a = MvPolynomial.X 0 := e.apply_symm_apply _
  have heb : e b = MvPolynomial.X 1 := e.apply_symm_apply _
  have ha₀ : a ∈ P₀ := by
    rw [RingHom.mem_ker]
    change f₀ (e a) = 0
    rw [hea]
    simp [f₀]
  have ha : a ≠ 0 := by
    intro h
    have := congrArg e h
    rw [hea, map_zero] at this
    exact MvPolynomial.X_ne_zero 0 this
  have hb₁ : b ∈ P₁ := by
    rw [RingHom.mem_ker]
    change f₁ (f₀ (e b)) = 0
    rw [heb]
    simp [f₀, f₁]
  have hb₀ : b ∉ P₀ := by
    rw [RingHom.mem_ker]
    change ¬ f₀ (e b) = 0
    rw [heb]
    simp [f₀, MvPolynomial.X_ne_zero]
  have hle : P₀ ≤ P₁ := fun z hz ↦ by
    rw [RingHom.mem_ker] at hz ⊢
    change f₀ (e z) = 0 at hz
    change f₁ (f₀ (e z)) = 0
    rw [hz, map_zero]
  have hinj : Function.Injective (algebraMap (toricRing 0) (chartRing 0)) :=
    Subalgebra.inclusion_injective (toricRing_le 0)
  have hbot : (⊥ : Ideal (chartRing 0)).under (toricRing 0) ≤ P₀ := by
    intro z hz
    have : algebraMap (toricRing 0) (chartRing 0) z = 0 := hz
    have hz0 : z = 0 := hinj (this.trans (map_zero _).symm)
    rw [hz0]
    exact zero_mem _
  obtain ⟨Q₁, -, hQ₁, hQ₁P⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P₀ (⊥ : Ideal (chartRing 0)) hbot
  obtain ⟨Q₂, hQ₁₂, hQ₂, hQ₂P⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P₁ Q₁ (hQ₁P ▸ hle)
  have hlt₁ : (⊥ : Ideal (chartRing 0)) < Q₁ := by
    refine bot_lt_iff_ne_bot.mpr fun h ↦ ha ?_
    have : a ∈ Q₁.under (toricRing 0) := hQ₁P ▸ ha₀
    rw [h] at this
    exact hinj ((show algebraMap (toricRing 0) (chartRing 0) a = 0 from this).trans
      (map_zero _).symm)
  have hlt₂ : Q₁ < Q₂ := by
    refine lt_of_le_of_ne hQ₁₂ fun h ↦ hb₀ ?_
    rw [← hQ₁P, h, hQ₂P]
    exact hb₁
  have : (⊥ : Ideal (chartRing 0)).IsPrime := inferInstance
  have h₁ : (1 : ℕ∞) ≤ Q₁.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt₁
    exact (by simp : (1 : ℕ∞) ≤ (⊥ : Ideal (chartRing 0)).height + 1).trans h
  refine ⟨Q₂, hQ₂, ?_⟩
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Q₁.height + 1 := by gcongr
    _ ≤ Q₂.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt₂

/-- `X` is a surface. -/
theorem x_dimension : topologicalKrullDim X19 = 2 := by
  apply le_antisymm
  · rw [scheme_dimension_eq_iSup_stalk]
    refine iSup_le fun x ↦ ?_
    obtain ⟨i, p, rfl⟩ := atlas.chartInclusion_cover x
    have := atlas.chartInclusion_open i
    exact (stalk_dimension_le_of_affine_open (CommRingCat.of (atlas.ring i))
      (atlas.chartInclusion i) p).trans (chartRing_dimension_le i)
  · obtain ⟨Q, hQ, h2⟩ := exists_height_two
    let j : atlas.Index := (0 : Fin 5)
    let p : PrimeSpectrum (atlas.ring j) := ⟨Q, hQ⟩
    have h := stalk_dimension_le_scheme X19 (atlas.chartInclusion j p)
    have hp : p.asIdeal.IsPrime := p.isPrime
    rw [ringKrullDim_eq_of_ringEquiv (atlas.chartStalkEquiv j p),
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ p.asIdeal hp
        (Localization.AtPrime p.asIdeal)] at h
    exact (WithBot.coe_le_coe.mpr h2).trans h

end
end Geonormal

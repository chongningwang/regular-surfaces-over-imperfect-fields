import Geonormal.P11.Regular
import SurfaceLib.AlgebraicGeometry.GeometricNormality

/-! # The characteristic-11 surface is not geometrically normal

The base change of the chart `A` to `k' = k(γ)` is the subring `A' = k'[a, b, σ]` of `K'`, since
`1, γ, …, γ¹⁰` are linearly independent over `L`. Put `τ = σ + 2γ`, so that `τ¹¹ = ab³ - 3a⁴b`,
and `h = aτ + 2b`. Then `h¹¹ = a¹²b³ - 3a¹⁵b + 2b¹¹ = u² M` with
`M = -3a⁹b - 5a⁶b³ + 4a³b⁵ + 2b⁷`, so `g = h⁶/u` satisfies `g¹¹ = u M⁶` and is integral over `A'`.
The `γ⁶`-component of `g` is `(2a)⁶/u`, which is not in `A`: the specialization
`a ↦ t², b ↦ t³, σ ↦ s - 2t` kills `u` and sends `c` to `-6s¹¹`. Hence `A'` is not integrally
closed, and `X ×_k k'` is not normal.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry MvPolynomial
open scoped TensorProduct

noncomputable section

/-! ## `a⁶/u` is not in the chart `A` -/

/-- The specialization `a ↦ t², b ↦ t³, σ ↦ s - 2t`, which kills `u`. -/
def spec : P₄ →ₐ[F₁₁] MvPolynomial (Fin 2) F₁₁ := aeval ![0, X 0 ^ 2, X 0 ^ 3, X 1 - 2 * X 0]

theorem spec_X0 : spec (X 0) = 0 := by simp [spec]
theorem spec_X1 : spec (X 1) = X 0 ^ 2 := by simp [spec]
theorem spec_X2 : spec (X 2) = X 0 ^ 3 := by simp [spec]
theorem spec_X3 : spec (X 3) = X 1 - 2 * X 0 := by simp [spec]

theorem h11T : (11 : MvPolynomial (Fin 2) F₁₁) = 0 := by
  have : ((11 : ℕ) : MvPolynomial (Fin 2) F₁₁) = 0 := by
    rw [← map_natCast (algebraMap F₁₁ _), ZMod.natCast_self, map_zero]
  exact_mod_cast this

theorem spec_cPolyE : spec (cPolyE 0) = -6 * X 1 ^ 11 := by
  simp only [cPolyE, Matrix.cons_val_zero, map_mul, map_sub, map_pow, map_ofNat, spec_X1,
    spec_X2, spec_X3]
  rw [sub_pow_char]
  linear_combination (1116 * X 0 ^ 11 : MvPolynomial (Fin 2) F₁₁) * h11T

theorem transcendental_spec : Transcendental F₁₁ (-6 * X 1 ^ 11 : MvPolynomial (Fin 2) F₁₁) := by
  have h : (-6 * X 1 ^ 11 : MvPolynomial (Fin 2) F₁₁) =
      Polynomial.aeval (X 1) (Polynomial.C (-6 : F₁₁) * Polynomial.X ^ 11 : Polynomial F₁₁) := by
    simp [map_ofNat]
  rw [h]
  refine (MvPolynomial.transcendental_X F₁₁ (1 : Fin 2)).aeval _ ?_ ?_
  · rw [Polynomial.natDegree_C_mul_X_pow 11 _ (by decide)]
    norm_num
  · rw [Polynomial.leadingCoeff_C_mul_X_pow]
    exact mem_nonZeroDivisors_of_ne_zero (by decide)

theorem spec_cPoly_ne_zero {q : P₁} (hq : q ≠ 0) : spec (cPoly 0 q) ≠ 0 := by
  have h : spec (cPoly 0 q) =
      MvPolynomial.aeval (fun _ : Fin 1 ↦ (-6 * X 1 ^ 11 : MvPolynomial (Fin 2) F₁₁)) q := by
    rw [cPoly, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp only [spec_cPolyE]
  have hinj : Function.Injective
      (MvPolynomial.aeval (R := F₁₁) fun _ : Fin 1 ↦ (-6 * X 1 ^ 11 : MvPolynomial (Fin 2) F₁₁)) :=
    algebraicIndependent_unique_type_iff.mpr transcendental_spec
  rw [h]
  intro h0
  exact hq (hinj (h0.trans (map_zero _).symm))

theorem not_mem_chartA : aL ^ 6 / uL ∉ chartA := by
  intro hz
  have hu := uL_ne_zero
  obtain ⟨p, q, hq, hpq⟩ := chartRing_frac 0 (aL ^ 6 / uL) hz
  have ha : chartEval 0 (X 1) = aL := by simp [chartEval, coordV]
  have hb : chartEval 0 (X 2) = bL := by simp [chartEval, coordV]
  have h1 : chartEval 0 (cPoly 0 q * X 1 ^ 6 - (X 2 ^ 2 - X 1 ^ 3) * p) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_sub, map_pow, map_pow, ha, hb, chartEval_cPoly,
      ← hpq, show bL ^ 2 - aL ^ 3 = uL from rfl]
    field_simp
    ring
  rw [← RingHom.mem_ker, ker_chartEval, Ideal.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 := congrArg spec hr
  simp only [map_sub, map_mul, map_pow, spec_X1, spec_X2, hPoly, Matrix.cons_val_zero, spec_X0,
    zero_mul] at h2
  have h3 : spec (cPoly 0 q) * X 0 ^ 12 = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact spec_cPoly_ne_zero hq h
  · exact pow_ne_zero 12 (X_ne_zero 0) h

/-! ## The base change of the chart `A` -/

theorem k'_decomp_k (μ : k') : ∃ f : Fin 11 → k, μ = ∑ i, f i • γ ^ (i : ℕ) := by
  obtain ⟨f, hf⟩ := k'_basis μ
  refine ⟨f, (algebraMap k' K').injective ?_⟩
  rw [hf, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow, ← algebraMap_k_K']
  rfl

/-- `x ⊗ z ↦ ι(x) z`. -/
def muA : chartA ⊗[k] k' →ₐ[k] K' :=
  Algebra.TensorProduct.lift (ιk.comp chartA.val) (IsScalarTower.toAlgHom k k' K')
    (fun _ _ ↦ Commute.all _ _)

theorem muA_tmul (x : chartA) (z : k') : muA (x ⊗ₜ z) = ι x * algebraMap k' K' z := by
  rw [muA, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensor_decomp (t : chartA ⊗[k] k') :
    ∃ x : Fin 11 → chartA, t = ∑ i, x i ⊗ₜ[k] (γ ^ (i : ℕ)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a μ =>
    obtain ⟨f, rfl⟩ := k'_decomp_k μ
    refine ⟨fun i ↦ f i • a, ?_⟩
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add t t' ht ht' =>
    obtain ⟨x, rfl⟩ := ht
    obtain ⟨x', rfl⟩ := ht'
    exact ⟨x + x', by simp [Finset.sum_add_distrib, TensorProduct.add_tmul]⟩

theorem muA_decomp (x : Fin 11 → chartA) :
    muA (∑ i, x i ⊗ₜ[k] (γ ^ (i : ℕ))) = ∑ i, ι (x i) * γK ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [muA_tmul, map_pow]
  rfl

theorem muA_injective : Function.Injective muA := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨x, rfl⟩ := tensor_decomp t
  rw [muA_decomp] at ht
  have h0 : ∀ i, x i = 0 := fun i ↦ Subtype.ext (decomp_unique (fun i ↦ (x i : L)) ht i)
  simp [h0]

/-- The base change `A ⊗_k k'`, inside `K'`. -/
def Ak' : Subalgebra k K' := muA.range

def tensorEquiv : chartA ⊗[k] k' ≃ₐ[k] Ak' := AlgEquiv.ofInjective muA muA_injective

theorem mem_Ak' (x : chartA) (z : k') : ι x * algebraMap k' K' z ∈ Ak' := ⟨x ⊗ₜ z, muA_tmul x z⟩

theorem ι_mem_Ak' {x : L} (hx : x ∈ chartA) : ι x ∈ Ak' := by
  simpa using mem_Ak' ⟨x, hx⟩ 1

theorem k'_mem_Ak' (z : k') : algebraMap k' K' z ∈ Ak' := by
  simpa using mem_Ak' 1 z

instance Ak'_isFractionRing : IsFractionRing Ak' K' := by
  apply IsFractionRing.of_field
  intro z
  have hF (r : F₁₁) : algebraMap F₁₁ K' r ∈ Subfield.closure (Ak' : Set K') := by
    rw [IsScalarTower.algebraMap_apply F₁₁ k' K']
    exact Subfield.subset_closure (k'_mem_Ak' _)
  let M : IntermediateField F₁₁ K' := (Subfield.closure (Ak' : Set K')).toIntermediateField hF
  have hM : M = ⊤ := by
    rw [eq_top_iff, ← generation_vK, IntermediateField.adjoin_le_iff]
    rintro _ (⟨i, rfl⟩ | h)
    · fin_cases i
      · have h := ι_mem_Ak' aL_mem_A
        rw [ι_aL] at h
        exact Subfield.subset_closure h
      · have h := ι_mem_Ak' bL_mem_A
        rw [ι_bL] at h
        exact Subfield.subset_closure h
      · have h := ι_mem_Ak' σL_mem_A
        rw [ι_σL] at h
        exact Subfield.subset_closure h
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact Subfield.subset_closure (k'_mem_Ak' γ)
  have hz : z ∈ Subfield.closure (Ak' : Set K') := by
    change z ∈ M
    rw [hM]
    exact IntermediateField.mem_top
  rw [Subfield.mem_closure_iff] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have hS : Subring.closure (Ak' : Set K') = Ak'.toSubring := Subring.closure_eq Ak'.toSubring
  rw [hS] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

/-! ## A non-integral-closure witness -/

/-- `τ = σ + 2γ`. -/
def τK : K' := ι σL + 2 * γK

theorem h11Kn : (11 : K') = 0 := by exact_mod_cast CharP.cast_eq_zero K' 11

theorem two_pow_K' : (2 : K') ^ 11 = 2 := by linear_combination (186 : K') * h11Kn

theorem τK_pow : τK ^ 11 = ι (aL * bL ^ 3 - 3 * aL ^ 3 * (aL * bL)) := by
  have h := congrArg ι σ11
  rw [map_pow, map_sub, map_mul, map_ofNat, ι_cL] at h
  rw [τK, add_pow_char, mul_pow, two_pow_K', h]
  ring

/-- `h = aτ + 2b`. -/
def hK : K' := ι aL * τK + 2 * ι bL

def Mpol : L := -3 * aL ^ 9 * bL - 5 * aL ^ 6 * bL ^ 3 + 4 * aL ^ 3 * bL ^ 5 + 2 * bL ^ 7

theorem N_eq : aL ^ 11 * (aL * bL ^ 3 - 3 * aL ^ 3 * (aL * bL)) + 2 * bL ^ 11 = uL ^ 2 * Mpol := by
  simp only [uL, Mpol]
  grind

theorem hK_pow : hK ^ 11 = ι uL ^ 2 * ι Mpol := by
  rw [hK, add_pow_char, mul_pow, mul_pow, τK_pow, two_pow_K', ← map_pow, ← map_pow, ← map_mul,
    ← map_ofNat ι 2, ← map_mul, ← map_add, N_eq, map_mul, map_pow]

/-- The witness `g = h⁶/u`. -/
def gK : K' := hK ^ 6 / ι uL

theorem gK_pow : gK ^ 11 = ι (uL * Mpol ^ 6) := by
  have hu : ι uL ≠ 0 := (map_ne_zero ι).mpr uL_ne_zero
  rw [gK, div_pow, ← pow_mul, show 6 * 11 = 11 * 6 by norm_num, pow_mul, hK_pow, map_mul, map_pow]
  field_simp

theorem gK_integral : IsIntegral Ak' gK := by
  have hm : ι (uL * Mpol ^ 6) ∈ Ak' := by
    refine ι_mem_Ak' ?_
    have hu : uL ∈ chartA := by
      rw [show uL = bL ^ 2 - aL ^ 3 from rfl]
      exact chartA.sub_mem (chartA.pow_mem bL_mem_A 2) (chartA.pow_mem aL_mem_A 3)
    have hM : Mpol ∈ chartA := by
      have ha := aL_mem_A
      have hb := bL_mem_A
      simp only [Mpol]
      subalg_mem
    exact chartA.mul_mem hu (chartA.pow_mem hM 6)
  refine ⟨Polynomial.X ^ 11 - Polynomial.C ⟨_, hm⟩, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, gK_pow]
  exact sub_self _

/-- The `γ`-components of `g`. -/
def gComp : Fin 11 → L := ![(aL * σL + 2 * bL) ^ 6 / uL, 6 * (aL * σL + 2 * bL) ^ 5 * (2 * aL) / uL,
  15 * (aL * σL + 2 * bL) ^ 4 * (2 * aL) ^ 2 / uL, 20 * (aL * σL + 2 * bL) ^ 3 * (2 * aL) ^ 3 / uL,
  15 * (aL * σL + 2 * bL) ^ 2 * (2 * aL) ^ 4 / uL, 6 * (aL * σL + 2 * bL) * (2 * aL) ^ 5 / uL,
  (2 * aL) ^ 6 / uL, 0, 0, 0, 0]

theorem gK_decomp : gK = ∑ i, ι (gComp i) * γK ^ (i : ℕ) := by
  have hu : ι uL ≠ 0 := (map_ne_zero ι).mpr uL_ne_zero
  have hh : hK = ι (aL * σL + 2 * bL) + ι (2 * aL) * γK := by
    simp only [hK, τK, map_add, map_mul, map_ofNat]
    ring
  rw [gK, hh]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, gComp, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_div₀, map_mul, map_pow, map_add, map_ofNat, map_zero, zero_mul, add_zero, Fin.val_zero,
    Fin.val_succ]
  field_simp
  ring

theorem gK_not_mem : ¬ ∃ y : Ak', algebraMap Ak' K' y = gK := by
  rintro ⟨⟨_, t, rfl⟩, hy⟩
  obtain ⟨x, rfl⟩ := tensor_decomp t
  have hy' : muA (∑ i, x i ⊗ₜ[k] (γ ^ (i : ℕ))) = gK := hy
  rw [muA_decomp] at hy'
  have hsum : ∑ i, ι ((x i : L) - gComp i) * γK ^ (i : ℕ) = 0 := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hy', ← gK_decomp, sub_self]
  have h6 := decomp_unique _ hsum 6
  rw [sub_eq_zero] at h6
  have hx6 : (x 6 : L) = (2 * aL) ^ 6 / uL := by
    rw [h6]
    rfl
  have hmem : (2 * aL) ^ 6 / uL ∈ chartA := hx6 ▸ (x 6).2
  apply not_mem_chartA
  have h5 : aL ^ 6 / uL = 5 * ((2 * aL) ^ 6 / uL) := by
    linear_combination (-(29 : L) * (aL ^ 6 / uL)) * h11L
  rw [h5]
  exact chartA.mul_mem (ofNat_mem' chartA 5) hmem

theorem Ak'_not_isIntegrallyClosed : ¬ IsIntegrallyClosed Ak' := by
  intro h
  exact gK_not_mem ((isIntegrallyClosed_iff K').mp h gK_integral)

/-- `X` is not geometrically normal: its base change to `k'` is not normal. -/
theorem x_not_geometrically_normal : ¬ geometrically SurfaceLib.IsNormalScheme xToBase := by
  have : IsOpenImmersion (atlas.chartInclusion (0 : Fin 4)) := atlas.chartInclusion_open _
  exact SurfaceLib.not_geometrically_normal_of_open (ℓ' := k') xToBase
    (atlas.chartInclusion (0 : Fin 4)) (atlas.chartInclusion_toBase (0 : Fin 4))
    tensorEquiv.toRingEquiv Ak'_not_isIntegrallyClosed

end
end Geonormal.P11

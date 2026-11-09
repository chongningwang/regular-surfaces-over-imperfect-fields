import Geonormal.P11.Projective
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Global functions on the characteristic-11 surface are constants

The field `k` is algebraically closed in `L`. If `z ∈ L` is algebraic over `k`, then `ι(z)` is
algebraic over `k'`, hence a constant of `K' = k'(x', y')`, since `k[x', y']` is factorial and a
nonconstant polynomial is not integral over `k'` by total degree. Writing that constant as
`Σ_{i<11} λ_i γ^i` with `λ_i ∈ k`, linear independence of `1, γ, …, γ¹⁰` over `ι(L)` gives
`z = λ₀`. Since `X` is proper and integral, its global functions are therefore the constants.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry

noncomputable section

/-! ## `k'` is algebraically closed in `K'` -/

theorem polynomial_constant_of_isIntegral (p : S₂) (hp : IsIntegral k' p) :
    ∃ c : k', MvPolynomial.C c = p := by
  by_cases hd : p.totalDegree = 0
  · exact ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd).symm⟩
  exfalso
  obtain ⟨q, hq, hroot⟩ := hp
  have hp0 : p ≠ 0 := by rintro rfl; simp at hd
  have hpow (n : ℕ) : (p ^ n).totalDegree = n * p.totalDegree := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain (pow_ne_zero n hp0) hp0, ih]
      ring
  have hq1 : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h | h
    · rw [Polynomial.Monic.natDegree_eq_zero hq] at h
      simp [h] at hroot
    · exact h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hq,
    map_one, one_mul] at hroot
  have hlt : (∑ i ∈ Finset.range q.natDegree, algebraMap k' S₂ (q.coeff i) * p ^ i).totalDegree <
      (p ^ q.natDegree).totalDegree := by
    rw [hpow]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
    refine (Finset.sup_lt_iff (by positivity)).mpr fun i hi ↦ ?_
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, hpow]
    have := Finset.mem_range.mp hi
    have hd' : 0 < p.totalDegree := Nat.pos_of_ne_zero hd
    nlinarith
  have h0 := MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt
  rw [add_comm] at hroot
  rw [hroot, MvPolynomial.totalDegree_zero, hpow] at h0
  have hd' : 0 < p.totalDegree := Nat.pos_of_ne_zero hd
  have : 0 < q.natDegree * p.totalDegree := Nat.mul_pos hq1 hd'
  omega

theorem K'_constants (α : K') (hα : IsIntegral k' α) : ∃ c : k', algebraMap k' K' c = α := by
  have hR : IsIntegral S₂ α := hα.tower_top
  obtain ⟨p, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hR
  have hp : IsIntegral k' p :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k' S₂ K')
      (IsFractionRing.injective S₂ K')).mp hα
  obtain ⟨c, hc⟩ := polynomial_constant_of_isIntegral p hp
  exact ⟨c, by rw [← hc, IsScalarTower.algebraMap_apply k' S₂ K']; rfl⟩

/-! ## `k` is algebraically closed in `L` -/

/-- Every element of `k'` is `Σ_{i<11} λ_i γ^i` with `λ_i ∈ k`. -/
theorem k'_basis (μ : k') : ∃ f : Fin 11 → k,
    algebraMap k' K' μ = ∑ i, algebraMap k K' (f i) * γK ^ (i : ℕ) := by
  obtain ⟨l, q, rfl⟩ := k'_decomp μ
  have hT : (Polynomial.X ^ 11 - Polynomial.C c : Polynomial k).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hTγ : Polynomial.aeval γ (Polynomial.X ^ 11 - Polynomial.C c : Polynomial k) = 0 := by
    simp [algebraMap_c]
  have hT1 : (Polynomial.X ^ 11 - Polynomial.C c : Polynomial k) ≠ 1 := by
    intro h1
    have := congrArg Polynomial.natDegree h1
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at this
    omega
  have hdeg : (q.map (algebraMap F₁₁ k) %ₘ (Polynomial.X ^ 11 - Polynomial.C c)).natDegree < 11 := by
    have := Polynomial.natDegree_modByMonic_lt (q.map (algebraMap F₁₁ k)) hT hT1
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have hval : Polynomial.aeval γ q = Polynomial.aeval γ
      (q.map (algebraMap F₁₁ k) %ₘ (Polynomial.X ^ 11 - Polynomial.C c)) := by
    rw [← Polynomial.aeval_map_algebraMap k γ q]
    conv_lhs => rw [← Polynomial.modByMonic_add_div (q.map (algebraMap F₁₁ k))
      (Polynomial.X ^ 11 - Polynomial.C c)]
    rw [map_add, map_mul, hTγ, zero_mul, add_zero]
  refine ⟨fun i ↦ l * (q.map (algebraMap F₁₁ k) %ₘ (Polynomial.X ^ 11 - Polynomial.C c)).coeff i,
    ?_⟩
  rw [hval, Polynomial.aeval_eq_sum_range' hdeg, Finset.mul_sum, map_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [γK, Algebra.smul_def, algebraMap_k_K', map_mul, map_pow]
  ring

theorem L_constants (z : L) (hz : IsAlgebraic k z) : ∃ c : k, algebraMap k L c = z := by
  have : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq algebraMap_k_K'
  have h1 : IsAlgebraic k (ι z) := hz.algHom ιk
  have h2 : IsAlgebraic k' (ι z) := h1.extendScalars (algebraMap k k').injective
  obtain ⟨μ, hμ⟩ := K'_constants (ι z) h2.isIntegral
  obtain ⟨f, hf⟩ := k'_basis μ
  have h0 := decomp_unique (fun i ↦ (if i = 0 then z else 0) - algebraMap k L (f i)) (by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ι_algebraMap]
    rw [← hf, hμ, Fin.sum_univ_succ]
    simp) 0
  have h0' : z - algebraMap k L (f 0) = 0 := by simpa using h0
  exact ⟨f 0, (sub_eq_zero.mp h0').symm⟩

/-! ## The function field of `X` -/

theorem P₃_mem_A (p : P₃) : algebraMap P₃ L p ∈ chartA := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply F₁₁ k L]
    exact chartA.algebraMap_mem _
  | add p q hp hq => simpa only [map_add] using chartA.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    refine chartA.mul_mem hp ?_
    fin_cases j
    · exact aL_mem_A
    · exact bL_mem_A
    · exact σL_mem_A

instance chartA_isFractionRing : IsFractionRing chartA L := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := P₃) z
  exact ⟨⟨_, P₃_mem_A p⟩, ⟨_, P₃_mem_A q⟩, rfl⟩

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

instance chartRing_isFractionRing (i : atlas.Index) : IsFractionRing (atlas.ring i) L :=
  @atlas_chart_isFractionRing k L _ _ _ atlas (0 : Fin 4) i chartA_isFractionRing

/-- `H⁰(X, O_X) = k`. -/
theorem x_globalScalarMap_bijective : Function.Bijective (globalScalarMap k xToBase) := by
  have : IsProper xToBase := x_proper
  have : IsFractionRing (atlas.ring (0 : Fin 4)) L := chartA_isFractionRing
  let := functionFieldAlgebra k xToBase
  let e := atlas.functionFieldAlgEquiv (0 : Fin 4)
  exact globalScalarMap_bijective_of_constants k L xToBase L_constants e.toRingEquiv
    (RingHom.ext fun c ↦ e.commutes c)

end
end Geonormal.P11

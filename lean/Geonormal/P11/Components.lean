import Geonormal.P11.Charts

/-! # The polynomial ring `S = k'[x', y']` over the chart `P`

The elements `ξ_n = θ_n/u²` map to the polynomials `r_n(γ, x', y')`, the `γ^n`-components of
`x'`. Since `1, γ, …, γ¹⁰` are linearly independent over `ι(L)`, every element of
`S = k'[x', y']` is uniquely `Σ_{i<11} ι(ρ_i) γ^i` with `ρ_i ∈ P`. Consequently an element of `L`
lies in `P` exactly when its image is a polynomial, and `s¹¹ ∈ ι(P)` for every `s ∈ S`.
-/

namespace Geonormal.P11

noncomputable section

/-! ## The components `r_n` -/

section Components

variable {R : Type*} [CommRing R]

/-- The `γ^0`-component `r_0` of `x'`. -/
def r0 (g x y : R) : R := -g ^ 10 * y ^ 4 + 2 * g ^ 10 * x ^ 3 * y ^ 2 - g ^ 10 * x ^ 6
    + 5 * g ^ 9 * x * y ^ 3 - 4 * g ^ 9 * x ^ 4 * y - 3 * g ^ 8 * x ^ 2 * y ^ 2 + g ^ 8 * x ^ 5
    + 2 * g ^ 7 * y ^ 3 + g ^ 7 * x ^ 3 * y + 4 * g ^ 6 * x * y ^ 2 + 3 * g ^ 6 * x ^ 4
    + 5 * g ^ 5 * x ^ 2 * y + 2 * g ^ 4 * y ^ 2 + 3 * g ^ 4 * x ^ 3 - 4 * g ^ 3 * x * y
    + 3 * g ^ 2 * x ^ 2 - 2 * g * y + x

/-- The `γ^1`-component `r_1` of `x'`. -/
def r1 (g x y : R) : R := -g ^ 9 * y ^ 4 + 2 * g ^ 9 * x ^ 3 * y ^ 2 - g ^ 9 * x ^ 6
    - g ^ 8 * x * y ^ 3 + 3 * g ^ 8 * x ^ 4 * y + 2 * g ^ 7 * x ^ 2 * y ^ 2 + 3 * g ^ 7 * x ^ 5
    - 3 * g ^ 6 * y ^ 3 + 4 * g ^ 6 * x ^ 3 * y - 2 * g ^ 5 * x * y ^ 2 + 4 * g ^ 5 * x ^ 4
    - 3 * g ^ 4 * x ^ 2 * y + 3 * g ^ 3 * y ^ 2 - g ^ 3 * x ^ 3 + g ^ 2 * x * y + 5 * g * x ^ 2
    + 2 * y

/-- The `γ^2`-component `r_2` of `x'`. -/
def r2 (g x y : R) : R := -g ^ 8 * y ^ 4 + 2 * g ^ 8 * x ^ 3 * y ^ 2 - g ^ 8 * x ^ 6
    + 4 * g ^ 7 * x * y ^ 3 - g ^ 7 * x ^ 4 * y + 4 * g ^ 6 * x ^ 2 * y ^ 2 - 5 * g ^ 6 * x ^ 5
    - 2 * g ^ 5 * y ^ 3 - g ^ 5 * x ^ 3 * y + 5 * g ^ 4 * x * y ^ 2 + g ^ 4 * x ^ 4
    - 5 * g ^ 3 * x ^ 2 * y + g ^ 2 * y ^ 2 - 4 * g ^ 2 * x ^ 3 - g * x * y + 3 * x ^ 2

/-- The `γ^3`-component `r_3` of `x'`. -/
def r3 (g x y : R) : R := -g ^ 7 * y ^ 4 + 2 * g ^ 7 * x ^ 3 * y ^ 2 - g ^ 7 * x ^ 6
    - 2 * g ^ 6 * x * y ^ 3 - 5 * g ^ 6 * x ^ 4 * y + 3 * g ^ 5 * x ^ 2 * y ^ 2 - g ^ 5 * x ^ 5
    - 4 * g ^ 4 * y ^ 3 - 2 * g ^ 4 * x ^ 3 * y - 3 * g ^ 3 * x * y ^ 2 - 5 * g ^ 3 * x ^ 4
    + 5 * g ^ 2 * x ^ 2 * y + 3 * g * y ^ 2 - g * x ^ 3 + 4 * x * y

/-- The `γ^4`-component `r_4` of `x'`. -/
def r4 (g x y : R) : R := -g ^ 6 * y ^ 4 + 2 * g ^ 6 * x ^ 3 * y ^ 2 - g ^ 6 * x ^ 6
    + 3 * g ^ 5 * x * y ^ 3 + 2 * g ^ 5 * x ^ 4 * y - g ^ 4 * x ^ 2 * y ^ 2 + 4 * g ^ 4 * x ^ 5
    + 4 * g ^ 3 * y ^ 3 + 2 * g ^ 3 * x ^ 3 * y + 5 * g ^ 2 * x * y ^ 2 + g ^ 2 * x ^ 4
    + 3 * g * x ^ 2 * y + 2 * y ^ 2 + 3 * x ^ 3

/-- The `γ^5`-component `r_5` of `x'`. -/
def r5 (g x y : R) : R := -g ^ 5 * y ^ 4 + 2 * g ^ 5 * x ^ 3 * y ^ 2 - g ^ 5 * x ^ 6
    - 3 * g ^ 4 * x * y ^ 3 - 2 * g ^ 4 * x ^ 4 * y + 3 * g ^ 3 * x ^ 2 * y ^ 2 - g ^ 3 * x ^ 5
    + 2 * g ^ 2 * y ^ 3 + g ^ 2 * x ^ 3 * y - 2 * g * x * y ^ 2 + 4 * g * x ^ 4 - 5 * x ^ 2 * y

/-- The `γ^6`-component `r_6` of `x'`. -/
def r6 (g x y : R) : R := -g ^ 4 * y ^ 4 + 2 * g ^ 4 * x ^ 3 * y ^ 2 - g ^ 4 * x ^ 6
    + 2 * g ^ 3 * x * y ^ 3 + 5 * g ^ 3 * x ^ 4 * y + 4 * g ^ 2 * x ^ 2 * y ^ 2
    - 5 * g ^ 2 * x ^ 5 + 3 * g * y ^ 3 - 4 * g * x ^ 3 * y + 4 * x * y ^ 2 + 3 * x ^ 4

/-- The `γ^7`-component `r_7` of `x'`. -/
def r7 (g x y : R) : R := -g ^ 3 * y ^ 4 + 2 * g ^ 3 * x ^ 3 * y ^ 2 - g ^ 3 * x ^ 6
    - 4 * g ^ 2 * x * y ^ 3 + g ^ 2 * x ^ 4 * y + 2 * g * x ^ 2 * y ^ 2 + 3 * g * x ^ 5
    - 2 * y ^ 3 - x ^ 3 * y

/-- The `γ^8`-component `r_8` of `x'`. -/
def r8 (g x y : R) : R := -g ^ 2 * y ^ 4 + 2 * g ^ 2 * x ^ 3 * y ^ 2 - g ^ 2 * x ^ 6
    + g * x * y ^ 3 - 3 * g * x ^ 4 * y - 3 * x ^ 2 * y ^ 2 + x ^ 5

/-- The `γ^9`-component `r_9` of `x'`. -/
def r9 (g x y : R) : R := -g * y ^ 4 + 2 * g * x ^ 3 * y ^ 2 - g * x ^ 6 - 5 * x * y ^ 3
    + 4 * x ^ 4 * y

/-- The `γ^10`-component `r_10` of `x'`. -/
def r10 (_g x y : R) : R := -y ^ 4 + 2 * x ^ 3 * y ^ 2 - x ^ 6
/-- The eleven components `r_n`. -/
def rE (n : Fin 11) (g x y : R) : R :=
  ![r0 g x y, r1 g x y, r2 g x y, r3 g x y, r4 g x y, r5 g x y, r6 g x y, r7 g x y, r8 g x y,
    r9 g x y, r10 g x y] n

end Components

set_option maxHeartbeats 1000000 in
theorem rE_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 11) (g x y : R) :
    f (rE n g x y) = rE n (f g) (f x) (f y) := by
  fin_cases n <;> simp [rE, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, map_ofNat]

section Generic

variable {F : Type*} [Field F]

theorem θE_homog (n : Fin 11) (A B T w : F) (hw : w ≠ 0) :
    θE n (A / w ^ 4) (B / w ^ 6) (T / w ^ 2) * w ^ 20 = θE n A B T * w ^ (2 * (n : ℕ)) := by
  fin_cases n <;> simp [θE, θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10] <;> field_simp

variable [CharP F 11]

set_option maxHeartbeats 4000000 in
/-- `ι(ξ_n) = r_n`, cleared of denominators. -/
theorem r_poly (n : Fin 11) (g x y : F) :
    rE n g x y * (y ^ 2 - x ^ 3) ^ 18 = θE n (x ^ 11) (y ^ 11)
      (x * y * (y ^ 2 - 3 * x ^ 3) - 2 * g * (y ^ 2 - x ^ 3) ^ 2) * (y ^ 2 - x ^ 3) ^ (2 * (n : ℕ)) := by
  fin_cases n <;> simp [rE, θE, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, θ0, θ1, θ2, θ3, θ4,
    θ5, θ6, θ7, θ8, θ9, θ10] <;> grind

theorem r_ident (n : Fin 11) (x y g : F) (hw : y ^ 2 - x ^ 3 ≠ 0) :
    θE n (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6)
      (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) * (y ^ 2 - x ^ 3) ^ 2 =
      rE n g x y := by
  have hT : x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g =
      (x * y * (y ^ 2 - 3 * x ^ 3) - 2 * g * (y ^ 2 - x ^ 3) ^ 2) / (y ^ 2 - x ^ 3) ^ 2 := by
    field_simp
  rw [hT]
  have h1 := θE_homog n (x ^ 11) (y ^ 11)
    (x * y * (y ^ 2 - 3 * x ^ 3) - 2 * g * (y ^ 2 - x ^ 3) ^ 2) _ hw
  have h2 := r_poly n g x y
  have hw18 : (y ^ 2 - x ^ 3) ^ 18 ≠ 0 := pow_ne_zero _ hw
  apply mul_right_cancel₀ hw18
  calc _ = θE n (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6)
        ((x * y * (y ^ 2 - 3 * x ^ 3) - 2 * g * (y ^ 2 - x ^ 3) ^ 2) / (y ^ 2 - x ^ 3) ^ 2) *
        (y ^ 2 - x ^ 3) ^ 20 := by ring
    _ = _ := by rw [h1, h2]

end Generic

/-- `r_n` as a polynomial in `S₂ = k'[x', y']`. -/
def rK (n : Fin 11) : S₂ := rE n (MvPolynomial.C γ) (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem algebraMap_rK (n : Fin 11) : algebraMap S₂ K' (rK n) = rE n γK xK yK := by
  rw [rK, rE_map]
  rfl

/-- `ι(ξ_n) = r_n(γ, x', y')`. -/
theorem ι_ξ (n : Fin 11) : ι (ξ n) = algebraMap S₂ K' (rK n) := by
  rw [algebraMap_rK, ξ, map_mul, map_pow, θE_map, ι_aL, ι_bL, ι_σL, ι_wL]
  exact r_ident n xK yK γK wK_ne_zero'

/-! ## `1, γ, …, γ¹⁰` are linearly independent over `ι(L)` -/

/-- `c = (ab³ - 3a⁴b - σ¹¹)/2` in `𝔽₁₁[a, b, σ]`. -/
def cP : P₃ := 6 * (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 -
  3 * MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 - MvPolynomial.X 2 ^ 11)

theorem cL_eq : cL = algebraMap P₃ L cP := by
  simp [cL, cP, aL, bL, σL, map_ofNat]

instance : CharP P₃ 11 := charP_of_injective_algebraMap (algebraMap F₁₁ P₃).injective 11

/-- `c` is not an `11`th power in `L`: `∂c/∂a = 6(b³ - 12a³b) ≠ 0`. -/
theorem cL_not_pow (y : L) : y ^ 11 ≠ cL := by
  intro h
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := P₃) y
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqL : algebraMap P₃ L q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective P₃ L)).mpr hq0
  have h1 : p ^ 11 = cP * q ^ 11 := by
    apply IsFractionRing.injective P₃ L
    rw [map_pow, map_mul, map_pow, ← cL_eq, ← h, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hqL)]
  have h11 : (11 : P₃) = 0 := by exact_mod_cast CharP.cast_eq_zero P₃ 11
  have h2 := congrArg (MvPolynomial.pderiv (0 : Fin 3)) h1
  rw [Derivation.leibniz_pow, Derivation.leibniz, Derivation.leibniz_pow] at h2
  simp only [Nat.add_one_sub_one, nsmul_eq_mul, Nat.cast_ofNat, h11, zero_mul, smul_eq_mul,
    mul_zero, zero_smul, zero_add] at h2
  have h3 : MvPolynomial.pderiv (0 : Fin 3) cP = 0 := by
    rcases mul_eq_zero.mp h2.symm with h4 | h4
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h4) hq0
    · exact h4
  have h4 := congrArg (MvPolynomial.eval ![(0 : F₁₁), 1, 0]) h3
  simp [cP, MvPolynomial.pderiv_X] at h4
  exact absurd h4 (by decide)

theorem irreducible_T : Irreducible (Polynomial.X ^ 11 - Polynomial.C cL) :=
  X_pow_sub_C_irreducible_of_prime fact11.out cL_not_pow

/-- `1, γ, …, γ¹⁰` are linearly independent over `ι(L)`. -/
theorem decomp_unique (f : Fin 11 → L) (h : ∑ i, ι (f i) * γK ^ (i : ℕ) = 0) (i : Fin 11) :
    f i = 0 := by
  letI : Algebra L K' := ι.toAlgebra
  have hqm : (Polynomial.X ^ 11 - Polynomial.C cL).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hroot : Polynomial.aeval γK (Polynomial.X ^ 11 - Polynomial.C cL) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change γK ^ 11 - ι cL = 0
    rw [ι_cL, sub_self]
  have hmin : minpoly L γK = Polynomial.X ^ 11 - Polynomial.C cL :=
    (minpoly.eq_of_irreducible_of_monic irreducible_T hroot hqm).symm
  set p : Polynomial L := ∑ j : Fin 11, Polynomial.C (f j) * Polynomial.X ^ (j : ℕ)
  have hp : Polynomial.aeval γK p = 0 := by
    simp only [p, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    exact h
  have hdvd : Polynomial.X ^ 11 - Polynomial.C cL ∣ p := hmin ▸ minpoly.dvd L γK hp
  have hdeg : p.degree < (Polynomial.X ^ 11 - Polynomial.C cL).degree := by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]
    exact Polynomial.degree_sum_fin_lt f
  have hp0 : p = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have := congrArg (fun r ↦ Polynomial.coeff r (i : ℕ)) hp0
  simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using this

/-! ## `k' = k[γ]` -/

instance : IsScalarTower F₁₁ k k' := IsScalarTower.of_algebraMap_eq fun r ↦
  RingHom.congr_fun (Subsingleton.elim (α := F₁₁ →+* k') (algebraMap F₁₁ k')
    ((algebraMap k k').comp (algebraMap F₁₁ k))) r

theorem frobenius_poly (r : Pγ) : r ^ 11 = Polynomial.expand F₁₁ 11 r := by
  have h := Polynomial.map_frobenius_expand 11 r
  rw [ZMod.frobenius_zmod, Polynomial.map_id] at h
  exact h.symm

/-- Every element of `k'` is `μ q(γ)` with `μ ∈ k` and `q ∈ 𝔽₁₁[γ]`. -/
theorem k'_decomp (z : k') : ∃ (μ : k) (q : Pγ), z = algebraMap k k' μ * Polynomial.aeval γ q := by
  obtain ⟨q, r, hr, rfl⟩ := IsFractionRing.div_surjective (A := Pγ) z
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hev (t : Pγ) : algebraMap Pγ k' t = Polynomial.aeval γ t := by
    rw [γ, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  have hr' : Polynomial.aeval γ r ≠ 0 := by
    rw [← hev]
    exact (map_ne_zero_iff _ (IsFractionRing.injective Pγ k')).mpr hr0
  have hfrob : Polynomial.aeval γ r ^ 11 = algebraMap k k' (Polynomial.aeval c r) := by
    rw [← map_pow, frobenius_poly, Polynomial.expand_aeval, ← algebraMap_c,
      Polynomial.aeval_algebraMap_apply]
  have hc : Polynomial.aeval c r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hfrob
    exact hr' (pow_eq_zero_iff (by norm_num) |>.mp hfrob)
  refine ⟨(Polynomial.aeval c r)⁻¹, q * r ^ 10, ?_⟩
  rw [hev, hev, map_inv₀, ← hfrob, map_mul, map_pow]
  field_simp

/-! ## The decomposition of `S = k'[x', y']` -/

/-- `ι` on the chart `P`. -/
def ιP : chartP →+* K' := ι.comp chartP.val.toRingHom

/-- Evaluation `P[T] → K'` at `T = γ`. -/
def evalP : Polynomial chartP →+* K' := Polynomial.eval₂RingHom ιP γK

theorem evalP_C (f : chartP) : evalP (Polynomial.C f) = ι f := Polynomial.eval₂_C _ _

theorem evalP_X : evalP Polynomial.X = γK := Polynomial.eval₂_X _ _

set_option synthInstance.maxHeartbeats 200000 in
theorem sum_mem_range (ρ : Fin 11 → chartP) :
    ∑ i, ι (ρ i) * γK ^ (i : ℕ) ∈ evalP.rangeS :=
  ⟨∑ i, Polynomial.C (ρ i) * Polynomial.X ^ (i : ℕ), by simp [evalP_C, evalP_X]⟩

theorem algebraMap_k_mem (μ : k) : algebraMap k L μ ∈ chartP := chartP.algebraMap_mem μ

theorem xK_mem_range : xK ∈ evalP.rangeS := by
  have h := sum_mem_range (fun n ↦ ⟨ξ n, ξ_mem n⟩)
  have hx : xK = ∑ i : Fin 11, ι (ξ i) * γK ^ (i : ℕ) := by
    rw [xK_eq]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [ξ, map_mul, map_pow, θE_map, ι_aL, ι_bL, ι_σL, ι_wL]
    rfl
  rw [hx]
  exact h

theorem yK_mem_range : yK ∈ evalP.rangeS := by
  have hy : yK = ∑ i : Fin 10, ι ((6 * ((i : ℕ) + 1) : L) * ξ i.succ) * γK ^ (i : ℕ) := by
    rw [yK_eq]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [ξ, map_mul, map_pow, map_add, map_natCast, map_ofNat, map_one, θE_map, ι_aL, ι_bL,
      ι_σL, ι_wL, vK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hy]
  refine evalP.rangeS.sum_mem fun n _ ↦ ?_
  refine evalP.rangeS.mul_mem ⟨Polynomial.C ⟨_, chartP.mul_mem (by
    have := natCast_mem chartP (6 * ((n : ℕ) + 1))
    push_cast at this
    exact this) (ξ_mem n.succ)⟩, by simp [evalP_C]⟩ ?_
  exact evalP.rangeS.pow_mem ⟨Polynomial.X, evalP_X⟩ _

theorem k'_mem_range (z : k') : algebraMap k' K' z ∈ evalP.rangeS := by
  obtain ⟨μ, q, rfl⟩ := k'_decomp z
  rw [map_mul]
  refine evalP.rangeS.mul_mem ⟨Polynomial.C ⟨_, algebraMap_k_mem μ⟩, ?_⟩ ?_
  · rw [evalP_C]
    change ι (algebraMap k L μ) = _
    rw [ι_algebraMap, algebraMap_k_K']
  · induction q using Polynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (algebraMap F₁₁ chartP a), ?_⟩
      rw [evalP_C, Polynomial.aeval_C]
      exact RingHom.congr_fun (Subsingleton.elim (α := F₁₁ →+* K')
        (ι.comp ((chartP.val.toRingHom).comp (algebraMap F₁₁ chartP)))
        ((algebraMap k' K').comp (algebraMap F₁₁ k'))) a
    | add p q hp hq => simpa only [map_add] using evalP.rangeS.add_mem hp hq
    | monomial n a ih =>
      have : algebraMap k' K' (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n + 1))) =
          algebraMap k' K' (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n)) * γK := by
        simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, γK]
        ring
      rw [this]
      exact evalP.rangeS.mul_mem ih ⟨Polynomial.X, evalP_X⟩

theorem S_mem_range (s : S₂) : algebraMap S₂ K' s ∈ evalP.rangeS := by
  induction s using MvPolynomial.induction_on with
  | C z =>
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact k'_mem_range z
  | add p q hp hq => simpa only [map_add] using evalP.rangeS.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    refine evalP.rangeS.mul_mem hp ?_
    fin_cases j
    · exact xK_mem_range
    · exact yK_mem_range

/-- `T¹¹ - c` over the chart `P`. -/
def qT : Polynomial chartP := Polynomial.X ^ 11 - Polynomial.C (algebraMap k chartP c)

theorem qT_monic : qT.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)

theorem evalP_qT : evalP qT = 0 := by
  change Polynomial.eval₂ ιP γK qT = 0
  rw [qT, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  change γK ^ 11 - ι (algebraMap k L c) = 0
  rw [algebraMap_c_L, ι_cL, sub_self]

/-- Every element of `S` is `Σ_{i<11} ι(ρ_i) γ^i` with `ρ_i ∈ P`. -/
theorem decomp_exists (s : S₂) :
    ∃ ρ : Fin 11 → chartP, algebraMap S₂ K' s = ∑ i, ι (ρ i) * γK ^ (i : ℕ) := by
  obtain ⟨p, hp⟩ := S_mem_range s
  have hdeg : (p %ₘ qT).natDegree < 11 := by
    have := Polynomial.natDegree_modByMonic_lt p qT_monic (by
      intro h1
      have := congrArg Polynomial.natDegree h1
      rw [qT, Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_one] at this
      omega)
    rwa [qT, Polynomial.natDegree_X_pow_sub_C] at this
  refine ⟨fun i ↦ (p %ₘ qT).coeff i, ?_⟩
  have hmod : evalP p = evalP (p %ₘ qT) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p qT]
    rw [RingHom.map_add, RingHom.map_mul, evalP_qT, zero_mul, add_zero]
  rw [← hp, hmod, evalP, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_eq_sum_range' _ hdeg]
  rw [Finset.sum_range (fun i ↦ ιP ((p %ₘ qT).coeff i) * γK ^ i)]
  rfl

/-- An element of `L` lies in `P` when its image in `K'` is a polynomial. -/
theorem mem_chartP_of_ι {f : L} {s : S₂} (h : ι f = algebraMap S₂ K' s) : f ∈ chartP := by
  obtain ⟨ρ, hρ⟩ := decomp_exists s
  have h0 := decomp_unique (fun i ↦ (if i = 0 then f else 0) - ρ i) (by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← hρ, ← h, Fin.sum_univ_succ]
    simp) 0
  simp only [↓reduceIte, sub_eq_zero] at h0
  rw [h0]
  exact (ρ 0).2

/-- The image of `P` lies in `S`. -/
theorem ι_chartP {f : L} (hf : f ∈ chartP) : ∃ s : S₂, ι f = algebraMap S₂ K' s := by
  induction hf using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨n, rfl⟩ := hz
    exact ⟨rK n, ι_ξ n⟩
  | algebraMap μ =>
    refine ⟨MvPolynomial.C (algebraMap k k' μ), ?_⟩
    rw [ι_algebraMap, algebraMap_k_K', ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k' S₂ K']
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [map_add, map_add, hs, ht]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s * t, by rw [map_mul, map_mul, hs, ht]⟩

/-- `s¹¹ ∈ ι(P)` for every `s ∈ S`. -/
theorem frob_mem (s : S₂) : ∃ t ∈ chartP, ι t = (algebraMap S₂ K' s) ^ 11 := by
  obtain ⟨ρ, hρ⟩ := decomp_exists s
  refine ⟨∑ i : Fin 11, (ρ i : L) ^ 11 * (algebraMap k L c) ^ (i : ℕ), chartP.sum_mem fun i _ ↦
    chartP.mul_mem (chartP.pow_mem (ρ i).2 _) (chartP.pow_mem (algebraMap_k_mem c) _), ?_⟩
  rw [hρ, sum_pow_char, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, map_pow, algebraMap_c_L, ι_cL, mul_pow, ← pow_mul, ← pow_mul, mul_comm 11]

end
end Geonormal.P11

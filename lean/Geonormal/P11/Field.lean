import Mathlib

/-! # The fields of the characteristic-11 example

The function field of the surface of Proposition `prop:p11` is the rational function field
`L = 𝔽₁₁(a, b, σ)`. The base field `k = 𝔽₁₁(c)` embeds by `c = (ab³ - 3a⁴b - σ¹¹)/2`, and we put
`u = b² - a³`.

The auxiliary field `K' = k'(x', y')`, with `k' = 𝔽₁₁(γ)` and `γ¹¹ = c`, is `L ⊗_k k'`. The
embedding `ι : L → K'` sends `a ↦ x'¹¹/w'⁴`, `b ↦ y'¹¹/w'⁶` and `σ ↦ s/w'² - 2γ`, where
`w' = y'² - x'³` and `s = x'y'(y'² - 3x'³)`. In `K'` the element `x'` is
`Σ_k ι(θ_k/u²) γ^k`, where `θ_k = (2∂_σ)^k θ / k!` and `θ` is the polynomial of the
manuscript.
-/

namespace Geonormal.P11

open MvPolynomial

noncomputable section

instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

abbrev F₁₁ := ZMod 11

/-! ## The base field `k = 𝔽₁₁(c)` and its extension `k' = 𝔽₁₁(γ)` -/

abbrev P₁ := MvPolynomial (Fin 1) F₁₁
/-- The base field `k = 𝔽₁₁(c)`. -/
abbrev k := FractionRing P₁

/-- The transcendental generator `c` of `k`. -/
def c : k := algebraMap P₁ k (X 0)

abbrev Pγ := Polynomial F₁₁
/-- The field `k' = 𝔽₁₁(γ)`; it becomes a purely inseparable extension of `k` by `c ↦ γ¹¹`. -/
abbrev k' := FractionRing Pγ

/-- The generator `γ` of `k'`. -/
def γ : k' := algebraMap Pγ k' Polynomial.X

theorem γ_transcendental : Transcendental F₁₁ γ := by
  have h : Transcendental F₁₁ (Polynomial.X : Pγ) := Polynomial.transcendental_X F₁₁
  exact (transcendental_algebraMap_iff (IsFractionRing.injective Pγ k')).mpr h

theorem γ_pow_transcendental : Transcendental F₁₁ (γ ^ 11) :=
  γ_transcendental.pow (by norm_num)

theorem kToK'_injective :
    Function.Injective (MvPolynomial.aeval (R := F₁₁) fun _ : Fin 1 ↦ γ ^ 11) :=
  algebraicIndependent_unique_type_iff.mpr γ_pow_transcendental

instance algebraKK' : Algebra k k' :=
  (IsFractionRing.lift (A := P₁) (g := (MvPolynomial.aeval fun _ : Fin 1 ↦ γ ^ 11).toRingHom)
    kToK'_injective).toAlgebra

theorem algebraMap_c : algebraMap k k' c = γ ^ 11 := by
  change IsFractionRing.lift _ (algebraMap P₁ k (X 0)) = _
  rw [IsFractionRing.lift_algebraMap]
  simp

/-! ## The auxiliary field `K' = k'(x', y')` -/

abbrev S₂ := MvPolynomial (Fin 2) k'
/-- The auxiliary field `K' = k'(x', y')`. -/
abbrev K' := FractionRing S₂

example : IsScalarTower k k' K' := inferInstance

instance : CharP k 11 := charP_of_injective_algebraMap (algebraMap F₁₁ k).injective 11
instance : CharP k' 11 := charP_of_injective_algebraMap (algebraMap F₁₁ k').injective 11
instance : CharP K' 11 := charP_of_injective_algebraMap (algebraMap F₁₁ K').injective 11

def xK : K' := algebraMap S₂ K' (X 0)
def yK : K' := algebraMap S₂ K' (X 1)
def γK : K' := algebraMap k' K' γ
/-- `w' = y'² - x'³`; in `L` it is `1/u`. -/
def wK : K' := yK ^ 2 - xK ^ 3
/-- `s = x'y'(y'² - 3x'³)`. -/
def sK : K' := xK * yK * (yK ^ 2 - 3 * xK ^ 3)

theorem wK_ne_zero : wK ≠ 0 := by
  intro h
  have h' : algebraMap S₂ K' (X 1 ^ 2 - X 0 ^ 3) = 0 := by
    simpa [wK, xK, yK] using h
  rw [map_eq_zero_iff _ (IsFractionRing.injective S₂ K')] at h'
  have := congrArg (MvPolynomial.eval ![(0 : k'), 1]) h'
  simp at this

/-! ## The polynomial `θ` and its rescaled `σ`-derivatives

These are written over an arbitrary commutative ring, so that they specialize to `L` and `K'`.
Here `a, b, s` stand for `a, b, σ`. -/

section Theta

variable {R : Type*} [CommRing R]

/-- `θ = θ₀`, the polynomial of the manuscript. -/
def θ0 (a b s : R) : R := -s ^ 10 + 4 * a * s ^ 8 - 5 * b * s ^ 7 + 4 * a ^ 2 * s ^ 6 + 4 *
    a * b * s ^ 5 - 4 * b ^ 2 * s ^ 4 + 5 * a ^ 3 * s ^ 4 + 2 * a ^ 2 * b * s ^ 3 + a * b ^
    2 * s ^ 2 - 2 * a ^ 4 * s ^ 2 + b ^ 3 * s - 5 * a ^ 3 * b * s - 3 * a ^ 2 * b ^ 2 + a ^
    5

/-- `θ_1 = (2∂_σ)^1 θ / 1!`. -/
def θ1 (a b s : R) : R := 2 * s ^ 9 - 2 * a * s ^ 7 - 4 * b * s ^ 6 + 4 * a ^ 2 * s ^ 5 - 4
    * a * b * s ^ 4 + b ^ 2 * s ^ 3 - 4 * a ^ 3 * s ^ 3 + a ^ 2 * b * s ^ 2 + 4 * a * b ^ 2
    * s + 3 * a ^ 4 * s + 2 * b ^ 3 + a ^ 3 * b

/-- `θ_2 = (2∂_σ)^2 θ / 2!`. -/
def θ2 (a b s : R) : R := -4 * s ^ 8 - 3 * a * s ^ 6 - 2 * b * s ^ 5 - 2 * a ^ 2 * s ^ 4 - 5
    * a * b * s ^ 3 + 3 * b ^ 2 * s ^ 2 - a ^ 3 * s ^ 2 + 2 * a ^ 2 * b * s + 4 * a * b ^ 2
    + 3 * a ^ 4

/-- `θ_3 = (2∂_σ)^3 θ / 3!`. -/
def θ3 (a b s : R) : R := -3 * s ^ 7 - a * s ^ 5 - 3 * b * s ^ 4 + 2 * a ^ 2 * s ^ 3 + a * b
    * s ^ 2 + 4 * b ^ 2 * s - 5 * a ^ 3 * s + 5 * a ^ 2 * b

/-- `θ_4 = (2∂_σ)^4 θ / 4!`. -/
def θ4 (a b s : R) : R := -5 * s ^ 6 + 3 * a * s ^ 4 + 5 * b * s ^ 3 + 3 * a ^ 2 * s ^ 2 + a
    * b * s + 2 * b ^ 2 + 3 * a ^ 3

/-- `θ_5 = (2∂_σ)^5 θ / 5!`. -/
def θ5 (a b s : R) : R := -s ^ 5 - 4 * a * s ^ 3 - 5 * b * s ^ 2 - 2 * a ^ 2 * s - 4 * a * b

/-- `θ_6 = (2∂_σ)^6 θ / 6!`. -/
def θ6 (a b s : R) : R := 2 * s ^ 4 - 4 * a * s ^ 2 + 4 * b * s + 3 * a ^ 2

/-- `θ_7 = (2∂_σ)^7 θ / 7!`. -/
def θ7 (a b s : R) : R := -4 * s ^ 3 + 4 * a * s - 2 * b

/-- `θ_8 = (2∂_σ)^8 θ / 8!`. -/
def θ8 (a _b s : R) : R := -3 * s ^ 2 + a

/-- `θ_9 = (2∂_σ)^9 θ / 9!`. -/
def θ9 (_a _b s : R) : R := -5 * s

/-- `θ_10 = (2∂_σ)^10 θ / 10!`. -/
def θ10 (_a _b _s : R) : R := -1

/-- The eleven components `θ_k`. -/
def θE (n : Fin 11) (a b s : R) : R :=
  ![θ0 a b s, θ1 a b s, θ2 a b s, θ3 a b s, θ4 a b s, θ5 a b s, θ6 a b s, θ7 a b s, θ8 a b s,
    θ9 a b s, θ10 a b s] n

/-- `∂_σ θ`. -/
def dθ (a b s : R) : R := s ^ 9 - a * s ^ 7 - 2 * b * s ^ 6 + 2 * a ^ 2 * s ^ 5 - 2 * a * b
    * s ^ 4 - 5 * b ^ 2 * s ^ 3 - 2 * a ^ 3 * s ^ 3 - 5 * a ^ 2 * b * s ^ 2 + 2 * a * b ^ 2
    * s - 4 * a ^ 4 * s + b ^ 3 - 5 * a ^ 3 * b

end Theta

/-! ## Identities in characteristic `11` -/

section Identities

theorem θE_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 11) (a b s : R) :
    f (θE n a b s) = θE n (f a) (f b) (f s) := by
  fin_cases n <;> simp [θE, θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10, map_ofNat]

theorem dθ_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b s : R) :
    f (dθ a b s) = dθ (f a) (f b) (f s) := by
  simp [dθ, map_ofNat]

variable {F : Type*} [Field F] [CharP F 11]

/-- Taylor expansion: `Σ θ_k γ^k = θ(a, b, σ + 2γ)`, since `θ` has degree `10` in `σ`. -/
theorem taylor (a b s g : F) :
    ∑ n : Fin 11, θE n a b s * g ^ (n : ℕ) = θ0 a b (s + 2 * g) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, θE]
  simp [θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10]
  grind

/-- The derivative of the Taylor expansion: `Σ (k+1)/2 · θ_{k+1} γ^k = (∂_σ θ)(a, b, σ + 2γ)`. -/
theorem taylor_d (a b s g : F) :
    ∑ n : Fin 10, (6 * ((n : ℕ) + 1) : F) * θE n.succ a b s * g ^ (n : ℕ) = dθ a b (s + 2 * g) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, θE]
  simp [θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10, dθ]
  grind

/-- `x = θ(a, b, τ)` in the model `y'² = x'³ + w`, cleared of denominators. -/
theorem base_x (x y : F) :
    x * (y ^ 2 - x ^ 3) ^ 18 = θ0 (x ^ 11) (y ^ 11) (x * y * (y ^ 2 - 3 * x ^ 3)) := by
  simp only [θ0]
  grind

/-- `y = u ∂_τ θ(a, b, τ)`, cleared of denominators. -/
theorem base_y (x y : F) :
    y * (y ^ 2 - x ^ 3) ^ 16 = dθ (x ^ 11) (y ^ 11) (x * y * (y ^ 2 - 3 * x ^ 3)) := by
  simp only [dθ]
  grind

omit [CharP F 11] in
/-- `θ` is weighted homogeneous of degree `10` for the weights `(2, 3, 1)`. -/
theorem θ0_homog (A B s w : F) (hw : w ≠ 0) :
    θ0 (A / w ^ 4) (B / w ^ 6) (s / w ^ 2) = θ0 A B s / w ^ 20 := by
  simp only [θ0]
  field_simp

omit [CharP F 11] in
/-- `∂_σ θ` is weighted homogeneous of degree `9`. -/
theorem dθ_homog (A B s w : F) (hw : w ≠ 0) :
    dθ (A / w ^ 4) (B / w ^ 6) (s / w ^ 2) = dθ A B s / w ^ 18 := by
  simp only [dθ]
  field_simp

end Identities

/-! ## The identities in the auxiliary field -/

section Generic

variable {F : Type*} [Field F] [CharP F 11] (x y g : F)

/-- `u = b² - a³` maps to `1/w'`. -/
theorem u_ident (hw : y ^ 2 - x ^ 3 ≠ 0) :
    (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) ^ 2 - (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) ^ 3 = (y ^ 2 - x ^ 3)⁻¹ := by
  field_simp
  grind

/-- `c = (ab³ - 3a⁴b - σ¹¹)/2` maps to `γ¹¹`. -/
theorem c_ident (hw : y ^ 2 - x ^ 3 ≠ 0) :
    6 * (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4 * (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) ^ 3 -
      3 * (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) ^ 4 * (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) -
      (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) ^ 11) = g ^ 11 := by
  have h : (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) ^ 11 =
      (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2) ^ 11 - 2 * g ^ 11 := by
    rw [sub_pow_char, mul_pow]
    norm_num
    grind
  rw [h]
  field_simp
  grind

/-- `x' = Σ_k θ_k(a, b, σ) w'² γ^k`. -/
theorem x_ident (hw : y ^ 2 - x ^ 3 ≠ 0) :
    x = ∑ n : Fin 11, θE n (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6)
      (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) * (y ^ 2 - x ^ 3) ^ 2 * g ^ (n : ℕ) := by
  have h := taylor (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6)
    (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) g
  simp only [sub_add_cancel] at h
  rw [θ0_homog _ _ _ _ hw, ← base_x] at h
  calc x = (y ^ 2 - x ^ 3) ^ 2 * (x * (y ^ 2 - x ^ 3) ^ 18 / (y ^ 2 - x ^ 3) ^ 20) := by
        field_simp
    _ = _ := by
        rw [← h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        ring

/-- `y' = Σ_k (k+1)/2 · θ_{k+1}(a, b, σ) w'² γ^k`. -/
theorem y_ident (hw : y ^ 2 - x ^ 3 ≠ 0) :
    y = ∑ n : Fin 10, (6 * ((n : ℕ) + 1) : F) * θE n.succ (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4)
      (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6) (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) *
      (y ^ 2 - x ^ 3) ^ 2 * g ^ (n : ℕ) := by
  have h := taylor_d (x ^ 11 / (y ^ 2 - x ^ 3) ^ 4) (y ^ 11 / (y ^ 2 - x ^ 3) ^ 6)
    (x * y * (y ^ 2 - 3 * x ^ 3) / (y ^ 2 - x ^ 3) ^ 2 - 2 * g) g
  simp only [sub_add_cancel] at h
  rw [dθ_homog _ _ _ _ hw, ← base_y] at h
  calc y = (y ^ 2 - x ^ 3) ^ 2 * (y * (y ^ 2 - x ^ 3) ^ 16 / (y ^ 2 - x ^ 3) ^ 18) := by
        field_simp
    _ = _ := by
        rw [← h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        ring

end Generic

/-! ## The embedding `ι : L → K'` -/

theorem θE_mem {K : Type*} [CommRing K] (T : Subring K) (n : Fin 11) {a b s : K} (ha : a ∈ T)
    (hb : b ∈ T) (hs : s ∈ T) : θE n a b s ∈ T := by
  have h := θE_map T.subtype n ⟨a, ha⟩ ⟨b, hb⟩ ⟨s, hs⟩
  simp only [Subring.coe_subtype] at h
  rw [← h]
  exact Subtype.prop _

/-- The images of `a, b, σ` in `K'`. -/
def vK : Fin 3 → K' := ![xK ^ 11 / wK ^ 4, yK ^ 11 / wK ^ 6, sK / wK ^ 2 - 2 * γK]

theorem wK_ne_zero' : yK ^ 2 - xK ^ 3 ≠ 0 := wK_ne_zero

theorem uK_eq : vK 1 ^ 2 - vK 0 ^ 3 = wK⁻¹ := u_ident xK yK wK_ne_zero'

theorem cK_eq : 6 * (vK 0 * vK 1 ^ 3 - 3 * vK 0 ^ 4 * vK 1 - vK 2 ^ 11) = γK ^ 11 :=
  c_ident xK yK γK wK_ne_zero'

theorem xK_eq : xK = ∑ n : Fin 11, θE n (vK 0) (vK 1) (vK 2) * wK ^ 2 * γK ^ (n : ℕ) :=
  x_ident xK yK γK wK_ne_zero'

theorem yK_eq : yK = ∑ n : Fin 10, (6 * ((n : ℕ) + 1) : K') * θE n.succ (vK 0) (vK 1) (vK 2) *
    wK ^ 2 * γK ^ (n : ℕ) :=
  y_ident xK yK γK wK_ne_zero'

theorem standard_independent :
    AlgebraicIndependent F₁₁ (Sum.elim ![xK, yK] (algebraMap k' K' ∘ ![γ])) := by
  have hx : AlgebraicIndependent F₁₁ ![γ] :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using γ_transcendental)
  have hy : AlgebraicIndependent k' ![xK, yK] := by
    have h := (MvPolynomial.algebraicIndependent_X (Fin 2) k').map'
      (f := IsScalarTower.toAlgHom k' S₂ K') (IsFractionRing.injective S₂ K')
    convert h using 1
    ext j
    fin_cases j <;> rfl
  exact AlgebraicIndependent.sumElim_comp hx hy

theorem three_le_trdeg : (3 : Cardinal) ≤ Algebra.trdeg F₁₁ K' := by
  have := standard_independent.cardinalMk_le_trdeg
  simpa using this

/-- `K'` is generated over `𝔽₁₁` by `γ, x', y'`. -/
theorem standard_generation : IntermediateField.adjoin F₁₁ ({γK, xK, yK} : Set K') = ⊤ := by
  set M := IntermediateField.adjoin F₁₁ ({γK, xK, yK} : Set K')
  have hγ : γK ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have hx : xK ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have hy : yK ∈ M := IntermediateField.subset_adjoin _ _ (by simp)
  have hPγ (q : Pγ) : algebraMap k' K' (algebraMap Pγ k' q) ∈ M := by
    induction q using Polynomial.induction_on with
    | C a =>
      have h := RingHom.congr_fun (Subsingleton.elim
        (((algebraMap k' K').comp (algebraMap Pγ k')).comp Polynomial.C) (algebraMap F₁₁ K')) a
      simp only [RingHom.coe_comp, Function.comp_apply] at h
      rw [h]
      exact M.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using M.add_mem hp hq
    | monomial n a ih =>
      have : algebraMap k' K' (algebraMap Pγ k' (Polynomial.C a * Polynomial.X ^ (n + 1))) =
          algebraMap k' K' (algebraMap Pγ k' (Polynomial.C a * Polynomial.X ^ n)) * γK := by
        simp only [map_mul, map_pow, γK, γ]
        ring
      rw [this]
      exact M.mul_mem ih hγ
  have hk (z : k') : algebraMap k' K' z ∈ M := by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := Pγ) z
    rw [map_div₀]
    exact M.div_mem (hPγ u) (hPγ v)
  have hR (p : S₂) : algebraMap S₂ K' p ∈ M := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hk a
    | add p q hp hq => simpa only [map_add] using M.add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine M.mul_mem hp ?_
      fin_cases j
      · exact hx
      · exact hy
  rw [eq_top_iff]
  intro z _
  obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := S₂) z
  exact M.div_mem (hR u) (hR v)

theorem generation_vK : IntermediateField.adjoin F₁₁ (Set.range vK ∪ {γK}) = ⊤ := by
  set N := IntermediateField.adjoin F₁₁ (Set.range vK ∪ {γK})
  have hv (i : Fin 3) : vK i ∈ N := IntermediateField.subset_adjoin _ _ (Or.inl ⟨i, rfl⟩)
  have hγ : γK ∈ N := IntermediateField.subset_adjoin _ _ (Or.inr rfl)
  have hw : wK ∈ N := by
    have h : wK = (vK 1 ^ 2 - vK 0 ^ 3)⁻¹ := by rw [uK_eq, inv_inv]
    rw [h]
    exact N.inv_mem (N.sub_mem (N.pow_mem (hv 1) 2) (N.pow_mem (hv 0) 3))
  have hθ (n : Fin 11) : θE n (vK 0) (vK 1) (vK 2) ∈ N :=
    θE_mem N.toSubfield.toSubring n (hv 0) (hv 1) (hv 2)
  have hx : xK ∈ N := by
    rw [xK_eq]
    exact N.sum_mem fun n _ ↦ N.mul_mem (N.mul_mem (hθ n) (N.pow_mem hw 2)) (N.pow_mem hγ (n : ℕ))
  have hy : yK ∈ N := by
    rw [yK_eq]
    refine N.sum_mem fun n _ ↦ N.mul_mem (N.mul_mem (N.mul_mem ?_ (hθ _)) (N.pow_mem hw 2))
      (N.pow_mem hγ (n : ℕ))
    have h := natCast_mem N (6 * ((n : ℕ) + 1))
    push_cast at h
    exact h
  rw [eq_top_iff, ← standard_generation, IntermediateField.adjoin_le_iff]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hγ
  · exact hx
  · exact hy

theorem γK_pow_transcendental : Transcendental F₁₁ (γK ^ 11) := by
  rw [γK, ← map_pow]
  exact (transcendental_algebraMap_iff (algebraMap k' K').injective).mpr γ_pow_transcendental

theorem vK_algebraic : Algebra.IsAlgebraic (Algebra.adjoin F₁₁ (Set.range vK)) K' := by
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  set M := IntermediateField.adjoin F₁₁ (Set.range vK)
  have hv (i : Fin 3) : vK i ∈ M := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have hc : γK ^ 11 ∈ M := by
    rw [← cK_eq]
    have h6 : (6 : K') ∈ M := by simpa using natCast_mem M 6
    have h3 : (3 : K') ∈ M := by simpa using natCast_mem M 3
    exact M.mul_mem h6 (M.sub_mem (M.sub_mem (M.mul_mem (hv 0) (M.pow_mem (hv 1) 3))
      (M.mul_mem (M.mul_mem h3 (M.pow_mem (hv 0) 4)) (hv 1))) (M.pow_mem (hv 2) 11))
  have hint : IsIntegral M γK := by
    refine ⟨Polynomial.X ^ 11 - Polynomial.C ⟨γK ^ 11, hc⟩, Polynomial.monic_X_pow_sub_C _ (by norm_num),
      ?_⟩
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  have htop : IntermediateField.adjoin M {γK} = ⊤ := by
    apply IntermediateField.restrictScalars_injective F₁₁
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top]
    exact generation_vK
  have : FiniteDimensional M (IntermediateField.adjoin M {γK}) :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [htop] at this
  have : FiniteDimensional M K' := IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  exact Algebra.IsAlgebraic.of_finite M K'

/-- `ι(a), ι(b), ι(σ)` are algebraically independent over `𝔽₁₁`. -/
theorem vK_independent : AlgebraicIndependent F₁₁ vK := by
  have := vK_algebraic
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₁₁ vK
    (by simpa using three_le_trdeg)).1

abbrev P₃ := MvPolynomial (Fin 3) F₁₁

/-- The function field `L = 𝔽₁₁(a, b, σ)`. -/
abbrev L := FractionRing P₃

def aL : L := algebraMap P₃ L (X 0)
def bL : L := algebraMap P₃ L (X 1)
def σL : L := algebraMap P₃ L (X 2)

/-- The embedding `ι : L → K'`. -/
def ι : L →+* K' :=
  IsFractionRing.lift (A := P₃) (g := (MvPolynomial.aeval vK).toRingHom) vK_independent

theorem ι_P₃ (p : P₃) : ι (algebraMap P₃ L p) = MvPolynomial.aeval vK p :=
  IsFractionRing.lift_algebraMap _ _

theorem ι_aL : ι aL = xK ^ 11 / wK ^ 4 := by simp [aL, ι_P₃, vK]
theorem ι_bL : ι bL = yK ^ 11 / wK ^ 6 := by simp [bL, ι_P₃, vK]
theorem ι_σL : ι σL = sK / wK ^ 2 - 2 * γK := by simp [σL, ι_P₃, vK]

/-- `c = (ab³ - 3a⁴b - σ¹¹)/2` in `L`. -/
def cL : L := 6 * (aL * bL ^ 3 - 3 * aL ^ 4 * bL - σL ^ 11)

theorem ι_cL : ι cL = γK ^ 11 := by
  have h := cK_eq
  simp only [vK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  simp only [cL, map_mul, map_sub, map_pow, map_ofNat, ι_aL, ι_bL, ι_σL]
  exact h

/-- `ι` as a homomorphism of `𝔽₁₁`-algebras. -/
def ιA : L →ₐ[F₁₁] K' where
  toRingHom := ι
  commutes' r :=
    RingHom.congr_fun (Subsingleton.elim (ι.comp (algebraMap F₁₁ L)) (algebraMap F₁₁ K')) r

theorem cL_transcendental : Transcendental F₁₁ cL := by
  intro h
  apply γK_pow_transcendental
  rw [← ι_cL]
  exact h.algHom ιA

theorem cHom_injective :
    Function.Injective (MvPolynomial.aeval (R := F₁₁) fun _ : Fin 1 ↦ cL) :=
  algebraicIndependent_unique_type_iff.mpr cL_transcendental

instance algebraKL : Algebra k L :=
  (IsFractionRing.lift (A := P₁) (g := (MvPolynomial.aeval fun _ : Fin 1 ↦ cL).toRingHom)
    cHom_injective).toAlgebra

instance : IsScalarTower F₁₁ k L := IsScalarTower.of_algebraMap_eq fun r ↦
  RingHom.congr_fun (Subsingleton.elim (α := F₁₁ →+* L) (algebraMap F₁₁ L)
    ((algebraMap k L).comp (algebraMap F₁₁ k))) r

instance : CharP L 11 := charP_of_injective_algebraMap (algebraMap F₁₁ L).injective 11

theorem algebraMap_c_L : algebraMap k L c = cL := by
  change IsFractionRing.lift _ (algebraMap P₁ k (X 0)) = _
  rw [IsFractionRing.lift_algebraMap]
  simp

theorem algebraMap_k_K' (z : k) : algebraMap k K' z = algebraMap k' K' (algebraMap k k' z) :=
  IsScalarTower.algebraMap_apply k k' K' z

/-- `ι` is a homomorphism of `k`-algebras. -/
theorem ι_algebraMap (z : k) : ι (algebraMap k L z) = algebraMap k K' z := by
  have h : ι.comp (algebraMap k L) = algebraMap k K' := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors P₁)
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (Subsingleton.elim (α := F₁₁ →+* K')
        (((ι.comp (algebraMap k L)).comp (algebraMap P₁ k)).comp MvPolynomial.C)
        (((algebraMap k K').comp (algebraMap P₁ k)).comp MvPolynomial.C)) r
    · intro i
      rw [Subsingleton.elim i 0]
      simp only [RingHom.coe_comp, Function.comp_apply]
      have h1 : algebraMap P₁ k (X 0) = c := rfl
      rw [h1, algebraMap_c_L, ι_cL, algebraMap_k_K', algebraMap_c, map_pow]
      rfl
  exact RingHom.congr_fun h z

/-- `ι` as a homomorphism of `k`-algebras. -/
def ιk : L →ₐ[k] K' := { ι with commutes' := ι_algebraMap }

end
end Geonormal.P11

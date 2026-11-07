import Eff.YOrder

/-! # Geometric non-normality of the second quotient

Over `k`, the principal open where `B` is invertible has coordinate ring `C`, generated over `k`
by `A/B²`, `W/B³` and `B^{±5}`. The function `B` lies in the fraction field of `C` and is integral
over it, because `B⁵ ∈ C`. It does not lie in `C`, because a derivation sends `C` into the ideal of
the line `c₂ + c₁ t = 0`, while it sends `B` to a unit multiple of `B`.
-/

namespace Eff

noncomputable section
set_option backward.isDefEq.respectTransparency false

section FifthRoot
open Polynomial

/-- A fifth root that is also a root of a nonzero polynomial of degree at most three is rational:
it is purely inseparable of degree prime to five. -/
theorem mem_range_of_fifth_root {E F : Type*} [Field E] [Field F] [Algebra E F] [CharP F 5]
    (r : F) (s : E) (hs : r ^ 5 = algebraMap E F s) (p : E[X]) (hp : p ≠ 0) (hd : p.natDegree ≤ 3)
    (hr : aeval r p = 0) : r ∈ (algebraMap E F).range := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hCE : CharP E 5 := (RingHom.charP_iff (algebraMap E F) (algebraMap E F).injective 5).mpr
    inferInstance
  have hint : IsIntegral E r := IsAlgebraic.isIntegral ⟨p, hp, hr⟩
  let μ := minpoly E r
  have hμ : μ.Monic := minpoly.monic hint
  have hdvdp : μ ∣ p := minpoly.dvd E r hr
  have hdeg : μ.natDegree ≤ 3 := (natDegree_le_of_dvd hdvdp hp).trans hd
  have hpos : 0 < μ.natDegree := minpoly.natDegree_pos hint
  have hdvd5 : μ ∣ X ^ 5 - C s := minpoly.dvd E r (by
    simp [hs, aeval_C])
  have hmapdvd : μ.map (algebraMap E F) ∣ (X - C r) ^ 5 := by
    have h := Polynomial.map_dvd (algebraMap E F) hdvd5
    have he : (X ^ 5 - C s : E[X]).map (algebraMap E F) = (X - C r) ^ 5 := by
      rw [sub_pow_char, ← C_pow, hs]
      simp
    rwa [he] at h
  obtain ⟨e, -, hassoc⟩ := (dvd_prime_pow (prime_X_sub_C r) 5).mp hmapdvd
  have hmonic : (μ.map (algebraMap E F)).Monic := hμ.map _
  have heq : μ.map (algebraMap E F) = (X - C r) ^ e :=
    eq_of_monic_of_associated hmonic ((monic_X_sub_C r).pow e) hassoc
  have hne : e = μ.natDegree := by
    have := congrArg natDegree heq
    rw [natDegree_map, natDegree_pow, natDegree_X_sub_C, mul_one] at this
    exact this.symm
  have hcoeff : algebraMap E F (μ.coeff (e - 1)) = (-r) * (e : F) := by
    have h := congrArg (fun q : F[X] ↦ q.coeff (e - 1)) heq
    simp only [coeff_map] at h
    rw [h, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow,
      show e - (e - 1) = 1 by omega, pow_one, Nat.choose_symm (by omega : 1 ≤ e),
      Nat.choose_one_right]
  have heF : (e : F) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff F 5 e).mp h0
    omega
  have heE : (e : E) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff E 5 e).mp h0
    omega
  refine ⟨-(μ.coeff (e - 1)) / (e : E), ?_⟩
  rw [map_div₀, map_neg, map_natCast, hcoeff]
  field_simp

end FifthRoot

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent
  AlgebraicGeometry CategoryTheory

/-! ### A derivation contracting the line `c₂ + c₁ t = 0` -/

/-- The polynomial form of the derivation. It kills the coefficients `c₁, c₂`. -/
def polyContract : Derivation F₅ P₄ P₄ :=
  MvPolynomial.mkDerivation F₅
    ![0, 0, MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 - MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.X 2, 3 * MvPolynomial.X 0 * MvPolynomial.X 3]

def contract : Derivation F₅ K K := FractionDerivation.extend polyContract

@[simp] theorem contract_c₁ : contract c₁ = 0 := by simp [contract, coord, polyContract]
@[simp] theorem contract_c₂ : contract c₂ = 0 := by simp [contract, coord, polyContract]

theorem contract_t : contract t = c₁ ^ 2 * w - c₂ + c₁ * t := by
  simp [contract, coord, polyContract]

theorem contract_w : contract w = 3 * c₁ * w := by
  simp [contract, coord, polyContract, map_ofNat]

@[simp] theorem contract_k (x : k) : contract (includeK x) = 0 := by
  rw [derivation_on_k, contract_c₁, contract_c₂]
  simp

theorem contract_fifth (x : K) : contract (x ^ 5) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]

/-- The line along which the coordinate ring of the quotient is not normal. -/
def lineEq : K := c₂ + c₁ * t

theorem contract_B : contract B = c₁ * B := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h3 : contract (3 : K) = 0 := contract.map_natCast 3
  simp only [B, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, contract_c₁,
    contract_c₂, contract_t, contract_w, h3, smul_eq_mul, nsmul_eq_mul]
  linear_combination c₁ ^ 3 * w * h5

theorem contract_A : contract A = -2 * c₁ ^ 2 * w - c₂ + c₁ * t := by
  simp only [A, map_sub, Derivation.leibniz, contract_c₁, contract_t, contract_w, smul_eq_mul]
  ring

theorem contract_W : contract W = 3 * c₁ * W := contract_w

theorem B_ne : B ≠ 0 := by
  have hne : ((base0.x 1 : L) : K) ≠ 0 := fun h0 ↦ base0.x_ne 1 (Subtype.ext h0)
  have h : ((base0.x 1 : L) : K) = B := by
    change (x0 1 : K) = B
    exact congrFun x0_coe 1
  rwa [h] at hne

theorem contract_a : contract (A / B ^ 2) * B ^ 2 = -lineEq := by
  have hB := B_ne
  have h2 : contract (B ^ 2) = 2 * B * (c₁ * B) := by
    rw [Derivation.leibniz_pow, contract_B]
    simp
    ring
  rw [Derivation.leibniz_div, h2, contract_A]
  simp only [smul_eq_mul]
  field_simp
  simp only [A, lineEq]
  ring

theorem contract_b : contract (W / B ^ 3) = 0 := by
  have hB := B_ne
  have h3 : contract (B ^ 3) = 3 * B ^ 2 * (c₁ * B) := by
    rw [Derivation.leibniz_pow, contract_B]
    simp
    ring
  rw [Derivation.leibniz_div, h3, contract_W]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The ring of functions of the open `B ≠ 0` in `V₁` with derivative in the ideal of the line. -/
def contractRing : Subalgebra k K where
  carrier := {f | (∃ m : ℕ, f * B ^ m ∈ chartRing 0) ∧
    ∃ (n : ℕ) (g : K), g ∈ chartRing 0 ∧ contract f * B ^ n = lineEq * g}
  mul_mem' := by
    rintro f f' ⟨⟨m, hm⟩, n, g, hg, hn⟩ ⟨⟨m', hm'⟩, n', g', hg', hn'⟩
    refine ⟨⟨m + m', ?_⟩, m + m' + n + n', (f * B ^ m) * (B ^ n * g') * B ^ m' * B ^ 0 +
      (f' * B ^ m') * (B ^ n' * g) * B ^ m, ?_, ?_⟩
    · have he : f * f' * B ^ (m + m') = (f * B ^ m) * (f' * B ^ m') := by rw [pow_add]; ring
      rw [he]
      exact (chartRing 0).mul_mem hm hm'
    · have hBm : B ∈ chartRing 0 := by
        have h : (x0 1 : K) ∈ chartRing 0 := x0_mem 1
        rwa [show (x0 1 : K) = B from congrFun x0_coe 1] at h
      have hp (j : ℕ) : B ^ j ∈ chartRing 0 := (chartRing 0).pow_mem hBm j
      exact (chartRing 0).add_mem
        ((chartRing 0).mul_mem ((chartRing 0).mul_mem ((chartRing 0).mul_mem hm
          ((chartRing 0).mul_mem (hp n) hg')) (hp m')) (hp 0))
        ((chartRing 0).mul_mem ((chartRing 0).mul_mem hm'
          ((chartRing 0).mul_mem (hp n') hg)) (hp m))
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      simp only [pow_add, pow_zero, mul_one]
      linear_combination (f * B ^ m * B ^ m' * B ^ n) * hn' +
        (f' * B ^ m' * B ^ m * B ^ n') * hn
  add_mem' := by
    rintro f f' ⟨⟨m, hm⟩, n, g, hg, hn⟩ ⟨⟨m', hm'⟩, n', g', hg', hn'⟩
    have hBm : B ∈ chartRing 0 := by
      have h : (x0 1 : K) ∈ chartRing 0 := x0_mem 1
      rwa [show (x0 1 : K) = B from congrFun x0_coe 1] at h
    have hp (j : ℕ) : B ^ j ∈ chartRing 0 := (chartRing 0).pow_mem hBm j
    refine ⟨⟨m + m', ?_⟩, n + n', B ^ n' * g + B ^ n * g', ?_, ?_⟩
    · have he : (f + f') * B ^ (m + m') = (f * B ^ m) * B ^ m' + (f' * B ^ m') * B ^ m := by
        rw [pow_add]; ring
      rw [he]
      exact (chartRing 0).add_mem ((chartRing 0).mul_mem hm (hp m'))
        ((chartRing 0).mul_mem hm' (hp m))
    · exact (chartRing 0).add_mem ((chartRing 0).mul_mem (hp n') hg)
        ((chartRing 0).mul_mem (hp n) hg')
    · rw [map_add, pow_add]
      linear_combination B ^ n' * hn + B ^ n * hn'
  algebraMap_mem' x := by
    refine ⟨⟨0, by simp [(chartRing 0).algebraMap_mem x]⟩, 0, 0, (chartRing 0).zero_mem, ?_⟩
    simp only [pow_zero, mul_one, mul_zero]
    exact contract_k x

theorem B_mem_chart : B ∈ chartRing 0 := by
  have h : (x0 1 : K) ∈ chartRing 0 := x0_mem 1
  rwa [show (x0 1 : K) = B from congrFun x0_coe 1] at h

theorem contractRing_inv {f : K} (hf : f ∈ contractRing) (hne : f ≠ 0)
    (hi : ∃ m : ℕ, f⁻¹ * B ^ m ∈ chartRing 0) : f⁻¹ ∈ contractRing := by
  obtain ⟨-, n, g, hg, hn⟩ := hf
  obtain ⟨m, hm⟩ := hi
  refine ⟨⟨m, hm⟩, n + 2 * m, -(g * (f⁻¹ * B ^ m) ^ 2), ?_, ?_⟩
  · exact (chartRing 0).neg_mem ((chartRing 0).mul_mem hg ((chartRing 0).pow_mem hm 2))
  · rw [Derivation.leibniz_inv, smul_eq_mul, pow_add, pow_mul]
    linear_combination (-(f⁻¹) ^ 2 * (B ^ 2) ^ m) * hn

/-- The principal open of `Y` where `B` is invertible. -/
abbrev openB : YOpen (0 : Fin 4) := yOpen .B

theorem openB_clear (x : L) (hx : x ∈ openB.A) : ∃ m : ℕ, (x : K) * B ^ m ∈ chartRing 0 := by
  obtain ⟨n, hn⟩ := openB.clear x hx
  refine ⟨5 * n, ?_⟩
  have hd : (((openB.d : yAtlas.ring (0 : Fin 4)) : M) : L).1 = B ^ 5 := by
    have h := d_B
    change (openB.d : yAtlas.ring (0 : Fin 4)) = _ at h
    rw [h]
    rfl
  have h' : (x : K) * (((openB.d : yAtlas.ring (0 : Fin 4)) : M) : L).1 ^ n ∈ chartRing 0 := hn
  rw [hd, ← pow_mul] at h'
  exact h'

theorem openB_coord (k : Fin 4) : ((openB.coordinates k : L) : K) =
    ![B ^ 5, c₁ ^ 5, A / B ^ 2, W / B ^ 3] k := by
  rw [show openB = yOpen .B from rfl, coord_B k, ← B_eqK, ← A_eqK, ← W_eqK, ← s₁_eqK]

theorem openB_coord_mem (k : Fin 4) : ((openB.coordinates k : L) : K) ∈ contractRing := by
  rw [openB_coord k]
  have hB := B_ne
  fin_cases k
  · refine ⟨⟨0, by simpa using (chartRing 0).pow_mem B_mem_chart 5⟩, 0, 0, (chartRing 0).zero_mem, ?_⟩
    change contract (B ^ 5) * B ^ 0 = lineEq * 0
    rw [contract_fifth]
    ring
  · refine ⟨⟨0, ?_⟩, 0, 0, (chartRing 0).zero_mem, ?_⟩
    · simpa using (chartRing 0).pow_mem (contracted_c₁_mem (0 : Fin 4)) 5
    · change contract (c₁ ^ 5) * B ^ 0 = lineEq * 0
      rw [contract_fifth]
      ring
  · refine ⟨⟨2, ?_⟩, 2, -1, ?_, ?_⟩
    · have he : A / B ^ 2 * B ^ 2 = A := by field_simp
      change A / B ^ 2 * B ^ 2 ∈ chartRing 0
      rw [he]
      exact (show (x0 2 : K) = A from congrFun x0_coe 2) ▸ x0_mem 2
    · exact (chartRing 0).neg_mem (chartRing 0).one_mem
    · change contract (A / B ^ 2) * B ^ 2 = lineEq * -1
      rw [contract_a]
      ring
  · refine ⟨⟨3, ?_⟩, 0, 0, (chartRing 0).zero_mem, ?_⟩
    · have he : W / B ^ 3 * B ^ 3 = W := by field_simp
      change W / B ^ 3 * B ^ 3 ∈ chartRing 0
      rw [he]
      exact (show (x0 3 : K) = W from congrFun x0_coe 3) ▸ x0_mem 3
    · change contract (W / B ^ 3) * B ^ 0 = lineEq * 0
      rw [contract_b]
      ring

/-- The whole invariant coordinate ring has derivative in the ideal of the line. -/
theorem openB_kernel_le (x : L) (hx : x ∈ openB.kernel) : (x : K) ∈ contractRing := by
  let T : Subalgebra F₅ L :=
    (contractRing.restrictScalars F₅).comap ConeRing.invariantInclusion
  have hP : polynomialRing (F := F₅) (powerCoordinates openB.v) ≤ T := Algebra.adjoin_le (by
    rintro _ ⟨k, rfl⟩
    exact openB_coord_mem k)
  obtain ⟨β, hβ, hβ0, hβi, hxβ⟩ :=
    kernel_le_hull openB.D openB.v openB.independent openB.values openB.A openB.hull_le hx
  have hβK : (β : K) ∈ contractRing := hP hβ
  have hxβK : ((x * β : L) : K) ∈ contractRing := hP hxβ
  have hβK0 : (β : K) ≠ 0 := fun h ↦ hβ0 (Subtype.ext h)
  have hinv : (β : K)⁻¹ ∈ contractRing :=
    contractRing_inv hβK hβK0 (openB_clear β⁻¹ hβi.1)
  have he : (x : K) = ((x * β : L) : K) * (β : K)⁻¹ := by
    rw [Subfield.coe_mul]
    field_simp
  rw [he]
  exact contractRing.mul_mem hxβK hinv

section Line

open MvPolynomial

theorem c_ne_zero (i : Fin 2) : c i ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective P₂ k)).mpr (MvPolynomial.X_ne_zero i)

/-- `B` is not a function with derivative in the ideal of the line. -/
theorem B_not_mem_contractRing : B ∉ contractRing := by
  rintro ⟨-, n, g, hg, hn⟩
  rw [contract_B] at hn
  let e := chartPolynomialEquiv 0
  let ι : MvPolynomial (Fin 2) k →ₐ[k] K := (chartRing 0).val.comp e.toAlgHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have ht : ι (X 0) = t := by
    have h : ι (X 0) = chartCoordinates 0 0 := chartPolynomialEquiv_X 0 0
    rw [h]
    simp [chartCoordinates, y₁, first, Charts.monomial]
  have hw : ι (X 1) = w := by
    have h : ι (X 1) = chartCoordinates 0 1 := chartPolynomialEquiv_X 0 1
    rw [h]
    simp [chartCoordinates, y₂, second, Charts.monomial]
  have hc (a : k) : ι (C a) = includeK a := ι.commutes a
  have hc₁ : ι (C (c 0)) = c₁ := by rw [hc]; simpa using includeK_c 0
  have hc₂ : ι (C (c 1)) = c₂ := by rw [hc]; simpa using includeK_c 1
  let pB : MvPolynomial (Fin 2) k := C (c 1) - C (c 0) * X 0 + 3 * C (c 0) ^ 2 * X 1
  let pL : MvPolynomial (Fin 2) k := C (c 1) + C (c 0) * X 0
  let pg : MvPolynomial (Fin 2) k := e.symm ⟨g, hg⟩
  have hpB : ι pB = B := by
    simp only [pB, map_add, map_sub, map_mul, map_pow, map_ofNat, ht, hw, hc₁, hc₂, B]
  have hpL : ι pL = lineEq := by
    simp only [pL, map_add, map_mul, ht, hc₁, hc₂, lineEq]
  have hpg : ι pg = g := by
    change ((e (e.symm ⟨g, hg⟩) : chartRing 0) : K) = g
    rw [AlgEquiv.apply_symm_apply]
  have hpoly : C (c 0) * pB ^ (n + 1) = pL * pg := by
    apply hι
    rw [map_mul, map_mul, map_pow, hc₁, hpB, hpL, hpg, ← hn]
    ring
  have hc0 := c_ne_zero 0
  have hc1 := c_ne_zero 1
  let Θ : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
    aeval ![Polynomial.C (-(c 1) / c 0), Polynomial.X]
  have hΘL : Θ pL = 0 := by
    simp only [pL, Θ, map_add, map_mul, aeval_C, aeval_X, Matrix.cons_val_zero]
    change Polynomial.C (c 1) + Polynomial.C (c 0) * Polynomial.C (-(c 1) / c 0) = 0
    rw [← Polynomial.C_mul, ← Polynomial.C_add]
    have : c 1 + c 0 * (-(c 1) / c 0) = 0 := by field_simp; ring
    rw [this, Polynomial.C_0]
  have hΘB : Θ pB ≠ 0 := by
    intro h0
    have he := congrArg (Polynomial.eval 0) h0
    simp only [pB, Θ, map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    have he' : c 1 - c 0 * (-(c 1) / c 0) = 0 := by
      simpa [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul] using he
    have h2 : (2 : k) * c 1 = 0 := by
      rw [← he']
      field_simp
      ring
    have h5 : (5 : k) = 0 := CharP.cast_eq_zero k 5
    have h2' : (2 : k) ≠ 0 := by
      intro h
      exact one_ne_zero (show (1 : k) = 0 by linear_combination h5 - 2 * h)
    exact (mul_ne_zero h2' hc1) h2
  have himg := congrArg Θ hpoly
  rw [map_mul, map_mul, hΘL, zero_mul, map_pow] at himg
  have hC0 : Θ (C (c 0)) ≠ 0 := by
    rw [show Θ (C (c 0)) = Polynomial.C (c 0) from aeval_C _ _]
    exact Polynomial.C_ne_zero.mpr hc0
  exact (mul_ne_zero hC0 (pow_ne_zero _ hΘB)) himg

end Line

/-! ### The coordinate ring over `k` -/

/-- Generators of the coordinate ring over `k`. -/
def openBImage : Set K := (fun x : L ↦ (x : K)) '' (openB.kernel : Set L)

/-- The coordinate ring over `k` of the principal open where `B` is invertible. -/
def openBk : Subalgebra k K := Algebra.adjoin k openBImage

theorem openBk_le : openBk ≤ contractRing :=
  Algebra.adjoin_le (by rintro _ ⟨x, hx, rfl⟩; exact openB_kernel_le x hx)

theorem B_not_mem_openBk : B ∉ openBk := fun h ↦ B_not_mem_contractRing (openBk_le h)

theorem openB_coord_image (k : Fin 4) : ((openB.coordinates k : L) : K) ∈ openBImage :=
  ⟨_, (openB.coordinates k).property, rfl⟩

theorem z_mem_image : B ^ 5 ∈ openBImage := by
  have := openB_coord_image 0
  rwa [openB_coord 0] at this

theorem a_mem_image : A / B ^ 2 ∈ openBImage := by
  have := openB_coord_image 2
  rwa [openB_coord 2] at this

theorem b_mem_image : W / B ^ 3 ∈ openBImage := by
  have := openB_coord_image 3
  rwa [openB_coord 3] at this

/-- `B` is in the field generated by the coordinate ring. -/
theorem B_mem_field : B ∈ IntermediateField.adjoin k openBImage := by
  let E := IntermediateField.adjoin k openBImage
  have hS {x : K} (hx : x ∈ openBImage) : x ∈ E := IntermediateField.subset_adjoin k _ hx
  have hk (a : k) : includeK a ∈ E := E.algebraMap_mem a
  have hc₁E : c₁ ∈ E := by simpa [includeK_c] using hk (c 0)
  have hc₂E : c₂ ∈ E := by simpa [includeK_c] using hk (c 1)
  let γ₃ : E := ⟨3 * c₁ ^ 2 * (W / B ^ 3), E.mul_mem (E.mul_mem (E.natCast_mem 3) (E.pow_mem hc₁E 2))
    (hS b_mem_image)⟩
  let γ₂ : E := ⟨c₁ * (A / B ^ 2), E.mul_mem hc₁E (hS a_mem_image)⟩
  let γ₀ : E := ⟨c₂, hc₂E⟩
  let s : E := ⟨B ^ 5, hS z_mem_image⟩
  let p : Polynomial E := Polynomial.C γ₃ * Polynomial.X ^ 3 + Polynomial.C γ₂ * Polynomial.X ^ 2 +
    Polynomial.X - Polynomial.C γ₀
  have hp : p ≠ 0 := by
    intro h0
    have := congrArg (fun q ↦ Polynomial.coeff q 1) h0
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at this
  have hd : p.natDegree ≤ 3 := by
    simp only [p]
    compute_degree
  have hB := B_ne
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hr : Polynomial.aeval B p = 0 := by
    have hγ₃ : algebraMap E K γ₃ = 3 * c₁ ^ 2 * (W / B ^ 3) := rfl
    have hγ₂ : algebraMap E K γ₂ = c₁ * (A / B ^ 2) := rfl
    have hγ₀ : algebraMap E K γ₀ = c₂ := rfl
    simp only [p, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      hγ₃, hγ₂, hγ₀]
    field_simp
    simp only [A, W, B]
    linear_combination c₁ ^ 2 * w * h5
  have := mem_range_of_fifth_root (E := E) (F := K) B s rfl p hp hd hr
  obtain ⟨x, hx⟩ := this
  rw [← hx]
  exact x.property

theorem openBk_field_top : IntermediateField.adjoin k openBImage = ⊤ := by
  let E := IntermediateField.adjoin k openBImage
  have hS {x : K} (hx : x ∈ openBImage) : x ∈ E := IntermediateField.subset_adjoin k _ hx
  have hB : B ∈ E := B_mem_field
  have hB0 := B_ne
  have hk (a : k) : includeK a ∈ E := E.algebraMap_mem a
  have hc₁E : c₁ ∈ E := by simpa [includeK_c] using hk (c 0)
  have hw : w ∈ E := by
    have he : w = W / B ^ 3 * B ^ 3 := by
      change W = _
      field_simp
    rw [he]
    exact E.mul_mem (hS b_mem_image) (E.pow_mem hB 3)
  have hA : A ∈ E := by
    have he : A = A / B ^ 2 * B ^ 2 := by field_simp
    rw [he]
    exact E.mul_mem (hS a_mem_image) (E.pow_mem hB 2)
  have ht : t ∈ E := by
    have he : t = A + c₁ * w := by simp only [A]; ring
    rw [he]
    exact E.add_mem hA (E.mul_mem hc₁E hw)
  apply top_unique
  rw [← rational_generation]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ht
  · exact Set.mem_singleton_iff.mp hx ▸ hw

instance openBk_isFractionRing : IsFractionRing openBk K := by
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ IntermediateField.adjoin k openBImage := by
    rw [openBk_field_top]
    trivial
  obtain ⟨a, ha, b, hb, he⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he⟩

/-- The coordinate ring over `k` is not integrally closed. -/
theorem openBk_not_isIntegrallyClosed : ¬ IsIntegrallyClosed openBk := by
  intro h
  have hz : B ^ 5 ∈ openBk := Algebra.subset_adjoin z_mem_image
  have hi : IsIntegral openBk (B ^ 5) := isIntegral_algebraMap (x := (⟨B ^ 5, hz⟩ : openBk))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide) hi
  exact B_not_mem_openBk (hy ▸ y.property)

/-! ### Linear disjointness from the invariant field -/

theorem lineEq_ne : lineEq ≠ 0 := by
  have h : lineEq = algebraMap P₄ K (MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2) := by
    simp [lineEq, coord]
  rw [h]
  apply (map_ne_zero_iff _ (IsFractionRing.injective P₄ K)).mpr
  intro h0
  have := congrArg (MvPolynomial.eval ![0, 1, 0, 0]) h0
  simp at this

/-- A derivation killing `M` and `c₂`, with `c₁ ↦ 1`. -/
def firstSlice : Derivation F₅ K K := lineEq⁻¹ • (c₂ • delta - t • euler)
/-- A derivation killing `M` and `c₁`, with `c₂ ↦ 1`. -/
def secondSlice : Derivation F₅ K K := lineEq⁻¹ • (c₁ • delta + euler)

theorem firstSlice_c₁ : firstSlice c₁ = 1 := by
  have := lineEq_ne
  simp only [firstSlice, Derivation.smul_apply, Derivation.sub_apply, delta_c₁, euler_c₁,
    smul_eq_mul]
  rw [inv_mul_eq_div, div_eq_one_iff_eq this]
  simp only [lineEq]
  ring

theorem firstSlice_c₂ : firstSlice c₂ = 0 := by
  simp only [firstSlice, Derivation.smul_apply, Derivation.sub_apply, delta_c₂, euler_c₂,
    smul_eq_mul]
  ring

theorem secondSlice_c₁ : secondSlice c₁ = 0 := by
  simp only [secondSlice, Derivation.smul_apply, Derivation.add_apply, delta_c₁, euler_c₁,
    smul_eq_mul]
  ring

theorem secondSlice_c₂ : secondSlice c₂ = 1 := by
  have := lineEq_ne
  simp only [secondSlice, Derivation.smul_apply, Derivation.add_apply, delta_c₂, euler_c₂,
    smul_eq_mul]
  rw [inv_mul_eq_div, div_eq_one_iff_eq this]
  simp only [lineEq]
  ring

theorem firstSlice_M (x : M) : firstSlice ((x : L) : K) = 0 := by
  have h1 : delta ((x : L) : K) = 0 := (x : L).property
  have h2 : euler ((x : L) : K) = 0 := congrArg Subtype.val x.property
  simp [firstSlice, h1, h2]

theorem secondSlice_M (x : M) : secondSlice ((x : L) : K) = 0 := by
  have h1 : delta ((x : L) : K) = 0 := (x : L).property
  have h2 : euler ((x : L) : K) = 0 := congrArg Subtype.val x.property
  simp [secondSlice, h1, h2]

/-- The monomials in `c₁, c₂` are linearly independent over the second invariant field. -/
theorem monomials_independent (m : Fin 5 × Fin 5 → M)
    (h : ∑ ij, ((m ij : L) : K) * (c₁ ^ (ij.1 : ℕ) * c₂ ^ (ij.2 : ℕ)) = 0) : ∀ ij, m ij = 0 := by
  let b : Fin 5 → K := fun j ↦ ∑ i : Fin 5, ((m (i, j) : L) : K) * c₁ ^ (i : ℕ)
  have hb (j : Fin 5) : secondSlice (b j) = 0 := by
    simp [b, map_sum, Derivation.leibniz, Derivation.leibniz_pow, secondSlice_M, secondSlice_c₁]
  have hs : ∑ j : Fin 5, b j * c₂ ^ (j : ℕ) = 0 := by
    rw [Fintype.sum_prod_type] at h
    simp only [b, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hb0 := slice_sum_unique secondSlice c₂ secondSlice_c₂ b hb hs
  intro ij
  have h1 := slice_sum_unique firstSlice c₁ firstSlice_c₁ (fun i ↦ ((m (i, ij.2) : L) : K))
    (fun i ↦ firstSlice_M _) (hb0 ij.2) ij.1
  apply Subtype.ext
  apply Subtype.ext
  exact h1

/-! ### The base change of the principal open -/

open scoped TensorProduct

/-- The structure of `ell`-algebra on the coordinate ring of the principal open. -/
@[instance_reducible] def openBEllAlgebra : Algebra ell openB.kernel :=
  (openB.toKernel.comp (algebraMap ell (yAtlas.ring (0 : Fin 4)))).toAlgebra

attribute [local instance] openBEllAlgebra

theorem openB_algebraMap_coe (a : ell) :
    (((algebraMap ell openB.kernel a : openB.kernel) : L) : K) = algebraMap ell K a := rfl

/-- The inclusion of the coordinate ring in `K`. -/
def openBToK : openB.kernel →ₐ[ell] K where
  toFun x := ((x : L) : K)
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def kToK : k →ₐ[ell] K where
  __ := includeK
  commutes' _ := rfl

/-- The multiplication map from the base change of the coordinate ring. -/
def openBMul : openB.kernel ⊗[ell] k →ₐ[ell] K :=
  Algebra.TensorProduct.productMap openBToK kToK

theorem openBMul_tmul (x : openB.kernel) (a : k) :
    openBMul (x ⊗ₜ[ell] a) = ((x : L) : K) * includeK a := by
  simp [openBMul, openBToK, kToK]

theorem openB_kernel_mem_M (x : openB.kernel) : (x : L) ∈ M :=
  ((openB.mem_kernel_iff _).mp x.property).2

theorem pMonomial_coe (ij : Fin 5 × Fin 5) :
    includeK (pBasis ij) = c₁ ^ (ij.1 : ℕ) * c₂ ^ (ij.2 : ℕ) := by
  rw [pBasis_apply, pMonomial, map_mul, map_pow, map_pow, includeK_c, includeK_c]
  rfl

/-- The base change is a domain inside `K`: the multiplication map is injective. -/
theorem openBMul_injective : Function.Injective openBMul := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  let b := TensorProduct.equivFinsuppOfBasisRight (M := openB.kernel) pBasis x
  have hsum : b.sum (fun i m ↦ m ⊗ₜ[ell] pBasis i) = x := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    exact LinearEquiv.symm_apply_apply _ x
  have hzero : ∀ ij, b ij = 0 := by
    have hm := monomials_independent (fun ij ↦ ⟨(b ij : L), openB_kernel_mem_M (b ij)⟩) (by
      rw [← hx, ← hsum, Finsupp.sum_fintype _ _ (by simp), map_sum]
      refine Finset.sum_congr rfl fun ij _ ↦ ?_
      rw [openBMul_tmul, pMonomial_coe])
    intro ij
    apply Subtype.ext
    exact congrArg (fun z : M ↦ (z : L)) (hm ij)
  rw [← hsum, Finsupp.sum_fintype _ _ (by simp)]
  simp [hzero]

theorem openBMul_mem (x : openB.kernel ⊗[ell] k) : openBMul x ∈ openBk := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [openBMul_tmul]
    exact openBk.mul_mem (Algebra.subset_adjoin ⟨_, r.property, rfl⟩) (openBk.algebraMap_mem a)
  | add p q hp hq =>
    rw [map_add]
    exact openBk.add_mem hp hq

/-- The base change of the coordinate ring is the subring of `K` generated over `k`. -/
def openBTensorEquiv : openB.kernel ⊗[ell] k ≃+* openBk :=
  RingEquiv.ofBijective
    ((openBMul.toRingHom).codRestrict openBk.toSubring openBMul_mem) (by
    constructor
    · intro x y h
      exact openBMul_injective (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      induction hy using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨r, hr, rfl⟩ := hz
        exact ⟨(⟨r, hr⟩ : openB.kernel) ⊗ₜ[ell] 1, Subtype.ext (by
          change openBMul _ = _
          rw [openBMul_tmul, map_one, mul_one])⟩
      | algebraMap a =>
        exact ⟨1 ⊗ₜ[ell] a, Subtype.ext (by
          change openBMul _ = _
          rw [openBMul_tmul]
          simp
          rfl)⟩
      | add a b ha hb iha ihb =>
        obtain ⟨p, hp⟩ := iha
        obtain ⟨q, hq⟩ := ihb
        exact ⟨p + q, Subtype.ext (by
          have h1 := congrArg Subtype.val hp
          have h2 := congrArg Subtype.val hq
          change openBMul (p + q) = a + b
          rw [map_add]
          exact congrArg₂ _ h1 h2)⟩
      | mul a b ha hb iha ihb =>
        obtain ⟨p, hp⟩ := iha
        obtain ⟨q, hq⟩ := ihb
        exact ⟨p * q, Subtype.ext (by
          have h1 := congrArg Subtype.val hp
          have h2 := congrArg Subtype.val hq
          change openBMul (p * q) = a * b
          rw [map_mul]
          exact congrArg₂ _ h1 h2)⟩)

/-- A normal scheme: every local ring is an integrally closed domain. -/
def IsNormalScheme : ObjectProperty Scheme :=
  fun X ↦ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- The principal open lies over `ell` through the algebra structure of its coordinate ring. -/
theorem openB_over_base :
    openB.openMap ≫ yToBase = Spec.map (CommRingCat.ofHom (algebraMap ell openB.kernel)) := by
  have h : yAtlas.chartInclusion (0 : Fin 4) ≫ yToBase =
      Spec.map (CommRingCat.ofHom (algebraMap ell (yAtlas.ring (0 : Fin 4)))) :=
    yAtlas.chartInclusion_toBase (0 : Fin 4)
  simp only [YOpen.openMap, Category.assoc]
  change Spec.map (CommRingCat.ofHom openB.toKernel) ≫ yAtlas.chartInclusion (0 : Fin 4) ≫ yToBase = _
  rw [h, ← Spec.map_comp]
  rfl

/-- The second quotient is not geometrically normal: the base change to `k` is not normal. -/
theorem y_not_geometrically_normal : ¬ geometrically IsNormalScheme yToBase := by
  intro hG
  let y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ell) :=
    Spec.map (CommRingCat.ofHom (algebraMap ell k))
  let Z := Limits.pullback yToBase y
  have hZ : IsNormalScheme Z :=
    hG y (Limits.pullback.fst yToBase y) (Limits.pullback.snd yToBase y) (.of_hasPullback _ _)
  -- The base change of the principal open.
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ell openB.kernel k)
  have hZsq : IsPullback (Limits.pullback.fst yToBase y) (Limits.pullback.snd yToBase y) yToBase y :=
    .of_hasPullback _ _
  let P := CommRingCat.of (openB.kernel ⊗[ell] k)
  let pr₁ : Spec P ⟶ Spec (CommRingCat.of openB.kernel) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom))
  let pr₂ : Spec P ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight.toRingHom))
  have hw : (pr₁ ≫ openB.openMap) ≫ yToBase = pr₂ ≫ y := by
    rw [Category.assoc, openB_over_base]
    exact hsq.w
  let ι : Spec P ⟶ Z := Limits.pullback.lift (pr₁ ≫ openB.openMap) pr₂ hw
  have hι₁ : ι ≫ Limits.pullback.fst yToBase y = pr₁ ≫ openB.openMap :=
    Limits.pullback.lift_fst _ _ _
  have hι₂ : ι ≫ Limits.pullback.snd yToBase y = pr₂ := Limits.pullback.lift_snd _ _ _
  have hwhole : IsPullback (ι ≫ Limits.pullback.snd yToBase y) pr₁ y (openB.openMap ≫ yToBase) := by
    rw [hι₂, openB_over_base]
    exact hsq.flip
  have hleft : IsPullback ι pr₁ (Limits.pullback.fst yToBase y) openB.openMap :=
    IsPullback.of_right hwhole hι₁ hZsq.flip
  have hopen : IsOpenImmersion ι :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hleft.flip inferInstance
  -- Hence every localization of the base change is integrally closed.
  have hloc (m : PrimeSpectrum (openB.kernel ⊗[ell] k)) :
      IsIntegrallyClosed (Localization.AtPrime m.asIdeal) := by
    have hint := (hZ (ι m)).2
    have h1 : IsIntegrallyClosed ((Spec P).presheaf.stalk m) :=
      IsIntegrallyClosed.of_equiv (asIso (ι.stalkMap m)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (Spec.stalkIso P m).commRingCatIsoToRingEquiv
  apply openBk_not_isIntegrallyClosed
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : PrimeSpectrum openBk := ⟨p, hp.isPrime⟩
  have h2 : IsIntegrallyClosed (Localization.AtPrime
      (q.asIdeal.comap openBTensorEquiv.toRingHom)) :=
    hloc (PrimeSpectrum.comap openBTensorEquiv.toRingHom q)
  exact @IsIntegrallyClosed.of_equiv _ _ _ _ (primeLocalizationRingEquiv openBTensorEquiv q) h2

end
end Eff

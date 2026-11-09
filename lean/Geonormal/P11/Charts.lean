import Geonormal.P11.Field

/-! # The four charts of the characteristic-11 surface

Inside `L = 𝔽₁₁(a, b, σ)` put `u = b² - a³`, `w = 1/u`, `α = 1/a`, `β = b/a²`, `ρ = σ + 2b/a`,
`α″ = u⁴/a`, `β″ = u²b/a²`, and `ξ_n = θ_n w²`. The surface is glued from

* `A = k[a, b, σ]`, the affine Weierstrass part over `u ≠ ∞`;
* `B = k[u, α, β, ρ]`, with `β² = α + uα⁴`, around the section at infinity over `u ≠ ∞`;
* `D = k[w, α″, β″, ρ]`, with `β″² = α″ + w¹¹α″⁴`, the same over `u ≠ 0`;
* `P = k[ξ₀, …, ξ₁₀]`, the affine part over `u ≠ 0`, which contains the cusp `P₀` of the fibre
  over `u = ∞`.
-/

namespace Geonormal.P11

open MvPolynomial

noncomputable section

/-! ## Elements of the function field -/

def uL : L := bL ^ 2 - aL ^ 3
def wL : L := uL⁻¹
def αL : L := aL⁻¹
def βL : L := bL / aL ^ 2
def ρL : L := σL + 2 * bL / aL
def αD : L := uL ^ 4 / aL
def βD : L := uL ^ 2 * bL / aL ^ 2
/-- `a″ = a w⁴`, which is `x'¹¹` in `K'`. -/
def aP : L := aL * wL ^ 4
/-- `b″ = b w⁶`, which is `y'¹¹` in `K'`. -/
def bP : L := bL * wL ^ 6
/-- `σ w²`, which is `s - 2γw'²` in `K'`. -/
def sP : L := σL * wL ^ 2
/-- The generators `ξ_n = θ_n/u²` of the chart around the cusp of the fibre over `u = ∞`. -/
def ξ (n : Fin 11) : L := θE n aL bL σL * wL ^ 2

theorem xK_ne_zero : xK ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective S₂ K')).mpr (MvPolynomial.X_ne_zero 0)

theorem yK_ne_zero : yK ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective S₂ K')).mpr (MvPolynomial.X_ne_zero 1)

theorem ι_uL : ι uL = wK⁻¹ := by
  simp only [uL, map_sub, map_pow, ι_aL, ι_bL]
  exact u_ident xK yK wK_ne_zero'

theorem ι_wL : ι wL = wK := by
  rw [wL, map_inv₀, ι_uL, inv_inv]

theorem ι_aP : ι aP = xK ^ 11 := by
  have := wK_ne_zero
  rw [aP, map_mul, map_pow, ι_aL, ι_wL]
  field_simp

theorem ι_bP : ι bP = yK ^ 11 := by
  have := wK_ne_zero
  rw [bP, map_mul, map_pow, ι_bL, ι_wL]
  field_simp

theorem ι_sP : ι sP = sK - 2 * γK * wK ^ 2 := by
  have := wK_ne_zero
  rw [sP, map_mul, map_pow, ι_σL, ι_wL]
  field_simp

/-- `Ψ = (x'¹¹s + 2y'¹¹)/w'²`, a polynomial. -/
def Ψ {R : Type*} [CommRing R] (x y : R) : R :=
  -3 * x ^ 9 * y - 5 * x ^ 6 * y ^ 3 + 4 * x ^ 3 * y ^ 5 + 2 * y ^ 7

theorem Ψ_ident {F : Type*} [Field F] [CharP F 11] (x y : F) :
    x ^ 11 * (x * y * (y ^ 2 - 3 * x ^ 3)) + 2 * y ^ 11 = Ψ x y * (y ^ 2 - x ^ 3) ^ 2 := by
  simp only [Ψ]
  grind

theorem aL_ne_zero : aL ≠ 0 := by
  intro h
  have h' := congrArg ι h
  rw [ι_aL, map_zero] at h'
  exact div_ne_zero (pow_ne_zero _ xK_ne_zero) (pow_ne_zero _ wK_ne_zero) h'

theorem bL_ne_zero : bL ≠ 0 := by
  intro h
  have h' := congrArg ι h
  rw [ι_bL, map_zero] at h'
  exact div_ne_zero (pow_ne_zero _ yK_ne_zero) (pow_ne_zero _ wK_ne_zero) h'

theorem uL_ne_zero : uL ≠ 0 := by
  intro h
  have h' := congrArg ι h
  rw [ι_uL, map_zero] at h'
  exact inv_ne_zero wK_ne_zero h'

theorem wL_ne_zero : wL ≠ 0 := inv_ne_zero uL_ne_zero

theorem ι_ρaP : ι (ρL * aP) = Ψ xK yK - 2 * γK * xK ^ 11 := by
  have hw := wK_ne_zero
  have ha := aL_ne_zero
  have h := Ψ_ident xK yK
  have hx := xK_ne_zero
  rw [map_mul, ι_aP, ρL, map_add, map_div₀, map_mul, ι_σL, ι_bL, ι_aL, map_ofNat]
  field_simp
  simp only [sK, wK] at *
  linear_combination h

/-! ## The four chart rings -/

/-- The affine Weierstrass chart `A = k[a, b, σ]`. -/
def chartA : Subalgebra k L := Algebra.adjoin k {aL, bL, σL}
/-- The chart `B = k[u, α, β, ρ]` around the section at infinity over `u ≠ ∞`. -/
def chartB : Subalgebra k L := Algebra.adjoin k {uL, αL, βL, ρL}
/-- The chart `D = k[w, α″, β″, ρ]` around the section at infinity over `u ≠ 0`. -/
def chartD : Subalgebra k L := Algebra.adjoin k {wL, αD, βD, ρL}
/-- The chart `P = k[ξ₀, …, ξ₁₀]` over `u ≠ 0`. -/
def chartP : Subalgebra k L := Algebra.adjoin k (Set.range ξ)

theorem ξ_mem (n : Fin 11) : ξ n ∈ chartP := Algebra.subset_adjoin ⟨n, rfl⟩

end
end Geonormal.P11

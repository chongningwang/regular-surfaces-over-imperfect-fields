import Mathlib.Tactic
import Mathlib.Tactic.ReduceModChar

/-! # Coordinates of the principal opens in terms of `(q₁, q₂, u, r)`

These are pure identities in a field of characteristic five. They express the coordinates of
each principal open through the reference coordinates `(q₁⁵, q₂/q₁⁴, u/q₁³, r/q₁)`.
-/

namespace Eff.YTuples

variable {F : Type*} [Field F] [CharP F 5]
variable (g q u r : F)

/-- The reference coordinates. -/
def z : F := g ^ 5
def a : F := q / g ^ 4
def c : F := u / g ^ 3
def d : F := r / g

def W₀ : F := a g q * z g * c g u + 3
def N₀ : F := d g r + 2 * a g q ^ 3 * z g ^ 2

/-- The chart functions. -/
def B : F := q + 3 * g ^ 2 / u
def A : F := -g / u
def W : F := u⁻¹
def s₁ : F := g ^ 5 + u ^ 3 * r
def s₂ : F := q ^ 5 + 3 * u * r ^ 2
def Q : F := g + 2 * q ^ 3 / r
def H : F := 4 * q ^ 2 / r
def Y : F := 2 / q
def Z : F := 3 * q
def τ : F := r⁻¹

theorem four_ne : (4 : F) ≠ 0 := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  intro h
  have : (1 : F) = 0 := by linear_combination h5 - h
  exact one_ne_zero this

variable (hg : g ≠ 0) (hq : q ≠ 0) (hu : u ≠ 0) (hr : r ≠ 0)
include hg

omit [CharP F 5] in
theorem z_ne : z g ≠ 0 := pow_ne_zero 5 hg

omit [CharP F 5] in
include hq in theorem a_ne : a g q ≠ 0 := div_ne_zero hq (pow_ne_zero 4 hg)
omit [CharP F 5] in
include hu in theorem c_ne : c g u ≠ 0 := div_ne_zero hu (pow_ne_zero 3 hg)
omit [CharP F 5] in
include hr in theorem d_ne : d g r ≠ 0 := div_ne_zero hr hg

omit [CharP F 5] in
include hu in
theorem B_eq : B g q u = W₀ g q u * g ^ 2 / u := by
  simp only [B, W₀, a, z, c]
  field_simp

omit [CharP F 5] in
include hr in
theorem Q_eq : Q g q r = g ^ 2 * N₀ g q r / r := by
  simp only [Q, N₀, a, z, d]
  field_simp

variable (hW : W₀ g q u ≠ 0) (hN : N₀ g q r ≠ 0)

/-! ### The tuples -/

omit [CharP F 5] in include hu in
theorem s1_eq : s₁ g u r = z g + c g u ^ 3 * d g r * z g ^ 2 := by
  simp only [s₁, z, c, d]; field_simp

omit [CharP F 5] in
theorem s2_eq : s₂ q u r = a g q ^ 5 * z g ^ 4 + 3 * c g u * d g r ^ 2 * z g := by
  simp only [s₂, z, c, d, a]; field_simp

omit [CharP F 5] in include hu in
theorem B0 : B g q u ^ 5 = W₀ g q u ^ 5 / (c g u ^ 5 * z g) := by
  rw [B_eq g q u hg hu]; simp only [c, z]; generalize W₀ g q u = w; field_simp

omit [CharP F 5] in include hu hW in
theorem B2 : A g u / B g q u ^ 2 = -c g u / W₀ g q u ^ 2 := by
  rw [B_eq g q u hg hu]; simp only [c, A]; generalize W₀ g q u = w at hW; field_simp

omit [CharP F 5] in include hu hW in
theorem B3 : W u / B g q u ^ 3 = c g u ^ 2 / W₀ g q u ^ 3 := by
  rw [B_eq g q u hg hu]; simp only [c, W]; generalize W₀ g q u = w at hW; field_simp

omit [CharP F 5] in include hu in
theorem A0 : A g u ^ 5 = -1 / (c g u ^ 5 * z g ^ 2) := by
  simp only [c, z, A]; field_simp

omit [CharP F 5] in include hu in
theorem A1 : B g q u / A g u ^ 3 = -W₀ g q u * c g u ^ 2 * z g := by
  rw [B_eq g q u hg hu]; simp only [c, z, A]; generalize W₀ g q u = w; field_simp

omit [CharP F 5] in include hu in
theorem A3 : W u / A g u ^ 4 = c g u ^ 3 * z g := by
  simp only [c, z, A, W]; field_simp

omit [CharP F 5] in include hu in
theorem W0 : W u ^ 5 = 1 / (c g u ^ 5 * z g ^ 3) := by
  simp only [c, z, W]; field_simp

omit [CharP F 5] in include hu in
theorem W1 : B g q u / W u ^ 2 = W₀ g q u * c g u * z g := by
  rw [B_eq g q u hg hu]; simp only [c, z, W]; generalize W₀ g q u = w; field_simp

omit [CharP F 5] in include hu in
theorem W2 : A g u / W u ^ 4 = -c g u ^ 3 * z g ^ 2 := by
  simp only [c, z, A, W]; field_simp

omit [CharP F 5] in include hr in
theorem Q0 : Q g q r ^ 5 = z g * N₀ g q r ^ 5 / d g r ^ 5 := by
  rw [Q_eq g q r hg hr]; simp only [d, z]; generalize N₀ g q r = n; field_simp

omit [CharP F 5] in include hq hr hN in
theorem Q2 : H q r / Q g q r ^ 2 = 4 * a g q ^ 2 * z g * d g r / N₀ g q r ^ 2 := by
  rw [Q_eq g q r hg hr]; simp only [H, a, z, d]; generalize N₀ g q r = n at hN; field_simp

omit [CharP F 5] in include hq hr hN in
theorem Q3 : Y q / Q g q r = 2 * d g r / (a g q * z g * N₀ g q r) := by
  rw [Q_eq g q r hg hr]; simp only [Y, a, z, d]; generalize N₀ g q r = n at hN; field_simp

include hq hr in
theorem H0 : H q r ^ 5 = 4 * a g q ^ 10 * z g ^ 7 / d g r ^ 5 := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  simp only [H, a, z, d]; field_simp; linear_combination 204 * h5

include hq hr in
theorem H1 : Q g q r / H q r ^ 3 = 4 * N₀ g q r * d g r ^ 2 / (a g q ^ 6 * z g ^ 4) := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  have h4 : (4 : F) ≠ 0 := four_ne
  rw [Q_eq g q r hg hr]; simp only [H, a, z, d]; generalize N₀ g q r = n; field_simp
  linear_combination (-51 * n) * h5

include hq hr in
theorem H3 : Y q / H q r ^ 3 = 3 * d g r ^ 3 / (a g q ^ 7 * z g ^ 5) := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  have h4 : (4 : F) ≠ 0 := four_ne
  simp only [Y, H, a, z, d]; field_simp
  linear_combination -38 * h5

include hq hr hN in
theorem G2 : Z q / Q g q r ^ 4 = -2 * a g q * d g r ^ 4 / N₀ g q r ^ 4 := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  rw [Q_eq g q r hg hr]; simp only [Z, a, d]; generalize N₀ g q r = n at hN; field_simp
  linear_combination h5

omit [CharP F 5] in include hr hN in
theorem G3 : τ r / Q g q r ^ 4 = d g r ^ 3 / (z g * N₀ g q r ^ 4) := by
  rw [Q_eq g q r hg hr]; simp only [τ, z, d]; generalize N₀ g q r = n at hN; field_simp

omit [CharP F 5] in include hr in
theorem τ0 : τ r ^ 5 = 1 / (d g r ^ 5 * z g) := by
  simp only [τ, z, d]; field_simp

omit [CharP F 5] in include hr in
theorem τ1 : Q g q r / τ r ^ 4 = N₀ g q r * d g r ^ 3 * z g := by
  rw [Q_eq g q r hg hr]; simp only [τ, z, d]; generalize N₀ g q r = n; field_simp

include hr in
theorem τ2 : Z q / τ r = -2 * a g q * d g r * z g := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  simp only [Z, τ, a, z, d]; field_simp
  linear_combination q * h5

omit [CharP F 5] in include hu in
theorem u0 : u ^ 5 = c g u ^ 5 * z g ^ 3 := by
  simp only [c, z]; field_simp

omit [CharP F 5] in include hu in
theorem u1 : q / u ^ 3 = a g q / (c g u ^ 3 * z g) := by
  simp only [a, c, z]; field_simp

omit [CharP F 5] in include hu in
theorem u2 : g / u ^ 2 = 1 / (c g u ^ 2 * z g) := by
  simp only [c, z]; field_simp

omit [CharP F 5] in include hu in
theorem u3 : r / u ^ 2 = d g r / (c g u ^ 2 * z g) := by
  simp only [c, z, d]; field_simp

/-! ### The Jacobian factors as weight `-1` functions times `g⁴` -/

omit [CharP F 5] in include hu hW in
theorem uB : 4 * z g * c g u / W₀ g q u = 4 * (B g q u)⁻¹ * g ^ 4 := by
  rw [B_eq g q u hg hu]; simp only [c, z]; generalize W₀ g q u = w at hW; field_simp

include hu in
theorem uA : c g u ^ 3 * z g ^ 2 = 4 * (A g u ^ 3)⁻¹ * g ^ 4 := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  simp only [c, z, A]; field_simp
  linear_combination h5

omit [CharP F 5] in include hu in
theorem uW : 4 * c g u ^ 2 * z g ^ 2 = 4 * (W u ^ 2)⁻¹ * g ^ 4 := by
  simp only [c, z, W]; field_simp

omit [CharP F 5] in include hr in
theorem uQ : 4 * N₀ g q r * z g / d g r = 4 * Q g q r * g ^ 4 := by
  rw [Q_eq g q r hg hr]; simp only [z, d]; generalize N₀ g q r = n; field_simp

include hq hr in
theorem uH : 4 * d g r ^ 2 / (a g q ^ 4 * z g ^ 2) = 4 * (H q r ^ 2)⁻¹ * g ^ 4 := by
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  have h4 : (4 : F) ≠ 0 := four_ne
  simp only [H, a, z, d]; field_simp
  linear_combination 3 * h5

omit [CharP F 5] in include hr hN in
theorem uG : 4 * d g r ^ 4 / N₀ g q r ^ 4 = 4 * (Q g q r ^ 4)⁻¹ * g ^ 4 := by
  rw [Q_eq g q r hg hr]; simp only [d]; generalize N₀ g q r = n at hN; field_simp

omit [CharP F 5] in include hr in
theorem uτ : 4 * d g r * z g = 4 * (τ r)⁻¹ * g ^ 4 := by
  simp only [τ, z, d]; field_simp

omit [CharP F 5] in include hu in
theorem uu : 4 / (c g u ^ 3 * z g) = 4 * (u ^ 3)⁻¹ * g ^ 4 := by
  simp only [c, z]; field_simp

end Eff.YTuples

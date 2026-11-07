import Eff.Euler

/-! # The invariant affine coordinates and their weights

This file proves the coordinate identities in the concrete existing function field. The
coordinate-ring presentation requires a separate kernel and generation argument.
-/

namespace Eff

open Red61 Red61.Fields
noncomputable section

def A : K := t - c₁ * w
def B : K := c₂ - c₁ * t + 3 * c₁ ^ 2 * w
def W : K := w

@[simp] theorem delta_A : delta A = 0 := by
  simp [A, Derivation.leibniz, smul_eq_mul]

@[simp] theorem delta_B : delta B = 0 := by
  simp only [B, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    delta_c₁, delta_c₂, delta_t, delta_w,
    show delta (3 : K) = 0 from delta.map_natCast 3, smul_eq_mul,
    nsmul_eq_mul]
  linear_combination c₁ * w * (CharP.cast_eq_zero K 5)

@[simp] theorem delta_W : delta W = 0 := delta_w

@[simp] theorem euler_A : euler A = 2 * A := by
  simp only [A, map_sub, Derivation.leibniz, euler_c₁, euler_t, euler_w, smul_eq_mul]
  ring

@[simp] theorem euler_B : euler B = B := by
  simp only [B, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    euler_c₁, euler_c₂, euler_t, euler_w,
    show euler (3 : K) = 0 from euler.map_natCast 3, smul_eq_mul,
    nsmul_eq_mul]
  ring

@[simp] theorem euler_W : euler W = 3 * W := euler_w

/-- The equation of the affine invariant hypersurface, inside the function field. -/
theorem invariant_relation :
    B ^ 5 - c₂ ^ 5 + c₁ ^ 5 * A ^ 5 + 3 * (c₁ ^ 5) ^ 2 * W ^ 5 = 0 := by
  simp only [A, B, W, add_pow_char (p := 5), sub_pow_char (p := 5), mul_pow]
  linear_combination (49 * c₁ ^ 10 * w ^ 5) * (CharP.cast_eq_zero K 5)

/-- The sum of the three adjunction numerator weights is one modulo five. -/
theorem adjunction_weight : (2 + 1 + 3 : ZMod 5) = 1 := by decide

/-- The resulting weight has exact additive order five. -/
theorem canonical_weight_order : addOrderOf (1 : ZMod 5) = 5 := ZMod.addOrderOf_one 5

end
end Eff

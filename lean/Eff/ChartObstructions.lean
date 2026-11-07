import Mathlib.Tactic

/-! # The six residue-field obstructions

These are the six separate calculations needed to exclude proportionality of the Euler
derivation to the foliation generator. They hold over arbitrary characteristic-five residue
fields, including non-rational points. Connecting them to scheme stalks is a separate step.
-/

namespace Eff.ChartObstructions

variable {F : Type*} [Field F] [CharP F 5]

private theorem cast_ne_zero (n : ℕ) (h : ¬ 5 ∣ n) : (n : F) ≠ 0 :=
  (CharP.cast_eq_zero_iff F 5 n).not.mpr h

theorem chart_one (c₂ t w l : F) (hc₂ : c₂ ≠ 0)
    (h₂ : c₂ = l * t) (ht : 2 * t = l * w) (hw : 3 * w = 0) : False := by
  have hw0 : w = 0 := (mul_eq_zero.mp hw).resolve_left (cast_ne_zero _ (by decide))
  have ht0 : t = 0 :=
    (mul_eq_zero.mp (by simpa [hw0] using ht)).resolve_left (cast_ne_zero 2 (by decide))
  exact hc₂ (by simpa [ht0] using h₂)

theorem chart_two (c₁ v l : F) (hc₁ : c₁ ≠ 0)
    (h₁ : -c₁ = l * v) (hv : 2 * v = 0) : False := by
  have hv0 : v = 0 := (mul_eq_zero.mp hv).resolve_left (cast_ne_zero _ (by decide))
  exact hc₁ (by simpa [hv0] using h₁)

theorem chart_three (c₁ t v l : F) (hc₁ : c₁ ≠ 0)
    (h₁ : -c₁ = l * (t ^ 2 * v))
    (ht : 3 * t = l * (-t)) (hv : 3 * v = l * (3 * v)) : False := by
  have hv0 : v ≠ 0 := by
    intro h
    exact hc₁ (by simpa [h] using h₁)
  have hl : l = 1 := by
    have h3 : (3 : F) * v ≠ 0 := mul_ne_zero (cast_ne_zero _ (by decide)) hv0
    exact (mul_right_cancel₀ h3 (by simpa using hv.symm))
  have ht0 : t = 0 := by
    have h4 : 4 * t = 0 := by
      rw [hl] at ht
      linear_combination ht
    exact (mul_eq_zero.mp h4).resolve_left (cast_ne_zero _ (by decide))
  exact hc₁ (by simpa [ht0] using h₁)

theorem chart_four (c₁ t e l : F) (hc₁ : c₁ ≠ 0)
    (h₁ : -c₁ = l * t)
    (ht : 3 * t = l * (-t * e)) (he : 4 * e = l * (3 * e ^ 2)) : False := by
  have ht0 : t ≠ 0 := by
    intro h
    exact hc₁ (by simpa [h] using h₁)
  have hle : l * e = -3 := by
    apply (mul_right_cancel₀ ht0)
    linear_combination ht
  have he0 : e ≠ 0 := by
    intro h
    exact cast_ne_zero (F := F) 3 (by decide) (by simpa [h] using hle.symm)
  have hbad : (13 : F) * e = 0 := by
    linear_combination he + 3 * e * hle
  exact he0 ((mul_eq_zero.mp hbad).resolve_left (cast_ne_zero _ (by decide)))

theorem chart_five (c₂ r l : F) (hc₂ : c₂ ≠ 0)
    (h₂ : c₂ = l * r) (hr : 4 * r = 0) : False := by
  have hr0 : r = 0 := (mul_eq_zero.mp hr).resolve_left (cast_ne_zero _ (by decide))
  exact hc₂ (by simpa [hr0] using h₂)

omit [CharP F 5] in
theorem chart_six (c₁ x t l : F) (hc₁ : c₁ ≠ 0)
    (h₁ : -c₁ = l * (x ^ 2 * t)) (ht : t = 0) : False := by
  exact hc₁ (by simpa [ht] using h₁)

omit [CharP F 5] in
/-- At the exceptional point a unit eigenvector of weight minus one prevents vanishing. -/
theorem special_point (q dq : F) (hq : q ≠ 0) (hweight : dq = -q)
    (hvanish : dq = 0) : False := by
  exact hq (by simpa [hvanish] using hweight.symm)

end Eff.ChartObstructions

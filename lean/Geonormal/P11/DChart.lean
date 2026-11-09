import Geonormal.P11.Field

/-! # The components `ξ_n` in the coordinates of the chart `D`

`ξ_n α″ = Φ_n(w, α″, β″, ρ)`, a polynomial, where `a = 1/(α″w⁴)`, `b = β″/(α″²w⁶)` and
`σ = ρ - 2β″/(α″w²)`, using `β″² = α″ + w¹¹α″⁴`.
-/

namespace Geonormal.P11

noncomputable section

/-! ## `ξ_n` in the coordinates of the chart `D` -/

section Phi

variable {R : Type*} [CommRing R]

/-- `ξ_0 α″` in the coordinates of the chart `D`. -/
def Φ0 (w al be rh : R) : R := -w ^ 2 * al * rh ^ 10 - 2 * be * rh ^ 9
    - 4 * w ^ 9 * al ^ 3 * rh ^ 8 + 3 * w ^ 7 * al ^ 2 * be * rh ^ 7 + 2 * w ^ 5 * al ^ 2 * rh ^ 6
    - 5 * w ^ 16 * al ^ 5 * rh ^ 6 + w ^ 3 * al * be * rh ^ 5 + w ^ 14 * al ^ 4 * be * rh ^ 5
    + 5 * w * al * rh ^ 4 + w ^ 12 * al ^ 4 * rh ^ 4 + 2 * w ^ 23 * al ^ 7 * rh ^ 4
    - w ^ 10 * al ^ 3 * be * rh ^ 3 + 4 * w ^ 21 * al ^ 6 * be * rh ^ 3 + w ^ 8 * al ^ 3 * rh ^ 2
    - 3 * w ^ 30 * al ^ 9 * rh ^ 2 - 4 * w ^ 6 * al ^ 2 * be * rh - 2 * w ^ 17 * al ^ 5 * be * rh
    + 5 * w ^ 28 * al ^ 8 * be * rh + 2 * w ^ 4 * al ^ 2 - 2 * w ^ 26 * al ^ 8 - w ^ 37 * al ^ 11

/-- `ξ_1 α″` in the coordinates of the chart `D`. -/
def Φ1 (w al be rh : R) : R := 2 * w ^ 2 * al * rh ^ 9 - 3 * be * rh ^ 8
    + 2 * w ^ 9 * al ^ 3 * rh ^ 7 - 2 * w ^ 7 * al ^ 2 * be * rh ^ 6 + 2 * w ^ 5 * al ^ 2 * rh ^ 5
    - 5 * w ^ 16 * al ^ 5 * rh ^ 5 - w ^ 3 * al * be * rh ^ 4 - w ^ 14 * al ^ 4 * be * rh ^ 4
    - 4 * w * al * rh ^ 3 - 3 * w ^ 12 * al ^ 4 * rh ^ 3 + 5 * w ^ 23 * al ^ 7 * rh ^ 3
    + 5 * w ^ 10 * al ^ 3 * be * rh ^ 2 + 2 * w ^ 21 * al ^ 6 * be * rh ^ 2
    + 4 * w ^ 8 * al ^ 3 * rh - w ^ 30 * al ^ 9 * rh + 3 * w ^ 6 * al ^ 2 * be
    - 4 * w ^ 17 * al ^ 5 * be - w ^ 28 * al ^ 8 * be

/-- `ξ_2 α″` in the coordinates of the chart `D`. -/
def Φ2 (w al be rh : R) : R := -4 * w ^ 2 * al * rh ^ 8 - 2 * be * rh ^ 7
    + 3 * w ^ 9 * al ^ 3 * rh ^ 6 - w ^ 7 * al ^ 2 * be * rh ^ 5 - w ^ 5 * al ^ 2 * rh ^ 4
    - 3 * w ^ 16 * al ^ 5 * rh ^ 4 - 4 * w ^ 3 * al * be * rh ^ 3
    - 4 * w ^ 14 * al ^ 4 * be * rh ^ 3 - w * al * rh ^ 2 + 2 * w ^ 12 * al ^ 4 * rh ^ 2
    + 4 * w ^ 23 * al ^ 7 * rh ^ 2 - w ^ 10 * al ^ 3 * be * rh + 4 * w ^ 21 * al ^ 6 * be * rh
    + 4 * w ^ 8 * al ^ 3 - w ^ 30 * al ^ 9

/-- `ξ_3 α″` in the coordinates of the chart `D`. -/
def Φ3 (w al be rh : R) : R := -3 * w ^ 2 * al * rh ^ 7 - 2 * be * rh ^ 6
    + w ^ 9 * al ^ 3 * rh ^ 5 + 4 * w ^ 7 * al ^ 2 * be * rh ^ 4 + w ^ 5 * al ^ 2 * rh ^ 3
    + 3 * w ^ 16 * al ^ 5 * rh ^ 3 + 3 * w ^ 3 * al * be * rh ^ 2
    + 3 * w ^ 14 * al ^ 4 * be * rh ^ 2 - 5 * w * al * rh - w ^ 12 * al ^ 4 * rh
    - 2 * w ^ 23 * al ^ 7 * rh + 3 * w ^ 10 * al ^ 3 * be - w ^ 21 * al ^ 6 * be

/-- `ξ_4 α″` in the coordinates of the chart `D`. -/
def Φ4 (w al be rh : R) : R := -5 * w ^ 2 * al * rh ^ 6 + 5 * be * rh ^ 5
    - 3 * w ^ 9 * al ^ 3 * rh ^ 4 - 3 * w ^ 7 * al ^ 2 * be * rh ^ 3 - 4 * w ^ 5 * al ^ 2 * rh ^ 2
    - w ^ 16 * al ^ 5 * rh ^ 2 + 3 * w ^ 3 * al * be * rh + 3 * w ^ 14 * al ^ 4 * be * rh
    + 3 * w * al + 5 * w ^ 12 * al ^ 4 - w ^ 23 * al ^ 7

/-- `ξ_5 α″` in the coordinates of the chart `D`. -/
def Φ5 (w al be rh : R) : R := -w ^ 2 * al * rh ^ 5 - be * rh ^ 4 + 4 * w ^ 9 * al ^ 3 * rh ^ 3
    + 3 * w ^ 7 * al ^ 2 * be * rh ^ 2 - w ^ 5 * al ^ 2 * rh - 3 * w ^ 16 * al ^ 5 * rh
    - w ^ 3 * al * be - w ^ 14 * al ^ 4 * be

/-- `ξ_6 α″` in the coordinates of the chart `D`. -/
def Φ6 (w al be rh : R) : R := 2 * w ^ 2 * al * rh ^ 4 - 5 * be * rh ^ 3
    + 4 * w ^ 9 * al ^ 3 * rh ^ 2 + 2 * w ^ 7 * al ^ 2 * be * rh - 4 * w ^ 5 * al ^ 2
    - w ^ 16 * al ^ 5

/-- `ξ_7 α″` in the coordinates of the chart `D`. -/
def Φ7 (w al be rh : R) : R := -4 * w ^ 2 * al * rh ^ 3 + 2 * be * rh ^ 2
    - 4 * w ^ 9 * al ^ 3 * rh - w ^ 7 * al ^ 2 * be

/-- `ξ_8 α″` in the coordinates of the chart `D`. -/
def Φ8 (w al be rh : R) : R := -3 * w ^ 2 * al * rh ^ 2 + be * rh - w ^ 9 * al ^ 3

/-- `ξ_9 α″` in the coordinates of the chart `D`. -/
def Φ9 (w al be rh : R) : R := -5 * w ^ 2 * al * rh - be

/-- `ξ_10 α″` in the coordinates of the chart `D`. -/
def Φ10 (w al _be _rh : R) : R := -w ^ 2 * al
def ΦE (n : Fin 11) (w al be rh : R) : R :=
  ![Φ0 w al be rh, Φ1 w al be rh, Φ2 w al be rh, Φ3 w al be rh, Φ4 w al be rh, Φ5 w al be rh,
    Φ6 w al be rh, Φ7 w al be rh, Φ8 w al be rh, Φ9 w al be rh, Φ10 w al be rh] n

end Phi

set_option maxHeartbeats 4000000 in
theorem Φ_ident {F : Type*} [Field F] [CharP F 11] (n : Fin 11) (w al be rh : F) (hw : w ≠ 0)
    (hal : al ≠ 0) (hR : be ^ 2 = al + w ^ 11 * al ^ 4) :
    θE n (1 / (al * w ^ 4)) (be / (al ^ 2 * w ^ 6)) (rh - 2 * be / (al * w ^ 2)) * w ^ 2 * al =
      ΦE n w al be rh := by
  fin_cases n <;> simp [θE, ΦE, θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10, Φ0, Φ1, Φ2, Φ3, Φ4,
    Φ5, Φ6, Φ7, Φ8, Φ9, Φ10] <;> field_simp <;> grind (ringSteps := 1000000)

end
end Geonormal.P11

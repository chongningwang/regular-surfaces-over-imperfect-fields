import Geonormal.P11.Field

/-! # The components `θ_k` in the coordinates of the chart `B`

`θ_k α = Ψ_k(u, α, β, ρ)`, a polynomial, where `a = 1/α`, `b = β/α²` and `σ = ρ - 2β/α`, using
`β² = α + uα⁴`.
-/

namespace Geonormal.P11

noncomputable section

section Psi

variable {R : Type*} [CommRing R]

/-- `θ_0 α` in the coordinates of the chart `B`. -/
def Ψ0 (u al be rh : R) : R := -al * rh ^ 10 - 2 * be * rh ^ 9 - 4 * u * al ^ 3 * rh ^ 8
    + 3 * u * al ^ 2 * be * rh ^ 7 + 2 * u * al ^ 2 * rh ^ 6 - 5 * u ^ 2 * al ^ 5 * rh ^ 6
    + u * al * be * rh ^ 5 + u ^ 2 * al ^ 4 * be * rh ^ 5 + 5 * u * al * rh ^ 4
    + u ^ 2 * al ^ 4 * rh ^ 4 + 2 * u ^ 3 * al ^ 7 * rh ^ 4 - u ^ 2 * al ^ 3 * be * rh ^ 3
    + 4 * u ^ 3 * al ^ 6 * be * rh ^ 3 + u ^ 2 * al ^ 3 * rh ^ 2 - 3 * u ^ 4 * al ^ 9 * rh ^ 2
    - 4 * u ^ 2 * al ^ 2 * be * rh - 2 * u ^ 3 * al ^ 5 * be * rh + 5 * u ^ 4 * al ^ 8 * be * rh
    + 2 * u ^ 2 * al ^ 2 - 2 * u ^ 4 * al ^ 8 - u ^ 5 * al ^ 11

/-- `θ_1 α` in the coordinates of the chart `B`. -/
def Ψ1 (u al be rh : R) : R := 2 * al * rh ^ 9 - 3 * be * rh ^ 8 + 2 * u * al ^ 3 * rh ^ 7
    - 2 * u * al ^ 2 * be * rh ^ 6 + 2 * u * al ^ 2 * rh ^ 5 - 5 * u ^ 2 * al ^ 5 * rh ^ 5
    - u * al * be * rh ^ 4 - u ^ 2 * al ^ 4 * be * rh ^ 4 - 4 * u * al * rh ^ 3
    - 3 * u ^ 2 * al ^ 4 * rh ^ 3 + 5 * u ^ 3 * al ^ 7 * rh ^ 3 + 5 * u ^ 2 * al ^ 3 * be * rh ^ 2
    + 2 * u ^ 3 * al ^ 6 * be * rh ^ 2 + 4 * u ^ 2 * al ^ 3 * rh - u ^ 4 * al ^ 9 * rh
    + 3 * u ^ 2 * al ^ 2 * be - 4 * u ^ 3 * al ^ 5 * be - u ^ 4 * al ^ 8 * be

/-- `θ_2 α` in the coordinates of the chart `B`. -/
def Ψ2 (u al be rh : R) : R := -4 * al * rh ^ 8 - 2 * be * rh ^ 7 + 3 * u * al ^ 3 * rh ^ 6
    - u * al ^ 2 * be * rh ^ 5 - u * al ^ 2 * rh ^ 4 - 3 * u ^ 2 * al ^ 5 * rh ^ 4
    - 4 * u * al * be * rh ^ 3 - 4 * u ^ 2 * al ^ 4 * be * rh ^ 3 - u * al * rh ^ 2
    + 2 * u ^ 2 * al ^ 4 * rh ^ 2 + 4 * u ^ 3 * al ^ 7 * rh ^ 2 - u ^ 2 * al ^ 3 * be * rh
    + 4 * u ^ 3 * al ^ 6 * be * rh + 4 * u ^ 2 * al ^ 3 - u ^ 4 * al ^ 9

/-- `θ_3 α` in the coordinates of the chart `B`. -/
def Ψ3 (u al be rh : R) : R := -3 * al * rh ^ 7 - 2 * be * rh ^ 6 + u * al ^ 3 * rh ^ 5
    + 4 * u * al ^ 2 * be * rh ^ 4 + u * al ^ 2 * rh ^ 3 + 3 * u ^ 2 * al ^ 5 * rh ^ 3
    + 3 * u * al * be * rh ^ 2 + 3 * u ^ 2 * al ^ 4 * be * rh ^ 2 - 5 * u * al * rh
    - u ^ 2 * al ^ 4 * rh - 2 * u ^ 3 * al ^ 7 * rh + 3 * u ^ 2 * al ^ 3 * be
    - u ^ 3 * al ^ 6 * be

/-- `θ_4 α` in the coordinates of the chart `B`. -/
def Ψ4 (u al be rh : R) : R := -5 * al * rh ^ 6 + 5 * be * rh ^ 5 - 3 * u * al ^ 3 * rh ^ 4
    - 3 * u * al ^ 2 * be * rh ^ 3 - 4 * u * al ^ 2 * rh ^ 2 - u ^ 2 * al ^ 5 * rh ^ 2
    + 3 * u * al * be * rh + 3 * u ^ 2 * al ^ 4 * be * rh + 3 * u * al + 5 * u ^ 2 * al ^ 4
    - u ^ 3 * al ^ 7

/-- `θ_5 α` in the coordinates of the chart `B`. -/
def Ψ5 (u al be rh : R) : R := -al * rh ^ 5 - be * rh ^ 4 + 4 * u * al ^ 3 * rh ^ 3
    + 3 * u * al ^ 2 * be * rh ^ 2 - u * al ^ 2 * rh - 3 * u ^ 2 * al ^ 5 * rh - u * al * be
    - u ^ 2 * al ^ 4 * be

/-- `θ_6 α` in the coordinates of the chart `B`. -/
def Ψ6 (u al be rh : R) : R := 2 * al * rh ^ 4 - 5 * be * rh ^ 3 + 4 * u * al ^ 3 * rh ^ 2
    + 2 * u * al ^ 2 * be * rh - 4 * u * al ^ 2 - u ^ 2 * al ^ 5

/-- `θ_7 α` in the coordinates of the chart `B`. -/
def Ψ7 (u al be rh : R) : R := -4 * al * rh ^ 3 + 2 * be * rh ^ 2 - 4 * u * al ^ 3 * rh
    - u * al ^ 2 * be

/-- `θ_8 α` in the coordinates of the chart `B`. -/
def Ψ8 (u al be rh : R) : R := -3 * al * rh ^ 2 + be * rh - u * al ^ 3

/-- `θ_9 α` in the coordinates of the chart `B`. -/
def Ψ9 (_u al be rh : R) : R := -5 * al * rh - be

/-- `θ_10 α` in the coordinates of the chart `B`. -/
def Ψ10 (_u al _be _rh : R) : R := -al
def ΨE (n : Fin 11) (u al be rh : R) : R :=
  ![Ψ0 u al be rh, Ψ1 u al be rh, Ψ2 u al be rh, Ψ3 u al be rh, Ψ4 u al be rh, Ψ5 u al be rh,
    Ψ6 u al be rh, Ψ7 u al be rh, Ψ8 u al be rh, Ψ9 u al be rh, Ψ10 u al be rh] n

end Psi

set_option maxHeartbeats 8000000 in
theorem ΨE_ident {F : Type*} [Field F] [CharP F 11] (n : Fin 11) (u al be rh : F) (hal : al ≠ 0)
    (hR : be ^ 2 = al + u * al ^ 4) :
    θE n (1 / al) (be / al ^ 2) (rh - 2 * be / al) * al = ΨE n u al be rh := by
  fin_cases n <;> simp [θE, ΨE, θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8, θ9, θ10, Ψ0, Ψ1, Ψ2, Ψ3, Ψ4,
    Ψ5, Ψ6, Ψ7, Ψ8, Ψ9, Ψ10] <;> field_simp <;> grind (ringSteps := 1000000)

end
end Geonormal.P11

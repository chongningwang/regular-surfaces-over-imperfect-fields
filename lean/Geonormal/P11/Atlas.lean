import Geonormal.P11.Components
import Geonormal.P11.DChart
import Red61.AlgebraicGeometry.Atlas

/-! # The atlas of the characteristic-11 surface

The four chart rings are glued along principal localizations:

| pair | inverted in the first chart | inverted in the second chart |
|---|---|---|
| `A, B` | `a` | `α` |
| `A, D` | `ua` | `wα″` |
| `A, P` | `u` | `w` |
| `B, D` | `u` | `w` |
| `B, P` | `uα` | `wa″` |
| `D, P` | `α″` | `a″` |

Elements of `P` are recognized through their images in `K'` (`mem_chartP_of_ι`). Only the pair
`D, P` needs an explicit expansion: `ξ_n α″` is a polynomial `Φ_n` in the coordinates of `D`.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry

noncomputable section

set_option maxHeartbeats 1000000 in
theorem ΦE_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 11) (w al be rh : R) :
    f (ΦE n w al be rh) = ΦE n (f w) (f al) (f be) (f rh) := by
  fin_cases n <;> simp [ΦE, Φ0, Φ1, Φ2, Φ3, Φ4, Φ5, Φ6, Φ7, Φ8, Φ9, Φ10, map_ofNat]

theorem ΦE_mem {K : Type*} [CommRing K] (T : Subring K) (n : Fin 11) {w al be rh : K}
    (hw : w ∈ T) (hal : al ∈ T) (hbe : be ∈ T) (hrh : rh ∈ T) : ΦE n w al be rh ∈ T := by
  have h := ΦE_map T.subtype n ⟨w, hw⟩ ⟨al, hal⟩ ⟨be, hbe⟩ ⟨rh, hrh⟩
  simp only [Subring.coe_subtype] at h
  rw [← h]
  exact Subtype.prop _

/-! ## Membership in the charts -/

theorem aL_mem_A : aL ∈ chartA := Algebra.subset_adjoin (by simp)
theorem bL_mem_A : bL ∈ chartA := Algebra.subset_adjoin (by simp)
theorem σL_mem_A : σL ∈ chartA := Algebra.subset_adjoin (by simp)
theorem uL_mem_A : uL ∈ chartA :=
  chartA.sub_mem (chartA.pow_mem bL_mem_A 2) (chartA.pow_mem aL_mem_A 3)
theorem θE_mem_A (n : Fin 11) : θE n aL bL σL ∈ chartA :=
  θE_mem chartA.toSubring n aL_mem_A bL_mem_A σL_mem_A

theorem uL_mem_B : uL ∈ chartB := Algebra.subset_adjoin (by simp)
theorem αL_mem_B : αL ∈ chartB := Algebra.subset_adjoin (by simp)
theorem βL_mem_B : βL ∈ chartB := Algebra.subset_adjoin (by simp)
theorem ρL_mem_B : ρL ∈ chartB := Algebra.subset_adjoin (by simp)

theorem wL_mem_D : wL ∈ chartD := Algebra.subset_adjoin (by simp)
theorem αD_mem_D : αD ∈ chartD := Algebra.subset_adjoin (by simp)
theorem βD_mem_D : βD ∈ chartD := Algebra.subset_adjoin (by simp)
theorem ρL_mem_D : ρL ∈ chartD := Algebra.subset_adjoin (by simp)

theorem algebraMap_C (z : k') : algebraMap S₂ K' (MvPolynomial.C z) = algebraMap k' K' z := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem wL_mem_P : wL ∈ chartP :=
  mem_chartP_of_ι (s := MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) (by
    rw [ι_wL]; simp [wK, xK, yK])
theorem aP_mem_P : aP ∈ chartP :=
  mem_chartP_of_ι (s := MvPolynomial.X 0 ^ 11) (by rw [ι_aP]; simp [xK])
theorem bP_mem_P : bP ∈ chartP :=
  mem_chartP_of_ι (s := MvPolynomial.X 1 ^ 11) (by rw [ι_bP]; simp [yK])
theorem sP_mem_P : sP ∈ chartP :=
  mem_chartP_of_ι (s := MvPolynomial.X 0 * MvPolynomial.X 1 *
    (MvPolynomial.X 1 ^ 2 - 3 * MvPolynomial.X 0 ^ 3) -
      2 * MvPolynomial.C γ * (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) ^ 2) (by
    rw [ι_sP]; simp [sK, wK, xK, yK, γK, map_ofNat, algebraMap_C])
theorem ρaP_mem_P : ρL * aP ∈ chartP :=
  mem_chartP_of_ι (s := Ψ (MvPolynomial.X 0) (MvPolynomial.X 1) -
    2 * MvPolynomial.C γ * MvPolynomial.X 0 ^ 11) (by
    rw [ι_ρaP]; simp [Ψ, xK, yK, γK, map_ofNat, algebraMap_C])

/-! ## Relations between the coordinates -/

theorem αL_ne_zero : αL ≠ 0 := inv_ne_zero aL_ne_zero
theorem aP_ne_zero : aP ≠ 0 := mul_ne_zero aL_ne_zero (pow_ne_zero _ wL_ne_zero)
theorem αD_ne_zero : αD ≠ 0 := div_ne_zero (pow_ne_zero _ uL_ne_zero) aL_ne_zero

theorem uw : uL * wL = 1 := mul_inv_cancel₀ uL_ne_zero

theorem ξ_eq (n : Fin 11) : ξ n = θE n aL bL σL * wL ^ 2 := rfl

/-- `βD² = αD + w¹¹ αD⁴`. -/
theorem βD_sq : βD ^ 2 = αD + wL ^ 11 * αD ^ 4 := by
  have ha := aL_ne_zero
  have hu := uL_ne_zero
  simp only [βD, αD, wL, uL] at *
  field_simp
  ring

theorem aL_D : aL = 1 / (αD * wL ^ 4) := by
  have ha := aL_ne_zero
  have hu := uL_ne_zero
  simp only [αD, wL]
  field_simp

theorem bL_D : bL = βD / (αD ^ 2 * wL ^ 6) := by
  have ha := aL_ne_zero
  have hu := uL_ne_zero
  simp only [βD, αD, wL]
  field_simp

theorem σL_D : σL = ρL - 2 * βD / (αD * wL ^ 2) := by
  have ha := aL_ne_zero
  have hu := uL_ne_zero
  simp only [ρL, βD, αD, wL]
  field_simp
  ring

/-- `ξ_n α″` in the coordinates of `D`. -/
theorem ξ_D (n : Fin 11) : ξ n * αD = ΦE n wL αD βD ρL := by
  rw [ξ_eq, aL_D, bL_D, σL_D]
  exact Φ_ident n wL αD βD ρL wL_ne_zero αD_ne_zero βD_sq

/-! ## The overlaps -/

theorem loc_of (A B : Subalgebra k L) (d : L) (hdA : d ∈ A) (hd : d ≠ 0) (hinv : d⁻¹ ∈ A ⊔ B)
    (hgen : B ≤ A ⊔ Algebra.adjoin k ({d⁻¹} : Set L)) :
    letI := inclusionAlgebra (show A ≤ A ⊔ B from le_sup_left)
    ∃ e : A, IsLocalization.Away e ↥(A ⊔ B) :=
  ⟨⟨d, hdA⟩, subalgebra_isLocalizationAway A (A ⊔ B) le_sup_left ⟨d, hdA⟩ hd hinv
    (sup_le le_sup_left hgen)⟩

theorem inv_mem_adj {A : Subalgebra k L} (d : L) : d⁻¹ ∈ A ⊔ Algebra.adjoin k ({d⁻¹} : Set L) :=
  le_sup_right (a := A) (Algebra.subset_adjoin (Set.mem_singleton _))

theorem mem_adj {A : Subalgebra k L} {z : L} (d : L) (hz : z ∈ A) :
    z ∈ A ⊔ Algebra.adjoin k ({d⁻¹} : Set L) := le_sup_left (a := A) hz

theorem ofNat_mem' (A : Subalgebra k L) (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : L) ∈ A := by
  simpa using natCast_mem A n

theorem loc_AB : letI := inclusionAlgebra (show chartA ≤ chartA ⊔ chartB from le_sup_left)
    ∃ e : chartA, IsLocalization.Away e ↥(chartA ⊔ chartB) := by
  have hinv : aL⁻¹ ∈ chartA ⊔ chartB := le_sup_right (a := chartA) αL_mem_B
  refine loc_of _ _ aL aL_mem_A aL_ne_zero hinv (Algebra.adjoin_le ?_)
  set M := chartA ⊔ Algebra.adjoin k ({aL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartA) aL
  have ha := mem_adj aL aL_mem_A
  have hb := mem_adj aL bL_mem_A
  have hs := mem_adj aL σL_mem_A
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact mem_adj aL uL_mem_A
  · exact hi
  · rw [βL, div_eq_mul_inv, ← inv_pow]; exact M.mul_mem hb (M.pow_mem hi 2)
  · rw [ρL, mul_div_assoc, div_eq_mul_inv]
    exact M.add_mem hs (M.mul_mem (ofNat_mem' M 2) (M.mul_mem hb hi))

/-- Closes membership goals for polynomial expressions in a subalgebra. -/
macro "subalg_mem" : tactic => `(tactic| repeat (first
  | assumption
  | apply ofNat_mem'
  | apply Subalgebra.one_mem
  | apply Subalgebra.add_mem | apply Subalgebra.sub_mem | apply Subalgebra.mul_mem
  | apply Subalgebra.pow_mem | apply Subalgebra.neg_mem))

theorem loc_self (A : Subalgebra k L) :
    letI := inclusionAlgebra (show A ≤ A ⊔ A from le_sup_left)
    ∃ e : A, IsLocalization.Away e ↥(A ⊔ A) :=
  loc_of A A 1 A.one_mem one_ne_zero (by rw [inv_one]; exact Subalgebra.one_mem _)
    (le_sup_left (a := A))

theorem θE_mem_sup {M : Subalgebra k L} (n : Fin 11) (ha : aL ∈ M) (hb : bL ∈ M)
    (hs : σL ∈ M) : θE n aL bL σL ∈ M := θE_mem M.toSubring n ha hb hs

theorem loc_AD : letI := inclusionAlgebra (show chartA ≤ chartA ⊔ chartD from le_sup_left)
    ∃ e : chartA, IsLocalization.Away e ↥(chartA ⊔ chartD) := by
  have hu := uL_ne_zero
  have ha0 := aL_ne_zero
  refine loc_of _ _ (uL * aL) (chartA.mul_mem uL_mem_A aL_mem_A) (mul_ne_zero hu ha0) ?_
    (Algebra.adjoin_le ?_)
  · have : (uL * aL)⁻¹ = αD * wL ^ 5 := by simp only [αD, wL]; field_simp
    rw [this]
    exact le_sup_right (a := chartA) (chartD.mul_mem αD_mem_D (chartD.pow_mem wL_mem_D 5))
  set M := chartA ⊔ Algebra.adjoin k ({(uL * aL)⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartA) (uL * aL)
  have ha := mem_adj (uL * aL) aL_mem_A
  have hb := mem_adj (uL * aL) bL_mem_A
  have hs := mem_adj (uL * aL) σL_mem_A
  have huM := mem_adj (uL * aL) uL_mem_A
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [show wL = aL * (uL * aL)⁻¹ by simp only [wL]; field_simp]; subalg_mem
  · rw [show αD = uL ^ 5 * (uL * aL)⁻¹ by simp only [αD]; field_simp <;> ring]; subalg_mem
  · rw [show βD = uL ^ 4 * bL * ((uL * aL)⁻¹) ^ 2 by simp only [βD]; field_simp <;> ring]; subalg_mem
  · rw [show ρL = σL + 2 * bL * uL * (uL * aL)⁻¹ by simp only [ρL]; field_simp]; subalg_mem

theorem loc_AP : letI := inclusionAlgebra (show chartA ≤ chartA ⊔ chartP from le_sup_left)
    ∃ e : chartA, IsLocalization.Away e ↥(chartA ⊔ chartP) := by
  have hinv : uL⁻¹ ∈ chartA ⊔ chartP := le_sup_right (a := chartA) wL_mem_P
  refine loc_of _ _ uL uL_mem_A uL_ne_zero hinv (Algebra.adjoin_le ?_)
  set M := chartA ⊔ Algebra.adjoin k ({uL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartA) uL
  rintro _ ⟨n, rfl⟩
  rw [ξ_eq, wL]
  exact M.mul_mem (mem_adj uL (θE_mem_A n)) (M.pow_mem hi 2)

theorem loc_BA : letI := inclusionAlgebra (show chartB ≤ chartB ⊔ chartA from le_sup_left)
    ∃ e : chartB, IsLocalization.Away e ↥(chartB ⊔ chartA) := by
  have hinv : αL⁻¹ ∈ chartB ⊔ chartA := by
    rw [αL, inv_inv]
    exact le_sup_right (a := chartB) aL_mem_A
  refine loc_of _ _ αL αL_mem_B αL_ne_zero hinv (Algebra.adjoin_le ?_)
  set M := chartB ⊔ Algebra.adjoin k ({αL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartB) αL
  have hβ := mem_adj αL βL_mem_B
  have hρ := mem_adj αL ρL_mem_B
  have ha0 := aL_ne_zero
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · rw [show aL = αL⁻¹ by simp [αL]]; exact hi
  · rw [show bL = βL * (αL⁻¹) ^ 2 by simp only [βL, αL]; field_simp]; subalg_mem
  · rw [show σL = ρL - 2 * βL * αL⁻¹ by simp only [ρL, βL, αL]; field_simp <;> ring]; subalg_mem

theorem loc_BD : letI := inclusionAlgebra (show chartB ≤ chartB ⊔ chartD from le_sup_left)
    ∃ e : chartB, IsLocalization.Away e ↥(chartB ⊔ chartD) := by
  have hinv : uL⁻¹ ∈ chartB ⊔ chartD := le_sup_right (a := chartB) wL_mem_D
  refine loc_of _ _ uL uL_mem_B uL_ne_zero hinv (Algebra.adjoin_le ?_)
  set M := chartB ⊔ Algebra.adjoin k ({uL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartB) uL
  have hu := mem_adj uL uL_mem_B
  have hα := mem_adj uL αL_mem_B
  have hβ := mem_adj uL βL_mem_B
  have hρ := mem_adj uL ρL_mem_B
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hi
  · rw [show αD = uL ^ 4 * αL by simp only [αD, αL]; field_simp]; subalg_mem
  · rw [show βD = uL ^ 2 * βL by simp only [βD, βL]; field_simp]; subalg_mem
  · exact hρ

theorem loc_BP : letI := inclusionAlgebra (show chartB ≤ chartB ⊔ chartP from le_sup_left)
    ∃ e : chartB, IsLocalization.Away e ↥(chartB ⊔ chartP) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  refine loc_of _ _ (uL * αL) (chartB.mul_mem uL_mem_B αL_mem_B) (mul_ne_zero hu0 αL_ne_zero) ?_
    (Algebra.adjoin_le ?_)
  · rw [show (uL * αL)⁻¹ = aP * uL ^ 3 by simp only [aP, αL, wL]; field_simp]
    exact (chartB ⊔ chartP).mul_mem (le_sup_right (a := chartB) aP_mem_P)
      (le_sup_left (a := chartB) (chartB.pow_mem uL_mem_B 3))
  set M := chartB ⊔ Algebra.adjoin k ({(uL * αL)⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartB) (uL * αL)
  have hu := mem_adj (uL * αL) uL_mem_B
  have hα := mem_adj (uL * αL) αL_mem_B
  have hβ := mem_adj (uL * αL) βL_mem_B
  have hρ := mem_adj (uL * αL) ρL_mem_B
  have ha : aL ∈ M := by
    rw [show aL = uL * (uL * αL)⁻¹ by simp only [αL]; field_simp]; subalg_mem
  have hb : bL ∈ M := by
    rw [show bL = βL * aL ^ 2 by simp only [βL]; field_simp]; subalg_mem
  have hs : σL ∈ M := by
    rw [show σL = ρL - 2 * βL * aL by simp only [ρL, βL]; field_simp <;> ring]; subalg_mem
  have hw : wL ∈ M := by
    rw [show wL = αL * (uL * αL)⁻¹ by simp only [wL, αL]; field_simp]; subalg_mem
  rintro _ ⟨n, rfl⟩
  rw [ξ_eq]
  exact M.mul_mem (θE_mem_sup n ha hb hs) (M.pow_mem hw 2)

theorem loc_DA : letI := inclusionAlgebra (show chartD ≤ chartD ⊔ chartA from le_sup_left)
    ∃ e : chartD, IsLocalization.Away e ↥(chartD ⊔ chartA) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  refine loc_of _ _ (wL * αD) (chartD.mul_mem wL_mem_D αD_mem_D) (mul_ne_zero wL_ne_zero αD_ne_zero)
    ?_ (Algebra.adjoin_le ?_)
  · rw [show (wL * αD)⁻¹ = aL * wL ^ 3 by simp only [αD, wL]; field_simp]
    exact (chartD ⊔ chartA).mul_mem (le_sup_right (a := chartD) aL_mem_A)
      (le_sup_left (a := chartD) (chartD.pow_mem wL_mem_D 3))
  set M := chartD ⊔ Algebra.adjoin k ({(wL * αD)⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartD) (wL * αD)
  have hw := mem_adj (wL * αD) wL_mem_D
  have hα := mem_adj (wL * αD) αD_mem_D
  have hβ := mem_adj (wL * αD) βD_mem_D
  have hρ := mem_adj (wL * αD) ρL_mem_D
  have ha : aL ∈ M := by
    rw [show aL = αD ^ 3 * ((wL * αD)⁻¹) ^ 4 by simp only [αD, wL]; field_simp]; subalg_mem
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · rw [show bL = βD * aL ^ 2 * wL ^ 2 by simp only [βD, wL]; field_simp]; subalg_mem
  · rw [show σL = ρL - 2 * βD * aL * wL ^ 2 by simp only [ρL, βD, wL]; field_simp <;> ring]
    subalg_mem

theorem loc_DB : letI := inclusionAlgebra (show chartD ≤ chartD ⊔ chartB from le_sup_left)
    ∃ e : chartD, IsLocalization.Away e ↥(chartD ⊔ chartB) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  have hinv : wL⁻¹ ∈ chartD ⊔ chartB := by
    rw [wL, inv_inv]
    exact le_sup_right (a := chartD) uL_mem_B
  refine loc_of _ _ wL wL_mem_D wL_ne_zero hinv (Algebra.adjoin_le ?_)
  set M := chartD ⊔ Algebra.adjoin k ({wL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartD) wL
  have hw := mem_adj wL wL_mem_D
  have hα := mem_adj wL αD_mem_D
  have hβ := mem_adj wL βD_mem_D
  have hρ := mem_adj wL ρL_mem_D
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [show uL = wL⁻¹ by simp [wL]]; exact hi
  · rw [show αL = αD * wL ^ 4 by simp only [αL, αD, wL]; field_simp]; subalg_mem
  · rw [show βL = βD * wL ^ 2 by simp only [βL, βD, wL]; field_simp]; subalg_mem
  · exact hρ

theorem loc_DP : letI := inclusionAlgebra (show chartD ≤ chartD ⊔ chartP from le_sup_left)
    ∃ e : chartD, IsLocalization.Away e ↥(chartD ⊔ chartP) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  refine loc_of _ _ αD αD_mem_D αD_ne_zero ?_ (Algebra.adjoin_le ?_)
  · rw [show αD⁻¹ = aP by simp only [αD, aP, wL]; field_simp]
    exact le_sup_right (a := chartD) aP_mem_P
  set M := chartD ⊔ Algebra.adjoin k ({αD⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartD) αD
  have hw := mem_adj αD wL_mem_D
  have hα := mem_adj αD αD_mem_D
  have hβ := mem_adj αD βD_mem_D
  have hρ := mem_adj αD ρL_mem_D
  rintro _ ⟨n, rfl⟩
  rw [show ξ n = ΦE n wL αD βD ρL * αD⁻¹ by rw [← ξ_D]; field_simp [αD_ne_zero]]
  exact M.mul_mem (ΦE_mem M.toSubring n hw hα hβ hρ) hi

theorem inv_PA : wL⁻¹ ∈ chartP ⊔ chartA := by
  rw [wL, inv_inv]
  exact le_sup_right (a := chartP) uL_mem_A

theorem gen_PA : chartA ≤ chartP ⊔ Algebra.adjoin k ({wL⁻¹} : Set L) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  apply Algebra.adjoin_le
  set M := chartP ⊔ Algebra.adjoin k ({wL⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartP) wL
  have haP := mem_adj wL aP_mem_P
  have hbP := mem_adj wL bP_mem_P
  have hsP := mem_adj wL sP_mem_P
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · rw [show aL = aP * (wL⁻¹) ^ 4 by simp only [aP, wL]; field_simp]; subalg_mem
  · rw [show bL = bP * (wL⁻¹) ^ 6 by simp only [bP, wL]; field_simp]; subalg_mem
  · rw [show σL = sP * (wL⁻¹) ^ 2 by simp only [sP, wL]; field_simp]; subalg_mem

theorem loc_PA : letI := inclusionAlgebra (show chartP ≤ chartP ⊔ chartA from le_sup_left)
    ∃ e : chartP, IsLocalization.Away e ↥(chartP ⊔ chartA) :=
  loc_of _ _ wL wL_mem_P wL_ne_zero inv_PA gen_PA

theorem loc_PB : letI := inclusionAlgebra (show chartP ≤ chartP ⊔ chartB from le_sup_left)
    ∃ e : chartP, IsLocalization.Away e ↥(chartP ⊔ chartB) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  refine loc_of _ _ (wL * aP) (chartP.mul_mem wL_mem_P aP_mem_P) (mul_ne_zero wL_ne_zero aP_ne_zero)
    ?_ (Algebra.adjoin_le ?_)
  · rw [show (wL * aP)⁻¹ = uL ^ 5 * αL by simp only [aP, αL, wL]; field_simp]
    exact le_sup_right (a := chartP) (chartB.mul_mem (chartB.pow_mem uL_mem_B 5) αL_mem_B)
  set M := chartP ⊔ Algebra.adjoin k ({(wL * aP)⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartP) (wL * aP)
  have hw := mem_adj (wL * aP) wL_mem_P
  have haP := mem_adj (wL * aP) aP_mem_P
  have hbP := mem_adj (wL * aP) bP_mem_P
  have hρa := mem_adj (wL * aP) ρaP_mem_P
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [show uL = aP * (wL * aP)⁻¹ by simp only [aP, wL]; field_simp]; subalg_mem
  · rw [show αL = wL ^ 5 * (wL * aP)⁻¹ by simp only [αL, aP, wL]; field_simp]; subalg_mem
  · rw [show βL = bP * wL ^ 4 * ((wL * aP)⁻¹) ^ 2 by simp only [βL, bP, aP, wL]; field_simp]
    subalg_mem
  · rw [show ρL = ρL * aP * wL * (wL * aP)⁻¹ by
      have := aP_ne_zero; have := wL_ne_zero; field_simp]
    subalg_mem

theorem inv_PD : aP⁻¹ ∈ chartP ⊔ chartD := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  rw [show aP⁻¹ = αD by simp only [αD, aP, wL]; field_simp]
  exact le_sup_right (a := chartP) αD_mem_D

theorem gen_PD : chartD ≤ chartP ⊔ Algebra.adjoin k ({aP⁻¹} : Set L) := by
  have ha0 := aL_ne_zero
  have hu0 := uL_ne_zero
  apply Algebra.adjoin_le
  set M := chartP ⊔ Algebra.adjoin k ({aP⁻¹} : Set L)
  have hi := inv_mem_adj (A := chartP) aP
  have hw := mem_adj aP wL_mem_P
  have hbP := mem_adj aP bP_mem_P
  have hρa := mem_adj aP ρaP_mem_P
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hw
  · rw [show αD = aP⁻¹ by simp only [αD, aP, wL]; field_simp]; exact hi
  · rw [show βD = bP * (aP⁻¹) ^ 2 by simp only [βD, bP, aP, wL]; field_simp]; subalg_mem
  · rw [show ρL = ρL * aP * aP⁻¹ by have := aP_ne_zero; field_simp]; subalg_mem

theorem loc_PD : letI := inclusionAlgebra (show chartP ≤ chartP ⊔ chartD from le_sup_left)
    ∃ e : chartP, IsLocalization.Away e ↥(chartP ⊔ chartD) :=
  loc_of _ _ aP aP_mem_P aP_ne_zero inv_PD gen_PD

/-! ## The atlas -/

/-- The four chart rings: `A`, `B`, `D` and `P`. -/
def chartRing : Fin 4 → Subalgebra k L := ![chartA, chartB, chartD, chartP]

/-- The principal atlas of the surface. -/
def atlas : PrincipalAtlas k L where
  Index := Fin 4
  ring := chartRing
  localization i j := by
    fin_cases i <;> fin_cases j
    · exact loc_self chartA
    · exact loc_AB
    · exact loc_AD
    · exact loc_AP
    · exact loc_BA
    · exact loc_self chartB
    · exact loc_BD
    · exact loc_BP
    · exact loc_DA
    · exact loc_DB
    · exact loc_self chartD
    · exact loc_DP
    · exact loc_PA
    · exact loc_PB
    · exact loc_PD
    · exact loc_self chartP

/-- The regular projective surface `X` of Proposition `prop:p11`. -/
abbrev X11 : Scheme := atlas.glued

/-- Its structure morphism to `Spec k`. -/
abbrev xToBase : X11 ⟶ Spec (CommRingCat.of k) := atlas.toBase

instance : Nonempty atlas.Index := ⟨(0 : Fin 4)⟩
instance : Finite atlas.Index := inferInstanceAs (Finite (Fin 4))

theorem x_integral : IsIntegral X11 := inferInstance

theorem chartRing_finiteType (i : Fin 4) : Algebra.FiniteType k (chartRing i) := by
  fin_cases i
  · exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)
  · exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)
  · exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)
  · exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

end
end Geonormal.P11

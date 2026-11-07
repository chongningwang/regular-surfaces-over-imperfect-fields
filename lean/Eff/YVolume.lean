import Eff.YStalks
import Eff.YJacobians
import Eff.YTuples

/-! # The canonical lattice of the second quotient, relative to one rational form -/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent Red61.LocalCoordinates
  AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 4096

private local instance (A : Type*) [CommRing A] [Algebra ℤ A] :
    Module A (KaehlerDifferential ℤ A) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ A (R' := A)

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing
private local instance : CharP Y.functionField 5 :=
  yFieldAmbientMap.charP yFieldAmbientMap_injective 5

private local instance (y : Y) : Module (Y.presheaf.stalk y) (AbsoluteStalkDifferentials Y y) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (Y.presheaf.stalk y) (R' := Y.presheaf.stalk y)

namespace YStalkCoordinateData

variable {y : Y} {v : Fin 4 → K} (d : YStalkCoordinateData y v)

def fieldCoordinates (k : Fin 4) : Y.functionField :=
  algebraMap (Y.presheaf.stalk y) Y.functionField (d.coordinates k)

def fieldBasis : Basis (Fin 4) Y.functionField (KaehlerDifferential ℤ Y.functionField) :=
  fractionAbsoluteDifferentialBasis (Y.presheaf.stalk y) Y.functionField d.basis

theorem fieldBasis_apply (k : Fin 4) :
    d.fieldBasis k = KaehlerDifferential.D ℤ Y.functionField (d.fieldCoordinates k) :=
  fractionAbsoluteDifferentialBasis_apply (Y.presheaf.stalk y) Y.functionField
    d.basis d.coordinates d.differential k

@[simp] theorem fieldCoordinates_embedding (k : Fin 4) :
    yFieldAmbientMap (d.fieldCoordinates k) = v k :=
  (yStalkAmbientMap_algebraMap y _).trans (d.embedding k)

/-- The wedge of the coordinate differentials generates the lattice at the given stalk. -/
theorem generates : GeneratesStalkDifferentialLattice (n := 4) y
    (exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (d.fieldCoordinates k))) := by
  refine ⟨d.basis, ?_⟩
  change _ = exteriorPower.map 4 (stalkRationalDifferentialEquiv y).toLinearMap
    (exteriorPower.ιMulti Y.functionField 4 (d.basis.baseChange Y.functionField))
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext k
  change _ = stalkRationalDifferentialEquiv y ((d.basis.baseChange Y.functionField) k)
  rw [Basis.baseChange_apply, d.differential, stalkRationalDifferentialEquiv_tmul_D, one_smul]
  rfl

end YStalkCoordinateData

/-! ### The K-level values of the chart functions -/

theorem q₁_ne : q₁ ≠ 0 := by
  have := ConeRing.invariantCoordinates_independent.ne_zero 0
  intro h
  apply this
  apply L.subtype_injective
  simpa [ConeRing.invariantCoordinates_coe] using h

theorem q₂_ne : q₂ ≠ 0 := by
  have := ConeRing.invariantCoordinates_independent.ne_zero 1
  intro h
  apply this
  apply L.subtype_injective
  simpa [ConeRing.invariantCoordinates_coe] using h

theorem u_ne : u ≠ 0 := by
  have := ConeRing.invariantCoordinates_independent.ne_zero 2
  intro h
  apply this
  apply L.subtype_injective
  simpa [ConeRing.invariantCoordinates_coe] using h

theorem r_ne : r ≠ 0 := by
  have := ConeRing.invariantCoordinates_independent.ne_zero 3
  intro h
  apply this
  apply L.subtype_injective
  simpa [ConeRing.invariantCoordinates_coe] using h

theorem W_eqK : W = YTuples.W u := by
  simp only [YTuples.W, u, U, W]
  simp

theorem A_eqK : A = YTuples.A q₁ u := by
  have h := q₁_eq0
  have hw : Eff.W ≠ 0 := coord_nonzero 3
  rw [YTuples.A, u_eq0, div_inv_eq_mul, h]
  field_simp

theorem B_eqK : B = YTuples.B q₁ q₂ u := by
  have hw : Eff.W ≠ 0 := coord_nonzero 3
  have hq := q₂_eq0
  rw [A_eqK, YTuples.A, u_eq0] at hq
  rw [YTuples.B, u_eq0]
  rw [hq]
  field_simp
  ring

theorem s₁_eqK : c₁ ^ 5 = YTuples.s₁ q₁ u r := by
  rw [YTuples.s₁, q₁_fifth]
  ring

theorem s₂_eqK : c₂ ^ 5 = YTuples.s₂ q₂ u r := by
  rw [YTuples.s₂, q₂_fifth]
  ring

theorem τ_eqK : y₂ 5 = YTuples.τ r := by
  rw [YTuples.τ, r_eq2, inv_inv]

theorem lastZ_eqK : lastZ = YTuples.Z q₂ := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  rw [YTuples.Z, q₂_eq2]
  linear_combination -lastZ * h5

theorem lastQ_eqK : lastQ = YTuples.Q q₁ q₂ r := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hr := r_ne
  have h := q₁_eq2
  rw [lastZ_eqK, τ_eqK, YTuples.Z, YTuples.τ] at h
  rw [YTuples.Q, h]
  field_simp
  linear_combination ((5 : K) * q₂ ^ 3) * h5

theorem middleY_eqK : middleY = YTuples.Y q₂ := by
  have hY : middleY ≠ 0 := div_ne_zero (monomial_nonzero _) h₀_ne
  have h2 : (2 : K) ≠ 0 := by
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    intro h
    exact one_ne_zero (show (1 : K) = 0 by linear_combination h5 - 2 * h)
  rw [YTuples.Y, q₂_eq1]
  field_simp

theorem middleQ_eqK : middleQ = YTuples.Q q₁ q₂ r := by
  have h := q₁_eq1
  rw [τ_eqK, YTuples.τ] at h
  rw [YTuples.Q, h]
  field_simp
  ring

theorem middleH_eqK : middleH = YTuples.H q₂ r := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h := τ_eq1
  have hq := q₂_ne
  have hr := r_ne
  rw [τ_eqK, middleY_eqK, YTuples.τ, YTuples.Y] at h
  rw [YTuples.H]
  have he : middleH = r⁻¹ * q₂ ^ 2 / 4 := by
    have h4 : (4 : K) ≠ 0 := YTuples.four_ne
    rw [h]
    field_simp
    ring
  rw [he]
  have h4 : (4 : K) ≠ 0 := YTuples.four_ne
  field_simp
  linear_combination (-3 : K) * h5

/-! ### The reference data -/

theorem YOpen.d_not_mem_bot {i : Fin 4} (U : YOpen i) (hp : (⊥ : Ideal (yAtlas.ring i)).IsPrime) :
    U.d ∉ (⟨⊥, hp⟩ : PrimeSpectrum (yAtlas.ring i)).asIdeal := by
  intro h
  have h0 : U.d = 0 := (Submodule.mem_bot _).mp h
  exact U.d_ne (by rw [h0]; rfl)

theorem yRef_exists : ∃ (y : Y) (_ : YStalkCoordinateData y (fun k ↦ ((yOpen .q).coordinates k : K))),
    True := by
  have hp : (⊥ : Ideal (yAtlas.ring (chartOf .q))).IsPrime := Ideal.isPrime_bot
  obtain ⟨d⟩ := (yOpen .q).stalkCoordinateData _ ((yOpen .q).d_not_mem_bot hp)
    (yAtlas.chartInclusion (chartOf .q) ⟨⊥, hp⟩) rfl
  exact ⟨_, d, trivial⟩

def yRefPoint : Y := Classical.choose yRef_exists

def refData : YStalkCoordinateData yRefPoint (fun k ↦ ((yOpen .q).coordinates k : K)) :=
  Classical.choose (Classical.choose_spec yRef_exists)

/-- The reference rational coordinates. -/
def ρ : Fin 4 → Y.functionField := refData.fieldCoordinates

def refBasis : Basis (Fin 4) Y.functionField (KaehlerDifferential ℤ Y.functionField) :=
  refData.fieldBasis

theorem refBasis_apply (k : Fin 4) :
    refBasis k = KaehlerDifferential.D ℤ Y.functionField (ρ k) := refData.fieldBasis_apply k

/-- The reference rational form `θ`. -/
def θ : RationalSchemeForms Y 4 := exteriorPower.ιMulti Y.functionField 4 refBasis

theorem toOpen_coord_zero {i : Fin 4} (B : YBase i) (j σ e hσ he hw hb hf) :
    (((B.toOpen j σ e hσ he hw hb hf).coordinates 0 : L) : K) = ((B.x j : L) : K) ^ 5 := by
  have h : ((B.toOpen j σ e hσ he hw hb hf).coordinates 0 : L) = B.tuple j σ e 0 ^ 5 := rfl
  rw [h, B.tuple_zero j σ e hσ he]
  rfl

theorem toOpen_coord_succ {i : Fin 4} (B : YBase i) (j σ e hσ he hw hb hf) (k : Fin 4)
    (hk : k ≠ 0) :
    (((B.toOpen j σ e hσ he hw hb hf).coordinates k : L) : K) =
      ((B.x (σ k) : L) : K) / ((B.x j : L) : K) ^ e (σ k) := by
  have h : ((B.toOpen j σ e hσ he hw hb hf).coordinates k : L) = B.tuple j σ e k := by
    fin_cases k
    · exact (hk rfl).elim
    all_goals rfl
  rw [h, YBase.tuple]
  simp

open YTuples (z a c d W₀ N₀ s₁ s₂ Q H Z τ)

theorem xval0 (k : Fin 4) : ((base0.x k : L) : K) =
    ![s₁ q₁ u r, YTuples.B q₁ q₂ u, YTuples.A q₁ u, YTuples.W u] k := by
  have h : (x0 k : K) = ![c₁ ^ 5, B, A, W] k := congrFun x0_coe k
  change (x0 k : K) = _
  rw [h]
  fin_cases k
  · exact s₁_eqK
  · exact B_eqK
  · exact A_eqK
  · exact W_eqK

theorem xval1 (k : Fin 4) : ((base1.x k : L) : K) =
    ![s₂ q₂ u r, Q q₁ q₂ r, H q₂ r, YTuples.Y q₂] k := by
  change (x1 k : K) = _
  rw [x1_coe k]
  fin_cases k
  · exact s₂_eqK
  · exact middleQ_eqK
  · exact middleH_eqK
  · exact middleY_eqK

theorem xval2 (k : Fin 4) : ((base2.x k : L) : K) =
    ![s₂ q₂ u r, Q q₁ q₂ r, Z q₂, τ r] k := by
  have h : (x2 k : K) = ![c₂ ^ 5, lastQ, lastZ, y₂ 5] k := congrFun x2_coe k
  change (x2 k : K) = _
  rw [h]
  fin_cases k
  · exact s₂_eqK
  · exact lastQ_eqK
  · exact lastZ_eqK
  · exact τ_eqK

theorem xval3 (k : Fin 4) : ((base3.x k : L) : K) = ![q₁, q₂, u, r] k :=
  ConeRing.invariantCoordinates_coe k

theorem coord_B (k : Fin 4) : ((yOpen .B).coordinates k : K) =
    ![YTuples.B q₁ q₂ u ^ 5, s₁ q₁ u r, YTuples.A q₁ u / YTuples.B q₁ q₂ u ^ 2, YTuples.W u / YTuples.B q₁ q₂ u ^ 3] k := by
  have h0 : ((yOpen .B).coordinates 0 : K) = _ :=
    toOpen_coord_zero base0 1 (Equiv.swap 0 1) ![0, 0, 2, 3] (by decide) (by decide) (by decide) (by decide) (x0_mem 1)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .B).coordinates k : K) = _ :=
    toOpen_coord_succ base0 1 (Equiv.swap 0 1) ![0, 0, 2, 3] (by decide) (by decide) (by decide) (by decide) (x0_mem 1) k hk
  fin_cases k
  · simpa [xval0] using h0
  · simpa [xval0, show (Equiv.swap 0 1) (1 : Fin 4) = 0 by decide] using hs 1 (by decide)
  · simpa [xval0, show (Equiv.swap 0 1) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval0, show (Equiv.swap 0 1) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_A (k : Fin 4) : ((yOpen .A).coordinates k : K) =
    ![YTuples.A q₁ u ^ 5, YTuples.B q₁ q₂ u / YTuples.A q₁ u ^ 3, s₁ q₁ u r, YTuples.W u / YTuples.A q₁ u ^ 4] k := by
  have h0 : ((yOpen .A).coordinates 0 : K) = _ :=
    toOpen_coord_zero base0 2 (Equiv.swap 0 2) ![0, 3, 0, 4] (by decide) (by decide) (by decide) (by decide) (x0_mem 2)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .A).coordinates k : K) = _ :=
    toOpen_coord_succ base0 2 (Equiv.swap 0 2) ![0, 3, 0, 4] (by decide) (by decide) (by decide) (by decide) (x0_mem 2) k hk
  fin_cases k
  · simpa [xval0] using h0
  · simpa [xval0, show (Equiv.swap 0 2) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval0, show (Equiv.swap 0 2) (2 : Fin 4) = 0 by decide] using hs 2 (by decide)
  · simpa [xval0, show (Equiv.swap 0 2) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_W (k : Fin 4) : ((yOpen .W).coordinates k : K) =
    ![YTuples.W u ^ 5, YTuples.B q₁ q₂ u / YTuples.W u ^ 2, YTuples.A q₁ u / YTuples.W u ^ 4, s₁ q₁ u r] k := by
  have h0 : ((yOpen .W).coordinates 0 : K) = _ :=
    toOpen_coord_zero base0 3 (Equiv.swap 0 3) ![0, 2, 4, 0] (by decide) (by decide) (by decide) (by decide) (x0_mem 3)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .W).coordinates k : K) = _ :=
    toOpen_coord_succ base0 3 (Equiv.swap 0 3) ![0, 2, 4, 0] (by decide) (by decide) (by decide) (by decide) (x0_mem 3) k hk
  fin_cases k
  · simpa [xval0] using h0
  · simpa [xval0, show (Equiv.swap 0 3) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval0, show (Equiv.swap 0 3) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval0, show (Equiv.swap 0 3) (3 : Fin 4) = 0 by decide] using hs 3 (by decide)

theorem coord_Q (k : Fin 4) : ((yOpen .Q).coordinates k : K) =
    ![Q q₁ q₂ r ^ 5, s₂ q₂ u r, H q₂ r / Q q₁ q₂ r ^ 2, YTuples.Y q₂ / Q q₁ q₂ r] k := by
  have h0 : ((yOpen .Q).coordinates 0 : K) = _ :=
    toOpen_coord_zero base1 1 (Equiv.swap 0 1) ![0, 0, 2, 1] (by decide) (by decide) (by decide) (by decide) x1_one_mem
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .Q).coordinates k : K) = _ :=
    toOpen_coord_succ base1 1 (Equiv.swap 0 1) ![0, 0, 2, 1] (by decide) (by decide) (by decide) (by decide) x1_one_mem k hk
  fin_cases k
  · simpa [xval1] using h0
  · simpa [xval1, show (Equiv.swap 0 1) (1 : Fin 4) = 0 by decide] using hs 1 (by decide)
  · simpa [xval1, show (Equiv.swap 0 1) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval1, show (Equiv.swap 0 1) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_H (k : Fin 4) : ((yOpen .H).coordinates k : K) =
    ![H q₂ r ^ 5, Q q₁ q₂ r / H q₂ r ^ 3, s₂ q₂ u r, YTuples.Y q₂ / H q₂ r ^ 3] k := by
  have h0 : ((yOpen .H).coordinates 0 : K) = _ :=
    toOpen_coord_zero base1 2 (Equiv.swap 0 2) ![0, 3, 0, 3] (by decide) (by decide) (by decide) (by decide) x1_two_mem
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .H).coordinates k : K) = _ :=
    toOpen_coord_succ base1 2 (Equiv.swap 0 2) ![0, 3, 0, 3] (by decide) (by decide) (by decide) (by decide) x1_two_mem k hk
  fin_cases k
  · simpa [xval1] using h0
  · simpa [xval1, show (Equiv.swap 0 2) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval1, show (Equiv.swap 0 2) (2 : Fin 4) = 0 by decide] using hs 2 (by decide)
  · simpa [xval1, show (Equiv.swap 0 2) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_G (k : Fin 4) : ((yOpen .G).coordinates k : K) =
    ![Q q₁ q₂ r ^ 5, s₂ q₂ u r, Z q₂ / Q q₁ q₂ r ^ 4, τ r / Q q₁ q₂ r ^ 4] k := by
  have h0 : ((yOpen .G).coordinates 0 : K) = _ :=
    toOpen_coord_zero base2 1 (Equiv.swap 0 1) ![0, 0, 4, 4] (by decide) (by decide) (by decide) (by decide) (x2_mem 1)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .G).coordinates k : K) = _ :=
    toOpen_coord_succ base2 1 (Equiv.swap 0 1) ![0, 0, 4, 4] (by decide) (by decide) (by decide) (by decide) (x2_mem 1) k hk
  fin_cases k
  · simpa [xval2] using h0
  · simpa [xval2, show (Equiv.swap 0 1) (1 : Fin 4) = 0 by decide] using hs 1 (by decide)
  · simpa [xval2, show (Equiv.swap 0 1) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval2, show (Equiv.swap 0 1) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_τ (k : Fin 4) : ((yOpen .τ).coordinates k : K) =
    ![τ r ^ 5, Q q₁ q₂ r / τ r ^ 4, Z q₂ / τ r, s₂ q₂ u r] k := by
  have h0 : ((yOpen .τ).coordinates 0 : K) = _ :=
    toOpen_coord_zero base2 3 (Equiv.swap 0 3) ![0, 4, 1, 0] (by decide) (by decide) (by decide) (by decide) (x2_mem 3)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .τ).coordinates k : K) = _ :=
    toOpen_coord_succ base2 3 (Equiv.swap 0 3) ![0, 4, 1, 0] (by decide) (by decide) (by decide) (by decide) (x2_mem 3) k hk
  fin_cases k
  · simpa [xval2] using h0
  · simpa [xval2, show (Equiv.swap 0 3) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval2, show (Equiv.swap 0 3) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval2, show (Equiv.swap 0 3) (3 : Fin 4) = 0 by decide] using hs 3 (by decide)

theorem coord_q (k : Fin 4) : ((yOpen .q).coordinates k : K) =
    ![q₁ ^ 5, q₂ / q₁ ^ 4, u / q₁ ^ 3, r / q₁] k := by
  have h0 : ((yOpen .q).coordinates 0 : K) = _ :=
    toOpen_coord_zero base3 0 (Equiv.refl _) ![0, 4, 3, 1] (by decide) (by decide) (by decide) (by decide) (x3_mem 0)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .q).coordinates k : K) = _ :=
    toOpen_coord_succ base3 0 (Equiv.refl _) ![0, 4, 3, 1] (by decide) (by decide) (by decide) (by decide) (x3_mem 0) k hk
  fin_cases k
  · simpa [xval3] using h0
  · simpa [xval3, show (Equiv.refl (Fin 4)) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval3, show (Equiv.refl (Fin 4)) (2 : Fin 4) = 2 by decide] using hs 2 (by decide)
  · simpa [xval3, show (Equiv.refl (Fin 4)) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

theorem coord_u (k : Fin 4) : ((yOpen .u).coordinates k : K) =
    ![u ^ 5, q₂ / u ^ 3, q₁ / u ^ 2, r / u ^ 2] k := by
  have h0 : ((yOpen .u).coordinates 0 : K) = _ :=
    toOpen_coord_zero base3 2 (Equiv.swap 0 2) ![2, 3, 0, 2] (by decide) (by decide) (by decide) (by decide) (x3_mem 2)
  have hs (k : Fin 4) (hk : k ≠ 0) : ((yOpen .u).coordinates k : K) = _ :=
    toOpen_coord_succ base3 2 (Equiv.swap 0 2) ![2, 3, 0, 2] (by decide) (by decide) (by decide) (by decide) (x3_mem 2) k hk
  fin_cases k
  · simpa [xval3] using h0
  · simpa [xval3, show (Equiv.swap 0 2) (1 : Fin 4) = 1 by decide] using hs 1 (by decide)
  · simpa [xval3, show (Equiv.swap 0 2) (2 : Fin 4) = 0 by decide] using hs 2 (by decide)
  · simpa [xval3, show (Equiv.swap 0 2) (3 : Fin 4) = 3 by decide] using hs 3 (by decide)

/-! ### The reference coordinates in `K` -/

local notation "κ" => yFieldAmbientMap

theorem ρ_embed (k : Fin 4) : κ (ρ k) = ![z q₁, a q₁ q₂, c q₁ u, d q₁ r] k := by
  have h : κ (ρ k) = ((yOpen .q).coordinates k : K) := refData.fieldCoordinates_embedding k
  rw [h, coord_q k]
  fin_cases k <;> rfl

theorem ρ0 : κ (ρ 0) = z q₁ := ρ_embed 0
theorem ρ1 : κ (ρ 1) = a q₁ q₂ := ρ_embed 1
theorem ρ2 : κ (ρ 2) = c q₁ u := ρ_embed 2
theorem ρ3 : κ (ρ 3) = d q₁ r := ρ_embed 3

theorem ρ_ne (k : Fin 4) : ρ k ≠ 0 := by
  intro h
  have h0 := ρ_embed k
  rw [h, map_zero] at h0
  fin_cases k
  · exact YTuples.z_ne q₁ q₁_ne h0.symm
  · exact YTuples.a_ne q₁ q₂ q₁_ne q₂_ne h0.symm
  · exact YTuples.c_ne q₁ u q₁_ne u_ne h0.symm
  · exact YTuples.d_ne q₁ r q₁_ne r_ne h0.symm

def W_E : Y.functionField := ρ 1 * ρ 0 * ρ 2 + 3
def N_E : Y.functionField := ρ 3 + 2 * ρ 1 ^ 3 * ρ 0 ^ 2

theorem κW : κ W_E = W₀ q₁ q₂ u := by
  simp only [W_E, map_add, map_mul, map_ofNat, ρ0, ρ1, ρ2, W₀]

theorem κN : κ N_E = N₀ q₁ q₂ r := by
  simp only [N_E, map_add, map_mul, map_pow, map_ofNat, ρ0, ρ1, ρ3, N₀]

theorem W₀_ne : W₀ q₁ q₂ u ≠ 0 := by
  intro h
  have hB : ((base0.x 1 : L) : K) = YTuples.B q₁ q₂ u := xval0 1
  have hne : ((base0.x 1 : L) : K) ≠ 0 := fun h0 ↦ base0.x_ne 1 (Subtype.ext h0)
  rw [hB, YTuples.B_eq q₁ q₂ u q₁_ne u_ne, h] at hne
  simp at hne

theorem N₀_ne : N₀ q₁ q₂ r ≠ 0 := by
  intro h
  have hB : ((base1.x 1 : L) : K) = Q q₁ q₂ r := xval1 1
  have hne : ((base1.x 1 : L) : K) ≠ 0 := fun h0 ↦ base1.x_ne 1 (Subtype.ext h0)
  rw [hB, YTuples.Q_eq q₁ q₂ r q₁_ne r_ne, h] at hne
  simp at hne

theorem W_E_ne : W_E ≠ 0 := fun h ↦ W₀_ne (by rw [← κW, h, map_zero])
theorem N_E_ne : N_E ≠ 0 := fun h ↦ N₀_ne (by rw [← κN, h, map_zero])

/-- The Jacobian factor of each principal open relative to the reference form. -/
def ν : YIdx → Y.functionField
  | .B => 4 * ρ 0 * ρ 2 / W_E
  | .A => ρ 2 ^ 3 * ρ 0 ^ 2
  | .W => 4 * ρ 2 ^ 2 * ρ 0 ^ 2
  | .Q => 4 * N_E * ρ 0 / ρ 3
  | .H => 4 * ρ 3 ^ 2 / (ρ 1 ^ 4 * ρ 0 ^ 2)
  | .G => 4 * ρ 3 ^ 4 / N_E ^ 4
  | .τ => 4 * ρ 3 * ρ 0
  | .q => 1
  | .u => 4 / (ρ 2 ^ 3 * ρ 0)

theorem volume_B {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .B).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .B • θ := by
  have he : D.fieldCoordinates = ![W_E ^ 5 / (ρ 2 ^ 5 * ρ 0),
      ρ 0 + ρ 2 ^ 3 * ρ 3 * ρ 0 ^ 2, -ρ 2 / W_E ^ 2,
      ρ 2 ^ 2 / W_E ^ 3] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_B k]
    fin_cases k
    · have := YTuples.B0 q₁ q₂ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s1_eq q₁ u r q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.B2 q₁ q₂ u q₁_ne u_ne W₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.B3 q₁ q₂ u q₁_ne u_ne W₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .B := by
    rw [he]
    exact jac_B refBasis ρ refBasis_apply ρ_ne W_E rfl W_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_A {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .A).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .A • θ := by
  have he : D.fieldCoordinates = ![-1 / (ρ 2 ^ 5 * ρ 0 ^ 2),
      -W_E * ρ 2 ^ 2 * ρ 0, ρ 0 + ρ 2 ^ 3 * ρ 3 * ρ 0 ^ 2,
      ρ 2 ^ 3 * ρ 0] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_A k]
    fin_cases k
    · have := YTuples.A0 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.A1 q₁ q₂ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s1_eq q₁ u r q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.A3 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .A := by
    rw [he]
    exact jac_A refBasis ρ refBasis_apply ρ_ne W_E rfl W_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_W {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .W).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .W • θ := by
  have he : D.fieldCoordinates = ![1 / (ρ 2 ^ 5 * ρ 0 ^ 3),
      W_E * ρ 2 * ρ 0, -ρ 2 ^ 3 * ρ 0 ^ 2,
      ρ 0 + ρ 2 ^ 3 * ρ 3 * ρ 0 ^ 2] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_W k]
    fin_cases k
    · have := YTuples.W0 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.W1 q₁ q₂ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.W2 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s1_eq q₁ u r q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .W := by
    rw [he]
    exact jac_W refBasis ρ refBasis_apply ρ_ne W_E rfl W_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_Q {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .Q).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .Q • θ := by
  have he : D.fieldCoordinates = ![ρ 0 * N_E ^ 5 / ρ 3 ^ 5,
      ρ 1 ^ 5 * ρ 0 ^ 4 + 3 * ρ 2 * ρ 3 ^ 2 * ρ 0, 4 * ρ 1 ^ 2 * ρ 0 * ρ 3 / N_E ^ 2,
      2 * ρ 3 / (ρ 1 * ρ 0 * N_E)] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_Q k]
    fin_cases k
    · have := YTuples.Q0 q₁ q₂ r q₁_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s2_eq q₁ q₂ u r q₁_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.Q2 q₁ q₂ r q₁_ne q₂_ne r_ne N₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.Q3 q₁ q₂ r q₁_ne q₂_ne r_ne N₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .Q := by
    rw [he]
    exact jac_Q refBasis ρ refBasis_apply ρ_ne N_E rfl N_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_H {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .H).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .H • θ := by
  have he : D.fieldCoordinates = ![4 * ρ 1 ^ 10 * ρ 0 ^ 7 / ρ 3 ^ 5,
      4 * N_E * ρ 3 ^ 2 / (ρ 1 ^ 6 * ρ 0 ^ 4), ρ 1 ^ 5 * ρ 0 ^ 4 + 3 * ρ 2 * ρ 3 ^ 2 * ρ 0,
      3 * ρ 3 ^ 3 / (ρ 1 ^ 7 * ρ 0 ^ 5)] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_H k]
    fin_cases k
    · have := YTuples.H0 q₁ q₂ r q₁_ne q₂_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.H1 q₁ q₂ r q₁_ne q₂_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s2_eq q₁ q₂ u r q₁_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.H3 q₁ q₂ r q₁_ne q₂_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .H := by
    rw [he]
    exact jac_H refBasis ρ refBasis_apply ρ_ne N_E rfl N_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_G {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .G).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .G • θ := by
  have he : D.fieldCoordinates = ![ρ 0 * N_E ^ 5 / ρ 3 ^ 5,
      ρ 1 ^ 5 * ρ 0 ^ 4 + 3 * ρ 2 * ρ 3 ^ 2 * ρ 0, -2 * ρ 1 * ρ 3 ^ 4 / N_E ^ 4,
      ρ 3 ^ 3 / (ρ 0 * N_E ^ 4)] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_G k]
    fin_cases k
    · have := YTuples.Q0 q₁ q₂ r q₁_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s2_eq q₁ q₂ u r q₁_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.G2 q₁ q₂ r q₁_ne q₂_ne r_ne N₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.G3 q₁ q₂ r q₁_ne r_ne N₀_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .G := by
    rw [he]
    exact jac_G refBasis ρ refBasis_apply ρ_ne N_E rfl N_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_τ {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .τ).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .τ • θ := by
  have he : D.fieldCoordinates = ![1 / (ρ 3 ^ 5 * ρ 0),
      N_E * ρ 3 ^ 3 * ρ 0, -2 * ρ 1 * ρ 3 * ρ 0,
      ρ 1 ^ 5 * ρ 0 ^ 4 + 3 * ρ 2 * ρ 3 ^ 2 * ρ 0] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_τ k]
    fin_cases k
    · have := YTuples.τ0 q₁ r q₁_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.τ1 q₁ q₂ r q₁_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.τ2 q₁ q₂ r q₁_ne r_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.s2_eq q₁ q₂ u r q₁_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .τ := by
    rw [he]
    exact jac_τ refBasis ρ refBasis_apply ρ_ne N_E rfl N_E_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_u {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .u).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .u • θ := by
  have he : D.fieldCoordinates = ![ρ 2 ^ 5 * ρ 0 ^ 3,
      ρ 1 / (ρ 2 ^ 3 * ρ 0), 1 / (ρ 2 ^ 2 * ρ 0),
      ρ 3 / (ρ 2 ^ 2 * ρ 0)] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_u k]
    fin_cases k
    · have := YTuples.u0 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.u1 q₁ q₂ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.u2 q₁ u q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
    · have := YTuples.u3 q₁ u r q₁_ne u_ne
      simpa only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_add, map_mul, map_div₀, map_pow, map_neg, map_one,
        map_ofNat, κW, κN, ρ0, ρ1, ρ2, ρ3] using this
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .u := by
    rw [he]
    exact jac_u refBasis ρ refBasis_apply ρ_ne
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

theorem volume_q {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen .q).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν .q • θ := by
  have he : D.fieldCoordinates = ![ρ 0, ρ 1, ρ 2, ρ 3] := by
    funext k
    apply yFieldAmbientMap_injective
    rw [D.fieldCoordinates_embedding, coord_q k]
    fin_cases k
    · exact ρ0.symm
    · exact ρ1.symm
    · exact ρ2.symm
    · exact ρ3.symm
  have hdet : (coordinateDifferentialMatrix refBasis D.fieldCoordinates).det = ν .q := by
    rw [he]
    exact jac_q refBasis ρ refBasis_apply
  exact (wedge_eq_det_smul refBasis D.fieldCoordinates).trans (congrArg (fun c ↦ c • θ) hdet)

/-- Each principal open generates the lattice by a fixed multiple of the reference form. -/
theorem volume (a : YIdx) {y : Y} (D : YStalkCoordinateData y (fun k ↦ ((yOpen a).coordinates k : K))) :
    exteriorPower.ιMulti Y.functionField 4
      (fun k ↦ KaehlerDifferential.D ℤ Y.functionField (D.fieldCoordinates k)) = ν a • θ := by
  cases a
  · exact volume_B D
  · exact volume_A D
  · exact volume_W D
  · exact volume_Q D
  · exact volume_H D
  · exact volume_G D
  · exact volume_τ D
  · exact volume_q D
  · exact volume_u D

/-- The lattice of the canonical line at each point, relative to the reference form. -/
theorem y_lattice (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a)))
    (hd : (yOpen a).d ∉ q.asIdeal) :
    GeneratesStalkDifferentialLattice (n := 4) (yAtlas.chartInclusion (chartOf a) q) (ν a • θ) := by
  obtain ⟨D⟩ := (yOpen a).stalkCoordinateData q hd _ rfl
  rw [← volume a D]
  exact D.generates

end
end Eff

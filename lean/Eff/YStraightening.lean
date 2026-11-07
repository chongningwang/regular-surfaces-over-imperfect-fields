import Eff.FreenessCertificates
import Red61.Theorem61

/-! # Straightening the Euler derivation on principal opens

A homogeneous function `f` of nonzero weight turns the Euler derivation into a derivation `D`
with `D f = 1`. Red61's polynomial-kernel theorems then apply to it verbatim: on an open with
polynomial coordinates `(f, y₁, y₂, y₃)`, `yᵢ` invariant, the invariant ring is a localization
of the polynomial ring on `(f⁵, y₁, y₂, y₃)`.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The Euler derivation of `L`, over the prime field. -/
def eulerF₅ : Derivation F₅ L L where
  toFun := invariantEuler
  map_add' := map_add invariantEuler
  map_smul' a x := by
    have h : algebraMap F₅ L a = (a.val : L) := by
      conv_lhs => rw [show a = ((a.val : ℕ) : F₅) from (ZMod.natCast_zmod_val a).symm, map_natCast]
    have hc : invariantEuler (a.val : L) = 0 := invariantEuler.map_natCast _
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, h, Derivation.leibniz, hc]
    simp [smul_eq_mul]
  map_one_eq_zero' := invariantEuler.map_one_eq_zero
  leibniz' := invariantEuler.leibniz

@[simp] theorem eulerF₅_apply (x : L) : eulerF₅ x = invariantEuler x := rfl

/-- `(n f)⁻¹ • E`, which sends `f` to one when `E f = n f`. -/
def straightEuler (f : L) (n : ℤ) : Derivation F₅ L L := ((n : L) * f)⁻¹ • eulerF₅

theorem straightEuler_apply (f : L) (n : ℤ) (x : L) :
    straightEuler f n x = ((n : L) * f)⁻¹ * invariantEuler x := rfl

theorem intCast_ne_zero_of_weight {n : ℤ} (hn : (n : ZMod 5) ≠ 0) : (n : L) ≠ 0 := by
  intro h
  apply hn
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mpr ((CharP.intCast_eq_zero_iff L 5 n).mp h)

theorem straightEuler_eq_zero_iff (f : L) (hf : f ≠ 0) (n : ℤ) (hn : (n : ZMod 5) ≠ 0) (x : L) :
    straightEuler f n x = 0 ↔ x ∈ M := by
  rw [straightEuler_apply, mul_eq_zero, inv_eq_zero, mul_eq_zero]
  simp only [intCast_ne_zero_of_weight hn, hf, or_self, false_or]
  rfl

theorem straightEuler_values (v : Fin 4 → L) (n : ℤ) (hn : (n : ZMod 5) ≠ 0) (h0 : v 0 ≠ 0)
    (hE : invariantEuler (v 0) = n * v 0) (hv : ∀ j, j ≠ 0 → invariantEuler (v j) = 0) (i : Fin 4) :
    straightEuler (v 0) n (v i) = if i = 0 then 1 else 0 := by
  rw [straightEuler_apply]
  split_ifs with hi
  · subst hi
    rw [hE, inv_mul_cancel₀ (mul_ne_zero (intCast_ne_zero_of_weight hn) h0)]
  · rw [hv i hi, mul_zero]

/-- Fifth powers of arbitrary elements of `K` already lie in the invariant field of `L`. -/
def powL (x : K) : L := ⟨x ^ 5, field_fifth_power_invariant x⟩

@[simp] theorem powL_coe (x : K) : (powL x : K) = x ^ 5 := rfl

theorem powL_mem_M (x : K) : powL x ∈ M := by
  change invariantEuler _ = 0
  apply Subtype.ext
  change euler (x ^ 5) = 0
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero K 5, zero_mul]

/-- Fifth powers of arbitrary elements of `K`, in the second invariant field. -/
def powM (x : K) : M := ⟨powL x, powL_mem_M x⟩

@[simp] theorem powM_coe (x : K) : (((powM x : M) : L) : K) = x ^ 5 := rfl

/-- Frobenius of a contracted chart ring lands in the corresponding chart ring of `Y`. -/
def yFrob (i : Fin 4) : contractedAtlas.ring i →+* yAtlas.ring i where
  toFun x := ⟨powM (x : K), (contractedAtlas.ring i).pow_mem x.property 5⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    simp
  map_zero' := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    simp [add_pow_char]
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    simp [mul_pow]

@[simp] theorem yFrob_coe (i : Fin 4) (x : contractedAtlas.ring i) :
    (((yFrob i x : yAtlas.ring i) : M) : L).1 = (x : K) ^ 5 := rfl

/-- Subrings of `L` carrying localized coordinate data for a principal open of `Y`. -/
structure YOpen (i : Fin 4) where
  A : Subalgebra F₅ L
  d : yAtlas.ring i
  weight : ℤ
  v : Fin 4 → L
  d_ne : (((d : yAtlas.ring i) : M) : L) ≠ 0
  d_inv : (((d : yAtlas.ring i) : M) : L)⁻¹ ∈ A
  chart_le : ∀ a : quotientAtlas.ring i, (a : L) ∈ A
  clear : ∀ c ∈ A, ∃ n : ℕ, c * (((d : yAtlas.ring i) : M) : L) ^ n ∈ quotientAtlas.ring i
  weight_ne : (weight : ZMod 5) ≠ 0
  v_ne : v 0 ≠ 0
  v_inv : (v 0)⁻¹ ∈ A
  euler_v0 : invariantEuler (v 0) = weight * v 0
  euler_v : ∀ j, j ≠ 0 → invariantEuler (v j) = 0
  independent : AlgebraicIndependent F₅ v
  poly_le : polynomialRing v ≤ A
  hull_le : A ≤ hull (polynomialRing v) A

namespace YOpen

variable {i : Fin 4} (U : YOpen i)

abbrev D : Derivation F₅ L L := straightEuler (U.v 0) U.weight

theorem values (j : Fin 4) : U.D (U.v j) = if j = 0 then 1 else 0 :=
  straightEuler_values U.v U.weight U.weight_ne U.v_ne U.euler_v0 U.euler_v j

/-- The invariant coordinate ring of the principal open. -/
abbrev kernel : Subalgebra F₅ L := kernelIn U.D U.A

theorem mem_kernel_iff (c : L) : c ∈ U.kernel ↔ c ∈ U.A ∧ c ∈ M :=
  and_congr_right fun _ ↦ straightEuler_eq_zero_iff (U.v 0) U.v_ne U.weight U.weight_ne c

instance kernel_regular' : IsRegularRing U.kernel :=
  kernel_regular U.D U.v U.independent U.values U.A U.poly_le U.hull_le

def toKernel : yAtlas.ring i →+* U.kernel where
  toFun x := ⟨((x : M) : L), (U.mem_kernel_iff _).mpr ⟨U.chart_le ⟨((x : M) : L), x.property⟩,
    (x : M).property⟩⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[instance_reducible] def algebra : Algebra (yAtlas.ring i) U.kernel := U.toKernel.toAlgebra

theorem isLocalization :
    letI := U.algebra
    IsLocalization.Away U.d U.kernel := by
  let := U.algebra
  have hd : (((U.d : yAtlas.ring i) : M) : L)⁻¹ ∈ U.kernel := by
    refine (U.mem_kernel_iff _).mpr ⟨U.d_inv, ?_⟩
    exact M.inv_mem (U.d : M).property
  apply IsLocalization.Away.mk
  · refine ⟨⟨algebraMap _ U.kernel U.d, ⟨_, hd⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ U.d_ne)
    · exact Subtype.ext (inv_mul_cancel₀ U.d_ne)
  · intro c
    obtain ⟨n, hn⟩ := U.clear c c.property.1
    have hM : (c : L) * (((U.d : yAtlas.ring i) : M) : L) ^ n ∈ M :=
      M.mul_mem ((U.mem_kernel_iff _).mp c.property).2 (M.pow_mem (U.d : M).property n)
    exact ⟨n, ⟨⟨_, hM⟩, hn⟩, rfl⟩
  · intro x y hxy
    have he : x = y := by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : U.kernel ↦ (z : L)) hxy
    exact ⟨0, by rw [he]⟩

theorem atPrime_regular (p : PrimeSpectrum (yAtlas.ring i)) (hd : U.d ∉ p.asIdeal) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  let := U.algebra
  have := U.isLocalization
  exact atPrime_regular_of_away (A := U.kernel) U.d p hd

end YOpen

end
end Eff

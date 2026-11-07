import Eff.YStraightening

/-! # Polynomial coordinates on principal opens of the second quotient

`YBase` records polynomial coordinates of nonzero-weight eigenfunctions on an open of `S`, and
`YBase.toOpen` produces the corresponding straightened coordinates after inverting one of them.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Elements of `L` whose denominators are cleared by powers of `δ ∈ C`. -/
def clearingRing (C : Subalgebra ell L) (δ : L) (hδ : δ ∈ C) : Subalgebra F₅ L where
  carrier := {c | ∃ n : ℕ, c * δ ^ n ∈ C}
  mul_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have he : x * y * δ ^ (n + m) = (x * δ ^ n) * (y * δ ^ m) := by rw [pow_add]; ring
    rw [he]
    exact C.mul_mem hn hm
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have he : (x + y) * δ ^ (n + m) = (x * δ ^ n) * δ ^ m + (y * δ ^ m) * δ ^ n := by
      rw [pow_add]; ring
    rw [he]
    exact C.add_mem (C.mul_mem hn (C.pow_mem hδ m)) (C.mul_mem hm (C.pow_mem hδ n))
  algebraMap_mem' a := by
    refine ⟨0, ?_⟩
    have h : algebraMap F₅ L a = (a.val : L) := by
      conv_lhs => rw [show a = ((a.val : ℕ) : F₅) from (ZMod.natCast_zmod_val a).symm, map_natCast]
    rw [h, pow_zero, mul_one]
    exact C.natCast_mem _

theorem hull_mono {P P' A A' : Subalgebra F₅ L} (hP : P ≤ P') (hA : A ≤ A') :
    hull P A ≤ hull P' A' := by
  rintro x ⟨b, hb, hb0, hbi, hxb⟩
  exact ⟨b, hP hb, hb0, hA hbi, hP hxb⟩

theorem independent_of_field_top (v : Fin 4 → L)
    (h : IntermediateField.adjoin F₅ (Set.range v) = ⊤) : AlgebraicIndependent F₅ v := by
  have : Algebra.IsAlgebraic (Algebra.adjoin F₅ (Set.range v)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, h]
    infer_instance
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite F₅
    v ConeRing.invariantCoordinates_independent.cardinalMk_le_trdeg).1

/-- A weight calculation for quotients. -/
theorem euler_div_pow (x f : L) (hf : f ≠ 0) (a b : ℤ)
    (hx : invariantEuler x = a * x) (hb : invariantEuler f = b * f) (e : ℕ) :
    invariantEuler (x / f ^ e) = ((a - e * b : ℤ) : L) * (x / f ^ e) := by
  have hfe : f ^ e ≠ 0 := pow_ne_zero e hf
  have hp : invariantEuler (f ^ e) = ((e * b : ℤ) : L) * f ^ e := by
    rw [Derivation.leibniz_pow, hb]
    rcases e with _ | e
    · simp
    · simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
  rw [Derivation.leibniz_div, hp, hx]
  simp only [smul_eq_mul]
  push_cast
  field_simp

theorem weight_cast_eq_zero (a e b : ℤ) (h : (a : ZMod 5) = e * b) :
    ((a - e * b : ℤ) : L) = 0 := by
  apply (CharP.intCast_eq_zero_iff L 5 _).mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
  push_cast
  rw [h, sub_self]

/-- Polynomial coordinates, all of them eigenfunctions, on an open of `S` defined over `Y`. -/
structure YBase (i : Fin 4) where
  A : Subalgebra F₅ L
  d : yAtlas.ring i
  x : Fin 4 → L
  wt : Fin 4 → ℤ
  d_ne : (((d : yAtlas.ring i) : M) : L) ≠ 0
  d_inv : (((d : yAtlas.ring i) : M) : L)⁻¹ ∈ A
  chart_le : ∀ a : quotientAtlas.ring i, (a : L) ∈ A
  clear : ∀ c ∈ A, ∃ n : ℕ, c * (((d : yAtlas.ring i) : M) : L) ^ n ∈ quotientAtlas.ring i
  euler_x : ∀ k, invariantEuler (x k) = (wt k : L) * x k
  poly_le : polynomialRing x ≤ A
  hull_le : A ≤ hull (polynomialRing x) A
  field_top : IntermediateField.adjoin F₅ (Set.range x) = ⊤

namespace YBase

variable {i : Fin 4} (B : YBase i)

theorem independent : AlgebraicIndependent F₅ B.x := independent_of_field_top _ B.field_top

theorem x_ne (k : Fin 4) : B.x k ≠ 0 := B.independent.ne_zero k

/-- The straightened tuple after inverting `x j`; the permutation only reorders the entries. -/
def tuple (j : Fin 4) (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) (k : Fin 4) : L :=
  B.x (σ k) / B.x j ^ e (σ k)

variable (j : Fin 4) (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) (hσ : σ 0 = j) (he : e j = 0)
include hσ he

theorem tuple_zero : B.tuple j σ e 0 = B.x j := by
  simp [tuple, hσ, he]

theorem x_eq_tuple (a : Fin 4) :
    B.x a = B.tuple j σ e (σ.symm a) * B.tuple j σ e 0 ^ e a := by
  rw [B.tuple_zero j σ e hσ he, tuple, σ.apply_symm_apply, div_mul_cancel₀ _
    (pow_ne_zero _ (B.x_ne j))]

theorem x_mem_tuple_ring (a : Fin 4) : B.x a ∈ polynomialRing (F := F₅) (B.tuple j σ e) := by
  rw [B.x_eq_tuple j σ e hσ he a]
  have hv (k : Fin 4) : B.tuple j σ e k ∈ polynomialRing (F := F₅) (B.tuple j σ e) :=
    Algebra.subset_adjoin (Set.mem_range_self k)
  exact Subalgebra.mul_mem _ (hv _) (Subalgebra.pow_mem _ (hv 0) _)

theorem poly_le_tuple : polynomialRing (F := F₅) B.x ≤ polynomialRing (F := F₅) (B.tuple j σ e) :=
  Algebra.adjoin_le (by rintro _ ⟨a, rfl⟩; exact B.x_mem_tuple_ring j σ e hσ he a)

theorem tuple_field_top : IntermediateField.adjoin F₅ (Set.range (B.tuple j σ e)) = ⊤ := by
  apply top_unique
  rw [← B.field_top]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  have hle : polynomialRing (F := F₅) (B.tuple j σ e) ≤
      (IntermediateField.adjoin F₅ (Set.range (B.tuple j σ e))).toSubalgebra :=
    Algebra.adjoin_le (IntermediateField.subset_adjoin _ _)
  exact hle (B.x_mem_tuple_ring j σ e hσ he a)

omit hσ he

/-- The localized ring on which the tuple is defined. -/
def openRing : Subalgebra F₅ L := B.A ⊔ Algebra.adjoin F₅ {(B.x j)⁻¹}

theorem A_le_openRing : B.A ≤ B.openRing j := le_sup_left

theorem inv_mem_openRing : (B.x j)⁻¹ ∈ B.openRing j :=
  (show Algebra.adjoin F₅ _ ≤ B.openRing j from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_singleton _))

theorem x_mem_A (a : Fin 4) : B.x a ∈ B.A :=
  B.poly_le (Algebra.subset_adjoin (Set.mem_range_self a))

theorem tuple_mem_openRing (k : Fin 4) : B.tuple j σ e k ∈ B.openRing j := by
  rw [tuple, div_eq_mul_inv, ← inv_pow]
  exact Subalgebra.mul_mem _ (B.A_le_openRing j (B.x_mem_A _))
    (Subalgebra.pow_mem _ (B.inv_mem_openRing j) _)

include hσ he

theorem openRing_le_hull :
    B.openRing j ≤ hull (polynomialRing (B.tuple j σ e)) (B.openRing j) := by
  apply sup_le
  · exact B.hull_le.trans (hull_mono (B.poly_le_tuple j σ e hσ he) (B.A_le_openRing j))
  · apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    refine ⟨B.x j, ?_, B.x_ne j, ?_, ?_⟩
    · exact B.x_mem_tuple_ring j σ e hσ he j
    · simpa using B.inv_mem_openRing j
    · rw [inv_mul_cancel₀ (B.x_ne j)]
      exact Subalgebra.one_mem _

end YBase

/-- The fifth power of a chart element of `S`, in the chart ring of `Y`. -/
def fifthY (i : Fin 4) (a : quotientAtlas.ring i) : yAtlas.ring i :=
  powerElement M 5 fifth_power_in_M ((quotientAtlas.ring i).restrictScalars ell) a

@[simp] theorem fifthY_coe (i : Fin 4) (a : quotientAtlas.ring i) :
    (((fifthY i a : yAtlas.ring i) : M) : L) = (a : L) ^ 5 := rfl

namespace YBase

variable {i : Fin 4} (B : YBase i)

/-- The denominator of the principal open where `x j` is inverted. -/
def openDenominator (j : Fin 4) (hf : B.x j ∈ quotientAtlas.ring i) : yAtlas.ring i :=
  B.d * fifthY i ⟨B.x j, hf⟩

theorem openDenominator_coe (j : Fin 4) (hf : B.x j ∈ quotientAtlas.ring i) :
    (((B.openDenominator j hf : yAtlas.ring i) : M) : L) =
      (((B.d : yAtlas.ring i) : M) : L) * B.x j ^ 5 := rfl

/-- Inverting one coordinate of nonzero weight. -/
def toOpen (j : Fin 4) (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) (hσ : σ 0 = j) (he : e j = 0)
    (hw : (B.wt j : ZMod 5) ≠ 0)
    (hb : ∀ k, k ≠ j → (B.wt k : ZMod 5) = (e k : ZMod 5) * B.wt j)
    (hf : B.x j ∈ quotientAtlas.ring i) : YOpen i where
  A := B.openRing j
  d := B.openDenominator j hf
  weight := B.wt j
  v := B.tuple j σ e
  d_ne := by
    rw [openDenominator_coe]
    exact mul_ne_zero B.d_ne (pow_ne_zero _ (B.x_ne j))
  d_inv := by
    rw [openDenominator_coe, mul_inv, ← inv_pow]
    exact Subalgebra.mul_mem _ (B.A_le_openRing j B.d_inv)
      (Subalgebra.pow_mem _ (B.inv_mem_openRing j) _)
  chart_le a := B.A_le_openRing j (B.chart_le a)
  clear := by
    let T := clearingRing (quotientAtlas.ring i) _ (B.openDenominator j hf).property
    have hle : B.openRing j ≤ T := by
      apply sup_le
      · intro c hc
        obtain ⟨n, hn⟩ := B.clear c hc
        refine ⟨n, ?_⟩
        change c * ((((B.d : yAtlas.ring i) : M) : L) * B.x j ^ 5) ^ n ∈ quotientAtlas.ring i
        rw [mul_pow, ← mul_assoc]
        exact Subalgebra.mul_mem _ hn (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hf 5) n)
      · apply Algebra.adjoin_le
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        refine ⟨1, ?_⟩
        change (B.x j)⁻¹ * (((((B.d : yAtlas.ring i) : M) : L)) * B.x j ^ 5) ^ 1 ∈
          quotientAtlas.ring i
        have he : (B.x j)⁻¹ * ((((B.d : yAtlas.ring i) : M) : L) * B.x j ^ 5) ^ 1 =
            ((B.d : yAtlas.ring i) : M) * B.x j ^ 4 := by
          have := B.x_ne j
          field_simp
        rw [he]
        exact Subalgebra.mul_mem _ B.d.property (Subalgebra.pow_mem _ hf 4)
    intro c hc
    exact hle hc
  weight_ne := hw
  v_ne := by
    rw [B.tuple_zero j σ e hσ he]
    exact B.x_ne j
  v_inv := by
    rw [B.tuple_zero j σ e hσ he]
    exact B.inv_mem_openRing j
  euler_v0 := by
    rw [B.tuple_zero j σ e hσ he]
    exact B.euler_x j
  euler_v := by
    intro k hk
    have hne : σ k ≠ j := by
      intro h
      exact hk (σ.injective (h.trans hσ.symm))
    rw [tuple, euler_div_pow _ _ (B.x_ne j) _ _ (B.euler_x _) (B.euler_x j),
      show ((B.wt (σ k) - (e (σ k) : ℤ) * B.wt j : ℤ) : L) = 0 from
        weight_cast_eq_zero _ _ _ (by simpa using hb _ hne), zero_mul]
  independent := independent_of_field_top _ (B.tuple_field_top j σ e hσ he)
  poly_le := Algebra.adjoin_le (by
    rintro _ ⟨k, rfl⟩
    exact B.tuple_mem_openRing j σ e k)
  hull_le := B.openRing_le_hull j σ e hσ he

end YBase

end
end Eff

import Geonormal.Projective
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Global functions on the characteristic-19 surface are constants

The field `k` is algebraically closed in the function field `F`. In `E = k(x, t)` an element
algebraic over `k` is integral over the factorial ring `k[x, t]`, hence a polynomial, and a
nonconstant polynomial is not integral over `k` by total degree. For `F = E ⊕ E y`, the
conjugation `y ↦ -y` reduces to `E`, and `g = x³ + c²t⁷x + t` is not a constant multiple of a
square because its degree in `x` is odd. Since `X` is proper and integral, its global
functions are therefore the constants.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry Polynomial

noncomputable section

/-! ## `k` is algebraically closed in `E` -/

theorem polynomial_constant_of_isIntegral (p : R₂) (hp : IsIntegral k p) :
    ∃ c : k, MvPolynomial.C c = p := by
  by_cases hd : p.totalDegree = 0
  · exact ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd).symm⟩
  exfalso
  obtain ⟨q, hq, hroot⟩ := hp
  have hp0 : p ≠ 0 := by rintro rfl; simp at hd
  have hpow (n : ℕ) : (p ^ n).totalDegree = n * p.totalDegree := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain (pow_ne_zero n hp0) hp0, ih]
      ring
  have hq1 : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h | h
    · rw [Polynomial.Monic.natDegree_eq_zero hq] at h
      simp [h] at hroot
    · exact h
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hq, map_one,
    one_mul] at hroot
  have hlt : (∑ i ∈ Finset.range q.natDegree, algebraMap k R₂ (q.coeff i) * p ^ i).totalDegree <
      (p ^ q.natDegree).totalDegree := by
    rw [hpow]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
    refine (Finset.sup_lt_iff (by positivity)).mpr fun i hi ↦ ?_
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add, hpow]
    have := Finset.mem_range.mp hi
    have hd' : 0 < p.totalDegree := Nat.pos_of_ne_zero hd
    nlinarith
  have h0 := MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt
  rw [add_comm] at hroot
  rw [hroot, MvPolynomial.totalDegree_zero, hpow] at h0
  have hd' : 0 < p.totalDegree := Nat.pos_of_ne_zero hd
  have : 0 < q.natDegree * p.totalDegree := Nat.mul_pos hq1 hd'
  omega

theorem E_constants (α : E) (hα : IsIntegral k α) : ∃ c : k, algebraMap k E c = α := by
  have hR : IsIntegral R₂ α := hα.tower_top
  obtain ⟨p, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hR
  have hp : IsIntegral k p :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k R₂ E)
      (IsFractionRing.injective R₂ E)).mp hα
  obtain ⟨c, hc⟩ := polynomial_constant_of_isIntegral p hp
  exact ⟨c, by rw [← hc, IsScalarTower.algebraMap_apply k R₂ E]; rfl⟩


/-! ## `k` is algebraically closed in `F` -/

/-- `g` is not a constant multiple of a square in `k[x, t]`. -/
theorem gPoly_mul_sq_ne (κ : k) (a b : R₂) (hb : b ≠ 0) :
    gPoly * b ^ 2 ≠ MvPolynomial.C κ * a ^ 2 := by
  intro h
  have hL : gPoly * b ^ 2 ≠ 0 := mul_ne_zero gPoly_ne_zero (pow_ne_zero 2 hb)
  have hκ : κ ≠ 0 := by rintro rfl; simp [h] at hL
  have ha : a ≠ 0 := by rintro rfl; simp [h] at hL
  set φ := MvPolynomial.finSuccEquiv k 1
  have hφa : φ a ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr ha
  have hφb : φ b ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr hb
  have hφg : φ gPoly ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr gPoly_ne_zero
  have hφκ : φ (MvPolynomial.C κ) = C (MvPolynomial.C κ) := φ.commutes κ
  have hdeg := congrArg (fun p ↦ (φ p).natDegree) h
  simp only [map_pow, map_mul, hφκ] at hdeg
  rw [natDegree_mul hφg (pow_ne_zero 2 hφb), natDegree_pow, natDegree_finSuccEquiv_gPoly,
    natDegree_C_mul (by simpa using hκ), natDegree_pow] at hdeg
  omega

/-- Every element of `F` is `α + β y` with `α, β ∈ E`. -/
theorem F_decomp (z : F) : ∃ α β : E, z = algebraMap E F α + algebraMap E F β * y := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hr : (p %ₘ quad).natDegree ≤ 1 := by
      have := natDegree_modByMonic_lt p quad_monic (by
        intro h; have := quad_natDegree; rw [h] at this; simp at this)
      rw [quad_natDegree] at this
      omega
    have hmk : AdjoinRoot.mk quad p = AdjoinRoot.mk quad (p %ₘ quad) := by
      rw [AdjoinRoot.mk_eq_mk]
      refine ⟨p /ₘ quad, ?_⟩
      have := modByMonic_add_div p quad
      rw [← sub_eq_iff_eq_add.mpr this.symm]
      ring
    refine ⟨(p %ₘ quad).coeff 0, (p %ₘ quad).coeff 1, ?_⟩
    conv_lhs => rw [hmk, Polynomial.eq_X_add_C_of_natDegree_le_one hr]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, y]
    rw [add_comm]
    rfl

theorem quad_eval₂_neg_y : quad.eval₂ (algebraMap E F) (-y) = 0 := by
  simp only [quad, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq, y_sq, algebraMap_gE, sub_self]

/-- The conjugation `y ↦ -y`, a `k`-algebra map. -/
def conj : F →ₐ[k] F :=
  AdjoinRoot.liftAlgHom quad (IsScalarTower.toAlgHom k E F) (-y) quad_eval₂_neg_y

@[simp] theorem conj_algebraMap (α : E) : conj (algebraMap E F α) = algebraMap E F α :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ α

@[simp] theorem conj_y : conj y = -y := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem two_ne_zero_F : (2 : F) ≠ 0 := by
  have h : (2 : F) = algebraMap F₁₉ F 2 := (map_ofNat (algebraMap F₁₉ F) 2).symm
  rw [h, map_ne_zero_iff _ (algebraMap F₁₉ F).injective]
  decide

theorem F_constants (z : F) (hz : IsIntegral k z) : ∃ c : k, algebraMap k F c = z := by
  obtain ⟨α, β, rfl⟩ := F_decomp z
  have hconj' : conj (algebraMap E F α + algebraMap E F β * y) =
      algebraMap E F α + algebraMap E F β * -y := by
    rw [map_add, map_mul, conj_algebraMap, conj_algebraMap, conj_y]
  have hconj : IsIntegral k (algebraMap E F α + algebraMap E F β * -y) := hconj' ▸ hz.map conj
  -- the even part
  have hα : IsIntegral k (algebraMap E F α) := by
    have h2 : algebraMap E F α = algebraMap k F (2⁻¹ : k) *
        ((algebraMap E F α + algebraMap E F β * y) + (algebraMap E F α + algebraMap E F β * -y)) := by
      have : algebraMap k F (2⁻¹ : k) = (2 : F)⁻¹ := by simp [map_ofNat]
      rw [this]
      field_simp [two_ne_zero_F]
      ring
    rw [h2]
    exact (isIntegral_algebraMap).mul (hz.add hconj)
  have hαE : IsIntegral k α :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k E F) (algebraMap E F).injective).mp hα
  obtain ⟨c₀, hc₀⟩ := E_constants α hαE
  -- the odd part
  have hw : IsIntegral k (algebraMap E F β * y) := by
    have : algebraMap E F β * y = (algebraMap E F α + algebraMap E F β * y) - algebraMap E F α := by
      ring
    rw [this]
    exact hz.sub hα
  have hw2 : IsIntegral k (algebraMap E F (β ^ 2 * gE)) := by
    have : algebraMap E F (β ^ 2 * gE) = (algebraMap E F β * y) ^ 2 := by
      rw [mul_pow, y_sq, ← algebraMap_gE, map_mul, map_pow]
    rw [this]
    exact hw.pow 2
  obtain ⟨κ, hκ⟩ := E_constants _
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom k E F) (algebraMap E F).injective).mp hw2)
  have hβ : β = 0 := by
    by_contra hβ
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := R₂) β
    have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
    have hu0 : u ≠ 0 := by rintro rfl; simp at hβ
    have hvE : algebraMap R₂ E v ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R₂ E)).mpr hv0
    apply gPoly_mul_sq_ne κ v u hu0
    apply IsFractionRing.injective R₂ E
    have hC : algebraMap R₂ E (MvPolynomial.C κ) = algebraMap k E κ :=
      (IsScalarTower.algebraMap_apply k R₂ E κ).symm
    rw [map_mul, map_mul, map_pow, map_pow, ← gE, hC, hκ]
    field_simp
  refine ⟨c₀, ?_⟩
  rw [hβ, map_zero, zero_mul, add_zero, ← hc₀, ← IsScalarTower.algebraMap_apply]


/-! ## Generation of the function field and global sections -/

theorem algebraMap_cE : algebraMap E F cE = algebraMap k F c :=
  (IsScalarTower.algebraMap_apply k E F c).symm

/-- A subfield containing `c, t, x, y` is the whole function field. -/
theorem subfield_eq_top (K : Subfield F) (hc : algebraMap k F c ∈ K) (ht : t ∈ K) (hx : x ∈ K)
    (hy : y ∈ K) : K = ⊤ := by
  let K' : Subfield E := K.comap (algebraMap E F)
  have hF (r : F₁₉) : algebraMap F₁₉ E r ∈ K' := by
    change algebraMap E F (algebraMap F₁₉ E r) ∈ K
    rw [← IsScalarTower.algebraMap_apply, ← ZMod.natCast_zmod_val r, map_natCast]
    exact natCast_mem K _
  let M : IntermediateField F₁₉ E := K'.toIntermediateField hF
  have hM : M = ⊤ := by
    rw [eq_top_iff, ← standard_generation, IntermediateField.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · change algebraMap E F cE ∈ K
      rw [algebraMap_cE]; exact hc
    · exact ht
    · exact hx
  have hE (α : E) : algebraMap E F α ∈ K := by
    have : α ∈ M := hM ▸ IntermediateField.mem_top
    exact this
  rw [eq_top_iff]
  intro z _
  obtain ⟨α, β, rfl⟩ := F_decomp z
  exact K.add_mem (hE α) (K.mul_mem (hE β) hy)

theorem t_mem_chart_zero : t ∈ chartRing 0 := by
  have h := first_mem 0
  rwa [show monoF (first 0) = t by rw [t_eq_monoF]; rfl] at h

theorem x_mem_chart_zero : x ∈ chartRing 0 := by
  have h := second_mem 0
  rwa [show monoF (second 0) = x by rw [x_eq_monoF]; rfl] at h

theorem y_mem_chart_zero : y ∈ chartRing 0 := by
  have h := yc_mem 0
  rwa [show yc 0 = y by rw [yc, show yScale 0 = 0 from rfl, monoF_zero, mul_one]] at h

instance chartRing_zero_isFractionRing : IsFractionRing (chartRing 0) F := by
  apply IsFractionRing.of_field
  intro z
  have hK : Subfield.closure (chartRing 0 : Set F) = ⊤ :=
    subfield_eq_top _ (Subfield.subset_closure ((chartRing 0).algebraMap_mem c))
      (Subfield.subset_closure t_mem_chart_zero) (Subfield.subset_closure x_mem_chart_zero)
      (Subfield.subset_closure y_mem_chart_zero)
  have hz : z ∈ Subfield.closure (chartRing 0 : Set F) := hK ▸ Subfield.mem_top z
  rw [Subfield.mem_closure_iff] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have hS : Subring.closure (chartRing 0 : Set F) = (chartRing 0).toSubring :=
    Subring.closure_eq (chartRing 0).toSubring
  rw [hS] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

/-- The global functions on `X` are the constants `k`. -/
theorem x_globalScalarMap_bijective : Function.Bijective (globalScalarMap k xToBase) := by
  have : IsProper xToBase := x_proper
  have : IsFractionRing (atlas.ring (0 : Fin 5)) F := chartRing_zero_isFractionRing
  let := functionFieldAlgebra k xToBase
  let e := atlas.functionFieldAlgEquiv (0 : Fin 5)
  exact globalScalarMap_bijective_of_constants k F xToBase
    (fun z hz ↦ F_constants z hz.isIntegral) e.toRingEquiv (RingHom.ext fun c ↦ e.commutes c)

end
end Geonormal

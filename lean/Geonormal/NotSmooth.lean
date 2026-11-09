import Geonormal.Dimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth

/-! # The characteristic-19 surface is not smooth

Over `B = k[u]/(u¹⁹ - 1/c)` the point `t₀ = 17u⁶`, `x₀ = 12u²`, `y₀ = 0` of chart `0` has
`g = ∂g/∂t = ∂g/∂x = 0`. The tangent vector `y ↦ ε` is therefore a `k`-algebra map from chart `0`
to `B[ε]/(ε³)` modulo `ε²`, but it has no lift to `B[ε]/(ε³)`: a lift would force `ε² = 0`.
Hence chart `0` is not formally smooth over `k`, and `X` is not smooth over `k`.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

/-! ## The presentation of chart `0` over `k` -/

/-- The equation `Y² - (X³ + c²T⁷X + T)` in `k[Y, T, X]`. -/
def fK : MvPolynomial (Fin 3) k := X 0 ^ 2 - (X 2 ^ 3 + C (c ^ 2) * X 1 ^ 7 * X 2 + X 1)

/-- `g = X³ + c²T⁷X + T` in `k[T, X]`. -/
def gK : MvPolynomial (Fin 2) k := X 1 ^ 3 + C (c ^ 2) * X 0 ^ 7 * X 1 + X 0

def evalK : MvPolynomial (Fin 3) k →ₐ[k] F := aeval ![y, t, x]

theorem finSuccEquiv_fK : finSuccEquiv k 2 fK = Polynomial.X ^ 2 - Polynomial.C gK := by
  have h1 : finSuccEquiv k 2 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
  have h2 : finSuccEquiv k 2 (X 2) = Polynomial.C (X 1) := finSuccEquiv_X_succ (j := 1)
  have hc : finSuccEquiv k 2 (C c) = Polynomial.C (C c) := (finSuccEquiv k 2).commutes _
  simp [fK, gK, finSuccEquiv_X_zero, h1, h2, hc]

/-- The coefficient evaluation `k[T, X] → F`. -/
def coeffK : MvPolynomial (Fin 2) k →+* F := (aeval ![t, x]).toRingHom

theorem evalK_eq_eval₂ (p : MvPolynomial (Fin 3) k) :
    evalK p = Polynomial.eval₂ coeffK y (finSuccEquiv k 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h := (finSuccEquiv k 2).commutes a
    rw [MvPolynomial.algebraMap_eq] at h
    rw [h, Polynomial.algebraMap_apply, Polynomial.eval₂_C, evalK, aeval_C]
    simp [coeffK]
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [finSuccEquiv_X_zero, Polynomial.eval₂_X]
      simp [evalK]
    · rw [finSuccEquiv_X_succ, Polynomial.eval₂_C]
      fin_cases j <;> simp [evalK, coeffK]

theorem coeffK_eq (q : MvPolynomial (Fin 2) k) :
    coeffK q = algebraMap E F (aeval ![tE, xE] q) := by
  have : (![t, x] : Fin 2 → F) = algebraMap E F ∘ ![tE, xE] := by
    funext j; fin_cases j <;> rfl
  rw [coeffK, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this, MvPolynomial.aeval_algebraMap_apply]

theorem coeffK_gK : coeffK gK = y ^ 2 := by
  rw [y_sq]
  simp [coeffK, gK]

theorem txE_independent : AlgebraicIndependent k ![tE, xE] := by
  convert toricE_independent 0 using 1
  funext j
  fin_cases j <;> simp [monoE, first, second]

theorem ker_evalK : RingHom.ker evalK = Ideal.span {fK} := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    set φ := finSuccEquiv k 2
    set H : Polynomial (MvPolynomial (Fin 2) k) := Polynomial.X ^ 2 - Polynomial.C gK
    have hH : H.Monic := by unfold H; monicity!
    have hHdeg : H.natDegree = 2 := by unfold H; compute_degree!
    have hdecomp := Polynomial.modByMonic_add_div (φ p) H
    have hr : (φ p %ₘ H).natDegree ≤ 1 := by
      have := Polynomial.natDegree_modByMonic_lt (φ p) hH (by
        intro h1; rw [h1, Polynomial.natDegree_one] at hHdeg; omega)
      omega
    have h2 : Polynomial.eval₂ coeffK y H = 0 := by
      simp [H, coeffK_gK]
    have hev : Polynomial.eval₂ coeffK y (φ p %ₘ H) = 0 := by
      have h1 : Polynomial.eval₂ coeffK y (φ p) = 0 := (evalK_eq_eval₂ p) ▸ hp
      rw [← hdecomp, Polynomial.eval₂_add, Polynomial.eval₂_mul, h2, zero_mul, add_zero] at h1
      exact h1
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hr] at hev
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, coeffK_eq] at hev
    have hu := decomp_unique (aeval ![tE, xE] ((φ p %ₘ H).coeff 0))
      (aeval ![tE, xE] ((φ p %ₘ H).coeff 1)) (by rw [← hev]; ring)
    have hr0 : (φ p %ₘ H).coeff 0 = 0 := txE_independent (by rw [hu.1, map_zero])
    have hr1 : (φ p %ₘ H).coeff 1 = 0 := txE_independent (by rw [hu.2, map_zero])
    have hrz : φ p %ₘ H = 0 := by
      rw [Polynomial.eq_X_add_C_of_natDegree_le_one hr, hr0, hr1]
      simp
    rw [Ideal.mem_span_singleton]
    refine ⟨φ.symm (φ p /ₘ H), ?_⟩
    apply φ.injective
    rw [map_mul, φ.apply_symm_apply, finSuccEquiv_fK]
    rw [hrz, zero_add] at hdecomp
    exact hdecomp.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      evalK_eq_eval₂, finSuccEquiv_fK]
    simp [coeffK_gK]


theorem evalK_mem (p : MvPolynomial (Fin 3) k) : evalK p ∈ chartRing 0 := by
  have h : Set.range ![y, t, x] ⊆ (chartRing 0 : Set F) := by
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact y_mem_chart_zero
    · exact t_mem_chart_zero
    · exact x_mem_chart_zero
  have := (Algebra.adjoin_le h : Algebra.adjoin k (Set.range ![y, t, x]) ≤ chartRing 0)
  apply this
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨p, rfl⟩

/-- The presentation map onto chart `0`. -/
def piK : MvPolynomial (Fin 3) k →ₐ[k] chartRing 0 := evalK.codRestrict (chartRing 0) evalK_mem

theorem piK_surjective : Function.Surjective piK := by
  rintro ⟨z, hz⟩
  have hle : chartRing 0 ≤ Algebra.adjoin k (Set.range ![y, t, x]) := by
    apply Algebra.adjoin_le
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact Algebra.subset_adjoin ⟨1, by rw [t_eq_monoF]; rfl⟩
    · exact Algebra.subset_adjoin ⟨2, by rw [x_eq_monoF]; rfl⟩
    · exact Algebra.subset_adjoin ⟨0, by
        simp [yc, show yScale 0 = 0 from rfl, monoF_zero]⟩
  obtain ⟨p, hp⟩ := (Algebra.adjoin_range_eq_range_aeval k ![y, t, x] ▸ hle hz :
    z ∈ (aeval ![y, t, x] : MvPolynomial (Fin 3) k →ₐ[k] F).range)
  exact ⟨p, Subtype.ext hp⟩

theorem ker_piK : RingHom.ker piK = Ideal.span {fK} := by
  rw [← ker_evalK]
  ext p
  simp only [RingHom.mem_ker]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

/-! ## A singular point over `k[u]/(u¹⁹ - 1/c)` -/

/-- The polynomial `u¹⁹ - 1/c`. -/
def rootPoly : Polynomial k := Polynomial.X ^ 19 - Polynomial.C c⁻¹

/-- The ring `B = k[u]/(u¹⁹ - 1/c)`. -/
abbrev Bpt := AdjoinRoot rootPoly

def u : Bpt := AdjoinRoot.root rootPoly

theorem u_pow : u ^ 19 = algebraMap k Bpt c⁻¹ := by
  have h := AdjoinRoot.eval₂_root rootPoly
  rw [rootPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  exact h

instance : Nontrivial Bpt := AdjoinRoot.nontrivial rootPoly (by
  rw [rootPoly, Polynomial.degree_sub_C (by rw [Polynomial.degree_X_pow]; norm_num),
    Polynomial.degree_X_pow]
  norm_num)

theorem c_mul_inv_B : algebraMap k Bpt c * algebraMap k Bpt c⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ c_ne_zero, map_one]

theorem nineteen_B : (19 : Bpt) = 0 := by
  have : ((19 : ℕ) : Bpt) = 0 := by
    rw [← map_natCast (algebraMap F₁₉ Bpt), ZMod.natCast_self, map_zero]
  exact_mod_cast this

/-- The singular point. -/
def t₀ : Bpt := 17 * u ^ 6
def x₀ : Bpt := 12 * u ^ 2

theorem g_t₀_x₀ : x₀ ^ 3 + algebraMap k Bpt c ^ 2 * t₀ ^ 7 * x₀ + t₀ = 0 := by
  have hu := u_pow
  have hgd := c_mul_inv_B
  have h19 := nineteen_B
  set γ := algebraMap k Bpt c
  set δ := algebraMap k Bpt c⁻¹
  rw [t₀, x₀]
  linear_combination (4924064076 * δ * γ ^ 2 * u ^ 6 + 4924064076 * γ ^ 2 * u ^ 25) * hu +
    (4924064076 * δ * γ * u ^ 6 + 4924064076 * u ^ 6) * hgd + (259161359 * u ^ 6) * h19

theorem gt_t₀_x₀ : 7 * algebraMap k Bpt c ^ 2 * t₀ ^ 6 * x₀ + 1 = 0 := by
  have hu := u_pow
  have hgd := c_mul_inv_B
  have h19 := nineteen_B
  set γ := algebraMap k Bpt c
  set δ := algebraMap k Bpt c⁻¹
  rw [t₀, x₀]
  linear_combination (2027555796 * δ * γ ^ 2 + 2027555796 * γ ^ 2 * u ^ 19) * hu +
    (2027555796 * δ * γ + 2027555796) * hgd + 106713463 * h19

theorem gx_t₀_x₀ : 3 * x₀ ^ 2 + algebraMap k Bpt c ^ 2 * t₀ ^ 7 = 0 := by
  have hu := u_pow
  have hgd := c_mul_inv_B
  have h19 := nineteen_B
  set γ := algebraMap k Bpt c
  set δ := algebraMap k Bpt c⁻¹
  rw [t₀, x₀]
  linear_combination (410338673 * δ * γ ^ 2 * u ^ 4 + 410338673 * γ ^ 2 * u ^ 23) * hu +
    (410338673 * δ * γ * u ^ 4 + 410338673 * u ^ 4) * hgd + (21596795 * u ^ 4) * h19


/-! ## The tangent vector `y ↦ ε` does not lift -/

/-- `B[ε]/(ε³)`. -/
abbrev Cring := Polynomial Bpt ⧸ Ideal.span {(Polynomial.X : Polynomial Bpt) ^ 3}

def ε : Cring := Ideal.Quotient.mk _ Polynomial.X

theorem ε_cube : ε ^ 3 = 0 := by
  rw [ε, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem ε_sq_ne : ε ^ 2 ≠ 0 := by
  rw [ε, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  have h2 := congrArg (Polynomial.coeff · 2) hq
  simp only [Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow_mul'] at h2
  norm_num at h2

/-- The square-zero ideal `(ε²)`. -/
def Isq : Ideal Cring := Ideal.span {ε ^ 2}

theorem Isq_nilpotent : IsNilpotent Isq := by
  refine ⟨2, ?_⟩
  have h4 : (ε ^ 2) ^ 2 = 0 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, ε_cube, zero_mul]
  rw [Isq, Ideal.span_singleton_pow, h4, Ideal.span_singleton_eq_bot.mpr rfl]
  rfl

/-- `B → B[ε]/(ε²)`. -/
def ρ : Bpt →ₐ[k] Cring ⧸ Isq := (Ideal.Quotient.mkₐ k Isq).comp (IsScalarTower.toAlgHom k Bpt Cring)

/-- The tangent vector at the singular point, as a map to `B[ε]/(ε²)`. -/
def φ₀ : MvPolynomial (Fin 3) k →ₐ[k] Cring ⧸ Isq := aeval ![Ideal.Quotient.mk Isq ε, ρ t₀, ρ x₀]

theorem φ₀_fK : φ₀ fK = 0 := by
  have hε : Ideal.Quotient.mk Isq ε ^ 2 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hg : ρ (x₀ ^ 3 + algebraMap k Bpt c ^ 2 * t₀ ^ 7 * x₀ + t₀) = 0 := by
    rw [g_t₀_x₀, map_zero]
  simp only [map_add, map_mul, map_pow, AlgHom.commutes] at hg
  simp only [fK, φ₀, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [hε, hg, sub_zero]

theorem φ₀_ker : ∀ a ∈ RingHom.ker piK, φ₀ a = 0 := by
  intro a ha
  rw [ker_piK] at ha
  have hle : Ideal.span {fK} ≤ RingHom.ker φ₀ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact φ₀_fK
  exact hle ha

/-- The tangent vector as a map from chart `0`. -/
def tangent : chartRing 0 →ₐ[k] Cring ⧸ Isq :=
  (Ideal.Quotient.liftₐ (RingHom.ker piK) φ₀ φ₀_ker).comp
    (Ideal.quotientKerAlgEquivOfSurjective piK_surjective).symm.toAlgHom

theorem tangent_piK (p : MvPolynomial (Fin 3) k) : tangent (piK p) = φ₀ p := by
  have he : (Ideal.quotientKerAlgEquivOfSurjective piK_surjective).symm (piK p) =
      Ideal.Quotient.mk _ p := by
    apply (Ideal.quotientKerAlgEquivOfSurjective piK_surjective).injective
    rw [AlgEquiv.apply_symm_apply]
    rfl
  change Ideal.Quotient.liftₐ (RingHom.ker piK) φ₀ φ₀_ker
    ((Ideal.quotientKerAlgEquivOfSurjective piK_surjective).symm (piK p)) = φ₀ p
  rw [he]
  rfl


/-- Chart `0` is not formally smooth over `k`: the tangent vector has no lift. -/
theorem chart_zero_not_formallySmooth : ¬ Algebra.FormallySmooth k (chartRing 0) := by
  intro hfs
  set ψ := Algebra.FormallySmooth.lift Isq Isq_nilpotent tangent
  have hψ (z : chartRing 0) : Ideal.Quotient.mk Isq (ψ z) = tangent z :=
    Algebra.FormallySmooth.mk_lift Isq Isq_nilpotent tangent z
  have hgen (j : Fin 3) (v : Cring) (hv : Ideal.Quotient.mk Isq v = φ₀ (X j)) :
      ∃ b, ψ (piK (X j)) = v + ε ^ 2 * b := by
    have h := hψ (piK (X j))
    rw [tangent_piK, ← hv, Ideal.Quotient.eq, Isq, Ideal.mem_span_singleton'] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by linear_combination -hb⟩
  obtain ⟨b₃, h₃⟩ := hgen 0 ε (by simp [φ₀])
  obtain ⟨b₁, h₁⟩ := hgen 1 (algebraMap Bpt Cring t₀) (by simp [φ₀, ρ])
  obtain ⟨b₂, h₂⟩ := hgen 2 (algebraMap Bpt Cring x₀) (by simp [φ₀, ρ])
  have hrel0 : piK fK = 0 := by
    rw [← RingHom.mem_ker, ker_piK]
    exact Ideal.mem_span_singleton_self _
  have hrel : (ψ.comp piK) fK = 0 := by
    rw [AlgHom.comp_apply, hrel0, map_zero]
  have hexp : (ψ.comp piK) fK = (ψ (piK (X 0))) ^ 2 - ((ψ (piK (X 2))) ^ 3 +
      algebraMap k Cring c ^ 2 * (ψ (piK (X 1))) ^ 7 * ψ (piK (X 2)) + ψ (piK (X 1))) := by
    simp [fK]
  rw [hexp, h₁, h₂, h₃] at hrel
  have hG : algebraMap k Cring c = algebraMap Bpt Cring (algebraMap k Bpt c) :=
    IsScalarTower.algebraMap_apply k Bpt Cring c
  have hg0 := congrArg (algebraMap Bpt Cring) g_t₀_x₀
  have hgt := congrArg (algebraMap Bpt Cring) gt_t₀_x₀
  have hgx := congrArg (algebraMap Bpt Cring) gx_t₀_x₀
  simp only [map_add, map_mul, map_pow, map_zero, map_one, map_ofNat, ← hG] at hg0 hgt hgx
  set T := algebraMap Bpt Cring t₀
  set Xx := algebraMap Bpt Cring x₀
  set G := algebraMap k Cring c
  apply ε_sq_ne
  linear_combination hrel + hg0 + (ε ^ 2 * b₁) * hgt + (ε ^ 2 * b₂) * hgx -
    (-7 * G ^ 2 * T ^ 6 * b₁ * b₂ * ε - 21 * G ^ 2 * T ^ 5 * Xx * b₁ ^ 2 * ε -
      21 * G ^ 2 * T ^ 5 * b₁ ^ 2 * b₂ * ε ^ 3 - 35 * G ^ 2 * T ^ 4 * Xx * b₁ ^ 3 * ε ^ 3 -
      35 * G ^ 2 * T ^ 4 * b₁ ^ 3 * b₂ * ε ^ 5 - 35 * G ^ 2 * T ^ 3 * Xx * b₁ ^ 4 * ε ^ 5 -
      35 * G ^ 2 * T ^ 3 * b₁ ^ 4 * b₂ * ε ^ 7 - 21 * G ^ 2 * T ^ 2 * Xx * b₁ ^ 5 * ε ^ 7 -
      21 * G ^ 2 * T ^ 2 * b₁ ^ 5 * b₂ * ε ^ 9 - 7 * G ^ 2 * T * Xx * b₁ ^ 6 * ε ^ 9 -
      7 * G ^ 2 * T * b₁ ^ 6 * b₂ * ε ^ 11 - G ^ 2 * Xx * b₁ ^ 7 * ε ^ 11 -
      G ^ 2 * b₁ ^ 7 * b₂ * ε ^ 13 - 3 * Xx * b₂ ^ 2 * ε - b₂ ^ 3 * ε ^ 3 + b₃ ^ 2 * ε +
      2 * b₃) * ε_cube

/-- `X` is not smooth over `k`. -/
theorem x_not_smooth : ¬ Smooth xToBase := by
  intro h
  let j : atlas.Index := (0 : Fin 5)
  have h0 : Smooth (atlas.chartInclusion j ≫ atlas.toBase) := inferInstance
  rw [atlas.chartInclusion_toBase, PrincipalAtlas.chartToBase] at h0
  have h1 := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h0
  rw [CommRingCat.hom_ofHom, RingHom.smooth_algebraMap] at h1
  exact chart_zero_not_formallySmooth h1.formallySmooth

end
end Geonormal

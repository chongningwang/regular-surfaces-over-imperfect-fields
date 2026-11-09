import Geonormal.Constants
import SurfaceLib.RingTheory.Hypersurface
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-! # Every local ring of the characteristic-19 surface is regular

Each chart ring is presented over `F₁₉` as the hypersurface `Y² = g_i(c, e₁, e₂)` in
`F₁₉[Y, c, e₁, e₂]`, after inverting the nonzero polynomials in `c`. The partial derivatives of
the equation generate an ideal containing a power of `c`; this explicit certificate puts the
equation outside the square of the maximal ideal at every prime, and the quotient of a regular
local ring by such an element is regular.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry IsLocalRing MvPolynomial

noncomputable section

/-- The ambient polynomial ring `F₁₉[Y, c, e₁, e₂]`. -/
abbrev P₄ := MvPolynomial (Fin 4) F₁₉

/-- The chart equations `Y² - g_i(c, e₁, e₂)`. -/
def hPoly : Fin 5 → P₄ := ![
  X 0 ^ 2 - (X 3 ^ 3 + X 1 ^ 2 * X 2 ^ 7 * X 3 + X 2),
  X 0 ^ 2 - (X 3 + X 1 ^ 2 * X 2 ^ 7 * X 3 ^ 3 + X 2 * X 3 ^ 4),
  X 0 ^ 2 - (X 2 * X 3 ^ 3 + X 1 ^ 2 * X 3 + X 2 ^ 9),
  X 0 ^ 2 - (X 3 + X 1 ^ 2 * X 2 + X 2 ^ 11 * X 3 ^ 9),
  X 0 ^ 2 - (X 3 + X 1 ^ 2 * X 2 * X 3 ^ 3 + X 2 ^ 11 * X 3 ^ 4)]

/-- The branch polynomials `g_i` in `F₁₉[c, e₁, e₂]`. -/
def gChart3 : Fin 5 → MvPolynomial (Fin 3) F₁₉ := ![
  X 2 ^ 3 + X 0 ^ 2 * X 1 ^ 7 * X 2 + X 1,
  X 2 + X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 3 + X 1 * X 2 ^ 4,
  X 1 * X 2 ^ 3 + X 0 ^ 2 * X 2 + X 1 ^ 9,
  X 2 + X 0 ^ 2 * X 1 + X 1 ^ 11 * X 2 ^ 9,
  X 2 + X 0 ^ 2 * X 1 * X 2 ^ 3 + X 1 ^ 11 * X 2 ^ 4]

theorem finSuccEquiv_X_one : finSuccEquiv F₁₉ 3 (X 1) = Polynomial.C (X 0) :=
  finSuccEquiv_X_succ (j := 0)
theorem finSuccEquiv_X_two : finSuccEquiv F₁₉ 3 (X 2) = Polynomial.C (X 1) :=
  finSuccEquiv_X_succ (j := 1)
theorem finSuccEquiv_X_three : finSuccEquiv F₁₉ 3 (X 3) = Polynomial.C (X 2) :=
  finSuccEquiv_X_succ (j := 2)

theorem finSuccEquiv_hPoly (i : Fin 5) :
    finSuccEquiv F₁₉ 3 (hPoly i) = Polynomial.X ^ 2 - Polynomial.C (gChart3 i) := by
  fin_cases i <;>
    simp [hPoly, gChart3, finSuccEquiv_X_zero, finSuccEquiv_X_one, finSuccEquiv_X_two,
      finSuccEquiv_X_three]

/-- The values of `Y, c, e₁, e₂` on chart `i`. -/
def chartVals (i : Fin 5) : Fin 4 → F := ![yc i, algebraMap k F c, monoF (first i), monoF (second i)]

/-- Evaluation of the ambient polynomial ring on chart `i`. -/
def chartEval (i : Fin 5) : P₄ →ₐ[F₁₉] F := aeval (chartVals i)

theorem chartVals_succ (i : Fin 5) (j : Fin 3) :
    chartVals i j.succ = algebraMap E F (coordE i j) := by
  fin_cases j
  · exact (IsScalarTower.algebraMap_apply k E F c)
  · rfl
  · rfl

/-- The coefficient evaluation on chart `i`. -/
def coeffEval (i : Fin 5) : MvPolynomial (Fin 3) F₁₉ →+* F :=
  (algebraMap E F).comp (aeval (coordE i)).toRingHom

theorem chartEval_eq_eval₂ (i : Fin 5) (p : P₄) :
    chartEval i p = Polynomial.eval₂ (coeffEval i) (yc i) (finSuccEquiv F₁₉ 3 p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h := (finSuccEquiv F₁₉ 3).commutes a
    rw [MvPolynomial.algebraMap_eq] at h
    rw [h, Polynomial.algebraMap_apply, Polynomial.eval₂_C, chartEval, aeval_C]
    simp only [coeffEval, RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_eq,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    exact IsScalarTower.algebraMap_apply F₁₉ E F a
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [finSuccEquiv_X_zero, Polynomial.eval₂_X]
      simp [chartEval, chartVals]
    · rw [finSuccEquiv_X_succ, Polynomial.eval₂_C, chartEval, aeval_X, chartVals_succ]
      simp [coeffEval]


/-! ## The presentation of each chart -/

theorem gChart3_eval (i : Fin 5) : aeval (coordE i) (gChart3 i) = gE * monoE (yScale i) ^ 2 := by
  rw [gE_eq]
  have ht := tE_ne_zero
  have hx := xE_ne_zero
  fin_cases i <;>
    simp [gChart3, coordE, monoE, first, second, yScale, zpow_neg] <;> field_simp <;> ring

theorem coeffEval_eq (i : Fin 5) (q : MvPolynomial (Fin 3) F₁₉) :
    coeffEval i q = algebraMap E F (aeval (coordE i) q) := rfl

theorem yc_sq_eq (i : Fin 5) : yc i ^ 2 = coeffEval i (gChart3 i) := by
  rw [coeffEval_eq, gChart3_eval, map_mul, map_pow, yc, mul_pow, y_sq, ← algebraMap_gE]
  rfl

theorem chartEval_hPoly (i : Fin 5) : chartEval i (hPoly i) = 0 := by
  rw [chartEval_eq_eval₂, finSuccEquiv_hPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C, yc_sq_eq, sub_self]

/-- `1, y` are linearly independent over `E`. -/
theorem decomp_unique (α β : E) (h : algebraMap E F α + algebraMap E F β * y = 0) :
    α = 0 ∧ β = 0 := by
  have hmk : AdjoinRoot.mk quad (Polynomial.C α + Polynomial.C β * Polynomial.X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hdeg : (Polynomial.C α + Polynomial.C β * Polynomial.X).degree < quad.degree := by
    rw [Polynomial.degree_eq_natDegree quad_monic.ne_zero, quad_natDegree]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le β) (by norm_num)
  have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hmk hdeg
  constructor
  · simpa using congrArg (Polynomial.coeff · 0) h0
  · simpa using congrArg (Polynomial.coeff · 1) h0

theorem ker_chartEval (i : Fin 5) : RingHom.ker (chartEval i) = Ideal.span {hPoly i} := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    set φ := finSuccEquiv F₁₉ 3
    set H : Polynomial (MvPolynomial (Fin 3) F₁₉) := Polynomial.X ^ 2 - Polynomial.C (gChart3 i)
    have hH : H.Monic := by unfold H; monicity!
    have hHdeg : H.natDegree = 2 := by unfold H; compute_degree!
    have hdecomp := Polynomial.modByMonic_add_div (φ p) H
    have hr : (φ p %ₘ H).natDegree ≤ 1 := by
      have := Polynomial.natDegree_modByMonic_lt (φ p) hH (by
        intro h1; rw [h1, Polynomial.natDegree_one] at hHdeg; omega)
      omega
    have h2 : Polynomial.eval₂ (coeffEval i) (yc i) H = 0 := by
      rw [show H = φ (hPoly i) from (finSuccEquiv_hPoly i).symm, ← chartEval_eq_eval₂]
      exact chartEval_hPoly i
    have hev : Polynomial.eval₂ (coeffEval i) (yc i) (φ p %ₘ H) = 0 := by
      have h1 : Polynomial.eval₂ (coeffEval i) (yc i) (φ p) = 0 := (chartEval_eq_eval₂ i p) ▸ hp
      rw [← hdecomp, Polynomial.eval₂_add, Polynomial.eval₂_mul, h2, zero_mul, add_zero] at h1
      exact h1
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hr] at hev
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, coeffEval_eq, yc] at hev
    have hu := decomp_unique (aeval (coordE i) ((φ p %ₘ H).coeff 0))
      (aeval (coordE i) ((φ p %ₘ H).coeff 1) * monoE (yScale i)) (by
        rw [map_mul]
        rw [← hev]
        unfold monoF
        ring)
    have hr0 : (φ p %ₘ H).coeff 0 = 0 :=
      coordE_independent i (by rw [hu.1, map_zero])
    have hr1 : (φ p %ₘ H).coeff 1 = 0 :=
      coordE_independent i (by
        rw [map_zero]
        exact (mul_eq_zero.mp hu.2).resolve_right (monoE_ne_zero _))
    have hrz : φ p %ₘ H = 0 := by
      rw [Polynomial.eq_X_add_C_of_natDegree_le_one hr, hr0, hr1]
      simp
    rw [Ideal.mem_span_singleton]
    refine ⟨φ.symm (φ p /ₘ H), ?_⟩
    apply φ.injective
    rw [map_mul, φ.apply_symm_apply, finSuccEquiv_hPoly]
    rw [hrz, zero_add] at hdecomp
    exact hdecomp.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact chartEval_hPoly i


/-! ## Jacobian certificates -/

theorem h19 : (19 : P₄) = 0 := by
  have : ((19 : ℕ) : P₄) = 0 := by
    rw [← map_natCast (algebraMap F₁₉ P₄), ZMod.natCast_self, map_zero]
  exact_mod_cast this

/-- On each chart, the partial derivatives of the equation generate an ideal containing a power
of `c`. -/
theorem pow_c_mem (i : Fin 5) (Q : Ideal P₄) (hQ : ∀ j : Fin 3, pderiv j.succ (hPoly i) ∈ Q) :
    ∃ N : ℕ, (X 1 : P₄) ^ N ∈ Q := by
  have h1 : pderiv 1 (hPoly i) ∈ Q := hQ 0
  have h2 : pderiv 2 (hPoly i) ∈ Q := hQ 1
  have h3 : pderiv 3 (hPoly i) ∈ Q := hQ 2
  fin_cases i
  · refine ⟨0, ?_⟩
    have e : (X 1 : P₄) ^ 0 = (4 * X 1 ^ 3 * X 2 ^ 5 * X 3) * pderiv 1 (hPoly 0) +
        (7 * X 1 ^ 2 * X 2 ^ 6 * X 3 - 1) * pderiv 2 (hPoly 0) := by
      simp only [hPoly, Matrix.cons_val_zero]
      simp [pderiv_X]
      linear_combination (3 * X 1 ^ 4 * X 2 ^ 12 * X 3 ^ 2 : P₄) * h19
    rw [e]
    exact Q.add_mem (Q.mul_mem_left _ h1) (Q.mul_mem_left _ h2)
  · refine ⟨0, ?_⟩
    have e : (X 1 : P₄) ^ 0 =
        (9 * X 1 ^ 3 * X 2 ^ 7 * X 3 - 7 * X 1 * X 2 * X 3 ^ 2) * pderiv 1 (hPoly 1) +
        (7 * X 1 ^ 2 * X 2 ^ 8 * X 3 + 3 * X 2 ^ 2 * X 3 ^ 2) * pderiv 2 (hPoly 1) +
        (3 * X 1 ^ 2 * X 2 ^ 7 * X 3 ^ 2 + 4 * X 2 * X 3 ^ 3 - 1) * pderiv 3 (hPoly 1) := by
      simp only [hPoly, Matrix.cons_val_one, Matrix.cons_val_zero]
      simp [pderiv_X]
      linear_combination (4 * X 1 ^ 4 * X 2 ^ 14 * X 3 ^ 4 + 2 * X 1 ^ 2 * X 2 ^ 8 * X 3 ^ 5 +
        X 2 ^ 2 * X 3 ^ 6 : P₄) * h19
    rw [e]
    exact Q.add_mem (Q.add_mem (Q.mul_mem_left _ h1) (Q.mul_mem_left _ h2)) (Q.mul_mem_left _ h3)
  · refine ⟨3, ?_⟩
    have e : (X 1 : P₄) ^ 3 = (-8 * X 2 * X 3) * pderiv 1 (hPoly 2) +
        (-X 1) * pderiv 3 (hPoly 2) := by
      simp only [hPoly]
      simp [pderiv_X]
      linear_combination (-X 1 * X 2 * X 3 ^ 2 : P₄) * h19
    rw [e]
    exact Q.add_mem (Q.mul_mem_left _ h1) (Q.mul_mem_left _ h3)
  · refine ⟨0, ?_⟩
    have e : (X 1 : P₄) ^ 0 = (8 * X 1 * X 2 ^ 11 * X 3 ^ 7) * pderiv 1 (hPoly 3) +
        (3 * X 2 ^ 12 * X 3 ^ 7) * pderiv 2 (hPoly 3) +
        (9 * X 2 ^ 11 * X 3 ^ 8 - 1) * pderiv 3 (hPoly 3) := by
      simp only [hPoly]
      simp [pderiv_X]
      linear_combination (X 1 ^ 2 * X 2 ^ 12 * X 3 ^ 7 + 6 * X 2 ^ 22 * X 3 ^ 16 : P₄) * h19
    rw [e]
    exact Q.add_mem (Q.add_mem (Q.mul_mem_left _ h1) (Q.mul_mem_left _ h2)) (Q.mul_mem_left _ h3)
  · refine ⟨0, ?_⟩
    have e : (X 1 : P₄) ^ 0 =
        (-7 * X 1 * X 2 ^ 11 * X 3 ^ 2 + 9 * X 1 ^ 3 * X 2 * X 3) * pderiv 1 (hPoly 4) +
        (2 * X 2 ^ 12 * X 3 ^ 2 - 8 * X 1 ^ 2 * X 2 ^ 2 * X 3) * pderiv 2 (hPoly 4) +
        (4 * X 2 ^ 11 * X 3 ^ 3 + 3 * X 1 ^ 2 * X 2 * X 3 ^ 2 - 1) * pderiv 3 (hPoly 4) := by
      simp only [hPoly]
      simp [pderiv_X]
      linear_combination (X 1 ^ 4 * X 2 ^ 2 * X 3 ^ 4 - 4 * X 1 ^ 2 * X 2 ^ 12 * X 3 ^ 5 +
        2 * X 2 ^ 22 * X 3 ^ 6 : P₄) * h19
    rw [e]
    exact Q.add_mem (Q.add_mem (Q.mul_mem_left _ h1) (Q.mul_mem_left _ h2)) (Q.mul_mem_left _ h3)


/-! ## Chart rings as localizations of the hypersurfaces -/

theorem chartVals_mem (i : Fin 5) (j : Fin 4) : chartVals i j ∈ chartRing i := by
  fin_cases j
  · exact yc_mem i
  · exact (chartRing i).algebraMap_mem c
  · exact first_mem i
  · exact second_mem i

theorem chartEval_mem (i : Fin 5) (p : P₄) : chartEval i p ∈ chartRing i := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [chartEval, aeval_C, IsScalarTower.algebraMap_apply F₁₉ k F]
    exact (chartRing i).algebraMap_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]
    exact mul_mem hp (by rw [chartEval, aeval_X]; exact chartVals_mem i j)

/-- The evaluation into the chart ring. -/
def chartHom (i : Fin 5) : P₄ →+* chartRing i :=
  (chartEval i).toRingHom.codRestrict (chartRing i) (chartEval_mem i)

@[simp] theorem coe_chartHom (i : Fin 5) (p : P₄) : (chartHom i p : F) = chartEval i p := rfl

/-- A polynomial in `c` inside the ambient ring. -/
def cPoly (q : P₁) : P₄ := rename (fun _ ↦ (1 : Fin 4)) q

theorem chartEval_cPoly (i : Fin 5) (q : P₁) :
    chartEval i (cPoly q) = algebraMap k F (algebraMap P₁ k q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [cPoly, rename_C, chartEval, aeval_C]
    rw [IsScalarTower.algebraMap_apply F₁₉ k F, IsScalarTower.algebraMap_apply F₁₉ P₁ k]
    rfl
  | add p q hp hq => simp only [cPoly, map_add] at *; rw [hp, hq]
  | mul_X p j hp =>
    simp only [cPoly, map_mul, rename_X] at *
    rw [hp]
    congr 1
    rw [Subsingleton.elim j 0]
    simp [chartEval, chartVals, c]

/-- Every element of a chart ring is a fraction with a polynomial in `c` as denominator. -/
theorem chartRing_frac (i : Fin 5) (a : F) (ha : a ∈ chartRing i) :
    ∃ p : P₄, ∃ q : P₁, q ≠ 0 ∧ algebraMap k F (algebraMap P₁ k q) * a = chartEval i p := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨(X 2 : P₄), 1, one_ne_zero, by simp [chartEval, chartVals]⟩
    · exact ⟨(X 3 : P₄), 1, one_ne_zero, by simp [chartEval, chartVals]⟩
    · exact ⟨(X 0 : P₄), 1, one_ne_zero, by simp [chartEval, chartVals]⟩
  | algebraMap r =>
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := P₁) r
    refine ⟨cPoly u, v, nonZeroDivisors.ne_zero hv, ?_⟩
    have hv0 : algebraMap P₁ k v ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective P₁ k)).mpr (nonZeroDivisors.ne_zero hv)
    rw [chartEval_cPoly, ← map_mul, mul_div_cancel₀ _ hv0]
  | add a b _ _ ha hb =>
    obtain ⟨p, q, hq, hpq⟩ := ha
    obtain ⟨p', q', hq', hpq'⟩ := hb
    refine ⟨cPoly q' * p + cPoly q * p', q * q', mul_ne_zero hq hq', ?_⟩
    simp only [map_add, map_mul, chartEval_cPoly]
    rw [← hpq, ← hpq']
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨p, q, hq, hpq⟩ := ha
    obtain ⟨p', q', hq', hpq'⟩ := hb
    refine ⟨p * p', q * q', mul_ne_zero hq hq', ?_⟩
    simp only [map_mul]
    rw [← hpq, ← hpq']
    ring


/-! ## Regularity -/

theorem chartHom_cPoly (i : Fin 5) (q : P₁) :
    chartHom i (cPoly q) = algebraMap k (chartRing i) (algebraMap P₁ k q) :=
  Subtype.ext (chartEval_cPoly i q)

theorem isUnit_chartHom_cPoly (i : Fin 5) {q : P₁} (hq : q ≠ 0) : IsUnit (chartHom i (cPoly q)) := by
  rw [chartHom_cPoly]
  exact ((Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective P₁ k)).mpr hq)).map _)

theorem c_ne_zero : c ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective P₁ k)).mpr (MvPolynomial.X_ne_zero 0)

theorem chartHom_X_one (i : Fin 5) : chartHom i (X 1) = algebraMap k (chartRing i) c :=
  Subtype.ext (by simp [chartEval, chartVals])

theorem ker_chartHom (i : Fin 5) : RingHom.ker (chartHom i) = Ideal.span {hPoly i} := by
  rw [← ker_chartEval]
  ext p
  simp only [RingHom.mem_ker]
  constructor
  · intro h; simpa using congrArg Subtype.val h
  · intro h; exact Subtype.ext (by simpa using h)

/-- Every local ring of every chart is regular. -/
theorem chart_localization_regular (i : Fin 5) (𝔭 : Ideal (chartRing i)) [𝔭.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  set φ := chartHom i
  set Q : Ideal P₄ := 𝔭.comap φ
  set ψ : Localization.AtPrime Q →+* Localization.AtPrime 𝔭 := Localization.localRingHom Q 𝔭 φ rfl
  have hφh : φ (hPoly i) = 0 := Subtype.ext (chartEval_hPoly i)
  have hdom : ∀ {u v : chartRing i}, u ≠ 0 → u * v = 0 → v = 0 := fun hu huv ↦
    (mul_eq_zero.mp huv).resolve_left hu
  -- surjectivity
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
    obtain ⟨p, q, hq, hpq⟩ := chartRing_frac i (a : F) a.2
    obtain ⟨p', q', hq', hpq'⟩ := chartRing_frac i (s : chartRing i) (s : chartRing i).2
    have hpq₁ : φ (cPoly q) * a = φ p := Subtype.ext (by
      change chartEval i (cPoly q) * (a : F) = chartEval i p
      rw [chartEval_cPoly]; exact hpq)
    have hpq₂ : φ (cPoly q') * s = φ p' := Subtype.ext (by
      change chartEval i (cPoly q') * ((s : chartRing i) : F) = chartEval i p'
      rw [chartEval_cPoly]; exact hpq')
    have hden : cPoly q * p' ∈ Q.primeCompl := by
      change φ (cPoly q * p') ∉ 𝔭
      rw [map_mul, ← hpq₂]
      intro hmem
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
      · exact (Ideal.IsPrime.ne_top inferInstance)
          (Ideal.eq_top_of_isUnit_mem _ h (isUnit_chartHom_cPoly i hq))
      · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h' | h'
        · exact (Ideal.IsPrime.ne_top inferInstance)
            (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_chartHom_cPoly i hq'))
        · exact s.2 h'
    refine ⟨IsLocalization.mk' _ (p * cPoly q') ⟨_, hden⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul, ← hpq₁, ← hpq₂]
    ring
  -- kernel
  have hker : RingHom.ker ψ = Ideal.span {algebraMap P₄ (Localization.AtPrime Q) (hPoly i)} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
      rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
      obtain ⟨m, hm⟩ := hz
      have hm0 : (m : chartRing i) ≠ 0 := fun h0 ↦ m.2 (h0 ▸ zero_mem _)
      have hr : r ∈ RingHom.ker φ := hdom hm0 hm
      rw [ker_chartHom, Ideal.mem_span_singleton] at hr
      obtain ⟨r', rfl⟩ := hr
      rw [Ideal.mem_span_singleton]
      exact ⟨IsLocalization.mk' _ r' t, (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change ψ (algebraMap P₄ _ (hPoly i)) = 0
      rw [Localization.localRingHom_to_map, hφh, map_zero]
  have hm : algebraMap P₄ (Localization.AtPrime Q) (hPoly i) ∈
      maximalIdeal (Localization.AtPrime Q) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    change φ (hPoly i) ∈ 𝔭
    rw [hφh]
    exact zero_mem _
  have hhQ : hPoly i ∈ Q := by
    change φ (hPoly i) ∈ 𝔭
    rw [hφh]
    exact zero_mem _
  have hcQ : (X 1 : P₄) ∉ Q := by
    change φ (X 1) ∉ 𝔭
    rw [chartHom_X_one]
    intro hmem
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit c_ne_zero).map _))
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, pderiv j.succ (hPoly i) ∉ Q := by
    by_contra h
    push Not at h
    obtain ⟨N, hN⟩ := pow_c_mem i Q h
    exact hcQ (Ideal.IsPrime.mem_of_pow_mem inferInstance N hN)
  exact SurfaceLib.isRegularLocalRing_of_surjective ψ hsurj hker hm
    (SurfaceLib.algebraMap_not_mem_maximalIdeal_sq Q (pderiv j.succ) hhQ hj)

/-- Every local ring of `X` is regular. -/
theorem x_stalk_regular (x : X19) : IsRegularLocalRing (X19.presheaf.stalk x) := by
  obtain ⟨i, p, rfl⟩ := atlas.chartInclusion_cover x
  have := @chart_localization_regular (i : Fin 5) p.asIdeal p.isPrime
  exact @IsRegularLocalRing.of_ringEquiv _ _ this _ _ (atlas.chartStalkEquiv i p).symm

end
end Geonormal

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Basic
import Red61.Foliation

/-! # The base field k = F₅(s₁, s₂) and its p-basis

Formerly the modules `Fields`, `PowersBasis`, `FieldTensor`, `FieldRelations`, `Independence`, `RationalCoefficientDifferentials`.
-/

namespace Red61.Fields

noncomputable section

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F₅ := ZMod 5
abbrev P₂ := MvPolynomial (Fin 2) F₅
abbrev k := FractionRing P₂
abbrev P₄ := PolynomialModel.P
abbrev K := FractionRing P₄

def c (i : Fin 2) : k := algebraMap P₂ k (MvPolynomial.X i)
def ell : Subfield k := (frobenius k 5).fieldRange

/-- This is the explicit abstract field isomorphism F₅(s₁,s₂) ≃ k⁵. -/
def baseEquiv : k ≃+* ell := (frobenius k 5).rangeRestrictFieldEquiv

theorem fifth_power_mem (x : k) : x ^ 5 ∈ ell :=
  (frobenius k 5).mem_fieldRange_self x

def includePoly : P₂ →+* P₄ :=
  (MvPolynomial.rename (fun i : Fin 2 => (⟨i, by omega⟩ : Fin 4))).toRingHom

theorem includePoly_injective : Function.Injective includePoly := by
  apply MvPolynomial.rename_injective
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 4 => z.val) h

def includeK : k →+* K := IsFractionRing.lift
  (g := (algebraMap P₄ K).comp includePoly)
  ((IsFractionRing.injective P₄ K).comp includePoly_injective)

@[simp] theorem includeK_poly (f : P₂) :
    includeK (algebraMap P₂ k f) = algebraMap P₄ K (includePoly f) := by
  exact IsFractionRing.lift_algebraMap _ f

def coord (i : Fin 4) : K := algebraMap P₄ K (MvPolynomial.X i)
abbrev c₁ : K := coord 0
abbrev c₂ : K := coord 1
abbrev t : K := coord 2
abbrev w : K := coord 3

def delta : Derivation F₅ K K := FractionDerivation.extend PolynomialModel.delta

@[simp] theorem delta_c₁ : delta c₁ = 1 := by simp [delta, coord]
@[simp] theorem delta_c₂ : delta c₂ = t := by simp [delta, coord]
@[simp] theorem delta_t : delta t = w := by simp [delta, coord]
@[simp] theorem delta_w : delta w = 0 := by simp [delta, coord]

theorem delta_fifth_zero : fifthDerivation delta = 0 := by
  apply FractionDerivation.ext (A := P₄)
  intro f
  simp [delta, PolynomialModel.delta_five]

theorem delta_five (x : K) : delta (delta (delta (delta (delta x)))) = 0 :=
  Derivation.congr_fun delta_fifth_zero x

theorem coord_nonzero (i : Fin 4) : coord i ≠ 0 := by
  apply (map_ne_zero_iff _ (IsFractionRing.injective P₄ K)).mpr
  exact MvPolynomial.X_ne_zero i

def ellEmbedding : ell →+* K := includeK.comp ell.subtype

instance : Algebra ell K := ellEmbedding.toAlgebra

theorem delta_ell (a : ell) : delta (algebraMap ell K a) = 0 := by
  obtain ⟨x, hx⟩ := a.property
  change delta (includeK (a : k)) = 0
  change x ^ 5 = (a : k) at hx
  rw [← hx, map_pow, Derivation.leibniz_pow, nsmul_eq_mul,
    CharP.cast_eq_zero K 5, zero_mul]

/-- The derivation with the correct base field: it does not fix k. -/
def ellDelta : Derivation ell K K where
  toFun := delta
  map_add' := map_add delta
  map_smul' a x := by simp [Algebra.smul_def, Derivation.leibniz, delta_ell, smul_eq_mul]
  map_one_eq_zero' := delta.map_one_eq_zero
  leibniz' := delta.leibniz

def L : Subfield K := constants ellDelta

def invariantBasis : Module.Basis (Fin 5) L K :=
  sliceBasis ellDelta c₁ delta_c₁ delta_five

theorem invariant_index : Module.finrank L K = 5 :=
  slice_finrank ellDelta c₁ delta_c₁ delta_five

end
end Red61.Fields

namespace Red61.Fields

open Module
noncomputable section

def coeffDeriv (i : Fin 2) : Derivation F₅ k k :=
  FractionDerivation.extend (MvPolynomial.pderiv i)

@[simp] theorem coeffDeriv_c (i j : Fin 2) : coeffDeriv i (c j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j; simp [coeffDeriv, c, MvPolynomial.pderiv_X]
  · simp [coeffDeriv, c, MvPolynomial.pderiv_X, hij]

theorem coeffDeriv_ell (i : Fin 2) (a : ell) : coeffDeriv i (a : k) = 0 := by
  obtain ⟨x, hx⟩ := a.property
  change x ^ 5 = (a : k) at hx
  rw [← hx, Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero k 5, zero_mul]

def pMonomial (ij : Fin 5 × Fin 5) : k := c 0 ^ (ij.1 : ℕ) * c 1 ^ (ij.2 : ℕ)

theorem pMonomials_independent : LinearIndependent ell pMonomial := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let b : Fin 5 → k := fun i => ∑ j : Fin 5, (a (i, j) : k) * c 1 ^ (j : ℕ)
  have hb (i : Fin 5) : coeffDeriv 0 (b i) = 0 := by
    simp [b, map_sum, Derivation.leibniz, Derivation.leibniz_pow,
      coeffDeriv_ell, smul_eq_mul]
  have hs : ∑ i : Fin 5, b i * c 0 ^ (i : ℕ) = 0 := by
    have cast_eq (z : ell) : algebraMap ell k z = (z : k) := rfl
    simpa [b, pMonomial, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
      Algebra.smul_def, cast_eq, mul_assoc, mul_left_comm, mul_comm] using ha
  have hbzero := slice_sum_unique (coeffDeriv 0) (c 0) (by simp) b hb hs
  intro ij
  have hz := slice_sum_unique (coeffDeriv 1) (c 1) (by simp)
    (fun j => (a (ij.1, j) : k)) (fun j => coeffDeriv_ell 1 _) (hbzero ij.1)
  exact Subtype.ext (hz ij.2)

def pSpan : Submodule ell k := Submodule.span ell (Set.range pMonomial)

theorem scalar_monomial_mem (x : k) (i j : Fin 5) : x ^ 5 * pMonomial (i,j) ∈ pSpan := by
  let a : ell := ⟨x ^ 5, fifth_power_mem x⟩
  exact pSpan.smul_mem a (Submodule.subset_span (Set.mem_range_self (i,j)))

theorem polynomial_monomial_mem (d : Fin 2 →₀ ℕ) (a : F₅) :
    algebraMap P₂ k (MvPolynomial.monomial d a) ∈ pSpan := by
  let i : Fin 5 := ⟨d 0 % 5, Nat.mod_lt _ (by decide)⟩
  let j : Fin 5 := ⟨d 1 % 5, Nat.mod_lt _ (by decide)⟩
  let x : k := algebraMap F₅ k a * c 0 ^ (d 0 / 5) * c 1 ^ (d 1 / 5)
  have hmem := scalar_monomial_mem x i j
  have ha : (algebraMap F₅ k a) ^ 5 = algebraMap F₅ k a := by
    rw [← map_pow]
    congr 1
    exact ZMod.pow_card a
  have hmono : algebraMap P₂ k (MvPolynomial.monomial d a) =
      algebraMap F₅ k a * c 0 ^ d 0 * c 1 ^ d 1 := by
    rw [MvPolynomial.monomial_eq]
    simp only [map_mul, 
      ]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_succ, c, mul_assoc]
      exact (IsScalarTower.algebraMap_apply F₅ P₂ k a).symm
    · simp
  rw [hmono]
  convert hmem using 1
  dsimp [x, pMonomial, i, j]
  rw [mul_pow, mul_pow, ha]
  rw [← pow_mul, ← pow_mul]
  have h0 : d 0 = d 0 / 5 * 5 + d 0 % 5 := by omega
  have h1 : d 1 = d 1 / 5 * 5 + d 1 % 5 := by omega
  conv_lhs => rw [h0, h1, pow_add, pow_add]
  ring

theorem polynomial_mem_pSpan (f : P₂) : algebraMap P₂ k f ∈ pSpan := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a => exact polynomial_monomial_mem d a
  | add f g hf hg => simpa using pSpan.add_mem hf hg

theorem pSpan_top : pSpan = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := P₂) x
  have hb' : algebraMap P₂ k b ≠ 0 := by
    simpa using (IsFractionRing.injective P₂ k).ne (by simpa using hb)
  let s : ell := ⟨(algebraMap P₂ k b)⁻¹ ^ 5, fifth_power_mem _⟩
  have h := pSpan.smul_mem s (polynomial_mem_pSpan (a * b ^ 4))
  convert h using 1
  change _ = (algebraMap P₂ k b)⁻¹ ^ 5 * algebraMap P₂ k (a * b ^ 4)
  simp only [map_mul, map_pow]
  field_simp

def pBasis : Basis (Fin 5 × Fin 5) ell k :=
  Basis.mk pMonomials_independent pSpan_top.ge

@[simp] theorem pBasis_apply (ij : Fin 5 × Fin 5) : pBasis ij = pMonomial ij := by
  exact Basis.mk_apply _ _ ij

theorem constant_extension_degree : Module.finrank ell k = 25 := by
  simpa using Module.finrank_eq_card_basis pBasis

theorem common_kernel {x : k} (h₀ : coeffDeriv 0 x = 0) (h₁ : coeffDeriv 1 x = 0) :
    x ∈ ell := by
  let a : Fin 5 × Fin 5 → ell := fun ij => pBasis.repr x ij
  let b : Fin 5 → k := fun i => ∑ j : Fin 5, (a (i,j) : k) * c 1 ^ (j : ℕ)
  have hb (i : Fin 5) : coeffDeriv 0 (b i) = 0 := by
    simp [b, map_sum, Derivation.leibniz, Derivation.leibniz_pow, coeffDeriv_ell, smul_eq_mul]
  have hsum : ∑ i : Fin 5, b i * c 0 ^ (i : ℕ) = x := by
    have cast_eq (z : ell) : algebraMap ell k z = (z : k) := rfl
    calc
      _ = ∑ ij : Fin 5 × Fin 5, a ij • pMonomial ij := by
        simp only [b, pMonomial, Fintype.sum_prod_type, Finset.sum_mul,
          Algebra.smul_def, cast_eq]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = x := by simpa only [pBasis_apply] using pBasis.sum_repr x
  have hb0 : b 0 = x := slice_constant_term (coeffDeriv 0) (c 0) (by simp) b hb x h₀ hsum
  have ha0 : (a (0,0) : k) = x :=
    slice_constant_term (coeffDeriv 1) (c 1) (by simp) (fun j => (a (0,j) : k))
      (fun j => coeffDeriv_ell 1 _) x h₁ hb0
  exact ha0 ▸ (a (0,0)).property

end
end Red61.Fields

namespace Red61.Fields

open scoped TensorProduct
noncomputable section

def ellToL : ell →+* L where
  toFun a := ⟨ellEmbedding a, delta_ell a⟩
  map_one' := Subtype.ext (map_one ellEmbedding)
  map_zero' := Subtype.ext (map_zero ellEmbedding)
  map_add' a b := Subtype.ext (map_add ellEmbedding a b)
  map_mul' a b := Subtype.ext (map_mul ellEmbedding a b)

instance : Algebra ell L := ellToL.toAlgebra

instance : IsScalarTower ell L K :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def includeKAlg : k →ₐ[ell] K where
  __ := includeK
  commutes' _ := rfl

def multiplication : L ⊗[ell] k →ₐ[L] K :=
  AlgHom.liftEquiv ell L k K includeKAlg

instance : Module.Finite ell k := Module.Finite.of_basis pBasis
instance : Module.Finite L K := Module.Finite.of_basis invariantBasis

instance : Nontrivial (L ⊗[ell] k) := multiplication.toRingHom.domain_nontrivial

instance : CharP (L ⊗[ell] k) 5 :=
  charP_of_injective_algebraMap (algebraMap L (L ⊗[ell] k)).injective 5

/-- A concrete algebraic certificate of failure of geometric reducedness.
All fields and embeddings here have been constructed, with no geometric input. -/
theorem baseChange_nonzero_nilpotent :
    ∃ z : L ⊗[ell] k, z ≠ 0 ∧ z ^ 5 = 0 := by
  apply tensor_nonzero_nilpotent (K := K) _ constant_extension_degree invariant_index multiplication
  intro b
  exact ⟨⟨b ^ 5, fifth_power_mem b⟩, rfl⟩

theorem baseChange_not_reduced : ¬ IsReduced (L ⊗[ell] k) := by
  intro h
  let := h
  obtain ⟨z, hz, hnil⟩ := baseChange_nonzero_nilpotent
  exact hz (IsNilpotent.eq_zero ⟨5, hnil⟩)

end
end Red61.Fields

namespace Red61.Fields

noncomputable section

instance : Algebra k K := includeK.toAlgebra

instance : IsScalarTower F₅ k K :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem includeK_c (i : Fin 2) :
    includeK (c i) = coord (⟨i, by omega⟩ : Fin 4) := by
  simp [c, includeK_poly, includePoly, coord]

/-- Chain rule along the explicitly chosen embedding k → K. -/
theorem derivation_on_k (E : Derivation F₅ K K) (x : k) :
    E (includeK x) = E c₁ * includeK (coeffDeriv 0 x) +
      E c₂ * includeK (coeffDeriv 1 x) := by
  let D₁ : Derivation F₅ k K := Derivation.compAlgebraMap k E
  let D₂ : Derivation F₅ k K :=
    E c₁ • (Algebra.linearMap k K).compDer (coeffDeriv 0) +
      E c₂ • (Algebra.linearMap k K).compDer (coeffDeriv 1)
  let : Algebra P₂ K := ((algebraMap k K).comp (algebraMap P₂ k)).toAlgebra
  let : IsScalarTower P₂ k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower F₅ P₂ K :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hpoly : D₁.compAlgebraMap (A := P₂) = D₂.compAlgebraMap (A := P₂) := by
    apply MvPolynomial.derivation_ext
    intro i
    change E (includeK (c i)) = _
    rw [includeK_c]
    fin_cases i <;>
      simp [D₂, Derivation.compAlgebraMap, LinearMap.compDer,
        Algebra.linearMap_apply, coeffDeriv, MvPolynomial.pderiv_X,
        smul_eq_mul, coord]
  have heq : D₁ = D₂ := by
    have hp (f : P₂) : D₁ (algebraMap P₂ k f) = D₂ (algebraMap P₂ k f) :=
      Derivation.congr_fun hpoly f
    apply Derivation.ext
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := P₂) y
    simp only [Derivation.leibniz_div]
    rw [hp a, hp b]
  exact Derivation.congr_fun heq x

theorem delta_on_k (x : k) :
    delta (includeK x) = includeK (coeffDeriv 0 x) + t * includeK (coeffDeriv 1 x) := by
  simpa using derivation_on_k delta x

def tDerivative : Derivation F₅ K K :=
  FractionDerivation.extend (MvPolynomial.pderiv (2 : Fin 4))

@[simp] theorem tDerivative_coord (i : Fin 4) :
    tDerivative (coord i) = if (2 : Fin 4) = i then 1 else 0 := by
  fin_cases i <;> simp [tDerivative, coord, MvPolynomial.pderiv_X]

theorem tDerivative_k (x : k) : tDerivative (includeK x) = 0 := by
  simp [derivation_on_k tDerivative, c₁, c₂]

/-- The independence of 1 and t over k needed for the constants argument. -/
theorem linear_t_coefficients {a b : k} (h : includeK a + t * includeK b = 0) :
    a = 0 ∧ b = 0 := by
  have hd := congrArg tDerivative h
  simp [Derivation.leibniz, tDerivative_k, t, smul_eq_mul] at hd
  have hb : b = 0 := includeK.injective (by simpa using hd)
  have ha : a = 0 := includeK.injective (by simpa [hb] using h)
  exact ⟨ha, hb⟩

theorem invariant_constant_partials {x : k} (h : includeK x ∈ L) :
    coeffDeriv 0 x = 0 ∧ coeffDeriv 1 x = 0 := by
  apply linear_t_coefficients
  rw [← delta_on_k]
  exact h

theorem invariant_constant_iff (x : k) : includeK x ∈ L ↔ x ∈ ell := by
  constructor
  · intro h
    obtain ⟨h₀, h₁⟩ := invariant_constant_partials h
    exact common_kernel h₀ h₁
  · intro hx
    exact delta_ell ⟨x, hx⟩

end
end Red61.Fields

namespace Red61.Fields

noncomputable section

instance : Algebra P₂ K := ((algebraMap k K).comp (algebraMap P₂ k)).toAlgebra

instance : IsScalarTower P₂ k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance : IsScalarTower F₅ P₂ K :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem coordinates_independent : AlgebraicIndependent F₅ coord :=
  (MvPolynomial.algebraicIndependent_X (Fin 4) F₅).map'
    (f := IsScalarTower.toAlgHom F₅ P₄ K) (IsFractionRing.injective P₄ K)

def surfaceCoordinates : Fin 2 → K := ![t, w]

def coefficientCoordinates (i : Fin 2) : K := includeK (c i)

theorem coefficientCoordinates_independent :
    AlgebraicIndependent F₅ coefficientCoordinates := by
  convert coordinates_independent.comp
    (fun i : Fin 2 => (⟨i, by omega⟩ : Fin 4)) (by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) h)) using 1
  ext i
  exact includeK_c i

theorem combinedCoordinates_independent :
    AlgebraicIndependent F₅ (Sum.elim surfaceCoordinates coefficientCoordinates) := by
  let e : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim
    (fun i => ⟨i.val + 2, by omega⟩) (fun i => ⟨i.val, by omega⟩)
  have he : Function.Injective e := by
    intro i j h
    cases i with
    | inl i => cases j with
      | inl j => congr 1; apply Fin.ext; have := congrArg Fin.val h; simpa [e] using this
      | inr j => have := congrArg Fin.val h; simp [e] at this; omega
    | inr i => cases j with
      | inl j => have := congrArg Fin.val h; simp [e] at this; omega
      | inr j => congr 1; apply Fin.ext; exact congrArg (fun x : Fin 4 => x.val) h
  convert coordinates_independent.comp e he using 1
  ext i
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => exact includeK_c i

theorem surfaceCoordinates_independent : AlgebraicIndependent k surfaceCoordinates := by
  have h := AlgebraicIndependent.sumElim_iff.mp combinedCoordinates_independent
  have hp : AlgebraicIndependent P₂ surfaceCoordinates := by
    apply h.2.of_ringHom_of_comp_eq coefficientCoordinates_independent.aevalEquiv
      (RingHom.id K) coefficientCoordinates_independent.aevalEquiv.injective
    apply RingHom.ext
    intro f
    change MvPolynomial.aeval coefficientCoordinates f = includeK (algebraMap P₂ k f)
    have he : (MvPolynomial.aeval coefficientCoordinates).toRingHom =
        includeK.comp (algebraMap P₂ k) := by
      ext i
      · exact RingHom.congr_fun (Subsingleton.elim _ _) i
      · simp [coefficientCoordinates, c]
    exact RingHom.congr_fun he f
  have : Algebra.IsAlgebraic P₂ k :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic k k)
  exact hp.extendScalars k

/-- Coordinates used at the contracted cone, ordered as U = w⁻¹ and T = t. -/
def coneCoordinates : Fin 2 → K := ![w⁻¹, t]

theorem coneCoordinates_independent : AlgebraicIndependent k coneCoordinates := by
  have ho : AlgebraicIndependent k (fun o : Option (Fin 1) => o.elim w (fun _ => t)) := by
    convert surfaceCoordinates_independent.comp
      (fun o : Option (Fin 1) => o.elim (1 : Fin 2) (fun _ => 0)) (by decide) using 1
    ext o
    cases o <;> rfl
  have hs := AlgebraicIndependent.option_iff.mp ho
  have hi : Transcendental (Algebra.adjoin k (Set.range (fun _ : Fin 1 => t))) w⁻¹ := by
    intro h
    exact hs.2 (IsAlgebraic.inv_iff.mp h)
  have hn : AlgebraicIndependent k
      (fun o : Option (Fin 1) => o.elim w⁻¹ (fun _ => t)) :=
    AlgebraicIndependent.option_iff.mpr ⟨hs.1, hi⟩
  convert hn.comp (fun i : Fin 2 => if i = 0 then none else some 0) (by decide) using 1
  ext i
  fin_cases i <;> rfl

/-- With the specified embedding of k, the whole field K is generated by t and w. -/
theorem rational_generation : IntermediateField.adjoin k {t, w} = ⊤ := by
  let M := IntermediateField.adjoin k ({t, w} : Set K)
  have hcoord (i : Fin 4) : coord i ∈ M := by
    fin_cases i
    · have h : includeK (c 0) ∈ M := M.algebraMap_mem (c 0)
      simpa [includeK_c] using h
    · have h : includeK (c 1) ∈ M := M.algebraMap_mem (c 1)
      simpa [includeK_c] using h
    · exact IntermediateField.subset_adjoin k _ (by simp)
    · exact IntermediateField.subset_adjoin k _ (by simp)
  have hpoly (p : P₄) : algebraMap P₄ K p ∈ M := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h : algebraMap P₄ K (MvPolynomial.C a) =
          algebraMap k K (algebraMap F₅ k a) := by
        rw [← IsScalarTower.algebraMap_apply F₅ k K]
        exact (IsScalarTower.algebraMap_apply F₅ P₄ K a).symm
      rw [h]
      exact M.algebraMap_mem _
    | add p q hp hq => simpa only [map_add] using M.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact M.mul_mem hp (hcoord i)
  apply top_unique
  intro x hx
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := P₄) x
  exact M.div_mem (hpoly a) (hpoly b)

end
end Red61.Fields

/-! Differentials of a rational coefficient field inside an arbitrary ring.
Only the chosen ring map is used; no compatibility with ell is imposed. -/

namespace Red61

open Fields
noncomputable section

theorem rationalCoefficient_derivation_mem
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M]
    (s : k →+* A) (D : Derivation R A M) (N : Submodule A M)
    (hvars : ∀ i : Fin 2, D (s (c i)) ∈ N) (a : k) : D (s a) ∈ N := by
  have hp (p : P₂) : D (s (algebraMap P₂ k p)) ∈ N := by
    induction p using MvPolynomial.induction_on with
    | C b =>
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective b
      simp
    | add p q hp hq => simpa only [map_add] using N.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul, Derivation.leibniz]
      exact N.add_mem (N.smul_mem _ (hvars i)) (N.smul_mem _ hp)
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := P₂) a
  by_cases hq : algebraMap P₂ k q = 0
  · simp [hq]
  rw [div_eq_mul_inv, map_mul, Derivation.leibniz]
  apply N.add_mem
  · apply N.smul_mem
    have he : s ((algebraMap P₂ k q)⁻¹) * s (algebraMap P₂ k q) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    rw [D.leibniz_of_mul_eq_one he]
    exact N.smul_mem _ (hp q)
  · exact N.smul_mem _ (hp p)

theorem rationalCoefficient_differential_mem
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (s : k →+* A) (N : Submodule A (KaehlerDifferential R A))
    (hvars : ∀ i : Fin 2, KaehlerDifferential.D R A (s (c i)) ∈ N) (a : k) :
    KaehlerDifferential.D R A (s a) ∈ N :=
  rationalCoefficient_derivation_mem s (KaehlerDifferential.D R A) N hvars a

end
end Red61

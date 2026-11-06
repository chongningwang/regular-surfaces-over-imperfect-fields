import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Red61.Surface.Quotient

/-! # The monomial projective model and properness

Formerly the modules `GlobalFunctions`, `MonomialProjectiveData`, `MonomialProjectiveAlgebra`, `MonomialProjectiveCover`, `MonomialProjectiveEvaluation`, `MonomialHomogeneousEvaluation`, `MonomialProjectiveChartRings`, `MonomialProjectiveOverlapRings`, `MonomialProjectiveComparison`, `ResolvedProjectivePolygon`, `ContractedFiniteness`, `ProjectivePolygon`, `ProjectiveAlgebra`, `ProjectiveComparison`, `ContractedProperness`.
-/

/-! Global functions of any proper integral ell-model of the concrete invariant field L. -/

namespace Red61.Fields

open CategoryTheory AlgebraicGeometry
noncomputable section

/-- For any given proper integral ell-scheme with function field L over ell,
the structure morphism identifies its global sections with ell. -/
def invariantGlobalSectionsEquiv {Y : Scheme} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of ell)) [IsProper f]
    (e : letI := functionFieldAlgebra ell f
      Y.functionField ≃ₐ[ell] L) :
    letI := (globalScalarMap ell f).toAlgebra
    ell ≃ₐ[ell] Γ(Y, ⊤) :=
  globalSectionsEquivOfFunctionField ell L f invariant_algebraic_constant e

@[simp] theorem invariantGlobalSectionsEquiv_apply {Y : Scheme} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of ell)) [IsProper f]
    (e : letI := functionFieldAlgebra ell f
      Y.functionField ≃ₐ[ell] L) (c : ell) :
    invariantGlobalSectionsEquiv f e c = globalScalarMap ell f c := rfl

theorem invariant_globalScalarMap_bijective {Y : Scheme} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of ell)) [IsProper f]
    (e : letI := functionFieldAlgebra ell f
      Y.functionField ≃ₐ[ell] L) :
    Function.Bijective (globalScalarMap ell f) := by
  let := (globalScalarMap ell f).toAlgebra
  exact (invariantGlobalSectionsEquiv f e).bijective

end
end Red61.Fields

/-! Finite algebraic data for identifying an affine monomial atlas with a
proper Proj. The hypotheses concern lattice points and coordinate subalgebras. -/

namespace Red61.MonomialProjectiveModel

open Fields Charts Fan AffineGluing
noncomputable section

structure Data (m n : ℕ) where
  point : Fin n → ℕ × ℕ
  ring : Fin m → Subalgebra k K
  localization : ∀ i j,
    letI := inclusionAlgebra (show ring i ≤ ring i ⊔ ring j from le_sup_left)
    ∃ d : ring i, IsLocalization.Away d ↥(ring i ⊔ ring j)
  vertexIndex : Fin m → Fin n
  ratio_adjoin : ∀ i, Algebra.adjoin k
    (Set.range (fun a ↦ monomial
      ((((point a).1 : ℤ), ((point a).2 : ℤ)) -
        (((point (vertexIndex i)).1 : ℤ), ((point (vertexIndex i)).2 : ℤ))))) = ring i
  vertexPower : Fin n → ℕ
  vertexMultiplicity : Fin n → Fin m → ℕ
  vertexPower_pos : ∀ a, 0 < vertexPower a
  vertexPower_sum : ∀ a, ∑ i, vertexMultiplicity a i = vertexPower a
  vertexPower_point : ∀ a,
    (vertexPower a : ℤ) • (((point a).1 : ℤ), ((point a).2 : ℤ)) =
      ∑ i, (vertexMultiplicity a i : ℤ) •
        (((point (vertexIndex i)).1 : ℤ), ((point (vertexIndex i)).2 : ℤ))

variable {m n : ℕ} (P : Data m n)

def atlas : PrincipalAtlas k K where
  Index := Fin m
  ring := P.ring
  localization := P.localization

def latticePoint (a : Fin n) : Lattice := ((P.point a).1, (P.point a).2)
def vertex (i : Fin m) : Lattice := latticePoint P (P.vertexIndex i)
def difference (i : Fin m) (a : Fin n) : Lattice := latticePoint P a - vertex P i

theorem ratio_mem (i : Fin m) (a : Fin n) : monomial (difference P i a) ∈ P.ring i := by
  rw [← P.ratio_adjoin i]
  exact Algebra.subset_adjoin (Set.mem_range_self a)

end
end Red61.MonomialProjectiveModel

/-! The finitely generated graded monoid algebra attached to the explicit polygon. -/

namespace Red61.MonomialProjectiveModel

open Fields AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} (P : Data m n)

def conePoint (a : Fin n) : ℕ × (ℕ × ℕ) := (1, P.point a)
def homogeneousMonoid : AddSubmonoid (ℕ × (ℕ × ℕ)) :=
  AddSubmonoid.closure (Set.range (conePoint P))

abbrev H := (homogeneousMonoid P)

def hGenerator (a : Fin n) : (H P) :=
  ⟨(conePoint P) a, AddSubmonoid.subset_closure (Set.mem_range_self a)⟩

def degree : (H P) →+ ℕ := (AddMonoidHom.fst ℕ (ℕ × ℕ)).comp (homogeneousMonoid P).subtype

theorem degree_zero (h : (H P)) (hh : (degree P) h = 0) : h = 0 := by
  apply Subtype.ext
  have aux (v : ℕ × (ℕ × ℕ)) (hv : v ∈ (homogeneousMonoid P)) : v.1 = 0 → v = 0 := by
    induction hv using AddSubmonoid.closure_induction with
    | mem v hv => obtain ⟨a,rfl⟩ := hv; simp [conePoint]
    | zero => simp
    | add a b ha hb iha ihb =>
      intro hab
      obtain ⟨ha0,hb0⟩ := Nat.add_eq_zero_iff.mp hab
      rw [iha ha0, ihb hb0, zero_add]
  exact aux h h.property hh

instance : AddMonoid.FG (H P) := by
  change AddMonoid.FG (AddSubmonoid.closure (Set.range (conePoint P)))
  infer_instance

abbrev homogeneousRing := AddMonoidAlgebra k (H P)
def grading (n : ℕ) : Submodule k (homogeneousRing P) := AddMonoidAlgebra.gradeBy k (degree P) n

instance : GradedAlgebra (grading P) := AddMonoidAlgebra.gradeBy.gradedAlgebra (degree P)

def generator (a : Fin n) : (homogeneousRing P) := AddMonoidAlgebra.single ((hGenerator P) a) 1

theorem generator_homogeneous (a : Fin n) : (generator P) a ∈ (grading P) 1 :=
  AddMonoidAlgebra.single_mem_gradeBy (degree P) ((hGenerator P) a) 1

theorem hGenerator_closure : AddSubmonoid.closure (Set.range (hGenerator P)) = ⊤ := by
  apply top_unique
  intro x _
  have aux (v : ℕ × (ℕ × ℕ)) (hv : v ∈ (homogeneousMonoid P)) :
      (⟨v,hv⟩ : (H P)) ∈ AddSubmonoid.closure (Set.range (hGenerator P)) := by
    induction hv using AddSubmonoid.closure_induction with
    | mem v hv =>
      obtain ⟨a,rfl⟩ := hv
      exact AddSubmonoid.subset_closure (Set.mem_range_self a)
    | zero => exact zero_mem _
    | add a b ha hb iha ihb => exact add_mem iha ihb
  exact aux x x.property

theorem generator_adjoin : Algebra.adjoin k (Set.range (generator P)) = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
    have hm : m ∈ AddSubmonoid.closure (Set.range (hGenerator P)) := by rw [(hGenerator_closure P)]; trivial
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => obtain ⟨a,rfl⟩ := hm; exact Algebra.subset_adjoin (Set.mem_range_self a)
    | zero => exact (Algebra.adjoin k (Set.range (generator P))).one_mem
    | add a b ha hb iha ihb =>
      simpa [AddMonoidAlgebra.of'_apply, AddMonoidAlgebra.single_mul_single] using
        (Algebra.adjoin k (Set.range (generator P))).mul_mem iha ihb
  | add a b ha hb => exact add_mem ha hb
  | smul r a ha => exact Subalgebra.smul_mem _ ha r

instance : Algebra.FiniteType k (homogeneousRing P) := inferInstance

/-- The (degree P)-zero part is precisely the coefficient field. -/
theorem zeroGrade_surjective : Function.Surjective (algebraMap k ((grading P) 0)) := by
  intro f
  refine ⟨f.val.coeff 0, Subtype.ext ?_⟩
  change AddMonoidAlgebra.single 0 (f.val.coeff 0) = f.val
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro h
  by_cases hh : h = 0
  · subst h; simp
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hh]
    symm
    by_contra hn
    exact hh ((degree_zero P) h (f.property h (Finsupp.mem_support_iff.mpr hn)))

def zeroGradeEquiv : k ≃ₐ[k] (grading P) 0 :=
  AlgEquiv.ofBijective (Algebra.ofId k ((grading P) 0))
    ⟨fun _ _ h ↦ (algebraMap k (homogeneousRing P)).injective (congrArg Subtype.val h),
      (zeroGrade_surjective P)⟩

instance : IsScalarTower k ((grading P) 0) (homogeneousRing P) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := (grading P) 0) (A := (homogeneousRing P)) (fun _ ↦ rfl)

instance : Algebra.FiniteType ((grading P) 0) (homogeneousRing P) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k ((grading P) 0) (homogeneousRing P)

def projectiveScheme : Scheme := Proj (grading P)

def projectiveToBase : (projectiveScheme P) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (grading P) ≫ Spec.map (CommRingCat.ofHom (R := k) (S := (grading P) 0)
    (algebraMap k ((grading P) 0)))

instance zeroGradeSpec_iso :
    IsIso (Spec.map (CommRingCat.ofHom (R := k) (S := (grading P) 0)
      (algebraMap k ((grading P) 0)))) := by
  change IsIso (Spec.map (CommRingCat.ofHom (R := k) (S := (grading P) 0)
    (zeroGradeEquiv P).toRingEquiv.toRingHom))
  have : IsIso (CommRingCat.ofHom (R := k) (S := (grading P) 0)
      (zeroGradeEquiv P).toRingEquiv.toRingHom) := by
    refine ⟨⟨CommRingCat.ofHom (R := (grading P) 0) (S := k)
      (zeroGradeEquiv P).symm.toRingEquiv.toRingHom, ?_, ?_⟩⟩ <;> ext x <;> simp
  infer_instance

/-- Properness of this Proj model follows from mathlib after checking finite generation.
The subsequent chart comparison identifies it with the specified atlas. -/
instance projectiveToBase_proper : IsProper (projectiveToBase P) := by
  unfold projectiveToBase
  infer_instance

end
end Red61.MonomialProjectiveModel

/-! Vertex standard opens cover the projective monoid scheme. -/

namespace Red61.MonomialProjectiveModel

open Fields AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} (P : Data m n)

theorem hGenerator_vertex_relation (a : Fin n) :
    P.vertexPower a • (hGenerator P) a =
      ∑ i : Fin m, P.vertexMultiplicity a i • (hGenerator P) (P.vertexIndex i) := by
  apply Subtype.ext
  have hp := P.vertexPower_point a
  have h₁ := congrArg Prod.fst hp
  have h₂ := congrArg Prod.snd hp
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h₁ h₂
  have hn₁ : P.vertexPower a * (P.point a).1 =
      ∑ i, P.vertexMultiplicity a i * (P.point (P.vertexIndex i)).1 := by exact_mod_cast h₁
  have hn₂ : P.vertexPower a * (P.point a).2 =
      ∑ i, P.vertexMultiplicity a i * (P.point (P.vertexIndex i)).2 := by exact_mod_cast h₂
  apply Prod.ext
  · simpa [hGenerator, conePoint, Prod.fst_sum] using (P.vertexPower_sum a).symm
  · apply Prod.ext
    · simpa [hGenerator, conePoint, Prod.fst_sum, Prod.snd_sum] using hn₁
    · simpa [hGenerator, conePoint, Prod.fst_sum, Prod.snd_sum] using hn₂

theorem generator_vertex_relation (a : Fin n) :
    (generator P) a ^ P.vertexPower a =
      ∏ i : Fin m, (generator P) (P.vertexIndex i) ^ P.vertexMultiplicity a i := by
  simp only [generator, AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.prod_single, Finset.prod_const_one, (hGenerator_vertex_relation P)]

theorem generator_adjoin_zeroGrade : Algebra.adjoin ((grading P) 0) (Set.range (generator P)) = ⊤ := by
  have h : Algebra.adjoin k (Set.range (generator P)) ≤
      (Algebra.adjoin ((grading P) 0) (Set.range (generator P))).restrictScalars k :=
    Algebra.adjoin_le Algebra.subset_adjoin
  apply top_unique
  intro x _
  apply h
  rw [(generator_adjoin P)]
  trivial

theorem generators_cover : ⨆ a, Proj.basicOpen (grading P) ((generator P) a) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (grading P) (generator P) (fun a ↦ ⟨1, (generator_homogeneous P) a⟩)
    (generator_adjoin_zeroGrade P)

/-- The integral convex-combination identities imply that the vertex opens cover. -/
theorem vertices_cover :
    ⨆ i : Fin m, Proj.basicOpen (grading P) ((generator P) (P.vertexIndex i)) = ⊤ := by
  apply top_unique
  rw [← (generators_cover P)]
  apply iSup_le
  intro a x hx
  have hsum : 0 < ∑ i, P.vertexMultiplicity a i := by
    rw [(P.vertexPower_sum a)]
    exact (P.vertexPower_pos a)
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change (generator P) (P.vertexIndex i) ∉ x.asHomogeneousIdeal
  intro hmem
  have hdiv : (generator P) (P.vertexIndex i) ∣ (generator P) a ^ P.vertexPower a := by
    rw [(generator_vertex_relation P)]
    exact (dvd_pow_self _ hi.ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hp : (generator P) a ^ P.vertexPower a ∈ x.asHomogeneousIdeal.toIdeal :=
    Ideal.mem_of_dvd _ hdiv hmem
  exact hx ((x.isPrime.pow_mem_iff_mem _ (P.vertexPower_pos a)).mp hp)

def vertexOpen (i : Fin m) :
    Spec (CommRingCat.of (HomogeneousLocalization.Away (grading P) ((generator P) (P.vertexIndex i)))) ⟶
      (projectiveScheme P) :=
  Proj.awayι (grading P) ((generator P) (P.vertexIndex i)) ((generator_homogeneous P) _) (by decide : 0 < 1)

instance vertexOpen_open (i : Fin m) : IsOpenImmersion ((vertexOpen P) i) := by
  unfold vertexOpen
  infer_instance

theorem vertexOpen_cover (x : (projectiveScheme P)) : ∃ i y, (vertexOpen P) i y = x := by
  have hx : x ∈ ⨆ i : Fin m, Proj.basicOpen (grading P) ((generator P) (P.vertexIndex i)) := by
    rw [(vertices_cover P)]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  rw [← Proj.opensRange_awayι (grading P) ((generator P) (P.vertexIndex i)) ((generator_homogeneous P) _)
    (by decide : 0 < 1)] at hi
  exact ⟨i,hi⟩

end
end Red61.MonomialProjectiveModel

/-! Evaluation of homogeneous monomials and injectivity in each (degree P). -/

namespace Red61.MonomialProjectiveModel

open Fields Charts
noncomputable section

variable {m n : ℕ} (P : Data m n)

def exponent : (H P) →+ (Fin 2 →₀ ℕ) where
  toFun h := Finsupp.single 0 h.val.2.1 + Finsupp.single 1 h.val.2.2
  map_zero' := by simp
  map_add' a b := by simp [Finsupp.single_add]; abel

def polynomialMap : (homogeneousRing P) →ₐ[k] MvPolynomial (Fin 2) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (exponent P)

def evaluate : (homogeneousRing P) →ₐ[k] K :=
  (MvPolynomial.aeval surfaceCoordinates).comp (polynomialMap P)

theorem exponent_injective_on_degree (n : ℕ) :
    Set.InjOn (exponent P) {h | (degree P) h = n} := by
  intro a ha b hb he
  apply Subtype.ext
  refine Prod.ext (ha.trans hb.symm) (Prod.ext ?_ ?_)
  · simpa [exponent] using congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) he
  · simpa [exponent] using congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) he

/-- Dropping the (degree P) coordinate is injective on a fixed homogeneous component. -/
theorem evaluate_injective_homogeneous {n : ℕ} {a b : (homogeneousRing P)}
    (ha : a ∈ (grading P) n) (hb : b ∈ (grading P) n) (he : (evaluate P) a = (evaluate P) b) : a = b := by
  have he' : (polynomialMap P) a = (polynomialMap P) b :=
    (algebraicIndependent_iff_injective_aeval.mp surfaceCoordinates_independent) he
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.mapDomain_injOn {h | (degree P) h = n} ((exponent_injective_on_degree P) n)
    ha hb (congrArg AddMonoidAlgebra.coeff he')

theorem evaluate_single (h : (H P)) (c : k) :
    (evaluate P) (AddMonoidAlgebra.single h c) =
      algebraMap k K c * t ^ h.val.2.1 * w ^ h.val.2.2 := by
  simp [evaluate, polynomialMap, exponent, MvPolynomial.single_eq_monomial,
    MvPolynomial.aeval_monomial,
    surfaceCoordinates, mul_assoc]

theorem evaluate_generator (a : Fin n) : (evaluate P) ((generator P) a) = monomial ((latticePoint P) a) := by
  rw [generator, (evaluate_single P)]
  simp [hGenerator, conePoint, monomial, latticePoint]

theorem evaluate_generator_nonzero (a : Fin n) : (evaluate P) ((generator P) a) ≠ 0 := by
  rw [(evaluate_generator P)]
  exact monomial_nonzero _

end
end Red61.MonomialProjectiveModel

/-! Evaluation of (degree P)-zero homogeneous localizations in the specified field K. -/

namespace Red61.MonomialProjectiveModel

open Fields Charts HomogeneousLocalization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {m n : ℕ} (P : Data m n)

abbrev awayRing (f : (homogeneousRing P)) := Away (grading P) f

def awayEvaluation (f : (homogeneousRing P)) (hf : (evaluate P) f ≠ 0) : (awayRing P) f →+* K :=
  (Localization.awayLift (evaluate P).toRingHom f (isUnit_iff_ne_zero.mpr hf)).comp
    (algebraMap ((awayRing P) f) (Localization.Away f))

theorem awayEvaluation_mk {f : (homogeneousRing P)} (hf : (evaluate P) f ≠ 0)
    {d : ℕ} (hd : f ∈ (grading P) d) (n : ℕ) (a : (homogeneousRing P)) (ha : a ∈ (grading P) (n • d)) :
    (awayEvaluation P) f hf (Away.mk (grading P) hd n a ha) = (evaluate P) a / (evaluate P) f ^ n := by
  change Localization.awayLift (evaluate P).toRingHom f (isUnit_iff_ne_zero.mpr hf)
    (Localization.mk a ⟨f ^ n, n, rfl⟩) = _
  simpa only [div_eq_mul_inv, inv_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    Localization.awayLift_mk (evaluate P).toRingHom f a ((evaluate P) f)⁻¹ (mul_inv_cancel₀ hf) n

theorem awayEvaluation_algebraMap (f : (homogeneousRing P)) (hf : (evaluate P) f ≠ 0) (c : k) :
    (awayEvaluation P) f hf (fromZeroRingHom (grading P) (Submonoid.powers f)
      (algebraMap k ((grading P) 0) c)) = algebraMap k K c := by
  change Localization.awayLift (evaluate P).toRingHom f (isUnit_iff_ne_zero.mpr hf)
    (Localization.mk (algebraMap k (homogeneousRing P) c) ⟨f ^ 0, 0, rfl⟩) = _
  simpa only [pow_zero, mul_one, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    (evaluate P).commutes] using Localization.awayLift_mk (evaluate P).toRingHom f (algebraMap k (homogeneousRing P) c)
    ((evaluate P) f)⁻¹ (mul_inv_cancel₀ hf) 0

def awayEvaluationRange (f : (homogeneousRing P)) (hf : (evaluate P) f ≠ 0) : Subalgebra k K where
  __ := RingHom.range (R := (awayRing P) f) ((awayEvaluation P) f hf)
  algebraMap_mem' c := ⟨_, (awayEvaluation_algebraMap P) f hf c⟩

theorem awayEvaluation_injective {f : (homogeneousRing P)} (hf : (evaluate P) f ≠ 0)
    {d : ℕ} (hd : f ∈ (grading P) d) : Function.Injective ((awayEvaluation P) f hf) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (grading P) hd x
  rw [(awayEvaluation_mk P)] at hx
  have he : a = 0 := (evaluate_injective_homogeneous P) ha (zero_mem _) (by
    rw [map_zero]
    exact (div_eq_zero_iff.mp hx).resolve_right (pow_ne_zero _ hf))
  subst a
  exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl

end
end Red61.MonomialProjectiveModel

/-! Homogeneous localization rings agree with the specified atlas coordinate rings. -/

namespace Red61.MonomialProjectiveModel

open Fields Charts HomogeneousLocalization
noncomputable section

variable {m n : ℕ} (P : Data m n)

abbrev vertexElement (i : Fin m) := (generator P) (P.vertexIndex i)
abbrev vertexRing (i : Fin m) := (awayRing P) ((vertexElement P) i)

def vertexEvaluation (i : Fin m) : (vertexRing P) i →+* K :=
  (awayEvaluation P) ((vertexElement P) i) ((evaluate_generator_nonzero P) _)

theorem evaluated_ratio (i : Fin m) (a : Fin n) :
    (evaluate P) ((generator P) a) / (evaluate P) ((vertexElement P) i) = monomial ((difference P) i a) := by
  rw [(evaluate_generator P), (evaluate_generator P)]
  simp only [difference, sub_eq_add_neg, monomial_mul, monomial_neg, div_eq_mul_inv, vertex]

theorem vertexEvaluation_product (i : Fin m) (q : ℕ) (c : Fin n → ℕ)
    (hn : ∑ a, c a = q) (ha : (∏ a, (generator P) a ^ c a) ∈ (grading P) (q • 1)) :
    (vertexEvaluation P) i (Away.mk (grading P) ((generator_homogeneous P) _) q _ ha) =
      ∏ a, monomial ((difference P) i a) ^ c a := by
  rw [vertexEvaluation, (awayEvaluation_mk P), map_prod]
  simp only [map_pow]
  calc
    _ = ∏ a, ((evaluate P) ((generator P) a) / (evaluate P) ((vertexElement P) i)) ^ c a := by
      simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hn]
    _ = _ := by simp only [(evaluated_ratio P)]

theorem vertexEvaluation_mem (i : Fin m) (x : (vertexRing P) i) : (vertexEvaluation P) i x ∈ P.ring i := by
  have hx : x ∈ Algebra.adjoin ((grading P) 0)
      {Away.mk (grading P) ((generator_homogeneous P) (P.vertexIndex i)) q (∏ a, (generator P) a ^ c a)
        (hc ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun a _ ↦ (generator_homogeneous P) a) |
        (q : ℕ) (c : Fin n → ℕ) (hc : ∑ a, c a • (1 : ℕ) = q • 1) (_ : ∀ a, c a ≤ 1)} := by
    rw [Away.adjoin_mk_prod_pow_eq_top ((generator_homogeneous P) _) (Fin n) (generator P)
      (generator_adjoin_zeroGrade P) (fun _ ↦ 1) (generator_homogeneous P)]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q,c,hc,_,rfl⟩ := hx
    rw [(vertexEvaluation_product P) i q c (by simpa using hc)]
    exact (P.ring i).prod_mem (fun a _ ↦ (P.ring i).pow_mem ((ratio_mem P) i a) _)
  | algebraMap c =>
    obtain ⟨r,rfl⟩ := (zeroGrade_surjective P) c
    change (awayEvaluation P) ((vertexElement P) i) ((evaluate_generator_nonzero P) _)
      (fromZeroRingHom (grading P) (Submonoid.powers ((vertexElement P) i))
        (algebraMap k ((grading P) 0) r)) ∈ P.ring i
    rw [(awayEvaluation_algebraMap P)]
    exact (P.ring i).algebraMap_mem _
  | add a b ha hb iha ihb => simpa using (P.ring i).add_mem iha ihb
  | mul a b ha hb iha ihb => simpa using (P.ring i).mul_mem iha ihb

theorem vertexEvaluation_range (i : Fin m) :
    (awayEvaluationRange P) ((vertexElement P) i) ((evaluate_generator_nonzero P) _) = P.ring i := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact (vertexEvaluation_mem P) i x
  · rw [← P.ratio_adjoin i]
    apply Algebra.adjoin_le
    rintro _ ⟨a,rfl⟩
    refine ⟨Away.mk (grading P) ((generator_homogeneous P) _) 1 ((generator P) a)
      ((generator_homogeneous P) a), ?_⟩
    rw [(awayEvaluation_mk P), pow_one, (evaluated_ratio P)]
    rfl

/-- The chart isomorphism is compatible with the specified embeddings into K. -/
def vertexEquiv (i : Fin m) : (vertexRing P) i ≃+* P.ring i :=
  RingEquiv.ofBijective (((vertexEvaluation P) i).codRestrict (P.ring i) ((vertexEvaluation_mem P) i))
    ⟨fun _ _ h ↦ (awayEvaluation_injective P) ((evaluate_generator_nonzero P) _)
      ((generator_homogeneous P) _) (congrArg Subtype.val h), fun y ↦ by
      have hy : (y : K) ∈ (awayEvaluationRange P) ((vertexElement P) i)
          ((evaluate_generator_nonzero P) _) := by rw [(vertexEvaluation_range P)]; exact y.property
      obtain ⟨x,hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem vertexEquiv_coe (i : Fin m) (x : (vertexRing P) i) :
    ((vertexEquiv P) i x : K) = (vertexEvaluation P) i x := rfl

end
end Red61.MonomialProjectiveModel

/-! Compatibility of the homogeneous chart rings on every pairwise overlap. -/

namespace Red61.MonomialProjectiveModel

open Fields Charts HomogeneousLocalization
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {m n : ℕ} (P : Data m n)

theorem awayEvaluation_awayMap {f g x : (homogeneousRing P)} {d e : ℕ}
    (hf : f ∈ (grading P) d) (hg : g ∈ (grading P) e) (hx : x = f * g)
    (hf0 : (evaluate P) f ≠ 0) (hx0 : (evaluate P) x ≠ 0) (a : (awayRing P) f) :
    (awayEvaluation P) x hx0 (awayMap (grading P) hg hx a) = (awayEvaluation P) f hf0 a := by
  have hg0 : (evaluate P) g ≠ 0 := by
    intro h
    apply hx0
    rw [hx, map_mul, h, mul_zero]
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective (grading P) hf a
  rw [awayMap_mk, (awayEvaluation_mk P), (awayEvaluation_mk P), hx, map_mul, map_mul, map_pow,
    mul_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero n hg0)

abbrev pairElement (i j : Fin m) := (vertexElement P) i * (vertexElement P) j
abbrev pairRing (i j : Fin m) := (awayRing P) ((pairElement P) i j)

theorem pairElement_nonzero (i j : Fin m) : (evaluate P) ((pairElement P) i j) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero ((evaluate_generator_nonzero P) _) ((evaluate_generator_nonzero P) _)

def pairEvaluation (i j : Fin m) : (pairRing P) i j →+* K :=
  (awayEvaluation P) _ ((pairElement_nonzero P) i j)

def pairLeft (i j : Fin m) : (vertexRing P) i →+* (pairRing P) i j :=
  awayMap (grading P) ((generator_homogeneous P) (P.vertexIndex j)) rfl

def pairRight (i j : Fin m) : (vertexRing P) j →+* (pairRing P) i j :=
  awayMap (grading P) ((generator_homogeneous P) (P.vertexIndex i)) (mul_comm _ _)

@[simp] theorem pairEvaluation_left (i j : Fin m) (a : (vertexRing P) i) :
    (pairEvaluation P) i j ((pairLeft P) i j a) = (vertexEvaluation P) i a :=
  (awayEvaluation_awayMap P) ((generator_homogeneous P) _) ((generator_homogeneous P) _) rfl _ _ a

@[simp] theorem pairEvaluation_right (i j : Fin m) (a : (vertexRing P) j) :
    (pairEvaluation P) i j ((pairRight P) i j a) = (vertexEvaluation P) j a :=
  (awayEvaluation_awayMap P) ((generator_homogeneous P) _) ((generator_homogeneous P) _) (mul_comm _ _) _ _ a

theorem pairEvaluation_mem (i j : Fin m) (z : (pairRing P) i j) :
    (pairEvaluation P) i j z ∈ P.ring i ⊔ P.ring j := by
  let := ((pairLeft P) i j).toAlgebra
  let d : (vertexRing P) i := Away.isLocalizationElem
    ((generator_homogeneous P) (P.vertexIndex i)) ((generator_homogeneous P) (P.vertexIndex j))
  have : IsLocalization.Away d ((pairRing P) i j) :=
    Away.isLocalization_mul ((generator_homogeneous P) _) ((generator_homogeneous P) _) rfl (by decide)
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj d z
  have he := congrArg ((pairEvaluation P) i j) ha
  change (pairEvaluation P) i j (z * (pairLeft P) i j d ^ n) = (pairEvaluation P) i j ((pairLeft P) i j a) at he
  rw [map_mul] at he
  have hp : (pairEvaluation P) i j ((pairLeft P) i j d ^ n) =
      (pairEvaluation P) i j ((pairLeft P) i j d) ^ n := ((pairEvaluation P) i j).map_pow _ n
  rw [hp, (pairEvaluation_left P), (pairEvaluation_left P)] at he
  have hd : (vertexEvaluation P) i d = (evaluate P) ((vertexElement P) j) / (evaluate P) ((vertexElement P) i) := by
    dsimp [d, Away.isLocalizationElem, vertexEvaluation]
    rw [(awayEvaluation_mk P), pow_one, pow_one]
  rw [hd] at he
  have hne : (evaluate P) ((vertexElement P) j) / (evaluate P) ((vertexElement P) i) ≠ 0 :=
    div_ne_zero ((evaluate_generator_nonzero P) _) ((evaluate_generator_nonzero P) _)
  have hz : (pairEvaluation P) i j z = (vertexEvaluation P) i a *
      ((evaluate P) ((vertexElement P) i) / (evaluate P) ((vertexElement P) j)) ^ n := by
    calc
      _ = (vertexEvaluation P) i a /
          ((evaluate P) ((vertexElement P) j) / (evaluate P) ((vertexElement P) i)) ^ n :=
        (eq_div_iff (pow_ne_zero n hne)).mpr he
      _ = _ := by rw [div_eq_mul_inv, ← inv_pow, inv_div]
  rw [hz]
  apply (P.ring i ⊔ P.ring j).mul_mem
  · exact (show P.ring i ≤ P.ring i ⊔ P.ring j from le_sup_left) ((vertexEvaluation_mem P) i a)
  · apply (P.ring i ⊔ P.ring j).pow_mem
    rw [(evaluated_ratio P) j (P.vertexIndex i)]
    exact (show P.ring j ≤ P.ring i ⊔ P.ring j from le_sup_right) ((ratio_mem P) j (P.vertexIndex i))

theorem pairEvaluation_range (i j : Fin m) :
    (awayEvaluationRange P) ((pairElement P) i j) ((pairElement_nonzero P) i j) = P.ring i ⊔ P.ring j := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    exact (pairEvaluation_mem P) i j z
  · apply sup_le
    · intro x hx
      rw [← (vertexEvaluation_range P) i] at hx
      obtain ⟨a,rfl⟩ := hx
      exact ⟨(pairLeft P) i j a, (pairEvaluation_left P) i j a⟩
    · intro x hx
      rw [← (vertexEvaluation_range P) j] at hx
      obtain ⟨a,rfl⟩ := hx
      exact ⟨(pairRight P) i j a, (pairEvaluation_right P) i j a⟩

def pairEquiv (i j : Fin m) : (pairRing P) i j ≃+* ↥(P.ring i ⊔ P.ring j) :=
  RingEquiv.ofBijective (((pairEvaluation P) i j).codRestrict (P.ring i ⊔ P.ring j)
    ((pairEvaluation_mem P) i j))
    ⟨fun _ _ h ↦ (awayEvaluation_injective P) ((pairElement_nonzero P) i j)
      (SetLike.mul_mem_graded ((generator_homogeneous P) _) ((generator_homogeneous P) _))
      (congrArg Subtype.val h), fun y ↦ by
      have hy : (y : K) ∈ (awayEvaluationRange P) ((pairElement P) i j) ((pairElement_nonzero P) i j) := by
        rw [(pairEvaluation_range P)]; exact y.property
      obtain ⟨x,hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem pairEquiv_coe (i j : Fin m) (x : (pairRing P) i j) :
    ((pairEquiv P) i j x : K) = (pairEvaluation P) i j x := rfl

theorem pairEquiv_left (i j : Fin m) (x : (vertexRing P) i) :
    (pairEquiv P) i j ((pairLeft P) i j x) = Subalgebra.inclusion le_sup_left ((vertexEquiv P) i x) := by
  apply Subtype.ext
  exact (pairEvaluation_left P) i j x

theorem pairEquiv_right (i j : Fin m) (x : (vertexRing P) j) :
    (pairEquiv P) i j ((pairRight P) i j x) = Subalgebra.inclusion le_sup_right ((vertexEquiv P) j x) := by
  apply Subtype.ext
  exact (pairEvaluation_right P) i j x

end
end Red61.MonomialProjectiveModel

/-! Gluing homogeneous chart isomorphisms to identify Proj with the specified atlas. -/

namespace Red61.MonomialProjectiveModel

open Fields AffineGluing AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} (P : Data m n)

def vertexIso (i : Fin m) : (atlas P).chart i ≅ Spec (CommRingCat.of ((vertexRing P) i)) :=
  Scheme.Spec.mapIso ((vertexEquiv P) i).toCommRingCatIso.op

def pairIso (i j : Fin m) :
    (atlas P).overlap i j ≅ Spec (CommRingCat.of ((pairRing P) i j)) :=
  Scheme.Spec.mapIso ((pairEquiv P) i j).toCommRingCatIso.op

@[reassoc] theorem vertexIso_left (i j : Fin m) :
    (atlas P).left i j ≫ ((vertexIso P) i).hom =
      ((pairIso P) i j).hom ≫ Spec.map (CommRingCat.ofHom ((pairLeft P) i j)) := by
  change Spec.map (CommRingCat.ofHom (Subalgebra.inclusion le_sup_left).toRingHom) ≫
    Spec.map (CommRingCat.ofHom ((vertexEquiv P) i).toRingHom) =
    Spec.map (CommRingCat.ofHom ((pairEquiv P) i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((pairLeft P) i j))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact ((pairEquiv_left P) i j x).symm

@[reassoc] theorem vertexIso_right (i j : Fin m) :
    (atlas P).transition i j ≫ (atlas P).left j i ≫ ((vertexIso P) j).hom =
      ((pairIso P) i j).hom ≫ Spec.map (CommRingCat.ofHom ((pairRight P) i j)) := by
  change (atlas P).transition i j ≫ (atlas P).left j i ≫
    Spec.map (CommRingCat.ofHom ((vertexEquiv P) j).toRingHom) =
    Spec.map (CommRingCat.ofHom ((pairEquiv P) i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((pairRight P) i j))
  simp only [PrincipalAtlas.transition, PrincipalAtlas.left, specMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact ((pairEquiv_right P) i j x).symm

def pairOpen (i j : Fin m) : Spec (CommRingCat.of ((pairRing P) i j)) ⟶ (projectiveScheme P) :=
  Proj.awayι (grading P) ((pairElement P) i j)
    (SetLike.mul_mem_graded ((generator_homogeneous P) _) ((generator_homogeneous P) _))
    (by decide : 0 < 1 + 1)

@[reassoc] theorem pairLeft_open (i j : Fin m) :
    Spec.map (CommRingCat.ofHom ((pairLeft P) i j)) ≫ (vertexOpen P) i = (pairOpen P) i j :=
  Proj.SpecMap_awayMap_awayι (grading P) ((generator_homogeneous P) _) (by decide)
    ((generator_homogeneous P) _) rfl

@[reassoc] theorem pairRight_open (i j : Fin m) :
    Spec.map (CommRingCat.ofHom ((pairRight P) i j)) ≫ (vertexOpen P) j = (pairOpen P) i j :=
  Proj.SpecMap_awayMap_awayι (grading P) ((generator_homogeneous P) _) (by decide)
    ((generator_homogeneous P) _) (mul_comm _ _)

theorem comparison_compatible (i j : Fin m) :
    (atlas P).left i j ≫ ((vertexIso P) i).hom ≫ (vertexOpen P) i =
    (atlas P).transition i j ≫ (atlas P).left j i ≫
      ((vertexIso P) j).hom ≫ (vertexOpen P) j := by
  rw [(vertexIso_left_assoc P), (vertexIso_right_assoc P), (pairLeft_open P), (pairRight_open P)]

def toProjective : (atlas P).glued ⟶ (projectiveScheme P) :=
  Multicoequalizer.desc (atlas P).glueData.toGlueData.diagram _
    (fun i ↦ ((vertexIso P) i).hom ≫ (vertexOpen P) i) (fun ⟨i,j⟩ ↦ by
      change (atlas P).left i j ≫ (((vertexIso P) i).hom ≫ (vertexOpen P) i) =
        ((atlas P).transition i j ≫ (atlas P).left j i) ≫
          (((vertexIso P) j).hom ≫ (vertexOpen P) j)
      simpa only [Category.assoc] using (comparison_compatible P) i j)

@[simp, reassoc] theorem chartInclusion_toProjective (i : Fin m) :
    (atlas P).chartInclusion i ≫ (toProjective P) = ((vertexIso P) i).hom ≫ (vertexOpen P) i := by
  apply Multicoequalizer.π_desc

def vertexCover : (projectiveScheme P).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin m) (fun i ↦ Spec (CommRingCat.of ((vertexRing P) i)))
    (vertexOpen P) (vertexOpen_cover P)

def pairPullbackIso (i j : Fin m) :
    pullback ((vertexOpen P) i) ((vertexOpen P) j) ≅ Spec (CommRingCat.of ((pairRing P) i j)) :=
  Proj.pullbackAwayιIso (grading P) ((generator_homogeneous P) _) (by decide)
    ((generator_homogeneous P) _) (by decide) rfl

@[simp, reassoc] theorem pairPullbackIso_inv_fst (i j : Fin m) :
    ((pairPullbackIso P) i j).inv ≫ pullback.fst ((vertexOpen P) i) ((vertexOpen P) j) =
      Spec.map (CommRingCat.ofHom ((pairLeft P) i j)) :=
  Proj.pullbackAwayιIso_inv_fst (grading P) ((generator_homogeneous P) _) (by decide)
    ((generator_homogeneous P) _) (by decide) rfl

@[simp, reassoc] theorem pairPullbackIso_inv_snd (i j : Fin m) :
    ((pairPullbackIso P) i j).inv ≫ pullback.snd ((vertexOpen P) i) ((vertexOpen P) j) =
      Spec.map (CommRingCat.ofHom ((pairRight P) i j)) :=
  Proj.pullbackAwayιIso_inv_snd (grading P) ((generator_homogeneous P) _) (by decide)
    ((generator_homogeneous P) _) (by decide) rfl

@[reassoc] theorem inverse_left (i j : Fin m) :
    Spec.map (CommRingCat.ofHom ((pairLeft P) i j)) ≫ ((vertexIso P) i).inv =
      ((pairIso P) i j).inv ≫ (atlas P).left i j := by
  rw [← cancel_epi ((pairIso P) i j).hom, ← (vertexIso_left_assoc P)]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc] theorem inverse_right (i j : Fin m) :
    Spec.map (CommRingCat.ofHom ((pairRight P) i j)) ≫ ((vertexIso P) j).inv =
      ((pairIso P) i j).inv ≫ (atlas P).transition i j ≫ (atlas P).left j i := by
  rw [← cancel_epi ((pairIso P) i j).hom, ← (vertexIso_right_assoc P)]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

theorem inverse_compatible (i j : Fin m) :
    pullback.fst ((vertexOpen P) i) ((vertexOpen P) j) ≫
      ((vertexIso P) i).inv ≫ (atlas P).chartInclusion i =
    pullback.snd ((vertexOpen P) i) ((vertexOpen P) j) ≫
      ((vertexIso P) j).inv ≫ (atlas P).chartInclusion j := by
  rw [← cancel_epi ((pairPullbackIso P) i j).inv]
  rw [(pairPullbackIso_inv_fst_assoc P i j), (pairPullbackIso_inv_snd_assoc P i j),
    (inverse_left_assoc P i j), (inverse_right_assoc P i j)]
  exact congrArg (fun f ↦ ((pairIso P) i j).inv ≫ f)
    ((atlas P).glueData.glue_condition i j).symm

def fromProjective : (projectiveScheme P) ⟶ (atlas P).glued :=
  (vertexCover P).glueMorphisms (fun i ↦ ((vertexIso P) i).inv ≫ (atlas P).chartInclusion i)
    (inverse_compatible P)

@[simp, reassoc] theorem vertexOpen_fromProjective (i : Fin m) :
    (vertexOpen P) i ≫ (fromProjective P) = ((vertexIso P) i).inv ≫ (atlas P).chartInclusion i := by
  apply Scheme.Cover.ι_glueMorphisms

def projectiveIso : (atlas P).glued ≅ (projectiveScheme P) where
  hom := (toProjective P)
  inv := (fromProjective P)
  hom_inv_id := by
    apply (atlas P).glueData.openCover.hom_ext
    intro i
    change Fin m at i
    change (atlas P).chartInclusion i ≫ _ = (atlas P).chartInclusion i ≫ _
    simp only [(chartInclusion_toProjective_assoc P), (vertexOpen_fromProjective P),
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply (vertexCover P).hom_ext
    intro i
    change Fin m at i
    change (vertexOpen P) i ≫ _ = (vertexOpen P) i ≫ _
    simp only [(vertexOpen_fromProjective_assoc P), (chartInclusion_toProjective P),
      Iso.inv_hom_id_assoc, Category.comp_id]

theorem projectiveIso_over_base : (projectiveIso P).hom ≫ (projectiveToBase P) = ((atlas P).toBase) := by
  apply (atlas P).glueData.openCover.hom_ext
  intro i
  change (atlas P).chartInclusion i ≫ (toProjective P) ≫ (projectiveToBase P) =
    (atlas P).chartInclusion i ≫ (atlas P).toBase
  rw [(chartInclusion_toProjective_assoc P), PrincipalAtlas.chartInclusion_toBase]
  change Spec.map (CommRingCat.ofHom ((vertexEquiv P) i).toRingHom) ≫
    (vertexOpen P) i ≫ (projectiveToBase P) = (atlas P).chartToBase i
  simp only [projectiveToBase, vertexOpen, Proj.awayι_toSpecZero_assoc,
    PrincipalAtlas.chartToBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact (awayEvaluation_algebraMap P) _ _ c

end
end Red61.MonomialProjectiveModel

/-! A six-vertex polygon whose affine tangent monoids are exactly the six
resolved chart rings. Every certificate below is checked by the Lean kernel. -/

namespace Red61.ResolvedProjectiveModel

open Fields Charts Fan Contraction
noncomputable section

def point : Fin 10 → ℕ × ℕ := ![(0,0), (0,4), (1,4), (11,0), (4,3), (9,1), (1,0), (0,1), (0,3), (10,0)]

def latticePoint (a : Fin 10) : Lattice := ((point a).1, (point a).2)
def vertex (i : Fin 6) : Lattice := latticePoint (i.castAdd 4)
def difference (i : Fin 6) (a : Fin 10) : Lattice := latticePoint a - vertex i

def coefficients : Fin 6 → Fin 10 → Fin 2 → ℕ := ![![![0, 0], ![0, 4], ![1, 4], ![11, 0], ![4, 3], ![9, 1], ![1, 0], ![0, 1], ![0, 3], ![10, 0]], ![![0, 4], ![0, 0], ![1, 0], ![11, 4], ![4, 1], ![9, 3], ![1, 4], ![0, 3], ![0, 1], ![10, 4]], ![![13, 4], ![1, 0], ![0, 0], ![2, 4], ![0, 1], ![1, 3], ![12, 4], ![10, 3], ![4, 1], ![3, 4]], ![![11, 0], ![3, 4], ![2, 4], ![0, 0], ![1, 3], ![0, 1], ![10, 0], ![9, 1], ![5, 3], ![1, 0]], ![![23, 13], ![3, 1], ![1, 0], ![1, 2], ![0, 0], ![0, 1], ![21, 12], ![18, 10], ![8, 4], ![3, 3]], ![![23, 11], ![3, 3], ![1, 2], ![1, 0], ![0, 1], ![0, 0], ![21, 10], ![18, 9], ![8, 5], ![3, 1]]]

theorem ratio_certificate (i : Fin 6) (a : Fin 10) :
    difference i a = combination ![first i,second i] (coefficients i a) := by
  fin_cases i <;> fin_cases a <;>
    norm_num [difference, latticePoint, point, vertex, coefficients, first, second,
      combination, Fin.sum_univ_succ, Prod.ext_iff]

theorem ratio_mem (i : Fin 6) (a : Fin 10) : monomial (difference i a) ∈ chartRing i := by
  rw [ratio_certificate]
  apply combination_mem
  intro b
  fin_cases b
  · exact y₁_mem i
  · exact y₂_mem i

def generatorIndex : Fin 6 → Fin 2 → Fin 10 := ![![6, 7], ![2, 8], ![1, 4], ![9, 5], ![2, 5], ![3, 4]]

theorem generator_certificate (i : Fin 6) (a : Fin 2) :
    difference i (generatorIndex i a) = (![first i,second i] : Fin 2 → Lattice) a := by
  fin_cases i <;> fin_cases a <;>
    norm_num [difference, latticePoint, point, vertex, generatorIndex, first, second]

theorem ratio_adjoin (i : Fin 6) :
    Algebra.adjoin k (Set.range (fun a ↦ monomial (difference i a))) = chartRing i := by
  apply le_antisymm (Algebra.adjoin_le (by rintro _ ⟨a,rfl⟩; exact ratio_mem i a))
  apply Algebra.adjoin_le
  intro x hx
  have h (a : Fin 2) : monomial ((![first i,second i] : Fin 2 → Lattice) a)
      ∈ Algebra.adjoin k (Set.range (fun b ↦ monomial (difference i b))) := by
    rw [← generator_certificate]
    exact Algebra.subset_adjoin (Set.mem_range_self _)
  rcases hx with rfl | hx
  · exact h 0
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ h 1

def vertexPower : Fin 10 → ℕ := ![1, 1, 1, 1, 1, 1, 11, 4, 4, 11]
def vertexMultiplicity : Fin 10 → Fin 6 → ℕ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![10, 0, 0, 1, 0, 0], ![3, 1, 0, 0, 0, 0], ![1, 3, 0, 0, 0, 0], ![1, 0, 0, 10, 0, 0]]

theorem vertex_certificate (a : Fin 10) :
    0 < vertexPower a ∧ (∑ i, vertexMultiplicity a i) = vertexPower a ∧
      (vertexPower a : ℤ) • latticePoint a = combination vertex (vertexMultiplicity a) := by
  fin_cases a <;> norm_num [vertexPower, vertexMultiplicity, latticePoint, point, vertex,
    combination, Fin.sum_univ_succ, Prod.ext_iff]

def data : MonomialProjectiveModel.Data 6 10 where
  point := point
  ring := chartRing
  localization := every_pair_isLocalization
  vertexIndex i := i.castAdd 4
  ratio_adjoin := ratio_adjoin
  vertexPower := vertexPower
  vertexMultiplicity := vertexMultiplicity
  vertexPower_pos a := (vertex_certificate a).1
  vertexPower_sum a := (vertex_certificate a).2.1
  vertexPower_point a := (vertex_certificate a).2.2

end
end Red61.ResolvedProjectiveModel

/-! Separated finite type models, the finite quotient, and properness descent. -/

namespace Red61.Contraction

open Fields Charts AffineGluing FrobeniusDescent CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem original_chart_finiteType (i : Fin 6) : Algebra.FiniteType k (chartRing i) :=
  Algebra.FiniteType.equiv inferInstance (chartPolynomialEquiv i)

theorem contracted_chart_finiteType (i : Fin 4) : Algebra.FiniteType k (contractedAtlas.ring i) := by
  fin_cases i
  · exact original_chart_finiteType 0
  · exact original_chart_finiteType 3
  · exact original_chart_finiteType 5
  · exact Algebra.FiniteType.equiv inferInstance coneRingEquiv

theorem contracted_chart_finiteType_ell (i : Fin 4) :
    Algebra.FiniteType ell ((contractedAtlas.ring i).restrictScalars ell) := by
  change Algebra.FiniteType ell (contractedAtlas.ring i)
  exact Algebra.FiniteType.trans (S := k) inferInstance (contracted_chart_finiteType i)

theorem quotient_chart_finiteType (i : Fin 4) : Algebra.FiniteType ell (quotientAtlas.ring i) := by
  have := contracted_chart_finiteType_ell i
  exact fixed_finiteType L 5 field_fifth_power_invariant _

instance x_separated : IsSeparated xToBase := contractedAtlas.toBase_separated
instance s_separated : IsSeparated sToBase := quotientAtlas.toBase_separated

instance x_finiteType : LocallyOfFiniteType xToBase :=
  contractedAtlas.toBase_locallyOfFiniteType contracted_chart_finiteType

instance s_finiteType : LocallyOfFiniteType sToBase :=
  quotientAtlas.toBase_locallyOfFiniteType quotient_chart_finiteType

instance x_quasiCompact : QuasiCompact xToBase := by
  have : Finite contractedAtlas.Index := inferInstanceAs (Finite (Fin 4))
  exact contractedAtlas.toBase_quasiCompact

instance s_quasiCompact : QuasiCompact sToBase := by
  have : Finite quotientAtlas.Index := inferInstanceAs (Finite (Fin 4))
  exact quotientAtlas.toBase_quasiCompact

/-- Finiteness of the actual global quotient, beyond its already proved homeomorphism. -/
instance pi_finite : IsFinite pi :=
  AtlasDescent.quotientMap_finite contractedAtlas L 5 field_fifth_power_invariant
    contracted_chart_finiteType_ell

instance pi_surjective : Surjective pi := ⟨pi_bijective.2⟩

instance constantExtension_finite :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ell k))) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Properness of X over k suffices for properness of S over ell. All descent
hypotheses here are proved for the constructed schemes. -/
theorem s_proper_of_x_proper [IsProper xToBase] : IsProper sToBase := by
  have : UniversallyClosed (pi ≫ sToBase) := by
    rw [pi_over_ell]
    infer_instance
  have : UniversallyClosed sToBase := UniversallyClosed.of_comp_surjective pi sToBase
  exact ⟨⟩

end
end Red61.Contraction

/-! Finite lattice certificates for a degree-one monomial projective model of X. -/

namespace Red61.Contraction.ProjectiveModel

open Fields Charts Fan
noncomputable section

/-- Four vertices followed by the points needed to generate the affine charts. -/
def point : Fin 10 → ℕ × ℕ :=
  ![(0,0),(7,0),(5,1),(0,3),(1,0),(0,1),(6,0),(0,2),(1,2),(2,2)]

def latticePoint (a : Fin 10) : Lattice := ((point a).1, (point a).2)
def vertex (i : Fin 4) : Lattice := latticePoint (i.castAdd 6)
def difference (i : Fin 4) (a : Fin 10) : Lattice := latticePoint a - vertex i

def smoothCoefficients : Fin 3 → Fin 10 → Fin 2 → ℕ :=
  ![![![0,0], ![7,0], ![5,1], ![0,3], ![1,0], ![0,1], ![6,0], ![0,2], ![1,2], ![2,2]],
    ![![7,0], ![0,0], ![0,1], ![1,3], ![6,0], ![5,1], ![1,0], ![3,2], ![2,2], ![1,2]],
    ![![15,7], ![1,0], ![0,0], ![0,1], ![13,6], ![10,5], ![3,1], ![5,3], ![3,2], ![1,1]]]

def singularCoefficients : Fin 10 → Fin 4 → ℕ :=
  ![![3,0,0,0], ![0,0,1,1], ![0,0,0,1], ![0,0,0,0], ![2,1,0,0],
    ![2,0,0,0], ![0,0,3,0], ![1,0,0,0], ![0,1,0,0], ![0,0,1,0]]

theorem smooth_certificate (i : Fin 3) (a : Fin 10) :
    difference i.castSucc a =
      combination ![first (kept i), second (kept i)] (smoothCoefficients i a) := by
  fin_cases i <;> fin_cases a <;>
    norm_num [difference, vertex, latticePoint, point, combination, smoothCoefficients,
      kept, first, second, Fin.sum_univ_succ, Prod.ext_iff]

theorem singular_certificate (a : Fin 10) :
    difference 3 a = combination coneExponent (singularCoefficients a) := by
  fin_cases a <;> norm_num [difference, vertex, latticePoint, point, combination,
    singularCoefficients, coneExponent, Fin.sum_univ_succ, Prod.ext_iff]

theorem ratio_mem (i : Fin 4) (a : Fin 10) : monomial (difference i a) ∈ ring i := by
  rcases i.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
  · have he : ring j.castSucc = chartRing (kept j) := by fin_cases j <;> rfl
    rw [he, smooth_certificate]
    apply combination_mem
    intro b
    fin_cases b
    · exact y₁_mem _
    · exact y₂_mem _
  · change monomial (difference 3 a) ∈ coneRing
    rw [singular_certificate]
    exact combination_mem _ _ _ cone_generator_mem

/-- Each coordinate generator occurs as the ratio of two selected degree-one monomials. -/
def smoothGeneratorIndex : Fin 3 → Fin 2 → Fin 10 := ![![4,5], ![6,2], ![1,3]]
def singularGeneratorIndex : Fin 4 → Fin 10 := ![7,8,9,2]

theorem smooth_generator_certificate (i : Fin 3) (a : Fin 2) :
    difference i.castSucc (smoothGeneratorIndex i a) =
      (![first (kept i), second (kept i)] : Fin 2 → Lattice) a := by
  fin_cases i <;> fin_cases a <;>
    norm_num [difference, vertex, latticePoint, point, smoothGeneratorIndex, kept, first, second]

theorem singular_generator_certificate (a : Fin 4) :
    difference 3 (singularGeneratorIndex a) = coneExponent a := by
  fin_cases a <;> norm_num [difference, vertex, latticePoint, point,
    singularGeneratorIndex, coneExponent]

/-- The proposed Proj charts have exactly the existing coordinate subalgebras. -/
theorem ratio_adjoin (i : Fin 4) :
    Algebra.adjoin k (Set.range (fun a ↦ monomial (difference i a))) = ring i := by
  apply le_antisymm (Algebra.adjoin_le (by rintro _ ⟨a,rfl⟩; exact ratio_mem i a))
  rcases i.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
  · have he : ring j.castSucc = chartRing (kept j) := by fin_cases j <;> rfl
    rw [he]
    apply Algebra.adjoin_le
    intro x hx
    have h (a : Fin 2) : monomial ((![first (kept j),second (kept j)] : Fin 2 → Lattice) a)
        ∈ Algebra.adjoin k (Set.range (fun b ↦ monomial (difference j.castSucc b))) := by
      rw [← smooth_generator_certificate]
      exact Algebra.subset_adjoin (Set.mem_range_self _)
    rcases hx with rfl | hx
    · exact h 0
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ h 1
  · apply (coneRing_le_iff _).mpr
    intro a
    rw [← singular_generator_certificate]
    exact Algebra.subset_adjoin (Set.mem_range_self _)

/-- Multiples expressing each selected point as an integral combination of vertices. -/
def vertexPower : Fin 10 → ℕ := ![1,1,1,1,7,3,7,3,21,21]
def vertexMultiplicity : Fin 10 → Fin 4 → ℕ :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1], ![6,1,0,0],
    ![2,0,0,1], ![1,6,0,0], ![1,0,0,2], ![4,3,0,14], ![1,6,0,14]]

theorem vertex_certificate (a : Fin 10) :
    0 < vertexPower a ∧ (∑ i, vertexMultiplicity a i) = vertexPower a ∧
      (vertexPower a : ℤ) • latticePoint a = combination vertex (vertexMultiplicity a) := by
  fin_cases a <;> norm_num [vertexPower, vertexMultiplicity, latticePoint, point, vertex,
    combination, Fin.sum_univ_succ, Prod.ext_iff]

/-- The original four-chart polygon supplies the same general Proj construction
used for the six-chart resolved model. -/
def data : MonomialProjectiveModel.Data 4 10 where
  point := point
  ring := ring
  localization := all_pairs_localization
  vertexIndex i := i.castAdd 6
  ratio_adjoin := ratio_adjoin
  vertexPower := vertexPower
  vertexMultiplicity := vertexMultiplicity
  vertexPower_pos a := (vertex_certificate a).1
  vertexPower_sum a := (vertex_certificate a).2.1
  vertexPower_point a := (vertex_certificate a).2.2

end
end Red61.Contraction.ProjectiveModel

/-! The four-chart specialization of the shared monomial Proj construction. -/

namespace Red61.Contraction.ProjectiveModel

open AlgebraicGeometry CategoryTheory
noncomputable section

abbrev conePoint := @MonomialProjectiveModel.conePoint 4 10 data

abbrev homogeneousMonoid := @MonomialProjectiveModel.homogeneousMonoid 4 10 data

abbrev H := @MonomialProjectiveModel.H 4 10 data

abbrev hGenerator := @MonomialProjectiveModel.hGenerator 4 10 data

abbrev degree := @MonomialProjectiveModel.degree 4 10 data

abbrev homogeneousRing := @MonomialProjectiveModel.homogeneousRing 4 10 data

abbrev grading := @MonomialProjectiveModel.grading 4 10 data

abbrev generator := @MonomialProjectiveModel.generator 4 10 data

abbrev zeroGradeEquiv := @MonomialProjectiveModel.zeroGradeEquiv 4 10 data

abbrev projectiveScheme := @MonomialProjectiveModel.projectiveScheme 4 10 data

abbrev projectiveToBase := @MonomialProjectiveModel.projectiveToBase 4 10 data

instance projectiveToBase_proper : IsProper projectiveToBase :=
  MonomialProjectiveModel.projectiveToBase_proper data

end
end Red61.Contraction.ProjectiveModel

/-! The four-chart specialization of the shared monomial Proj construction. -/

namespace Red61.Contraction.ProjectiveModel

open AlgebraicGeometry CategoryTheory
noncomputable section

abbrev vertexIso := @MonomialProjectiveModel.vertexIso 4 10 data

abbrev pairIso := @MonomialProjectiveModel.pairIso 4 10 data

abbrev pairOpen := @MonomialProjectiveModel.pairOpen 4 10 data

abbrev toProjective := @MonomialProjectiveModel.toProjective 4 10 data

abbrev vertexCover := @MonomialProjectiveModel.vertexCover 4 10 data

abbrev pairPullbackIso := @MonomialProjectiveModel.pairPullbackIso 4 10 data

abbrev fromProjective := @MonomialProjectiveModel.fromProjective 4 10 data

def projectiveIso : X ≅ projectiveScheme := MonomialProjectiveModel.projectiveIso data

theorem projectiveIso_over_base : projectiveIso.hom ≫ projectiveToBase = xToBase :=
  MonomialProjectiveModel.projectiveIso_over_base data

end
end Red61.Contraction.ProjectiveModel

/-! Properness and global functions for the actual four-chart quotient S. -/

namespace Red61.Contraction

open Fields AlgebraicGeometry CategoryTheory
noncomputable section

instance x_proper : IsProper xToBase := by
  rw [← ProjectiveModel.projectiveIso_over_base]
  infer_instance

instance s_proper : IsProper sToBase := s_proper_of_x_proper

/-- The structure morphism identifies the global functions of the constructed S with ell. -/
def sGlobalSectionsEquiv :
    letI := (globalScalarMap ell sToBase).toAlgebra
    ell ≃ₐ[ell] Γ(S, ⊤) :=
  invariantGlobalSectionsEquiv sToBase sFunctionFieldEquiv

@[simp] theorem sGlobalSectionsEquiv_apply (c : ell) :
    sGlobalSectionsEquiv c = globalScalarMap ell sToBase c := rfl

theorem s_globalScalarMap_bijective : Function.Bijective (globalScalarMap ell sToBase) :=
  invariant_globalScalarMap_bijective sToBase sFunctionFieldEquiv

end
end Red61.Contraction

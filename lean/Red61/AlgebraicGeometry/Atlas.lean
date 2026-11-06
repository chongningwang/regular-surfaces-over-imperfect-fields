import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic
import Red61.AlgebraicGeometry.Modules
import Red61.Foliation
import Red61.RingTheory.Valuation

/-! # Principal affine atlases, their gluing, function fields and regular neighbourhoods

Formerly the modules `AffineAlgebraIsoBase`, `AffineBasics`, `DimensionLowerBound`, `OpenRestriction`, `PrincipalAtlas`, `AtlasGeometry`, `AtlasMaps`, `AtlasDescent`, `AtlasOpenMap`, `AtlasSeparated`, `AtlasFinite`, `SchemeDimension`, `SmoothRegularNeighborhood`, `SmoothRegularPairNeighborhood`, `DifferentialRegularNeighborhood`, `RegularNeighborhoodFiniteness`, `AtlasFunctionField`, `AtlasStalkFields`, `AtlasDifferentialBasis`, `GenericFieldMap`, `AtlasFieldIndependence`, `FunctionFieldNaturality`, `AtlasFieldMaps`, `HomeomorphicDivisorPullback`.
-/

/-! An algebra isomorphism gives an affine scheme isomorphism over the
prescribed base algebra map. -/

namespace Red61
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {F R Q : Type} [CommRing F] [CommRing R] [CommRing Q]
  [Algebra F R] [Algebra F Q]

def affineAlgebraIso (e : Q ≃ₐ[F] R) :
    Spec (CommRingCat.of Q) ≅ Spec (CommRingCat.of R) :=
  Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op

theorem affineAlgebraIso_toBase (e : Q ≃ₐ[F] R) :
    (affineAlgebraIso e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F R)) =
      Spec.map (CommRingCat.ofHom (algebraMap F Q)) := by
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  exact e.symm.commutes c
end
end Red61

namespace Red61

open AlgebraicGeometry
noncomputable section

/-- Identify an affine scheme's function field with any given fraction field. -/
def affineFunctionFieldEquiv (R : CommRingCat) [IsDomain R]
    (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] :
    (Spec R).functionField ≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R)

/-- A domain and an injective localization have the same fraction field. -/
theorem fractionRing_of_localization
    (A B Q : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [CommRing Q]
    [Algebra A B] [Algebra A Q] [Algebra B Q] [IsScalarTower A B Q]
    (M : Submonoid A) [IsLocalization M B] [IsFractionRing B Q]
    (hinj : Function.Injective (algebraMap A B)) : IsFractionRing A Q := by
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors B) Q (fun _ hx ↦ hx.mem_nonZeroDivisors)
  convert h using 1
  ext x
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact (map_ne_zero_iff _ hinj).symm

end
end Red61

namespace Red61

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- A nonzero parameter and a second parameter outside its radical give a two-step prime chain. -/
theorem two_le_dimension (u r : R) (hu : u ≠ 0)
    (hrm : r ∈ IsLocalRing.maximalIdeal R)
    (hr : r ∉ (Ideal.span ({u} : Set R)).radical) : 2 ≤ ringKrullDim R := by
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf] at hr
  push Not at hr
  obtain ⟨p, hp, hpr⟩ := hr
  have hpp : Ideal.IsPrime p := hp.2
  have := hpp
  have hup : u ∈ p := hp.1 (Ideal.subset_span (by simp))
  have hbot : (⊥ : Ideal R) < p := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    exact hu (by simpa [h] using hup)
  have hmax : p < IsLocalRing.maximalIdeal R := by
    apply lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top)
    intro h
    exact hpr (h ▸ hrm)
  have h₁ : (1 : ℕ∞) ≤ Ideal.height p := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    exact (by simp : (1 : ℕ∞) ≤ (⊥ : Ideal R).height + 1).trans h
  have h₂ : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal R).height := by
    calc
      (2 : ℕ∞) = 1+1 := by norm_num
      _ ≤ Ideal.height p + 1 := by gcongr
      _ ≤ (IsLocalRing.maximalIdeal R).height := Ideal.height_add_one_le_of_lt_of_isPrime hmax
  exact (WithBot.coe_le_coe.mpr h₂).trans Ideal.height_le_ringKrullDim_of_isPrime

end Red61

/-! A morphism identified with the identity on a common open model restricts
to an isomorphism when the two open images are the specified complements. -/

namespace Red61

open AlgebraicGeometry CategoryTheory
noncomputable section

theorem isIso_restrict_of_common_open {Y Z W : Scheme} (f : Y ⟶ Z)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion a] [IsOpenImmersion b]
    (hab : a ≫ f = b) (U : Z.Opens)
    (ha : Set.range a = (f ⁻¹ᵁ U : Set Y)) (hb : Set.range b = (U : Set Z)) :
    IsIso (f ∣_ U) := by
  let ea : W ≅ (f ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.isoOfRangeEq a (f ⁻¹ᵁ U).ι (by simpa only [Scheme.Opens.range_ι] using ha)
  let eb : W ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq b U.ι (by simpa only [Scheme.Opens.range_ι] using hb)
  have hfa : ea.hom ≫ (f ⁻¹ᵁ U).ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hfb : eb.hom ≫ U.ι = b := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he : f ∣_ U = ea.inv ≫ eb.hom := by
    rw [← cancel_epi ea.hom, ← cancel_mono U.ι]
    simp only [Category.assoc, morphismRestrict_ι, ea.hom_inv_id_assoc]
    rw [← Category.assoc, hfa, hab, hfb]
  rw [he]
  infer_instance

end
end Red61

namespace Red61.AffineGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (k F : Type) [Field k] [Field F] [Algebra k F]

/-- A family of coordinate subalgebras with principal affine intersections. -/
structure PrincipalAtlas where
  Index : Type
  ring : Index → Subalgebra k F
  localization : ∀ i j,
    letI := inclusionAlgebra (show ring i ≤ ring i ⊔ ring j from le_sup_left)
    ∃ d : ring i, IsLocalization.Away d ↥(ring i ⊔ ring j)

namespace PrincipalAtlas

variable {k F} (D : PrincipalAtlas k F)

abbrev chart (i : D.Index) : Scheme := Spec (CommRingCat.of (D.ring i))
abbrev overlap (i j : D.Index) : Scheme := Spec (CommRingCat.of ↥(D.ring i ⊔ D.ring j))

def left (i j : D.Index) : D.overlap i j ⟶ D.chart i := specMap le_sup_left

instance left_open (i j : D.Index) : IsOpenImmersion (D.left i j) := by
  let := inclusionAlgebra (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
  obtain ⟨d,hd⟩ := D.localization i j
  let := hd
  exact IsOpenImmersion.of_isLocalization d

instance left_self_iso (i : D.Index) : IsIso (D.left i i) := by
  refine ⟨⟨specMap (sup_le le_rfl le_rfl), ?_, ?_⟩⟩ <;> simp [left]

def transition (i j : D.Index) : D.overlap i j ⟶ D.overlap j i :=
  specMap (le_of_eq (sup_comm _ _))

@[simp] theorem transition_self (i : D.Index) : D.transition i i = 𝟙 _ := by simp [transition]

def tripleRing (i j l : D.Index) : Subalgebra k F :=
  (D.ring i ⊔ D.ring j) ⊔ (D.ring i ⊔ D.ring l)

def tripleLeft (i j l : D.Index) :
    Spec (CommRingCat.of (D.tripleRing i j l)) ⟶ D.overlap i j := specMap le_sup_left

def tripleRight (i j l : D.Index) :
    Spec (CommRingCat.of (D.tripleRing i j l)) ⟶ D.overlap i l := specMap le_sup_right

theorem triple_isPullback (i j l : D.Index) :
    IsPullback (D.tripleLeft i j l) (D.tripleRight i j l) (D.left i j) (D.left i l) := by
  obtain ⟨d,hd⟩ := D.localization i j
  exact join_isPullback le_sup_left le_sup_left d hd

theorem rotate_le (i j l : D.Index) : D.tripleRing j l i ≤ D.tripleRing i j l := by
  dsimp [tripleRing]
  exact sup_le (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
    (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left))

def tripleTransition (i j l : D.Index) :
    pullback (D.left i j) (D.left i l) ⟶ pullback (D.left j l) (D.left j i) :=
  (D.triple_isPullback i j l).isoPullback.inv ≫ specMap (D.rotate_le i j l) ≫
    (D.triple_isPullback j l i).isoPullback.hom

theorem tripleTransition_fac (i j l : D.Index) :
    D.tripleTransition i j l ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ D.transition i j := by
  rw [← cancel_epi (D.triple_isPullback i j l).isoPullback.hom]
  simp [tripleTransition, tripleRight, tripleLeft, transition]

theorem tripleTransition_cocycle (i j l : D.Index) :
    D.tripleTransition i j l ≫ D.tripleTransition j l i ≫ D.tripleTransition l i j = 𝟙 _ := by
  rw [← cancel_epi (D.triple_isPullback i j l).isoPullback.hom]
  simp [tripleTransition, specMap_comp_assoc]

/-- The cocycle and all overlap hypotheses are proved from the ring-localization data. -/
def glueData : Scheme.GlueData where
  J := D.Index
  U := D.chart
  V := fun ij ↦ D.overlap ij.1 ij.2
  f := D.left
  f_id := D.left_self_iso
  t := D.transition
  t_id := D.transition_self
  t' := D.tripleTransition
  t_fac := D.tripleTransition_fac
  cocycle := D.tripleTransition_cocycle
  f_open := D.left_open

abbrev glued : Scheme := D.glueData.glued

abbrev chartInclusion (i : D.Index) : D.chart i ⟶ D.glued := D.glueData.ι i

instance chartInclusion_open (i : D.Index) : IsOpenImmersion (D.chartInclusion i) :=
  inferInstanceAs (IsOpenImmersion (D.glueData.ι i))

theorem chartInclusion_cover (x : D.glued) : ∃ i y, D.chartInclusion i y = x :=
  D.glueData.ι_jointly_surjective x

theorem overlap_isPullback (i j : D.Index) :
    IsPullback (D.left i j) (D.transition i j ≫ D.left j i)
      (D.chartInclusion i) (D.chartInclusion j) :=
  ⟨⟨D.glueData.glue_condition i j |>.symm⟩, ⟨D.glueData.vPullbackConeIsLimit i j⟩⟩

end PrincipalAtlas
end
end Red61.AffineGluing

namespace Red61.AffineGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k F : Type} [Field k] [Field F] [Algebra k F]

@[simp] theorem specMap_bot {A B : Subalgebra k F} (h : A ≤ B) :
    specMap h (⊥ : PrimeSpectrum B) = (⊥ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective _ (Subalgebra.inclusion_injective h)

namespace PrincipalAtlas

variable (D : PrincipalAtlas k F)

def chartToBase (i : D.Index) : D.chart i ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (D.ring i)))

theorem chartToBase_compatible (i j : D.Index) :
    D.left i j ≫ D.chartToBase i = D.transition i j ≫ D.left j i ≫ D.chartToBase j := by
  simp only [left, transition, chartToBase, specMap, ← Spec.map_comp]
  congr 1

def toBase : D.glued ⟶ Spec (CommRingCat.of k) :=
  Multicoequalizer.desc D.glueData.toGlueData.diagram _ D.chartToBase
    (fun ⟨i,j⟩ ↦ by
      change D.left i j ≫ D.chartToBase i = (D.transition i j ≫ D.left j i) ≫ D.chartToBase j
      rw [Category.assoc]
      exact D.chartToBase_compatible i j)

@[simp, reassoc] theorem chartInclusion_toBase (i : D.Index) :
    D.chartInclusion i ≫ D.toBase = D.chartToBase i := by
  apply Multicoequalizer.π_desc

theorem common_genericPoint (i j : D.Index) :
    D.chartInclusion i (⊥ : PrimeSpectrum (D.ring i)) =
      D.chartInclusion j (⊥ : PrimeSpectrum (D.ring j)) := by
  have h := congrArg (fun f : D.overlap i j ⟶ D.glued ↦
    f (⊥ : PrimeSpectrum ↥(D.ring i ⊔ D.ring j))) (D.glueData.glue_condition i j)
  change (D.transition i j ≫ D.left j i ≫ D.chartInclusion j) _ =
    (D.left i j ≫ D.chartInclusion i) _ at h
  simpa only [Scheme.Hom.comp_apply, transition, left, specMap_bot] using h.symm

theorem chart_genericPoint (i : D.Index) :
    IsGenericPoint (D.chartInclusion i (⊥ : PrimeSpectrum (D.ring i))) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro x
  refine ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ ?_⟩
  obtain ⟨j,y,rfl⟩ := D.chartInclusion_cover x
  rw [D.common_genericPoint i j]
  have h : (⊥ : PrimeSpectrum (D.ring j)) ⤳ y := by
    simpa only [genericPoint_eq_bot_of_affine] using
      (genericPoint_spec (Spec (CommRingCat.of (D.ring j)))).specializes (Set.mem_univ y)
  exact h.map (D.chartInclusion j).continuous

instance glued_irreducible [Nonempty D.Index] : IrreducibleSpace D.glued :=
  (irreducibleSpace_def _).mpr (D.chart_genericPoint (Classical.arbitrary D.Index)).isIrreducible

instance glued_reduced : IsReduced D.glued := by
  have : ∀ i : D.glueData.openCover.I₀, IsReduced (D.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (IsReduced (Spec (CommRingCat.of (D.ring i))))
  exact IsReduced.of_openCover _ D.glueData.openCover

instance glued_integral [Nonempty D.Index] : IsIntegral D.glued :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- A chart's generic stalk agrees with the generic stalk of the glued scheme. -/
def functionFieldChartEquiv [Nonempty D.Index] (i : D.Index) :
    D.glued.functionField ≃+* (D.chart i).functionField :=
  ((eqToIso (congrArg D.glued.presheaf.stalk
    (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)))).symm ≪≫
    asIso ((D.chartInclusion i).stalkMap (genericPoint (D.chart i)))).commRingCatIsoToRingEquiv

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Morphisms of affine atlases and refinements by inclusions in a common field. -/

namespace Red61.AffineGluing.PrincipalAtlas

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k F l G : Type} [Field k] [Field F] [Algebra k F]
  [Field l] [Field G] [Algebra l G]

structure MapData (D : PrincipalAtlas k F) (E : PrincipalAtlas l G) where
  index : D.Index → E.Index
  chart : ∀ i, D.chart i ⟶ E.chart (index i)
  overlap : ∀ i j, D.overlap i j ⟶ E.overlap (index i) (index j)
  left_comm : ∀ i j, D.left i j ≫ chart i = overlap i j ≫ E.left (index i) (index j)
  right_comm : ∀ i j, D.transition i j ≫ D.left j i ≫ chart j =
    overlap i j ≫ E.transition (index i) (index j) ≫ E.left (index j) (index i)

namespace MapData

variable {D : PrincipalAtlas k F} {E : PrincipalAtlas l G} (m : MapData D E)

theorem compatible (i j : D.Index) :
    D.left i j ≫ m.chart i ≫ E.chartInclusion (m.index i) =
      D.transition i j ≫ D.left j i ≫ m.chart j ≫ E.chartInclusion (m.index j) := by
  calc
    _ = m.overlap i j ≫ E.left (m.index i) (m.index j) ≫ E.chartInclusion (m.index i) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ E.chartInclusion (m.index i)) (m.left_comm i j)
    _ = m.overlap i j ≫ E.transition (m.index i) (m.index j) ≫
        E.left (m.index j) (m.index i) ≫ E.chartInclusion (m.index j) :=
      congrArg (fun f ↦ m.overlap i j ≫ f) (E.glueData.glue_condition _ _).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ E.chartInclusion (m.index j)) (m.right_comm i j).symm

def gluedMap : D.glued ⟶ E.glued :=
  Multicoequalizer.desc D.glueData.toGlueData.diagram _
    (fun i ↦ m.chart i ≫ E.chartInclusion (m.index i))
    (fun ⟨i,j⟩ ↦ by
      change D.left i j ≫ (m.chart i ≫ E.chartInclusion (m.index i)) =
        (D.transition i j ≫ D.left j i) ≫ (m.chart j ≫ E.chartInclusion (m.index j))
      simpa only [Category.assoc] using m.compatible i j)

@[simp, reassoc] theorem chartInclusion_gluedMap (i : D.Index) :
    D.chartInclusion i ≫ m.gluedMap = m.chart i ≫ E.chartInclusion (m.index i) := by
  apply Multicoequalizer.π_desc

end MapData

/-- The target chart rings inject into source chart rings inside one field. -/
def inclusionMapData (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) ≤ D.ring i) : MapData D E where
  index := f
  chart i := specMap (h i)
  overlap i j := specMap (sup_le ((h i).trans le_sup_left) ((h j).trans le_sup_right))
  left_comm _ _ := by simp [left]
  right_comm _ _ := by simp [transition, left]

theorem inclusionMapData_over_base (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) ≤ D.ring i) :
    (inclusionMapData D E f h).gluedMap ≫ E.toBase = D.toBase := by
  apply D.glueData.openCover.hom_ext
  intro i
  change D.chartInclusion i ≫ _ = D.chartInclusion i ≫ _
  simp only [MapData.chartInclusion_gluedMap_assoc, chartInclusion_toBase,
    inclusionMapData, chartToBase, specMap, ← Spec.map_comp]
  congr 1

end
end Red61.AffineGluing.PrincipalAtlas

/-! Invariant quotients of arbitrary principal atlases by Frobenius descent. -/

namespace Red61.AtlasDescent

open AffineGluing FrobeniusDescent CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R S F : Type} [Field R] [Field S] [Field F]
  [Algebra R S] [Algebra S F] [Algebra R F] [IsScalarTower R S F]
variable (D : PrincipalAtlas S F) (M : Subfield F) [Algebra R M] [IsScalarTower R M F]

def ring (i : D.Index) : Subalgebra R M := fixed M ((D.ring i).restrictScalars R)
def pair (i j : D.Index) : Subalgebra R M := fixed M ((D.ring i ⊔ D.ring j).restrictScalars R)

theorem restricted_le_pair (i j : D.Index) :
    (D.ring i).restrictScalars R ≤ (D.ring i ⊔ D.ring j).restrictScalars R :=
  fun _ hx ↦ (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left) hx

variable (p : ℕ) [Fact p.Prime] [CharP F p] (hp : ∀ x : F, x^p ∈ M)

include p hp in
theorem pair_eq_sup (i j : D.Index) : pair (R := R) D M i j = ring (R := R) D M i ⊔ ring (R := R) D M j := by
  obtain ⟨d,hd⟩ := D.localization i j
  let := inclusionAlgebra (show (D.ring i).restrictScalars R ≤
    (D.ring i).restrictScalars R ⊔ (D.ring j).restrictScalars R from le_sup_left)
  have hloc : IsLocalization.Away (show (D.ring i).restrictScalars R from d)
      ↥((D.ring i).restrictScalars R ⊔ (D.ring j).restrictScalars R) :=
    localization_congr (restricted_le_pair (R := R) D i j) le_sup_left
      (restrictScalars_sup (D.ring i) (D.ring j)) d hd
  change fixed M ((D.ring i ⊔ D.ring j).restrictScalars R) = _
  rw [restrictScalars_sup]
  exact fixed_sup M p hp _ _ d hloc

include p hp in
theorem pair_localization (i j : D.Index) :
    letI := inclusionAlgebra (show ring (R := R) D M i ≤ ring (R := R) D M i ⊔ ring (R := R) D M j from le_sup_left)
    ∃ d : ring (R := R) D M i, IsLocalization.Away d ↥(ring (R := R) D M i ⊔ ring (R := R) D M j) := by
  obtain ⟨d,hd⟩ := D.localization i j
  refine ⟨powerElement M p hp ((D.ring i).restrictScalars R) d, ?_⟩
  exact localization_congr (fixed_mono M (restricted_le_pair (R := R) D i j)) le_sup_left
    (pair_eq_sup (R := R) D M p hp i j) _
    (fixed_isLocalization M p hp (restricted_le_pair (R := R) D i j) d hd)

def atlas : PrincipalAtlas R M where
  Index := D.Index
  ring := ring (R := R) D M
  localization := pair_localization (R := R) D M p hp

def chartMap (i : D.Index) : D.chart i ⟶ (atlas (R := R) D M p hp).chart i :=
  Spec.map (CommRingCat.ofHom (FrobeniusDescent.embed M
    ((D.ring i).restrictScalars R)).toRingHom)

def overlapEmbedding (i j : D.Index) :
    ↥(ring (R := R) D M i ⊔ ring (R := R) D M j) →ₐ[R] (D.ring i ⊔ D.ring j).restrictScalars R :=
  (FrobeniusDescent.embed M _).comp
    (Subalgebra.inclusion (le_of_eq (pair_eq_sup (R := R) D M p hp i j).symm))

def overlapMap (i j : D.Index) : D.overlap i j ⟶ (atlas (R := R) D M p hp).overlap i j :=
  Spec.map (CommRingCat.ofHom (overlapEmbedding (R := R) D M p hp i j).toRingHom)

def mapData : PrincipalAtlas.MapData D (atlas (R := R) D M p hp) where
  index := id
  chart := chartMap (R := R) D M p hp
  overlap := overlapMap (R := R) D M p hp
  left_comm _ _ := by
    simp only [PrincipalAtlas.left, chartMap, overlapMap, specMap, ← Spec.map_comp]
    congr 1
  right_comm _ _ := by
    simp only [PrincipalAtlas.transition, PrincipalAtlas.left, chartMap, overlapMap,
      specMap, ← Spec.map_comp]
    congr 1

abbrev quotientMap : D.glued ⟶ (atlas (R := R) D M p hp).glued := (mapData (R := R) D M p hp).gluedMap

@[reassoc] theorem chartInclusion_quotientMap (i : D.Index) :
    D.chartInclusion i ≫ quotientMap (R := R) D M p hp =
      chartMap (R := R) D M p hp i ≫ (atlas (R := R) D M p hp).chartInclusion i :=
  (mapData (R := R) D M p hp).chartInclusion_gluedMap i

theorem quotientMap_over_base :
    quotientMap (R := R) D M p hp ≫ (atlas (R := R) D M p hp).toBase =
      D.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply D.glueData.openCover.hom_ext
  intro i
  change D.chartInclusion i ≫ _ = D.chartInclusion i ≫ _
  simp only [chartInclusion_quotientMap_assoc, PrincipalAtlas.chartInclusion_toBase,
    PrincipalAtlas.chartInclusion_toBase_assoc, chartMap, PrincipalAtlas.chartToBase,
    ← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R M F r).symm.trans
    (IsScalarTower.algebraMap_apply R S F r)

theorem chartMap_homeomorph (i : D.Index) : IsHomeomorph (chartMap (R := R) D M p hp i) := by
  apply PrimeSpectrum.isHomeomorph_comap
  · intro x
    exact ⟨p, Nat.Prime.pos Fact.out,
      powerElement M p hp ((D.ring i).restrictScalars R) x, rfl⟩
  · rw [(RingHom.injective_iff_ker_eq_bot _).mp ?_]
    · exact bot_le
    · intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : D.ring i ↦ (z : F)) h))

theorem overlapMap_homeomorph (i j : D.Index) : IsHomeomorph (overlapMap (R := R) D M p hp i j) := by
  apply PrimeSpectrum.isHomeomorph_comap
  · intro x
    refine ⟨p, Nat.Prime.pos Fact.out, ⟨powerMap M p hp (x : F), ?_⟩, rfl⟩
    change powerMap M p hp (x : F) ∈ ring (R := R) D M i ⊔ ring (R := R) D M j
    rw [← pair_eq_sup (R := R) D M p hp]
    exact (D.ring i ⊔ D.ring j).pow_mem x.property p
  · rw [(RingHom.injective_iff_ker_eq_bot _).mp ?_]
    · exact bot_le
    · intro x y h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(D.ring i ⊔ D.ring j) ↦ (z : F)) h))

theorem quotientMap_surjective : Function.Surjective (quotientMap (R := R) D M p hp) := by
  intro y
  obtain ⟨i,a,rfl⟩ := (atlas (R := R) D M p hp).chartInclusion_cover y
  obtain ⟨b,rfl⟩ := (chartMap_homeomorph (R := R) D M p hp i).surjective a
  exact ⟨D.chartInclusion i b, congrArg (fun f : D.chart i ⟶ _ ↦ f b)
    (chartInclusion_quotientMap (R := R) D M p hp i)⟩

theorem quotientMap_injective : Function.Injective (quotientMap (R := R) D M p hp) := by
  intro x y hxy
  obtain ⟨i,a,rfl⟩ := D.chartInclusion_cover x
  obtain ⟨j,b,rfl⟩ := D.chartInclusion_cover y
  have hq (l : D.Index) (c : D.chart l) :
      quotientMap (R := R) D M p hp (D.chartInclusion l c) =
        (atlas (R := R) D M p hp).chartInclusion l (chartMap (R := R) D M p hp l c) :=
    congrArg (fun f : D.chart l ⟶ _ ↦ f c) (chartInclusion_quotientMap (R := R) D M p hp l)
  rw [hq, hq] at hxy
  obtain ⟨z,hz₁,hz₂⟩ := ((atlas (R := R) D M p hp).glueData.ι_eq_iff i j _ _).mp hxy
  obtain ⟨v,rfl⟩ := (overlapMap_homeomorph (R := R) D M p hp i j).surjective z
  apply (D.glueData.ι_eq_iff i j a b).mpr
  refine ⟨v, ?_, ?_⟩
  · apply (chartMap_homeomorph (R := R) D M p hp i).injective
    exact (congrArg (fun f : D.overlap i j ⟶ _ ↦ f v)
      ((mapData (R := R) D M p hp).left_comm i j)).trans hz₁
  · apply (chartMap_homeomorph (R := R) D M p hp j).injective
    exact (congrArg (fun f : D.overlap i j ⟶ _ ↦ f v)
      ((mapData (R := R) D M p hp).right_comm i j)).trans hz₂

theorem chart_preimage (i : D.Index) :
    quotientMap (R := R) D M p hp ⁻¹ᵁ ((atlas (R := R) D M p hp).chartInclusion i).opensRange =
      (D.chartInclusion i).opensRange := by
  ext x
  change (∃ y, (atlas (R := R) D M p hp).chartInclusion i y = quotientMap (R := R) D M p hp x) ↔
    ∃ z, D.chartInclusion i z = x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,rfl⟩ := (chartMap_homeomorph (R := R) D M p hp i).surjective y
    exact ⟨z, quotientMap_injective (R := R) D M p hp
      ((congrArg (fun f : D.chart i ⟶ _ ↦ f z)
        (chartInclusion_quotientMap (R := R) D M p hp i)).trans hy)⟩
  · rintro ⟨z,rfl⟩
    exact ⟨chartMap (R := R) D M p hp i z, (congrArg (fun f : D.chart i ⟶ _ ↦ f z)
      (chartInclusion_quotientMap (R := R) D M p hp i)).symm⟩

theorem chart_isPullback (i : D.Index) :
    IsPullback (chartMap (R := R) D M p hp i) (D.chartInclusion i)
      ((atlas (R := R) D M p hp).chartInclusion i) (quotientMap (R := R) D M p hp) :=
  IsOpenImmersion.isPullback _ _ _ _
    (chartInclusion_quotientMap (R := R) D M p hp i) (chart_preimage (R := R) D M p hp i)

theorem quotientMap_homeomorph : IsHomeomorph (quotientMap (R := R) D M p hp) := by
  refine ⟨(quotientMap (R := R) D M p hp).continuous, ?_,
    quotientMap_injective (R := R) D M p hp, quotientMap_surjective (R := R) D M p hp⟩
  intro U hU
  apply ((atlas (R := R) D M p hp).glueData.isOpen_iff _).mpr
  intro i
  have he : (atlas (R := R) D M p hp).chartInclusion i ⁻¹'
      (quotientMap (R := R) D M p hp '' U) =
      chartMap (R := R) D M p hp i '' (D.chartInclusion i ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      obtain ⟨z,rfl⟩ := (chartMap_homeomorph (R := R) D M p hp i).surjective y
      have hz : D.chartInclusion i z = x := quotientMap_injective (R := R) D M p hp
        ((congrArg (fun f : D.chart i ⟶ _ ↦ f z)
          (chartInclusion_quotientMap (R := R) D M p hp i)).trans hxy.symm)
      refine ⟨z, ?_, rfl⟩
      change D.chartInclusion i z ∈ U
      rwa [hz]
    · rintro ⟨z,hz,rfl⟩
      exact ⟨D.chartInclusion i z, hz, congrArg (fun f : D.chart i ⟶ _ ↦ f z)
        (chartInclusion_quotientMap (R := R) D M p hp i)⟩
  change IsOpen ((atlas (R := R) D M p hp).chartInclusion i ⁻¹'
    (quotientMap (R := R) D M p hp '' U))
  rw [he]
  exact (chartMap_homeomorph (R := R) D M p hp i).isOpenMap _
    ((D.chartInclusion i).continuous.isOpen_preimage _ hU)

end
end Red61.AtlasDescent

/-! Atlas maps that identify their chart rings are open immersions. -/

namespace Red61.AffineGluing

open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k F l G : Type} [Field k] [Field F] [Algebra k F]
  [Field l] [Field G] [Algebra l G]

theorem specMap_isIso_of_eq {A B : Subalgebra k F} (h : A ≤ B) (he : A = B) :
    IsIso (specMap h) := by
  subst B
  simpa only [specMap_refl] using inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of A))))

namespace PrincipalAtlas
namespace MapData

variable {D : PrincipalAtlas k F} {E : PrincipalAtlas l G} (m : MapData D E)

theorem gluedMap_injective_of_overlap_surjective
    (hc : ∀ i, Function.Injective (m.chart i))
    (ho : ∀ i j, Function.Surjective (m.overlap i j)) :
    Function.Injective m.gluedMap := by
  intro x y hxy
  obtain ⟨i,p,rfl⟩ := D.chartInclusion_cover x
  obtain ⟨j,q,rfl⟩ := D.chartInclusion_cover y
  change (D.chartInclusion i ≫ m.gluedMap) p = (D.chartInclusion j ≫ m.gluedMap) q at hxy
  rw [m.chartInclusion_gluedMap, m.chartInclusion_gluedMap] at hxy
  obtain ⟨z,hzi,hzj⟩ := (E.glueData.ι_eq_iff (m.index i) (m.index j) _ _).mp hxy
  obtain ⟨w,rfl⟩ := ho i j z
  apply (D.glueData.ι_eq_iff i j p q).mpr
  refine ⟨w, hc i ?_, hc j ?_⟩
  · have h := congrArg (fun f : D.overlap i j ⟶ E.chart (m.index i) ↦ f w) (m.left_comm i j)
    exact h.trans hzi
  · have h := congrArg (fun f : D.overlap i j ⟶ E.chart (m.index j) ↦ f w) (m.right_comm i j)
    exact h.trans hzj

theorem gluedMap_open_of_overlap_surjective
    [hc : ∀ i, IsOpenImmersion (m.chart i)]
    (ho : ∀ i j, Function.Surjective (m.overlap i j)) : IsOpenImmersion m.gluedMap := by
  apply IsOpenImmersion.of_openCover_source m.gluedMap D.glueData.openCover
    (m.gluedMap_injective_of_overlap_surjective (fun i ↦ (m.chart i).isOpenEmbedding.injective) ho)
  intro i
  change IsOpenImmersion (D.chartInclusion i ≫ m.gluedMap)
  rw [m.chartInclusion_gluedMap]
  infer_instance

end MapData

def reindex (D : PrincipalAtlas k F) {I : Type} (f : I → D.Index) : PrincipalAtlas k F where
  Index := I
  ring i := D.ring (f i)
  localization i j := D.localization (f i) (f j)

def ringEqMapData (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) = D.ring i) : MapData D E :=
  inclusionMapData D E f (fun i ↦ (h i).le)

instance ringEqMapData_chart_isIso (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) = D.ring i) (i : D.Index) :
    IsIso ((ringEqMapData D E f h).chart i) :=
  specMap_isIso_of_eq _ (h i)

instance ringEqMapData_overlap_isIso (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) = D.ring i) (i j : D.Index) :
    IsIso ((ringEqMapData D E f h).overlap i j) :=
  specMap_isIso_of_eq _ (congrArg₂ (· ⊔ ·) (h i) (h j))

instance ringEqMapData_open (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) = D.ring i) :
    IsOpenImmersion (ringEqMapData D E f h).gluedMap :=
  (ringEqMapData D E f h).gluedMap_open_of_overlap_surjective
    (fun i j ↦ ((ringEqMapData D E f h).overlap i j).homeomorph.surjective)

theorem ringEqMapData_range (D E : PrincipalAtlas k F) (f : D.Index → E.Index)
    (h : ∀ i, E.ring (f i) = D.ring i) :
    Set.range (ringEqMapData D E f h).gluedMap =
      ⋃ i, Set.range (E.chartInclusion (f i)) := by
  let m := ringEqMapData D E f h
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨i,p,rfl⟩ := D.chartInclusion_cover x
    apply Set.mem_iUnion.mpr
    refine ⟨i, m.chart i p, ?_⟩
    exact (congrArg (fun g : D.chart i ⟶ E.glued ↦ g p) (m.chartInclusion_gluedMap i)).symm
  · intro hy
    obtain ⟨i,p,rfl⟩ := Set.mem_iUnion.mp hy
    obtain ⟨q,rfl⟩ := (m.chart i).homeomorph.surjective p
    refine ⟨D.chartInclusion i q, ?_⟩
    exact congrArg (fun g : D.chart i ⟶ E.glued ↦ g q) (m.chartInclusion_gluedMap i)

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Separatedness of an atlas whose intersections are joins of coordinate subalgebras. -/

namespace Red61.AffineGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme
open CategoryTheory.Limits.pullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The multiplication map onto the coordinate ring of an intersection. -/
def joinTensorMap (A B : Subalgebra k F) : A ⊗[k] B →ₐ[k] ↥(A ⊔ B) :=
  Algebra.TensorProduct.lift (Subalgebra.inclusion le_sup_left)
    (Subalgebra.inclusion le_sup_right) (fun _ _ ↦ .all _ _)

theorem joinTensorMap_surjective (A B : Subalgebra k F) :
    Function.Surjective (joinTensorMap A B) := by
  let f := joinTensorMap A B
  have h : A ⊔ B ≤ (f.range).map (A ⊔ B).val := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨f (⟨x,hx⟩ ⊗ₜ[k] 1), ⟨_, rfl⟩, by simp [f, joinTensorMap]⟩
    · intro x hx
      exact ⟨f (1 ⊗ₜ[k] ⟨x,hx⟩), ⟨_, rfl⟩, by simp [f, joinTensorMap]⟩
  intro x
  obtain ⟨y, ⟨z, rfl⟩, hz⟩ := h x.property
  exact ⟨z, Subtype.ext hz⟩

namespace PrincipalAtlas

variable (D : PrincipalAtlas k F)

/-- The diagonal is closed: on each pair of charts it is the spectrum of
the surjective tensor-product multiplication map onto their join. -/
instance toBase_separated : IsSeparated D.toBase := by
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Pullback.openCoverOfLeftRight
    D.glueData.openCover D.glueData.openCover _ _) ?_⟩
  intro ⟨i,j⟩
  dsimp [Scheme, Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  let e₁ : pullback (D.chartInclusion i ≫ D.toBase)
      (D.chartInclusion j ≫ D.toBase) ≅
      Spec (.of (D.ring i ⊗[k] D.ring j)) :=
    pullback.congrHom (D.chartInclusion_toBase i) (D.chartInclusion_toBase j) ≪≫
      pullbackSpecIso k (D.ring i) (D.ring j)
  let e₂ : pullback (D.chartInclusion i) (D.chartInclusion j) ≅ D.overlap i j :=
    (D.overlap_isPullback i j).isoPullback.symm
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e₁.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e₂.inv]
  convert! IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (joinTensorMap (D.ring i) (D.ring j)).toRingHom)
    (joinTensorMap_surjective _ _) using 1
  rw [← cancel_mono (pullbackSpecIso ..).inv]
  apply pullback.hom_ext
  · simp only [e₁, e₂, chartToBase, Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    erw [pullbackDiagonalMapIdIso_inv_snd_fst]
    erw [IsPullback.isoPullback_hom_fst]
    simp only [left, specMap]
    congr 1
    ext x : 2
    simp [joinTensorMap]
  · simp only [e₁, e₂, chartToBase, Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd,
      ← Spec.map_comp]
    erw [pullbackDiagonalMapIdIso_inv_snd_snd]
    erw [IsPullback.isoPullback_hom_snd]
    simp only [transition, left, specMap, ← Spec.map_comp]
    congr 1
    ext x : 2
    simp [joinTensorMap]

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Finite type principal atlases and their finite invariant quotient morphisms. -/

namespace Red61.AffineGluing.PrincipalAtlas

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k F : Type} [Field k] [Field F] [Algebra k F]
variable (D : PrincipalAtlas k F)

theorem toBase_locallyOfFiniteType (h : ∀ i, Algebra.FiniteType k (D.ring i)) :
    LocallyOfFiniteType D.toBase := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) D.glueData.openCover
  intro i
  change LocallyOfFiniteType (D.chartInclusion i ≫ D.toBase)
  rw [D.chartInclusion_toBase]
  rw [chartToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr (h i)

instance glued_compact [Finite D.Index] : CompactSpace D.glued := by
  have : Finite D.glueData.openCover.I₀ := inferInstanceAs (Finite D.Index)
  have : ∀ i : D.glueData.openCover.I₀, CompactSpace (D.glueData.openCover.X i) :=
    fun i ↦ inferInstanceAs (CompactSpace (D.chart i))
  exact D.glueData.openCover.compactSpace

instance toBase_quasiCompact [Finite D.Index] : QuasiCompact D.toBase :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr D.glued_compact

end
end Red61.AffineGluing.PrincipalAtlas

namespace Red61.AtlasDescent

open AffineGluing FrobeniusDescent CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R S F : Type} [Field R] [Field S] [Field F]
  [Algebra R S] [Algebra S F] [Algebra R F] [IsScalarTower R S F]
variable (D : PrincipalAtlas S F) (M : Subfield F) [Algebra R M] [IsScalarTower R M F]
variable (p : ℕ) [Fact p.Prime] [CharP F p] (hp : ∀ x : F, x^p ∈ M)

theorem chartMap_finite (i : D.Index)
    [Algebra.FiniteType R ((D.ring i).restrictScalars R)] :
    IsFinite (chartMap (R := R) D M p hp i) := by
  rw [chartMap, IsFinite.SpecMap_iff]
  exact embed_finite M p hp ((D.ring i).restrictScalars R)

/-- Finiteness is checked on the actual cartesian affine restrictions. -/
theorem quotientMap_finite
    (h : ∀ i, Algebra.FiniteType R ((D.ring i).restrictScalars R)) :
    IsFinite (quotientMap (R := R) D M p hp) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite)
    (atlas (R := R) D M p hp).glueData.openCover
  intro i
  change IsFinite (pullback.snd (quotientMap (R := R) D M p hp)
    ((atlas (R := R) D M p hp).chartInclusion i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (chart_isPullback (R := R) D M p hp i).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  have := h i
  exact chartMap_finite D M p hp i

end
end Red61.AtlasDescent

/-! Global scheme dimension and the dimensions of its local rings. -/

namespace Red61

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
noncomputable section

/-- The global dimension of a scheme is the supremum of its local dimensions. -/
theorem scheme_dimension_eq_iSup_stalk (Y : Scheme) :
    topologicalKrullDim Y = ⨆ y : Y, ringKrullDim (Y.presheaf.stalk y) := by
  rw [topologicalKrullDim,
    krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y)),
    krullDim_eq_iSup_coheight]
  simp only [ringKrullDim_stalk_eq_coheight]

theorem stalk_dimension_le_scheme (Y : Scheme) (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) ≤ topologicalKrullDim Y := by
  rw [scheme_dimension_eq_iSup_stalk]
  exact le_iSup (fun z : Y ↦ ringKrullDim (Y.presheaf.stalk z)) y

/-- A homeomorphism of scheme spaces preserves local dimension, without requiring
an isomorphism of the local rings. -/
theorem stalk_dimension_eq_of_homeomorph {Y Z : Scheme} (f : Y ⟶ Z)
    (hf : IsHomeomorph f) (y : Y) :
    ringKrullDim (Z.presheaf.stalk (f y)) = ringKrullDim (Y.presheaf.stalk y) := by
  let e : Y ≃o Z :=
    { (hf.homeomorph f).toEquiv with
      map_rel_iff' := hf.isInducing.specializes_iff }
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) (coheight_orderIso e y)

theorem stalk_dimension_le_of_affine_open {Y : Scheme} (R : CommRingCat)
    (f : Spec R ⟶ Y) [IsOpenImmersion f] (p : Spec R) :
    ringKrullDim (Y.presheaf.stalk (f p)) ≤ ringKrullDim R := by
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion f,
    ← idealHeight_eq_coheight R p]
  exact Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top

end
end Red61

/-! Every principal open of a smooth regular-pair quotient has a
smooth regular-pair presentation, by lifting its denominator to the
original ambient and using native localized quotient maps. -/

namespace Red61
open RingTheory.Sequence
noncomputable section
variable {F R Q : Type*} [CommRing F] [CommRing R] [CommRing Q]
  [Algebra F R] [Algebra F Q] [Algebra.Smooth F R]

theorem exists_smooth_regular_quotient_neighborhood (f : R →ₐ[F] Q)
    (hf : Function.Surjective f) (a b : R)
    (hk : RingHom.ker f = Ideal.ofList [a, b]) (hr : IsRegular R [a, b])
    (e : Q) [Nontrivial (Localization.Away e)] :
    ∃ c : R, ∃ g : Localization.Away c →ₐ[F] Localization.Away e,
      f c = e ∧ Algebra.Smooth F (Localization.Away c) ∧ Function.Surjective g ∧
      RingHom.ker g = Ideal.ofList
        [algebraMap R (Localization.Away c) a, algebraMap R (Localization.Away c) b] ∧
      IsRegular (Localization.Away c)
        [algebraMap R (Localization.Away c) a, algebraMap R (Localization.Away c) b] := by
  obtain ⟨c, rfl⟩ := hf e
  have : Algebra.Smooth R (Localization.Away c) := Algebra.Smooth.of_isLocalization_Away c
  refine ⟨c, Localization.awayMapₐ f c, rfl, Algebra.Smooth.comp F R _,
    localizedRegularQuotient_surjective f hf c, ?_, ?_⟩
  · exact localizedRegularQuotient_kernel f a b c hk
  · exact localizedRegularQuotient_regular f a b c hk hr
end
end Red61

/-! Explicit neighborhood data records an actual open immersion into
a scheme and a regular-pair quotient of a smooth algebra. Its native
closed immersion and smooth structural morphism commute with the base. -/

namespace Red61
open AlgebraicGeometry CategoryTheory RingTheory.Sequence
noncomputable section
variable (F : Type) [Field F] (X : Scheme) (b : X ⟶ Spec (CommRingCat.of F)) (x : X)

structure SmoothRegularPairNeighborhood where
  coordinateRing : Type
  [coordinateCommRing : CommRing coordinateRing]
  [coordinateAlgebra : Algebra F coordinateRing]
  ambientRing : Type
  [ambientCommRing : CommRing ambientRing]
  [ambientAlgebra : Algebra F ambientRing]
  openMap : Spec (CommRingCat.of coordinateRing) ⟶ X
  openImmersion : IsOpenImmersion openMap
  point_mem : x ∈ Set.range openMap
  base_comp : openMap ≫ b = Spec.map (CommRingCat.ofHom (algebraMap F coordinateRing))
  quotient : ambientRing →ₐ[F] coordinateRing
  quotient_surjective : Function.Surjective quotient
  left : ambientRing
  right : ambientRing
  kernel : RingHom.ker quotient = Ideal.ofList [left, right]
  regular : IsRegular ambientRing [left, right]
  smooth : Algebra.Smooth F ambientRing

namespace SmoothRegularPairNeighborhood
variable {F X b x} (P : SmoothRegularPairNeighborhood F X b x)
attribute [instance] coordinateCommRing coordinateAlgebra ambientCommRing ambientAlgebra

end SmoothRegularPairNeighborhood
end
end Red61

/-! Smooth regular-pair neighborhoods with an explicit ambient differential basis
have native conormal and cotangent bases. -/

namespace Red61
open AlgebraicGeometry CategoryTheory Module
noncomputable section
variable (n : ℕ) (F : Type) [Field F] (X : Scheme)
  (b : X ⟶ Spec (CommRingCat.of F)) (x : X)

structure DifferentialRegularPairNeighborhood extends SmoothRegularPairNeighborhood F X b x where
  ambientBasis : Basis (Fin n) ambientRing (KaehlerDifferential F ambientRing)

namespace DifferentialRegularPairNeighborhood
variable {n F X b x} (P : DifferentialRegularPairNeighborhood n F X b x)

def extension : Algebra.Extension F P.coordinateRing :=
  Algebra.Extension.ofSurjective P.quotient P.quotient_surjective

private local instance : Algebra P.ambientRing P.coordinateRing := P.quotient.toAlgebra
private local instance : IsScalarTower F P.ambientRing P.coordinateRing :=
  IsScalarTower.of_algHom P.quotient

end DifferentialRegularPairNeighborhood
end
end Red61

/-! Smooth regular-pair neighborhood algebras are finitely presented
and Noetherian over the prescribed field, for both the smooth ambient
and its actual surjective quotient. -/

namespace Red61.SmoothRegularPairNeighborhood
open AlgebraicGeometry
noncomputable section
variable {F : Type} [Field F] {X : Scheme} {b : X ⟶ Spec (CommRingCat.of F)} {x : X}
  (P : SmoothRegularPairNeighborhood F X b x)

theorem ambient_finitePresentation : Algebra.FinitePresentation F P.ambientRing :=
  P.smooth.finitePresentation

theorem ambient_finiteType : Algebra.FiniteType F P.ambientRing :=
  @Algebra.FiniteType.of_finitePresentation F P.ambientRing _ _ _ P.ambient_finitePresentation

theorem coordinate_finiteType : Algebra.FiniteType F P.coordinateRing := by
  have := P.ambient_finiteType
  exact Algebra.FiniteType.of_surjective P.quotient P.quotient_surjective

theorem coordinate_noetherian : IsNoetherianRing P.coordinateRing := by
  have := P.coordinate_finiteType
  exact Algebra.FiniteType.isNoetherianRing F P.coordinateRing

end
end Red61.SmoothRegularPairNeighborhood

/-! Compatibility of an atlas's function-field identification with its structure morphism. -/

namespace Red61.AffineGluing

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem topGerm_eqToHom (X : Scheme) {x y : X} (h : x = y) :
    X.presheaf.germ ⊤ x (by trivial) ≫ eqToHom (congrArg X.presheaf.stalk h) =
      X.presheaf.germ ⊤ y (by trivial) := by
  subst y
  simp

namespace PrincipalAtlas

variable {k F : Type} [Field k] [Field F] [Algebra k F]
variable (D : PrincipalAtlas k F) [Nonempty D.Index]

theorem functionFieldChartEquiv_germ (i : D.Index) :
    (CommRingCat.ofHom (globalGerm D.glued)) ≫ CommRingCat.ofHom (D.functionFieldChartEquiv i).toRingHom =
      (D.chartInclusion i).appTop ≫ (CommRingCat.ofHom (globalGerm (D.chart i))) := by
  change D.glued.presheaf.germ ⊤ (genericPoint D.glued) (by trivial) ≫
    (eqToHom (congrArg D.glued.presheaf.stalk
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)).symm) ≫
      (D.chartInclusion i).stalkMap (genericPoint (D.chart i))) = _
  rw [← Category.assoc, topGerm_eqToHom D.glued
    (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)).symm, Scheme.Hom.germ_stalkMap]
  rfl

theorem functionFieldChartEquiv_scalar (i : D.Index) :
    (D.functionFieldChartEquiv i).toRingHom.comp (functionFieldScalarMap k D.toBase) =
      functionFieldScalarMap k (D.chartToBase i) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ D.toBase.appTop ≫
    (CommRingCat.ofHom (globalGerm D.glued)) ≫
    CommRingCat.ofHom (D.functionFieldChartEquiv i).toRingHom).hom =
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (D.chartToBase i).appTop ≫
      (CommRingCat.ofHom (globalGerm (D.chart i)))).hom
  rw [D.functionFieldChartEquiv_germ, ← Category.assoc D.toBase.appTop,
    ← Scheme.Hom.comp_appTop, D.chartInclusion_toBase]

omit [Nonempty D.Index] in
/-- The affine scalar map is the specified algebra map to the affine fraction field. -/
theorem affineFunctionField_scalar (i : D.Index) [IsFractionRing (D.ring i) F] :
    (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F).toRingHom.comp
      (functionFieldScalarMap k (D.chartToBase i)) = algebraMap k F := by
  let : Algebra (D.ring i) (D.chart i).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (D.ring i))
  have : IsFractionRing (D.ring i) (D.chart i).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of (D.ring i))
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k (D.ring i)))
  have hs : functionFieldScalarMap k (D.chartToBase i) =
      (algebraMap (D.ring i) (D.chart i).functionField).comp (algebraMap k (D.ring i)) := by
    change (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k (D.ring i)))).appTop) ≫
      (CommRingCat.ofHom (globalGerm (D.chart i)))).hom = _
    rw [← hn]
    rfl
  rw [hs]
  ext c
  change affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F
    (algebraMap (D.ring i) (D.chart i).functionField (algebraMap k (D.ring i) c)) = _
  rw [affineFunctionFieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact (IsScalarTower.algebraMap_apply k (D.ring i) F c).symm

/-- The resulting isomorphism is over the base field with its structure-morphism scalars. -/
def functionFieldAlgEquiv (i : D.Index) [IsFractionRing (D.ring i) F] :
    letI := functionFieldAlgebra k D.toBase
    D.glued.functionField ≃ₐ[k] F := by
  letI := functionFieldAlgebra k D.toBase
  refine
    { (D.functionFieldChartEquiv i).trans
        (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F) with
      commutes' := ?_ }
  intro c
  have h := congrArg
    (fun f : k →+* (D.chart i).functionField ↦
      (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F).toRingHom.comp f)
    (D.functionFieldChartEquiv_scalar i)
  rw [D.affineFunctionField_scalar i] at h
  exact RingHom.congr_fun h c

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Compatibility of the actual atlas function-field isomorphisms with all
stalk embeddings, including the localization maps from chart rings. -/

namespace Red61.AffineGluing

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem stalkSpecializes_eqToHom (X : Scheme) {x y z : X} (h : x ⤳ z) (e : x = y) :
    X.presheaf.stalkSpecializes h ≫ eqToHom (congrArg X.presheaf.stalk e) =
      X.presheaf.stalkSpecializes (e ▸ h) := by
  subst y
  simp

theorem affineFunctionFieldEquiv_stalk (A : CommRingCat) [IsDomain A]
    (F : Type) [Field F] [Algebra A F] [IsFractionRing A F] (p : PrimeSpectrum A) :
    (affineFunctionFieldEquiv A F).toRingHom.comp
        (algebraMap ((Spec A).presheaf.stalk p) (Spec A).functionField) =
      (atPrimeEmbedding A F p).comp (Spec.stalkIso A p).hom.hom := by
  apply (RingHom.cancel_right
    (Spec.stalkIso A p).symm.commRingCatIsoToRingEquiv.surjective).mp
  apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
  ext a
  have h := Spec.algebraMap_stalkIso_inv (R := A) (x := p)
  have hs : (Spec.stalkIso A p).inv.hom.comp
      (algebraMap A (Localization.AtPrime p.asIdeal)) = (StructureSheaf.toStalk A p).hom := by
    exact congrArg CommRingCat.Hom.hom h
  change affineFunctionFieldEquiv A F
    (algebraMap ((Spec A).presheaf.stalk p) (Spec A).functionField
      ((Spec.stalkIso A p).inv (algebraMap A (Localization.AtPrime p.asIdeal) a))) = _
  have hsa := RingHom.congr_fun hs a
  change (Spec.stalkIso A p).inv (algebraMap A (Localization.AtPrime p.asIdeal) a) =
    (StructureSheaf.toStalk A p) a at hsa
  rw [hsa]
  change affineFunctionFieldEquiv A F
    (((StructureSheaf.toStalk A p) ≫ (Spec A).presheaf.stalkSpecializes
      ((genericPoint_spec (Spec A)).specializes trivial)) a) = _
  have ht : StructureSheaf.toStalk A p ≫ (Spec A).presheaf.stalkSpecializes
      ((genericPoint_spec (Spec A)).specializes trivial) =
      StructureSheaf.toStalk A (genericPoint (Spec A)) :=
    StructureSheaf.toStalk_stalkSpecializes _
  rw [ht]
  change affineFunctionFieldEquiv A F (algebraMap A (Spec A).functionField a) = _
  rw [affineFunctionFieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp

namespace PrincipalAtlas

variable {k F : Type} [Field k] [Field F] [Algebra k F]
variable (D : PrincipalAtlas k F) [Nonempty D.Index]

theorem functionFieldChartEquiv_stalk (i : D.Index) (p : D.chart i) :
    CommRingCat.ofHom (algebraMap (D.glued.presheaf.stalk (D.chartInclusion i p))
      D.glued.functionField) ≫ CommRingCat.ofHom (D.functionFieldChartEquiv i).toRingHom =
      (D.chartInclusion i).stalkMap p ≫
        CommRingCat.ofHom (algebraMap ((D.chart i).presheaf.stalk p) (D.chart i).functionField) := by
  change D.glued.presheaf.stalkSpecializes ((genericPoint_spec D.glued).specializes trivial) ≫
    (eqToHom (congrArg D.glued.presheaf.stalk
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)).symm) ≫
      (D.chartInclusion i).stalkMap (genericPoint (D.chart i))) = _
  rw [← Category.assoc, stalkSpecializes_eqToHom D.glued _
    (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)).symm]
  exact (D.chartInclusion i).stalkSpecializes_stalkMap _ _
    ((genericPoint_spec (D.chart i)).specializes trivial)

def chartStalkEquiv (i : D.Index) (p : PrimeSpectrum (D.ring i)) :
    D.glued.presheaf.stalk (D.chartInclusion i p) ≃+* Localization.AtPrime p.asIdeal :=
  (asIso ((D.chartInclusion i).stalkMap p)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso (CommRingCat.of (D.ring i)) p).commRingCatIsoToRingEquiv

theorem functionFieldEquiv_stalk (i : D.Index) [IsFractionRing (D.ring i) F]
    (p : PrimeSpectrum (D.ring i))
    (a : D.glued.presheaf.stalk (D.chartInclusion i p)) :
    affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F
      (D.functionFieldChartEquiv i
        (algebraMap (D.glued.presheaf.stalk (D.chartInclusion i p)) D.glued.functionField a)) =
      atPrimeEmbedding (D.ring i) F p (D.chartStalkEquiv i p a) := by
  have h := congrArg (fun f : D.glued.presheaf.stalk (D.chartInclusion i p) ⟶
      (D.chart i).functionField ↦ f a) (D.functionFieldChartEquiv_stalk i p)
  change D.functionFieldChartEquiv i
    (algebraMap (D.glued.presheaf.stalk (D.chartInclusion i p)) D.glued.functionField a) =
      algebraMap ((D.chart i).presheaf.stalk p) (D.chart i).functionField
        ((D.chartInclusion i).stalkMap p a) at h
  change affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F
    (D.functionFieldChartEquiv i
      (algebraMap (D.glued.presheaf.stalk (D.chartInclusion i p)) D.glued.functionField a)) = _
  rw [h]
  exact RingHom.congr_fun (affineFunctionFieldEquiv_stalk
    (CommRingCat.of (D.ring i)) F p) ((D.chartInclusion i).stalkMap p a)

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Local differential bases transferred from an actual affine atlas chart
to the corresponding scheme stalk. -/

namespace Red61.AffineGluing.PrincipalAtlas

open AlgebraicGeometry Module
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (D : PrincipalAtlas k F) [Nonempty D.Index]

def chartStalkDifferentialBasisOfLocalization (i : D.Index) (p : PrimeSpectrum (D.ring i))
    (b : Basis (Fin 4) (Localization.AtPrime p.asIdeal)
      (KaehlerDifferential ℤ (Localization.AtPrime p.asIdeal))) :
    Basis (Fin 4) (D.glued.presheaf.stalk (D.chartInclusion i p))
      (KaehlerDifferential ℤ (D.glued.presheaf.stalk (D.chartInclusion i p))) :=
  absoluteDifferentialBasisOfRingEquiv (D.chartStalkEquiv i p).symm b

end
end Red61.AffineGluing.PrincipalAtlas

/-! Functorial generic-stalk maps for morphisms carrying generic point to
generic point, with their compatibility with affine fraction-field maps. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem stalkMap_eqToHom {X Y : Scheme} (f : X ⟶ Y) {x y : X} (h : x = y) :
    f.stalkMap x ≫ eqToHom (congrArg X.presheaf.stalk h) =
      eqToHom (congrArg (fun z ↦ Y.presheaf.stalk (f z)) h) ≫ f.stalkMap y := by
  subst y
  simp

def genericFieldMap {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫ f.stalkMap (genericPoint X)).hom

theorem genericFieldMap_comp {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f (genericPoint X) = genericPoint Y)
    (hg : g (genericPoint Y) = genericPoint Z) :
    genericFieldMap (f ≫ g) ((congrArg g hf).trans hg) =
      (genericFieldMap f hf).comp (genericFieldMap g hg) := by
  apply CommRingCat.hom_ext_iff.mp
  change eqToHom _ ≫ (f ≫ g).stalkMap (genericPoint X) =
    (eqToHom _ ≫ g.stalkMap (genericPoint Y)) ≫
      (eqToHom _ ≫ f.stalkMap (genericPoint X))
  rw [Scheme.Hom.stalkMap_comp]
  rw [Category.assoc, ← Category.assoc (g.stalkMap _), stalkMap_eqToHom g hf.symm]
  simp only [← Category.assoc, eqToHom_trans]

theorem genericFieldMap_germ {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y) :
    CommRingCat.ofHom (globalGerm Y) ≫ CommRingCat.ofHom (genericFieldMap f hf) =
      f.appTop ≫ CommRingCat.ofHom (globalGerm X) := by
  change Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫
    (eqToHom _ ≫ f.stalkMap (genericPoint X)) = _
  rw [← Category.assoc, AffineGluing.topGerm_eqToHom Y hf.symm, Scheme.Hom.germ_stalkMap]
  rfl

theorem genericFieldMap_affine_algebraMap {A B : CommRingCat} [IsDomain A] [IsDomain B]
    (f : A ⟶ B) (hf : Spec.map f (genericPoint (Spec B)) = genericPoint (Spec A)) (a : A) :
    genericFieldMap (Spec.map f) hf (algebraMap A (Spec A).functionField a) =
      algebraMap B (Spec B).functionField (f a) := by
  have h := congrArg (fun g : A ⟶ (Spec B).functionField ↦ g a)
    (congrArg (fun g ↦ (Scheme.ΓSpecIso A).inv ≫ g)
      (genericFieldMap_germ (Spec.map f) hf))
  simp only [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality] at h
  exact h

theorem genericFieldMap_congr {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) (h : f = g)
    (hf : f (genericPoint X) = genericPoint Y)
    (hg : g (genericPoint X) = genericPoint Y) : genericFieldMap f hf = genericFieldMap g hg := by
  subst g
  rfl

end
end Red61

/-! Every chart of a principal atlas gives the same function-field
identification with the specified ambient field. -/

namespace Red61.AffineGluing

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem subalgebra_isFractionRing_of_le {A B : Subalgebra k F} (h : A ≤ B)
    [IsFractionRing A F] : IsFractionRing B F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,_,he⟩ := IsFractionRing.div_surjective A z
  exact ⟨Subalgebra.inclusion h a, Subalgebra.inclusion h b, he.symm⟩

theorem specMap_generic {A B : Subalgebra k F} (h : A ≤ B) :
    specMap h (genericPoint (Spec (CommRingCat.of B))) =
      genericPoint (Spec (CommRingCat.of A)) := by
  simpa only [genericPoint_eq_bot_of_affine] using specMap_bot h

theorem genericFieldMap_subalgebra {A B : Subalgebra k F} (h : A ≤ B)
    [IsFractionRing A F] [IsFractionRing B F] :
    (affineFunctionFieldEquiv (CommRingCat.of B) F).toRingHom.comp
      (genericFieldMap (specMap h) (specMap_generic h)) =
      (affineFunctionFieldEquiv (CommRingCat.of A) F).toRingHom := by
  let : Algebra A (Spec (CommRingCat.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)
  have : IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of A)
  let : Algebra B (Spec (CommRingCat.of B)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of B)
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  change affineFunctionFieldEquiv (CommRingCat.of B) F
    (genericFieldMap (specMap h) (specMap_generic h)
      (algebraMap A (Spec (CommRingCat.of A)).functionField a)) =
    affineFunctionFieldEquiv (CommRingCat.of A) F
      (algebraMap A (Spec (CommRingCat.of A)).functionField a)
  calc
    _ = affineFunctionFieldEquiv (CommRingCat.of B) F
        (algebraMap (CommRingCat.of B) (Spec (CommRingCat.of B)).functionField
          (Subalgebra.inclusion h a)) :=
      congrArg (affineFunctionFieldEquiv (CommRingCat.of B) F)
        (genericFieldMap_affine_algebraMap
          (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) (specMap_generic h) a)
    _ = _ := by
      simp only [affineFunctionFieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      rfl

namespace PrincipalAtlas

variable (D : PrincipalAtlas k F) [Nonempty D.Index]

theorem functionField_identification_independent (i j : D.Index)
    [IsFractionRing (D.ring i) F] [IsFractionRing (D.ring j) F] :
    (D.functionFieldChartEquiv i).trans (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F) =
      (D.functionFieldChartEquiv j).trans (affineFunctionFieldEquiv (CommRingCat.of (D.ring j)) F) := by
  have : IsFractionRing ↥(D.ring i ⊔ D.ring j) F :=
    subalgebra_isFractionRing_of_le (show D.ring i ≤ D.ring i ⊔ D.ring j from le_sup_left)
  let h₁ : D.ring i ≤ D.ring i ⊔ D.ring j := le_sup_left
  let h₂ : D.ring j ≤ D.ring i ⊔ D.ring j := le_sup_right
  have he : specMap h₁ ≫ D.chartInclusion i = specMap h₂ ≫ D.chartInclusion j := by
    have h := (D.glueData.glue_condition i j).symm
    change D.left i j ≫ D.chartInclusion i =
      D.transition i j ≫ D.left j i ≫ D.chartInclusion j at h
    simpa only [left, transition, ← Category.assoc, specMap_comp] using h
  have hmaps := genericFieldMap_congr _ _ he
    ((congrArg (D.chartInclusion i) (specMap_generic h₁)).trans
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)))
    ((congrArg (D.chartInclusion j) (specMap_generic h₂)).trans
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion j)))
  rw [genericFieldMap_comp (specMap h₁) (D.chartInclusion i) (specMap_generic h₁)
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)),
    genericFieldMap_comp (specMap h₂) (D.chartInclusion j) (specMap_generic h₂)
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion j))] at hmaps
  have hh := congrArg (fun g ↦
    (affineFunctionFieldEquiv (CommRingCat.of ↥(D.ring i ⊔ D.ring j)) F).toRingHom.comp g) hmaps
  rw [← RingHom.comp_assoc, genericFieldMap_subalgebra,
    ← RingHom.comp_assoc, genericFieldMap_subalgebra] at hh
  ext f
  exact RingHom.congr_fun hh f

end PrincipalAtlas
end
end Red61.AffineGluing

/-! Naturality of function-field pullback, including actual stalk maps and
specified homomorphisms between affine fraction fields. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem specMap_generic_of_injective {A B : CommRingCat} [IsDomain A] [IsDomain B]
    (f : A ⟶ B) (hf : Function.Injective f) :
    Spec.map f (genericPoint (Spec B)) = genericPoint (Spec A) := by
  simp only [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective f.hom hf

theorem genericFieldMap_stalk {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y) (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
      CommRingCat.ofHom (genericFieldMap f hf) =
      f.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
    (eqToHom (congrArg Y.presheaf.stalk hf.symm) ≫ f.stalkMap (genericPoint X)) = _
  rw [← Category.assoc, AffineGluing.stalkSpecializes_eqToHom Y _ hf.symm]
  exact f.stalkSpecializes_stalkMap _ _ ((genericPoint_spec X).specializes trivial)

theorem genericFieldMap_affine_compat {A B : CommRingCat} [IsDomain A] [IsDomain B]
    (F G : Type) [Field F] [Field G] [Algebra A F] [IsFractionRing A F]
    [Algebra B G] [IsFractionRing B G]
    (f : A ⟶ B) (hf : Spec.map f (genericPoint (Spec B)) = genericPoint (Spec A))
    (φ : F →+* G) (hφ : ∀ a : A, φ (algebraMap A F a) = algebraMap B G (f a)) :
    (affineFunctionFieldEquiv B G).toRingHom.comp (genericFieldMap (Spec.map f) hf) =
      φ.comp (affineFunctionFieldEquiv A F).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  change affineFunctionFieldEquiv B G
      (genericFieldMap (Spec.map f) hf (algebraMap A (Spec A).functionField a)) =
    φ (affineFunctionFieldEquiv A F (algebraMap A (Spec A).functionField a))
  rw [genericFieldMap_affine_algebraMap]
  simp only [affineFunctionFieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact (hφ a).symm

theorem genericPoint_morphism_of_chart {X Y U V : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral U] [IsIntegral V]
    (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]
    (g : U ⟶ V) (hg : g (genericPoint U) = genericPoint V) (h : a ≫ f = g ≫ b) :
    f (genericPoint X) = genericPoint Y := by
  calc
    f (genericPoint X) = f (a (genericPoint U)) :=
      congrArg f (genericPoint_eq_of_isOpenImmersion a).symm
    _ = b (g (genericPoint U)) := congrArg (fun q : U ⟶ Y ↦ q (genericPoint U)) h
    _ = genericPoint Y := (congrArg b hg).trans (genericPoint_eq_of_isOpenImmersion b)

end
end Red61

/-! A commuting affine chart square identifies the induced map of the actual
glued function fields with its prescribed ambient-field homomorphism. -/

namespace Red61.AffineGluing.PrincipalAtlas

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

variable {k F l G : Type} [Field k] [Field F] [Algebra k F]
  [Field l] [Field G] [Algebra l G]
variable (D : PrincipalAtlas k F) (E : PrincipalAtlas l G)
  [Nonempty D.Index] [Nonempty E.Index]

theorem functionFieldMap_compat (f : D.glued ⟶ E.glued)
    (hf : f (genericPoint D.glued) = genericPoint E.glued)
    (i : D.Index) (j : E.Index) [IsFractionRing (D.ring i) F] [IsFractionRing (E.ring j) G]
    (g : CommRingCat.of (E.ring j) ⟶ CommRingCat.of (D.ring i))
    (hg : Spec.map g (genericPoint (D.chart i)) = genericPoint (E.chart j))
    (hs : D.chartInclusion i ≫ f = Spec.map g ≫ E.chartInclusion j)
    (φ : G →+* F) (hφ : ∀ a : E.ring j, φ (a : G) = (g a : F)) :
    ((D.functionFieldChartEquiv i).trans
      (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F)).toRingHom.comp
        (genericFieldMap f hf) =
      φ.comp ((E.functionFieldChartEquiv j).trans
        (affineFunctionFieldEquiv (CommRingCat.of (E.ring j)) G)).toRingHom := by
  have hmaps := genericFieldMap_congr _ _ hs
    ((congrArg f (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i))).trans hf)
    ((congrArg (E.chartInclusion j) hg).trans
      (genericPoint_eq_of_isOpenImmersion (E.chartInclusion j)))
  rw [genericFieldMap_comp (D.chartInclusion i) f
      (genericPoint_eq_of_isOpenImmersion (D.chartInclusion i)) hf,
    genericFieldMap_comp (Spec.map g) (E.chartInclusion j) hg
      (genericPoint_eq_of_isOpenImmersion (E.chartInclusion j))] at hmaps
  have hh := congrArg (fun q ↦
    (affineFunctionFieldEquiv (CommRingCat.of (D.ring i)) F).toRingHom.comp q) hmaps
  rw [← RingHom.comp_assoc, ← RingHom.comp_assoc,
    genericFieldMap_affine_compat G F g hg φ hφ] at hh
  exact hh

end
end Red61.AffineGluing.PrincipalAtlas

/-! Codimension-one cycle pullback for a morphism inducing a homeomorphism.
Its coefficient at x is the local ramification index times the coefficient at
f(x). This supplies the usual finite-map Weil-divisor pullback in this setting. -/

namespace Red61

open AlgebraicGeometry CategoryTheory TopologicalSpace Order IsLocalRing
noncomputable section

def weightedHomeomorphPullback {X Y : Scheme} (e : X ≃ₜ Y) (w : X → ℤ) :
    AlgebraicCycle Y ℤ →+ AlgebraicCycle X ℤ where
  toFun c :=
    { toFun x := w x * c (e x)
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' x _ := by
        obtain ⟨U,hU,hfin⟩ := c.supportLocallyFiniteWithinDomain (e x) (Set.mem_univ _)
        refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
        apply (hfin.preimage e.injective.injOn).subset
        intro z hz
        exact ⟨hz.1, right_ne_zero_of_mul hz.2⟩ }
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp [mul_add]

@[simp] theorem weightedHomeomorphPullback_apply {X Y : Scheme}
    (e : X ≃ₜ Y) (w : X → ℤ) (c : AlgebraicCycle Y ℤ) (x : X) :
    weightedHomeomorphPullback e w c x = w x * c (e x) := rfl

end
end Red61

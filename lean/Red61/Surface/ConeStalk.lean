import Red61.Surface.Cone
import Red61.Surface.GeometricNonreduced

/-! # The invariant local ring at the cone point as a stalk

Formerly the modules `AffineInvariantGeometry`, `ConeChartInvariants`.
-/

/-! The invariant local ring is the actual stalk of the affine invariant spectrum. -/

namespace Red61.ConeRing

open Fields CategoryTheory AlgebraicGeometry
noncomputable section
set_option maxRecDepth 4096

def affineInvariantRing : Subalgebra ell A := invariantAlgebra D

instance : IsNoetherianRing affineInvariantRing := invariantAlgebra_noetherian D D_five

instance : IsDomain affineInvariantRing := inferInstance

def invariantLocalizationMap : affineInvariantRing →ₐ[ell] B :=
  ((IsScalarTower.toAlgHom ell A R).comp affineInvariantRing.val).codRestrict B (by
    intro x
    change localD (algebraMap A R (x : A)) = 0
    rw [localD_algebraMap, x.property, map_zero])

instance affineInvariantToLocalAlgebra : Algebra affineInvariantRing B :=
  invariantLocalizationMap.toAlgebra

@[simp] theorem invariantLocalizationMap_coe (x : affineInvariantRing) :
    (algebraMap affineInvariantRing B x : R) = algebraMap A R (x : A) := rfl

theorem invariantLocalizationMap_injective : Function.Injective invariantLocalizationMap := by
  intro x y h
  apply Subtype.ext
  apply localization_injective
  exact congrArg (fun z : B ↦ (z : R)) h

def invariantVertexIdeal : Ideal affineInvariantRing := maximal.comap affineInvariantRing.val

instance : invariantVertexIdeal.IsPrime :=
  Ideal.comap_isPrime _ maximal

def affineInvariantResidue : affineInvariantRing →ₐ[ell] k :=
  (residue.restrictScalars ell).comp affineInvariantRing.val

theorem affineInvariantResidue_surjective : Function.Surjective affineInvariantResidue := by
  intro a
  refine ⟨invariantRetraction D D_five (algebraMap k A a), ?_⟩
  change residue (algebraMap k A a - D (D (D (D (algebraMap k A a))))) = a
  rw [map_sub, residue_D, sub_zero]
  exact residue.commutes a

instance invariantVertex_maximal : invariantVertexIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective affineInvariantResidue affineInvariantResidue_surjective

theorem invariantVertex_primeCompl (x : affineInvariantRing) :
    x ∈ invariantVertexIdeal.primeCompl ↔ (x : A) ∈ maximal.primeCompl := Iff.rfl

theorem D_fifth_power (a : A) : D (a^5) = 0 := by
  apply localization_injective
  rw [map_zero, ← localD_algebraMap, map_pow, localD_fifth_power]

/-- Invariants commute with localization here: denominators can be replaced by fifth powers. -/
instance invariant_localization : IsLocalization invariantVertexIdeal.primeCompl B where
  map_units s := by
    apply (invariantAlgebra_isUnit localD _).mpr
    exact IsLocalization.map_units R
      (⟨((s : affineInvariantRing) : A), s.property⟩ : maximal.primeCompl)
  surj x := by
    obtain ⟨⟨a,b⟩,h⟩ := IsLocalization.surj maximal.primeCompl (x : R)
    let aa : affineInvariantRing := ⟨a * (b : A)^4, invariant_numerator x a b h⟩
    let bb : affineInvariantRing := ⟨(b : A)^5, D_fifth_power b⟩
    have hb : bb ∈ invariantVertexIdeal.primeCompl :=
      (invariantVertex_primeCompl bb).mpr (maximal.primeCompl.pow_mem b.property 5)
    refine ⟨⟨aa, ⟨bb,hb⟩⟩, ?_⟩
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, invariantLocalizationMap_coe]
    dsimp only [aa, bb]
    rw [map_mul, map_pow, map_pow, ← h]
    ring
  exists_of_eq {x y} h := by
    have he : x = y := invariantLocalizationMap_injective h
    exact ⟨1, by simp [he]⟩

abbrev affineInvariantSpec : Scheme := Spec (CommRingCat.of affineInvariantRing)

def invariantVertex : PrimeSpectrum affineInvariantRing := ⟨invariantVertexIdeal, inferInstance⟩

def affineQuotientMap : coneSpec ⟶ affineInvariantSpec :=
  Spec.map (CommRingCat.ofHom affineInvariantRing.val.toRingHom)

theorem affineQuotientMap_vertex : affineQuotientMap vertex = invariantVertex := rfl

/-- This is the quotient point's stalk, not merely the spectrum of the already-local ring. -/
def affineInvariantStalkEquiv :
    affineInvariantSpec.presheaf.stalk invariantVertex ≃+* B :=
  (Spec.stalkIso (CommRingCat.of affineInvariantRing) invariantVertex).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv invariantVertexIdeal.primeCompl
      (Localization.AtPrime invariantVertexIdeal) B).toRingEquiv

def affineInvariantEmbedding : affineInvariantRing →+* L :=
  invariantEmbedding.comp invariantLocalizationMap.toRingHom

@[instance_reducible] def affineInvariantFieldAlgebra : Algebra affineInvariantRing L :=
  affineInvariantEmbedding.toAlgebra

theorem affineInvariant_isFractionRing :
    letI := affineInvariantFieldAlgebra
    IsFractionRing affineInvariantRing L := by
  let := invariantFieldAlgebra
  let := invariant_isFractionRing
  let := affineInvariantFieldAlgebra
  let : Algebra affineInvariantRing B := affineInvariantToLocalAlgebra
  let : SMul affineInvariantRing B := affineInvariantToLocalAlgebra.toSMul
  let : IsScalarTower affineInvariantRing B L := .of_algebraMap_eq' rfl
  exact fractionRing_of_localization affineInvariantRing B L invariantVertexIdeal.primeCompl
    invariantLocalizationMap_injective

def affineInvariantFunctionFieldEquiv : affineInvariantSpec.functionField ≃+* L := by
  letI := affineInvariantFieldAlgebra
  letI := affineInvariant_isFractionRing
  exact affineFunctionFieldEquiv (CommRingCat.of affineInvariantRing) L

end
end Red61.ConeRing

/-! Identify the invariant chart in L with the affine invariant algebra used in the
local regularity proof. All maps use the original embedding of the cone algebra in K. -/

namespace Red61.Contraction

open Fields Charts FrobeniusDescent CategoryTheory AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

def coneFixedRing : Subalgebra ell L := fixed L (coneRing.restrictScalars ell)

theorem cone_derivation_kernel (a : ConeRing.A) :
    ConeRing.D a = 0 ↔ ConeRing.embed a ∈ L := by
  constructor
  · intro h
    apply ConeRing.theta_kernel_in_L
    change LocalCoordinates.theta (ConeRing.embedEll a) = 0
    rw [← ConeRing.embed_D, h, map_zero]
  · intro h
    apply ConeRing.embed_injective
    change ConeRing.embedEll (ConeRing.D a) = ConeRing.embedEll 0
    rw [ConeRing.embed_D, map_zero]
    change LocalCoordinates.U * LocalCoordinates.T * delta (ConeRing.embed a) = 0
    change delta (ConeRing.embed a) = 0 at h
    rw [h, mul_zero]

def coneInvariantHom : ConeRing.affineInvariantRing →ₐ[ell] coneFixedRing where
  toFun a := ⟨⟨ConeRing.embed a, (cone_derivation_kernel a).mp a.property⟩, ⟨a.val, rfl⟩⟩
  map_zero' := by apply Subtype.ext; apply Subtype.ext; exact map_zero ConeRing.embed
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one ConeRing.embed
  map_add' a b := by apply Subtype.ext; apply Subtype.ext; exact map_add ConeRing.embed a.val b.val
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact map_mul ConeRing.embed a.val b.val
  commutes' r := by
    apply Subtype.ext; apply Subtype.ext
    exact ConeRing.embedEll.commutes r

theorem coneInvariantHom_bijective : Function.Bijective coneInvariantHom := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply ConeRing.embed_injective
    exact congrArg (fun z : coneFixedRing ↦ (z.val : K)) h
  · intro x
    obtain ⟨a,ha⟩ := x.property
    have h : ConeRing.D a = 0 := (cone_derivation_kernel a).mpr (ha.symm ▸ x.val.property)
    refine ⟨⟨a,h⟩, ?_⟩
    exact Subtype.ext (Subtype.ext ha)

def coneInvariantEquiv : ConeRing.affineInvariantRing ≃ₐ[ell] coneFixedRing :=
  AlgEquiv.ofBijective coneInvariantHom coneInvariantHom_bijective

@[simp] theorem coneInvariantEquiv_coe (a : ConeRing.affineInvariantRing) :
    ((coneInvariantEquiv a : L) : K) = ConeRing.embed a := rfl

def coneIso : ConeRing.coneSpec ≅ Spec (CommRingCat.of coneRing) :=
  Scheme.Spec.mapIso coneRingEquiv.symm.toRingEquiv.toCommRingCatIso.op

def coneInvariantIso : ConeRing.affineInvariantSpec ≅ Spec (CommRingCat.of coneFixedRing) :=
  Scheme.Spec.mapIso coneInvariantEquiv.symm.toRingEquiv.toCommRingCatIso.op

def coneQuotient : Spec (CommRingCat.of coneRing) ⟶ Spec (CommRingCat.of coneFixedRing) :=
  Spec.map (CommRingCat.ofHom (FrobeniusDescent.embed L (coneRing.restrictScalars ell)).toRingHom)

theorem cone_quotient_square :
    coneIso.hom ≫ coneQuotient = ConeRing.affineQuotientMap ≫ coneInvariantIso.hom := by
  change Spec.map (CommRingCat.ofHom coneRingEquiv.symm.toRingHom) ≫ coneQuotient =
    ConeRing.affineQuotientMap ≫ Spec.map (CommRingCat.ofHom coneInvariantEquiv.symm.toRingHom)
  simp only [coneQuotient, ConeRing.affineQuotientMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply coneRingEquiv.injective
  change coneRingEquiv (coneRingEquiv.symm _) = coneRingEquiv (coneInvariantEquiv.symm x).val
  rw [coneRingEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (congrArg (fun z : coneFixedRing ↦ (z.val : K))
    (coneInvariantEquiv.apply_symm_apply x)).symm

end
end Red61.Contraction

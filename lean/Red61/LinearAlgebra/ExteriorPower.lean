import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Top exterior powers and determinants

Formerly the modules `DeterminantLineEvaluation`, `ExteriorLinearEquiv`, `RingHomExterior`, `RingHomExteriorEquiv`, `RingHomExteriorNaturality`, `SquarePresentation`, `ExactPresentations`, `TopExteriorCoordinates`, `IntegralTopExterior`, `RingHomExteriorCoefficient`, `SemilinearTopExterior`, `SplitExactVolume`, `DeterminantAdjunction`, `DeterminantCancellation`.
-/

/-! A fixed volume of a one-dimensional base determinant identifies the
relative determinant line Hom(base determinant, target determinant) with
the target determinant. All scalar actions and inverse maps are explicit. -/

namespace Red61

noncomputable section

variable {F K B V : Type*} [CommRing F] [CommRing K] [Algebra F K]
  [AddCommGroup B] [Module F B] [AddCommGroup V] [Module K V] [Module F V]
  [IsScalarTower F K V]

def determinantLineEvaluation (e : B ≃ₗ[F] F) : (B →ₗ[F] V) ≃ₗ[K] V where
  toFun φ := φ (e.symm 1)
  invFun v :=
    { toFun := fun b ↦ e b • v
      map_add' := fun a b ↦ by rw [map_add, add_smul]
      map_smul' := fun a b ↦ by simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul] }
  left_inv φ := by
    ext b
    change e b • φ (e.symm 1) = φ b
    rw [← map_smul]
    congr 1
    apply e.injective
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  right_inv v := by
    change e (e.symm 1) • v = v
    rw [e.apply_symm_apply, one_smul]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem determinantLineEvaluation_apply (e : B ≃ₗ[F] F) (φ : B →ₗ[F] V) :
    determinantLineEvaluation (K := K) e φ = φ (e.symm 1) := rfl

@[simp] theorem determinantLineEvaluation_symm_apply (e : B ≃ₗ[F] F) (v : V) (b : B) :
    (determinantLineEvaluation (K := K) e).symm v b = e b • v := rfl

end
end Red61

/-! Linear equivalences induce equivalences on genuine exterior powers,
with their action on exterior products and their composition explicit. -/

namespace Red61

noncomputable section

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def exteriorLinearEquiv (n : ℕ) (e : M ≃ₗ[R] N) : (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective (n := n) e.symm.toLinearMap (by ext x; simp),
      exteriorPower.map_surjective (n := n) e.surjective⟩

@[simp] theorem exteriorLinearEquiv_apply (n : ℕ) (e : M ≃ₗ[R] N) (ω : ⋀[R]^n M) :
    exteriorLinearEquiv n e ω = exteriorPower.map n e.toLinearMap ω := rfl

theorem exteriorLinearEquiv_wedge (n : ℕ) (e : M ≃ₗ[R] N) (v : Fin n → M) :
    exteriorLinearEquiv n e (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R n (e ∘ v) := by
  simp [Function.comp_def]

end
end Red61

/-! Exterior powers act on arbitrary semilinear maps without a basis
choice. The actual wedge formula, extensionality, linear specialization,
identity and composition are proved from the exterior universal property. -/

namespace Red61
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v t w z q
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  {V : Type w} {W : Type z} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module S W] (φ : R →+* S) (n : ℕ)

def semilinearExteriorMap (f : V →ₛₗ[φ] W) :
    (⋀[R]^n V) →ₛₗ[φ] (⋀[S]^n W) := by
  letI := φ.toAlgebra
  letI : Module R W := Module.compHom W φ
  letI : Module R (⋀[S]^n W) := Module.compHom (⋀[S]^n W) φ
  letI : IsScalarTower R S W := IsScalarTower.of_compHom R S W
  letI : IsScalarTower R S (⋀[S]^n W) := IsScalarTower.of_compHom R S _
  let fR : V →ₗ[R] W := { f.toAddHom with map_smul' := f.map_smul' }
  let j : W [⋀^Fin n]→ₗ[R] (⋀[S]^n W) :=
    { toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := fun a i j h hij ↦
        (exteriorPower.ιMulti S n).map_eq_zero_of_eq a h hij }
  let g := exteriorPower.alternatingMapLinearEquiv (j.compLinearMap fR)
  exact { g.toAddHom with map_smul' := g.map_smul }

theorem semilinearExteriorMap_wedge (f : V →ₛₗ[φ] W) (a : Fin n → V) :
    semilinearExteriorMap φ n f (exteriorPower.ιMulti R n a) =
      exteriorPower.ιMulti S n (fun i ↦ f (a i)) := by
  let := φ.toAlgebra
  let : Module R W := Module.compHom W φ
  let : Module R (⋀[S]^n W) := Module.compHom (⋀[S]^n W) φ
  let : IsScalarTower R S W := IsScalarTower.of_compHom R S W
  let : IsScalarTower R S (⋀[S]^n W) := IsScalarTower.of_compHom R S _
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ a

theorem exteriorSemilinearMap_ext
    {f g : (⋀[R]^n V) →ₛₗ[φ] W}
    (h : ∀ a : Fin n → V, f (exteriorPower.ιMulti R n a) =
      g (exteriorPower.ιMulti R n a)) : f = g := by
  let : Module R W := Module.compHom W φ
  let fR : (⋀[R]^n V) →ₗ[R] W := { f.toAddHom with map_smul' := f.map_smul' }
  let gR : (⋀[R]^n V) →ₗ[R] W := { g.toAddHom with map_smul' := g.map_smul' }
  have he : fR = gR := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    exact h a
  exact LinearMap.ext (fun ω ↦ DFunLike.congr_fun he ω)

theorem semilinearExteriorMap_linear {U : Type z} [AddCommGroup U] [Module R U]
    (f : V →ₗ[R] U) :
    semilinearExteriorMap (RingHom.id R) n f = exteriorPower.map n f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  exact (semilinearExteriorMap_wedge (RingHom.id R) n f a).trans
    (exteriorPower.map_apply_ιMulti f a).symm

variable {T : Type t} [CommRing T] {Z : Type q} [AddCommGroup Z] [Module T Z]
  (ψ : S →+* T)

private local instance : RingHomCompTriple φ ψ (ψ.comp φ) := ⟨rfl⟩

end
end Red61

/-! Exterior powers preserve inverse pairs of semilinear maps through
a ring isomorphism. The actual wedge formula proves both inverse identities
and bijectivity without any freeness or basis assumptions. -/

namespace Red61
open Module
noncomputable section
variable {R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
  (n : ℕ) (e : R ≃+* S)
  (f : V →ₛₗ[e.toRingHom] W) (g : W →ₛₗ[e.symm.toRingHom] V)

theorem semilinearExteriorMap_leftInverse (h : Function.LeftInverse g f) :
    Function.LeftInverse (semilinearExteriorMap e.symm.toRingHom n g)
      (semilinearExteriorMap e.toRingHom n f) := by
  let : RingHomCompTriple e.toRingHom e.symm.toRingHom (RingHom.id R) :=
    ⟨by ext r; exact e.symm_apply_apply r⟩
  let F : (⋀[R]^n V) →ₗ[R] (⋀[R]^n V) :=
    (semilinearExteriorMap e.symm.toRingHom n g).comp
      (semilinearExteriorMap e.toRingHom n f)
  have hF : F = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    exact (congrArg (semilinearExteriorMap e.symm.toRingHom n g)
      (semilinearExteriorMap_wedge e.toRingHom n f a)).trans
        ((semilinearExteriorMap_wedge e.symm.toRingHom n g (fun i ↦ f (a i))).trans
          (congrArg (exteriorPower.ιMulti R n) (funext fun i ↦ h (a i))))
  intro ω
  exact LinearMap.congr_fun hF ω

theorem semilinearExteriorMap_bijective (hL : Function.LeftInverse g f)
    (hR : Function.RightInverse g f) :
    Function.Bijective (semilinearExteriorMap e.toRingHom n f) := by
  have h₁ := semilinearExteriorMap_leftInverse n e f g hL
  have h₂ := semilinearExteriorMap_leftInverse n e.symm g f hR
  exact ⟨h₁.injective, h₂.surjective⟩
end
end Red61

/-! Exterior powers of arbitrary semilinear maps preserve commuting
squares of ring maps. Both composites use the displayed common ring
homomorphism; the wedge formula proves naturality in every degree. -/

namespace Red61
open Module
noncomputable section
variable {R S T U V W X Y : Type*}
  [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
  [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module U Y]
  (φ : R →+* S) (ψ : R →+* T) (φ' : T →+* U) (ψ' : S →+* U) (τ : R →+* U)
  [RingHomCompTriple ψ φ' τ] [RingHomCompTriple φ ψ' τ]

include τ in
theorem semilinearExteriorMap_natural (n : ℕ)
    (f : V →ₛₗ[φ] W) (g : V →ₛₗ[ψ] X) (f' : X →ₛₗ[φ'] Y) (g' : W →ₛₗ[ψ'] Y)
    (h : ∀ v, f' (g v) = g' (f v)) (ω : ⋀[R]^n V) :
    semilinearExteriorMap φ' n f' (semilinearExteriorMap ψ n g ω) =
      semilinearExteriorMap ψ' n g' (semilinearExteriorMap φ n f ω) := by
  have he : (semilinearExteriorMap φ' n f').comp (semilinearExteriorMap ψ n g) =
      ((semilinearExteriorMap ψ' n g').comp
        (semilinearExteriorMap φ n f) : (⋀[R]^n V) →ₛₗ[τ] (⋀[U]^n Y)) := by
    apply exteriorSemilinearMap_ext τ n
    intro a
    change semilinearExteriorMap φ' n f'
      (semilinearExteriorMap ψ n g (exteriorPower.ιMulti R n a)) =
        semilinearExteriorMap ψ' n g'
          (semilinearExteriorMap φ n f (exteriorPower.ιMulti R n a))
    rw [semilinearExteriorMap_wedge, semilinearExteriorMap_wedge,
      semilinearExteriorMap_wedge, semilinearExteriorMap_wedge]
    exact congrArg (exteriorPower.ιMulti U n) (funext fun i ↦ h (a i))
  exact LinearMap.congr_fun he ω
end
end Red61

/-! An injective square free presentation, its determinant, and independence
of its determinant ideal over a DVR. The cokernel is identified by a linear
equivalence with the specified module, not merely by an equality of lengths. -/

namespace Red61

open Module
noncomputable section

structure SquarePresentation (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] (Fin rank → R)
  injective : Function.Injective map
  cokernelEquiv : ((Fin rank → R) ⧸ LinearMap.range map) ≃ₗ[R] M

namespace SquarePresentation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def determinant (P : SquarePresentation R M) : R := LinearMap.det P.map

end SquarePresentation
end
end Red61

/-! Coordinates of exact sequences and square presentations of their
cokernels. Injectivity over a DVR follows from finite cokernel length and
equal finite free ranks; it is not an extra assumption in that result. -/

namespace Red61

open Module Submodule
noncomputable section

variable {R U V M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]

def cokernelEquivOfExact (f : U →ₗ[R] V) (q : V →ₗ[R] M)
    (hq : Function.Surjective q) (hex : Function.Exact f q) :
    (V ⧸ LinearMap.range f) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hex).symm).trans
    (q.quotKerEquivOfSurjective hq)

@[simp] theorem cokernelEquivOfExact_mk (f : U →ₗ[R] V) (q : V →ₗ[R] M)
    (hq : Function.Surjective q) (hex : Function.Exact f q) (x : V) :
    cokernelEquivOfExact f q hq hex (Submodule.Quotient.mk x) = q x := by
  simp [cokernelEquivOfExact]

theorem topForm_pullback_coordinates {n : ℕ}
    (bU : Basis (Fin n) R U) (bV : Basis (Fin n) R V) (f : U →ₗ[R] V) :
    bV.det.compLinearMap f = (LinearMap.toMatrix bU bV f).det • bU.det := by
  rw [(bV.det.compLinearMap f).eq_smul_basis_det bU]
  congr 1
  change bV.det (f ∘ bU) = _
  rw [bV.det_apply, LinearMap.toMatrix_eq_basisToMatrix]

end
end Red61

/-! Coordinates of genuine elements of the top exterior power, including
their change under a linear map and under extension of scalars. -/

namespace Red61

open Module
open scoped TensorProduct
noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

def topExteriorCoefficient (b : Basis (Fin n) R M) : (⋀[R]^n M) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv b.det

@[simp] theorem topExteriorCoefficient_wedge (b : Basis (Fin n) R M) (v : Fin n → M) :
    topExteriorCoefficient b (exteriorPower.ιMulti R n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem topExteriorCoefficient_volume (b : Basis (Fin n) R M) :
    topExteriorCoefficient b (exteriorPower.ιMulti R n b) = 1 := by
  rw [topExteriorCoefficient_wedge, b.det_self]

theorem topExteriorCoefficient_map (b : Basis (Fin n) R M) (c : Basis (Fin n) R N)
    (f : M →ₗ[R] N) (ω : ⋀[R]^n M) :
    topExteriorCoefficient c (exteriorPower.map n f ω) =
      (LinearMap.toMatrix b c f).det * topExteriorCoefficient b ω := by
  have he : (topExteriorCoefficient c).comp (exteriorPower.map n f) =
      (LinearMap.toMatrix b c f).det • topExteriorCoefficient b := by
    apply exteriorPower.linearMap_ext
    ext v
    simpa [LinearMap.compAlternatingMap_apply, topExteriorCoefficient_wedge, Function.comp_def,
      exteriorPower.map_apply_ιMulti] using
        DFunLike.congr_fun (topForm_pullback_coordinates b c f) v
  exact DFunLike.congr_fun he ω

theorem topExteriorCoefficient_bijective {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (b : Basis (Fin n) F V) :
    Function.Bijective (topExteriorCoefficient b) := by
  have := Module.Finite.of_basis b
  have hd : Module.finrank F (⋀[F]^n V) = Module.finrank F F := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b]
    simp
  have hs : Function.Surjective (topExteriorCoefficient b) := by
    intro a
    exact ⟨a • exteriorPower.ιMulti F n b, by simp [b.det_self]⟩
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

variable (F : Type*) [CommRing F] [Algebra R F]

theorem basisDet_baseChange (b c : Basis (Fin n) R M) :
    (c.baseChange F).det (b.baseChange F) = algebraMap R F (c.det b) := by
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, Algebra.smul_def]

end
end Red61

/-! Top exterior powers over a commutative ring, including local rings.
A finite basis identifies its integral determinant module with the ring.
The result requires no fraction-field passage or dimension argument. -/

namespace Red61

open Module
noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

theorem alternatingMap_eq_det_smul (b : Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) : f = b.det.smulRight (f b) := by
  classical
  apply b.ext_alternating
  intro i hi
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
  change f (b ∘ σ) = (b.det.smulRight (f b)) (b ∘ σ)
  rw [AlternatingMap.map_perm]
  change Equiv.Perm.sign σ • f b = b.det (b ∘ σ) • f b
  rw [AlternatingMap.map_perm, b.det_self]
  simp

theorem integralTopExterior_eq_coefficient (b : Basis (Fin n) R M) (ω : ⋀[R]^n M) :
    ω = topExteriorCoefficient b ω • exteriorPower.ιMulti R n b := by
  have he : (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M)) =
      (LinearMap.id.smulRight (exteriorPower.ιMulti R n b)).comp
        (topExteriorCoefficient b) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, topExteriorCoefficient_wedge]
    change exteriorPower.ιMulti R n v =
      b.det v • exteriorPower.ιMulti R n b
    exact congrArg (fun g ↦ g v) (alternatingMap_eq_det_smul b (exteriorPower.ιMulti R n))
  exact DFunLike.congr_fun he ω

def integralTopExteriorCoefficient (b : Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R where
  toLinearMap := topExteriorCoefficient b
  invFun a := a • exteriorPower.ιMulti R n b
  left_inv ω := (integralTopExterior_eq_coefficient b ω).symm
  right_inv a := by simp [b.det_self]

@[simp] theorem integralTopExteriorCoefficient_volume (b : Basis (Fin n) R M) :
    integralTopExteriorCoefficient b (exteriorPower.ιMulti R n b) = 1 :=
  topExteriorCoefficient_volume b

@[simp] theorem integralTopExteriorCoefficient_symm_apply (b : Basis (Fin n) R M) (a : R) :
    (integralTopExteriorCoefficient b).symm a = a • exteriorPower.ιMulti R n b := rfl

end
end Red61

/-! A semilinear map carrying a displayed finite basis to another
preserves the integral top exterior coefficient through the stated
ring homomorphism. -/

namespace Red61
open Module
noncomputable section
variable {R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]
  (φ : R →+* S) {n : ℕ} (b : Basis (Fin n) R V) (c : Basis (Fin n) S W)
  (f : V →ₛₗ[φ] W)

theorem integralTopExteriorCoefficient_ringHom
    (hf : ∀ i, f (b i) = c i) (ω : ⋀[R]^n V) :
    integralTopExteriorCoefficient c (semilinearExteriorMap φ n f ω) =
      φ (integralTopExteriorCoefficient b ω) := by
  rw [integralTopExterior_eq_coefficient b ω, map_smulₛₗ, semilinearExteriorMap_wedge,
    funext hf, map_smul, integralTopExteriorCoefficient_volume, smul_eq_mul, mul_one]
  simp only [map_smul, integralTopExteriorCoefficient_volume, smul_eq_mul, mul_one]
end
end Red61

/-! The genuine top exterior map along an extension of scalars. Its wedge
formula proves independence of the source basis, agreement with the linear
exterior map, and compatibility with composition. -/

namespace Red61
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W] {n : ℕ}

def semilinearTopExteriorMap (b : Basis (Fin n) R V)
    (f : V →ₛₗ[algebraMap R S] W) : (⋀[R]^n V) →ₛₗ[algebraMap R S] (⋀[S]^n W) where
  toFun ω := algebraMap R S (topExteriorCoefficient b ω) •
    exteriorPower.ιMulti S n (fun i ↦ f (b i))
  map_add' ω η := by rw [map_add, map_add, add_smul]
  map_smul' r ω := by rw [map_smul, smul_eq_mul, map_mul, mul_smul]

theorem semilinearTopExteriorMap_wedge (b : Basis (Fin n) R V)
    (f : V →ₛₗ[algebraMap R S] W) (v : Fin n → V) :
    semilinearTopExteriorMap b f (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i ↦ f (v i)) := by
  let : Module R W := Module.compHom W (algebraMap R S)
  let : Module R (⋀[S]^n W) := Module.compHom (⋀[S]^n W) (algebraMap R S)
  have : IsScalarTower R S W := IsScalarTower.of_compHom R S W
  have : IsScalarTower R S (⋀[S]^n W) := IsScalarTower.of_compHom R S _
  let fR : V →ₗ[R] W :=
    { toFun := f
      map_add' := f.map_add
      map_smul' r x := f.map_smul' r x }
  let j : W [⋀^Fin n]→ₗ[R] (⋀[S]^n W) :=
    { toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := fun v i j h hij ↦
        (exteriorPower.ιMulti S n).map_eq_zero_of_eq v h hij }
  have he := DFunLike.congr_fun (alternatingMap_eq_det_smul b (j.compLinearMap fR)) v
  change exteriorPower.ιMulti S n (fun i ↦ f (v i)) =
    algebraMap R S (b.det v) • exteriorPower.ιMulti S n (fun i ↦ f (b i)) at he
  simpa only [semilinearTopExteriorMap, LinearMap.coe_mk, AddHom.coe_mk,
    topExteriorCoefficient_wedge] using he.symm

def linearToAlgebraSemilinear [Module R W] [IsScalarTower R S W]
    (f : V →ₗ[R] W) : V →ₛₗ[algebraMap R S] W where
  toFun := f
  map_add' := f.map_add
  map_smul' r v := (map_smul f r v).trans (algebraMap_smul S r (f v)).symm

variable {T Z : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [AddCommGroup Z] [Module T Z]

private local instance : RingHomCompTriple (algebraMap R S) (algebraMap S T)
    (algebraMap R T) := ⟨(IsScalarTower.algebraMap_eq R S T).symm⟩

end
end Red61

/-! Integral volumes of split exact sequences. Changing the lift of a
quotient basis changes the combined basis by a block upper triangular
matrix with identity diagonal blocks. Its determinant is one. -/

namespace Red61

open Module
noncomputable section

variable {R C V M : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]
  (f : C →ₗ[R] V) (g : V →ₗ[R] M) (hf : Function.Injective f)
  (hex : Function.Exact f g) (s : M →ₗ[R] V) (hs : g.comp s = LinearMap.id)

include hf hex hs in
theorem splitExact_coprod_bijective : Function.Bijective (f.coprod s) := by
  constructor
  · rintro ⟨c, m⟩ ⟨d, n⟩ h
    have hmn : m = n := by
      have h' := congrArg g h
      simpa only [LinearMap.coprod_apply, map_add, hex.apply_apply_eq_zero,
        show ∀ x, g (s x) = x from fun x ↦ DFunLike.congr_fun hs x, zero_add] using h'
    subst n
    have hcd : c = d := hf (add_right_cancel h)
    exact Prod.ext hcd rfl
  · intro v
    have hz : g (v - s (g v)) = 0 := by
      rw [map_sub, show g (s (g v)) = g v from DFunLike.congr_fun hs (g v), sub_self]
    obtain ⟨c, hc⟩ := (hex (v - s (g v))).mp hz
    exact ⟨(c, g v), by simp only [LinearMap.coprod_apply, hc, sub_add_cancel]⟩

def splitExactEquiv : (C × M) ≃ₗ[R] V :=
  LinearEquiv.ofBijective (f.coprod s) (splitExact_coprod_bijective f g hf hex s hs)

@[simp] theorem splitExactEquiv_apply (c : C) (m : M) :
    splitExactEquiv f g hf hex s hs (c, m) = f c + s m := rfl

theorem splitExactEquiv_symm_f (c : C) :
    (splitExactEquiv f g hf hex s hs).symm (f c) = (c, 0) := by
  apply (splitExactEquiv f g hf hex s hs).injective
  simp

def splitExactBasis {ι κ : Type*} (bC : Basis ι R C) (bM : Basis κ R M) :
    Basis (ι ⊕ κ) R V :=
  (bC.prod bM).map (splitExactEquiv f g hf hex s hs)

@[simp] theorem splitExactBasis_inl {ι κ : Type*} (bC : Basis ι R C)
    (bM : Basis κ R M) (i : ι) :
    splitExactBasis f g hf hex s hs bC bM (.inl i) = f (bC i) := by
  simp [splitExactBasis, Basis.prod_apply, splitExactEquiv_apply]

@[simp] theorem splitExactBasis_inr {ι κ : Type*} (bC : Basis ι R C)
    (bM : Basis κ R M) (i : κ) :
    splitExactBasis f g hf hex s hs bC bM (.inr i) = s (bM i) := by
  simp [splitExactBasis, Basis.prod_apply, splitExactEquiv_apply]

def splitExactFinBasis {c m : ℕ} (bC : Basis (Fin c) R C) (bM : Basis (Fin m) R M) :
    Basis (Fin (c + m)) R V :=
  (splitExactBasis f g hf hex s hs bC bM).reindex finSumFinEquiv

end
end Red61

/-! Integral determinant adjunction for a split conormal sequence.
The map uses actual exterior powers and is independent of the chosen
linear section. All coefficients and maps live over the original ring. -/

namespace Red61

open Module
noncomputable section

variable {R C V M : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M]
  (f : C →ₗ[R] V) (g : V →ₗ[R] M) (hf : Function.Injective f)
  (hex : Function.Exact f g) (s : M →ₗ[R] V) (hs : g.comp s = LinearMap.id)
  {c m : ℕ} (bC : Basis (Fin c) R C) (bM : Basis (Fin m) R M)

def splitDeterminantAdjunction :
    ((⋀[R]^c C) →ₗ[R] (⋀[R]^(c + m) V)) ≃ₗ[R] (⋀[R]^m M) :=
  (determinantLineEvaluation (K := R) (integralTopExteriorCoefficient bC)).trans
    ((integralTopExteriorCoefficient (splitExactFinBasis f g hf hex s hs bC bM)).trans
      (integralTopExteriorCoefficient bM).symm)

end
end Red61

/-! Cancellation of an ambient determinant in two adjunction sequences.
Applied to the absolute conormal sequence and the ambient base sequence,
this gives the comparison between the relative adjunction line and the
base-normalized absolute determinant line. -/

namespace Red61

open Module
noncomputable section

variable {R C B V M P : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
  [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

def determinantAdjunctionCancellation
    (eC : (C →ₗ[R] V) ≃ₗ[R] M) (eB : (B →ₗ[R] V) ≃ₗ[R] P) :
    (C →ₗ[R] P) ≃ₗ[R] (B →ₗ[R] M) :=
  (LinearEquiv.congrRight eB.symm).trans
    (LinearMap.lflip.trans (LinearEquiv.congrRight eC))

def exteriorPowerDegreeEquiv (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    {n k : ℕ} (h : n = k) : (⋀[R]^n V) ≃ₗ[R] (⋀[R]^k V) :=
  h ▸ LinearEquiv.refl R (⋀[R]^n V)

def normalizedDeterminantAdjunction {c m b p : ℕ}
    (fC : C →ₗ[R] V) (gM : V →ₗ[R] M) (hfC : Function.Injective fC)
    (hexC : Function.Exact fC gM) (sM : M →ₗ[R] V) (hsM : gM.comp sM = LinearMap.id)
    (fB : B →ₗ[R] V) (gP : V →ₗ[R] P) (hfB : Function.Injective fB)
    (hexB : Function.Exact fB gP) (sP : P →ₗ[R] V) (hsP : gP.comp sP = LinearMap.id)
    (bC : Basis (Fin c) R C) (bM : Basis (Fin m) R M)
    (bB : Basis (Fin b) R B) (bP : Basis (Fin p) R P) (hrank : c + m = b + p) :
    ((⋀[R]^c C) →ₗ[R] (⋀[R]^p P)) ≃ₗ[R]
      ((⋀[R]^b B) →ₗ[R] (⋀[R]^m M)) :=
  determinantAdjunctionCancellation (splitDeterminantAdjunction fC gM hfC hexC sM hsM bC bM)
    ((LinearEquiv.congrRight (exteriorPowerDegreeEquiv R V hrank)).trans
      (splitDeterminantAdjunction fB gP hfB hexB sP hsP bB bP))

end
end Red61

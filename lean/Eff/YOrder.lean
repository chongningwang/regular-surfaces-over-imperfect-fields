import Eff.AffineUnits
import Eff.YVolume
import SurfaceLib.LineBundle.RationalLine

/-! # The canonical line of the second quotient has exact order five

Tensor powers are genuine sheaf tensor powers. The fifth power is trivial because the fifth
power of a local generator is a unit multiple of one fixed rational function. Conversely, a
trivialization of the `n`-th power produces a function with weight `4n` which is a unit on an
affine chart of `S`. Units there are scalars of weight zero, so `5 ∣ n`.
-/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent Red61.LocalCoordinates
  AlgebraicGeometry CategoryTheory Module Opposite SurfaceLib.LineBundle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000

private local instance : CommRing Y.functionField :=
  (inferInstance : Field Y.functionField).toCommRing

/-- The sheaf of absolute top forms of `Y`. -/
abbrev yTop : Y.Modules := nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) 4

private local instance (y : Y) : Module (Y.presheaf.stalk y) (yTop.presheaf.stalk y) :=
  schemeModuleNativeStalkModule Y yTop y

/-- The coefficient of a rational top form relative to the reference form. -/
def topCoefficient : RationalSchemeForms Y 4 →ₗ[Y.functionField] Y.functionField :=
  topExteriorCoefficient refBasis

theorem topCoefficient_smul (c : Y.functionField) : topCoefficient (c • θ) = c := by
  rw [map_smul, topCoefficient, θ, topExteriorCoefficient_volume, smul_eq_mul, mul_one]

/-- The rational realization of the sheaf of top forms. -/
def yTopLine : RationalLine yTop.val where
  ev x :=
    { toFun := fun ξ ↦ topCoefficient (nativeAbsoluteExteriorStalkToRational Y x 4 ξ)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  ev_smul x a ξ := by
    change topCoefficient (nativeAbsoluteExteriorStalkToRational Y x 4 (a • ξ)) =
      _ * topCoefficient (nativeAbsoluteExteriorStalkToRational Y x 4 ξ)
    rw [map_smulₛₗ, map_smul, smul_eq_mul]
  ev_germ U x z hx hz t :=
    congrArg topCoefficient
      (nativeAbsoluteExteriorSectionRationalValue_eq Y 4 U t ⟨x, hx⟩ ⟨z, hz⟩)

/-- A local top-form frame on a principal open. -/
def YOpen.topFrame {i : Fin 4} (U : YOpen i) :
    SheafOfModules.unit (Spec (CommRingCat.of U.kernel)).ringCatSheaf ≅ yTop.restrict U.openMap :=
  (nativeFiniteFreeTopExteriorIso (Spec (CommRingCat.of U.kernel)) 4).symm ≪≫
    (nativeExteriorFunctor (Spec (CommRingCat.of U.kernel)) 4).mapIso
      (affineOpenNativeAbsoluteDifferentialFrame (A := CommRingCat.of U.kernel) U.openMap U.absBasis) ≪≫
        nativeExteriorRestrictionIso U.openMap (nativeAbsoluteDifferentialModule Y) 4

theorem yTop_stalk_frame (y : Y) :
    Nonempty (Y.presheaf.stalk y ≃ₗ[Y.presheaf.stalk y] yTop.presheaf.stalk y) := by
  obtain ⟨a, q, hd, rfl⟩ := y_open_cover y
  obtain ⟨z, hz⟩ := (yOpen a).mem_openMap q hd
  rw [← hz]
  exact ⟨openImmersionStalkFrameEquiv (yOpen a).openMap z yTop (yOpen a).topFrame⟩

/-- The Jacobian factors generate the lattice of top forms. -/
theorem yTop_isGenerator (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a)))
    (hd : (yOpen a).d ∉ q.asIdeal) :
    yTopLine.IsGenerator (yAtlas.chartInclusion (chartOf a) q) (ν a) := by
  let y : Y := yAtlas.chartInclusion (chartOf a) q
  have hL : GeneratesStalkDifferentialLattice (n := 4) y (ν a • θ) := y_lattice a q hd
  obtain ⟨b, hb⟩ := id hL
  have hν : ν a ≠ 0 := by
    rintro h
    apply hL.ne_zero
    rw [h, zero_smul]
  have hint : IsIntegralStalkTopForm y (ν a • θ) :=
    (isIntegralStalkTopForm_iff_generator y hL _).mpr ⟨1, by simp⟩
  obtain ⟨g, hg⟩ := (nativeAbsoluteExteriorStalkToRational_range Y y 4 b _).mpr hint
  obtain ⟨e⟩ := yTop_stalk_frame y
  let g₁ : yTop.presheaf.stalk y := e 1
  have hsmul (c : Y.presheaf.stalk y) : e c = c • g₁ := by
    conv_lhs => rw [show c = c • (1 : Y.presheaf.stalk y) by simp]
    exact e.map_smul c 1
  have hg₁ := (isIntegralStalkTopForm_iff_generator y hL _).mp
    (nativeAbsoluteExteriorStalkToRational_integral Y y 4 b g₁)
  obtain ⟨a₁, ha₁⟩ := hg₁
  have hga : g = e.symm g • g₁ := by
    rw [← hsmul, LinearEquiv.apply_symm_apply]
  have hratio : ν a = algebraMap _ Y.functionField (e.symm g) *
      (algebraMap _ Y.functionField a₁ * ν a) := by
    have h1 := congrArg (fun z ↦ nativeAbsoluteExteriorStalkToRational Y y 4 z) hga
    simp only [map_smulₛₗ, hg, ha₁, smul_smul] at h1
    have h2 := congrArg topCoefficient h1
    rw [topCoefficient_smul, topCoefficient_smul] at h2
    exact h2.trans (by ring)
  have hunit : e.symm g * a₁ = 1 := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, map_one]
    apply mul_right_cancel₀ hν
    rw [one_mul, mul_assoc]
    exact hratio.symm
  refine ⟨hν, g, ?_, ?_⟩
  · change topCoefficient (nativeAbsoluteExteriorStalkToRational Y y 4 g) = ν a
    rw [hg, topCoefficient_smul]
  · intro ξ
    refine ⟨e.symm ξ * a₁, ?_⟩
    have h1 : ξ = e.symm ξ • g₁ := by rw [← hsmul, LinearEquiv.apply_symm_apply]
    have hg1g : g₁ = a₁ • g := by
      conv_rhs => rw [hga]
      rw [smul_smul, mul_comm a₁, hunit, one_smul]
    conv_lhs => rw [h1, hg1g]
    rw [smul_smul]

/-! ### The local units -/

open YTuples (z a c d W₀ N₀)

def yc : YIdx → ℕ
  | .q => 1
  | _ => 4

def yn : YIdx → ℤ
  | .B => -1 | .A => -3 | .W => -2 | .Q => 1 | .H => -2 | .G => -4 | .τ => -1 | .q => -4 | .u => -3

/-- The unit by which the local generator differs from `q₁⁴` times the reference form. -/
def ψ (a : YIdx) : L := (yc a : L) * (yOpen a).v 0 ^ yn a

theorem ψ_coe (a : YIdx) : (ψ a : K) = (yc a : K) * ((yOpen a).v 0 : K) ^ yn a := by
  have h : ((((yOpen a).v 0 ^ yn a : L)) : K) = ((yOpen a).v 0 : K) ^ yn a :=
    map_zpow₀ L.subtype _ _
  rw [ψ, Subfield.coe_mul, h]
  simp

theorem v0_B : ((yOpen .B).v 0 : K) = YTuples.B q₁ q₂ u := by
  have h : (yOpen .B).v 0 = base0.x 1 :=
    base0.tuple_zero 1 (Equiv.swap 0 1) ![0, 0, 2, 3] (by decide) (by decide)
  rw [h]
  exact xval0 1

theorem v0_A : ((yOpen .A).v 0 : K) = YTuples.A q₁ u := by
  have h : (yOpen .A).v 0 = base0.x 2 :=
    base0.tuple_zero 2 (Equiv.swap 0 2) ![0, 3, 0, 4] (by decide) (by decide)
  rw [h]
  exact xval0 2

theorem v0_W : ((yOpen .W).v 0 : K) = YTuples.W u := by
  have h : (yOpen .W).v 0 = base0.x 3 :=
    base0.tuple_zero 3 (Equiv.swap 0 3) ![0, 2, 4, 0] (by decide) (by decide)
  rw [h]
  exact xval0 3

theorem v0_Q : ((yOpen .Q).v 0 : K) = YTuples.Q q₁ q₂ r := by
  have h : (yOpen .Q).v 0 = base1.x 1 :=
    base1.tuple_zero 1 (Equiv.swap 0 1) ![0, 0, 2, 1] (by decide) (by decide)
  rw [h]
  exact xval1 1

theorem v0_H : ((yOpen .H).v 0 : K) = YTuples.H q₂ r := by
  have h : (yOpen .H).v 0 = base1.x 2 :=
    base1.tuple_zero 2 (Equiv.swap 0 2) ![0, 3, 0, 3] (by decide) (by decide)
  rw [h]
  exact xval1 2

theorem v0_G : ((yOpen .G).v 0 : K) = YTuples.Q q₁ q₂ r := by
  have h : (yOpen .G).v 0 = base2.x 1 :=
    base2.tuple_zero 1 (Equiv.swap 0 1) ![0, 0, 4, 4] (by decide) (by decide)
  rw [h]
  exact xval2 1

theorem v0_τ : ((yOpen .τ).v 0 : K) = YTuples.τ r := by
  have h : (yOpen .τ).v 0 = base2.x 3 :=
    base2.tuple_zero 3 (Equiv.swap 0 3) ![0, 4, 1, 0] (by decide) (by decide)
  rw [h]
  exact xval2 3

theorem v0_q : ((yOpen .q).v 0 : K) = q₁ := by
  have h : (yOpen .q).v 0 = base3.x 0 :=
    base3.tuple_zero 0 (Equiv.refl _) ![0, 4, 3, 1] (by decide) (by decide)
  rw [h]
  exact xval3 0

theorem v0_u : ((yOpen .u).v 0 : K) = u := by
  have h : (yOpen .u).v 0 = base3.x 2 :=
    base3.tuple_zero 2 (Equiv.swap 0 2) ![2, 3, 0, 2] (by decide) (by decide)
  rw [h]
  exact xval3 2

local notation "κ" => yFieldAmbientMap

theorem ν_embed (a : YIdx) : κ (ν a) = (ψ a : K) * q₁ ^ 4 := by
  rw [ψ_coe]
  cases a
  · rw [v0_B]
    have := YTuples.uB q₁ q₂ u q₁_ne u_ne W₀_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_A]
    have := YTuples.uA q₁ u q₁_ne u_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_W]
    have := YTuples.uW q₁ u q₁_ne u_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_Q]
    have := YTuples.uQ q₁ q₂ r q₁_ne r_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_H]
    have := YTuples.uH q₁ q₂ r q₁_ne q₂_ne r_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_G]
    have := YTuples.uG q₁ q₂ r q₁_ne r_ne N₀_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_τ]
    have := YTuples.uτ q₁ r q₁_ne r_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this
  · rw [v0_q]
    have hne : q₁ ^ 4 ≠ 0 := pow_ne_zero 4 q₁_ne
    simp only [ν, map_one, yc, yn]
    rw [zpow_neg, zpow_ofNat, Nat.cast_one, one_mul, inv_mul_cancel₀ hne]
  · rw [v0_u]
    have := YTuples.uu q₁ u q₁_ne u_ne
    simpa [ν, yc, yn, map_div₀, κW, κN, ρ0, ρ1, ρ2, ρ3, zpow_neg, zpow_ofNat, map_ofNat] using this

theorem YOpen.v0_mem {i : Fin 4} (U : YOpen i) : U.v 0 ∈ U.A :=
  U.poly_le (Algebra.subset_adjoin (Set.mem_range_self 0))

theorem yOpen_inv_mem (a : YIdx) : ((yOpen a).v 0)⁻¹ ∈ (yOpen a).A := (yOpen a).v_inv

theorem zpow_mem_A (a : YIdx) (n : ℤ) : (yOpen a).v 0 ^ n ∈ (yOpen a).A := by
  cases n with
  | ofNat m => exact Subalgebra.pow_mem _ (YOpen.v0_mem _) m
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow]
    exact Subalgebra.pow_mem _ (yOpen_inv_mem a) _

theorem yc_inv_mem (a : YIdx) : ((yc a : L))⁻¹ ∈ (yOpen a).A := by
  have h5 : (5 : L) = 0 := CharP.cast_eq_zero L 5
  have h4 : ((4 : ℕ) : L)⁻¹ = ((4 : ℕ) : L) := by
    apply inv_eq_of_mul_eq_one_right
    push_cast
    linear_combination 3 * h5
  cases a <;> simp only [yc] <;> first
    | (rw [h4]; exact Subalgebra.natCast_mem _ 4)
    | simp [Subalgebra.one_mem]

theorem ψ_mem (a : YIdx) : ψ a ∈ (yOpen a).A :=
  Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (zpow_mem_A a _)

theorem ψ_inv_mem (a : YIdx) : (ψ a)⁻¹ ∈ (yOpen a).A := by
  rw [ψ, mul_inv, ← zpow_neg]
  exact Subalgebra.mul_mem _ (yc_inv_mem a) (zpow_mem_A a _)

theorem ψ_ne (a : YIdx) : ψ a ≠ 0 := by
  have h5 : (5 : L) = 0 := CharP.cast_eq_zero L 5
  have h4 : ((4 : ℕ) : L) ≠ 0 := by
    intro h
    have h' : (4 : L) = 0 := by exact_mod_cast h
    exact one_ne_zero (show (1 : L) = 0 by linear_combination h5 - h')
  apply mul_ne_zero
  · cases a <;> simp only [yc] <;> first | exact h4 | simp
  · exact zpow_ne_zero _ (yOpen a).v_ne

/-- Fifth powers of the local units are units of the invariant coordinate ring. -/
theorem ψ_fifth_mem (a : YIdx) (x : L) (hx : x ∈ (yOpen a).A) : x ^ 5 ∈ (yOpen a).kernel := by
  refine ((yOpen a).mem_kernel_iff _).mpr ⟨Subalgebra.pow_mem _ hx 5, fifth_power_in_M x⟩

/-- A rational line with the Jacobian factors as generators. -/
def IsCanonicalLine {𝓛 : Y.Modules} (F : RationalLine 𝓛.val) : Prop :=
  ∀ (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a))), (yOpen a).d ∉ q.asIdeal →
    F.IsGenerator (yAtlas.chartInclusion (chartOf a) q) (ν a)

/-- The fifth tensor powers are trivial. -/
theorem tensorPower_five_trivial {𝓛 : Y.Modules} (F : RationalLine 𝓛.val) (hF : IsCanonicalLine F)
    (m : ℕ) : Nonempty (structureSheafModule Y ≅ tensorPower 𝓛 (5 * m)) := by
  apply trivial_of_generators (powerLine F (5 * m)) ((ρ 0 ^ 4) ^ m)
  intro y
  obtain ⟨a, q, hd, rfl⟩ := y_open_cover y
  obtain ⟨f, hf⟩ := (yOpen a).exists_stalkMap q hd _ rfl
  let w : (yOpen a).kernel := ⟨(ψ a)⁻¹ ^ 5, ψ_fifth_mem a _ (ψ_inv_mem a)⟩
  let w' : (yOpen a).kernel := ⟨ψ a ^ 5, ψ_fifth_mem a _ (ψ_mem a)⟩
  have hww : w * w' = 1 := Subtype.ext (by
    change (ψ a)⁻¹ ^ 5 * ψ a ^ 5 = 1
    rw [← mul_pow, inv_mul_cancel₀ (ψ_ne a), one_pow])
  have hunit : IsUnit (f w) := IsUnit.of_mul_eq_one (f w') (by rw [← map_mul, hww, map_one])
  refine ⟨ν a ^ (5 * m), f w ^ m, powerLine_isGenerator F (hF a q hd) _, hunit.pow m, ?_⟩
  apply yFieldAmbientMap_injective
  rw [map_mul, map_pow, map_pow, map_pow, map_pow, yStalkAmbientMap_algebraMap, map_pow, hf, ρ0,
    ν_embed]
  have hw : ((w : L) : K) = ((ψ a)⁻¹ ^ 5 : L) := rfl
  rw [hw, show (((ψ a)⁻¹ ^ 5 : L) : K) = (((ψ a : K))⁻¹) ^ 5 by simp, YTuples.z]
  have hψ : (ψ a : K) ≠ 0 := fun h ↦ ψ_ne a (Subtype.ext h)
  rw [pow_mul (_ * _) 5 m, ← mul_pow]
  congr 1
  field_simp

/-- A function of `L` regular at every prime of a chart of `Y` belongs to the chart of `S`. -/
theorem mem_chart_of_locally (i : Fin 4) (x : L)
    (h : ∀ p : PrimeSpectrum (yAtlas.ring i), ∃ s : yAtlas.ring i, s ∉ p.asIdeal ∧
      ((s : M) : L) * x ∈ quotientAtlas.ring i) : x ∈ quotientAtlas.ring i := by
  let I : Ideal (yAtlas.ring i) :=
    { carrier := {s | ((s : M) : L) * x ∈ quotientAtlas.ring i}
      zero_mem' := by
        change ((0 : L)) * x ∈ quotientAtlas.ring i
        rw [zero_mul]
        exact Subalgebra.zero_mem _
      add_mem' := by
        intro a b ha hb
        change (((a : M) : L) + ((b : M) : L)) * x ∈ quotientAtlas.ring i
        rw [add_mul]
        exact Subalgebra.add_mem _ ha hb
      smul_mem' := by
        intro c a ha
        change (((c : M) : L) * ((a : M) : L)) * x ∈ quotientAtlas.ring i
        rw [mul_assoc]
        exact Subalgebra.mul_mem _ c.property ha }
  by_cases htop : I = ⊤
  · have h1 : (1 : yAtlas.ring i) ∈ I := htop ▸ Submodule.mem_top
    change ((1 : L)) * x ∈ quotientAtlas.ring i at h1
    rwa [one_mul] at h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I htop
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime⟩
    exact (hs (hle hsx)).elim

/-- Clearing the denominators of a product of a stalk element and a function on a principal open. -/
theorem clear_product {i : Fin 4} (U : YOpen i) (q : PrimeSpectrum (yAtlas.ring i))
    (hd : U.d ∉ q.asIdeal) (y : Y) (hy : y = yAtlas.chartInclusion i q)
    (v : Y.presheaf.stalk y) (x : L) (hx : x ∈ U.A) (T : L)
    (hT : (T : K) = yStalkAmbientMap y v * (x : K)) :
    ∃ s : yAtlas.ring i, s ∉ q.asIdeal ∧ ((s : M) : L) * T ∈ quotientAtlas.ring i := by
  obtain ⟨r, s₀, hs₀, hrs⟩ := stalk_fraction i q y hy v
  obtain ⟨N, hN⟩ := U.clear x hx
  refine ⟨s₀ * U.d ^ N, ?_, ?_⟩
  · intro hm
    rcases q.isPrime.mem_or_mem hm with h | h
    · exact hs₀ h
    · exact hd ((q.isPrime.pow_mem_iff_mem N (by
        by_contra h0
        simp only [not_lt, nonpos_iff_eq_zero] at h0
        subst h0
        rw [pow_zero] at h
        exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one))).mp h)
  · have he : ((((s₀ * U.d ^ N : yAtlas.ring i)) : M) : L) * T =
        ((r : M) : L) * (x * ((U.d : M) : L) ^ N) := by
      apply Subtype.ext
      change (((s₀ : M) : L) : K) * ((((U.d : M) : L) : K)) ^ N * (T : K) =
        (((r : M) : L) : K) * ((x : K) * ((((U.d : M) : L) : K)) ^ N)
      rw [hT, ← hrs]
      ring
    rw [he]
    exact Subalgebra.mul_mem _ r.property hN

theorem clear_unit {i : Fin 4} (U : YOpen i) (q : PrimeSpectrum (yAtlas.ring i))
    (hd : U.d ∉ q.asIdeal) (y : Y) (hy : y = yAtlas.chartInclusion i q)
    (u : Y.presheaf.stalk y) (hu : IsUnit u) (x T : L) (hx : x ∈ U.A) (hxi : x⁻¹ ∈ U.A)
    (hT : (T : K) = yStalkAmbientMap y u * (x : K)) :
    (∃ s : yAtlas.ring i, s ∉ q.asIdeal ∧ ((s : M) : L) * T ∈ quotientAtlas.ring i) ∧
      (∃ s : yAtlas.ring i, s ∉ q.asIdeal ∧ ((s : M) : L) * T⁻¹ ∈ quotientAtlas.ring i) := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨clear_product U q hd y hy _ x hx T hT,
    clear_product U q hd y hy ((v⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) x⁻¹ hxi T⁻¹ ?_⟩
  have hvv : yStalkAmbientMap y (v : Y.presheaf.stalk y) *
      yStalkAmbientMap y ((v⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hc : ((T⁻¹ : L) : K) = (T : K)⁻¹ := rfl
  have hc' : ((x⁻¹ : L) : K) = (x : K)⁻¹ := rfl
  rw [hc, hc', hT, mul_inv]
  congr 1
  exact inv_eq_of_mul_eq_one_right hvv

theorem chart0_cover (p : PrimeSpectrum (yAtlas.ring (0 : Fin 4))) :
    (yOpen .A).d ∉ p.asIdeal ∨ (yOpen .B).d ∉ p.asIdeal ∨ (yOpen .W).d ∉ p.asIdeal := by
  obtain ⟨j, hj⟩ := certY_cover 0 p
  fin_cases j
  · exact Or.inl (by rw [d_A]; exact hj)
  · exact Or.inr (Or.inl (by rw [d_B]; exact hj))
  · exact Or.inr (Or.inr (by rw [d_W]; exact hj))

set_option maxHeartbeats 1500000 in
/-- A trivial tensor power of the canonical line forces the exponent to be divisible by five. -/
theorem five_dvd_of_trivial {𝓛 : Y.Modules} (F : RationalLine 𝓛.val) (hF : IsCanonicalLine F)
    (n : ℕ) (φ : structureSheafModule Y ≅ tensorPower 𝓛 n) : 5 ∣ n := by
  obtain ⟨h, hh⟩ := generators_of_trivial φ (powerLine F n)
  let hM : M := yFunctionFieldEquiv h
  let hL : L := hM
  have hκ : κ h = (hL : K) := rfl
  let g : L := x3 0
  have hg : (g : K) = q₁ := ConeRing.invariantCoordinates_coe 0
  have hg0 : g ≠ 0 := fun h0 ↦ q₁_ne (by rw [← hg, h0]; rfl)
  let Ψ : L := hL / g ^ (4 * n)
  -- The local description of `Ψ`.
  have hlocal (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a))) (hd : (yOpen a).d ∉ q.asIdeal) :
      ∃ (u : Y.presheaf.stalk (yAtlas.chartInclusion (chartOf a) q)), IsUnit u ∧
        (Ψ : K) = yStalkAmbientMap _ u * (ψ a : K) ^ n := by
    obtain ⟨u, hu, he⟩ := hh _ _ (powerLine_isGenerator F (hF a q hd) n)
    refine ⟨u, hu, ?_⟩
    have hk := congrArg κ he
    rw [map_mul, map_pow, yStalkAmbientMap_algebraMap, ν_embed, hκ] at hk
    have hq : (q₁ : K) ≠ 0 := q₁_ne
    have hΨ : (Ψ : K) = (hL : K) / q₁ ^ (4 * n) := by
      rw [← hg]
      simp [Ψ]
    rw [hΨ, hk, mul_pow, ← pow_mul]
    field_simp
  have hreg (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a))) (hd : (yOpen a).d ∉ q.asIdeal) :
      (∃ s : yAtlas.ring (chartOf a), s ∉ q.asIdeal ∧
        ((s : M) : L) * Ψ ∈ quotientAtlas.ring (chartOf a)) ∧
      (∃ s : yAtlas.ring (chartOf a), s ∉ q.asIdeal ∧
        ((s : M) : L) * Ψ⁻¹ ∈ quotientAtlas.ring (chartOf a)) := by
    obtain ⟨u, hu, he⟩ := hlocal a q hd
    refine clear_unit (yOpen a) q hd _ rfl u hu (ψ a ^ n) Ψ (Subalgebra.pow_mem _ (ψ_mem a) n) ?_ ?_
    · rw [← inv_pow]
      exact Subalgebra.pow_mem _ (ψ_inv_mem a) n
    · simpa using he
  have hreg0 (p : PrimeSpectrum (yAtlas.ring (0 : Fin 4))) :
      (∃ s : yAtlas.ring (0 : Fin 4), s ∉ p.asIdeal ∧
        ((s : M) : L) * Ψ ∈ quotientAtlas.ring (0 : Fin 4)) ∧
      (∃ s : yAtlas.ring (0 : Fin 4), s ∉ p.asIdeal ∧
        ((s : M) : L) * Ψ⁻¹ ∈ quotientAtlas.ring (0 : Fin 4)) := by
    rcases chart0_cover p with h | h | h
    · exact hreg .A p h
    · exact hreg .B p h
    · exact hreg .W p h
  have hmem : Ψ ∈ quotientAtlas.ring (0 : Fin 4) :=
    mem_chart_of_locally 0 Ψ fun p ↦ (hreg0 p).1
  have hmem' : Ψ⁻¹ ∈ quotientAtlas.ring (0 : Fin 4) :=
    mem_chart_of_locally 0 Ψ⁻¹ fun p ↦ (hreg0 p).2
  -- `Ψ` is nonzero, using any point.
  have hh0 : h ≠ 0 := by
    obtain ⟨a, q, hd, -⟩ := y_open_cover yRefPoint
    obtain ⟨hc, -⟩ := powerLine_isGenerator F (hF a q hd) n
    obtain ⟨u, hu, he⟩ := hh _ _ (powerLine_isGenerator F (hF a q hd) n)
    rw [he]
    refine mul_ne_zero ?_ hc
    intro h0
    have hu0 : u = 0 := IsFractionRing.injective (Y.presheaf.stalk _) Y.functionField (by
      rw [h0, map_zero])
    rw [hu0] at hu
    exact not_isUnit_zero hu
  have hL0 : hL ≠ 0 := by
    intro h0
    apply hh0
    apply yFieldAmbientMap_injective
    rw [hκ, h0, map_zero]
    rfl
  have hΨ0 : Ψ ≠ 0 := div_ne_zero hL0 (pow_ne_zero _ hg0)
  -- `Ψ` is a unit on the chart, so it is a scalar of weight zero.
  have hunit : IsUnit (⟨Ψ, hmem⟩ : invariantChartRing 0) := by
    refine ⟨⟨⟨Ψ, hmem⟩, ⟨Ψ⁻¹, hmem'⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hΨ0)
    · exact Subtype.ext (inv_mul_cancel₀ hΨ0)
  obtain ⟨c, -, hc⟩ := invariant_chart_unit_constant 0 ⟨Ψ, hmem⟩ hunit
  have hcL : algebraMap ell L c = Ψ := congrArg Subtype.val hc
  have hE0 : invariantEuler Ψ = 0 := by
    rw [← hcL]
    exact invariantEuler.map_algebraMap c
  -- But `Ψ` has weight `4 n`.
  have hhL : invariantEuler hL = ((0 : ℤ) : L) * hL := by
    have : invariantEuler hL = 0 := hM.property
    rw [this]
    simp
  have hgE : invariantEuler g = ((-1 : ℤ) : L) * g := x3_euler 0
  have hEΨ := euler_div_pow hL g hg0 0 (-1) hhL hgE (4 * n)
  rw [show hL / g ^ (4 * n) = Ψ from rfl, hE0] at hEΨ
  have hzero := (mul_eq_zero.mp hEΨ.symm).resolve_right hΨ0
  have hdvd := (CharP.intCast_eq_zero_iff L 5 _).mp hzero
  have h5 : (5 : ℕ) ∣ 4 * n := by
    have : ((5 : ℕ) : ℤ) ∣ ((4 * n : ℕ) : ℤ) := by
      convert hdvd using 1
      push_cast
      ring
    exact Int.natCast_dvd_natCast.mp this
  exact (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 5 4)).mp h5

/-- The exact order of the top-form line, for every sheaf isomorphic to it. -/
theorem tensorPower_trivial_iff {𝓛 : Y.Modules} (e : 𝓛 ≅ yTop) (n : ℕ) :
    Nonempty (tensorPower 𝓛 n ≅ structureSheafModule Y) ↔ 5 ∣ n := by
  let F : RationalLine 𝓛.val := RationalLine.ofHom e.hom.val yTopLine
  have hiso : IsIso e.hom.val := inferInstanceAs (IsIso ((SheafOfModules.forget _).map e.hom))
  have hF : IsCanonicalLine F := fun a q hd ↦
    RationalLine.ofHom_isGenerator e.hom.val yTopLine (yTop_isGenerator a q hd)
  constructor
  · rintro ⟨φ⟩
    exact five_dvd_of_trivial F hF n φ.symm
  · rintro ⟨m, rfl⟩
    obtain ⟨φ⟩ := tensorPower_five_trivial F hF m
    exact ⟨φ.symm⟩

end
end Eff

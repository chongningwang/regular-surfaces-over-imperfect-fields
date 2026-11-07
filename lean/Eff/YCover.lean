import Eff.YBases

/-! # The principal opens covering the second quotient, and its regularity -/

namespace Eff

open Red61 Red61.Fields Red61.Charts Red61.Contraction Red61.PolynomialInvariants
  Red61.FieldLocalization Red61.AffineGluing Red61.FrobeniusDescent Red61.LocalCoordinates
  AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem yRing_ext {i : Fin 4} {x y : yAtlas.ring i}
    (h : (((x : M) : L) : K) = (((y : M) : L) : K)) : x = y := by
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  exact h

theorem x0_mem (k : Fin 4) : x0 k ∈ quotientAtlas.ring (0 : Fin 4) :=
  base0.poly_le (Algebra.subset_adjoin (Set.mem_range_self k))

theorem x2_mem (k : Fin 4) : x2 k ∈ quotientAtlas.ring (2 : Fin 4) :=
  base2.poly_le (Algebra.subset_adjoin (Set.mem_range_self k))

theorem x1_one_mem : x1 1 ∈ quotientAtlas.ring (1 : Fin 4) := by
  change (x1 1 : K) ∈ contractedAtlas.ring (1 : Fin 4)
  rw [x1_one]
  exact certificate_mem (1 : Fin 4) (0 : Fin 3)

theorem x1_two_mem : x1 2 ∈ quotientAtlas.ring (1 : Fin 4) := by
  change (x1 2 : K) ∈ contractedAtlas.ring (1 : Fin 4)
  rw [x1_two]
  exact certificate_mem (1 : Fin 4) (1 : Fin 3)

/-- The nine principal opens. -/
inductive YIdx
  | B | A | W | Q | H | G | τ | q | u
  deriving DecidableEq

def chartOf : YIdx → Fin 4
  | .B | .A | .W => 0
  | .Q | .H => 1
  | .G | .τ => 2
  | .q | .u => 3

def yOpen : (a : YIdx) → YOpen (chartOf a)
  | .B => base0.toOpen 1 (Equiv.swap 0 1) ![0, 0, 2, 3] (by decide) (by decide)
      (by decide) (by decide) (x0_mem 1)
  | .A => base0.toOpen 2 (Equiv.swap 0 2) ![0, 3, 0, 4] (by decide) (by decide)
      (by decide) (by decide) (x0_mem 2)
  | .W => base0.toOpen 3 (Equiv.swap 0 3) ![0, 2, 4, 0] (by decide) (by decide)
      (by decide) (by decide) (x0_mem 3)
  | .Q => base1.toOpen 1 (Equiv.swap 0 1) ![0, 0, 2, 1] (by decide) (by decide)
      (by decide) (by decide) x1_one_mem
  | .H => base1.toOpen 2 (Equiv.swap 0 2) ![0, 3, 0, 3] (by decide) (by decide)
      (by decide) (by decide) x1_two_mem
  | .G => base2.toOpen 1 (Equiv.swap 0 1) ![0, 0, 4, 4] (by decide) (by decide)
      (by decide) (by decide) (x2_mem 1)
  | .τ => base2.toOpen 3 (Equiv.swap 0 3) ![0, 4, 1, 0] (by decide) (by decide)
      (by decide) (by decide) (x2_mem 3)
  | .q => base3.toOpen 0 (Equiv.refl _) ![0, 4, 3, 1] (by decide) (by decide)
      (by decide) (by decide) (x3_mem 0)
  | .u => base3.toOpen 2 (Equiv.swap 0 2) ![2, 3, 0, 2] (by decide) (by decide)
      (by decide) (by decide) (x3_mem 2)

/-- The fifth powers of the certificates generate the unit ideal of each chart of `Y`. -/
def certY (i : Fin 4) (j : Fin 3) : yAtlas.ring i := yFrob i ⟨certificateValue i j, certificate_mem i j⟩

theorem certY_cover (i : Fin 4) (p : PrimeSpectrum (yAtlas.ring i)) :
    ∃ j, certY i j ∉ p.asIdeal := by
  by_contra! h
  let a (j : Fin 3) : contractedAtlas.ring i := ⟨coverCoefficient i j, coverCoefficient_mem i j⟩
  let b (j : Fin 3) : contractedAtlas.ring i := ⟨certificateValue i j, certificate_mem i j⟩
  have hs : ∑ j, a j * b j = 1 := Subtype.ext (by simpa [a, b] using cover_identity i)
  have hf := congrArg (yFrob i) hs
  rw [map_sum, map_one] at hf
  apply p.isPrime.ne_top
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← hf]
  exact Ideal.sum_mem _ fun j _ ↦ by
    rw [map_mul]
    exact p.asIdeal.mul_mem_left _ (h j)

theorem d_B : (yOpen .B).d = (certY 0 1 : yAtlas.ring (0 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * (B) ^ 5 = (B) ^ 5
  rw [one_mul]

theorem d_A : (yOpen .A).d = (certY 0 0 : yAtlas.ring (0 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * (A) ^ 5 = (A) ^ 5
  rw [one_mul]

theorem d_W : (yOpen .W).d = (certY 0 2 : yAtlas.ring (0 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * (W) ^ 5 = (W) ^ 5
  rw [one_mul]

theorem d_τ : (yOpen .τ).d = (certY 2 0 : yAtlas.ring (2 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * (y₂ 5) ^ 5 = (y₂ 5) ^ 5
  rw [one_mul]

theorem d_u : (yOpen .u).d = (certY 3 0 : yAtlas.ring (3 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * ((x3 2 : L) : K) ^ 5 = U ^ 5
  rw [ConeRing.invariantCoordinates_coe 2, one_mul]
  rfl

theorem d_q : (yOpen .q).d = (certY 3 1 : yAtlas.ring (3 : Fin 4)) := by
  apply yRing_ext
  change (1 : K) * ((x3 0 : L) : K) ^ 5 = q₁ ^ 5
  rw [ConeRing.invariantCoordinates_coe 0, one_mul]
  rfl

theorem d_G_coe : ((((yOpen .G).d : yAtlas.ring (2 : Fin 4)) : M) : L).1 = lastQ ^ 5 := by
  change (1 : K) * lastQ ^ 5 = lastQ ^ 5
  rw [one_mul]

/-- Certificate elements of `Y` have vanishing images under Frobenius when they are zero. -/
theorem certY_zero (i : Fin 4) (h : certificateValue i 2 = 0) : certY i 2 = 0 := by
  apply yRing_ext
  change (certificateValue i 2) ^ 5 = 0
  rw [h, zero_pow (by decide)]

theorem lastQ_mem : lastQ ∈ contractedAtlas.ring (2 : Fin 4) := x2_mem 1
theorem lastZ_mem : lastZ ∈ contractedAtlas.ring (2 : Fin 4) := x2_mem 2
theorem lastτ_mem : y₂ 5 ∈ contractedAtlas.ring (2 : Fin 4) := x2_mem 3

/-- The conclusion of the cover, over a given chart point of `Y`. -/
def InOpen {i : Fin 4} (p : PrimeSpectrum (yAtlas.ring i)) : Prop :=
  ∃ (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a))),
    (yOpen a).d ∉ q.asIdeal ∧
      yAtlas.chartInclusion (chartOf a) q = yAtlas.chartInclusion i p

set_option maxHeartbeats 1000000 in
theorem cert22 : certificateValue 2 2 = 0 := by
  show (![y₂ 5, q₁, 0] : Fin 3 → K) 2 = 0
  rfl

theorem cover_zero (p : PrimeSpectrum (yAtlas.ring (0 : Fin 4))) : InOpen p := by
  obtain ⟨j, hj⟩ := certY_cover 0 p
  fin_cases j
  · exact ⟨.A, p, by rw [d_A]; exact hj, rfl⟩
  · exact ⟨.B, p, by rw [d_B]; exact hj, rfl⟩
  · exact ⟨.W, p, by rw [d_W]; exact hj, rfl⟩

theorem cover_three (p : PrimeSpectrum (yAtlas.ring (3 : Fin 4))) : InOpen p := by
  obtain ⟨j, hj⟩ := certY_cover 3 p
  fin_cases j
  · exact ⟨.u, p, by rw [d_u]; exact hj, rfl⟩
  · exact ⟨.q, p, by rw [d_q]; exact hj, rfl⟩
  · have h0 : certY 3 2 = 0 := certY_zero 3 rfl
    exact (hj (show certY 3 2 ∈ p.asIdeal from h0 ▸ p.asIdeal.zero_mem)).elim

theorem cover_two (p : PrimeSpectrum (yAtlas.ring (2 : Fin 4))) : InOpen p := by
  obtain ⟨j, hj⟩ := certY_cover 2 p
  fin_cases j
  · exact ⟨.τ, p, by rw [d_τ]; exact hj, rfl⟩
  · by_cases hτ : (yOpen .τ).d ∈ p.asIdeal
    · refine ⟨.G, p, ?_, rfl⟩
      intro hG
      let dG : yAtlas.ring (2 : Fin 4) := (yOpen .G).d
      let dτ : yAtlas.ring (2 : Fin 4) := (yOpen .τ).d
      have he : (certY 2 1 : yAtlas.ring (2 : Fin 4)) = dG -
          dτ * yFrob 2 ⟨lastZ ^ 3, (contractedAtlas.ring (2 : Fin 4)).pow_mem lastZ_mem 3⟩ := by
        apply yRing_ext
        change q₁ ^ 5 = (((dG : yAtlas.ring (2 : Fin 4)) : M) : L).1 -
          (1 * (y₂ 5) ^ 5) * (lastZ ^ 3) ^ 5
        rw [show ((dG : yAtlas.ring (2 : Fin 4)) : M).1.1 = lastQ ^ 5 from d_G_coe, q₁_eq2,
          sub_pow_char (p := 5), mul_pow, one_mul]
      have hm : (certY 2 1 : yAtlas.ring (2 : Fin 4)) ∈ p.asIdeal := by
        rw [he]
        exact p.asIdeal.sub_mem hG (p.asIdeal.mul_mem_right _ hτ)
      exact hj hm
    · exact ⟨.τ, p, hτ, rfl⟩
  · have h0 : certY 2 2 = 0 := certY_zero 2 cert22
    have hm : certY 2 2 ∈ p.asIdeal := by
      rw [h0]
      exact p.asIdeal.zero_mem
    exact (hj hm).elim

theorem h₀_identity : h₀ - 3 * c₂ * y₂ 3 = 1 := by
  rw [h₀_eq]
  ring

theorem y₂3_mem : y₂ 3 ∈ contractedAtlas.ring (1 : Fin 4) := y₂_mem 3

/-- Moving between charts of `Y` along an overlap of the contracted atlas. -/
theorem y_chart_move (i j : Fin 4) (d : contractedAtlas.ring i)
    (hloc : letI := inclusionAlgebra (show contractedAtlas.ring i ≤
        contractedAtlas.ring i ⊔ contractedAtlas.ring j from le_sup_left);
      IsLocalization.Away d ↥(contractedAtlas.ring i ⊔ contractedAtlas.ring j))
    (p : PrimeSpectrum (yAtlas.ring i)) (hd : yFrob i d ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (yAtlas.ring j),
      yAtlas.chartInclusion j q = yAtlas.chartInclusion i p := by
  have h1 := localization_congr
    (fixed_mono L (AtlasDescent.restricted_le_pair (R := ell) contractedAtlas i j)) le_sup_left
    (AtlasDescent.pair_eq_sup (R := ell) contractedAtlas L 5 field_fifth_power_invariant i j) _
    (fixed_isLocalization L 5 field_fifth_power_invariant
      (AtlasDescent.restricted_le_pair (R := ell) contractedAtlas i j) d hloc)
  have h2 := localization_congr
    (fixed_mono M (AtlasDescent.restricted_le_pair (R := ell) quotientAtlas i j)) le_sup_left
    (AtlasDescent.pair_eq_sup (R := ell) quotientAtlas M 5 fifth_power_in_M i j) _
    (fixed_isLocalization M 5 fifth_power_in_M
      (AtlasDescent.restricted_le_pair (R := ell) quotientAtlas i j) _ h1)
  refine yAtlas.point_in_chart_of_localization i j _ h2 p ?_
  intro hm
  apply hd
  have hm' : (yFrob i d) ^ 5 ∈ p.asIdeal := by
    convert hm using 1
    apply yRing_ext
    rfl
  exact (p.isPrime.pow_mem_iff_mem 5 (by decide)).mp hm'

theorem d_Q : (yOpen .Q).d = (middleD * certY 1 0 : yAtlas.ring (1 : Fin 4)) := by
  apply yRing_ext
  change h₀ ^ 5 * ((x1 1 : L) : K) ^ 5 = h₀ ^ 5 * middleQ ^ 5
  rw [x1_one]

theorem d_H : (yOpen .H).d = (middleD * certY 1 1 : yAtlas.ring (1 : Fin 4)) := by
  apply yRing_ext
  change h₀ ^ 5 * ((x1 2 : L) : K) ^ 5 = h₀ ^ 5 * middleH ^ 5
  rw [x1_two]

theorem middleJ_identity : middleJ * h₀ ^ 2 = middleH * (y₂ 3) ^ 2 := by
  rw [middleJ, middleH, h₀_eq]
  ring

def hh₁ : contractedAtlas.ring (1 : Fin 4) := ⟨h₀, h₀_mem_chart⟩
def η₁ : contractedAtlas.ring (1 : Fin 4) := ⟨y₂ 3, y₂3_mem⟩
def s₁' : contractedAtlas.ring (1 : Fin 4) :=
  ⟨3 * c₂, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 3) (contracted_c₂_mem _)⟩

theorem hh_identity : hh₁ - s₁' * η₁ = 1 := Subtype.ext h₀_identity

theorem middle_or_eta (p : PrimeSpectrum (yAtlas.ring (1 : Fin 4))) :
    middleD ∉ p.asIdeal ∨ yFrob 1 η₁ ∉ p.asIdeal := by
  by_contra! hc
  have hf := congrArg (yFrob 1) hh_identity
  rw [map_sub, map_mul, map_one] at hf
  apply p.isPrime.ne_top
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← hf]
  exact p.asIdeal.sub_mem hc.1 (p.asIdeal.mul_mem_left _ hc.2)

theorem certJ_identity : (certY 1 2 : yAtlas.ring (1 : Fin 4)) * middleD ^ 2 =
    certY 1 1 * (yFrob 1 η₁) ^ 2 := by
  apply yRing_ext
  change middleJ ^ 5 * (h₀ ^ 5) ^ 2 = middleH ^ 5 * ((y₂ 3) ^ 5) ^ 2
  have := congrArg (fun z : K ↦ z ^ 5) middleJ_identity
  simp only [mul_pow] at this
  calc
    _ = middleJ ^ 5 * (h₀ ^ 2) ^ 5 := by ring
    _ = _ := this.trans (by ring)

theorem cover_one_open (p : PrimeSpectrum (yAtlas.ring (1 : Fin 4))) (hd : middleD ∉ p.asIdeal) :
    (certY 1 0 : yAtlas.ring (1 : Fin 4)) ∉ p.asIdeal ∨ certY 1 1 ∉ p.asIdeal := by
  by_contra! hc
  obtain ⟨j, hj⟩ := certY_cover 1 p
  have h0 : (certY 1 2 : yAtlas.ring (1 : Fin 4)) ∈ p.asIdeal := by
    have hm : (certY 1 2 : yAtlas.ring (1 : Fin 4)) * middleD ^ 2 ∈ p.asIdeal := by
      rw [certJ_identity]
      exact p.asIdeal.mul_mem_right _ hc.2
    rcases p.isPrime.mem_or_mem hm with h | h
    · exact h
    · exact (hd ((p.isPrime.pow_mem_iff_mem 2 (by decide)).mp h)).elim
  fin_cases j
  · exact hj hc.1
  · exact hj hc.2
  · exact hj h0

theorem cover_one_prod (p : PrimeSpectrum (yAtlas.ring (1 : Fin 4))) (hd : middleD ∉ p.asIdeal)
    {z : yAtlas.ring (1 : Fin 4)} (hz : z ∉ p.asIdeal) : middleD * z ∉ p.asIdeal := by
  intro hm
  exact (p.isPrime.mem_or_mem hm).elim hd hz

theorem cover_one (p : PrimeSpectrum (yAtlas.ring (1 : Fin 4))) : InOpen p := by
  rcases middle_or_eta p with hd | hη
  · rcases cover_one_open p hd with h | h
    · exact ⟨.Q, p, by rw [d_Q]; exact cover_one_prod p hd h, rfl⟩
    · exact ⟨.H, p, by rw [d_H]; exact cover_one_prod p hd h, rfl⟩
  · obtain ⟨q, hq⟩ := y_chart_move 1 2 η₁ (overlap_isLocalization 1 0) p hη
    obtain ⟨a, q', hd, he⟩ := cover_two q
    exact ⟨a, q', hd, he.trans hq⟩

/-- Every point of `Y` lies on one of the nine principal opens. -/
theorem y_open_cover (y : Y) : ∃ (a : YIdx) (q : PrimeSpectrum (yAtlas.ring (chartOf a))),
    (yOpen a).d ∉ q.asIdeal ∧ yAtlas.chartInclusion (chartOf a) q = y := by
  obtain ⟨i, p, rfl⟩ := yAtlas.chartInclusion_cover y
  change Fin 4 at i
  fin_cases i
  · exact cover_zero p
  · exact cover_one p
  · exact cover_two p
  · exact cover_three p

theorem YOpen.stalk_regular {i : Fin 4} (U : YOpen i) (q : PrimeSpectrum (yAtlas.ring i))
    (hd : U.d ∉ q.asIdeal) :
    IsRegularLocalRing (Y.presheaf.stalk (yAtlas.chartInclusion i q)) := by
  have := U.atPrime_regular q hd
  have h : IsRegularLocalRing ((yAtlas.chart i).presheaf.stalk q) :=
    IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (CommRingCat.of (yAtlas.ring i)) q).symm.commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((yAtlas.chartInclusion i).stalkMap q)).symm.commRingCatIsoToRingEquiv

/-- Every local ring of the second quotient is regular. -/
theorem y_stalk_regular (y : Y) : IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨a, q, hd, rfl⟩ := y_open_cover y
  exact (yOpen a).stalk_regular q hd

end
end Eff

import Geonormal.P11.Atlas
import Geonormal.P11.BChart
import SurfaceLib.Projective.AtlasModel
import Mathlib.Algebra.MonoidAlgebra.Grading

/-! # The characteristic-11 surface is projective

`X` is the `Proj` of the subalgebra of `L[T]` generated in degree one by sections of
`H = 6S_∞ + 13F_∞`, where `S_∞` is the section at infinity and `F_∞` the fibre over `u = ∞`:

* the monomials `a^i b^j u^l T` for twenty lattice points `(i, j, l)` of
  `{2i + 3j ≤ 6, 4i + 6j + l ≤ 13}`;
* the fibre sections `σ T`, `ρa³ T`, `ρa³u T` and `u¹¹θ_k T`.

The four charts `A, B, D, P` are the degree-zero localizations at `1, a³, a³u, u¹³`. A monomial
divided by a vertex section is a monomial in the coordinates of the chart. The cover condition
uses toric relations for the monomials with `j = 0`, the relation `b² = a³ + u` for the others,
and `11`th powers for the fibre sections.
-/

namespace Geonormal.P11

open Red61 Red61.AffineGluing AlgebraicGeometry SurfaceLib.Projective
open scoped DirectSum

noncomputable section

/-! ## Laurent monomials in `a, b, u` -/

abbrev Exp := ℤ × ℤ × ℤ

/-- The Laurent monomial `a^i b^j u^l`. -/
def monoL (v : Exp) : L := aL ^ v.1 * bL ^ v.2.1 * uL ^ v.2.2

theorem monoL_ne_zero (v : Exp) : monoL v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (zpow_ne_zero _ aL_ne_zero) (zpow_ne_zero _ bL_ne_zero))
    (zpow_ne_zero _ uL_ne_zero)

theorem monoL_add (v w : Exp) : monoL (v + w) = monoL v * monoL w := by
  simp only [monoL, Prod.fst_add, Prod.snd_add, zpow_add₀ aL_ne_zero, zpow_add₀ bL_ne_zero,
    zpow_add₀ uL_ne_zero]
  ring

theorem monoL_zero : monoL 0 = 1 := by simp [monoL]

theorem monoL_nsmul (n : ℕ) (v : Exp) : monoL (n • v) = monoL v ^ n := by
  induction n with
  | zero => simp [monoL_zero]
  | succ n ih => rw [succ_nsmul, monoL_add, ih, pow_succ]

theorem monoL_neg (v : Exp) : monoL (-v) = (monoL v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← monoL_add, neg_add_cancel, monoL_zero]

theorem monoL_sub (v w : Exp) : monoL (v - w) = monoL v / monoL w := by
  rw [sub_eq_add_neg, monoL_add, monoL_neg, div_eq_mul_inv]

/-- `b² = a³ + u` on monomials. -/
theorem monoL_b_sq (v : Exp) : monoL (v + (0, 2, 0)) = monoL (v + (3, 0, 0)) + monoL (v + (0, 0, 1)) := by
  rw [monoL_add, monoL_add, monoL_add, ← mul_add]
  congr 1
  simp [monoL, uL]

/-! ## Monomial coordinates of the charts -/

/-- The three coordinate monomials of each chart: `a, b, u`; `α, β, u`; `α″, β″, w`; `a″, b″, w`. -/
def coordVec : Fin 4 → Fin 3 → Exp := ![
  ![(1, 0, 0), (0, 1, 0), (0, 0, 1)],
  ![(-1, 0, 0), (-2, 1, 0), (0, 0, 1)],
  ![(-1, 0, 4), (-2, 1, 2), (0, 0, -1)],
  ![(1, 0, -4), (0, 1, -6), (0, 0, -1)]]

/-- The coordinates of an exponent vector in the coordinate monomials of a chart. -/
def chartCoord : Fin 4 → Exp → Exp := ![
  fun v ↦ v,
  fun v ↦ (-v.1 - 2 * v.2.1, v.2.1, v.2.2),
  fun v ↦ (-v.1 - 2 * v.2.1, v.2.1, -4 * v.1 - 6 * v.2.1 - v.2.2),
  fun v ↦ (v.1, v.2.1, -4 * v.1 - 6 * v.2.1 - v.2.2)]

theorem chartCoord_spec (i : Fin 4) (v : Exp) :
    (chartCoord i v).1 • coordVec i 0 + (chartCoord i v).2.1 • coordVec i 1 +
      (chartCoord i v).2.2 • coordVec i 2 = v := by
  obtain ⟨v1, v2, v3⟩ := v
  fin_cases i <;> simp [chartCoord, coordVec] <;> ring_nf <;> trivial

theorem coordVec_mem (i : Fin 4) (m : Fin 3) : monoL (coordVec i m) ∈ chartRing i := by
  have ha := aL_ne_zero
  have hb := bL_ne_zero
  have hu := uL_ne_zero
  fin_cases i <;> fin_cases m
  · simpa [monoL, coordVec, chartRing] using aL_mem_A
  · simpa [monoL, coordVec, chartRing] using bL_mem_A
  · simpa [monoL, coordVec, chartRing] using uL_mem_A
  · simpa [monoL, coordVec, chartRing, αL] using αL_mem_B
  · have : monoL ((-2, 1, 0) : Exp) = βL := by simp [monoL, βL] <;> field_simp
    simpa [coordVec, chartRing, this] using βL_mem_B
  · simpa [monoL, coordVec, chartRing] using uL_mem_B
  · have : monoL ((-1, 0, 4) : Exp) = αD := by simp [monoL, αD] <;> field_simp
    simpa [coordVec, chartRing, this] using αD_mem_D
  · have : monoL ((-2, 1, 2) : Exp) = βD := by simp [monoL, βD] <;> field_simp
    simpa [coordVec, chartRing, this] using βD_mem_D
  · have : monoL ((0, 0, -1) : Exp) = wL := by simp [monoL, wL]
    simpa [coordVec, chartRing, this] using wL_mem_D
  · have : monoL ((1, 0, -4) : Exp) = aP := by simp [monoL, aP, wL] <;> field_simp
    simpa [coordVec, chartRing, this] using aP_mem_P
  · have : monoL ((0, 1, -6) : Exp) = bP := by simp [monoL, bP, wL] <;> field_simp
    simpa [coordVec, chartRing, this] using bP_mem_P
  · have : monoL ((0, 0, -1) : Exp) = wL := by simp [monoL, wL]
    simpa [coordVec, chartRing, this] using wL_mem_P

/-- Nonnegative coordinates in chart `i`. -/
def NonnegIn (i : Fin 4) (v : Exp) : Prop :=
  0 ≤ (chartCoord i v).1 ∧ 0 ≤ (chartCoord i v).2.1 ∧ 0 ≤ (chartCoord i v).2.2

instance (i : Fin 4) (v : Exp) : Decidable (NonnegIn i v) := by unfold NonnegIn; infer_instance

theorem monoL_zsmul (n : ℤ) (v : Exp) (hn : 0 ≤ n) : monoL (n • v) = monoL v ^ n.toNat := by
  rw [← monoL_nsmul]
  congr 1
  rw [← natCast_zsmul, Int.toNat_of_nonneg hn]

/-- A monomial with nonnegative coordinates in chart `i` lies in its ring. -/
theorem monoL_mem {i : Fin 4} {v : Exp} (h : NonnegIn i v) : monoL v ∈ chartRing i := by
  rw [← chartCoord_spec i v, monoL_add, monoL_add, monoL_zsmul _ _ h.1, monoL_zsmul _ _ h.2.1,
    monoL_zsmul _ _ h.2.2]
  exact (chartRing i).mul_mem ((chartRing i).mul_mem ((chartRing i).pow_mem (coordVec_mem i 0) _)
    ((chartRing i).pow_mem (coordVec_mem i 1) _)) ((chartRing i).pow_mem (coordVec_mem i 2) _)

/-! ## The generators -/

/-- Twenty lattice points: the four vertices, the chart coordinates and the points needed for the
cover condition. -/
def monoPt : Fin 20 → Exp := ![(0, 0, 0), (3, 0, 0), (3, 0, 1), (0, 0, 13), (1, 0, 0), (2, 0, 0),
  (2, 0, 5), (0, 0, 2), (1, 0, 9), (0, 0, 1), (2, 0, 3), (0, 0, 7), (0, 0, 9), (0, 1, 0), (1, 1, 0),
  (1, 1, 3), (1, 1, 2), (0, 1, 4), (0, 1, 5), (0, 1, 7)]

/-- The vertices of the charts `A, B, D, P`: the sections `1, a³, a³u, u¹³`. -/
def vertex : Fin 4 → Exp := ![(0, 0, 0), (3, 0, 0), (3, 0, 1), (0, 0, 13)]

theorem monoPt_vertex (i : Fin 4) : monoPt (Fin.castLE (by norm_num) i) = vertex i := by
  fin_cases i <;> rfl

theorem mono_table (q : Fin 20) (i : Fin 4) : NonnegIn i (monoPt q - vertex i) := by
  fin_cases q <;> fin_cases i <;> decide

/-- The fibre sections `σ, ρa³, ρa³u` and `u¹¹θ_k`. -/
def fibValue : Fin 3 ⊕ Fin 11 → L :=
  Sum.elim ![σL, ρL * aL ^ 3, ρL * aL ^ 3 * uL] (fun n ↦ uL ^ 11 * θE n aL bL σL)

abbrev Gen := Fin 20 ⊕ (Fin 3 ⊕ Fin 11)

def genValue : Gen → L := Sum.elim (fun q ↦ monoL (monoPt q)) fibValue

/-! ## Relations in the coordinates of the charts -/

theorem aL_B : aL = 1 / αL := by simp [αL]
theorem bL_B : bL = βL / αL ^ 2 := by
  have := aL_ne_zero
  simp only [βL, αL]
  field_simp
theorem σL_B : σL = ρL - 2 * βL / αL := by
  have := aL_ne_zero
  simp only [ρL, βL, αL]
  field_simp
  ring
theorem βL_sq : βL ^ 2 = αL + uL * αL ^ 4 := by
  have := aL_ne_zero
  simp only [βL, αL, uL]
  field_simp
  ring

/-- `θ_n α` in the coordinates of `B`. -/
theorem θ_B (n : Fin 11) : θE n aL bL σL * αL = ΨE n uL αL βL ρL := by
  rw [aL_B, bL_B, σL_B]
  exact ΨE_ident n uL αL βL ρL αL_ne_zero βL_sq

/-- Closes an identity between explicit elements of `L`. -/
macro "lident" : tactic => `(tactic| ((try simp only [vertex, monoL, ρL, βL, αL, βD, αD, wL, aP,
  bP, sP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
  Matrix.head_cons, Matrix.tail_cons]) <;> (try simp) <;> (try field_simp) <;> (try ring) <;>
  (try simp)))

set_option maxHeartbeats 1000000 in
theorem ΨE_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 11) (u al be rh : R) :
    f (ΨE n u al be rh) = ΨE n (f u) (f al) (f be) (f rh) := by
  fin_cases n <;> simp [ΨE, Ψ0, Ψ1, Ψ2, Ψ3, Ψ4, Ψ5, Ψ6, Ψ7, Ψ8, Ψ9, Ψ10, map_ofNat]

theorem ΨE_mem {K : Type*} [CommRing K] (T : Subring K) (n : Fin 11) {u al be rh : K}
    (hu : u ∈ T) (hal : al ∈ T) (hbe : be ∈ T) (hrh : rh ∈ T) : ΨE n u al be rh ∈ T := by
  have h := ΨE_map T.subtype n ⟨u, hu⟩ ⟨al, hal⟩ ⟨be, hbe⟩ ⟨rh, hrh⟩
  simp only [Subring.coe_subtype] at h
  rw [← h]
  exact Subtype.prop _

theorem fib_div_mem (f : Fin 3 ⊕ Fin 11) (i : Fin 4) :
    fibValue f / monoL (vertex i) ∈ chartRing i := by
  have ha := aL_ne_zero
  have hb := bL_ne_zero
  have hu := uL_ne_zero
  have := αL_mem_B; have := βL_mem_B; have := ρL_mem_B; have := uL_mem_B
  have := αD_mem_D; have := βD_mem_D; have := ρL_mem_D; have := wL_mem_D
  have := aL_mem_A; have := bL_mem_A; have := σL_mem_A; have := uL_mem_A
  rcases f with f | n
  · fin_cases f <;> fin_cases i
    · show σL / monoL (vertex 0) ∈ chartA
      rw [show σL / monoL (vertex 0) = σL by lident]; exact σL_mem_A
    · show σL / monoL (vertex 1) ∈ chartB
      rw [show σL / monoL (vertex 1) = ρL * αL ^ 3 - 2 * βL * αL ^ 2 by lident]; subalg_mem
    · show σL / monoL (vertex 2) ∈ chartD
      rw [show σL / monoL (vertex 2) = ρL * αD ^ 3 * wL ^ 13 - 2 * βD * αD ^ 2 * wL ^ 11 by lident]
      subalg_mem
    · show σL / monoL (vertex 3) ∈ chartP
      rw [show σL / monoL (vertex 3) = sP * wL ^ 11 by lident]
      exact chartP.mul_mem sP_mem_P (chartP.pow_mem wL_mem_P _)
    · show ρL * aL ^ 3 / monoL (vertex 0) ∈ chartA
      rw [show ρL * aL ^ 3 / monoL (vertex 0) = σL * aL ^ 3 + 2 * aL ^ 2 * bL by lident]; subalg_mem
    · show ρL * aL ^ 3 / monoL (vertex 1) ∈ chartB
      rw [show ρL * aL ^ 3 / monoL (vertex 1) = ρL by lident]; exact ρL_mem_B
    · show ρL * aL ^ 3 / monoL (vertex 2) ∈ chartD
      rw [show ρL * aL ^ 3 / monoL (vertex 2) = ρL * wL by lident]; subalg_mem
    · show ρL * aL ^ 3 / monoL (vertex 3) ∈ chartP
      rw [show ρL * aL ^ 3 / monoL (vertex 3) = ρL * aP * aP ^ 2 * wL by lident]
      exact chartP.mul_mem (chartP.mul_mem ρaP_mem_P (chartP.pow_mem aP_mem_P _)) wL_mem_P
    · show ρL * aL ^ 3 * uL / monoL (vertex 0) ∈ chartA
      rw [show ρL * aL ^ 3 * uL / monoL (vertex 0) = (σL * aL ^ 3 + 2 * aL ^ 2 * bL) * uL by lident]
      subalg_mem
    · show ρL * aL ^ 3 * uL / monoL (vertex 1) ∈ chartB
      rw [show ρL * aL ^ 3 * uL / monoL (vertex 1) = ρL * uL by lident]; subalg_mem
    · show ρL * aL ^ 3 * uL / monoL (vertex 2) ∈ chartD
      rw [show ρL * aL ^ 3 * uL / monoL (vertex 2) = ρL by lident]; exact ρL_mem_D
    · show ρL * aL ^ 3 * uL / monoL (vertex 3) ∈ chartP
      rw [show ρL * aL ^ 3 * uL / monoL (vertex 3) = ρL * aP * aP ^ 2 by lident]
      exact chartP.mul_mem ρaP_mem_P (chartP.pow_mem aP_mem_P _)
  · fin_cases i
    · show uL ^ 11 * θE n aL bL σL / monoL (vertex 0) ∈ chartA
      rw [show uL ^ 11 * θE n aL bL σL / monoL (vertex 0) = uL ^ 11 * θE n aL bL σL by lident]
      exact chartA.mul_mem (chartA.pow_mem uL_mem_A _) (θE_mem_A n)
    · show uL ^ 11 * θE n aL bL σL / monoL (vertex 1) ∈ chartB
      rw [show uL ^ 11 * θE n aL bL σL / monoL (vertex 1) =
          uL ^ 11 * αL ^ 2 * (θE n aL bL σL * αL) by lident, θ_B]
      exact chartB.mul_mem (chartB.mul_mem (chartB.pow_mem uL_mem_B _) (chartB.pow_mem αL_mem_B _))
        (ΨE_mem chartB.toSubring n uL_mem_B αL_mem_B βL_mem_B ρL_mem_B)
    · show uL ^ 11 * θE n aL bL σL / monoL (vertex 2) ∈ chartD
      rw [show uL ^ 11 * θE n aL bL σL / monoL (vertex 2) = αD ^ 2 * (ξ n * αD) by
          rw [ξ_eq]; lident, ξ_D]
      exact chartD.mul_mem (chartD.pow_mem αD_mem_D _)
        (ΦE_mem chartD.toSubring n wL_mem_D αD_mem_D βD_mem_D ρL_mem_D)
    · show uL ^ 11 * θE n aL bL σL / monoL (vertex 3) ∈ chartP
      rw [show uL ^ 11 * θE n aL bL σL / monoL (vertex 3) = ξ n by rw [ξ_eq]; lident]
      exact ξ_mem n

theorem genValue_div_mem (g : Gen) (i : Fin 4) : genValue g / monoL (vertex i) ∈ chartRing i := by
  rcases g with q | f
  · rw [genValue, Sum.elim_inl, ← monoL_sub]
    exact monoL_mem (mono_table q i)
  · exact fib_div_mem f i

/-! ## The ambient graded ring `L[T]` -/

/-- The ambient graded ring `L[T]`. -/
abbrev Amb := AddMonoidAlgebra L ℕ
/-- Its grading by degree in `T`. -/
abbrev 𝒢 : ℕ → Submodule L Amb := AddMonoidAlgebra.grade L

/-- The degree-one element with value `a`. -/
def sec (a : L) : Amb := AddMonoidAlgebra.single 1 a

theorem sec_mem (a : L) : sec a ∈ 𝒢 1 := AddMonoidAlgebra.single_mem_grade 1 a

/-- Evaluation at `T = 1`. -/
def evAmb : Amb →ₐ[k] L := (AddMonoidAlgebra.lift L L ℕ 1).restrictScalars k

@[simp] theorem evAmb_single (n : ℕ) (a : L) : evAmb (AddMonoidAlgebra.single n a) = a := by
  simp [evAmb, AddMonoidAlgebra.lift_single]

@[simp] theorem evAmb_sec (a : L) : evAmb (sec a) = a := evAmb_single 1 a

theorem eq_single_of_mem {n : ℕ} {p : Amb} (hp : p ∈ 𝒢 n) :
    p = AddMonoidAlgebra.single n (evAmb p) := by
  change p ∈ AddMonoidAlgebra.grade L n at hp
  rw [AddMonoidAlgebra.grade_eq_lsingle_range] at hp
  obtain ⟨r, rfl⟩ := hp
  simp

def gens : Set Amb := Set.range fun g ↦ sec (genValue g)

/-- The homogeneous coordinate ring of `X`. -/
def B : Subalgebra k Amb := Algebra.adjoin k gens

theorem sec_genValue_mem_gens (g : Gen) : sec (genValue g) ∈ gens := ⟨g, rfl⟩

/-- Every product of generators is homogeneous, regular on each chart after dividing by the
vertex power, and either `1` or a multiple of a generator. -/
theorem closure_property {m : Amb} (hm : m ∈ Submonoid.closure gens) :
    ∃ n, m ∈ 𝒢 n ∧ (∀ i, evAmb m / monoL (vertex i) ^ n ∈ chartRing i) ∧
      (n = 0 → m = 1) ∧ (n ≠ 0 → ∃ g ∈ gens, ∃ m' ∈ Submonoid.closure gens, m = g * m') := by
  induction hm using Submonoid.closure_induction_left with
  | one =>
    refine ⟨0, SetLike.GradedOne.one_mem, fun i ↦ ?_, fun _ ↦ rfl, fun h ↦ (h rfl).elim⟩
    simp only [map_one, pow_zero, div_one]
    exact (chartRing i).one_mem
  | mul_left g hg m' hm' ih =>
    obtain ⟨n, hn, hdiv, -, -⟩ := ih
    obtain ⟨g', rfl⟩ := hg
    refine ⟨1 + n, SetLike.mul_mem_graded (sec_mem _) hn, fun i ↦ ?_, fun h ↦ by omega,
      fun _ ↦ ⟨_, ⟨g', rfl⟩, m', hm', rfl⟩⟩
    have hv := monoL_ne_zero (vertex i)
    have he : evAmb (sec (genValue g') * m') / monoL (vertex i) ^ (1 + n) =
        (genValue g' / monoL (vertex i)) * (evAmb m' / monoL (vertex i) ^ n) := by
      rw [map_mul, evAmb_sec, pow_add, pow_one]
      field_simp
    rw [he]
    exact (chartRing i).mul_mem (genValue_div_mem g' i) (hdiv i)

/-- The span of the products of generators of degree `n`. -/
def W (n : ℕ) : Submodule k Amb :=
  Submodule.span k {m | m ∈ Submonoid.closure gens ∧ m ∈ 𝒢 n}

theorem decompose_smul_k (c : k) (a : Amb) (n : ℕ) :
    (DirectSum.decompose 𝒢 (c • a) n : Amb) = c • (DirectSum.decompose 𝒢 a n : Amb) := by
  rw [algebra_compatible_smul L c a, DirectSum.decompose_smul, DirectSum.smul_apply,
    Submodule.coe_smul, ← algebra_compatible_smul]

theorem decompose_mem_W {a : Amb} (ha : a ∈ B) (n : ℕ) :
    (DirectSum.decompose 𝒢 a n : Amb) ∈ W n := by
  have ha' : a ∈ Submodule.span k (Submonoid.closure gens : Set Amb) := by
    rw [← Algebra.adjoin_eq_span]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨d, hd, -⟩ := closure_property hm
    by_cases h : d = n
    · subst h
      rw [DirectSum.decompose_of_mem_same 𝒢 hd]
      exact Submodule.subset_span ⟨hm, hd⟩
    · rw [DirectSum.decompose_of_mem_ne 𝒢 hd h]
      exact (W n).zero_mem
  | zero => simp
  | add a b _ _ ha hb => simpa using (W n).add_mem ha hb
  | smul c a _ ha =>
    rw [decompose_smul_k]
    exact (W n).smul_mem c ha

theorem W_le_B (n : ℕ) : W n ≤ Subalgebra.toSubmodule B := by
  rw [W, Submodule.span_le]
  rintro m ⟨hm, -⟩
  have : Submonoid.closure gens ≤ B.toSubmonoid :=
    Submonoid.closure_le.mpr fun z hz ↦ Algebra.subset_adjoin hz
  exact this hm

theorem W_div_mem {n : ℕ} {w : Amb} (hw : w ∈ W n) (i : Fin 4) :
    evAmb w / monoL (vertex i) ^ n ∈ chartRing i := by
  induction hw using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨d, hd, hdiv, -⟩ := closure_property hm.1
    by_cases h : d = n
    · exact h ▸ hdiv i
    · have h0 := DirectSum.decompose_of_mem_ne 𝒢 hd h
      rw [DirectSum.decompose_of_mem_same 𝒢 hm.2] at h0
      simp [h0]
  | zero => simp
  | add a b _ _ ha hb => simpa [add_div] using (chartRing i).add_mem ha hb
  | smul c a _ ha =>
    rw [map_smul, smul_div_assoc, Algebra.smul_def]
    exact (chartRing i).mul_mem ((chartRing i).algebraMap_mem c) ha

/-! ## The graded algebra `B` -/

theorem B_homogeneous : ∀ a ∈ B, ∀ n, (DirectSum.decompose 𝒢 a n : Amb) ∈ B :=
  fun a ha n ↦ W_le_B n (decompose_mem_W ha n)

/-- The grading of the homogeneous coordinate ring. -/
abbrev 𝒜 : ℕ → Submodule k B := gradedPart 𝒢 B

instance : GradedAlgebra 𝒜 := gradedAlgebraOfHomogeneous 𝒢 B B_homogeneous

theorem mem_W_of_mem {n : ℕ} {a : B} (ha : a ∈ 𝒜 n) : (a : Amb) ∈ W n := by
  have h := decompose_mem_W a.property n
  rwa [DirectSum.decompose_of_mem_same 𝒢 ((mem_gradedPart 𝒢 B).mp ha)] at h

/-- Evaluation of the coordinate ring in the function field. -/
def evB : B →ₐ[k] L := evAmb.comp B.val

/-- A generator as an element of `B`. -/
def genB (g : Gen) : B := ⟨sec (genValue g), Algebra.subset_adjoin (sec_genValue_mem_gens g)⟩

theorem genB_mem (g : Gen) : genB g ∈ 𝒜 1 := sec_mem _

@[simp] theorem evB_genB (g : Gen) : evB (genB g) = genValue g := by simp [evB, genB]

/-- The vertex section of chart `i`. -/
def vertexIdx : Fin 4 → Fin 20 := ![0, 1, 2, 3]

def xv (i : Fin 4) : B := genB (.inl (vertexIdx i))

theorem xv_val (i : Fin 4) : genValue (.inl (vertexIdx i)) = monoL (vertex i) := by
  fin_cases i <;> rfl

@[simp] theorem evB_xv (i : Fin 4) : evB (xv i) = monoL (vertex i) := by
  rw [xv, evB_genB, xv_val]

theorem xv_mem (i : Fin 4) : xv i ∈ 𝒜 1 := genB_mem _

/-! ## Charts as degree-zero localizations -/

theorem away_surj_of (i : Fin 4) (Sg : Set L) (hS : chartRing i = Algebra.adjoin k Sg)
    (hgen : ∀ z ∈ Sg, ∃ g, z = genValue g / monoL (vertex i)) (z : L) (hz : z ∈ chartRing i) :
    ∃ n a, a ∈ 𝒜 (n • 1) ∧ z = evB a / evB (xv i) ^ n := by
  rw [hS] at hz
  have hx : evB (xv i) ≠ 0 := by rw [evB_xv]; exact monoL_ne_zero _
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨g, rfl⟩ := hgen z hz
    exact ⟨1, genB g, genB_mem g, by rw [evB_genB, evB_xv, pow_one]⟩
  | algebraMap c =>
    exact ⟨0, algebraMap k B c, SetLike.algebraMap_mem_graded 𝒜 c, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨n, a, ha, rfl⟩ := hz
    obtain ⟨m, b, hb, rfl⟩ := hw
    refine ⟨n + m, a * xv i ^ m + b * xv i ^ n, ?_, ?_⟩
    · have h1 : a * xv i ^ m ∈ 𝒜 ((n + m) • 1) := by
        simpa [add_smul] using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m (xv_mem i))
      have h2 : b * xv i ^ n ∈ 𝒜 ((n + m) • 1) := by
        simpa [add_smul, add_comm] using
          SetLike.mul_mem_graded hb (SetLike.pow_mem_graded n (xv_mem i))
      exact add_mem h1 h2
    · simp only [map_add, map_mul, map_pow]
      field_simp
      ring
  | mul z w _ _ hz hw =>
    obtain ⟨n, a, ha, rfl⟩ := hz
    obtain ⟨m, b, hb, rfl⟩ := hw
    refine ⟨n + m, a * b, by simpa [add_smul] using SetLike.mul_mem_graded ha hb, ?_⟩
    rw [map_mul, pow_add]
    ring

theorem mono_ratio (q : Fin 20) (i : Fin 4) :
    genValue (.inl q) / monoL (vertex i) = monoL (monoPt q - vertex i) := by
  rw [genValue, Sum.elim_inl, monoL_sub]

theorem away_surj (i : Fin 4) (z : L) (hz : z ∈ chartRing i) :
    ∃ n a, a ∈ 𝒜 (n • 1) ∧ z = evB a / evB (xv i) ^ n := by
  have ha := aL_ne_zero
  have hb := bL_ne_zero
  have hu := uL_ne_zero
  fin_cases i
  · refine away_surj_of 0 {aL, bL, σL} rfl ?_ z hz
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨.inl 4, by rw [mono_ratio]; simp [monoPt, vertex, monoL]⟩
    · exact ⟨.inl 13, by rw [mono_ratio]; simp [monoPt, vertex, monoL]⟩
    · exact ⟨.inr (.inl 0), by simp [genValue, fibValue, vertex, monoL]⟩
  · refine away_surj_of 1 {uL, αL, βL, ρL} rfl ?_ z hz
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨.inl 2, by rw [mono_ratio]; simp [monoPt, vertex, monoL]⟩
    · exact ⟨.inl 5, by rw [mono_ratio]; simp [monoPt, vertex, monoL, αL]⟩
    · exact ⟨.inl 14, by rw [mono_ratio]; simp [monoPt, vertex, monoL, βL] <;> field_simp⟩
    · exact ⟨.inr (.inl 1), by simp [genValue, fibValue, vertex, monoL] <;> field_simp⟩
  · refine away_surj_of 2 {wL, αD, βD, ρL} rfl ?_ z hz
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨.inl 1, by rw [mono_ratio]; simp [monoPt, vertex, monoL, wL]⟩
    · exact ⟨.inl 6, by rw [mono_ratio]; simp [monoPt, vertex, monoL, αD] <;> field_simp⟩
    · exact ⟨.inl 15, by rw [mono_ratio]; simp [monoPt, vertex, monoL, βD] <;> field_simp⟩
    · exact ⟨.inr (.inl 2), by simp [genValue, fibValue, vertex, monoL] <;> field_simp⟩
  · refine away_surj_of 3 (Set.range ξ) rfl ?_ z hz
    rintro _ ⟨n, rfl⟩
    refine ⟨.inr (.inr n), ?_⟩
    simp only [genValue, fibValue, Sum.elim_inr, ξ_eq, vertex, monoL, wL]
    simp
    field_simp <;> ring

/-! ## The four vertex sections have no common zero -/

theorem monoL_sum {ι : Type} (s : Finset ι) (f : ι → Exp) :
    monoL (∑ i ∈ s, f i) = ∏ i ∈ s, monoL (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monoL_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monoL_add, ih]

/-- Powers of the monomials with `j = 0` that are products of vertex sections. -/
def vpN : Fin 13 → ℕ := ![1, 1, 1, 1, 3, 3, 3, 13, 3, 13, 9, 13, 13]
def vpM : Fin 13 → Fin 4 → ℕ :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![2, 1, 0, 0], ![1, 2, 0, 0],
    ![0, 0, 2, 1], ![11, 0, 0, 2], ![0, 0, 1, 2], ![12, 0, 0, 1], ![1, 5, 1, 2], ![6, 0, 0, 7],
    ![4, 0, 0, 9]]

theorem vp_table (q : Fin 13) :
    (∑ v : Fin 4, vpM q v) = vpN q ∧
      (∑ v : Fin 4, ((vpM q v : ℕ) : ℤ) • vertex v) =
        ((vpN q : ℕ) : ℤ) • monoPt (Fin.castLE (by norm_num) q) := by
  simp only [Fin.sum_univ_four]
  fin_cases q <;> decide

theorem vp_pos (q : Fin 13) : ∃ v, vpM q v ≠ 0 := by
  fin_cases q <;> decide

theorem sec_pow (a : L) (n : ℕ) : sec a ^ n = AddMonoidAlgebra.single n (a ^ n) := by
  rw [sec, AddMonoidAlgebra.single_pow, smul_eq_mul, mul_one]

@[simp] theorem coe_genB (g : Gen) : (genB g : Amb) = sec (genValue g) := rfl
@[simp] theorem coe_xv (i : Fin 4) : (xv i : Amb) = sec (monoL (vertex i)) := by
  rw [xv, coe_genB, xv_val]

theorem monoL_natCast_zsmul (n : ℕ) (v : Exp) : monoL ((n : ℤ) • v) = monoL v ^ n := by
  rw [natCast_zsmul, monoL_nsmul]

theorem toric_power (q : Fin 13) :
    genB (.inl (Fin.castLE (by norm_num) q)) ^ vpN q = ∏ v : Fin 4, xv v ^ vpM q v := by
  obtain ⟨h1, h2⟩ := vp_table q
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_finsetProd]
  simp only [SubmonoidClass.coe_pow, coe_genB, coe_xv, genValue, Sum.elim_inl, sec_pow]
  rw [AddMonoidAlgebra.prod_single, h1]
  congr 1
  rw [← monoL_natCast_zsmul, ← h2, monoL_sum]
  exact Finset.prod_congr rfl fun v _ ↦ monoL_natCast_zsmul _ _

theorem sec_mul_sec (a b : L) : sec a * sec b = AddMonoidAlgebra.single 2 (a * b) := by
  rw [sec, sec, AddMonoidAlgebra.single_mul_single]

/-- Pairs of points with `j = 0` whose products give `b² = a³ + u` times a monomial. -/
def sqPairs : Fin 7 → (Fin 20 × Fin 20) × (Fin 20 × Fin 20) :=
  ![((1, 0), (9, 0)), ((1, 5), (5, 9)), ((2, 6), (6, 7)), ((2, 10), (6, 0)), ((2, 11), (12, 0)),
    ((2, 12), (12, 7)), ((2, 3), (3, 7))]

theorem sq_table (q : Fin 7) :
    monoPt (sqPairs q).1.1 + monoPt (sqPairs q).1.2 =
        (2 : ℤ) • monoPt (q.natAdd 13 |>.cast (by norm_num)) - (0, 2, 0) + (3, 0, 0) ∧
      monoPt (sqPairs q).2.1 + monoPt (sqPairs q).2.2 =
        (2 : ℤ) • monoPt (q.natAdd 13 |>.cast (by norm_num)) - (0, 2, 0) + (0, 0, 1) := by
  fin_cases q <;> decide

theorem mono_square (q : Fin 7) :
    genB (.inl (q.natAdd 13 |>.cast (by norm_num))) ^ 2 =
      genB (.inl (sqPairs q).1.1) * genB (.inl (sqPairs q).1.2) +
        genB (.inl (sqPairs q).2.1) * genB (.inl (sqPairs q).2.2) := by
  obtain ⟨h1, h2⟩ := sq_table q
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_mul, coe_genB, genValue,
    Sum.elim_inl, sec_pow, sec_mul_sec, ← monoL_add, h1, h2, ← AddMonoidAlgebra.single_add]
  congr 1
  rw [← monoL_b_sq, sub_add_cancel, ← monoL_natCast_zsmul]
  rfl

/-! ## Fibre sections: `11`th powers -/

section RQ

variable {R : Type*} [CommRing R]

/-- `r_0` homogenized in degree `6`. -/
def rQ0 (g X Y Z : R) : R := -g ^ 10 * Y ^ 4 * Z ^ 2 + 2 * g ^ 10 * X ^ 3 * Y ^ 2 * Z
    - g ^ 10 * X ^ 6 + 5 * g ^ 9 * X * Y ^ 3 * Z ^ 2 - 4 * g ^ 9 * X ^ 4 * Y * Z
    - 3 * g ^ 8 * X ^ 2 * Y ^ 2 * Z ^ 2 + g ^ 8 * X ^ 5 * Z + 2 * g ^ 7 * Y ^ 3 * Z ^ 3
    + g ^ 7 * X ^ 3 * Y * Z ^ 2 + 4 * g ^ 6 * X * Y ^ 2 * Z ^ 3 + 3 * g ^ 6 * X ^ 4 * Z ^ 2
    + 5 * g ^ 5 * X ^ 2 * Y * Z ^ 3 + 2 * g ^ 4 * Y ^ 2 * Z ^ 4 + 3 * g ^ 4 * X ^ 3 * Z ^ 3
    - 4 * g ^ 3 * X * Y * Z ^ 4 + 3 * g ^ 2 * X ^ 2 * Z ^ 4 - 2 * g * Y * Z ^ 5 + X * Z ^ 5

/-- `r_1` homogenized in degree `6`. -/
def rQ1 (g X Y Z : R) : R := -g ^ 9 * Y ^ 4 * Z ^ 2 + 2 * g ^ 9 * X ^ 3 * Y ^ 2 * Z
    - g ^ 9 * X ^ 6 - g ^ 8 * X * Y ^ 3 * Z ^ 2 + 3 * g ^ 8 * X ^ 4 * Y * Z
    + 2 * g ^ 7 * X ^ 2 * Y ^ 2 * Z ^ 2 + 3 * g ^ 7 * X ^ 5 * Z - 3 * g ^ 6 * Y ^ 3 * Z ^ 3
    + 4 * g ^ 6 * X ^ 3 * Y * Z ^ 2 - 2 * g ^ 5 * X * Y ^ 2 * Z ^ 3 + 4 * g ^ 5 * X ^ 4 * Z ^ 2
    - 3 * g ^ 4 * X ^ 2 * Y * Z ^ 3 + 3 * g ^ 3 * Y ^ 2 * Z ^ 4 - g ^ 3 * X ^ 3 * Z ^ 3
    + g ^ 2 * X * Y * Z ^ 4 + 5 * g * X ^ 2 * Z ^ 4 + 2 * Y * Z ^ 5

/-- `r_2` homogenized in degree `6`. -/
def rQ2 (g X Y Z : R) : R := -g ^ 8 * Y ^ 4 * Z ^ 2 + 2 * g ^ 8 * X ^ 3 * Y ^ 2 * Z
    - g ^ 8 * X ^ 6 + 4 * g ^ 7 * X * Y ^ 3 * Z ^ 2 - g ^ 7 * X ^ 4 * Y * Z
    + 4 * g ^ 6 * X ^ 2 * Y ^ 2 * Z ^ 2 - 5 * g ^ 6 * X ^ 5 * Z - 2 * g ^ 5 * Y ^ 3 * Z ^ 3
    - g ^ 5 * X ^ 3 * Y * Z ^ 2 + 5 * g ^ 4 * X * Y ^ 2 * Z ^ 3 + g ^ 4 * X ^ 4 * Z ^ 2
    - 5 * g ^ 3 * X ^ 2 * Y * Z ^ 3 + g ^ 2 * Y ^ 2 * Z ^ 4 - 4 * g ^ 2 * X ^ 3 * Z ^ 3
    - g * X * Y * Z ^ 4 + 3 * X ^ 2 * Z ^ 4

/-- `r_3` homogenized in degree `6`. -/
def rQ3 (g X Y Z : R) : R := -g ^ 7 * Y ^ 4 * Z ^ 2 + 2 * g ^ 7 * X ^ 3 * Y ^ 2 * Z
    - g ^ 7 * X ^ 6 - 2 * g ^ 6 * X * Y ^ 3 * Z ^ 2 - 5 * g ^ 6 * X ^ 4 * Y * Z
    + 3 * g ^ 5 * X ^ 2 * Y ^ 2 * Z ^ 2 - g ^ 5 * X ^ 5 * Z - 4 * g ^ 4 * Y ^ 3 * Z ^ 3
    - 2 * g ^ 4 * X ^ 3 * Y * Z ^ 2 - 3 * g ^ 3 * X * Y ^ 2 * Z ^ 3 - 5 * g ^ 3 * X ^ 4 * Z ^ 2
    + 5 * g ^ 2 * X ^ 2 * Y * Z ^ 3 + 3 * g * Y ^ 2 * Z ^ 4 - g * X ^ 3 * Z ^ 3
    + 4 * X * Y * Z ^ 4

/-- `r_4` homogenized in degree `6`. -/
def rQ4 (g X Y Z : R) : R := -g ^ 6 * Y ^ 4 * Z ^ 2 + 2 * g ^ 6 * X ^ 3 * Y ^ 2 * Z
    - g ^ 6 * X ^ 6 + 3 * g ^ 5 * X * Y ^ 3 * Z ^ 2 + 2 * g ^ 5 * X ^ 4 * Y * Z
    - g ^ 4 * X ^ 2 * Y ^ 2 * Z ^ 2 + 4 * g ^ 4 * X ^ 5 * Z + 4 * g ^ 3 * Y ^ 3 * Z ^ 3
    + 2 * g ^ 3 * X ^ 3 * Y * Z ^ 2 + 5 * g ^ 2 * X * Y ^ 2 * Z ^ 3 + g ^ 2 * X ^ 4 * Z ^ 2
    + 3 * g * X ^ 2 * Y * Z ^ 3 + 2 * Y ^ 2 * Z ^ 4 + 3 * X ^ 3 * Z ^ 3

/-- `r_5` homogenized in degree `6`. -/
def rQ5 (g X Y Z : R) : R := -g ^ 5 * Y ^ 4 * Z ^ 2 + 2 * g ^ 5 * X ^ 3 * Y ^ 2 * Z
    - g ^ 5 * X ^ 6 - 3 * g ^ 4 * X * Y ^ 3 * Z ^ 2 - 2 * g ^ 4 * X ^ 4 * Y * Z
    + 3 * g ^ 3 * X ^ 2 * Y ^ 2 * Z ^ 2 - g ^ 3 * X ^ 5 * Z + 2 * g ^ 2 * Y ^ 3 * Z ^ 3
    + g ^ 2 * X ^ 3 * Y * Z ^ 2 - 2 * g * X * Y ^ 2 * Z ^ 3 + 4 * g * X ^ 4 * Z ^ 2
    - 5 * X ^ 2 * Y * Z ^ 3

/-- `r_6` homogenized in degree `6`. -/
def rQ6 (g X Y Z : R) : R := -g ^ 4 * Y ^ 4 * Z ^ 2 + 2 * g ^ 4 * X ^ 3 * Y ^ 2 * Z
    - g ^ 4 * X ^ 6 + 2 * g ^ 3 * X * Y ^ 3 * Z ^ 2 + 5 * g ^ 3 * X ^ 4 * Y * Z
    + 4 * g ^ 2 * X ^ 2 * Y ^ 2 * Z ^ 2 - 5 * g ^ 2 * X ^ 5 * Z + 3 * g * Y ^ 3 * Z ^ 3
    - 4 * g * X ^ 3 * Y * Z ^ 2 + 4 * X * Y ^ 2 * Z ^ 3 + 3 * X ^ 4 * Z ^ 2

/-- `r_7` homogenized in degree `6`. -/
def rQ7 (g X Y Z : R) : R := -g ^ 3 * Y ^ 4 * Z ^ 2 + 2 * g ^ 3 * X ^ 3 * Y ^ 2 * Z
    - g ^ 3 * X ^ 6 - 4 * g ^ 2 * X * Y ^ 3 * Z ^ 2 + g ^ 2 * X ^ 4 * Y * Z
    + 2 * g * X ^ 2 * Y ^ 2 * Z ^ 2 + 3 * g * X ^ 5 * Z - 2 * Y ^ 3 * Z ^ 3 - X ^ 3 * Y * Z ^ 2

/-- `r_8` homogenized in degree `6`. -/
def rQ8 (g X Y Z : R) : R := -g ^ 2 * Y ^ 4 * Z ^ 2 + 2 * g ^ 2 * X ^ 3 * Y ^ 2 * Z
    - g ^ 2 * X ^ 6 + g * X * Y ^ 3 * Z ^ 2 - 3 * g * X ^ 4 * Y * Z - 3 * X ^ 2 * Y ^ 2 * Z ^ 2
    + X ^ 5 * Z

/-- `r_9` homogenized in degree `6`. -/
def rQ9 (g X Y Z : R) : R := -g * Y ^ 4 * Z ^ 2 + 2 * g * X ^ 3 * Y ^ 2 * Z - g * X ^ 6
    - 5 * X * Y ^ 3 * Z ^ 2 + 4 * X ^ 4 * Y * Z

/-- `r_10` homogenized in degree `6`. -/
def rQ10 (_g X Y Z : R) : R := -Y ^ 4 * Z ^ 2 + 2 * X ^ 3 * Y ^ 2 * Z - X ^ 6
/-- The eleven homogenizations `r_n(g, X/Z, Y/Z) Z⁶`. -/
def rQE (n : Fin 11) (g X Y Z : R) : R :=
  ![rQ0 g X Y Z, rQ1 g X Y Z, rQ2 g X Y Z, rQ3 g X Y Z, rQ4 g X Y Z, rQ5 g X Y Z, rQ6 g X Y Z,
    rQ7 g X Y Z, rQ8 g X Y Z, rQ9 g X Y Z, rQ10 g X Y Z] n

theorem rQE_homog (n : Fin 11) (g x y z t : R) :
    rQE n g (x * t) (y * t) (z * t) = t ^ 6 * rQE n g x y z := by
  fin_cases n <;> simp [rQE, rQ0, rQ1, rQ2, rQ3, rQ4, rQ5, rQ6, rQ7, rQ8, rQ9, rQ10] <;> ring

theorem rQE_one (n : Fin 11) (g x y : R) : rQE n g x y 1 = rE n g x y := by
  fin_cases n <;> simp [rQE, rE, rQ0, rQ1, rQ2, rQ3, rQ4, rQ5, rQ6, rQ7, rQ8, rQ9, rQ10, r0, r1,
    r2, r3, r4, r5, r6, r7, r8, r9, r10] <;> ring

end RQ

set_option maxHeartbeats 1000000 in
theorem rQE_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 11) (g x y z : R) :
    f (rQE n g x y z) = rQE n (f g) (f x) (f y) (f z) := by
  fin_cases n <;> simp [rQE, rQ0, rQ1, rQ2, rQ3, rQ4, rQ5, rQ6, rQ7, rQ8, rQ9, rQ10, map_ofNat]

theorem rE_frob {R : Type*} [CommRing R] [CharP R 11] (n : Fin 11) (g x y : R) :
    rE n g x y ^ 11 = rE n (g ^ 11) (x ^ 11) (y ^ 11) := by
  have h := rE_map (frobenius R 11) n g x y
  simpa [frobenius_def] using h

theorem ξ_pow (n : Fin 11) : ξ n ^ 11 = rE n cL aP bP := by
  apply ι.injective
  rw [map_pow, ι_ξ, algebraMap_rK, rE_frob, rE_map, ι_cL, ι_aP, ι_bP]

theorem θ11 (n : Fin 11) : (uL ^ 11 * θE n aL bL σL) ^ 11 =
    (uL ^ 13) ^ 5 * rQE n cL (aL * uL ^ 9) (bL * uL ^ 7) (uL ^ 13) := by
  have hu := uL_ne_zero
  have hθ : θE n aL bL σL = ξ n * uL ^ 2 := by rw [ξ_eq, wL]; field_simp
  have ha : aL * uL ^ 9 = aP * uL ^ 13 := by simp only [aP, wL]; field_simp <;> ring
  have hb : bL * uL ^ 7 = bP * uL ^ 13 := by simp only [bP, wL]; field_simp <;> ring
  have h := rQE_homog n cL aP bP 1 (uL ^ 13)
  rw [one_mul] at h
  rw [hθ, ha, hb, h, rQE_one, ← ξ_pow]
  ring

theorem σ11 : σL ^ 11 = aL * bL ^ 3 - 3 * aL ^ 3 * (aL * bL) - 2 * cL := by
  simp only [cL]
  grind

theorem ρ11 : (ρL * aL ^ 3) ^ 11 = -2 * cL * (aL ^ 3) ^ 11 + 9 * (aL ^ 3) ^ 10 * (aL * bL * uL ^ 2) +
    9 * (aL ^ 3) ^ 9 * (aL * bL * uL ^ 3) + 10 * (aL ^ 3) ^ 8 * aL * (bL * uL ^ 4) +
    2 * (aL ^ 3) ^ 7 * aL * (bL * uL ^ 5) := by
  have ha := aL_ne_zero
  simp only [ρL, cL, uL]
  field_simp
  grind

theorem ρu11 : (ρL * aL ^ 3 * uL) ^ 11 = -2 * cL * (aL ^ 3 * uL) ^ 11 +
    9 * (aL ^ 3 * uL) ^ 10 * (aL * bL * uL ^ 3) + 9 * (aL ^ 3 * uL) ^ 9 * aL * (bL * uL ^ 5) +
    10 * (aL ^ 3 * uL) ^ 8 * aL * (bL * uL ^ 7) + 2 * (aL ^ 3 * uL) ^ 7 * aL * (bL * uL ^ 7) * uL ^ 2 := by
  rw [mul_pow, ρ11]
  ring

/-! ## Lifting identities to `B` -/

/-- `T` in `L[T]`. -/
def tT : Amb := AddMonoidAlgebra.single 1 1

theorem sec_eq_t (v : L) : sec v = algebraMap L Amb v * tT := by
  rw [sec, tT, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

theorem algebraMap_k_Amb (z : k) : algebraMap k Amb z = algebraMap L Amb (algebraMap k L z) :=
  IsScalarTower.algebraMap_apply k L Amb z

theorem coe_algebraMap_B (z : k) : ((algebraMap k B z : B) : Amb) = algebraMap k Amb z := rfl

theorem coe_ofNat_B (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : B) : Amb) = OfNat.ofNat n :=
  map_ofNat B.val n

theorem genValue_mono (q : Fin 20) : genValue (.inl q) = monoL (monoPt q) := rfl

theorem gv0 : genValue (.inl 0) = 1 := by simp [genValue, monoPt, monoL]
theorem gv1 : genValue (.inl 1) = aL ^ 3 := by simp [genValue, monoPt, monoL]
theorem gv2 : genValue (.inl 2) = aL ^ 3 * uL := by simp [genValue, monoPt, monoL]
theorem gv3 : genValue (.inl 3) = uL ^ 13 := by simp [genValue, monoPt, monoL]
theorem gv4 : genValue (.inl 4) = aL := by simp [genValue, monoPt, monoL]
theorem gv7 : genValue (.inl 7) = uL ^ 2 := by simp [genValue, monoPt, monoL]
theorem gv8 : genValue (.inl 8) = aL * uL ^ 9 := by simp [genValue, monoPt, monoL]
theorem gv13 : genValue (.inl 13) = bL := by simp [genValue, monoPt, monoL]
theorem gv14 : genValue (.inl 14) = aL * bL := by simp [genValue, monoPt, monoL]
theorem gv15 : genValue (.inl 15) = aL * bL * uL ^ 3 := by simp [genValue, monoPt, monoL]
theorem gv16 : genValue (.inl 16) = aL * bL * uL ^ 2 := by simp [genValue, monoPt, monoL]
theorem gv17 : genValue (.inl 17) = bL * uL ^ 4 := by simp [genValue, monoPt, monoL]
theorem gv18 : genValue (.inl 18) = bL * uL ^ 5 := by simp [genValue, monoPt, monoL]
theorem gv19 : genValue (.inl 19) = bL * uL ^ 7 := by simp [genValue, monoPt, monoL]
theorem gvσ : genValue (.inr (.inl 0)) = σL := rfl
theorem gvρ : genValue (.inr (.inl 1)) = ρL * aL ^ 3 := rfl
theorem gvρu : genValue (.inr (.inl 2)) = ρL * aL ^ 3 * uL := rfl
theorem gvθ (n : Fin 11) : genValue (.inr (.inr n)) = uL ^ 11 * θE n aL bL σL := rfl
theorem xv0 : genValue (.inl (vertexIdx 0)) = 1 := gv0
theorem coe_xv' (i : Fin 4) : (xv i : Amb) = sec (genValue (.inl (vertexIdx i))) := rfl

theorem fib_pow_σ : genB (.inr (.inl 0)) ^ 11 =
    genB (.inl 4) * (genB (.inl 13) ^ 3 * xv 0 ^ 7) -
      algebraMap k B 3 * genB (.inl 1) * (genB (.inl 14) * xv 0 ^ 9) -
      algebraMap k B (2 * c) * xv 0 ^ 11 := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul,
    coe_algebraMap_B, coe_genB, coe_xv', vertexIdx, Matrix.cons_val_zero, gv0, gv1, gv2, gv3, gv4,
    gv7, gv8, gv13, gv14, gv15, gv16, gv17, gv18, gv19, gvσ, gvρ, gvρu, sec_eq_t, algebraMap_k_Amb]
  simp only [map_mul, map_pow, map_ofNat, map_neg, map_one, algebraMap_c_L]
  have h := congrArg (algebraMap L Amb) σ11
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg] at h
  linear_combination tT ^ 11 * h

theorem fib_pow_ρ : genB (.inr (.inl 1)) ^ 11 =
    algebraMap k B (-2 * c) * genB (.inl 1) ^ 11 + algebraMap k B 9 * genB (.inl 1) ^ 10 * genB (.inl 16) +
      algebraMap k B 9 * genB (.inl 1) ^ 9 * genB (.inl 15) * xv 0 +
      algebraMap k B 10 * genB (.inl 1) ^ 8 * genB (.inl 4) * genB (.inl 17) * xv 0 +
      algebraMap k B 2 * genB (.inl 1) ^ 7 * genB (.inl 4) * genB (.inl 18) * xv 0 ^ 2 := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul,
    coe_algebraMap_B, coe_genB, coe_xv', vertexIdx, Matrix.cons_val_zero, gv0, gv1, gv2, gv3, gv4,
    gv7, gv8, gv13, gv14, gv15, gv16, gv17, gv18, gv19, gvσ, gvρ, gvρu, sec_eq_t, algebraMap_k_Amb]
  simp only [map_mul, map_pow, map_ofNat, map_neg, map_one, algebraMap_c_L]
  have h := congrArg (algebraMap L Amb) ρ11
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg] at h
  linear_combination tT ^ 11 * h

theorem fib_pow_ρu : genB (.inr (.inl 2)) ^ 11 =
    algebraMap k B (-2 * c) * genB (.inl 2) ^ 11 + algebraMap k B 9 * genB (.inl 2) ^ 10 * genB (.inl 15) +
      algebraMap k B 9 * genB (.inl 2) ^ 9 * genB (.inl 4) * genB (.inl 18) +
      algebraMap k B 10 * genB (.inl 2) ^ 8 * genB (.inl 4) * genB (.inl 19) * xv 0 +
      algebraMap k B 2 * genB (.inl 2) ^ 7 * genB (.inl 4) * genB (.inl 19) * genB (.inl 7) * xv 0 := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul,
    coe_algebraMap_B, coe_genB, coe_xv', vertexIdx, Matrix.cons_val_zero, gv0, gv1, gv2, gv3, gv4,
    gv7, gv8, gv13, gv14, gv15, gv16, gv17, gv18, gv19, gvσ, gvρ, gvρu, sec_eq_t, algebraMap_k_Amb]
  simp only [map_mul, map_pow, map_ofNat, map_neg, map_one, algebraMap_c_L]
  have h := congrArg (algebraMap L Amb) ρu11
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg] at h
  linear_combination tT ^ 11 * h

theorem fib_pow_θ (n : Fin 11) : genB (.inr (.inr n)) ^ 11 =
    xv 3 ^ 5 * rQE n (algebraMap k B c) (genB (.inl 8)) (genB (.inl 19)) (xv 3) := by
  apply Subtype.ext
  have hmap := rQE_map (B.val : B →+* Amb) n (algebraMap k B c) (genB (.inl 8)) (genB (.inl 19))
    (xv 3)
  simp only [RingHom.coe_coe, Subalgebra.coe_val] at hmap
  rw [SubmonoidClass.coe_pow, Subalgebra.coe_mul, SubmonoidClass.coe_pow, hmap]
  simp only [coe_algebraMap_B, coe_genB, coe_xv', vertexIdx, Matrix.cons_val_three,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, gv3, gv8, gv19, gvθ, sec_eq_t,
    algebraMap_k_Amb, algebraMap_c_L]
  rw [rQE_homog, ← rQE_map, mul_pow, ← map_pow (algebraMap L Amb), θ11 n, map_mul, map_pow]
  ring

/-! ## The cover condition -/

theorem closure_mem_B {m : Amb} (hm : m ∈ Submonoid.closure gens) : m ∈ B :=
  (Submonoid.closure_le.mpr fun _ hz ↦ Algebra.subset_adjoin hz :
    Submonoid.closure gens ≤ B.toSubmonoid) hm

/-- Every homogeneous element of positive degree lies in an ideal containing all generators. -/
theorem pos_mem_of_gens {P : Ideal B} (hP : ∀ g, genB g ∈ P) {n : ℕ} (hn : n ≠ 0) {a : B}
    (ha : a ∈ 𝒜 n) : a ∈ P := by
  have hw := mem_W_of_mem ha
  suffices h : ∀ w ∈ W n, ∀ hw : w ∈ B, (⟨w, hw⟩ : B) ∈ P from h _ hw a.property
  intro w hw
  induction hw using Submodule.span_induction with
  | mem m hm =>
    intro hmB
    obtain ⟨d, hd, -, -, hdec⟩ := closure_property hm.1
    by_cases h : d = n
    · subst h
      obtain ⟨g, ⟨g₀, rfl⟩, m', hm', rfl⟩ := hdec hn
      have he : (⟨sec (genValue g₀) * m', hmB⟩ : B) = genB g₀ * ⟨m', closure_mem_B hm'⟩ := rfl
      rw [he]
      exact P.mul_mem_right _ (hP g₀)
    · have h0 := DirectSum.decompose_of_mem_ne 𝒢 hd h
      rw [DirectSum.decompose_of_mem_same 𝒢 hm.2] at h0
      subst h0
      exact P.zero_mem
  | zero => intro _; exact P.zero_mem
  | add a b ha' hb' ha hb =>
    intro _
    have e : (⟨a + b, _⟩ : B) = ⟨a, W_le_B n ha'⟩ + ⟨b, W_le_B n hb'⟩ := rfl
    rw [e]
    exact P.add_mem (ha _) (hb _)
  | smul c a ha' ha =>
    intro _
    have e : (⟨c • a, _⟩ : B) = c • ⟨a, W_le_B n ha'⟩ := rfl
    rw [e, Algebra.smul_def]
    exact P.mul_mem_left _ (ha _)

/-- The four vertex sections have no common zero on `Proj`. -/
theorem vertex_cover (p : ProjectiveSpectrum 𝒜) : ∃ i, xv i ∉ p.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  have hP : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  set P := p.asHomogeneousIdeal.toIdeal
  have hx (i : Fin 4) : xv i ∈ P := h i
  have htoric (q : Fin 13) : genB (.inl (Fin.castLE (by norm_num) q)) ∈ P := by
    apply hP.mem_of_pow_mem (vpN q)
    rw [toric_power]
    obtain ⟨v, hv⟩ := vp_pos q
    exact Ideal.mem_of_dvd _
      ((dvd_pow_self _ hv).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ v))) (hx v)
  have hlow (q : Fin 20) (hq : q.val < 13) : genB (.inl q) ∈ P := by
    have := htoric ⟨q.val, hq⟩
    exact this
  have hsq (q : Fin 7) : genB (.inl (q.natAdd 13 |>.cast (by norm_num))) ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [mono_square]
    have h1 : (sqPairs q).1.1.val < 13 := by fin_cases q <;> decide
    have h2 : (sqPairs q).2.1.val < 13 := by fin_cases q <;> decide
    exact P.add_mem (P.mul_mem_right _ (hlow _ h1)) (P.mul_mem_right _ (hlow _ h2))
  have hmono (q : Fin 20) : genB (.inl q) ∈ P := by
    by_cases hq : q.val < 13
    · exact hlow q hq
    · have := hsq ⟨q.val - 13, by omega⟩
      have e : ((⟨q.val - 13, by omega⟩ : Fin 7).natAdd 13 |>.cast (by norm_num) : Fin 20) = q := by
        ext; simp; omega
      rwa [e] at this
  have hfib (f : Fin 3 ⊕ Fin 11) : genB (.inr f) ∈ P := by
    apply hP.mem_of_pow_mem 11
    rcases f with f | n
    · fin_cases f
      · show genB (.inr (.inl 0)) ^ 11 ∈ P
        rw [fib_pow_σ]
        exact P.sub_mem (P.sub_mem (P.mul_mem_right _ (hmono 4))
          (P.mul_mem_right _ (P.mul_mem_left _ (hmono 1))))
          (P.mul_mem_left _ (P.pow_mem_of_mem (hx 0) 11 (by norm_num)))
      · show genB (.inr (.inl 1)) ^ 11 ∈ P
        rw [fib_pow_ρ]
        refine P.add_mem (P.add_mem (P.add_mem (P.add_mem ?_ ?_) ?_) ?_) ?_
        · exact P.mul_mem_left _ (P.pow_mem_of_mem (hmono 1) 11 (by norm_num))
        · exact P.mul_mem_left _ (hmono 16)
        · exact P.mul_mem_left _ (hx 0)
        · exact P.mul_mem_left _ (hx 0)
        · exact P.mul_mem_left _ (P.pow_mem_of_mem (hx 0) 2 (by norm_num))
      · show genB (.inr (.inl 2)) ^ 11 ∈ P
        rw [fib_pow_ρu]
        refine P.add_mem (P.add_mem (P.add_mem (P.add_mem ?_ ?_) ?_) ?_) ?_
        · exact P.mul_mem_left _ (P.pow_mem_of_mem (hmono 2) 11 (by norm_num))
        · exact P.mul_mem_left _ (hmono 15)
        · exact P.mul_mem_left _ (hmono 18)
        · exact P.mul_mem_left _ (hx 0)
        · exact P.mul_mem_left _ (hx 0)
    · rw [fib_pow_θ]
      exact P.mul_mem_right _ (P.pow_mem_of_mem (hx 3) 5 (by norm_num))
  have hgen (g : Gen) : genB g ∈ P := by
    rcases g with q | f
    · exact hmono q
    · exact hfib f
  apply p.not_irrelevant_le
  intro a ha
  rw [HomogeneousIdeal.mem_irrelevant_iff] at ha
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  refine sum_mem fun n _ ↦ ?_
  by_cases hn : n = 0
  · subst hn
    have : (DirectSum.decompose 𝒜 a 0 : B) = GradedRing.proj 𝒜 0 a := rfl
    rw [this, ha]
    exact zero_mem _
  · exact pos_mem_of_gens hgen hn (DirectSum.decompose 𝒜 a n).property

/-! ## `X` is the `Proj` of `B` -/

theorem degree_zero_surj (a : B) (ha : a ∈ 𝒜 0) : ∃ r : k, algebraMap k B r = a := by
  have hw := mem_W_of_mem ha
  have key : ∀ w ∈ W 0, ∃ r : k, algebraMap k Amb r = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨d, hd, -, h0, -⟩ := closure_property hm.1
      by_cases h : d = 0
      · exact ⟨1, by rw [map_one, h0 h]⟩
      · have hz := DirectSum.decompose_of_mem_ne 𝒢 hd h
        rw [DirectSum.decompose_of_mem_same 𝒢 hm.2] at hz
        exact ⟨0, by rw [map_zero, hz]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨r, rfl⟩ := ha
      obtain ⟨r', rfl⟩ := hb
      exact ⟨r + r', map_add _ _ _⟩
    | smul c a _ ha =>
      obtain ⟨r, rfl⟩ := ha
      exact ⟨c * r, by rw [map_mul, Algebra.smul_def]⟩
  obtain ⟨r, hr⟩ := key _ hw
  exact ⟨r, Subtype.ext hr⟩

theorem degree_zero_bijective : Function.Bijective (algebraMap k (𝒜 0)) := by
  constructor
  · intro a b h
    have h' : algebraMap k Amb a = algebraMap k Amb b :=
      congrArg (fun z : 𝒜 0 ↦ ((z : B) : Amb)) h
    exact (algebraMap k Amb).injective h'
  · intro a
    obtain ⟨r, hr⟩ := degree_zero_surj (a : B) a.property
    exact ⟨r, Subtype.ext hr⟩

/-- The graded algebra `B` realizes the atlas of `X`. -/
def model : AtlasModel (A := B) atlas 𝒜 where
  ev := evB
  ev_injective {n a b} ha hb hab := by
    apply Subtype.ext
    rw [eq_single_of_mem ((mem_gradedPart 𝒢 B).mp ha),
      eq_single_of_mem ((mem_gradedPart 𝒢 B).mp hb)]
    exact congrArg _ hab
  d := 1
  d_pos := one_pos
  x := xv
  x_mem := xv_mem
  x_ne := fun (i : Fin 4) ↦ by
    rw [evB_xv]
    exact monoL_ne_zero _
  away_mem := fun (i : Fin 4) n a ha ↦ by
    have ha' : a ∈ 𝒜 n := by simpa using ha
    have h := W_div_mem (mem_W_of_mem ha') i
    change evB a / evB (xv i) ^ n ∈ chartRing i
    rw [evB_xv]
    exact h
  away_surj := away_surj
  cover := vertex_cover

/-- `X` is projective over `k`. -/
theorem x_projective : IsProjectiveOver k xToBase :=
  ⟨B, inferInstance, inferInstance, 𝒜, inferInstance, model.iso,
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _), degree_zero_bijective,
    model.iso_over_base⟩

/-- `X` is proper over `k`. -/
theorem x_proper : IsProper xToBase := x_projective.isProper

end
end Geonormal.P11

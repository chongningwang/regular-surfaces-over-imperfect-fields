import Geonormal.Atlas
import SurfaceLib.Projective.AtlasModel
import Mathlib.Algebra.MonoidAlgebra.Grading

/-! # The characteristic-19 surface is projective

`X` is the `Proj` of the subalgebra of `F[T]` generated in degree one by the sections
`t^a x^b T`, for the 17 lattice points `(a, b)` of the polygon, and `y t^a T` for `a ≤ 3`.
The five charts are the degree-zero localizations at the vertex sections
`1, x², t⁸, t⁵x, tx²`. Every condition is an exponent inequality or an explicit identity.
-/

namespace Geonormal

open Red61 Red61.AffineGluing AlgebraicGeometry SurfaceLib.Projective
open scoped DirectSum

noncomputable section

/-! ## The ambient graded ring `F[T]` -/

/-- The ambient graded ring `F[T]`. -/
abbrev Amb := AddMonoidAlgebra F ℕ
/-- Its grading by degree in `T`. -/
abbrev 𝒢 : ℕ → Submodule F Amb := AddMonoidAlgebra.grade F

/-- The degree-one element with value `a`. -/
def sec (a : F) : Amb := AddMonoidAlgebra.single 1 a

theorem sec_mem (a : F) : sec a ∈ 𝒢 1 := AddMonoidAlgebra.single_mem_grade 1 a

/-- Evaluation at `T = 1`. -/
def evAmb : Amb →ₐ[k] F := (AddMonoidAlgebra.lift F F ℕ 1).restrictScalars k

@[simp] theorem evAmb_single (n : ℕ) (a : F) : evAmb (AddMonoidAlgebra.single n a) = a := by
  simp [evAmb, AddMonoidAlgebra.lift_single]

@[simp] theorem evAmb_sec (a : F) : evAmb (sec a) = a := evAmb_single 1 a

theorem eq_single_of_mem {n : ℕ} {p : Amb} (hp : p ∈ 𝒢 n) :
    p = AddMonoidAlgebra.single n (evAmb p) := by
  change p ∈ AddMonoidAlgebra.grade F n at hp
  rw [AddMonoidAlgebra.grade_eq_lsingle_range] at hp
  obtain ⟨r, rfl⟩ := hp
  simp

/-! ## Generators and their exponent tables -/

/-- The 17 lattice points of the polygon. -/
def toricPt : Fin 17 → Lattice :=
  ![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0),
    (0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (0, 2), (1, 2)]

/-- The vertices of the polygon, one for each chart. -/
def vertex : Fin 5 → Lattice := ![(0, 0), (0, 2), (8, 0), (5, 1), (1, 2)]
def vertexIdx : Fin 5 → Fin 17 := ![0, 15, 8, 14, 16]

theorem toricPt_vertexIdx (i : Fin 5) : toricPt (vertexIdx i) = vertex i := by
  fin_cases i <;> rfl

/-- Generators: the toric sections and the odd sections `y t^a`. -/
abbrev Gen := Fin 17 ⊕ Fin 4

def genValue : Gen → F
  | .inl q => monoF (toricPt q)
  | .inr a => y * monoF (((a : ℕ) : ℤ), 0)

def gens : Set Amb := Set.range fun g ↦ sec (genValue g)

/-- The homogeneous coordinate ring of `X`. -/
def B : Subalgebra k Amb := Algebra.adjoin k gens

theorem sec_genValue_mem_gens (g : Gen) : sec (genValue g) ∈ gens := ⟨g, rfl⟩

theorem toric_table (q : Fin 17) (i : Fin 5) : NonnegIn i (toricPt q - vertex i) := by
  fin_cases q <;> fin_cases i <;> decide

theorem odd_table (a : Fin 4) (i : Fin 5) :
    NonnegIn i ((((a : ℕ) : ℤ), 0) - vertex i - yScale i) := by
  fin_cases a <;> fin_cases i <;> decide

theorem genValue_div_mem (g : Gen) (i : Fin 5) :
    genValue g / monoF (vertex i) ∈ chartRing i := by
  rcases g with q | a
  · rw [genValue, div_eq_mul_inv, ← monoF_neg, ← monoF_add, ← sub_eq_add_neg]
    exact monoF_mem_of_nonneg (toric_table q i)
  · have he : y * monoF (((a : ℕ) : ℤ), 0) / monoF (vertex i) =
        yc i * monoF ((((a : ℕ) : ℤ), 0) - vertex i - yScale i) := by
      rw [yc, div_eq_mul_inv, ← monoF_neg, mul_assoc, mul_assoc, ← monoF_add, ← monoF_add]
      congr 2
      abel
    rw [genValue, he]
    exact (chartRing i).mul_mem (yc_mem i) (monoF_mem_of_nonneg (odd_table a i))

/-! ## Products of generators -/

/-- Every product of generators is homogeneous, regular on each chart after dividing by the
vertex power, and either `1` or a multiple of a generator. -/
theorem closure_property {m : Amb} (hm : m ∈ Submonoid.closure gens) :
    ∃ n, m ∈ 𝒢 n ∧ (∀ i, evAmb m / monoF (vertex i) ^ n ∈ chartRing i) ∧
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
    have he : evAmb (sec (genValue g') * m') / monoF (vertex i) ^ (1 + n) =
        (genValue g' / monoF (vertex i)) * (evAmb m' / monoF (vertex i) ^ n) := by
      rw [map_mul, evAmb_sec, pow_add, pow_one]
      field_simp
    rw [he]
    exact (chartRing i).mul_mem (genValue_div_mem g' i) (hdiv i)

/-- The span of the products of generators of degree `n`. -/
def W (n : ℕ) : Submodule k Amb :=
  Submodule.span k {m | m ∈ Submonoid.closure gens ∧ m ∈ 𝒢 n}

theorem decompose_smul_k (c : k) (a : Amb) (n : ℕ) :
    (DirectSum.decompose 𝒢 (c • a) n : Amb) = c • (DirectSum.decompose 𝒢 a n : Amb) := by
  rw [algebra_compatible_smul F c a, DirectSum.decompose_smul, DirectSum.smul_apply,
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

theorem W_div_mem {n : ℕ} {w : Amb} (hw : w ∈ W n) (i : Fin 5) :
    evAmb w / monoF (vertex i) ^ n ∈ chartRing i := by
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
def evB : B →ₐ[k] F := evAmb.comp B.val

/-- The section of chart `i`. -/
def xv (i : Fin 5) : B :=
  ⟨sec (monoF (vertex i)), Algebra.subset_adjoin
    ⟨.inl (vertexIdx i), by simp [genValue, toricPt_vertexIdx]⟩⟩

@[simp] theorem evB_xv (i : Fin 5) : evB (xv i) = monoF (vertex i) := by
  simp [evB, xv]

theorem xv_mem (i : Fin 5) : xv i ∈ 𝒜 1 := sec_mem _

/-- A generator as an element of `B`. -/
def genB (g : Gen) : B := ⟨sec (genValue g), Algebra.subset_adjoin (sec_genValue_mem_gens g)⟩

theorem genB_mem (g : Gen) : genB g ∈ 𝒜 1 := sec_mem _

@[simp] theorem evB_genB (g : Gen) : evB (genB g) = genValue g := by simp [evB, genB]

/-! ## Charts as degree-zero localizations -/

def adjFirst : Fin 5 → Fin 17 := ![1, 16, 7, 8, 15]
def adjSecond : Fin 5 → Fin 17 := ![9, 9, 14, 16, 14]
def oddIdx : Fin 5 → Fin 4 := ![0, 0, 3, 3, 3]

theorem adjacent_table (i : Fin 5) :
    toricPt (adjFirst i) = vertex i + first i ∧ toricPt (adjSecond i) = vertex i + second i ∧
      ((((oddIdx i : ℕ) : ℤ), 0) : Lattice) = yScale i + vertex i := by
  fin_cases i <;> decide

theorem ratio_eq (i : Fin 5) (v : Lattice) :
    monoF (vertex i + v) / monoF (vertex i) = monoF v := by
  rw [monoF_add, mul_div_cancel_left₀ _ (monoF_ne_zero _)]

theorem away_surj (i : Fin 5) (z : F) (hz : z ∈ chartRing i) :
    ∃ n a, a ∈ 𝒜 (n • 1) ∧ z = evB a / evB (xv i) ^ n := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨hf, hs, hy⟩ := adjacent_table i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    refine ⟨1, ?_⟩
    rcases hz with rfl | rfl | rfl
    · refine ⟨genB (.inl (adjFirst i)), genB_mem _, ?_⟩
      rw [evB_genB, evB_xv, genValue, hf, pow_one, ratio_eq]
    · refine ⟨genB (.inl (adjSecond i)), genB_mem _, ?_⟩
      rw [evB_genB, evB_xv, genValue, hs, pow_one, ratio_eq]
    · refine ⟨genB (.inr (oddIdx i)), genB_mem _, ?_⟩
      rw [evB_genB, evB_xv, genValue, hy, pow_one, mul_div_assoc, add_comm, ratio_eq, yc]
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
    · have hx : evB (xv i) ≠ 0 := by rw [evB_xv]; exact monoF_ne_zero _
      simp only [map_add, map_mul, map_pow]
      field_simp
      ring
  | mul z w _ _ hz hw =>
    obtain ⟨n, a, ha, rfl⟩ := hz
    obtain ⟨m, b, hb, rfl⟩ := hw
    refine ⟨n + m, a * b, by simpa [add_smul] using SetLike.mul_mem_graded ha hb, ?_⟩
    rw [map_mul, pow_add]
    ring


/-! ## The five vertex sections have no common zero -/

theorem monoF_sum {ι : Type} (s : Finset ι) (f : ι → Lattice) :
    monoF (∑ i ∈ s, f i) = ∏ i ∈ s, monoF (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monoF_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, monoF_add, ih]

theorem monoF_natCast_zsmul (n : ℕ) (v : Lattice) : monoF ((n : ℤ) • v) = monoF v ^ n := by
  rw [natCast_zsmul, monoF_nsmul]

def vpN : Fin 17 → ℕ := ![1, 8, 4, 8, 2, 8, 4, 8, 1, 2, 5, 3, 5, 2, 1, 1, 1]
def vpM : Fin 17 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 3, 0, 0], ![1, 0, 1, 0, 0],
    ![3, 0, 5, 0, 0], ![1, 0, 3, 0, 0], ![1, 0, 7, 0, 0], ![0, 0, 1, 0, 0], ![1, 1, 0, 0, 0],
    ![2, 2, 0, 1, 0], ![1, 0, 0, 1, 1], ![1, 0, 1, 1, 2], ![0, 1, 1, 0, 0], ![0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1]]

/-- Each lattice point has a multiple which is a combination of vertices. -/
theorem vp_table (q : Fin 17) :
    (∑ v : Fin 5, vpM q v) = vpN q ∧
      (∑ v : Fin 5, ((vpM q v : ℕ) : ℤ) • vertex v) = ((vpN q : ℕ) : ℤ) • toricPt q := by
  simp only [Fin.sum_univ_five]
  fin_cases q <;> decide

theorem vp_pos (q : Fin 17) : ∃ v, vpM q v ≠ 0 := by
  fin_cases q <;> decide

theorem sec_pow (a : F) (n : ℕ) : sec a ^ n = AddMonoidAlgebra.single n (a ^ n) := by
  rw [sec, AddMonoidAlgebra.single_pow, smul_eq_mul, mul_one]

@[simp] theorem coe_genB (g : Gen) : (genB g : Amb) = sec (genValue g) := rfl
@[simp] theorem coe_xv (i : Fin 5) : (xv i : Amb) = sec (monoF (vertex i)) := rfl

theorem sec_mul_sec (a b : F) : sec a * sec b = AddMonoidAlgebra.single 2 (a * b) := by
  rw [sec, sec, AddMonoidAlgebra.single_mul_single]

theorem algebraMap_mul_single (r : k) (n : ℕ) (a : F) :
    algebraMap k Amb r * AddMonoidAlgebra.single n a =
      AddMonoidAlgebra.single n (algebraMap k F r * a) := by
  rw [← Algebra.smul_def, AddMonoidAlgebra.smul_single, Algebra.smul_def]

theorem toric_power (q : Fin 17) : genB (.inl q) ^ vpN q = ∏ v : Fin 5, xv v ^ vpM q v := by
  obtain ⟨h1, h2⟩ := vp_table q
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_finsetProd]
  simp only [SubmonoidClass.coe_pow, coe_genB, coe_xv, genValue, sec_pow]
  rw [AddMonoidAlgebra.prod_single, h1]
  congr 1
  rw [← monoF_natCast_zsmul, ← h2, monoF_sum]
  exact Finset.prod_congr rfl fun v _ ↦ monoF_natCast_zsmul _ _

/-- Pairs of lattice points whose products give the terms of `y² t^{2a}`. -/
def oddSq : Fin 4 → Fin 3 → Fin 17 × Fin 17 :=
  ![![(9, 15), (2, 14), (0, 1)], ![(10, 16), (4, 14), (0, 3)],
    ![(12, 16), (6, 14), (0, 5)], ![(14, 16), (8, 14), (0, 7)]]

theorem oddSq_table (a : Fin 4) :
    toricPt (oddSq a 0).1 + toricPt (oddSq a 0).2 = (2 * ((a : ℕ) : ℤ), 3) ∧
    toricPt (oddSq a 1).1 + toricPt (oddSq a 1).2 = (2 * ((a : ℕ) : ℤ) + 7, 1) ∧
    toricPt (oddSq a 2).1 + toricPt (oddSq a 2).2 = (2 * ((a : ℕ) : ℤ) + 1, 0) := by
  fin_cases a <;> decide

theorem x_eq_monoF : x = monoF (0, 1) := by simp [monoF, monoE, xE, x]
theorem t_eq_monoF : t = monoF (1, 0) := by simp [monoF, monoE, tE, t]

theorem y_sq_monoF : y ^ 2 = monoF (0, 3) + algebraMap k F c ^ 2 * monoF (7, 1) + monoF (1, 0) := by
  rw [y_sq, x_eq_monoF, t_eq_monoF]
  have h3 : monoF (0, 1) ^ 3 = monoF (0, 3) := by
    rw [← monoF_nsmul]; rfl
  have h7 : monoF (1, 0) ^ 7 * monoF (0, 1) = monoF (7, 1) := by
    rw [← monoF_nsmul, ← monoF_add]; rfl
  rw [h3, mul_assoc, h7]

theorem odd_value (a : Fin 4) :
    genValue (.inr a) ^ 2 =
      genValue (.inl (oddSq a 0).1) * genValue (.inl (oddSq a 0).2) +
        algebraMap k F (c ^ 2) * (genValue (.inl (oddSq a 1).1) * genValue (.inl (oddSq a 1).2)) +
          genValue (.inl (oddSq a 2).1) * genValue (.inl (oddSq a 2).2) := by
  obtain ⟨h0, h1, h2⟩ := oddSq_table a
  simp only [genValue, ← monoF_add, h0, h1, h2, mul_pow, y_sq_monoF, map_pow]
  rw [← monoF_nsmul]
  have e0 : (2 * ((a : ℕ) : ℤ), (3 : ℤ)) = (0, 3) + 2 • ((((a : ℕ) : ℤ), 0) : Lattice) := by
    ext <;> simp
  have e1 : (2 * ((a : ℕ) : ℤ) + 7, (1 : ℤ)) = (7, 1) + 2 • ((((a : ℕ) : ℤ), 0) : Lattice) := by
    ext <;> simp; ring
  have e2 : (2 * ((a : ℕ) : ℤ) + 1, (0 : ℤ)) = (1, 0) + 2 • ((((a : ℕ) : ℤ), 0) : Lattice) := by
    ext <;> simp; ring
  rw [e0, e1, e2, monoF_add, monoF_add, monoF_add]
  ring

theorem odd_square (a : Fin 4) :
    genB (.inr a) ^ 2 =
      genB (.inl (oddSq a 0).1) * genB (.inl (oddSq a 0).2) +
        algebraMap k B (c ^ 2) * (genB (.inl (oddSq a 1).1) * genB (.inl (oddSq a 1).2)) +
          genB (.inl (oddSq a 2).1) * genB (.inl (oddSq a 2).2) := by
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_add, Subalgebra.coe_mul,
    Subalgebra.coe_algebraMap, coe_genB, sec_pow, sec_mul_sec, algebraMap_mul_single]
  rw [odd_value, ← AddMonoidAlgebra.single_add, ← AddMonoidAlgebra.single_add]


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

/-- The five vertex sections have no common zero on `Proj`. -/
theorem vertex_cover (p : ProjectiveSpectrum 𝒜) : ∃ i, xv i ∉ p.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  have hP : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have htoric (q : Fin 17) : genB (.inl q) ∈ p.asHomogeneousIdeal.toIdeal := by
    apply hP.mem_of_pow_mem (vpN q)
    rw [toric_power]
    obtain ⟨v, hv⟩ := vp_pos q
    exact Ideal.mem_of_dvd _
      ((dvd_pow_self _ hv).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ v))) (h v)
  have hgen (g : Gen) : genB g ∈ p.asHomogeneousIdeal.toIdeal := by
    rcases g with q | a
    · exact htoric q
    · apply hP.mem_of_pow_mem 2
      rw [odd_square]
      refine add_mem (add_mem (Ideal.mul_mem_right _ _ (htoric _)) ?_)
        (Ideal.mul_mem_right _ _ (htoric _))
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (htoric _))
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
def model : AtlasModel atlas 𝒜 where
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
  x_ne := fun (i : Fin 5) ↦ by
    rw [evB_xv]
    exact monoF_ne_zero _
  away_mem := fun (i : Fin 5) n a ha ↦ by
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
end Geonormal

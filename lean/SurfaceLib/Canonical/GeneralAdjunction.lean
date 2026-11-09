import SurfaceLib.Canonical.ClassicalAdjunction

/-! # Classical adjunction in every prime characteristic and for every base differential rank

`omegaR F b r bF` is the normalized absolute differential line
`Hom(b^* ⋀^r Ω_{F/ℤ}, ⋀^{r+2} Ω_{Y/ℤ})` of a surface `Y` over a field `F` whose absolute
differentials have a basis `bF` with `r` elements. For `r = 2` it is `Red61.omega`.

`GeneralClassicalAdjunction` is the classical input of `ClassicalAdjunction`, stated for every
prime characteristic `p` and every `r`. Over a field of characteristic `p`, a basis of
`Ω_{F/ℤ} = Ω_{F/𝔽_p}` with `r` elements is a `p`-basis of size `r`. `ClassicalAdjunction` is the
case `p = 5`, `r = 2` (`GeneralClassicalAdjunction.toClassicalAdjunction`).
-/

namespace SurfaceLib.Canonical

open Red61 AlgebraicGeometry CategoryTheory Module

noncomputable section

variable (F : Type) [Field F] [Algebra ℤ F] {Y : Scheme.{0}}
  (b : Y ⟶ Spec (CommRingCat.of F)) (r : ℕ)

/-- The base differential determinant `b^* ⋀^r Ω_{F/ℤ}`. -/
def omegaBaseLineR : Y.Modules :=
  (Scheme.Modules.pullback b).obj
    (tilde (ModuleCat.of F (⋀[F]^r (KaehlerDifferential ℤ F))))

variable (bF : Basis (Fin r) F (KaehlerDifferential ℤ F))

/-- The base volume of the differential basis `bF`. -/
def omegaBaseVolumeR : structureSheafModule Y ≅ omegaBaseLineR F b r :=
  (pullbackStructureSheafIso b).symm ≪≫
    (Scheme.Modules.pullback b).mapIso
      ((tildeSelf (R := CommRingCat.of F)).symm ≪≫
        (tilde.functor (CommRingCat.of F)).mapIso
          (integralTopExteriorCoefficient bF).symm.toModuleIso)

/-- The normalized absolute differential line `Hom(O_Y ⊗_F ⋀^r Ω_{F/ℤ}, ⋀^{r+2} Ω_{Y/ℤ})`. -/
def omegaR : Y.Modules :=
  nativeFramedLineHom Y (omegaBaseVolumeR F b r bF)
    (nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) (r + 2))

/-- Evaluation at the base volume identifies `omegaR` with absolute top forms. -/
def omegaREvaluationIso :
    omegaR F b r bF ≅ nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) (r + 2) :=
  nativeFramedLineHomEvaluationIso Y (omegaBaseVolumeR F b r bF)
    (nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) (r + 2))

/-- For `r = 2`, `omegaR` is `Red61.omega`. -/
theorem omegaR_two (bF : Basis (Fin 2) F (KaehlerDifferential ℤ F)) :
    omegaR F b 2 bF = omega F b bF := rfl

end

/-- Classical normalized adjunction and top-degree Serre duality for regular proper surfaces over
essentially finitely generated fields of any prime characteristic `p`, whose absolute
differentials have a basis with `r` elements. Like `ClassicalAdjunction`, this is a general
theorem interface supplied as an explicit parameter, not a hypothesis about a particular surface. -/
structure GeneralClassicalAdjunction : Prop where
  normalizedDuality : ∀ (p r : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] [Algebra ℤ F]
    [Algebra (ZMod p) F] [Algebra.EssFiniteType (ZMod p) F]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F))
    [IsProper f] [IsIntegral X] [IsNoetherian X]
    (bF : Module.Basis (Fin r) F (KaehlerDifferential ℤ F)),
    topologicalKrullDim X = 2 →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
    IsLocallyFreeOfRank (r + 2) (nativeAbsoluteDifferentialModule X) →
    Nonempty (TopDuality F f 2 (omegaR F f r bF))

/-- `ClassicalAdjunction` is the case `p = 5`, `r = 2` of `GeneralClassicalAdjunction`. -/
theorem GeneralClassicalAdjunction.toClassicalAdjunction (h : GeneralClassicalAdjunction) :
    ClassicalAdjunction := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨?_⟩
  intro F _ _ _ _ _ X f _ _ _ bF hd hr hl
  exact h.normalizedDuality 5 2 F f bF hd hr hl

end SurfaceLib.Canonical

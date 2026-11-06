import Red61.AlgebraicGeometry.ExteriorPower
import Red61.CurveNumericalTriviality

/-! The canonical line in terms of ordinary absolute differentials.

For a surface over a field `F` with a two-element absolute differential basis,
`omega F b bF` is the actual Hom sheaf
`Hom(b* (⋀² Ω_{F/ℤ}), ⋀⁴ Ω_{Y/ℤ})`.
The basis supplies the base volume used to construct the Hom sheaf and its
evaluation isomorphism. Over `F = F₅(s₁,s₂)`, absolute differentials over `ℤ`
are canonically the differentials over `F₅`.
No presentation, invariant volume, or triviality hypothesis enters the definition.
-/

namespace Red61
open AlgebraicGeometry CategoryTheory Module
noncomputable section

variable (F : Type) [Field F] [Algebra ℤ F] {Y : Scheme.{0}}
  (b : Y ⟶ Spec (CommRingCat.of F))

/-- The base differential determinant, extended to the surface by actual pullback. -/
def omegaBaseLine : Y.Modules :=
  (Scheme.Modules.pullback b).obj
    (tilde (ModuleCat.of F (⋀[F]^2 (KaehlerDifferential ℤ F))))

variable (bF : Basis (Fin 2) F (KaehlerDifferential ℤ F))

/-- The base volume, obtained from the displayed differential basis. -/
def omegaBaseVolume : structureSheafModule Y ≅ omegaBaseLine F b :=
  (pullbackStructureSheafIso b).symm ≪≫
    (Scheme.Modules.pullback b).mapIso
      ((tildeSelf (R := CommRingCat.of F)).symm ≪≫
        (tilde.functor (CommRingCat.of F)).mapIso
          (integralTopExteriorCoefficient bF).symm.toModuleIso)

/-- The normalized absolute differential line
`Hom(O_Y ⊗_F ⋀² Ω_{F/ℤ}, ⋀⁴ Ω_{Y/ℤ})`. -/
def omega : Y.Modules :=
  nativeFramedLineHom Y (omegaBaseVolume F b bF)
    (nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) 4)

/-- Evaluation at the base volume identifies `omega` with absolute top forms. -/
def omegaEvaluationIso :
    omega F b bF ≅ nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) 4 :=
  nativeFramedLineHomEvaluationIso Y (omegaBaseVolume F b bF)
    (nativeExteriorModule Y (nativeAbsoluteDifferentialModule Y) 4)

end
end Red61

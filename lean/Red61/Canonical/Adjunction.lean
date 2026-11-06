import Red61.Canonical.Neighborhoods

/-! # Conormal adjunction at the surface stalks

Formerly the modules `SurfaceStalkAdjunction`, `SurfaceRelativeAdjunction`.
-/

/-! Absolute conormal determinant adjunction at every actual stalk of S.
Its rational image is exactly the existing integral differential lattice,
and the global invariant rational volume lifts to a nonzero generator of
each presented adjunction module. Relative canonical gluing is separate. -/

namespace Red61.Contraction

open Fields AlgebraicGeometry Module
noncomputable section

private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance (s : S) : Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

variable (s : S) [Algebra F₅ (S.presheaf.stalk s)]
  (P : Algebra.Extension F₅ (S.presheaf.stalk s)) [Algebra.FormallySmooth F₅ P.Ring]
  {c : ℕ} (bC : Basis (Fin c) (S.presheaf.stalk s) P.Cotangent)

def sStalkPrimeDifferentialBasis :
    Basis (Fin 4) (S.presheaf.stalk s) (KaehlerDifferential F₅ (S.presheaf.stalk s)) :=
  (sStalkDifferentialBasis s).map
    (quotientBaseDifferentialEquiv ℤ F₅ (S.presheaf.stalk s) ZMod.intCast_surjective)

end
end Red61.Contraction

/-! Relative adjunction at the actual surface stalks, with their original
ell-scalars. For a formally smooth ell-ambient presentation with the stated
finite bases and ranks, its adjunction line maps onto the proved normalized
integral lattice. Compatibility between presentations is still separate. -/

namespace Red61.Contraction

open Fields Module AlgebraicGeometry
open scoped TensorProduct
noncomputable section
set_option synthInstance.maxHeartbeats 80000

private local instance : Algebra F₅ ell := ZMod.algebra ell 5
private local instance : CommRing S.functionField :=
  (inferInstance : Field S.functionField).toCommRing
private local instance : Module S.functionField RelativeRationalDeterminant := by
  let := functionFieldAlgebra ell sToBase
  infer_instance
private local instance (priority := 100) (s : S) : Algebra ell (S.presheaf.stalk s) :=
  (stalkScalarMap ell sToBase s).toAlgebra
private local instance (priority := 100) (s : S) : Algebra F₅ (S.presheaf.stalk s) :=
  sStalkPrimeAlgebra s
private local instance (priority := 100) (s : S) :
    Module (S.presheaf.stalk s) (AbsoluteStalkDifferentials S s) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℤ (S.presheaf.stalk s) (R' := S.presheaf.stalk s)

variable (s : S) (P : Algebra.Extension ell (S.presheaf.stalk s))
  [Algebra.FormallySmooth ell P.Ring] {c q : ℕ}
  (bC : Basis (Fin c) (S.presheaf.stalk s) P.Cotangent)
  (bQ : Basis (Fin q) (S.presheaf.stalk s) P.CotangentSpace) (hrank : c + 4 = 2 + q)

set_option maxHeartbeats 800000 in
@[irreducible]
def sRelativeStalkAdjunction :
    ((⋀[S.presheaf.stalk s]^c P.Cotangent) →ₗ[S.presheaf.stalk s]
      (⋀[S.presheaf.stalk s]^q P.CotangentSpace)) ≃ₗ[S.presheaf.stalk s]
        (⋀[S.presheaf.stalk s]^4 (AbsoluteStalkDifferentials S s)) := by
  let := (stalkScalarMap ell sToBase s).toAlgebra
  let := sStalkPrimeAlgebra s
  have : @IsScalarTower F₅ ell (S.presheaf.stalk s)
      (Algebra.toSMul : SMul F₅ ell) (Algebra.toSMul : SMul ell (S.presheaf.stalk s))
      (Algebra.toSMul : SMul F₅ (S.presheaf.stalk s)) :=
    primeAlgebra_tower ell (S.presheaf.stalk s)
  have := ell_prime_formallySmooth
  have := s_stalk_formallySmooth s
  exact (relativeConormalDeterminantComparison F₅ P bC (sStalkPrimeDifferentialBasis s)
    ellPrimeDifferentialBasis bQ hrank).trans
      ((determinantLineEvaluation (K := S.presheaf.stalk s)
        (integralTopExteriorCoefficient
          (ellPrimeDifferentialBasis.baseChange (S.presheaf.stalk s)))).trans
            (exteriorLinearEquiv 4 (quotientBaseDifferentialEquiv ℤ F₅
              (S.presheaf.stalk s) ZMod.intCast_surjective).symm))

@[irreducible]
def sRelativeStalkToRational :
    ((⋀[S.presheaf.stalk s]^c P.Cotangent) →ₗ[S.presheaf.stalk s]
      (⋀[S.presheaf.stalk s]^q P.CotangentSpace))
        →ₛₗ[algebraMap (S.presheaf.stalk s) S.functionField] RelativeRationalDeterminant :=
  relativeDeterminantEvaluation.symm.toLinearMap.comp
    ((integralStalkTopToRational s (sStalkDifferentialBasis s)).comp
      (sRelativeStalkAdjunction s P bC bQ hrank).toLinearMap)

end
end Red61.Contraction

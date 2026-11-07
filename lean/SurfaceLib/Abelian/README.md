# Para-abelian varieties and rational rigidity

`IsParaAbelianVariety F π` says that `π : P ⟶ Spec F` is proper and that `P` over an algebraic
closure of `F` carries the structure of a proper geometrically integral group scheme. This is the
class of targets in the manuscript's definition of the Albanese morphism, which allows a target
without a rational point. `isParaAbelianVariety_id` proves that `Spec F` is one, namely the trivial
abelian variety. `IsAlbaneseMorphism` is the universal property of that definition.

## The supplied classical theorem

`ClassicalRationalRigidity` is a proposition with the single field `constant`. It is passed
explicitly as a parameter; the library supplies no inhabitant and installs no global instance.

The field states: for fields `F ⊂ E`, every `F`-morphism `φ : 𝔸²_E ⟶ P` to a para-abelian variety
factors through the structure morphism `𝔸²_E ⟶ Spec E`.

It is a general theorem and mentions no example. It is stronger in form than the statement in the
literature, which is over an algebraically closed field.

## Reference and reduction to it

J. S. Milne, *Abelian Varieties* (v2.00, 2008), Chapter I:

- Proposition 3.9: every rational map from `𝔸¹` or `ℙ¹` to an abelian variety is constant;
- Proposition 3.10: every rational map from a unirational variety to an abelian variety is constant.

The proofs do not restrict the characteristic. The reduction from the form used here is not
formalized:

1. Choose an algebraic closure `Ē` of `E` containing an algebraic closure `F̄` of `F`. Then `P_Ē` is
   the base change of an abelian variety over `F̄`, so it is an abelian variety over `Ē`.
2. Proposition 3.10 makes `𝔸²_Ē ⟶ P_Ē` constant.
3. Let `p : Spec E ⟶ P` be the value of `φ` at the origin. Then `φ` and the composite of the
   structure morphism with `p` agree after the faithfully flat base change `𝔸²_Ē ⟶ 𝔸²_E`, so they
   are equal by fpqc descent of morphisms.

## Search record

The pinned mathlib proves commutativity of proper geometrically integral group schemes
(`AlgebraicGeometry/Group/Abelian.lean`). It has no extension theorem for rational maps to group
schemes, no Jacobian of a curve, no Picard scheme and no statement about maps from `𝔸¹`.

## Consumers

`Eff.y_albanese_trivial`, `Eff.y_albanese_is_base`, `Eff.case_C_p5`.

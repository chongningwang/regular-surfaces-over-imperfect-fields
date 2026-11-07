# Classical diagonalizable quotient boundary

`ClassicalDiagonalizableQuotient.torsor` is an explicit mathematical hypothesis,
with no supplied inhabitant. It is independent of `ClassicalAdjunction`.
`Eff.rho_has_gradedTorsor`, `Eff.rho_is_muFiveTorsor`, `Eff.rho_action_weights`,
`Eff.rho_flat`, and `Eff.rho_rankFive` consume it.
The existing finite surjection and all four homogeneous covering certificates
are proved without either classical input.

## Exact scope

For a principal affine atlas in a field of characteristic five, the input takes
a derivation `E` with `E⁵ = E`, its actual kernel subfield, preservation of each
chart ring, and a finite homogeneous unit-ideal cover on every chart. Every
displayed weight must be nonzero modulo five. It concludes that the **existing**
invariant quotient morphism carries finite flat, surjective, rank-five torsor
data. It does not assert any example's covering identities or nonvanishing.

`MuFive.Torsor` is defined independently: its acting group on **every** test
scheme `T` is `{u : Γ(T,O_T)ˣ | u⁵ = 1}`. The action is natural under arbitrary
pullback, satisfies the group laws, and is simply transitive on pairs of lifts
of the same `T → Y`. Finite flat surjectivity supplies the fpqc cover. Rank is
recorded as dimension five of the global sections of every actual scheme fiber
over its residue field. This formulation retains the nonreduced group scheme
in characteristic five; testing only field-valued points would not suffice.

`GradedTorsor` additionally records compatibility with `E`. For every chart,
test scheme, group element `a`, and map from that test scheme to the chart, it
supplies a chart lift of the acted-on point. On every homogeneous chart function
of integer weight `n`, pullback by this lift multiplies the old pullback by `aⁿ`.
This ties the supplied torsor action to the actual Euler derivation and the
already verified weight calculations. It is part of the explicit classical
conclusion, rather than a separately proved geometric construction in Lean.

## Classical ingredients and references

- [SGA 3, Exposé VIII, Proposition 4.1 and 4.6](https://grothendiecksga.com/read/sga3/en/VIII-4.html)
  give the graded-algebra criterion for a diagonalizable torsor.
- [SGA 3, Exposé VIII, Theorem 5.1](https://grothendiecksga.com/read/sga3/en/VIII-5.html)
  identifies the affine quotient of a free diagonalizable action with the
  spectrum of the degree-zero algebra and proves it is a torsor.
- The interface additionally packages the translation from `E⁵ = E` to the
  `ℤ/5` grading, the homogeneous-open freeness criterion, compatibility on
  invariant principal localizations, gluing, and finite flat rank-five descent.
  The constructed action must realize the given weights on all test schemes.
  The global conclusion is a consequence of these ingredients, rather than
  the literal statement of the affine theorem 5.1.

Mathematically, after inverting a nonzero-weight homogeneous function `f`,
its weight generates `ℤ/5`. Its fifth power is invariant, so these opens
descend to the quotient. Homogeneous powers of `f` identify each of the five
graded pieces with the invariant ring; the graded-algebra criterion applies.
The unit-ideal cover makes these local constructions cover the quotient.

The pinned mathlib was searched in `AlgebraicGeometry/Group/{Affine,Abelian,Smooth}`,
the flat-descent modules, and by the terms `Torsor`, `Diagonalizable`, and
`diagonalizable`. It has general affine group and descent infrastructure, but
no complete theorem with this graded-quotient conclusion. The independent
five-weight decomposition is already proved in `Derivation/WeightFive`;
the classical interface still packages its geometric realization and gluing.

This boundary is deliberately visible in the audit. It is not a proof of the
general classical theorem inside Lean, and its consumers are conditional.

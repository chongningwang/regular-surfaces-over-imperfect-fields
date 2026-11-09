# Shared surface mathematics

This is an active library target for reusable mathematics developed during the
Eff and Geonormal formalizations. The algebraic results and the uniqueness results for top
duality are proved without extra geometric inputs.

- `Derivation/Slice`: residue-field proportionality from a finite slice expansion.
- `Derivation/StableSubalgebra`: testing stability when coefficients are preserved
  rather than fixed pointwise.
- `Derivation/WeightFive`: explicit weight projections, existence and uniqueness
  of decomposition, and multiplication of weights in characteristic five.
- `Derivation/FrobeniusCover`: descent of finite unit-ideal certificates when
  fifth powers lift from the larger ring.
- `Canonical/TopDuality`: an independent canonical-sheaf characterization,
  trace-preserving uniqueness, and functorial comparison isomorphisms.
- `Canonical/ClassicalAdjunction`: an explicitly supplied general classical
  theorem about the normalized determinant. No inhabitant is supplied.
- `Canonical/GeneralAdjunction`: the normalized determinant `omegaR` for any number `r`
  of base differentials, and the same classical theorem for every prime characteristic
  and every `r`; `ClassicalAdjunction` is its case `p = 5`, `r = 2`. No inhabitant is
  supplied.
- `GroupScheme/MuFive`: finite flat rank-five torsor data, tested on all schemes.
- `GroupScheme/DiagonalizableQuotient`: an explicit general classical graded
  quotient theorem; no inhabitant is supplied. See [its boundary](GroupScheme/README.md).
- `LineBundle/RationalLine`: genuine sheaf tensor powers, generators through their
  values in the function field, and the resulting criterion for a power to be trivial.
- `Projective/AtlasModel`: homogeneous subalgebras are graded; a graded algebra with
  the right degree-zero localizations identifies a principal atlas with its `Proj`;
  descent of a principal cover of `Proj` and of finite generation along a power map;
  a projective model is proper.
- `RingTheory/Hypersurface`: the quotient of a regular local ring by an element outside
  the square of the maximal ideal is regular, a derivation test for that condition, and
  the chain rule for derivations of polynomial evaluations.
- `AlgebraicGeometry/GeometricNormality`: normal schemes, and the criterion that a scheme
  over a field is not geometrically normal when an affine open over the field has a base
  change that is a domain but not integrally closed.
- `Abelian/Rigidity`: para-abelian varieties, the universal property of the Albanese
  morphism, and an explicit general classical rigidity theorem; no inhabitant is
  supplied. See [its boundary](Abelian/README.md).

The general modules already in `Red61` remain there; this implementation does
not reorganize that library or weaken its audit. The
[canonical comparison documentation](Canonical/README.md) records the exact
classical boundary, its mathematical ingredients, and the conditional application.

# Eff: the final characteristic-five example

This library formalizes Example `ex:case-C-p5` of the [eff
manuscript](../../papers/eff/main.tex).

`Eff.y_example` uses no classical input. It proves that `Y`, over `ell = F₅(s₁,s₂)`, is
projective, integral, regular and two-dimensional, has global constants `ell`, is not
geometrically normal, and that the determinant of its differentials, normalized by the
base, has `n`-th tensor power trivial exactly when `5 ∣ n`.

`Eff.case_C_p5` uses exactly two explicit parameters, `ClassicalAdjunction` and
`ClassicalRationalRigidity`. It proves that `Y` has a canonical sheaf, that every canonical
sheaf has exact order five, and that the Albanese morphism of `Y` is the structure
morphism to `Spec ell`.

All checked logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`;
the separate audit also reports the mathematical parameters, which those lists do not
detect.

Two statements are read as follows. `K_Y ≡ 0` is not stated separately, since numerical
equivalence is not formalized; it is immediate from `5 K_Y ∼ 0`. `IsProjectiveOver` means
`Proj` of a finitely generated graded algebra with degree-zero part the field; generation
in degree one is not proved.

## What is proved

The construction: `Eff.quotient_properties` constructs an actual scheme `Y` and morphisms
`rho : Red61.Contraction.S ⟶ Y` and `yToBase : Y ⟶ Spec ell`. It proves:

- `Y` is proper over `ell`, integral, Noetherian, and two-dimensional;
- `rho` is finite and surjective, and commutes with the structure morphisms;
- the scalar map `ell → Γ(Y, ⊤)` is bijective.

Here `ell` is the existing concrete subfield `k⁵`, with `k = F₅(c₁,c₂)`.
`Red61.Fields.baseEquiv` identifies it with a rational function field in two
variables. The code does not mistake `k` for the field of scalars of the derivation.

The supporting modules prove:

| Component | Verified content |
| --- | --- |
| `Euler` | Actual polynomial and fraction-field derivations; fifth power equals itself; commutator with the original foliation; restriction to its invariant field |
| `InvariantCoordinates` | Invariance of `A,B,W`, their weights, the hypersurface relation, and the additive order of weight one |
| `ChartWeights` | The coordinate weights on all six charts, preservation of their rings, and actual restricted derivations |
| `ContractedWeights` | Preservation of the singular cone ring, the special invariant's weight, and derivations on the six original invariant chart rings |
| `AtlasEuler` | Derivations on the four actual charts of `S`, their fifth-power identity, and agreement on overlaps |
| `FreenessCertificates` | Explicit homogeneous unit-ideal covers and nonvanishing modulo every prime on those four charts, including the cone chart |
| `Torsor` | Conditional mu-five torsor structure, flatness, rank five, and action compatibility with the Euler weights for the existing `rho` |
| `ChartObstructions` | Each of the six separate residue-field contradictions and the special-point unit obstruction |
| `AffineUnits` | Every unit on each invariant chart is a nonzero scalar in `ell` |
| `Canonical` | Conditional identification of the input surface's canonical sheaf and its trivialization; essential finite generation of the actual base field |
| `GeometricObstruction` | The actual candidate quotient polynomial, its partial derivatives, and the singular-locus parameter identities |
| `Quotient` | The four-chart invariant quotient, its scheme morphism, and the geometric properties listed above |
| `YStraightening`, `YCharts`, `YBases`, `YCover` | Nine principal opens of `Y`, each a localization of a polynomial ring in four variables over `F₅`; `y_stalk_regular` |
| `YDifferentials`, `YStalks`, `YJacobians`, `YTuples`, `YVolume` | Local freeness of the absolute differentials and an explicit generator of the top-form lattice on each open; `y_lattice` |
| `YOrder`, `YCanonical` | Exact order five, through genuine sheaf tensor powers; the transfer to any canonical sheaf is conditional on `ClassicalAdjunction` |
| `YNonnormal` | `y_not_geometrically_normal`: the base change to `k` contains an open whose ring is not integrally closed |
| `YProjective` | `y_projective`: `Y` is the `Proj` of the homogeneous elements of the coordinate ring of `X` with values in `M` |
| `YAlbanese` | `y_albanese_is_base`, conditional on `ClassicalRationalRigidity` |
| `YExample` | The two final statements |

`SurfaceLib` proves the residue-field slice comparison and the existence and
uniqueness of the five weight components without finite-dimensionality assumptions.
Multiplication adds their weights.

## Not needed for the final statements

These are proved conditionally or remain open. The final statements do not use them.

1. The presentation of the invariant chart ring by `A,B,W`: the relation alone does not
   establish either generation or injectivity.
2. `rho` is a finite flat rank-five `μ₅`-torsor, conditional on the general classical
   diagonalizable quotient input.
3. The canonical trivialization of the input surface `S`, conditional on
   `ClassicalAdjunction`, and any `μ₅`-equivariance of a canonical comparison. The order of
   `K_Y` is computed on `Y` itself.
4. Formal proofs of the classical inputs.

The library does not assume parts (A) or (B) of the paper's main theorem.

## Policy for classical inputs

`ClassicalRationalRigidity.constant` says that maps from an affine plane to a para-abelian
variety are constant. Its reference, its reduction to the literature and its search record
are in [Abelian/README.md](../SurfaceLib/Abelian/README.md).

`ClassicalAdjunction.normalizedDuality` is another explicit classical input.
It packages lci adjunction, determinant comparison and normalized top-degree Serre
duality for a general class of regular proper surfaces; it does not assert any
example's canonical triviality. Its exact scope, references, and unformalized
compatibilities are recorded in [Canonical/README.md](../SurfaceLib/Canonical/README.md).

`ClassicalDiagonalizableQuotient.torsor` is the third; the final statements do not use it.
Its independent definition
of torsor tests all scheme-valued points, including nonreduced test schemes.
It packages the general SGA 3 graded-algebra quotient theorem and gluing, while
the actual example's homogeneous covers are proved. Its precise scope and
action compatibility requirements are recorded in
[GroupScheme/README.md](../SurfaceLib/GroupScheme/README.md). Compatibility of the
action with the Euler weights is included explicitly. Equivariance of the
canonical comparison is not proved, and the final statements do not use it.

Future missing inputs must be independently stated, general classical results, passed explicitly to
theorems rather than installed as global axioms. Every input must have an exact
reference, complete hypotheses, a record of the search for existing formal
proofs, and a list of consumers.

The permitted subjects are canonical-sheaf comparison and adjunction, finite-flat
duality with naturality, fpqc descent, diagonalizable graded quotients and gluing,
norm-based projectivity and miracle
flatness, dimension/Jacobian/normality criteria, and rigidity of maps from rational
varieties to abelian varieties. This list does not authorize assuming the
example-specific conclusions or the canonical-character lemma.

The pinned mathlib has ordinary derivation, eigenspace, abelian group-scheme,
and several fpqc morphism-descent APIs. Those must be checked before introducing
a missing input. They do not supply the complete canonical-sheaf, projectivity,
or torsor interfaces needed by this example.

## Verification

From `lean/`, run:

```sh
lake build
python3 verify.py
python3 verify_eff.py
```

The original `Red61` statement and audit are preserved. The separate Eff audit
checks every imported project declaration, source coverage, and the fingerprints of
the implemented theorems, including the two final statements. It exports the checked
types of the classical interfaces and their independent duality and torsor data. Its
status report and manifest state which classical inputs the final statement takes.

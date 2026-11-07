# Canonical comparison and its classical boundary

This library adds an explicit conditional bridge from the differential line in
`Red61` to the normalized relative canonical sheaf. It leaves the original
unconditional theorem and its audit untouched.

## Independent canonical-sheaf characterization

`TopDuality F f n K` consists of:

1. finite presentation of the actual sheaf `K`;
2. an `F`-linear trace `Hⁿ(X,K) → F`;
3. for every finitely presented sheaf `M`, bijectivity of the actual pairing
   `Hom(M,K) → Hom_F(Hⁿ(X,M),F)` induced by that trace.

On a Noetherian proper Cohen--Macaulay scheme of dimension `n`, this is the
standard characterization of the relative canonical sheaf. Cohomology is the
existing Ext-from-the-structure-sheaf construction. The new `Cohomology F f`
type tags it with the specified structure morphism, so the field action cannot
silently use a different base map. This does not identify the canonical sheaf
with an arbitrary sheaf that has merely been given that name.

`TopDuality.lean` proves, without classical geometric assumptions, existence and
uniqueness of the trace-preserving comparison between two such sheaves, its
inverse, and its compatibility with composition. These are global sheaf
isomorphisms. No local isomorphisms are glued without a compatibility argument.

## The supplied classical theorem

`ClassicalAdjunction` is a proposition with the single field
`normalizedDuality`. It is passed explicitly as a parameter; the library supplies
no inhabitant and installs no global instance.

The field states that, for **any** regular proper integral Noetherian surface
`X/F` with the following hypotheses, the normalized differential determinant
`Red61.omega F f bF` satisfies `TopDuality F f 2`:

- `F` has characteristic five and is essentially of finite type over `F₅`;
- `bF` is a two-element basis of its absolute differential module;
- `X` has dimension two and its absolute differential sheaf is locally free of
  rank four.

It does not assume triviality of that determinant or any result about the
particular surface `S`. Its hypotheses are verified in `Eff/Canonical.lean`:
essential finite generation of `ell` is proved there, and the surface properties
come from the unchanged `Red61` development.

This is **one packaged interface containing several classical ingredients**, not
a claim that just one cited lemma supplies its entire statement:

- lci adjunction identifies the relative canonical sheaf locally with
  `det(I/I²)ᵛ ⊗ det(Ω_ambient/F)`, with compatible changes of presentation;
- cotangent transitivity and determinants identify this line with the normalized
  absolute determinant;
- relative normalization and Serre duality give the trace and perfect pairings
  used by `TopDuality`, expressed in Ext cohomology.

The formal proofs of those classical ingredients, including their global
compatibilities, remain assumed in this interface. This implementation proves
uniqueness and applies the resulting comparison; it does **not** claim to have
formalized local adjunction gluing from scratch.

References and their roles:

- [Stacks 0E9Z](https://stacks.math.columbia.edu/tag/0E9Z), especially its proof:
  the local complete intersection adjunction expression. Its stated global
  factorization hypotheses must not be silently treated as already proved here.
- [Stacks 08QR](https://stacks.math.columbia.edu/tag/08QR): cotangent transitivity.
- [Stacks 0FJW](https://stacks.math.columbia.edu/tag/0FJW): determinants of complexes.
- [Stacks 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ): duality on a proper,
  equidimensional Cohen--Macaulay scheme over a field.

These references support the mathematical corollary; none is asserted to contain
the complete Lean interface verbatim. The pinned mathlib has Ext, field-linear
categories, finitely presented sheaves, and conormal sequences. Searches under
`AlgebraicGeometry`, `RingTheory`, and the module-sheaf APIs did not find a
normalized dualizing-sheaf/Serre-duality or presentation-independent adjunction
implementation. Existing local determinant calculations are retained in `Red61`.

The mathematical argument for using absolute differentials is over `F₅`:
regular essentially finite type algebras over that perfect field are essentially
smooth. Ordinary differentials over `Z` and `F₅` agree in characteristic five,
but the corresponding cotangent complexes need not. Local freeness of ordinary
differentials alone is not used as a replacement for smoothness in that argument.

## What the application proves

`Eff.Canonical.canonicalSheaf_trivial adjunction K DK` proves
`Nonempty (K ≅ structureSheafModule S)` for any independently characterized
canonical sheaf `K` with top-duality data `DK`. Its proof composes the comparison
with `Red61.Contraction.omegaIsoStructureSheaf`.

`Eff.Canonical.exists_trivial_canonicalSheaf adjunction` also gives existence of
such a trivial canonical sheaf. This is the line-bundle formulation of `K_S ∼ 0`;
no new definition of a canonical Cartier divisor is introduced.

The result is conditional on the explicit classical interface. The existing
quotient-properties theorem remains unconditional. Equivariance for the new
`μ₅` action and compatibility under arbitrary base change are still required
for the Eff canonical-character calculation; trace-preserving composition in
`TopDuality` does not by itself prove those stronger statements.

The Eff audit exports the checked types of the classical field and all fields
of `TopDuality`, and fingerprints the conditional theorem including its inputs.
Logical dependency lists alone would not reveal mathematical parameters.

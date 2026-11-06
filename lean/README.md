# Lean formalization of Theorem 6.1 of arXiv:2604.05293

This repository is a Lean 4 formalization, built on mathlib, of Theorem 6.1 of

> [Chongning Wang (王崇宁)](https://chongningwang.github.io) and Lei Zhang, *Geometric singularities of regular surfaces with nef
> anti-canonical divisors over imperfect fields*,
> [arXiv:2604.05293v3](https://arxiv.org/abs/2604.05293v3).

> **Theorem 6.1.** Let $\ell=\mathbb F_5(s_1,s_2)$. Then there exists a projective regular
> surface $S$ over $\ell$ with $H^0(S,\mathcal O_S)=\ell$ and $K_S\equiv0$ such that
> $S$ is geometrically non-reduced over $\ell$.

## What Lean proves

The main theorem is `Red61.Contraction.exists_theorem61_omega_rationalBase` in
[`Red61/Theorem61.lean`](Red61/Theorem61.lean):

```lean
theorem exists_theorem61_omega_rationalBase :
    ∃ (Y : Scheme) (f : Y ⟶ Spec (CommRingCat.of k)),
      IsProper f ∧ IsIntegral Y ∧ IsNoetherian Y ∧ topologicalKrullDim Y = 2 ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      Function.Bijective (globalScalarMap k f) ∧ ¬ GeometricallyReduced f ∧
      IsLocallyFreeOfRank 4 (nativeAbsoluteDifferentialModule Y) ∧
      let ω := omega k f rationalBaseAbsoluteDifferentialBasis
      Nonempty (ω ≅ structureSheafModule Y) ∧ IsCurveNumericallyTrivial k f ω
```

Here `k` is `FractionRing (MvPolynomial (Fin 2) (ZMod 5))`, that is
$k=\mathbb F_5(s_1,s_2)$. In words: there are a scheme $Y$ and a morphism
$f\colon Y\to\mathrm{Spec}\,k$ such that

1. $f$ is proper;
2. $Y$ is integral, noetherian and of dimension 2;
3. every local ring of $Y$ is regular;
4. the map $k\to H^0(Y,\mathcal O_Y)$ is bijective;
5. $Y$ is not geometrically reduced over $k$;
6. the sheaf of absolute differentials $\Omega_{Y/\mathbb Z}$, which equals
   $\Omega_{Y/\mathbb F_5}$, is locally free of rank 4
   ([`IsLocallyFreeOfRank`](Red61/AlgebraicGeometry/Modules.lean));
7. the sheaf
   $\omega=\mathcal{H}om_{\mathcal O_Y}\bigl(f^*\bigwedge^2\Omega_{k/\mathbb Z},\,\bigwedge^4\Omega_{Y/\mathbb Z}\bigr)$,
   defined in [`Red61/Omega.lean`](Red61/Omega.lean), is isomorphic to $\mathcal O_Y$;
8. $\omega$ has degree 0 on every proper integral curve $g\colon C\to Y$: here the degree
   is $\chi(g^*\omega)-\chi(\mathcal O_C)$ with $\chi=\dim H^0-\dim H^1$
   ([`Red61/CurveNumericalTriviality.lean`](Red61/CurveNumericalTriviality.lean)).

The notions in items 1–5 are mathlib's. The scheme $Y$ is the surface `S` constructed
explicitly in `Red61/Surface/` from affine charts, an invariant quotient and a contraction.
The proof assumes no geometric hypotheses, and its only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## What is not formalized

Compared with Theorem 6.1:

- **Projectivity.** Lean proves that $f$ is proper, not that $Y$ is projective.
- **The canonical class.** Lean's $\omega$ is defined from absolute differentials. Its
  identification with the canonical sheaf $\omega_{Y/k}=\det L_{Y/k}$ of the local
  complete intersection $Y/k$, whose divisor class is $K_Y$, is standard but not
  formalized. Since $Y$ is regular of finite type over $k$, it is a local complete
  intersection. The transitivity triangle
  $f^*L_{k/\mathbb F_5}\to L_{Y/\mathbb F_5}\to L_{Y/k}$, with
  $L_{k/\mathbb F_5}\simeq\Omega_{k/\mathbb F_5}[0]$ free of rank 2, and item 6 give
  $L_{Y/\mathbb F_5}\simeq\Omega_{Y/\mathbb F_5}[0]$ and
  $\omega_{Y/k}\cong\bigwedge^4\Omega_{Y/\mathbb F_5}\otimes f^*(\bigwedge^2\Omega_{k/\mathbb F_5})^\vee\cong\omega$.
  With item 7 this gives $\omega_{Y/k}\cong\mathcal O_Y$, so $K_Y\sim0$, and in
  particular $K_Y\equiv0$.
- **Cohomology.** In item 8, cohomology is defined as $\mathrm{Ext}^n(\mathcal O_Y,-)$
  in sheaves of $\mathcal O_Y$-modules, and the Lean code does not compare it with other
  definitions. Item 8 also follows directly from item 7.

## Structure

The active library contains 42 modules, exactly the import closure of
`Red61.Theorem61`, in four layers:

- `LinearAlgebra/`, `RingTheory/`, `Foliation.lean` and `AlgebraicGeometry/`: general
  mathematics, independent of the paper's base field (exterior powers, localization,
  regularity, Kähler differentials, p-closed derivations, sheaves of modules, differential
  and exterior-power sheaves, rational forms, principal atlases);
- `Surface/`: the construction of the surface and its properties;
- `Canonical/`: local differential bases, the invariant volume and the proof that
  $\omega\cong\mathcal O_Y$;
- `Theorem61.lean`, `Omega.lean`, `CurveNumericalTriviality.lean`: the statement.

Each merged file lists the former modules it contains.

[`proper_regular_surface_rationalBase_properties`](Red61/Surface/Properties.lean)
proves, for the constructed surface `S`, properness, integrality, Noetherianity, dimension two,
regularity of every stalk, the prescribed global constants, and geometric
nonreducedness without geometric inputs.

The active proof has the following components:

| Component | Files |
|---|---|
| Base field, derivations, invariant field and constants | [Surface/Field](Red61/Surface/Field.lean), [Foliation](Red61/Foliation.lean), [Surface/SixChartModel](Red61/Surface/SixChartModel.lean) |
| Coordinate charts and quotient construction | [Surface/Charts](Red61/Surface/Charts.lean), [Surface/Quotient](Red61/Surface/Quotient.lean) |
| Properness, regularity, dimension, constants and geometric nonreducedness | [Surface/Projective](Red61/Surface/Projective.lean), [Surface/GeometricNonreduced](Red61/Surface/GeometricNonreduced.lean), [Surface/Properties](Red61/Surface/Properties.lean) |
| Absolute differential bases on affine neighborhoods and stalks | [Canonical/CINeighborhoods](Red61/Canonical/CINeighborhoods.lean), [Canonical/Volume](Red61/Canonical/Volume.lean) |
| Differential, exterior and framed Hom sheaves | [AlgebraicGeometry/Differentials/Basic](Red61/AlgebraicGeometry/Differentials/Basic.lean), [AlgebraicGeometry/ExteriorPower](Red61/AlgebraicGeometry/ExteriorPower.lean), [AlgebraicGeometry/Modules](Red61/AlgebraicGeometry/Modules.lean) |
| Explicit omega and its trivialization by the invariant volume | [Omega](Red61/Omega.lean), [Canonical/OmegaTrivialization](Red61/Canonical/OmegaTrivialization.lean), [Canonical/Volume](Red61/Canonical/Volume.lean) |
| Curve Euler degree and the main theorem | [CurveNumericalTriviality](Red61/CurveNumericalTriviality.lean), [Theorem61](Red61/Theorem61.lean) |

The environment uses Lean **4.34.1** and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, pinned in the project files.
Run verification from this directory:

```bash
lake exe cache get   # download prebuilt mathlib; without it mathlib compiles from source
lake build
python3 verify.py
```

`verify.py` checks that every source module is imported by the default build,
rejects proof placeholders and prohibited declarations, builds the project,
and checks `#print axioms` for the main theorem and every owned project
declaration, including private auxiliaries. The allowed logical axioms are only
`Classical.choice`, `Quot.sound`, and `propext`. It also compares a fingerprint
of the main statement with the value pinned in `verify.py`. The fingerprint hashes,
by content, the elaborated types and definition bodies of all project constants the
statement depends on: proofs are ignored, and private, auxiliary and instance
constants are hashed by their own content, not their names, so moving declarations
between files does not change it. Any change to the statement or to those
definitions makes the check fail until the pinned value is updated on purpose.

The latest completed full verification is recorded in
[`verification/status.txt`](verification/status.txt), with the detailed
[`build log`](verification/build.log) and [`axiom log`](verification/axioms.log).
The audit itself is [Audit.lean](Audit.lean).

## License

Apache License 2.0; see [LICENSE](LICENSE). [`third_party/NOTICES.txt`](third_party/NOTICES.txt)
records the origin and license of adapted code.

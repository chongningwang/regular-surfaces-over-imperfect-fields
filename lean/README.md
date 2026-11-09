# Lean formalization

This directory is a Lean 4 project, built on mathlib, for the papers in
[`papers/`](../papers). Each library has its own README:

- [`Red61`](Red61/README.md): Theorem 6.1 of the red paper.
- [`Eff`](Eff/README.md): Example `ex:case-C-p5` of the eff paper, and the parts of
  Theorem 6.1 that `Red61` leaves out.
- [`SurfaceLib`](SurfaceLib/README.md): general mathematics developed for `Eff`, for reuse.
- [`Geonormal`](Geonormal/README.md): Example `ex:p19` of the geonormal paper, at `p = 19`, and
  Proposition `prop:p11`, at `p = 11`.

## Results

| Paper | Statement | Content | Classical inputs |
| --- | --- | --- | --- |
| red, Theorem 6.1 | [<code>Red61.Contraction.<wbr>exists_theorem61_<wbr>omega_rationalBase</code>](Red61/README.md#what-lean-proves) | A proper, integral, regular surface $S$ over $\mathbb F_5(s_1,s_2)$ with constants the base field, not geometrically reduced, whose sheaf $\omega$ built from absolute differentials is trivial | none |
| red, Theorem 6.1 | [`Eff.s_example`](Red61/README.md#completing-theorem-61) | $S$ is projective | none |
| red, Theorem 6.1 | [`Eff.theorem_6_1`](Red61/README.md#completing-theorem-61) | Every canonical sheaf of $S$ is trivial | `ClassicalAdjunction` |
| eff, Example `ex:case-C-p5` | [`Eff.y_example`](Eff/README.md) | A projective, integral, regular surface $Y$ over $\mathbb F_5(s_1,s_2)$ with constants the base field, not geometrically normal, whose determinant of differentials, normalized by the base, has exact order 5 | none |
| eff, Example `ex:case-C-p5` | [`Eff.case_C_p5`](Eff/README.md) | Every canonical sheaf of $Y$ has exact order 5, and the Albanese morphism of $Y$ is its structure morphism | `ClassicalAdjunction`, `ClassicalRationalRigidity` |
| geonormal, Example `ex:p19`, $p=19$ | [`Geonormal.p19_example`](Geonormal/README.md) | A projective, integral, regular surface $X$ over $\mathbb F_{19}(c)$ with constants the base field, not smooth over it, whose absolute differentials are locally free of rank 3 and whose determinant of differentials, normalized by the base, is trivial | none |
| geonormal, Example `ex:p19`, $p=19$ | [`Geonormal.p19_canonical`](Geonormal/README.md) | Every canonical sheaf of $X$ is trivial | `GeneralClassicalAdjunction` |
| geonormal, Proposition `prop:p11`, $p=11$ | [<code>Geonormal.P11.<wbr>p11_example</code>](Geonormal/README.md#proposition-propp11-at-p--11) | A projective, integral, regular surface $X$ over $\mathbb F_{11}(c)$ with constants the base field, not geometrically normal, whose absolute differentials are locally free of rank 3 and whose determinant of differentials, normalized by the base, is trivial | none |
| geonormal, Proposition `prop:p11`, $p=11$ | [<code>Geonormal.P11.<wbr>p11_canonical</code>](Geonormal/README.md#proposition-propp11-at-p--11) | Every canonical sheaf of $X$ is trivial | `GeneralClassicalAdjunction` |

The only axioms are `propext`, `Classical.choice` and `Quot.sound`. A classical input
is a general theorem that is hard to formalize. It is passed to the statement as an
explicit hypothesis, never installed as an axiom; see the
[policy for classical inputs](Eff/README.md#policy-for-classical-inputs).
`GeneralClassicalAdjunction` is `ClassicalAdjunction` for every prime characteristic and
every rank of the base differentials; `ClassicalAdjunction` is one of its cases.

## Size

Lean source files, excluding mathlib and the build output in `.lake/`:

| Library | Files | Lines |
| --- | ---: | ---: |
| `Red61` | 42 | 21,420 |
| `Eff` | 28 | 6,168 |
| `SurfaceLib` | 14 | 2,011 |
| `Geonormal` | 26 | 9,132 |
| Top-level files (`Red61.lean`, `Eff.lean`, `SurfaceLib.lean`, `Geonormal.lean`, `Audit.lean`, `EffAudit.lean`, `GeonormalAudit.lean`) | 7 | 568 |
| **Total** | **117** | **39,299** |

## Building and verifying

The project uses Lean **4.35.0** and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in the project files. The default
build contains `Red61`, `SurfaceLib`, `Eff` and `Geonormal`. From this directory:

```bash
lake exe cache get           # download prebuilt mathlib; without it mathlib compiles from source
lake build
python3 verify.py            # Red61
python3 verify_eff.py        # Eff and SurfaceLib
python3 verify_geonormal.py  # Geonormal and SurfaceLib
```

Each script rejects proof placeholders and prohibited declarations, checks
`#print axioms` for every project declaration, and compares fingerprints of the main
statements with pinned values. `Eff`, `Geonormal` and `SurfaceLib` do not change `Red61` or
its audit. The latest results are in [`verification/`](verification/status.txt) for
`Red61`, [`verification/eff/`](verification/eff/status.txt) for `Eff`, and
[`verification/geonormal/`](verification/geonormal/status.txt) for `Geonormal`.

## License

Apache License 2.0; see [LICENSE](LICENSE). [`third_party/NOTICES.txt`](third_party/NOTICES.txt)
records the origin and license of adapted code.

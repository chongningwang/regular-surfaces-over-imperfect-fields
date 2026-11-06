# Regular surfaces over imperfect fields

This repository brings together papers and Lean code from the study of regular
projective surfaces over imperfect fields, with a focus on surfaces whose canonical
divisor is numerically trivial.

## Main results

Let $X$ be a regular projective surface over an arbitrary field $k$, with

$$
K_X \equiv 0, \qquad H^0(X,\mathcal O_X)=k.
$$

Write $p=\mathrm{char}(k)$. The following results hold:

| Characteristic | Conclusion | Paper |
| --- | --- | --- |
| $p\geq 7$ | $X$ is geometrically integral over $k$. | [red](papers/red/main.tex) |
| $p\geq 13$ | $X$ is geometrically normal over $k$. | [geonormal](papers/geonormal/intro.tex) |
| $p\geq 23$ | $X$ is smooth over $k$. | [geonormal](papers/geonormal/intro.tex) |

In every characteristic, the canonical divisor satisfies

$$
60K_X\sim 0.
$$

Thus its order in $\mathrm{Pic}(X)$ divides $60$; see the
[uniform bound in eff](papers/eff/main.tex#L145).

### Examples

Each example below satisfies the same hypotheses on $X$, over a suitable
imperfect field $k$ of the indicated characteristic.

| Example | Characteristic | Property | Construction |
| --- | --- | --- | --- |
| 1 | $p=5$ | $X$ is geometrically non-reduced. | [red](papers/red/main.tex#L1089) |
| 2 | $p=5$ | $\mathrm{ord}(K_X)=5$. | [eff](papers/eff/main.tex#L2704) |
| 3 | $p=11$ | $X$ is geometrically non-normal. | [geonormal](papers/geonormal/counterexample.tex) |
| 4 | $p=19$ | $X$ is not smooth over $k$. | [geonormal](papers/geonormal/sharpness.tex) |

Here $\mathrm{ord}(K_X)$ is the order of $\mathcal O_X(K_X)$ in
$\mathrm{Pic}(X)$. Examples 1, 3, and 4 show that the respective characteristic
bounds above are optimal. Example 2 shows that the factor $5$ is necessary in the
uniform canonical bound.

### Papers

| Directory | Paper | Authors | Read | Supporting material |
| --- | --- | --- | --- | --- |
| [red](papers/red/main.tex) | Geometric singularities of regular surfaces with nef anti-canonical divisors over imperfect fields | Chongning Wang and Lei Zhang | [arXiv:2604.05293](https://arxiv.org/abs/2604.05293), [PDF](papers/red/main.pdf) | [Lean construction associated with Theorem 6.1](lean/README.md) |
| [eff](papers/eff/main.tex) | Effective nonvanishing of K-trivial regular surfaces over imperfect fields | Jingshan Chen, Chongning Wang, and Lei Zhang | [arXiv:2610.09542](https://arxiv.org/abs/2610.09542), [PDF](papers/eff/main.pdf) | Manuscript and bibliography |
| [geonormal](papers/geonormal/main.tex) | Geometric singularities of K-trivial regular surfaces | Chongning Wang | [PDF](papers/geonormal/main.pdf) | [Verification appendix](papers/geonormal/verification-scripts.tex), [smoothness computations](papers/geonormal/smooth/README.md), and [characteristic 11 computations](papers/geonormal/p11/README.md) |

The first two papers, **red** and **eff**, are already available on arXiv.
The **geonormal** manuscript is a work in progress: the author is still checking and
revising its AI-assisted proofs. Comments and corrections are welcome.
The Lean formalization covers the construction documented below; it does not
provide formal verification of all three papers.

## Lean proof

The only example currently treated in Lean is **Example 1**, the geometrically
non-reduced surface in characteristic $5$, associated with Theorem 6.1 of the
[red paper](papers/red/main.tex). Its base field is $k=\mathbb F_5(s_1,s_2)$.
The main formal statement is
`Red61.Contraction.exists_theorem61_omega_rationalBase` in
[Red61/Theorem61.lean](lean/Red61/Theorem61.lean).


## Licensing

- The manuscripts in `papers/`, including their LaTeX sources, bibliographies and
  compiled PDFs, are licensed under the Creative Commons Attribution 4.0
  International License (CC BY 4.0); see [papers/LICENSE](papers/LICENSE).
- The Lean code, Python and Singular verification scripts, recorded computation
  outputs, repository documentation and configuration files are licensed under
  the Apache License 2.0; see [LICENSE](LICENSE). The supporting computation
  directories [smooth](papers/geonormal/smooth/LICENSE) and
  [p11](papers/geonormal/p11/LICENSE) include their own copies of this license,
  as does the standalone verification archive.

Third-party code retains its existing license and notices; see
[lean/third_party/NOTICES.txt](lean/third_party/NOTICES.txt).


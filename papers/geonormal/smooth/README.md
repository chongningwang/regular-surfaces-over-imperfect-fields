# Enumeration of exceptional configurations for the smoothness theorem

These scripts carry out the computer-assisted step of Section `sec:smooth` (`smoothness.tex`):
Proposition `prop:smooth-enum` (if `Z != 0` and `p >= 29`, then `d = 4`), which together with Lemma
`lem:smooth-tangent` (`d <= 3`) gives Theorem `thm:smooth` for `p = 1 mod 4`, `p <= 6912`.
All exceptional curves lie over the non-rational singular point by Lemma `lem:smooth-numerical`,
so each enumeration uses `r = 8+d`, with `1 <= d <= 4`.
The scripts, running instructions and saved outputs are distributed in the companion archive
`../verification-scripts.zip`, with the directory structure preserved.
Appendix `app:verification-scripts` (`../verification-scripts.tex`) summarizes their inputs and outputs.

| script | checks | used in |
|---|---|---|
| `configs.py` (Python 3, sympy, networkx) | lists all matrices `A = -(E_i.E_j)` satisfying Lemmas `lem:smooth-numerical` and `lem:smooth-config`(2),(3) with `r = 8+d`, `1 <= d <= 4`; prints their determinants, the primes `>= 29` among them (53 and 113, both with `d = 4`, `r = 12`) and their configurations up to isomorphism (one each) | Proposition `prop:smooth-enum` |
| `crosscheck.py` (Python 3, numpy, networkx) | independent recomputation, over all trees with `r = 8+d` vertices, of the determinants of configurations with transversal intersections and no triple points; must agree with the `simple-tree dets` lines of `configs.py` | proof of Proposition `prop:smooth-enum` |
| `p17.py` (Python 3, sympy, networkx; imports `configs.py`) | runs the search of `configs.py` with `r = 8+d`, `1 <= d <= 4`, and lists the configurations with `det A` equal to 17 or 17^3 up to isomorphism: exactly one, with `d = 2`, `r = 10` | Proposition `prop:small-primes-sing` |
| `p13.py` (Python 3, sympy, networkx; imports `configs.py`) | searches with `r = 8+d` and `det A` equal to 13 or 13^3: no configurations for `d = 1,2,3`; one for `d = 4`, excluded by the tangent-cone argument | Proposition `prop:small-primes-sing` |

Outputs are saved in `configs.out`, `crosscheck.out` and `p17.out`. Run and compare:

```
python3 configs.py > configs.out
python3 crosscheck.py > crosscheck.out
python3 p17.py > p17.out
diff <(grep simple configs.out | sed 's/^ *//') <(sed 's/^d=[0-9]* r=[0-9]*: //' crosscheck.out)
```

The `diff` prints nothing. Tested with Python 3.14, sympy 1.14.0, networkx 3.2.1 and numpy 2.3.5; on 16 cores
`configs.py` takes about 30 seconds and `crosscheck.py` about 7 minutes.

`python3 small_primes_checks.py` checks the equations in Example `ex:small-primes`
in `../sharpness.tex` for every prime 5 <= p <= 19: the discriminants and node identities,
the common twist, and the exceptional charts and double-point resolutions.
`Singular -q small_primes_local.sing` independently checks the local algebra over t=0
in characteristic 5, and the Tjurina number p of each geometric `A_(p-1)` point.

`python3 small_primes_lift_checks.py` checks the characteristic-19 lift in Proposition
`prop:small-primes-lift` in `../sharpness.tex` over `Z[c]_(19)`.
It verifies smoothness at t=0, the equation at infinity, the two charts of its single
blowup, their unit derivatives modulo 19, and the discriminant whose nineteen simple
roots in characteristic zero coalesce modulo 19.

`python3 nonrational_checks.py` checks the models in Example
`ex:nonrational-small-primes` in `../sharpness.tex` for p=7 and p=11:
regularity by eliminating c, the infinity equations and the characteristic-7
resolution, the geometric local equations, and the canonical-form pole giving
discrepancy -1. It uses the resolution helpers in `small_primes_checks.py`.

`python3 p13.py` and `python3 p17.py` give the exceptional configurations used
in Proposition `prop:small-primes-sing` in `../singularities.tex`. In the relevant
range `r = 8+d`, `1 <= d <= 3`, characteristic 13 has no configurations and
characteristic 17 has one, with `d = 2`, `r = 10`, and determinant 17.
`Singular -q p17_local.sing` independently checks one representative of that
characteristic-17 configuration: its Tjurina number is 19, no partial derivative
is redundant, and the normalized plane blowup has Tjurina number 8.
The proof's derivation obstruction covers every analytic type with this graph.

## License

The scripts, recorded outputs and documentation in this directory are licensed
under the Apache License 2.0; see [LICENSE](LICENSE).

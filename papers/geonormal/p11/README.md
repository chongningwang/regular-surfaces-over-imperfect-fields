# Verification scripts for the characteristic-11 counterexample

These scripts check the computational claims in Section `sec:p11`
(`counterexample.tex`), Proposition `prop:p11`.
The gradient and valuation identities are proved directly in that section.
Both source files below and their running instructions are distributed in the companion archive
`../verification-scripts.zip`.
Appendix `app:scripts-p11` (`../verification-scripts.tex`) summarizes their checks.

| script | checks | used in |
|---|---|---|
| `p11_checks.py` (Python 3, sympy) | table of the derivatives `d^i x` and `d^10 x = u^10`; `theta^11 = Q`; residue of `Q` along `u = 0`; value `c^9` of `xi^11 Q` at the point at infinity; orders 2 and 11 of `d'Q` and `(d theta)^11` along `u = 0`; the coordinate identities and `delta(beta) = 5r/(xi beta) + r^-2` | Lemmas `lem:p11-equations`, `lem:p11-regular`, `lem:p11-omega-zero`, `lem:p11-nonnormal` |
| `ekedahl.sing` (Singular) | with `h = gcd(Q_c, Q_a, Q_b)` in `F_11[c,a,b]`, the quotients `Q_c/h, Q_a/h, Q_b/h` generate the unit ideal (an explicit certificate is computed and checked) | Lemma `lem:p11-regular` |

Run:

```
python3 p11_checks.py
Singular -q ekedahl.sing
```

Tested with sympy 1.14.0 and Singular 4.4.1. Both finish in under a second.

## License

The scripts and documentation in this directory are licensed under the Apache
License 2.0; see [LICENSE](LICENSE).

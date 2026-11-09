# Geonormal: Example `ex:p19` at `p = 19` and Proposition `prop:p11`

This library formalizes the case `p = 19` of Example `ex:p19` of the [geonormal
manuscript](../../papers/geonormal/sharpness.tex), and, in the namespace `Geonormal.P11`,
[Proposition `prop:p11`](#proposition-propp11-at-p--11) at `p = 11`.

`Geonormal.p19_example` uses no classical input. It proves that `X`, over `k = 𝔽₁₉(c)`, is
projective, proper, integral, regular and two-dimensional, has global constants `k`, and is
not smooth over `k`. It also proves that the absolute differentials of `X` are locally free of
rank three, and that the normalized differential line
`xOmega = Hom(O_X ⊗_k Ω_{k/ℤ}, ⋀³ Ω_{X/ℤ})` is trivial.

`Geonormal.p19_canonical` uses exactly one explicit parameter, `GeneralClassicalAdjunction`. It
proves that `X` has a canonical sheaf and that every canonical sheaf of `X` is trivial.

All checked logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

Not formalized: that `X_k̄` has exactly one singular point, of type `A₁₈`, and the elliptic
fibration. Only non-smoothness over `k` is proved. `IsProjectiveOver` is as in `Eff`: `Proj`
of a finitely generated graded algebra with degree-zero part the field. The algebra used here
is generated in degree one by construction, but the statement does not record this.

## The surface

`k = FractionRing (MvPolynomial (Fin 1) (ZMod 19))`, with `c` the variable. The function field
is `F = k(x, t)[y] / (y² - x³ - c²t⁷x - t)`. In the manuscript, `X` is the blowup of the
Weierstrass model of this curve over `ℙ¹_k` at its double point over `t = ∞`. In Lean, `X` is
glued from five affine charts `y_i² = g_i(e₁, e₂)`, all inside `F`; the blowup description is
not formalized.

| Chart | `e₁` | `e₂` | `y_i` | `g_i` |
| --- | --- | --- | --- | --- |
| 0 | `t` | `x` | `y` | `e₂³ + c²e₁⁷e₂ + e₁` |
| 1 | `t` | `1/x` | `y/x²` | `e₂ + c²e₁⁷e₂³ + e₁e₂⁴` |
| 2 | `1/t` | `x/t³` | `y/t⁵` | `e₁e₂³ + c²e₂ + e₁⁹` |
| 3 | `t³/x` | `x/t⁴` | `y/(t²x)` | `e₂ + c²e₁ + e₁¹¹e₂⁹` |
| 4 | `1/t` | `t⁴/x` | `t²y/x²` | `e₂ + c²e₁e₂³ + e₁¹¹e₂⁴` |

## What is proved

| Module | Verified content |
| --- | --- |
| `Field`, `Charts` | The fields `k ⊂ E = k(x, t) ⊂ F`, the chart monomials, and the chart rings |
| `Atlas` | The principal atlas: all 25 overlaps are principal localizations; `X19`, `xToBase` |
| `Projective` | `X` is the `Proj` of an explicit graded subalgebra of `F[T]`; `x_projective`, `x_proper` |
| `Constants` | `H⁰(X, O_X) = k`: `x_globalScalarMap_bijective` |
| `Regular` | Every local ring is regular, from Jacobian certificates: `x_stalk_regular` |
| `Dimension` | `x_dimension : topologicalKrullDim X19 = 2` |
| `NotSmooth` | Over `k[u]/(u¹⁹ - 1/c)`, the point `t = 17u⁶`, `x = 12u²`, `y = 0` has a tangent vector that does not lift modulo `ε³`: `x_not_smooth` |
| `Differentials` | On each chart, `dc, de₁, de₂` is a basis of the differentials of `F`; on the principal open where `∂h/∂X_{m+1}` is a unit, the other three coordinate differentials form a basis; `x_differentials_locallyFree` |
| `Volume` | `dc ∧ dt ∧ dx / (2y)` generates the differential lattice at every point, so it trivializes `⋀³ Ω_{X/ℤ}`: `xVolumeIso` |
| `Example` | The base field, `xOmega ≅ O_X`, and the final statements |

The polynomial identities behind the Jacobian certificates were found with Singular and are
checked in Lean by `linear_combination`.

## Proposition `prop:p11` at `p = 11`

The namespace `Geonormal.P11` formalizes Proposition `prop:p11` of the [geonormal
manuscript](../../papers/geonormal/counterexample.tex).

`Geonormal.P11.p11_example` uses no classical input. It proves that `X`, over
`k = 𝔽₁₁(c)`, is projective, proper, integral, regular and two-dimensional, has global
constants `k`, and is not geometrically normal: its base change to `k' = k(c^{1/11})` is not
normal. It also proves that the absolute differentials of `X` are locally free of rank three,
and that the normalized differential line `xOmega` is trivial. `Geonormal.P11.p11_canonical`
uses the same parameter `GeneralClassicalAdjunction` and proves that `X` has a canonical sheaf
and that every canonical sheaf of `X` is trivial.

Not formalized: the genus-one fibration `X → ℙ¹_k` and the fibre computations of the
manuscript; in Lean, `X` is glued directly from four charts. Normality is
`SurfaceLib.IsNormalScheme` (every local ring is an integrally closed domain), and geometric
normality is mathlib's `geometrically`.

### The surface

The function field is `L = 𝔽₁₁(a, b, σ)`, containing `k = 𝔽₁₁(c)` with
`c = 6(ab³ - 3a⁴b - σ¹¹)`. Put `u = b² - a³` and `w = 1/u`. The field
`K' = 𝔽₁₁(γ, x', y')` contains `k' = k(γ)`, `γ¹¹ = c`, and `ι : L → K'` sends `a, b, σ` to
`x'¹¹/w'⁴, y'¹¹/w'⁶, s/w'² - 2γ`, where `w' = y'² - x'³` and `s = x'y'(y'² - 3x'³)`. `X` is
glued from four affine charts inside `L`:

| Chart | Ring | Relation over `𝔽₁₁` |
| --- | --- | --- |
| `A` | `k[a, b, σ]` | none |
| `B` | `k[u, α, β, ρ]` with `α = 1/a`, `β = b/a²`, `ρ = σ + 2b/a` | `β² = α + uα⁴` |
| `D` | `k[w, α″, β″, ρ]` with `α″ = u⁴/a`, `β″ = u²b/a²` | `β″² = α″ + w¹¹α″⁴` |
| `P` | `k[ξ₀, …, ξ₁₀]` with `ξ_n = θ_n/u²` | `ι(ξ_n) = r_n(γ, x', y')` |

Here `θ_n = (2∂_σ)ⁿθ/n!` for the polynomial `θ` of the manuscript, and `r_n` is the
`γⁿ`-component of `x'`, so that `P ⊗_k k' = k'[x', y']`. The chart `P` contains the cusp `P₀`
of the fibre over `u = ∞`; all other points of `X` lie on `A`, `B` or `D`.

### What is proved

| Module | Verified content |
| --- | --- |
| `P11/Field`, `P11/Charts` | The fields `k ⊂ L` and `k' ⊂ K'`, the embedding `ι`, the elements `θ_n`, `ξ_n`, and the chart rings |
| `P11/Components` | `1, γ, …, γ¹⁰` are linearly independent over `ι(L)`, and `k'[x', y'] = ⊕ ι(P)γⁱ` |
| `P11/BChart`, `P11/DChart`, `P11/Atlas` | The principal atlas: all 16 overlaps are principal localizations; `X11`, `xToBase` |
| `P11/Projective` | `X` is the `Proj` of an explicit graded subalgebra of `L[T]`; `x_projective`, `x_proper` |
| `P11/Constants` | `H⁰(X, O_X) = k`, since `k'` is algebraically closed in `K'`: `x_globalScalarMap_bijective` |
| `P11/Dimension` | `x_dimension : topologicalKrullDim X11 = 2` |
| `P11/Regular` | `A`, `B`, `D` are hypersurfaces over `𝔽₁₁` with Jacobian certificates; at `P₀`, `ξ₀, ξ₁` generate the maximal ideal, by taking `γ⁰`-components in `k'[x', y']`; the other points of `P` lie on `A` or `D`: `x_stalk_regular` |
| `P11/Differentials` | On the principal open of `A`, `B` or `D` where `∂h/∂X_m` is a unit, the other three coordinate differentials form a basis |
| `P11/PointP0` | `ξ_n ∈ 𝔪₀²` for `n ≥ 2`, from the relations `E_m`; by Nakayama `dc, dξ₀, dξ₁` is a basis on a principal open around `P₀`; `dc ∧ dξ₀ ∧ dξ₁ = δ · da ∧ db ∧ dσ` with `ι(δ) = ½ ∂(r₀, r₁)/∂(x', y')`, a unit at `P₀` |
| `P11/Volume` | `x_differentials_locallyFree`; `da ∧ db ∧ dσ` trivializes `⋀³ Ω_{X/ℤ}`: `xVolumeIso` |
| `P11/Nonnormal` | `A ⊗_k k'` is not integrally closed: with `τ = σ + 2γ`, `g = (aτ + 2b)⁶/u` is integral, and its `γ⁶`-component `(2a)⁶/u` is not in `A`; `x_not_geometrically_normal` |
| `P11/Example` | The base field, `xOmega ≅ O_X`, and the final statements |

The identities in characteristic 11 are checked in Lean by `grind` and `linear_combination`.

## Classical input

`SurfaceLib.Canonical.GeneralClassicalAdjunction` is `ClassicalAdjunction` for every prime
characteristic `p` and every size `r` of a basis of `Ω_{F/ℤ}`. It states normalized duality for
`SurfaceLib.Canonical.omegaR`, which is `Red61.omega` for `r = 2`. The Eff interface
`ClassicalAdjunction` is its case `p = 5`, `r = 2`
(`GeneralClassicalAdjunction.toClassicalAdjunction`), so the Eff statements are unchanged.
Here it is used with `r = 1`, for `p = 19` and for `p = 11`. See the
[canonical comparison documentation](../SurfaceLib/Canonical/README.md).

## Verification

From `lean/`, `python3 verify_geonormal.py` builds `Geonormal` and `SurfaceLib`, runs
[`GeonormalAudit.lean`](../GeonormalAudit.lean), and compares the fingerprints of the four final
statements with pinned values. The latest results are in
[`verification/geonormal/`](../verification/geonormal/status.txt).

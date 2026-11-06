"""Exact checks for the characteristic-19 lift in Proposition prop:small-primes-lift."""
import sympy as sp

s, u, v, c, t, x, y = sp.symbols("s u v c t x y")
base = sp.QQ.frac_field(c)
affine = y**2-x**3-c**2*t**7*x-t
infinity = v**2-u**3-c**2*s*u-s**11

assert sp.diff(affine, t).subs({t: 0, x: 0, y: 0}) == -1
substitution = {t: 1/s, x: u/s**4, y: v/s**6}
assert sp.cancel(s**12*affine.subs(substitution, simultaneous=True)-infinity) == 0

quadratic = v**2-c**2*s*u
hessian = sp.factor(sp.hessian(quadratic, (s, u, v)).det())
assert hessian == -2*c**4
assert not sp.Poly(hessian, c, modulus=19).is_zero

charts = [
    (s, u, {u: s*u, v: s*v}, v**2-c**2*u-s*u**3-s**9),
    (u, s, {s: u*s, v: u*v}, v**2-c**2*s-u-u**9*s**11),
]
for exceptional, other, substitution, expected in charts:
    strict = sp.cancel(infinity.subs(substitution, simultaneous=True)/exceptional**2)
    assert sp.expand(strict-expected) == 0
    assert sp.Poly(strict, v).is_monic
    for coefficient in sp.Poly(strict, s, u, v, domain=base).coeffs():
        denominator = sp.fraction(coefficient)[1]
        assert not sp.Poly(denominator, c, modulus=19).is_zero
    derivative = sp.diff(strict, other).subs(exceptional, 0)
    assert derivative == -c**2
    assert not sp.Poly(derivative, c, modulus=19).is_zero
    print(f"PASS {exceptional}-chart: exact identity, monic equation, unit derivative -c^2")

discriminant = sp.expand(-16*(4*(c**2*t**7)**3+27*t**2))
factor = 4*c**6*t**19+27
assert sp.expand(discriminant+16*t**2*factor) == 0
assert sp.Poly(factor, t, domain=base).degree() == 19
assert sp.gcd(sp.Poly(factor, t, domain=base),
              sp.Poly(sp.diff(factor, t), t, domain=base)).degree() == 0
assert sp.Poly(sp.diff(factor, t), t, c, modulus=19).is_zero
print("PASS p=19: smooth origin, infinity equation, one-blowup resolution over Z[c]_(19)")
print("PASS discriminant: nineteen distinct roots in characteristic zero, coalescing modulo 19")

"""Exact checks for Example ex:nonrational-small-primes, in p=7 and p=11."""
import sys

sys.dont_write_bytecode = True

import sympy as sp
from small_primes_checks import check_e8

x, y, t, c, s, u, v, z = sp.symbols('x y t c s u v z')


def main():
    for p in (7, 11):
        f = y**2 - x**3 - t**p - c
        assert sp.expand(f.subs(c, y**2 - x**3 - t**p)) == 0
        assert sp.diff(f, c) == -1
        assert sp.Poly(sp.diff(f, t), t, modulus=p).is_zero
        infinity = v**2 - u**3 - s**(12-p) - c*s**12
        substitution = {x: u/s**4, y: v/s**6, t: 1/s}
        assert sp.expand(s**12*f.subs(substitution, simultaneous=True) - infinity) == 0
        if p == 7:
            check_e8(infinity, p)
        else:
            assert sp.diff(infinity, s).subs({s: 0, u: 0, v: 0}) == -1
        discriminant = -16*27*(t**p+c)**2
        assert sp.expand(discriminant + 432*(t**p+c)**2) == 0
        a = sp.Symbol('a')
        local = f.subs({t: z+a, c: -a**p}, simultaneous=True)
        assert sp.Poly(local - (y**2-x**3-z**p), x, y, z, a, modulus=p).is_zero
        weighted = sp.expand((y**2-x**3-z**p).subs(
            {x: z**2*u, y: z**3*v}, simultaneous=True)/z**6)
        assert weighted == v**2-u**3-z**(p-6)
        jacobian = sp.Matrix([[sp.diff(z**2*u, u), sp.diff(z**2*u, z)],
                              [0, 1]]).det()
        assert sp.cancel(jacobian/(2*z**3*v) - 1/(2*z*v)) == 0
        assert p-6 in (1, 5)
        print(f'PASS p={p}: regularity, infinity, geometric local equation, and discrepancy -1')


if __name__ == '__main__':
    main()

"""Exact checks for the unified A_(p-1) example, for every prime 5 <= p <= 19."""
import sympy as sp

s, u, v, t, x, y, c, a, beta = sp.symbols('s u v t x y c a beta')
SHORT = {5: (5, 5), 7: (5, 4), 11: (5, 2), 13: (5, 1),
         17: (7, 2), 19: (7, 1)}


def poly(f, p, variables=(s, u, v)):
    return sp.Poly(sp.expand(f), *variables, domain=sp.GF(p).frac_field(c))


def blow(f, p, chart):
    if chart == s:
        f = f.subs({u: s*u, v: s*v}, simultaneous=True)/s**2
    else:
        f = f.subs({s: u*s, v: u*v}, simultaneous=True)/u**2
    return poly(f, p).as_expr()


def homogeneous(f, p, degree):
    return poly(sum(coef*s**i*u**j*v**k for (i, j, k), coef in poly(f, p).terms()
                    if i+j+k == degree), p).as_expr()


def ordinary(f, p, point=None):
    if point:
        f = f.subs({var: var+value for var, value in point.items()}, simultaneous=True)
    assert homogeneous(f, p, 0) == homogeneous(f, p, 1) == 0
    q = homogeneous(f, p, 2)
    coefficient = poly(q, p).coeff_monomial(s*u)
    assert coefficient != 0
    assert poly(q-v**2-coefficient*s*u, p).is_zero


def check_d4(f, p):
    assert homogeneous(f, p, 2) == v**2
    q = poly(homogeneous(f, p, 3), p)
    lam, mu = q.coeff_monomial(s*u**2), q.coeff_monomial(s**2*u)
    assert lam != 0 and mu != 0
    fs, fu = blow(f, p, s), blow(f, p, u)
    assert poly(fs.subs(s, 0)-v**2, p, (u, v)).is_zero
    assert poly(fu.subs(u, 0)-v**2, p, (s, v)).is_zero
    assert poly(sp.diff(fs, s).subs({s: 0, v: 0})-(lam*u**2+mu*u), p, (u,)).is_zero
    assert poly(sp.diff(fu, u).subs({u: 0, v: 0})-(lam*s+mu*s**2), p, (s,)).is_zero
    ordinary(fs, p)
    ordinary(fs, p, {u: -mu/lam})
    ordinary(fu, p)


def check_e8(f, p):
    # At the first two blowups, the other chart is smooth along its exceptional curve.
    other = blow(f, p, u)
    assert poly(sp.diff(other, u).subs({u: 0, v: 0}), p, (s,)).degree() == 0
    f1 = blow(f, p, s)
    derivative = poly(sp.diff(f1, s).subs({s: 0, v: 0}), p, (u,))
    assert len(derivative.terms()) == 1 and derivative.degree() == 3
    other = blow(f1, p, s)
    assert poly(sp.diff(other, s).subs({s: 0, v: 0}), p, (u,)).degree() == 0
    f2 = blow(f1, p, u)
    derivative = poly(sp.diff(f2, u).subs({u: 0, v: 0}), p, (s,))
    assert len(derivative.terms()) == 1 and derivative.degree() == 3
    ordinary(blow(f2, p, u), p)
    check_d4(blow(f2, p, s), p)


def check_e7(p, exponent):
    f = v**2-u**3-c**2*s**3*u-s**exponent
    other = blow(f, p, u)
    assert poly(sp.diff(other, u).subs({u: 0, v: 0})+1, p, (s,)).is_zero
    f1 = blow(f, p, s)
    ordinary(blow(f1, p, s), p)
    f2 = blow(f1, p, u)
    check_d4(f2, p)


def main():
    for p, (m, n) in SHORT.items():
        assert 3*m-2*n == p and m <= 8 and n <= 12
        r = -sp.Rational(3, 2)/(c**2*a**(m-n))
        relation = sp.Poly(4*c**6*a**p+27, a, c, modulus=p)
        for expression in [3*r**2+c**2*a**m, 2*r**3-a**n,
                           -m*c**2*a**(m-1)*r-n*a**(n-1)]:
            numerator = sp.together(expression).as_numer_denom()[0]
            assert sp.Poly(numerator, a, c, modulus=p).rem(relation).is_zero
        f = y**2-x**3-c**2*t**m*x-t**n
        original = (beta**(3*n)*y)**2-(beta**(2*n)*x)**3 \
            -(beta**6*t)**m*(beta**(2*n)*x)-(beta**6*t)**n
        assert sp.expand(original-beta**(6*n)*f.subs(c**2, beta**(2*p))) == 0
        if m == 5:
            check_e7(p, 12-n)
        if n == 5:
            check_e8(v**2-u**3-s**5, p)
        print(f'PASS p={p}: node identities, twist, and resolutions')

    # The E6 point in characteristic 7 becomes a split A5 point after one blowup.
    f1 = blow(v**2-u**3-s**4, 7, s)
    assert poly(f1-(v**2-(s+u**3/2)**2+u**6/4), 7).is_zero
    print('PASS: the characteristic-7 E6 point has a crepant resolution over k')


if __name__ == '__main__':
    main()

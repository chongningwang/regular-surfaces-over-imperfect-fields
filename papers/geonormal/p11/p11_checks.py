#!/usr/bin/env python3
"""Verification of the polynomial identities used in Section "A counterexample in
characteristic 11" (counterexample.tex).  Requires sympy.  Run:  python3 p11_checks.py

Notation as in the paper: E: y^2 = x^3 + u^5 over K = k(u), k = F_11(c);
d is the derivation with d x = 2y, d y = 3x^2, d u = 0;
a = x^11/u^18, b = y^11/u^27 (so b^2 = a^3 + u);
theta = sum_{i<=10} (-gamma/u)^i d^i(x)/i!,  gamma^11 = c.
"""
import sympy as sp

p = 11
u, x, y, a, b, c, s = sp.symbols('u x y a b c s')
REL = y**2 - x**3 - u**5


def red(e):
    """Reduce a polynomial in x, y, u modulo y^2 = x^3 + u^5 and modulo 11."""
    r = sp.rem(sp.expand(e), REL, y)
    return sp.Poly(r, x, y, u, modulus=p).as_expr()


def d(f):
    """The derivation d on F_11[u, x, y]/(y^2 - x^3 - u^5)."""
    return red(sp.diff(f, x) * 2 * y + sp.diff(f, y) * 3 * x**2)


def same(e1, e2, gens):
    return sp.Poly(sp.expand(e1 - e2), *gens, modulus=p).is_zero


def inv(n):
    return pow(n % p, p - 2, p)


fact = [1]
for i in range(1, 12):
    fact.append(fact[-1] * i % p)

# 1. The derivatives d^i x (table in the paper) and d^10 x = u^10, d^11 x = 0.
D = [x]
for i in range(11):
    D.append(d(D[-1]))
table = {1: 2*y, 2: 6*x**2, 3: 2*x*y, 4: 10*x**3 + 4*u**5, 5: 5*x**2*y,
         6: 2*x**4 + 9*u**5*x, 7: 5*x**3*y + 7*u**5*y, 8: x**5 + 7*u**5*x**2,
         9: 10*x**4*y + 6*u**5*x*y, 10: u**10}
for i, e in table.items():
    assert same(D[i], e, (x, y, u)), i
assert D[11] == 0
print("1. table of d^i x verified; d^10 x = u^10 and d^11 x = 0")


# 2. theta^11 = Q.  (d^i x)^11 = P_i(u^11, x^11, y^11) with x^11 = u^18 a, y^11 = u^27 b.
def eleventh(P):
    Pi = sp.Poly(P, x, y, u)
    return sum((co % p) * (u**18*a)**e1 * (u**27*b)**e2 * u**(11*e3)
               for (e1, e2, e3), co in Pi.terms())


Qc = sum(((-1)**i * inv(fact[i])) % p * c**i * u**(-11*i) * eleventh(D[i]) for i in range(11))
Qc = sp.expand(Qc)
assert all(sp.degree(t, u) >= 0 for t in sp.Add.make_args(Qc)), "Q has negative powers of u"
Q = (-c**10 + c**9*a**4*b + 5*c**9*u*a*b - 2*c**8*u**2*a**5 - 3*c**8*u**3*a**2
     + 3*c**7*u**4*a**3*b + 2*c**7*u**5*b - 4*c**6*u**6*a**4 + 4*c**6*u**7*a
     + 5*c**5*u**8*a**2*b + 5*c**4*u**10*a**3 + 2*c**4*u**11 - 4*c**3*u**12*a*b
     + 3*c**2*u**14*a**2 - 2*c*u**16*b + u**18*a)
assert same(Qc, Q, (u, a, b, c))
print("2. theta^11 = Q (formula in the paper) verified")


# Order along u = 0 in k[a,b] (u = b^2 - a^3 prime) and residue in k(s), a = s^2, b = s^3.
def ord_res(e, shift=300):
    e = sp.expand(e * u**shift)
    P = sp.Poly(e, u, a, b, c, modulus=p)
    red_terms = {}
    for (eu, ea, eb, ec), co in P.terms():
        ex = sp.expand(co * u**eu * a**ea * b**(eb % 2) * (a**3 + u)**(eb // 2) * c**ec)
        for mon, co2 in sp.Poly(ex, u, a, b, c, modulus=p).terms():
            red_terms[mon] = (red_terms.get(mon, 0) + co2) % p
    red_terms = {m: v for m, v in red_terms.items() if v}
    m0 = min(m[0] for m in red_terms)
    lead = sum(v * a**m[1] * b**m[2] * c**m[3] for m, v in red_terms.items() if m[0] == m0)
    res = sp.Poly(sp.expand(lead.subs({a: s**2, b: s**3})), s, c, modulus=p).as_expr()
    return m0 - shift, res


o, r = ord_res(Q)
assert o == 0 and same(r, c**9*s**11 - c**10, (s, c))
print("3. Q has residue c^9 s^11 - c^10 along u = 0")

# 4. Point at infinity: every monomial u^m a^i b^j of Q has 2i + 3j <= 11, and equality
#    holds only for c^9 a^4 b.  Hence xi^11 Q is regular at O with value c^9 there.
PQ = sp.Poly(Q, u, a, b, c)
eq = [(m, co) for m, co in PQ.terms() if 2*m[1] + 3*m[2] == 11]
assert all(2*m[1] + 3*m[2] <= 11 for m, co in PQ.terms())
assert eq == [((0, 4, 1, 9), 1)]
print("4. xi^11 Q is regular at the point at infinity O with value c^9")

# 5. d'Q = 2b dQ/da + 3a^2 dQ/db (u fixed) and (d theta)^11, orders along u = 0.
dQ = sp.expand(2*b*sp.diff(Q, a) + 3*a**2*sp.diff(Q, b))
o1, r1 = ord_res(dQ)
Q1 = sp.expand(sum(((-1)**i * inv(fact[i])) % p * c**i * u**(-11*i) * eleventh(D[i+1])
                   for i in range(10)))
o2, r2 = ord_res(Q1)
assert o1 == 2 and same(r1, c**8*(2*s**11 - c), (s, c))
assert o2 == 11 and same(r2, c**8*(2*s**11 - c), (s, c))
print("5. d'Q = u^2 * (unit), residue c^8(2s^11 - c);  (d theta)^11 = u^11 * (unit), same residue")

# 6. Coordinates for the non-normality lemma: t = y/x, r = x/t^2, xi = u^9/t^11, beta = t^5/u^4.
t = y / x
r = x / t**2
xi = u**9 / t**11
beta = t**5 / u**4


def zero_mod_rel(e):
    num, den = sp.fraction(sp.together(sp.expand(e)))
    return red(num) == 0


A = x**11 / u**18
Bv = y**11 / u**27
assert zero_mod_rel(u - xi**5 * beta**11)
assert zero_mod_rel(t - xi**4 * beta**9)
assert zero_mod_rel(A / Bv - xi)
assert zero_mod_rel(A - xi**(-2) * r**11)
assert zero_mod_rel(Bv - xi**(-3) * r**11)
assert zero_mod_rel(r**3 - r**2 + xi * beta)
# delta(beta) = u^{-1} d(beta), with d t = (x d y - y d x)/x^2 = (3x^3 - 2y^2)/x^2
dt = (3*x**3 - 2*y**2) / x**2
delta_beta = u**(-1) * 5 * t**4 * u**(-4) * dt
assert zero_mod_rel(delta_beta - (5*r/(xi*beta) + r**(-2)))
dxi = u**9 * (-11) * t**(-12) * dt
assert zero_mod_rel(dxi)
print("6. coordinate identities and delta(beta) = 5r/(xi beta) + r^-2, delta(xi) = 0 verified")
print("all checks passed")

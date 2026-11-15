"""h29-split numeric checks: Hurwitz quaternions of odd prime norm p (as 2*alpha = (a,b,c,d),
a = b = c = d mod 2, a^2+b^2+c^2+d^2 = 4p, |coords| <= 2p, i.e. the Lean `hurwitzNorm p`) number 24(p+1);
apE p (Lean: -sum_{x<p} jacobi(x^3-x, p)) equals p + 1 - #E(F_p) for E: y^2 = x^3 - x."""
from itertools import product
from sympy import jacobi_symbol, primerange

def hurwitz_count(p):
    R = range(-2 * p, 2 * p + 1)
    c = 0
    for a, b, cc, d in product(R, repeat=4):
        if (a - b) % 2 == 0 and (a - cc) % 2 == 0 and (a - d) % 2 == 0 and a*a + b*b + cc*cc + d*d == 4 * p:
            c += 1
    return c

def apE(p):
    return -sum(jacobi_symbol((x**3 - x) % p, p) for x in range(p))

def ap_count(p):
    pts = 1 + sum(1 for x in range(p) for y in range(p) if (y*y - (x**3 - x)) % p == 0)
    return p + 1 - pts

for p in primerange(3, 14):
    print(p, hurwitz_count(p), 24 * (p + 1), apE(p), ap_count(p))

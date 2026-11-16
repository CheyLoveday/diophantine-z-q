# cd-optimal log

Task: prove `ZInQ.GZOptimal.CdOptimal` (ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean) or reduce it.
Base wip/gz-optimal 2631cd0b. Build tree copied from ~/dzq-wt/gz-optimal (.lake/build, lean/.lake/build).

## Numerics (py/)

* `py/lev32.gp`, `py/lev32b.gp` (output `py/lev32b_out.txt`, 3888 rows, all (a, c), c = 32k, k <= 24,
  1 <= a <= c, gcd(a,c) = 1, max rounding error 1e-18): rho(gamma) = Phi_1(gamma tau) - Phi_1(tau) for
  gamma in Gamma0(32), in the basis (w1, w2) = E.omega of C_1 : y^2 = x^3 - x (w1 = Omega real, w2 = -i Omega).
  VERIFIED (computed): every coordinate is in (1/2)Z with x + y in Z, both kinds occur:
  Lambda_{f_1} = ((1+i)/2) L_1 (rhombic; X0(32) = 32a1, C_1 = 32a2).
* `py/analyze.py`: VERIFIED (computed, same sample): rho(gamma) in L_1 iff a = +-1 mod 8 (a = gamma_00), i.e.
  rho mod L_1 is the congruence character chi_8(d) (d = gamma_11, ad = 1 mod 8). The other two characters of
  Lambda_1/2Lambda_1 (restricted to d = +-1 mod 8: rho mod (1+i)L_1) do NOT depend on (a mod 256, c mod 512):
  non-congruence (as expected: unramified double covers of a genus-1 curve).
* `py/sroot.gp`, `py/sfit.gp`, `py/x1fit.gp`: with x = 2 + eta(2)^2eta(16)/(eta(4)eta(32)^2) (x0-32 model of
  32a1), s := sqrt(x^2+4) = eta(8)^5/(eta(4)^2 eta(16) eta(32)^2) (VERIFIED to q^20), and
  x1 := (x+s)/2 = q^-2 prod (1-q^m)^{e_m}, e_m = -1 (m = 4,28 mod 32), +1 (m = 12,20 mod 32): the reciprocal
  of the Goellnitz-Gordon (octic) continued fraction at q^4 -- a generalized eta quotient. x1 - 1/x1 = x.
  Identity: s = -y/w with w := eta(16)^3/(eta(8)eta(32)^2), w^2 = x (monomial identity from x = eta16^6/(eta8^2 eta32^4)).
  w has character (2/d) on Gamma0(32) by Gordon-Hughes/Newman (prod delta^r = 2^-1); all exponent sums OK.

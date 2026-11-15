# h29-fix results log

Base: origin/wip/h29-split 14503253. Contributor file under revision: copy of
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` (not edited in place; revised copy in scratch/h29-fix/).

## Step 1. Computations (2026-11-15)

* `brandt.py` (output `brandt-output.txt`), exact arithmetic. Model X = O_B^x \ (O_B/4O_B)^x (derivation in
  report §2). VERIFIED:
  - #X = 8, every left O_B^x-orbit has 24 elements (TYZ Lemma 2.5, L646-651: 8 classes, uniform measure).
  - the 8 elements 1 + 2x, x = a i + b j + c zeta (a,b,c in {0,1}), represent the 8 classes (Lemma 2.5, first map).
  - chi_0 o nrd on 1+2x is (-1)^c = (-1)^{tr x}.
  - dim A_0^U (orthogonal to 1 and chi_0 o nrd) = 6 (TYZ Thm 2.4(1), L777).
  - Hecke: for every odd prime p < 40, T_p = a_p(E) on A_0^U (a_p by point count of y^2 = x^3 - x);
    T_p 1 = (p+1) 1, T_p chi_0 = chi_0(p)(p+1) chi_0. [the unprinted bridge, checked for p < 40]
  - n = 3, all 8 admissible tau (tau(sqrt -3) = +-i +-j +-k): pi^{U_3} one-dimensional (TYZ Thm 2.6),
    integral generator f_3 takes values {1, -3} or {-1, 3}; **Q(3) = f_3(1) = +-3** for every tau
    (Cl_3 = 1, so 2Cl_3 = {1}).
  - n = 11 (4 taus), n = 19 (3 taus): one-dimensional, Q(n) = +-1.
* `lcal_small.py` (PARI 40 digits, output `lcal-output.txt`): TYZ's L(n)^2 = 1 at n = 1, 3, 11, 19; 4 at 17;
  0 at 41. VERIFIED numerically (19 digits).
* Verdict at n = 3: Lemma 2.9 printed (L1062-1066) says eps L(3) L(1) = Q(3), i.e. +-1 = +-3: FALSE.
  Theorem 2.1 (L554-559) at (d1,d2) = (3,1): P(3,1) = Q(3) (Cl_3 = 1, chi trivial) = +-2^{1-1} w_K L(3) L(1) = +-3:
  TRUE. **Lemma 2.9 is misprinted** (the factor w_K of Theorem 2.1 is dropped in its statement; the proof
  L1068-1077 gives w_K * sum = Q(n)). At n = 11, 19 (w_K = 1) both agree (+-1).
* `regular_form.py` (output `regular-output.txt`): every n = 1 (mod 8), n <= 10^6, is x^2 + y^2 + 16 z^2; the
  integers <= 10^6 not represented are exactly n = 3 (4), 6 (8), 12 (16), 4^a(8k+7). VERIFIED (exhaustive).
* Mathlib 4.35 has no three-square theorem (grep for three_sq / sum_three / three squares in
  .lake/packages/mathlib/Mathlib: only Nat.sum_four_squares). VERIFIED.

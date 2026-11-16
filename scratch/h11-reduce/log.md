# h11-reduce results log

Base origin/main 0caafe66. TYZ source Period7.tex: NOT on this host (~/tyz-src absent; searched ~/dzq, ~/notes,
~/local, ~/persistent, ~/dzq-runs, /tmp). TYZ line numbers below are quoted from earlier notes.

## Findings (before Lean)

1. VERIFIED (read in Leaves.lean / TYZLemma29Mod2.lean): the open leaves TYZLemma29PrintedNe3 and TYZThm21At31
   quantify over integer sign choices `ℓ : ℕ → ℤ` with `ℓ(m)^2 = lcalSq m` on all classes 1, 3. If h11 failed at
   one m, no such ℓ exists and both leaves are vacuously true. So h11 cannot be derived from the open leaves as
   stated; a form of Lemma 2.9 over real/complex square roots of 𝓛² (TYZ's 𝓛 is a real number) is needed.
2. TYZ's integrality argument (induction on divisors through Lemma 2.9, L1082-1088 per rv-pn-encoding) fails at
   n = 3 (w_K = 3: gives 3𝓛(3) ∈ ℤ only) and needs 𝓛(1) = ±1 (L1082, asserted).
3. Plan: n = 1 and n = 3 from Tunnell's formula (Invent. Math. 72 (1983); theorem number UNVERIFIED):
   L(C_n,1) = β (B(n) − A(n)/2)² / (4√n), n odd squarefree, β = ∫₁^∞ dx/√(x³−x) = omegaInt,
   A(n) = #{2x²+y²+8z² = n}, B(n) = #{2x²+y²+32z² = n}. A(1) = B(1) = 2, A(3) = B(3) = 4 give
   lcalSq 1 = lcalSq 3 = 1. Then h11 by strong induction from Lemma 2.9 (complex ℓ, n ≠ 3).
   The n = 3 case of h29 is also covered by Tunnell, so TYZThm21At31 is no longer needed.

## Computations

* `tunnell_check.py` (cypari2 via `uv run --offline --with cypari2`): Tunnell's formula on 30 odd squarefree n
  (1..187, all classes mod 8): max |L(C_n,1) − β(B−A/2)²/(4√n)| = 2.2e-19 at 38-digit precision. VERIFIED
  (numerically). Also lcalSq(n) = ((A−2B)/2^{k+1})² on the sample (1, 1, 4, 1, 1, ..., 16 at n = 113, 9 at 131).

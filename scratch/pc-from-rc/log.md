# pc-from-rc results log

## 2026-11-17 setup
- Base 19fdd483. `lake build ZInQKernel.Hypotheses.PoleManuscript` OK (VERIFIED).
- PARI/cypari2 and sympy are NOT installed on this host (~/pyenv missing); numerics use plain python3.
- 2-adic Kummer image of E_l (l = 3 mod 4), classes (x+3l, x-l) in (Q_2^*/Q_2^*2)^2, sampled
  x = a/2^k (|a|<2000, k<8) for l mod 32 in {3,...,31}: exactly the 8 classes {a odd unit, b in {1,5} mod 8}
  (scratch/pc-from-rc/local2.py). VERIFIED (computed, sampling). So every 2-Selmer class has a, b odd and
  b = 1 mod 4: the manuscript's representative shape (no factor 2, L1062) comes from the 2-adic image,
  which the text does not spell out (ELLIOT).

## Lean, first deliverable (core)
- `ZInQKernel/Contrib/PoleRC/Defs.lean`: `LocM`, `SelM`, `CRM`, `SimultaneousConstruction` (defs only). COMPILED.
- `Rescale.lean`: `point_of_locM`, `polePoly_eq_zero_of`, `witnesses_of_points` (L1107-1121). COMPILED.
- `Bookkeeping.lean`: `bookkeeping` (L1020-1032): from B get bits b (m | 2730 positive), beta, theta
  squarefree, beta = 17, theta = 1 mod 24, coprime, mutual local squares (in ZMod p), A = beta s^2,
  H = theta c^2. COMPILED, axioms [propext, Classical.choice, Quot.sound].
  Construction used: B = N/D^2, N = k^2 r, r0 = gcd(r,2730), r1 = r/r0, f | 455 with f r1 = 17 mod 24,
  m = r0 f / gcd(r0,f)^2, beta = f r1, theta = sqfree part of T = D^2 - N/m, H = T (mB/D)^2.
- `Reduction.lean`: `poleCompleteness_of_crm : CRM -> SimultaneousConstruction -> Manuscript.PoleCompleteness`.
  COMPILED, axioms [propext, Classical.choice, Quot.sound].

## Lean, second deliverable (statement level)
- `CRM.lean`: `crm_of_restrictedConverse P (hRC : RestrictedConverse P) (h54 : Lemma54At P)
  (hK : KolyvaginRankOne) (hMW : MordellWeil) (hD : DescentGlueM) : CRM`. COMPILED.

## Numerics (plain python3, scratch/pc-from-rc/{selmer,compare,construct,batch}.py)
- compare.py: for all 55 squarefree l < 700, l = 11 mod 12, the brute-force explicit 2-Selmer set
  (local searches at p | 6l and R; good primes assumed unramified) EQUALS the set predicted by the local
  image formulas: R: a > 0; Q_2: a, b odd, b = 1 mod 4; Q_3: 3 does not divide b, b = 1 mod 3;
  q | l: (a,b) in span of torsion classes (l,1), (3,-l) mod Q_q^*2. 0 mismatches. VERIFIED (computed).
- selmer.py: l = 323 = 17*19: matrix conditions (ker K = <1,1_beta>, lambda not in im K) hold for
  beta = 17, and brute-force #Sel = 8 with (17,1) in Sel. VERIFIED (computed).
- batch.py: for 30 random beta (1-3 primes < 400, beta = 17 mod 24), theta = 1 (the random theta
  generator produced no theta > 1 -- weak test for theta), a random search over n = beta*q0*p_1..p_{d-1}
  (q0 = 7 mod 12, p_k = 1 mod 12, the slot types of L1042) found n with the matrix conditions for n
  in all 30 cases (within <= 308 tries); for n = 5627 = 17*331 brute force gives #Sel = 8, (17,1) in Sel.
  construct.py: (beta, theta) = (65, 97*193) also succeeded (n = 308487335).

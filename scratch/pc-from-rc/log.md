# pc-from-rc results log

## 2026-11-17 setup
- Base 19fdd483. `lake build ZInQKernel.Hypotheses.PoleManuscript` OK (VERIFIED).
- PARI/cypari2 and sympy are NOT installed on this host (~/pyenv missing); numerics use plain python3.
- 2-adic Kummer image of E_l (l = 3 mod 4), classes (x+3l, x-l) in (Q_2^*/Q_2^*2)^2, sampled
  x = a/2^k (|a|<2000, k<8) for l mod 32 in {3,...,31}: exactly the 8 classes {a odd unit, b in {1,5} mod 8}
  (scratch/pc-from-rc/local2.py). VERIFIED (computed, sampling). So every 2-Selmer class has a, b odd and
  b = 1 mod 4: the manuscript's representative shape (no factor 2, L1062) comes from the 2-adic image,
  which the text does not spell out (ELLIOT).

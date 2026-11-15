# fh-printed results log

Base 43513d87 (leaf-fold25). Prebuilt tree copied from ~/dzq-check2 (bc90deac, same Lean files).

## Plan (statements)
- Printed leaf: FH 1995 Thm B with (a) local conditions chi_v = chi0,v as norm-residue (Hilbert symbol)
  characters of Q_p^x / R^x, (b) chi as the idele class character of Q(sqrt d) (d squarefree),
  its Dirichlet coefficients from local components at unramified p, (c) root number = sign of the
  FE of the completed L-function for some conductor q (no conductor theorem), (d) "infinitely many"
  as Set.Infinite. L-value read as G(1) (step iii, remains a reading).
- Dictionary steps proved in Lean: local chars equal => D/D0 square in Q_p and D D0 > 0, D = 1 mod 4;
  idelic chi_d(n) = jacobiSym n |d| for d odd fundamental; Set.Infinite => forall B exists |D| > B.

## Compile log
- 11-15 06:10 scratch/fh-printed/LocalNorm.lean: IsLocalNorm, Hensel (p odd, p = 2 mod 8),
  descent lemma, p not a norm (unramified nonsquare), nonsquare unit not a norm (ramified): COMPILES (VERIFIED).
- 11-15 06:40 LocalNorm.lean: + p=2 non-norms (2 for d=5 mod 8, -1 for d=3 mod 4, 5 for d=2 mod 4), unit norms (p odd, p=2), infinity, isSquare_div_of_localNorm_iff (odd p), isSquare_div_two_of_localNorm_iff: COMPILES (VERIFIED)

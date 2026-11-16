# charpoly-ell results log

Base: origin/main 2880fef1 (fork main after leaf-fold31). Field `charPolyIndepOfEllAlgClosed`
(bundle `OpenTextbookLeaves12`, ZInQKernel/OneProof/H/TailZ42.lean:16), statement
`ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (ZInQKernel/Contrib/AVB1/AlgClosed.lean:51). VERIFIED (read).

## Findings

1. (VERIFIED, read) The tree has no notion of the degree of an isogeny (grep for degree/deg definitions on
   `PkgI3.AbVar`, function-field degree: none). No theorem of the cube, no Riemann–Roch on abelian varieties.
2. (VERIFIED, read) Open fields usable without a new leaf that speak about endomorphisms: `homFreeFiniteAlgClosed`
   (End(A) free of finite rank, `ℤ_ℓ ⊗ End → End(T_ℓ)` injective), `mumfordTorsionAlgClosed` (A[n] ≅ (ℤ/n)^{2g}),
   `milneIsogenyQuasiInverse`, `weilPairingMumford`, `phiAmpleIsogeny`. None gives an ℓ-independent integer
   invariant of an endomorphism; ℓ-independence of the characteristic polynomial needs one (the degree).
3. (VERIFIED, math) The sketch "det(n − T_ℓφ) and deg(n − φ) agree for every integer n because both compute the
   order of the kernel on ℓ-power torsion" only gives equality of ℓ-adic absolute values, and equality of
   |·|_ℓ at every integer does not determine a monic polynomial: for ℓ ≡ 3 (mod 4), X²+1 and X²+1+ℓ³ are
   ℓ-adic units at every integer (−1 is not a square mod ℓ) and are different. Mumford's/Milne's proof needs in
   addition that deg is a polynomial function on all of End⁰ (not only on n − φ) and multiplicative, plus a lemma
   on multisets in ℚ̄_ℓ tested against all F ∈ ℤ[T].

## Plan

Reduce the field to (a) the open field `homFreeFiniteAlgClosed` (only `Module.Finite ℤ (End A)` is used, for
integrality of φ) and (b) one new leaf: Mumford §19 Thm 4 first assertion, `deg φ = det T_ℓ(φ)`, over a
genuine Lean definition of `deg` (function-field degree [K(A) : ψ*K(A)] for finite surjective ψ, 0 otherwise).
The glue (Lean): det(n − V_ℓφ) = charpoly(V_ℓφ)(n) = deg(n − φ) ∈ ℤ for all n; Lagrange interpolation over ℚ;
uniqueness across ℓ by infinitely many integer values; integer coefficients from the roots of the characteristic
polynomial being roots of a monic integer polynomial annihilating φ (Mathlib `isIntegral_coeff_of_factors`).

## Compile log
- 2026-11-16 09:2x: `lake build ZInQKernel.Contrib.AVB1.AlgClosed` OK (9053 jobs).
- scratch/charpoly-ell/CharPolyEll.lean: `CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate
  (hD : DegEqDetTate) (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed`
  compiles; axioms [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
  Pure-algebra lemmas (any char-0 field): exists_rat_of_int_values (Lagrange), exists_int_of_rat
  (roots of charpoly are roots of a monic integer polynomial; isIntegral_coeff_of_factors; ℤ integrally closed),
  charpoly_eq_map_int, int_poly_ext. `degEnd` (function-field degree via stalk map at the generic point,
  0 unless finite surjective), leaf `DegEqDetTate`.
- 10:24: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.CharPolyIndepOfEllAlgClosed`
  OK (13699 jobs); frozenTarget standard axioms. VERIFIED.
- `#discharges`: DISCHARGES [OpenTextbookLeaves12.charPolyIndepOfEllAlgClosed] by
  ZInQ.Contrib.OneProof.CharPolyEll.charPolyIndepOfEllAlgClosed_of_degEqDetTate; still assumes [DegEqDetTate,
  HomFreeFiniteAlgClosed]; axioms standard. VERIFIED (Discharges-output.txt).
- autofold dry run: strict 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11. FoldDryRun.lean compiles,
  sixContactMin_of_open36 standard axioms. VERIFIED.

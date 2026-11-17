# derham-scholze: the de Rham and Hodge–Tate rows re-routed to the manuscript's `lem:de-rham-descent`

Task derham-scholze, 2026-11-17. Base `wip/derham-scholze` = `origin/wip/leaf-fold33b` (d67ea55f6; `origin/main` is
an ancestor). Log `scratch/derham-scholze/log.md`. Lean: `ZInQKernel/Contrib/OneProof/DeRhamScholze.lean` (scratch
copy `scratch/derham-scholze/DeRhamScholze.lean`).

## 1. Result

(RESULT-PLACEHOLDER)

## 2. The manuscript's lemma and what each row needs

`lem:de-rham-descent` (diophantine_zq.tex L10939-11004, step C3; read in full, VERIFIED) has four parts:

1. (L10953-10965) `A/F` is smooth proper, its analytification is smooth proper rigid; Scholze's Cor. 1.8 (with the
   corrigendum) makes `H^i` of the analytification de Rham; Thms 9.1 (coherent, hence filtered de Rham cohomology)
   and 9.3 (`ℤ/ℓⁿ`-cohomology, `ℓⁿ` invertible since `char F = 0`) identify it with the algebraic cohomology,
   compatibly with `G_F`; so `H¹_ét(A_{F̄}, ℚ_ℓ)` is de Rham.
2. (L10966-10974) Milne's canonical Galois-equivariant `V_ℓ(A) ≅ H¹_ét(A_{F̄}, ℚ_ℓ)^∨` (Milne v2.00 Part I Thm
   12.1(a)), closure under duals and subquotients (Brinon–Conrad 5.2.1, 6.3.3), coefficients: `r|_{G_F}` de Rham.
3. (L10976-10991) finite descent from `F'` to `K` (Brinon–Conrad 6.3.8, finite case, written out).
4. (L10993-10998) Hodge numbers of `H¹_dR(A/F)` are `2, 2`, so the Tate module has weights `0,0,−1,−1`, hence each
   summand `0, −1`; descent preserves them. L11001-11004: the Hodge–Tate comparison alone would not give de Rham.

The two research fields concern `V_p(A)` for an abelian variety `A` over a finite `F/ℚ_p` (no `r`, no coefficient
field, no descent):

* `deRhamVpAbVarDirect` (`DeRhamPrint.Direct.DeRhamVpAbVarDirect`, `DeRhamPrintDirect.lean` L187): `dim_{F'} D_dR(V_p A)
  = dim V_p A`. Parts 1-2 of the lemma.
* `hodgeTateDecompOr` (`ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr`): `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b` (or the Hom
  form), some `a, b`; its consumer (hodgetate-from-dr) proves `a = b = g` from the Weil pairing. Part 4 of the lemma
  (weights in `{0, −1}`), without the multiplicities.

Parts 3 and the coefficient step of part 2 are not used by these two fields and are not formalized here.

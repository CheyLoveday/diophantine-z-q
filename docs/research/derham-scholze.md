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

## 3. The new leaves and their ratings

### 3.1 `ScholzeDeRhamAlg` (Scholze 2013, Cor. 1.8 with Thms 9.1, 9.3, as the manuscript applies it)

```lean
def ScholzeDeRhamAlg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (X : Over (Spec (CommRingCat.of F))) [IsProper X.hom] [Smooth X.hom] (i : ℕ),
    IsDeRhamFam p (F := F) (rhoH X p i) ∧ HodgeRange p (F := F) (rhoH X p i) i
```

Objects (all genuine definitions; none introduced for the purpose):

* `Hⁱ(X_{F̄}, ℚ_p) = ℚ_p ⊗_{ℤ_p} Hⁱ(X_{F̄}, ℤ_p)` (`HQ`), where `Hⁱ(X_{F̄}, ℤ_p)` is **Mathlib's**
  `Scheme.EllAdicCohomology (X ×_F Spec F̄) p i` (pro-étale cohomology of the sheaf `U ↦ C(U, ℤ_p)`, Bhatt–Scholze
  2015 Def. 6.8.1; `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`), with t10-etale's `ℤ_p`-module structure
  (`T10Etale.lean`: multiplication on the coefficient sheaf through `Sheaf.H.map`, checked in degree 0).
* the action of `σ ∈ G_F`: transport along the scheme automorphism `1 × Spec(σ⁻¹)` of `X_{F̄}` (`galHX`; t10-etale's
  `transportₗ`, proved bijective and checked in degree 0). For an abelian variety and `i = 1` it is t10-etale's
  `galH` by `rfl` (`galHX_abVar`).
* `D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` (`ddrFam`, the carrier of the kernel's `ddrTensorOver`, `ddrFam_rep`); de Rham
  = finite-dimensional with `dim_{ℚ_p} D_dR = [F:ℚ_p] dim W` (`IsDeRhamFam`, the kernel's `IsDeRhamTensorOver` plus
  finite dimension).
* `Fil^j B_dR = 𝔪^j` (`filB`; `= t^j B_dR^+ = ξ^j B_dR^+`, `B_dR^+` a DVR, `TDict.tt_eq_varpi_mul_unit`), and
  `Fil^j D_dR = D_dR ∩ (Fil^j B_dR ⊗ W)` (`filD`); `HodgeRange … i` says `Fil⁰ D_dR = D_dR` and
  `Fil^{i+1} D_dR = 0`.

**Rating: consequence of the print, not printed form.** The print (Cor. 1.8, wording quoted from arXiv:1205.3463 by
h-leaves §3.1 and read again by the locator audit, `locators.md` row R10): for a proper smooth *rigid-analytic*
variety `X` over a complete discretely valued `k/ℚ_p` with perfect residue field, `Hⁱ(X_ét, ℚ_p)` is de Rham, with
associated filtered `k`-vector space `Hⁱ_dR(X)`. Mathlib has no rigid-analytic spaces and no algebraic de Rham
cohomology, so the print cannot be stated. The leaf is the algebraic statement the manuscript derives from it
(L10953-10965), through these steps:

1. the analytification of a proper smooth `F`-scheme is a proper smooth rigid space (manuscript L10953-10954);
2. Thm 9.1 (coherent, hence filtered de Rham cohomology) and Thm 9.3 (`ℤ/pⁿ`-cohomology, `p` invertible since
   `char F = 0`), compatibly in `n` and with `G_F` (manuscript L10955-10964);
3. *on-the-spot (dictionary)*: Scholze's `Hⁱ(X_ét, ℚ_p)` for `X/k` is the cohomology over the completed algebraic
   closure; the leaf uses `F̄`. Sketch: for `X` proper, étale cohomology with torsion coefficients is invariant
   under extension of algebraically closed fields (proper base change, SGA 4 XII 5.4; UNVERIFIED number), and
   Thm 9.3 compares over any complete algebraically closed field; take limits over `n`;
4. *on-the-spot (dictionary)*: Mathlib's `ℓ`-adic cohomology is pro-étale; the manuscript's (and Scholze's)
   `H¹_ét(·, ℤ_p)` is `lim_n H¹_ét(·, ℤ/pⁿ)`. Sketch: Bhatt–Scholze 2015 §5.6 (continuous cohomology equals
   pro-étale cohomology of `ℤ̂_p`; UNVERIFIED number); for `X_{F̄}` proper the groups `Hⁱ_ét(X_{F̄}, ℤ/pⁿ)` are finite,
   so `lim¹ = 0` and both sides are `lim_n Hⁱ_ét(X_{F̄}, ℤ/pⁿ)`;
5. the jump clause: the filtered isomorphism `D_dR(Hⁱ) ≅ Hⁱ_dR(X)` (part of Cor. 1.8) carries `Fil^j D_dR` to the
   Hodge filtration `Fil^j Hⁱ_dR = im Hⁱ(Ω^{≥j})`, which is everything for `j ≤ 0` and zero for `j ≥ i + 1`
   (`Ω^{≥j}` sits in degrees `≥ j`). This is the standard description of `Fil` on `D_dR` (`(Fil^j B_dR ⊗ V)^{G_F}`,
   `V` trivially filtered).

The leaf asserts nothing beyond the print plus these dictionary steps, and it does not mention the Hodge numbers
(not statable without `H_dR`).

### 3.2 `T10_TateDuality` (Milne, reused from t10-etale)

`T10Etale.T10_TateDuality` (t10-etale; `ZInQKernel/HDecomp/Textbook/T10Etale.lean`), unchanged: for `A/K` and
`ℓ ≠ char K`, a `ℤ_ℓ`-linear `φ : H¹(A_{K̄}, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` with `φ ∘ galH σ = (galT σ⁻¹)^∨ ∘ φ`, over
Mathlib's pro-étale cohomology. It is the manuscript's citation (Milne, *Abelian varieties* v2.00, Part I, Thm
12.1(a), L10966-10970) with the equivariance the manuscript states ("canonical, Galois-equivariant"); t10-etale's
docstring cites the refereed version (Milne 1986, Thm 15.1(a)). It was a textbook leaf `t10` of earlier bundle
generations (av-b2 §2.6: "leaf, confirmed") and is no longer open at this base (pruned as unused), so the fold adds
it back as a leaf. **Rating: printed form with dictionary** (the pro-étale/étale comparison of §3.1 step 4, and
equivariance from canonicity), flagged unread (Milne not read here).

### 3.3 Glue: `DeRhamHodgeTate01`

(GLUE-PLACEHOLDER)

## 5. Known issues

1. **Scholze's Cor. 1.8 is not statable in Lean as printed.** It is a theorem about proper smooth rigid-analytic
   varieties, with the filtered `k`-vector space `Hⁱ_dR(X)`; Mathlib v4.35 has neither rigid-analytic spaces nor
   algebraic de Rham cohomology. The leaf `ScholzeDeRhamAlg` is the algebraic form the manuscript itself derives
   (L10955-10965), so it is a *consequence* of the cited print through Thms 9.1/9.3 and two on-the-spot dictionary
   steps (§3.1 steps 3-4), not printed form. This is a limitation of the library, not a gap in the manuscript.
2. **Mathlib's `ℓ`-adic cohomology is pro-étale.** The manuscript, Scholze and Milne use étale cohomology
   (`lim H¹_ét(·, ℤ/ℓⁿ)`). The identification (Bhatt–Scholze 2015 §5.6) is not cited by the manuscript; it is an
   on-the-spot dictionary step (§3.1 step 4) shared with t10-etale's leaf.
3. **Milne's notes are unrefereed** (h-trust C3 classifies the manuscript's citation, Milne v2.00 Part I Thm 12.1(a),
   as [P]). The reused leaf `T10_TateDuality` cites the refereed Milne 1986 Thm 15.1(a) (UNVERIFIED number). Neither
   was read here. Milne states the identification over a separably closed field; the Galois equivariance the
   manuscript asserts ("canonical, Galois-equivariant") follows from canonicity, and the leaf states it.
4. **The weights are not read off Hodge numbers in Lean.** The manuscript's weight claim uses the Hodge numbers
   `2, 2` of `H¹_dR(A/F)` (L10993); `H_dR` is not in Mathlib. The Lean route keeps only what the filtered comparison
   gives without `H_dR` (Hodge jumps in `[0, 1]`), and the consumer of `hodgeTateDecompOr` already proves
   `a = b = g` from the Weil pairing (hodgetate-from-dr), so no Hodge number is needed downstream.
5. **"Consequently" (L10995) is Fontaine's de Rham ⇒ Hodge–Tate**, which the lemma does not cite. It is stated as
   the glue Prop `DeRhamHodgeTate01` and proved in Lean in `DeRhamScholzeHT.lean` (§4) from Tate's theorems and
   Fontaine's `t` (`FontaineTwistT`).
6. L11001-11004 (Hodge–Tate comparison alone would not give de Rham): respected. Neither row uses a Hodge–Tate
   decomposition as an input; the de Rham row uses only Scholze + Milne + duality, and the Hodge–Tate row derives the
   decomposition from the de Rham comparison.
7. The corrigendum (Forum Math. Pi 4 (2016) e6): per the locator audit (`locators.md` R10), it repairs the
   definitions of the period sheaves and keeps the comparison results; no issue for this use. Not re-read here.

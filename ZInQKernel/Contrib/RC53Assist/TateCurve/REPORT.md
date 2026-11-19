# Tate uniformization and additive inertia coinvariants

## Result and scope

Both retained targets have proved reductions to explicit literature inputs.
The target statements and all original files are unchanged. The contribution
consists only of new modules in `ZInQKernel/Contrib/RC53Assist/TateCurve/`.
Import `ZInQKernel.Contrib.RC53Assist.TateCurve.Main` for the complete contribution.

This is not an unconditional proof of the printed theorems. They remain
proposition parameters, not newly declared axioms. In particular, C1 is not a
proof from C.14.1 alone: its independent local-field and semistability inputs
are explicit below.

## Exact exported theorem types

In namespace `ZInQ.Contrib.RC53Assist.GlobalTrace`, with the printed inputs
from namespace `ZInQ.Contrib.RC53Assist.TateCurve` opened:

```lean
theorem tateCurveTateModulePrint_of_literature
    (hT : SilvermanC141TateUniformizationPrint)
    (hS : LocalSemistableTatePrint)
    (hV : LocalUnramifiedValueGroupPrint)
    (hF : LocalFrobeniusGenerationPrint) :
    TateCurveTateModulePrint

theorem additiveReductionCoinvariantsVanish_of_prints
    (hS : GrothendieckSemistableReductionPrint)
    (hW : SilvermanIII81GaloisWeilPairingPrint) :
    AdditiveReductionCoinvariantsVanish
```

These conclusions are exactly the existing propositions, with their original
quantifiers, modules, representations, inertia subgroups, and Frobenius
normalizations. There is no input supplying either conclusion, no replacement
for the actual Tate representation, and no weakening of either target.

## What is proved

### C1

- The coefficient equation of the Tate curve and a separate C.14.1 PRINT are
  stated without any Tate-module basis, Kummer cocycle, twist, or inertia clause.
- `uniformizationQuotientEquiv` converts the surjective uniformization with
  exact kernel `q^ℤ` to the literal quotient-group isomorphism.
- Compatible primitive roots of unity and compatible roots of every nonzero
  parameter exist in the algebraic closure (`kummerRoots_nonempty`).
- Their finite-level images are independent. The prescribed compatible
  generators give a basis of the actual inverse-limit Tate module by finite
  cardinality and compactness (`kummerTateBasis`). Its first and second vectors
  are exactly the compatible roots of unity and roots of the parameter.
- The signed Galois columns are derived from pointwise uniformization and
  Kummer-coordinate powers (`signed_kummer_columns`).
- Comparing actual Weierstrass isomorphisms proves the quadratic descent sign
  and its multiplicativity (`quadraticSignCharacter`), not an assumed twist
  formula on a supplied representation.
- Unipotence at multiplicative reduction forces the sign to be one on inertia.
- Reduction is injective on prime-to-residue-characteristic roots of unity;
  hence the cyclotomic coefficient is one on inertia.
- If all compatible roots of the parameter were inertia-fixed, its nonzero
  valuation would be divisible by every power of `ℓ`. This is impossible,
  proving nonzero Kummer inertia.
- Frobenius generation and descent of the scaling coefficient prove the sign
  at arithmetic Frobenius: one in the split case and minus one otherwise.
- `tate_character_cocycle_laws` derives the normalized character law and the
  crossed-homomorphism law `κ(gh) = κ(g) + χ(g)κ(h)`. The normalized character
  is unit-valued (`tateCyclotomicCharacter`).

### C2

The proof uses the directly printed semistable-reduction criterion instead
of a finite-extension case split. At an additive prime inertia is not entirely
unipotent. For a two-dimensional determinant-one action, a singular defect
`ρ(i)-1` has square zero. Therefore a nonunipotent inertia element has an
invertible defect, and its image alone makes the augmentation subspace all of
`V_ℓ(E)`. The inertia coinvariants are consequently zero.

Determinant one on inertia is derived from printed Galois equivariance of the
Weil pairing, the proved prime-to-`p` root-of-unity argument, and the already
proved alternating nondegenerate pairing determinant calculation.

The alternative linear-algebra mechanisms are also proved independently:
`augmentation_eq_top_of_finite_image` and
`augmentation_eq_top_of_ramified_tate`. Neither takes a fixed-vector or
coinvariant-vanishing assertion as an input.

## Literature boundaries and exact locators

1. **Tate uniformization:** manuscript bibitem `silverman`, J. H. Silverman,
   *The Arithmetic of Elliptic Curves*, second edition, Springer, 2009,
   Appendix C, §14, Theorem C.14.1. Section-level locator; page and theorem
   body not checked. The PRINT records the uniformization, unique parameter
   with the specified `j`-invariant, and the split/base-isomorphism clause.
2. **Weil pairing:** the same manuscript bibitem, III.8.1(d), Galois
   equivariance `e_N(σP,σQ) = σ(e_N(P,Q))`. Page not checked.
3. **Semistability:** A. Silverberg and Yu. G. Zarhin, *Reduction of Abelian
   Varieties*, arXiv:alg-geom/9602014v2, dated 29 August 1998, Theorem 4.1(i)-(ii),
   PDF page 4. The PDF text body was read. The theorem also states the equivalent
   square-zero condition in (iii). Its proof cites SGA 7 I, Exposé IX,
   **Proposition 3.5 and Corollaire 3.8**, not a theorem numbered 3.5.
   Those original SGA pages have not been checked. There are two formal
   specializations, the global criterion for C2 and its local direction for C1.
4. **Unramified extension and Frobenius:** J.-P. Serre, *Local Fields*, English
   translation, Springer GTM 67, III, §5 (Unramified Extensions) and I, §8
   (Frobenius Substitution). The table-of-contents section locators were checked;
   theorem bodies and pages were not checked. The two inputs concern the value
   group of the inertia-fixed field and generation of the unramified quotient.

The blanket claim that every curve with `|j| > 1` splits over the unramified
quadratic extension is false. The unramified conclusion applies at
multiplicative reduction. The new C.14.1 PRINT does not package a quadratic
extension or unramified twist as an input; the required sign readings are
proved separately.

## Verification and non-vacuity

The modules were compiled with Lean 4.35.0, the unchanged dependency pins,
`LEAN_NUM_THREADS=8`, affinity 48-71, and priority 10. Only the new module
names were build targets. The complete signature and kernel-axiom receipt
is in `AxiomAudit.txt`. All 19 inspected declarations, including both exact
target reductions, depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The source guard checks all 20 final Lean modules. There are no prohibited
proof placeholders, new axiom declarations, executable commands, custom
syntax, or native kernel bypasses. Every configured heartbeat limit is at
most 800000, every source line is at most 100 characters, and the public
source hygiene checks pass.

Non-vacuity proofs include genuine admissible parameters in the actual local
completions, compatible roots in their algebraic closures, the order-two
nonidentity matrix `-I ∈ SL₂(ℚ)`, and the elliptic curve
`y² + xy = x³ + 5`. Its invariants are checked as
`c₄ = 1`, `c₆ = -4321`, `Δ = -10805`, and `j = -1/10805`.

## File receipts and what remains

`SOURCE_MANIFEST.json` gives the exact byte size, line count, and SHA-256 of
every final Lean source file. `SHA256SUMS` is the corresponding checksum list.
The final sources contain no inspection directives. The temporary audit
module was removed after its successful run.

The six explicit PRINT parameters remain to be proved in Lean or supplied
from the stated literature. No new glue equivalent to C1 or C2 is introduced.
Silverman and Serre theorem-page verification remains open, as does checking
the original SGA page bodies. No commit, checkout, dependency update, or
integration was performed, and no original file was edited.

## Classification after independent review

- `LocalSemistableTatePrint` and `GrothendieckSemistableReductionPrint`: faithful specializations of
  Silverberg-Zarhin, *Reduction of Abelian Varieties*, Theorem 4.1 (PDF page 4), a source that is not
  one of the manuscript's bibliography entries.
- `SilvermanC141TateUniformizationPrint`, `LocalUnramifiedValueGroupPrint` and
  `LocalFrobeniusGenerationPrint`: readings (GLUE), not certified literal printed statements.
- `SilvermanIII81GaloisWeilPairingPrint`: proved (`silvermanIII81GaloisWeilPairingPrint_proved`,
  `AdditiveOneInput.lean`), so the additive reading follows from the semistability criterion alone
  (`additiveReductionCoinvariantsVanish_of_semistability`).

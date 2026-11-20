# Berger reroute

**Scoped stop on the literal reroute.** The previous primary-source
reading records basis admissibility over Berger's $B_{max}[\log[\bar\pi]]$,
whereas `bergerSurveyF` needs dimension admissibility over the
$B_{cris}$-based image in `B_dR`. Berger's reported statement that
both rings compute the same $D_{st}$ identifies the mathematical
comparison to formalize. It is not yet a Lean comparison.

**Locator discrepancy (journal locator UNVERIFIED).**
The manuscript cites the $p$-adic monodromy theorem without a number
(`diophantine_zq.tex:739–741, 11037–11040`). The existing audit
(`docs/research/locators.md`, R11) records Théorème 0.6 and Théorème
5.19 in arXiv v3, and Théorème 0.7 and Corollaire 5.22 in the later
author copy. Do not assign 0.6 to the journal version without checking.

`ZInQ.Manuscript.BergerReroute.bergerSurveyF_of_thm06Print` compiles
(VERIFIED). It is the Lean bridge from the **draft Fontaine-ring consequence**. Its conclusion
has exactly the type of the current row. It assumes a theorem over
Fontaine's embedded ring; it does not identify that theorem with the
literal journal statement. The row remains GLUE pending the comparison
and reading. No statements or folds change.

## Berger draft and the remaining comparisons

`BergerThm06Print` in
`ZInQKernel/Contrib/OneProof/BergerReroute/BergerReroute.lean`
specializes to $G_{\mathbb Q_p}$. It takes a continuous representation
on $E^n$ for finite $E/\mathbb Q_p$, viewed by restriction of
scalars as a $\mathbb Q_p$-representation. The premise is
`PanBergerSplit.IsDeRhamU`: the $\mathbb Q_p$-dimension of
$(B_{\mathrm{dR}}\otimes_{\mathbb Q_p} V)^{G_{\mathbb Q_p}}$ is
$[E:\mathbb Q_p]n$. The fixed scalar field at the base is
$\mathbb Q_p$, by `BdRInv.bdRInvariantsPrinted_proof` and
`LogPTransc.bdr_invariant_eq_algebraMap`. If the paper gives the
de Rham premise in basis form, the identification uses the usual
semilinear independence argument over the field $B_{\mathrm{dR}}$:
normalize a shortest relation among invariant vectors and subtract its
Galois translates; minimality makes the coefficients invariant.
The surviving full-rank invariant family is a basis. The new bridge
uses the dimension premise as given and does not formalize this
argument for $B_{\mathrm{dR}}$.

The draft concludes `FontaineSt.IsPstFBasis` at the canonical
$\xi=p-[\widetilde p]$. Here are the definitions used:

- $A_{\inf}=W(\mathcal O_{\mathbb C_p}^{\flat})$, with its Fontaine map
  $\theta$. `AcrisOf` is the series image in $B_{\mathrm{dR}}^+$:
  $\sum a_i\xi^i/i!$, $a_i\in A_{\inf}$, $a_i\to0$ $p$-adically.
  The series is evaluated $\ker\theta$-adically.
- $B_{\mathrm{cris}}^+=A_{\mathrm{cris}}[1/p]$ and
  $B_{\mathrm{cris}}=B_{\mathrm{cris}}^+[1/t]$ in $B_{\mathrm{dR}}$,
  with $t=\log[\varepsilon_0]$ for a generator of $\mathbb Z_p(1)$.
- Fontaine's polynomial ring $B_{\mathrm{cris}}[X]$ maps to Mathlib's
  $B_{\mathrm{dR}}$ by $X\mapsto\log_{\mathrm{dR}}([\widetilde p]/p)$,
  with $\log(p)=0$; its image is `FontaineSt.BstFOf`. The Galois
  action on coefficients is inherited from $B_{\mathrm{dR}}$, and
  $\sigma X=X+\log[\sigma(\widetilde p)/\widetilde p]$.
  The usual Frobenius is Witt Frobenius extended to the completed
  divided powers and localization on coefficients, with
  $\varphi(t)=pt$, $\varphi(X)=pX$; with the chosen sign,
  $N=-d/dX$ and $N\varphi=p\varphi N$. Only the diagonal Galois
  action enters the representation predicate. The draft uses the
  induced Lean action on the image; it does not construct the
  crystalline Frobenius or transport either operator to
  $B_{\mathrm{dR}}$.

The witness is a finite $K/\mathbb Q_p$ inside the chosen algebraic
closure; `K.fixingSubgroup` is $G_K$. The new theorem keeps this
same $K$. It uses `FontaineSt.isAdmissible_of_pstF` (via
`BmaxOne.isAdmissible_of_T`) to pass from an invariant basis to the
dimension over the fixed ring. It then uses `FontaineSt.bstFOf_eq_xi`
to cover the row's arbitrary generator of `ker θ`. Neither step
requires the converse dimension-to-basis implication for
$B_{\mathrm{st}}$. The conclusion also does not require a separate
identification of $B_{\mathrm{st}}^{G_K}$ with the maximal
unramified subfield $K_0$.

| Remaining item | Size and status |
| --- | --- |
| Abstract Fontaine ring vs. image | `FontainePolynomialEmbedding`: one injectivity condition for $B_{\mathrm{cris}}[X]\to B_{\mathrm{dR}}$ at $\xi$ for each $p$ and cyclotomic generator; no $V$ or $K$. The range identification is already Lean: `LogPTransc.bstFOf_eq_adjoin` and `Algebra.adjoin_singleton_eq_range_aeval`. `fontainePolynomialEmbedding_of_logPTildeTranscendental` reduces injectivity to the stronger existing open Prop over $B_{\max}$. Its reduction to $\log[\widetilde p]\notin\operatorname{Frac}(B_{\max})$ is `LogPTransc.logPTildeTranscendental_iff_notInFrac`. The embedded-ring bridge itself does not assume injectivity. |
| Abstract crystalline coefficient ring vs. the series model | Identify the natural map from the $p$-adically completed PD envelope of $A_{\inf}$ along `ker θ` with the series image; include injectivity if using the abstract envelope as the coefficient ring. `FontaineSt.bcrisPlusOf_eq_set` and `PstModel.bcrisPlusOf_eq_printed` verify series descriptions in the image. They do not establish an isomorphism with the completed PD envelope. This is a coefficient-ring comparison independent of $V$ and $K$; a referee-checked series definition in the primary source could avoid retyping it into the statement. |
| Literal Berger ring vs. Fontaine's embedded ring | `BergerPaperStComparison p ell` is the exact missing direction, over the same finite $K$: an invariant basis over $B_{\max}[\ell]$ implies dimension admissibility over `BstFOf` at $\xi$, for each finite $E$, continuous model where used, and choice of $t$. Instantiate $\ell$ with the paper's $\log[\bar\pi]$ in $B_{\mathrm{dR}}$ once constructed. This Prop asks only for admissibility transfer, not equality of rings or the full comparison of $D_{\mathrm{st}}$. It is open. |
| Possible factorization of the literal comparison | First normalize $B_{\max}[\log[\bar\pi]]$ to the tree's `BergerBst.Bst`: `FontaineSt.bmax_adjoin_eq_bst` proves the algebraic half given a logarithm estimate. Then use `BmaxOne.isPstBOf_of_T`, followed by a Fontaine comparison in the required direction. `PanDict.BmaxStToFontaine` is the existing existential version of this latter gap. `FontaineSt.bstFOf_le` proves the inclusion in the opposite transport direction for an invariant basis. |

**SPECULATIVE (proof route).** A possible proof of the functor comparison uses the inclusion of
crystalline periods into the maximal period ring and an inclusion in
the reverse direction after Frobenius. With compatible log coordinates
and both fixed scalar fields identified with $K_0$, Frobenius on the
larger invariant space is injective and semilinear for an automorphism
of $K_0$. It is then surjective in finite dimension. Its image lies in
the Fontaine invariant space, so the two spaces agree. This is a
proposed proof route. The tree lacks the Frobenius construction and
compatibility for this argument.

For the source reading: inspect the journal page for the actual theorem
number, theorem versus corollary, the base-field and residue-field
hypotheses (specialize to $K=\mathbb Q_p$), and the meaning of
“de Rham” and “potentially semistable.” Check the definition of
$B_{\mathrm{st}}$, the logarithm coordinate and $N$ conventions,
and exactly where the paper identifies its $D_{\mathrm{st}}$ with
Fontaine's (including whether that identification is proved, or needs
a separate primary reference). Check Fontaine's completed PD envelope
or series description, the polynomial embedding, and the compatibility
of the Galois actions. The reported arXiv §1 and §1.2 readings are
secondary evidence in this run; the journal locators are UNVERIFIED.

## Pan's use of the same notes

All Lean filenames in the table are relative to
`ZInQKernel/Contrib/OneProof/`. Brinon–Conrad locators are from the
base inventory. The alternate Fontaine reference is *Périodes
p-adiques*, Astérisque 223 (1994), Exposés II and III; exact
section/page numbers and the individual claims against those pages
are UNVERIFIED. This is a list of replacements to investigate;
the Pan theorem has not been rerouted.

| Brinon–Conrad item | Lean use in `PanPrintedF` | Replacement and effect on the statement |
| --- | --- | --- |
| §5.2 pp. 67–68: $B$-admissibility in the dimension form | `BergerBst.fixedSub`, `dB`, `IsAdmissible` (`BergerBst.lean`) | Fontaine's representation formalism, Exposé III, and Lean. Keep the dimension form as written. A direct substitution of the basis form changes the premise; `FontaineSt.localIsPstF_of_basis` proves basis ⇒ dimension, while the converse needs a regularity/comparison argument. |
| Thm 9.3.5 p. 148: restriction to $G_K$ for finite $K$ | `FontaineSt.IsPstF`, `LocalIsPstF` (`PanBergerFontaine.lean`) | Fontaine's definition or Berger 2002 (after accounting for the ring). No statement change if the predicates are identified. The monodromy implication in the notes supplies no part of Pan's theorem: Pan already assumes pst. |
| Def. 9.2.3 p. 138 and pp. 140–142: polynomial $B_{\mathrm{st}}$, log embedding and Galois action | `FontaineSt.BstFOf`, `bstF_stable` (`PanBergerFontaine.lean`), `BergerBst.logPTilde`, `bdrAct_logPTilde` (`BergerBst.lean`) | Fontaine's period rings, Exposé II, and Lean for the Galois action. No change when keeping the embedded presentation after comparison; using the abstract polynomial type directly changes the Lean predicate. |
| Thm 9.2.10 p. 143: injectivity | `LogPTransc.transcendental_bcrisOf`, `bcrisPolyEquiv` (`LogPTranscendence.lean`) | Fontaine's logarithm transcendence/embedding, Exposé II, or a Lean proof of `FontainePolynomialEmbedding` with compatible action. No change to Pan if used to validate the current image. |
| Def. 9.1.4 p. 131 and pp. 128–129: $A_{\mathrm{cris}}$, the series image, $B_{\mathrm{cris}}^+$ and (t^{-1}) | `FontaineSt.AcrisOf`, `BcrisPlusOf`, `BcrisOf`, `acrisOf_eq` (`PanBergerFontaine.lean`); `PstModel.bcrisPlusOf_eq_printed` (`PstModel.lean`) | Fontaine's period rings, Exposé II; Lean for the two series presentations and generator independence. No change if sourcing the same embedded coefficient ring; replacing it with an abstract PD completion changes the definition and requires comparison. |
| Def. 4.4.7 and p. 131: ambient $B_{\mathrm{dR}}$ | `HDec.PkgI4.BdR` (`ZInQKernel/Contrib/G9/I4Layer.lean`); `PanBergerSplit.bdrLin` (`PanBergerPrinted.lean`); `DeRhamPrint.TDict` and `BdRT` (`DeRhamPrintTDict.lean`, `BdRT.lean`) | Fontaine's period rings, Exposé II, and the existing Mathlib/Lean comparison. No change. The Pan row itself has no de Rham admissibility premise. |
| Finite coefficient model (no further notes theorem) | `PstModel.localIsPstF_iff_forall` (`PstModel.lean`); separately `HTModel.localDistinctHTP_iff_forall` (`HTModel.lean`) for Hodge–Tate weights | Lean. No statement change. Passing from Berger to Pan in `PanDict.panBerger_of_F` uses the same model. |

## Known issues

- **Locator discrepancy.** Théorème 0.6 as a journal locator is
  UNVERIFIED; see the report's opening. The
  manuscript bibliography has no such numbering error.
- **Literal logarithm in the prior arXiv reading.** The formula with
  denominator $\bar\pi^{(0)}$ needs an interpretation to form a
  series in $B_{\mathrm{dR}}^+$: the untilt is supplied in
  $\mathcal O_{\mathbb C_p}$, on the residue side of `θ`, rather
  than as a specified scalar in that ring. The previous reading
  proposes the multiplicative logarithm via the proof of
  Prop. 2.23 (locator for that proof UNVERIFIED in the journal).
  This is a formalization/reading issue, not evidence that the
  monodromy theorem is false.
- **Berger's later survey, distinct from the monodromy paper.**
  The existing audit reports two misprints in arXiv:math/0210184v1
  II.3.3: exponent $i-1$ in place of $i$ in the log series, and
  $\varphi(X)=X^p$ in place of $pX$. Its $B_{\mathrm{cris}}^+$
  series description also leaves the topology implicit. The draft
  specifies $p$-adic decay and uses neither misprint.
- **Pan:** the repository reading is of the manuscript's cited arXiv
  v2. The JAMS theorem number/page remains UNVERIFIED. In the prior
  reading the extra residual hypothesis at $p=3$ is irrelevant for
  (p\ge5). The Pan row still has the period-ring dependencies listed
  above; changing the Berger supplier would not remove them.
- **No new mathematical error in the manuscript identified.** The
  gap concerns how the journal theorem is transported into the
  current Lean predicate.

## Manuscript check

All lines refer to `diophantine_zq.tex` at the base. The appendix
furnishes the input premise, and is included here to delimit the scope;
this contribution does not reprove it.

| Lines | Step | Verdict |
| --- | --- | --- |
| 719–731 | Use finite local coefficient scalars; take the two-dimensional summand of the representation. | OK — the draft takes the underlying $\mathbb Q_p$-representation of that finite coefficient model. |
| 735–738 | Supply de Rhamness at the coefficient prime and the Tate weights. | OK — de Rhamness is the input to the bridge; the bridge uses no weight hypothesis. |
| 739–741 | Apply Berger to get potential semistability for Pan. | unverified — the draft gives the correct target once the printed-ring comparison and journal locator are checked. |
| 755–758 | Apply Pan at $\ell=5$ with the Tate convention and no $p=3$ proviso. | OK — matches the covered (p\ge5) application and the existing Pan premise when instantiated with the common Fontaine image. |
| 10940–10951 | State the upstream de Rham descent lemma for a continuous summand with finite local coefficients. | OK — the use at $K=\mathbb Q_p$ provides the local input. |
| 10954–10972 | Comparison for the proper smooth variety and identification of the Tate module by duality. | OK — this is upstream of the bridge and gives the de Rham input, rather than invoking monodromy. |
| 10973–10978 | Use de Rham closure under duals and subquotients, then the finite coefficient sum. | OK — upstream; nothing here depends on the $B_{\mathrm{st}}$ definition. |
| 10980–10994 | Descend the de Rham condition by finite Galois descent. | OK — concerns $B_{\mathrm{dR}}$ and requires no semistable descent. |
| 10996–11006 | Read off Tate weights; distinguish Hodge–Tate comparison from de Rham comparison. | OK — the bridge consumes de Rhamness itself. |
| 11019–11023 | Cite the preliminary notes for upstream de Rham closure/descent. | OK — separate from the note locators in the two rows. |
| 11037–11040 | Identify the monodromy paper by title, journal and DOI. | OK — no theorem number appears in this citation. |
| 11041–11045 | Specify the Pan version used in the manuscript. | OK — the manuscript gives an arXiv number; the journal numbering remains unverified. |

## Lean verification

VERIFIED: the new module compiled with `lake env lean` after an offline
Lake build of its imports. The three new theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`; see
`scratch/berger-reroute/axioms-output.txt`.

The focused check in `scratch/berger-reroute/Discharges.lean` verified
the row's type against the source of `Main.lean` and `TailZ98.lean`
and ran the repository's `#discharges` matcher on that one row.
It matched `bergerSurveyF_of_thm06Print`, assuming only
`BergerThm06Print`; see `scratch/berger-reroute/discharges-output.txt`.
This does not check or fold the full headline.

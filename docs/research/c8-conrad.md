# c8-conrad: step C8 by local algebraicity (Conrad, App. B) — no defect, but the Picard rows cannot leave the route through C8

Task c8-conrad, 2026-11-17. Base: wip/c8-conrad `d67ea55f6` (wip/leaf-fold33b; origin/main is an ancestor). Results
log: `scratch/c8-conrad/log.md`. This is model work; nothing here has been reviewed by a person.

**VERIFIED** means read in a named file on this host, computed, or compiled. **STANDARD** means published, with the
reference given. **SPECULATIVE** means not checked. Theorem numbers given from memory are marked UNVERIFIED.

## 0. Verdict

1. **Why the appeal to Conrad was replaced: not because of a defect.** No review records a defect in the manuscript's
   use of Conrad's Appendix B (§1). The replacement was a shortening. Version 14/16 had used the determinant argument,
   up-h §4 item 1 recommended adopting it, and task h-v16-adopt did so. The project's notes also record that Conrad's
   paper is an unrefereed preprint. So there is **no Known issue** about Conrad App. B, and the task's main branch
   applies.
2. **The target is out of reach through C8 (VERIFIED: source reading and a field-taint run on the built top, §2).**
   `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` have **three** live consumers. C8 is only one of them:
   * (i) C8: `DetTate` (`det V₅(A) = χ²`, from the Weil pairing) in `G12DetPZ`;
   * (ii) step E1-E2: Poincaré reducibility, field `t8`/`poincareComplement`, at manuscript L865;
   * (iii) step C3/G9: the field `hodgeTateDecompAbVar`, where the Hodge–Tate multiplicities `a = b` come from the
     Weil pairing (hodgetate-from-dr).

   Rerouting C8 to Conrad removes consumer (i) only. Both rows stay hypotheses of `frozenTarget`, and the reroute
   would add a leaf and three glue Props without removing a field. So **no fold is proposed** (§5).
3. **Lean (VERIFIED compiled, standard axioms; §3-§4).** `scratch/c8-conrad/C8Conrad.lean`, copied to
   `ZInQKernel/Contrib/OneProof/C8Conrad.lean`, contains:
   * the printed-form statement of Conrad's App. B for base field `ℚ_p`, written over Tau Ceti's local Artin map
     (`ConradAppBQp`);
   * three named glue Props;
   * a proof of C8's consumer `HDec.G0Galois.G12DetPZ` from these, with neither `DetTate` nor the Weil pairing
     (`g12DetPZ_of_conrad`).

   This is ready for the day consumers (ii) and (iii) are rerouted too. At the call site
   (`g8_g12_of_leaves3_hf_pz_eb`) it is a one-term replacement (§5).
4. **Conrad App. B is unread on this host (Known limitation, not a Known issue).** WebFetch of
   `math.stanford.edu/~conrad/papers/locchar.pdf` was refused by the sandbox's domain check, and no copy is on the
   host. The statement used here is the one reported by Glazer's theorem-application audit
   (`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L94-104; §1.2). It keeps the flag
   **unread**.

## 1. Why the appeal to Conrad was replaced (VERIFIED, read in the named files)

### 1.1 The record

| source | what it says about C8's local-algebraicity sentence |
|---|---|
| h-trust.md C8, "Finiteness of ψ: the determinant argument" (L637-639) | the determinant argument "replaces N5's appeal to local algebraicity of Hodge–Tate characters at L760-761. This is Version 14's argument, kept in Version 16 at V16 L660-667". It was adopted by task h-v16-adopt "after up-h §4 item 1". |
| h-trust.md C8, "Suppliers" (L697-699) and §2.4 (L1034-1036) | "No longer used: local algebraicity … The determinant argument makes it unnecessary." The row `conrad-local-characters` "is gone". No defect is given as the reason. |
| up-h.md §4 item 1 (L307-312), under "Shortening h-trust.md: marginal (SPECULATIVE recommendations)" | replace local algebraicity by V14's determinant argument; "This removes the conrad-local-characters row … and the class-field-theory step of C8". |
| rv-h-c8.md §4 (L172-192), the focused review of C8 on the N5 text | N5's chain (Hodge–Tate character ⇒ Tate/Sen local algebraicity ⇒ class field theory ⇒ finite order) is "VERIFIED as an argument; the cited theorems STANDARD". Its one remark (item 3): the finiteness of `ψ` on inertia at `ℓ ≠ 5` is asserted "without argument … it is elementary". §3.1: Hodge–Tate suffices; de Rham is not needed. |
| rv-h-trust.md §1.2 item 1 | the input missing from C8 is (HT) for eigenforms. Both routes need it. It is not Conrad's appendix. |
| rv-up.md row 2d and §2.3 | the determinant argument is sound and "removes the local-algebraicity leaf but not the (HT) supplier and not Kronecker–Weber". |
| h-leaves.md L581, L638; h-v14.md L83, L567; nt-h.md L62, L408 | Conrad's paper is an "unrefereed … preprint". Upstream Version 14 dropped it (citation count 0; v14-routes.md L239-258). The refereed replacements named are Serre 1968 Ch. III and Tate 1967 §3.3. |
| Glazer's theorem-application audit, A011 (`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L94-118) | accepts A011. It **added** the Conrad citation to the manuscript (`MANUSCRIPT_EDITS.json` L135-136: the old text said only "By class field theory over ℚ"). Its conclusion: "There are no newly detected mathematical gaps in these five interfaces". |

**Conclusion.** No defect in the manuscript's use of Conrad App. B is recorded. The caveats on record are:
* the source is an unrefereed author preprint, which affects the LEAF rating (§3.2) but is not a gap;
* N5 states the elementary finiteness at `ℓ ≠ 5` without argument, which is on-the-spot glue inside
  `FiniteOfLocAlgTrivialQ` (§3.3).

### 1.2 The cited statement

The manuscript (diophantine_zq.tex L758-764) says, paraphrased: the twisting character is a de Rham subrepresentation
of the Hom representation and is unramified outside finitely many primes. Local algebraicity
[conrad-local-characters, App. B, pp. 32-33] and class field theory over ℚ make it a finite character times an
integral power of the cyclotomic character. The weight comparison then forces `k = 2` and power zero. The bibliography
entry is at L11046-11049 (author preprint, December 11, 2011).

**Not read on this host.** WebFetch of the PDF was refused by the sandbox ("Unable to verify if domain
math.stanford.edu is safe to fetch"). No copy is on the host; the audit's pinned copy, `work/theorem-application-audit-20261105/…/conrad-locchar.pdf`,
SHA256 `782fe71a…`, is not in this repository. The statement below is **as reported by the theorem-application
audit** (report L102, an AI reading by Glazer's audit, not a human one):

> "The paragraph after Definition B.1 states that a continuous character with values in a finite extension of Q_p is
> locally algebraic exactly when its underlying Q_p-representation is Hodge-Tate. It explicitly covers coefficient
> fields larger than Q_p. The arithmetic-Artin normalization and the local product formula are given immediately
> after it."

The audit applies it with base field `L = ℚ₅`: "a locally algebraic character on a neighborhood of 1 in Q_5^* is x
mapped to x^n for a single integer n" (L104). Definition B.1's exact wording, and whether the paragraph also ties the
exponent to the Hodge–Tate weight, remain **unread** (UNVERIFIED). This is why the weight dictionary is a separate glue
Prop below.

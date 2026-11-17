# gr512-bridge (11-17)

**Result.** The research field `gonzalezRotgerThm512X6` (strict review: GLUE, steps S1, S2) is proved from one
new leaf, `GR512Bridge.GonzalezRotgerThm512X6RCF`: González–Rotger Thm 5.12 (JMSJ 58 (2006) p. 946) as printed,
`ℚ(x) ≅ H_R` over **Tau Ceti's `ringClassField`** if `D(R) ≠ 1`, and `ℚ(x) ≅` an index-two subfield of `H_R`
otherwise, with `D(R)` read off the order (`grD6`: `p ∣ 6` with `pR` prime in `R`, i.e. Eichler symbol −1).
Consumers unchanged: `gonzalezRotgerThm512X6_of_rcf : GonzalezRotgerThm512X6RCF → GRDict.GonzalezRotgerThm512X6`.

**Compiles (VERIFIED, standard axioms)**, in `ZInQKernel/Contrib/OneProof/GR512Bridge.lean`:
* S2: `toOrder` (Tau Ceti order of a finite-index subring), bridge `picEquiv : Pic O ≃* CommRing.Pic R`
  (Mathlib 4.35 already has `ClassGroup.equivPic` for every domain), degree via `finrank_ringClassField`.
* S1: `isPrime_span_iff` (pR prime in R ↔ p𝓞_k prime, p ∤ conductor), `grD6_ne_one_iff` (↔ `inertCount6 k ≠ 0`).
* N1: `N1.O_maximal` — `LeafQM.O` is a maximal order (Gauss's lemma + a 576-case congruence by `decide`).
* `#discharges`: discharges `OpenResearchLeaves42.gonzalezRotgerThm512X6`, assumes only the new leaf.
* autofold `--dry-run` (scratch/gr512-bridge/autofold.json): strict 12/22 → 13/21 on 34, strictest 11/23 → 12/22
  (**GLUE −1, no new glue**); generated `sixContactMin_of_open61` compiles with standard axioms.

**Leaf rating.** Printed form, flag "reading risk": the one remaining reading point is GR §5's definition of
`D(R)` (read as ∏ p ∣ D with Eichler symbol (R/p) = −1; not re-read on this host). If the integrator wants it
GLUE until a statement check, flag it "pending reading" (the fold is then neutral). Report:
docs/research/gr512-bridge.md.

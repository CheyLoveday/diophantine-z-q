# ss-faltings: the last SGA 7 row off the bundle, through the stable Faltings height

Task ss-faltings, 2026-11-17/18. Base: fork main d435851d (lane74 landed); nothing merged. Results log:
scratch/ss-faltings/log.md.

Marks: **VERIFIED** means compiled or read in a named file on this host. **STANDARD** means published, with an exact
reference. **SPECULATIVE** means judgement. Theorem numbers and page locators recalled from memory are **UNVERIFIED**
(no network). Model work, no human review.

## 1. Result

@RESULT@

## 2. What SS2 and SS3 are used for (traced, VERIFIED)

Sources: d2a6-reroute's trace (read from origin/wip/d2a6-reroute without merging: docs/research/d2a6-reroute.md §4,
scratch/d2a6-reroute/taintD-out.txt section COR33) and this task's declaration-level taint
(scratch/ss-faltings/TaintS.lean → taintS-out.txt, on the closure of `sixContactMin_of_open72`).

- **The field's path.** `sga7_IX_Cor3_3_Def34` (OpenResearchLeaves53) → `sga7_IX_3_3_SHpre` (36EBCF) → `sga7_IX_3_3_SH`
  → `sga7_IX_3_3` and `semistablePersistsSHcp` (OpenResearchLeaves14GMEB).
- **Its two readers** (EichlerBoundCopy.lean):
  - `ss1_ss3_of14NF_hf_gm_pz_eb`: SS1 (`SemistableReductionThm`) **and** SS3 (`SemistablePersists`), by
    `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp …`. SS1 is tainted too: its global proof
    (`semistableReductionThm_of_leaves_nfNF`) uses persistence at the bad places (through `F O ≤ L₀`) and at the
    semistable places of `A`.
  - `researchLeaves9_of_open14_hf_gm_pz_eb`: SS2 := `semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 …`.
- **Downstream.** SS1-SS3 become fields of OpenResearchLeaves9EB and 8EB and are read only by
  - `heightRowsNo20_of8_hf_eb`: R18 (Javanpeykar), R19 (Gaudron–Rémond), R21 (Bost), R22 (Pazuki) and
    `StableHeightFinite`, through TailY's `r18_of_leaves`, `r19_of_leaves`, `r21_of_leaves'`, `r22_of_upper`,
    `stableHeightFinite_of'`;
  - `r20Lower_of8_hf_eb`: the lower half of R20 (Faltings' Lemma 5), through `r20Lower_of_leaves'`.
- **What the readers use.**
  - SS2 only through TailY's `stableFaltingsHeight_eq_of_semistable`: the kernel's stable height (an infimum over all
    number fields and all metrized group models) equals the height of any semistable Néron model. Its proof needs, for
    `L'/L` finite, `h(𝒩_{L'}) ≥ h(𝒩_L)` when `𝒩_L` is semistable (the other inequality is the Néron mapping property).
    That is **invariance of the height of a semistable abelian variety under finite extension**, Faltings' statement.
    The semistability of the base change itself, or the identity-component comparison of SS2, is never used.
  - SS3 only in `r20Lower_of_leaves'`, to make the Néron models of `A` and `B` over the compositum of their two
    semistable fields semistable, so that Faltings' Lemma 5 (semistable form) applies over one field. One common
    semistable field suffices.
  - SS1 (existence of a semistable field) in the identification (`exists_semistable_neron`) and in R20.
- **Answer to the lead's question.** The readers need invariance of the stable height under finite extension and one
  common field of semistable reduction for two abelian varieties; they do not need semistability of a base change of a
  given semistable model. Invariance under isogeny (L621) is R20, which is unchanged (its leaf is still Faltings'
  Lemma 5, `FaltingsLemma5BCLower`).

## 3. The reroute (Lean)

@LEAN@

## 4. Checks

@CHECKS@

## 5. The new leaf, rated

| field | rating | provenance line |
|---|---|---|
| `faltingsSemistableHeightBC` (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`) | kind published, **GLUE** (flag "pending reading: Faltings 1983 §1 not read on this host") | (b) Faltings, Invent. Math. 73 (1983), 349-366, §1 (locator UNVERIFIED): the height of an abelian variety with semistable reduction does not change under finite extension. The bibliography cites the paper (bibitem `faltings1983`, L11084-11086; cited at L621 and L733); at L596-598, where the statement is used, the manuscript cites nothing. Stated over the kernel's `GroupModel.height` and height-split's `IsSemistable`; not stronger than the row it replaces (`faltingsSemistableHeightBC_of_ss2`: SS2 implies it with the kernel's proved height lemmas) |

No other leaf is added. `SemistableReductionThmIF` is GLUE proved in Lean (`semistableReductionThmIF_of_raynaud`) from
fields already in the bundle and already used for SS1: the Raynaud leaf (`raynaudSemistableSHOr` on this base, via
`raynaudSemistableSH` and `ReductB.raynaudSemistable_of_SH_pair`; Silverberg–Zarhin Thm 3.5 as the manuscript cites it
at L816 once sz-raynaud's autofold is folded), `strictHenselizationPair`, the textbook fields `mumfordTorsionAlgClosed`,
`mulEtaleAbelianScheme`, `neronSchemeExtensionExists` and `blr_1_2_4` (BLR 1.2/4, proved by gt-blr).

**Stop rule.** Not triggered. The reroute needs nothing uncited beyond Faltings 1983: the one new statement is
Faltings' invariance; the semistable field comes from Raynaud's criterion (cited at L816) with textbook facts proved in
Lean (torsion fields of definition, `[m]` étale descent, `3` or `5` is a unit in a local ring, Néron models over DVRs
and localization). No on-the-spot leaf.

## 6. Manuscript check

One line per manuscript step this work formalizes or relies on.

| tex lines | step | verdict |
|---|---|---|
| L596-597 | "After a finite extension `E` has everywhere good reduction, since its `j`-invariant is integral." | **OK** (relied on only as the special case of semistable reduction; standard: CM `j` integral ⇒ potentially good reduction, Serre–Tate 1968 §2, UNVERIFIED locator). Not formalized here |
| L597-598 | "This extension does not change its stable Faltings height." | **gap filled**: uncited. It is Faltings 1983 §1 (invariance of the height of a semistable abelian variety under finite extension; locator UNVERIFIED), which the bibliography has; formalized as the leaf `faltingsSemistableHeightBC` (provenance (b), pending reading) in the general form the kernel's height rows need. Flag for the ledger: ELLIOT-type sentence at L597-598, now carried by a cited print |
| L598, L876 (and L611-623, L870-903, L939-945) | `h_F` is "the stable Faltings height" (L876: "the original stable Faltings height") of an abelian variety over a number field, used as a field-independent invariant | **gap filled**: the manuscript never defines it nor says why it is well defined. Well-definedness = (i) a field of semistable reduction exists, (ii) the height is the same over every larger field. (i): Raynaud's criterion (L816's citation) over `K(A[15])`, proved in Lean (`semistableReductionThmIF_of_raynaud`); (ii): Faltings 1983 (the new leaf). The kernel's identification `stableFaltingsHeight A = h(𝒩_L)` for any semistable `L` is proved from these (`stableFaltingsHeight_eq_of_semistableF`) |
| L621 | "Height variation under isogeny [faltings1983]" (R20, lower half) | **gap filled**: Faltings' Lemma 5 is for an isogeny of abelian varieties semistable over one field; applied to stable heights it needs a common field of semistable reduction for source and target, not mentioned. Supplied by `SemistableReductionThmIF` at `K(A[15])·K(B[15])` (`r20Lower_of_leavesF`); the leaf itself (`FaltingsLemma5BCLower`) is unchanged and not re-read here |
| L814-817 | `F = L_v(A[3])` (`A[5]` if `p = 3`); Raynaud's criterion [SZ Thm 3.5] gives semistable reduction there | **OK** for the use made here: the same criterion with the same torsion choice (`m = 3`, or `5` where `3` is not a unit, `3·2 − 5 = 1`) gives semistable reduction at every place of every number field containing `K(A[15])` |
| L870-876 | Javanpeykar Thm 1.1.1 + §2.3 over the stable height (R18) | **unverified** here (not this task's step; read by the locator audit): the row's proof now goes through the new identification, the leaf is unchanged |
| L879-885 | Gaudron–Rémond Thm 1.4 (R19) | **unverified** here (same remark) |
| L894-895 | `h_F(Z) ≥ −(3/2) dim Z` [GR §9] (R21, Bost) | **unverified** here (same remark) |
| L937-945 | Pazuki Cor. 1.3(2) (R22) | **unverified** here (same remark) |

## 7. Known issues

@ISSUES@

## 8. Files

@FILES@

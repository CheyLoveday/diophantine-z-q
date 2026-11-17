# cm-branch: the CM fibres of the six-contact estimate, routed through the manuscript

Task cm-branch (2026-11-17). Base: `wip/leaf-fold33b` d67ea55f (origin/main is an ancestor; top
`HDec.HSyn.sixContactMin_of_open67`, TailZ74). Results log: `scratch/cm-branch/log.md`. Marks: VERIFIED
(compiled, read in the tree or in the manuscript), AUDIT-READ (read in the print by the upstream audit,
`docs/reviews/height-replacement/height/AUDIT.md`; this host has no network, a WebFetch to arXiv was
refused), STANDARD (published, exact reference), UNVERIFIED (theorem numbers from memory), SPECULATIVE.

## 1. Result

**The manuscript's CM paragraph (diophantine_zq.tex L581-631, "CM fibers") is formalized in Lean from the
leaves it cites, and the case split CM / non-CM (L578-580, merged at L901-905) is a Lean proof.** The
consumer is glue-assembly's interface `GlueAssembly.GlueOutputs`, which already has the disjunct
`NonCMOutput … ∨ CMOutput h_F(A)` and already proves `CMOutput h_F(A) → h_F(A) ≤ C_cm`
(`GlueAssembly.cm_branch_nat`); the chain so far only ever used `Or.inl`, with NoCM (FS5) making the CM
case empty. Files (no `sorry`; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`, VERIFIED,
`scratch/cm-branch/Axioms.lean`):

* `ZInQKernel/Contrib/OneProof/CMBranch/Arith.lean` (pure Mathlib): Eq. (6.2)'s summand over Mathlib's
  Dedekind `η` and its expansion (`summand62_eq_archSummand`), the q-series estimate
  (`neg_tsum_log_le`), the summand bound `≤ π y/6 + 1` (`archSummand_le`), `π√|Δ|/12 + 1 ≤ B_cm`
  (`bcm_of_fowler`).
* `ZInQKernel/Contrib/OneProof/CMBranch.lean` (imports `ZInQKernel.OneProof.H.LPrefix`): the leaves,
  the glue, `faltingsHeight_le_bcm`, `cmOutput_of`, `le_heightCcm_of_cmOutput`, `cmBranchOut_of`,
  `glueOutputs_of_branches`, `sixContactMin_of_branches`.
* `ZInQKernel/Contrib/OneProof/CMBranch/NonCM.lean` (imports `EichlerBoundCopy`): the non-CM branch at
  fibres without CM (`nonCMBranch_of`, the chain's `glueOutputs_of_leaves3_hf_pz_eb` verbatim but
  restricted), `FibreSimpleNC` proved without FS5 (`fibreSimpleNC_of_pieces_hf`), and the assembly
  `sixContactMin_of_cmBranch`. Compile status: §7.

```lean
theorem HDec.CMBranch.sixContactMin_of_cmBranch (r : HSyn.ResearchLeaves3EB) (t : HSyn.TextbookLeavesHFPZ)
    (hDimF hDim hPMH hBC hProdE hRev hThetaPt hCopies)          -- GluePieces minus fibreSimple, modularConstituent
    (hYu h1 h2 h3 h4)                                         -- the chain's FibreSimple pieces, minus FS5
    (hMod : ModularConstituentNC) (h20 : R20Lower)
    (hSplit : CMFibreSplit) (hF : FowlerProp27) (hJ : CMjDegree) (hPG : CMPotentialGood)
    (h62 : CMHeight62) (hRP : ReducedCMPeriod) (hAddU : HeightAdditivityUpper) : ZInQ.SixContactMin
```

**Verdict on the target ("gonzalezRotgerThm512X6, x6CoarseModuliIdeal and elkiesX6StarEveryIdeal off the
route").** Not reached, and not reachable by the CM branch alone (§2): `x6CoarseModuliIdeal` and
`elkiesX6StarEveryIdeal` also build the moduli row `LeafAdopt.R1R2fpRepW` itself (the curve `X₆`, the
coordinate `π₆`), which every step reads, and `gonzalezRotgerThm512X6RCF` fills the conjunct `R5ptProps`
of that row. What this task does deliver is the CM-branch half of the re-route: once the non-CM chain is
localized to fibres without CM (`ModularConstituentNC`, §5) and the dead conjunct `R5ptProps` is pruned
from the row (§6), González–Rotger Thm 5.12 and Prop. 5.6 (the count), the `X₆` Kummer fibre and
`cmOptimalEmbedding` leave the route, replaced by Fowler, Eq. (6.2) and two classical CM facts.

## 2. What the NoCM fields feed (VERIFIED by reading the chain)

| top field (OpenResearchLeaves48) | becomes | consumers |
|---|---|---|
| `gonzalezRotgerThm512X6RCF` | `gonzalezRotgerThm512X6` (`GR512Bridge.gonzalezRotgerThm512X6_of_rcf`, TailZ74 L1259) | `GRX6AbPrint.gonzalezRotgerX6Ab_of_print` (TailZ74 L309) → `gonzalezRotgerX6Ab` |
| `x6CoarseModuliIdeal` | `x6CoarseModuli` (`X6ALIdeal.x6CoarseModuli_of_ideal`, L1169) | `gonzalezRotgerX6Ab_of_print` and `GRX6AbPrint.x6ModuliWitness_of_coarse` (L309, L314) |
| `elkiesX6StarEveryIdeal` | `elkiesX6StarEvery` (L1170) | `ElkiesPrint.elkiesX6StarFunctionField_of_every` (L314) → `elkiesX6StarFunctionField` |

Downstream (EichlerBoundCopy, TailZ23, TailZ27, TailZ36, TailZ37):

* `gonzalezRotgerX6Ab` → `x6Rows_of_open14_hf_gm_pz_eb` (`gonzalezRotger := …`, EichlerBoundCopy L2948) →
  `LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel`. `R1R2fpRepW` (LPrefix L5248) is the moduli row
  `∃ Y Φ X Ψ fY π₆, R1fpProps ∧ R1heckeProps ∧ X6Props ∧ R2X6PropsIff ∧ R1recProps ∧ X6Surj ∧ R5ptProps`;
  `R5ptProps` is González–Rotger Thm 5.12 on points of `X₆`. Also `gonzalezRotgerCountX6Ab` (TailZ27 L105).
* `elkiesX6StarFunctionField` → `elkiesX6StarPrinted` (TailZ36 L102) and `babaGranathRationalAb`
  (TailZ37 L91), which give `R2X6PropsIff` (the coordinate `π₆ : X₆ → P¹` with the CM values) inside the
  same row, and `x6ConicModel`.
* NoCM itself is `G0FibreSimple.FibreComTrivial` (FS5: `End_𝒪(P.A) = ℤ` at every point over `J(u)`),
  built in `gluePieces_of_open4_hf_pz_eb` (EichlerBoundCopy L2662) from the row's `R5ptProps`, `r5count`,
  `x6KummerFibre` (from `x6ConicModel`) and `cmOptimalEmbedding`. FS5 is consumed by
  (i) `fibreSimple` (G5-G6, then Poincaré in the non-CM transfer) and (ii) `KernelFieldExists`
  (`kernelFieldExists_of_split_hf''`, inside `modularConstituent`); `fibreSimple` is in turn consumed by
  `modelG3G6_of_leaves3` and `linkedTateLocal_of_leaves3_hf` inside `AfterG7` (G8-G16).
* The height consumer: `glueOutputs_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2574) always takes
  `Or.inl` (`NonCMOutput`). `heightCcm` enters only through `GlueAssembly.CMOutput` and `heightH6`.

So the statement the manuscript's CM branch must deliver in place of NoCM is exactly
`GlueAssembly.CMOutput h_F(A)` for the fibre surface `A` at a CM fibre (with Pazuki's bound and the theta
point for the same `A`), and the non-CM chain must be restricted to fibres without CM. The fields
`x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` are **not** NoCM-only: they also produce `X6Props` and
`π₆`. The manuscript does not use `X₆` there either (L421-434: `Y₃` with the normalizer action and
quotient `P¹_j`, branch values from [babagranath, linyang]); re-sourcing that is a separate re-route of R2,
outside this task.

## 3. Lean steps and the manuscript lines they formalize

| Lean | manuscript | status |
|---|---|---|
| `CMBranch.NoCMAt`, `glueOutputs_of_branches` (case split `NoCMAt u` or not) | L578-580 ("We treat these two cases separately"), L901-905 (merge) | proved |
| `CMFibreSplit` (glue): model `A/L`, `[L:ℚ] ≤ D`, all endomorphisms over `L`; `E/L` CM by an order `R`; `E² = E × E`; `L`-isogeny `E² → A` | A8 (L520-562) for the CM fibre; L583-586 | GLUE (open) |
| `CMjDegree` (leaf): `#Pic(R) ≤ [L:ℚ]` | L586-587 ("The degree of `j(E)` is its order class number, so `h(Δ) ≤ d ≤ D`") | leaf, uncited in the manuscript (§4) |
| `FowlerProp27` (leaf) at `n = D` | L588-593 | leaf, printed form |
| `CMPotentialGood` (leaf): an abelian-scheme model over some `L₁ ⊇ L` | L596-597 | leaf, uncited in the manuscript (§4) |
| `CMHeight62` (leaf): `h_F(E) ≤ avg_σ −(1/12) log(|Δ(τ_σ)|(Im τ_σ)⁶)` | L600-604 | leaf, consequence of the printed formula |
| "This extension does not change its stable Faltings height" | L597-598 | by definition: `CMHeight62` is stated for the stable height of `E`, the model lives over `L₁` |
| `ReducedCMPeriod` (glue): `√3/2 ≤ Im τ_σ ≤ √|Δ|/2` | L598-599 | GLUE, on-the-spot (sketch in its docstring) |
| `summand62_eq_archSummand`: `−(1/12)log(|(2π)¹²η²⁴| y⁶) = −log 2π + πy/6 − ½log y − 2Σlog|1−qⁿ|` | L600-604 | proved (Mathlib's `ModularForm.eta`) |
| `rho_lt_hundredth`, `neg_tsum_log_le`: `ρ < 1/100`, `−2Σ ≤ 2ρ/(1−ρ)² < 200/9801` | L605-606 | proved |
| `archSummand_le`: `−½ log y < 1/10`, discard `−log 2π`, summand `≤ πy/6 + 1` | L606-611 | proved |
| `faltingsHeight_le_bcm` with `bcm_of_fowler`: `h_F(E) ≤ π√|Δ|/12 + 1 ≤ D²3^{21000D²} + 1 = B_cm` | L608-612 | proved |
| `R19_GaudronRemond` (the chain's leaf, reused) over `L`, source `E²`, `g = 2`: `deg ≤ (28²⁵⁶ d max(h_F(E²), log d, 1)²)⁸¹⁹²` (`grKappa_two`) | L614-619 | leaf (existing) |
| `HeightAdditivityUpper` (glue): `h_F(E²) ≤ 2h_F(E)`; "The maximum is at most `2B_cm`" | L620-621 | GLUE (other half of the chain's `HeightAdditivity`) |
| `R20Lower` (the chain's, Faltings Lemma 5 lower half; proved in Contrib from the printed lemma) | L620-621 ("Height variation under isogeny") | existing |
| `cmOutput_of`: `CMOutput h_F(A)` | L622-624 | proved |
| `le_heightCcm_of_cmOutput` (glue-assembly's `cm_branch_nat`): `h_F(A) ≤ C_cm` | L624-628 | proved |
| `cmBranchOut_of`: theta point, Pazuki and `CMOutput` for the CM fibre | L901-905 (CM half), L907-960 unchanged | proved |
| `fibreSimpleNC_of_pieces_hf`: simplicity at fibres without CM, no FS5 | L632-634 ("In particular `A` is absolutely simple") | proved (compile §7) |
| `ModularConstituentNC` (glue): G2, G4, G7-G16 at fibres without CM | L632-900 | GLUE: the chain's proof, to be localized (§5) |
| `nonCMBranch_of`, `sixContactMin_of_cmBranch` | L632-905 | proved (compile §7) |

## 4. The new leaves and their rating

| leaf | statement (Lean) | source | printed form? |
|---|---|---|---|
| `FowlerProp27` | for an order `R` of an imaginary quadratic `k` and `1 ≤ n` with `#Pic(R) ≤ n`: `√|f²d_k| ≤ 2n² exp(21000n²)` | Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026) 607-641, Prop. 2.7, printed pp. 615-616 (AUDIT-READ) | **yes**, through the standard dictionary `h(Δ) = #Pic(𝒪_Δ)`, `Δ(𝒪_f) = f²d_k` (Cox Thm 7.7, Lemma 7.2, UNVERIFIED numbers); flag "unread here; read by the upstream audit" |
| `CMHeight62` | for `E/K` of dimension 1 with an abelian-scheme group model over `𝓞_L` and periods `τ_σ` (`IsPeriodAt`: an analytic uniformization of `E(ℂ)_σ` with lattice `c(ℤ+τℤ)`): `h_F^st(E) ≤ (1/[L:ℚ]) Σ_σ −(1/12)log(|(2π)¹²η(τ_σ)²⁴| Im(τ_σ)⁶)` | Barquero-Sanchez–Cadwallader–Cannon–Genao–Masri, Res. Number Theory 3 (2017) art. 13, §6 Eq. (6.2), pp. 13-14 (AUDIT-READ: original Faltings metric, `Δ = (2π)¹²η²⁴`, general formula after Silverman Prop. 1.1) | **consequence of the print**: the good-reduction case (finite term `0`), the `≤` half. Reading risk: the exact display of (6.2) was not read here |
| `CMjDegree` | `E/L` of dimension 1 with `End(E_{L̄}) ≅ R` ⇒ `#Pic(R) ≤ [L:ℚ]` | none in the manuscript; Cox, *Primes of the form x²+ny²*, Thm 11.1 (UNVERIFIED number); the upstream audit sources the degree to Fowler §2.1 | yes as a consequence of the classical theorem `[ℚ(j(E)):ℚ] = h(R)`; **Known issue 1** |
| `CMPotentialGood` | `E/L` CM ⇒ an abelian-scheme group model of `E_{L₁}` for some finite `L₁/L` | none in the manuscript; Serre–Tate 1968 §6 / Silverman AEC VII.5.5 (UNVERIFIED numbers); proved inside [cmheight], proof of Thm 1.3, p. 15 (AUDIT-READ) | yes; **Known issue 1** |

Reused leaves (no new statement): `R19_GaudronRemond` (Gaudron–Rémond Thm 1.4, the tree's leaf; on the
route as `gaudronRemondThm14An`), `R20Lower` (proved in the tree from Faltings' Lemma 5 lower half,
`faltingsLemma5Lower`). The tree has no separate Faltings 1983 isogeny-variation leaf beyond these.

New glue: `CMFibreSplit` (largest; A8 without NoCM plus the matrix-unit splitting and the CM order of `E`),
`ReducedCMPeriod` (on-the-spot), `HeightAdditivityUpper`, and `ModularConstituentNC` (§5).

## 5. Remaining step 1: localize the non-CM chain (`ModularConstituentNC`)

The chain proves `ModularConstituent` from FS5 and `FibreSimple`, both global; every use is at the fibre
context `(Y, Φ, π, u, P)` of the statement being proved (VERIFIED for `fibreSimple_of_pieces_hf`,
`conjMapsOnHomField_of`, `modelG3G6_of` (TailF L2316), `modularConstituent_of_ranges`). The localized
copies needed (each the original with the hypothesis `NoCMAt Y Φ π u` threaded):
`conjMapsOnHomField_of` → `kernelFieldExists_of_leaves(_hf)`, `_of_split_hf`, `_hf'`, `_hf''`;
`HSyn.LinkedTate.modelG3G6_of`, `modelG3G6_of_leaves3`; `LTLocal.linkedTateLocal_of_tateBridge35`,
`linkedTateLocal_of_leaves3_hf`, `linkedTateData_of_local`; `afterG7_of3_hf_pz_eb`;
`fieldDescentUnr`, `modularConstituent_of_ranges(_T14)`, `modularConstituent_of_G`,
`modularConstituent_of_field_hf_pz`, with NC versions of the Props `KernelFieldExists`,
`ConjMapsOnHomField`, `ModelG3G6`, `LinkedTateLocal`, `LinkedTateData`, `AfterG7`, `ModularConstituentG`.
No mathematics changes (the manuscript's non-CM paragraph L632-900 assumes `End⁰(A_ℚ̄) = B` throughout),
only bookkeeping. `fibreSimpleNC_of_pieces_hf` is the first such copy.

## 6. Remaining step 2: prune `R5ptProps`; what then leaves the route

After step 1, FS5 is unused, so `R5ptProps`, `r5count`/`gonzalezRotgerCountX6Ab`, `x6KummerFibre`,
`x6ConicModel` (if read nowhere else) and `cmOptimalEmbedding` are dead. `R5ptProps` is a conjunct of the
row `R1R2fpRepW`, so `gonzalezRotgerThm512X6RCF` stays syntactically on the route until the row is
replaced by its weak form without `R5ptProps` (sem-prune recipe: weaker row threaded through the chain,
then PruneScan). `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` stay (they produce `X6Props`, `π₆`).

## 7. Compile log and the fold

See `scratch/cm-branch/log.md`. `Arith.lean` and `CMBranch.lean`: compiled, standard axioms. `NonCM.lean`
needs the chain built to `EichlerBoundCopy`; its status is recorded in the log and in §8.

Fold: a hand-fold (`scratch/cm-branch/autofold.json` records it as a spec, not a mechanical
discharge). No top field can be discharged by these theorems: the fields above are still read by the
moduli row. The fold replaces, at the generation of `sixContactMin_of_leavesR3_hf_pz_eb`, the glue pieces
`fibreSimple` and `modularConstituent` (both proved today through FS5) by `sixContactMin_of_cmBranch`
with `ModularConstituentNC` and the CM-branch statements; it raises the GLUE count until step 1 is done,
so it should be applied only together with step 1 and the prune of step 2.

## 8. Known issues

1. **Uncited classical inputs in the CM paragraph.** L586-587 (`[ℚ(j(E)):ℚ] = h(Δ)`), L596-597
   (CM ⇒ potentially good reduction, "since its `j`-invariant is integral") and L598-599 (reduced CM
   period, `√3/2 ≤ y ≤ √|Δ|/2`) carry no citation. They are classical and true; here they are the leaves
   `CMjDegree`, `CMPotentialGood` (with proposed sources, UNVERIFIED numbers) and the on-the-spot glue
   `ReducedCMPeriod`. The upstream audit (FINDINGS.md) attributes the degree statement to Fowler §2.1 and
   the good reduction to [cmheight] p. 15; neither was read here.
2. **The CM branch needs A8 without NoCM.** The manuscript's `d = [L:ℚ] ≤ D` for the CM fibre is A8's
   field (L520-562), whose proof precedes the case split. The chain's `KernelFieldExists` is proved
   through FS5, so for CM fibres it is not available; `CMFibreSplit` carries it as glue.
3. **The `X₆` fields are not NoCM-only** (§2): the target cannot be reached by the CM branch alone.
4. **Reading risk for (6.2).** Only the AUDIT reading of Eq. (6.2) is available (normalization
   `Δ = (2π)¹²η²⁴`, original metric); the leaf is stated as the inequality the manuscript uses, for good
   reduction everywhere.
5. No Gross–Zagier or Tian–Yuan–Zhang argument is used.

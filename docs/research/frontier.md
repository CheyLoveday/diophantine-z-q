# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2 to r5, 2026-11-14 (text checks only, no Lean run). Base of r5:
integration w60 (fork main 28b41fb3), on wip/frontier-r5. Branch snapshot: the commits in `scratch/frontier/refs.txt`
(r5 section, read 13:20 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean`
(compiled 11-13, unchanged in r2). Mechanical check: `scratch/frontier/chain.py` (with `chainlib.py`), run from the
repository root; output `scratch/frontier/chain_out.txt`. Results log: `scratch/frontier/log.md`. Working notes from
three read-only survey agents (11-13): `scratch/frontier/agent-{h-glue,h-leaves,tyz}.md`. Only this report and
`scratch/frontier/` were edited. Model work; no human review.

Marks: **VERIFIED** (read in a named Lean file or report at a named commit, or compiled here), **REPORTED** (a task's
report or log says so; the Lean was not re-read), **UNVERIFIED** (a theorem number or locator taken from a report or
from memory; this host has no network and no copy of the papers).

**Classification (the integrator's rule, applied strictly).** **LEAF** = a published, refereed statement, and the
Lean Prop is that statement or a specialization of it (fewer cases, weaker constant read off the same display).
Textbook theorems (Mumford, Milne, BLR, …) count as published. Everything else is **GLUE**: the project's own
arguments, statements that are standard but not printed in that form, "consequences" whose derivation needs an
argument, readings of a printed statement, and composites of several published theorems. Where a GLUE Prop is a
consequence or composite of published theorems, the table says so ("lit-composite") and names the nearest sources;
it is still GLUE.

**Form and two counts (r3, the integrator's ruling of 2026-11-14).** Every row has a form: *published form* (the
printed statement, or a specialization read off the same display), *consequence of one theorem* (a short
derivation from one printed theorem), *composite* (several published results) or *project glue*. The **strict
count** (LEAF = published form only) leads: every GLUE row under it is a Lean argument the project still owes. The
**lenient count** follows, "if consequences of one theorem count as leaves". A consequence or composite row
becomes a strict LEAF once its derivation is compiled; the form column says where the derivation is written
(for leaf-fold3's fields, leaf-review-a and leaf-review-b).

## 0. Main result

**The list.** If every proof and reduction that the branches had compiled by 2026-11-14 13:20 PST is folded in
(scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **84: 49 LEAF and 35 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 62 LEAF and 22 GLUE. Three of the LEAF rows are
reduct-split's `SemistableReductionDVR`, `SemistableUnipotent`, `NeronSchemeModelExistsDVR` (H-146, H-147, H-148),
published forms pending the integrator's review of the printed base ring; if the review makes them consequences, the
strict count is 46 LEAF and 38 GLUE (the lenient count does not change).

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 69 hypotheses, and its proof uses 63
of them: **39 LEAF and 24 GLUE** in the strict count, 49 and 14 in the lenient count (leaf-fold9's forms for its
fields, with `GonzalezRotgerCountX6` a composite, §4.8). The 6 it never uses (`r3`, `t10` and reduct-split's four
leaves, §4.10) are planned for removal after leaf-fold10; counted with them, the 69 are 43 LEAF and 26 GLUE strict,
54 and 15 lenient. Scenario F has more rows because it also applies the splits that leaf-fold7 to leaf-fold9 left
out on purpose: each replaces one field by a leaf plus smaller statements (leaf-fold9 §5).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 0 | 2 | 0 | 2 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 5 | 2 | 3 | 3 | 2 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 5 | 3 | 2 | 3 | 2 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 1 | 0 | 1 | 1 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 6 | 5 | 1 | 5 | 1 | §4.5 |
| H: fields of the H base introduced in r4 | 30 | 29 | 1 | 29 | 1 | §4.6 |
| H: Props open only in scenario F, introduced in r4 | 12 | 3 | 9 | 5 | 7 | §4.7 |
| H: fields of leaf-fold9 introduced in r5 | 4 | 3 | 1 | 3 | 1 | §4.8 |
| H: Props open only in scenario F, introduced in r5 | 19 | 4 | 15 | 13 | 6 | §4.9 |
| **total** | **84** | **49** | **35** | **62** | **22** | |

By form: 49 published form, 13 consequences of one theorem, 13 composites, 9 project glue: under the tame-quotient
coordinate `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ` (§4.1); reduct-split's `FixedTorsionRationalImperfect`,
`SemistableLocalGlobal`, `SemistableAlmostAll`, `SemistableNeronBaseChangeLocalGlobal`; modular-split's
`H0DifferentialsEqHolo` and `HTDual`.

**Since r4 (23 new rows; 7 LEAF and 16 GLUE strict, 16 and 7 lenient).** 1 row is proved outright:
`DeligneSerreConseq` (H-12; modular-split, from `DSThm966`). 14 rows are split into smaller statements (§4.1), 3 leave
the route (H-114..H-116: leaf-fold9 takes `r5count` from shimura-split's count on points), and H-143 is dropped: it
was a renaming of H-43. The H base is leaf-fold9's `sixContactMin_of_open9` inside the library (C4''''', §1). It
proves `r1rec` and `r5` from `r1r2` (shimura-split's bridge), `r15` from `dsThm966` (modular-split), `t33` and
`normalModelOfFunctionFieldQ` (cloud PR #11), takes `r7b` and `r8` from reduct-split's four leaves and `r5count` from
shimura-split's `GonzalezRotgerCountX6`, so `ZInQ.OneProof.frozenTarget` on main is scenario A as one theorem (§6). On
top of it scenario F applies shimura-split (`r1r2`, H-43, H-59, H-139), modular-split (H-21, H-78, H-127),
reduct-split (H-4, H-106..H-108, H-111) and, from r4, qm-split's H-44 split, mcr-glue and mcr-quot under the
coordinate, and tyz-split's T-5 split.

**Being attempted (cloud workers W11-W15):** `TateTwistInvariants`, `AxSenTate`, `X0Transitive` (it would remove
`IgusaGL2`), `RegularSmoothPerfect`, `ShimuraGoodReductionNoGuard`, and the F-only leaf `FiniteQuotientExists`. The
rows say so. `CanonicalModelY3`, also being attempted, left the list: shimura-split derives it (§4.1).

**The 84 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.GZDecomp.FHNonvanishing`; `ZInQ.GZDecomp.GrossZagierHeegner`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2`; `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (L); `ZInQ.Contrib.TYZGenus.TYZSplitT5.CMModuli` (c); `ZInQ.Contrib.TYZGenus.TYZSplitT5.X0RatStructure`.
- H: `PkgI2.NeronOggShafarevich` (L); `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `LeafModCurves.R16_EichlerShimuraJ1'`; `WeilPairing.T09_SymmIsogenyExists` (c); `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` (L); `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` (L); `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `ZInQ.Contrib.AVB1.PoincareComplement` (L); `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (L); `ZInQ.Contrib.CurvesG.GenusX1Field`; `AVGlue.CartierSmooth` (L); `AVGlue.GeomConnOfRationalPoint` (L); `AVGlue.GroupSchemeEquidim` (L); `AvSplit.T4.MulEtaleAbelianScheme` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `BPAnalytic.Uniformization.UniformizationLeafAll` (L); `AvSplit.MilneIsogenyQuasiInverse` (L); `ZInQ.HomLattice.GAGAMorphism` (L); `ZInQ.HeightSplit.JavanpeykarBound` (L); `ZInQ.HeightSplit.GaudronRemondThm14` (L); `ZInQ.HeightSplit.BostLowerBound` (L); `ZInQ.HeightSplit.PazukiCor13Upper` (L); `ZInQ.RLeaf.IgusaGL2` (L); `CurveSplit.RegularSmoothPerfect` (L); `CurveSplit.ShimuraGoodReductionNoGuard`; `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` (L); `ZInQ.Contrib.HodgeSplit.AxSenTate` (L); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (L); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (L); `ZInQ.Contrib.HodgeSplit.BdRInvariants` (L); `ZInQ.Contrib.HodgeSplit.DSThm965` (L); `ZInQ.Contrib.HodgeSplit.DSThm966` (L); `HDec.QMSplit.Yu.YuThm11` (L); `HDec.QMSplit.Aut.QMCentralizerCMC` (L); `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (L); `HDec.QMSplit.Theta.IgusaPsi4` (L); `HDec.QMSplit.Theta.IgusaChi10` (L); `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (L); `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` (L); `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` (L); `MCRGlue.ProperCurveAF`; `MCRGlue.FiniteQuotientExists` (L); `MCRGlue.TameQuotientSmooth`; `MCRGlue.SmoothModelOfP1` (c); `MCRGlue.TameFixedPointsDisjoint` (c); `MCRGlue.TameInertiaCyclic`; `HDec.PropTSRed.CoverModelOfHeckeN`; `MCRQuot.P1SchemeQ`; `MCRQuot.CMStabObj`; `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaNullNonvanishing` (L); `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaFourthRatiosAlgebraic`; `HDec.QMSplit.Moduli.GonzalezRotgerX6` (L); `ShimuraSplit.GonzalezRotgerCountX6`; `ReductSplit.SemistableReductionDVR` (L); `ReductSplit.SemistableUnipotent` (L); `ReductSplit.NeronSchemeModelExistsDVR` (L); `HDec.QMSplit.Moduli.DeligneComponentsX6` (c); `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` (L); `HDec.QMSplit.Moduli.BabaGranathX6'` (c); `HDec.QMSplit.Moduli.ReciprocityCanonical` (c); `HDec.QMSplit.Moduli.ElkiesConicX6` (c); `HDec.QMSplit.Moduli.ShimuraHolFamily` (c); `ShimuraSplit.DeligneComponentsY3` (c); `ModularSplit.DimJac.H0DifferentialsEqHolo`; `ModularSplit.R17.CarayolRealization` (c); `ModularSplit.EigenHT.KatoRealizationCoh` (c); `ModularSplit.EigenHT.HTDual`; `ReductSplit.RaynaudSemistable` (L); `ReductSplit.FixedTorsionRationalImperfect`; `ReductSplit.SemistablePersistsDVR` (L); `ReductSplit.SemistableLocalGlobal`; `ReductSplit.SemistableAlmostAll`; `ReductSplit.IdentityComponentBaseChangeDVR` (L); `ReductSplit.SemistableNeronBaseChangeLocalGlobal`; `ZInQ.HeightSplit.FaltingsLemma5` (c).

Six bundle fields are hypotheses of the compiled H assembly that its proof never projects: R3, T10 and
reduct-split's four leaves (§4.10). Scenario F uses three of the four (reduct-split's splits of H-4, H-106 and
H-108), so those three are on the list; R3, T10 and `SerreTateThm2` are not.

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on leaf-fold9's
  bundles since w60) derives `ZInQ.FrozenTarget` from leaf-fold9's four bundles (30 + 18 + 14 + 1 = 63 fields), the
  TYZ Props `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraReciprocityModFn`, `TYZThm33` and the two GZ Props.
  leaf-fold9 reports `lake build +ZInQKernel.OneProof.Main` exit 0 and standard axioms (REPORTED, leaf-fold9 §1, §4).
  `chain.py onep` reads its signature: its hypotheses are scenario A's (the four bundles and the six top Props), and leaf-fold9's `fields9.tsv` lists the bundles' fields with the same names and types (the table abbreviates `bdRInvariants`'s binders).
- **Scenario F.** A plus the edges of §4.1, each compiled on its branch per its report and log. `chain.py` checks
  signatures (0 mismatches over 165 theorem edges, 30 of them followed on the route) and compares definitions where
  a proof lives in another Lean world (§5.2). F is not compiled as one file.

**Declarations proved by this task.** All compile with `lake env lean` (exit 0, no `sorry`), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each (VERIFIED; outputs `scratch/frontier/TYZChain_out.txt`,
`TopChain_out.txt`).

```lean
-- scratch/frontier/TYZChain.lean: tyz-cm's eleven Shimura modules and cm-bridge's Bridge.lean, both as on
-- cm-bridge ed50dc33 (which merges tyz-cm 0ad48a7d), verbatim minus imports (build_tyz.py), then:
theorem ZInQ.GZTheta.Frontier.newCM : ZInQ.GZTheta.NewCM     -- verbatim copy of atkin-li's proof
theorem ZInQ.GZTheta.Frontier.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.Frontier.tyzThm35ReadingA_of_open (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hS : ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Frontier.frozenTarget_of_open (hH : ZInQ.SixContactMin) (h11 …) (h1 …) (h29 …) (hS …)
    (h318 …) (h35 …) (h5 …)                          -- the seven hypotheses above
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
-- scratch/frontier/TopChain.lean: the same over fork main's modules only
theorem ZInQ.Frontier.frozenTarget_of_open_main (hH : ZInQ.SixContactMin)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```
`newCM`/`heckeThetaNewform` show that atkin-li's proof of the GZ leaf `HeckeThetaNewform` compiles verbatim over fork
main's modules; `TYZChain.lean` shows that tyz-cm's and cm-bridge's reductions compose.

**Findings in brief** (§7): since r4, 1 row proved, 14 split, 3 off the route and 1 dropped; scenario A is one
library theorem whose proof uses 63 of its 69 hypotheses (39 LEAF strict); `GonzalezRotgerCountX6` counts as a
composite; the 9 project-glue Props are under the tame-quotient coordinate, in reduct-split's local-to-global
steps and in two of modular-split's splits.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4''''' (r5) | H: `HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ9.lean` L161 @ main (leaf-fold9 cf6914e1, merged in w60; over leaf-fold8's `sixContactMin_of_open8` in `TailZ4.lean`: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open9` without `sorryAx`; REPORTED by its report §1, §4) | → `ZInQ.SixContactMin`; 30 + 18 + 14 + 1 fields (§4) |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`, 31 + 20 + 14 + 1 fields; superseded: leaf-fold9 fills its bundles (`researchLeaves8_of_open9`, `textbookLeaves8_of_open9`) inside OneProof |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4''''' in the library (r5)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves9) (t : HDec.HSyn.OpenTextbookLeaves9) (l : HDec.HSyn.OpenAddedLeaves8) (g : HDec.HSyn.OpenGlue7) (h11 …) (h29 …) (hS …) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hL2 …) (hL3 …) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; `OneProof/TYZSplit.lean` since w59; leaf-fold9's bundles since w60) | scenario A of this report: C4''''' with tyz-chain's T0, T-11 from the printed Theorem 3.3, and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4''''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's 45-field
`GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's `sixContactMin_of_open2`) are
superseded by C4, C4', C4'', C4''' and C4''''.

## 2. GZ: `ZInQ.Literature.GrossZagier`

Only `C_d`, `d ≡ 5 (mod 8)` squarefree, is used (gz-decomp §0.3): the chain goes through `ZInQ.GZDecomp.GrossZagierCd`,
which `Literature.GrossZagier` implies (`grossZagierCd_of_grossZagier`).

### 2.1 Chain (VERIFIED: signatures read; Z5 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| Z1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd` | `Contrib/GZDecomp/Scope.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `GrossZagierCd` → `FrozenTarget` |
| Z2 | `ZInQ.GZDecomp.grossZagierCd_of_leaves'` | `Contrib/GZDecomp/Decomp.lean` @ main | `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `GrossZagierCd` (glue G1-G6 proved) |
| Z3 | `ZInQ.GZTheta.heckeThetaNewform : HeckeThetaNewform` | `Contrib/GZTheta/NewCMFinal.lean` @ atkin-li 6f77abb1 | no hypotheses (also `AtkinLiTwistNew`, `NewformUniqueAcrossLevels` proved there) |
| Z5 | `ZInQ.GZTheta.Frontier.heckeThetaNewform` | `scratch/frontier/TYZChain.lean`, `TopChain.lean` | verbatim copy of Z3, compiled over fork main, standard axioms |

### 2.2 Open Props (2, both GLUE)

| # | Lean name | defined in | class | nearest published sources (all numbers UNVERIFIED) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| Z-1 | `ZInQ.GZDecomp.FHNonvanishing` | `Contrib/GZDecomp/Decomp.lean:109` @ main | GLUE (lit-composite: Friedberg–Hoffstein's theorem with chosen local conditions, plus the root number of a twist `ε(f⊗χ_D) = ε(f)χ_D(−N)`; gz-decomp §2.4 argues it is not stronger than the source; **open**: whether FH's printed theorem allows the level `32d²`, even and not squarefree; a human must check) | Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385–423, Thm B; Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990) 543–618; Waldspurger, Compositio Math. 54 (1985); Atkin–Li, Invent. Math. 48 (1978) | gz-decomp; main | no | composite: Friedberg–Hoffstein's theorem with chosen local conditions and the root number of a twist (gz-decomp §2.4) |
| Z-2 | `ZInQ.GZDecomp.GrossZagierHeegner` | `Contrib/GZDecomp/Decomp.lean:131` @ main | GLUE (lit-composite: Gross–Zagier's formula, Gross's `ȳ_K = −ε y_K`, the modular parametrization (Eichler–Shimura, Faltings' isogeny theorem), nondegeneracy of `ĥ` (proved in Tau Ceti), folded into one existential because the Heegner point cannot be named in Lean today; gz-decomp §2.5) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3, Ch. V; Gross, *Heegner points on X₀(N)* (Durham 1983), 1984, §5; Shimura 1971 Thm 7.14–7.15; Faltings, Invent. Math. 73 (1983), Kor. 2; Shimura, Nagoya Math. J. 43 (1971) | gz-decomp; main | no | composite: Gross–Zagier's formula, Gross's conjugation relation, the modular parametrization, nondegeneracy of the height (gz-decomp §2.5) |

Already on record, not applied (gz-decomp §0.3): replace the premise `Literature.GrossZagier` by `GZDecomp.GrossZagierCd`.

## 3. TYZ: `ZInQ.Literature.TYZThm35ReadingA`

Caveats attached to every row (tyz-decomp §0): reading A is printed in no refereed text (only in Smith,
arXiv:1603.08479, Thm 2.1, unrefereed); TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 = Asian J. Math. 21 (2017) 721–774,
read by AI agents in the arXiv version only; `Lnnnn` are lines of its source `Period7.tex` as quoted by the reports
(not on this host); Proposition N and the encoding were reviewed by AI models only.

### 3.1 Chain (VERIFIED: signatures read by `chain.py`; T0 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| A1 | `ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves` | `Contrib/TYZDecomp/Leaves.lean:380` @ main | `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`, `TYZGenusPackage` |
| A2 | `ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cmLeaves` | `Contrib/TYZGenus/Package.lean:948` @ main | h11, h1, h29, `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| A3 (finest in a kernel module on main) | `ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` | `Contrib/TYZGenus/RingClassBridge.lean:55` @ main | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (`IInH4`, `HprimeNormal` proved: `iInH4`, `hprimeNormal`); used by `TopChain.lean` |
| B1 (cm-bridge, scratch) | `ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five` | `scratch/cm-bridge/Bridge.lean` L3201 @ cm-bridge ed50dc33 (final; merges tyz-cm 0ad48a7d) | h11, h1, h29, `Shimura.ShimuraReciprocityModFn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`, `Lemma321Five` |
| inside B1 | cm-bridge: `GenusFieldLeLni`, `IInHprime`, `BetaOnGenus7`, `tyzThm36Seven_of` (TYZ Thm 3.6(3) from `ShimuraReciprocityPic`, `EtaModelFricke`, `CMAlgebraic`); tyz-cm: `etaModelInvariant`, `etaModelEquation`, `etaModelFricke`, `etaCuspGrowth`, `xQExpRational`, `yQExpRational`, `cmValueRingClass_of_modFn`, `shimuraReciprocityPic_of_shimuraModFn`, `cmFieldOfDefinition_of_cmValueRingClass` (proved) | `ZInQKernel/Contrib/TYZGenus/Shimura*.lean` (11 modules) and `Bridge.lean` @ ed50dc33 | |
| **T0** (this task, compiled) | `ZInQ.Frontier.tyzThm35ReadingA_of_open` (= B1) | `scratch/frontier/TYZChain.lean` (B1 with the 11 tyz-cm modules, verbatim) | the 7 Props of the 17:35 list → `TYZThm35ReadingA`; with B2-B4, the 5 Props of §3.2 |
| B2 (r2) | `ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves` | `scratch/tyz-lcal/TYZLcal.lean` L900 @ tyz-lcal 61d0b14e (on main since w52) | `TYZThm11Integral`, `TYZLemma29Mod2` → `TYZLcalOne` (Theorem 1.1 at `m = 1`, Lemma 2.9 mod 2 at `m = 3`, and an analytic bound `‖L(C₁,1)‖ ≤ 3.35` from the fork's Hecke continuation) |
| B3 (r2) | `ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn'` | `scratch/tyz-321/L321.lean` L5460 @ tyz-321 521eacc0 | `Shimura.ShimuraReciprocityModFn` → `Lemma321Five` (ring class field theory, the kernel's genus theory, cm-bridge's genus characters; no TYZ text) |
| B4 (r2) | `ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33` | `scratch/tyz-35/Thm35.lean` L1363 @ tyz-35 a8101726 (on main since w52) | `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ` |
| B5 (r3) | `T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn` with `Sqrt2Glue.sqrtTwoNotInHHprime` | `Contrib/TYZChain/Lemma318.lean`, `Sqrt2Glue.lean` @ w54 (tyz-318 94b05c87, sqrt2-glue 84107b66) | → `Lemma318Literal HHprime`, no hypotheses (ss-exponent proved the supersingular exponent tyz-318 used) |
| **T0 (r3, kernel)** | `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/TYZChain/Main.lean` @ w54 (tyz-chain; B1 with B2-B5 as kernel modules) | `TYZThm11Integral`, `TYZLemma29Mod2`, `Shimura.ShimuraReciprocityModFn`, `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `TYZThm35ReadingA` |
| T0' (r4) | `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33` | `ZInQKernel/OneProof/TYZSplit.lean` @ main (tyz-split 99e582b5, compiled into OneProof by leaf-fold8) | `TYZThm33` → T0's hypothesis `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ`, so T-11 follows from the printed Theorem 3.3; both scenarios use it |
| B6 (r4) | `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` | `scratch/tyz-split/T5.lean` @ main | `CMModuli`, `X0RatStructure` → `Shimura.ShimuraReciprocityModFn`; scenario F uses it |

### 3.2 Open Props (5: 2 LEAF, 3 GLUE in the strict count; 3 LEAF, 2 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-3 | `ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2` | same | GLUE (mod-2 composite of Lemma 2.9 and Prop. 2.3) | TYZ Lemma 2.9, L1062–1066 (journal Lemma 2.9 per the AI locator audit); Prop. 2.3, L580–586 | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | composite: TYZ Lemma 2.9 with Prop. 2.3, read mod 2 (tyz-lcal audit) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L147 @ main | **LEAF** | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | no | published form: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1), carried along the kernel's eta model of `X₀(32)` by the q-expansion principle (`IsRatModFn 32`), which already sits behind `hS`; a clause-by-clause statement review found the leaf Thm 3.3 or weaker (tyz-split §1 and the docstring, wip/w61 3c241950); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566) |
| T-13 | `ZInQ.Contrib.TYZGenus.TYZSplitT5.CMModuli` | `scratch/tyz-split/T5.lean` L92 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | the CM leaf for `j` and the symmetric functions of Weber values on the level structure | tyz-split | no | consequence of one theorem: Shimura 1971 Thm 5.4 with torsion, by shimura-modfn's lattice computation (tyz-split §1) |
| T-14 | `ZInQ.Contrib.TYZGenus.TYZSplitT5.X0RatStructure` | `scratch/tyz-split/T5.lean` L118 @ main | GLUE (composite) | on `Y₀(N)` the `ℚ`-structure of rational `q`-expansions is the moduli `ℚ`-structure; no CM | tyz-split | no | composite: the canonical model of `X₀(N)` with separation of points by Weber coordinates (tyz-split §1) |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11, B4),
T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)).

## 4. H: `ZInQ.SixContactMin`

Base (r5): leaf-fold9's compiled C4''''' (cf6914e1, in w60), inside OneProof, over leaf-fold8 (b0f2f6da, w59) and
leaf-fold7 (53acb891, w58). leaf-fold9 proves `r1rec` and `r5` from `r1r2` (shimura-split's bridge), `r15` from
`dsThm966` (modular-split), `t33` and `normalModelOfFunctionFieldQ` (cloud PR #11), and replaces `r7b`, `r8` by
reduct-split's four published-form leaves and `r5count` by shimura-split's `GonzalezRotgerCountX6`. Bundles:
`OpenResearchLeaves9` (30), `OpenTextbookLeaves9` (18), leaf-fold8's `OpenAddedLeaves8` (14) and leaf-fold7's
`OpenGlue7` (1: `quotientP1Coordinate`). leaf-fold9's count of these 63 fields (its §1): 42 published form, 11
consequences, 9 composites, 1 project glue; this report counts `GonzalezRotgerCountX6` as a composite (§4.8).
`chain.py` reads the bundles from `ZInQKernel/OneProof/H/TailZ9.lean`, `TailZ4.lean` and `TailX.lean` at main, and
the forms of the fields from leaf-fold9's `scratch/leaf-fold9/fields9.tsv`. Row numbers are kept, retired rows
listed, new rows from H-145 (§4.8, §4.9).

### 4.1 What changed since r4 (signatures VERIFIED by `chain.py`)

Compiled into C4''''' (scenario A, leaf-fold9): H-12 (`r15`) proved from `DSThm966` (modular-split); `r1rec` and `r5`
(never projected, never rows) from `r1r2`; `t33` and `normalModelOfFunctionFieldQ` proved (cloud PR #11; scenario F
had them in r4, H-36 and H-80); `r7b` and `r8` (never projected) from reduct-split's four leaves; `r5count` from
shimura-split's `GonzalezRotgerCountX6` (H-145), which takes height-glue's route for H-3 (H-114..H-116) off the list.
r4's changes are in the r4 report (`git show 5fd81e87:docs/research/frontier.md`, §4.1).

Applied on top by scenario F:

| field of C4''''' (rows) | now | theorems · task · file |
|---|---|---|
| `r1r2` (H-1; r4: H-137, H-138, H-140, H-141, H-142) | ⇐ `DeligneComponentsX6`, `GeomConnOfAlgClosure`, T5, `BabaGranathX6'`, `ReciprocityCanonical` (H-149, H-150, H-151, H-152) and `GonzalezRotgerX6` (H-142); shimura-split proves coarse-factor's inputs `CanonicalModelY3`, `ReciprocityOfFine`, `CanonicalCoarseX6` (with `PairsLift` from T5) and the surjectivity clause of `BabaGranathX6` | `HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5` · shimura-split, over coarse-factor's `r1r2fpRep_of_canonical''` · `scratch/shimura-split/Rows.lean` |
| `x6ConicModel` (H-43; r4: H-143) | ⇐ `ElkiesConicX6` (H-153) with `r1r2` and T5 (the kernel's `mobiusGlue_of_t5`) | `HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5` · shimura-split · `scratch/shimura-split/Rows.lean` |
| `y3Connected` (H-59) | ⇐ `DeligneComponentsY3` (H-155) with the orbit computation | `HDec.QMSplit.Moduli.y3Connected_of_deligne` · shimura-split · `scratch/shimura-split/Rows.lean` |
| `shimuraFamily` (H-139) | ⇐ `ShimuraHolFamily` (H-154) with the GAGA-level step | `HDec.QMSplit.Moduli.shimuraFamily_of_hol` · shimura-split · `scratch/shimura-split/ShimuraFam.lean` |
| `dimJacobianEqGenus` (H-78) | ⇐ the project glue `H0DifferentialsEqHolo` (H-156): no literature leaf is left | `ModularSplit.DimJac.dimJacobianEqGenus_of_glue` · modular-split · `scratch/modular-split/DimJac.lean` |
| `r17` (H-21) | ⇐ `CarayolRealization` (H-157); the transport to every attached representation is proved | `ModularSplit.R17.carayolR17'_of_realization` · modular-split · `scratch/modular-split/R17.lean` |
| `eigenformHTNew` (H-127) | ⇐ `KatoRealizationCoh` and the glue `HTDual` (H-158, H-159) | `ModularSplit.EigenHT.eigenformHTNew_of_coh` · modular-split · `scratch/modular-split/EigenHT.lean` |
| `r6` (H-4) | ⇐ `RaynaudSemistable`, `SemistableUnipotent`, `NeronSchemeModelExistsDVR`, `MumfordTorsionAlgClosed` and the glue `FixedTorsionRationalImperfect` (H-160, H-147, H-148, H-102, H-161) | `ReductSplit.raynaudCriterion_final'` · reduct-split · `ZInQKernel/OneProof/H/TailZ7.lean` (its `Reduction.lean` verbatim) |
| `semistableReductionThm`, `semistableNeronBaseChange`, `semistablePersists` (SS1-SS3, H-106..H-108) | ⇐ `SemistableReductionDVR`, `SemistablePersistsDVR`, `IdentityComponentBaseChangeDVR`, `NeronSchemeModelExistsDVR` and the glue `SemistableLocalGlobal`, `SemistableAlmostAll`, `SemistableNeronBaseChangeLocalGlobal` (H-146, H-162, H-165, H-148, H-163, H-164, H-166) | `ReductSplit.semistableReductionThm_final`, `ReductSplit.semistableNeronBaseChange_of_leaves`, `ReductSplit.semistablePersists_final` · reduct-split · `ZInQKernel/OneProof/H/TailZ7.lean` |
| `faltingsLemma5BC` (H-111) | ⇐ `FaltingsLemma5` (H-167), the base-field form; the base change is proved | `ReductSplit.faltingsLemma5BC_final` · reduct-split · `ZInQKernel/OneProof/H/TailZ7.lean` |
| `thetaRatiosAlgebraic` (H-44) | ⇐ `ThetaNullNonvanishing`, `ThetaFourthRatiosAlgebraic` (a published leaf and a smaller composite; leaf-fold7 §5 kept the field) | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of` · qm-split · `scratch/qm-split/ThetaRatios.lean` |
| `quotientP1Coordinate` (the glue field; H-84's successor) | ⇐ mcr-glue's six leaves (H-89..H-94; `TameQuotientSmooth` is L3), T5, and three glue Props: mcr-quot's `P1SchemeQ` and `CMStabObj`, and the decomposition's `CoverModelOfHeckeN` | `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (compiled in `ZInQKernel/OneProof/H/TailW.lean`) with mcr-glue's `coordinateNormalization_of` · mcr-glue · `scratch/mcr-glue/MCRGlue.lean`; `fibreAutTame_of''`, `genericQuotientP1_of''`, `cMSectionsDisjoint_of''`, `coordinateFromSections_of''` and their inputs (namespace `MCRQuot`) · mcr-quot · `scratch/mcr-quot/MCRQuot.lean` |

mcr-quot proves the four glue Props under the coordinate (`FibreAutTame`, `GenericQuotientP1`, `CMSectionsDisjoint`,
`CoordinateFromSections`) from T5, L3, `CurveBijIso` and three glue Props: `P1SchemeQ` and `CMStabObj`, which are
new, and `CoverModelOfHeckeN`, the decomposition's own glue. The chain derives `CoverModelOfHeckeN` only through
`HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds, so here it is counted as open glue: the coordinate
still rests on project glue, and mcr-quot does not discharge it.

On the TYZ side F uses B6 (§3.1). Off the route since r5 (the edges stay in `chain.py`): coarse-factor's
`r1r2fpRep_of_canonical''`, which shimura-split's theorem extends; qm-glue's and coarse-factor's `x6ConicModel`
theorems with `ConicCanonical`, which is `X6Kummer.X6ConicModel` verbatim (shimura-split, `Iff.rfl`); height-glue's
`r5fpCount_of_t11b`; the cloud-w07 proofs, now inside C4'''''. The r2-r4 edges compiled inside C4'''' are off the
route as well. Retired rows (r2, r3): H-23, H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-45, H-47, H-48, H-50,
H-55, H-58, H-62; r4: H-1, H-2, H-3, H-8, H-10, H-14..H-20, H-22, H-24, H-25, H-32, H-33, H-35, H-36, H-38,
H-41..H-44, H-46, H-51, H-52, H-54, H-61, H-63, H-64, H-66, H-67, H-69, H-73..H-76, H-80..H-88, T-5, T-11; r5: H-4,
H-12, H-21, H-59, H-78, H-106, H-107, H-108, H-111, H-114, H-115, H-116, H-127, H-137, H-138, H-139, H-140, H-141,
H-143.
Not applied: the variants each report keeps aside (r4: height-split's `r20_of_leaves` with
`IsogenySemistableBaseChange`; curve-split's `x0Transitive_of_igusaSL2X`; qm-split's `qmHauptmodulBase3_of_shimizu`
and `y3Connected_of`; hodge-split's `panBerger_of_templates`; r5: shimura-split's `r1r2fpRep_of_split6`, which keeps
`r1rec` and `r5` as inputs; modular-split's weaker `KatoRealization` leaf; reduct-split's `raynaudCriterion_final`,
which `raynaudCriterion_final'` supersedes by proving the perfect case of its glue).

### 4.2 Research-level fields of r3 still open (5: 3 LEAF, 2 GLUE strict; 3 LEAF, 2 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-5 | `r7a : PkgI2.NeronOggShafarevich` | R7(a) | **LEAF** | Serre–Tate, Ann. of Math. 88 (1968), Thm 1 | UNVERIFIED | pkg-I2 | published form: Serre–Tate 1968 Thm 1 (leaf-review-b §2.2) |
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4 | composite: Pan and Berger (leaf-review-b §2.4) |
| H-13 | `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | GLUE (three suppliers) | Shimura 1971 Thm 7.9; Shimura 1973 Thm 1 | | leaf-modcurves | composite: Shimura 1973, Shimura 1971 §7.4, Diamond–Shurman (leaf-review-a §3.3) |

### 4.3 Textbook fields of r3 still open (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

None left: each is proved or split (§4.1).

T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.
T4, T5, T23, T24, T27, T33, T35, T40 and the normal model of a function field are proved or split in r4 (§4.1).

### 4.4 Fields that were glue in C4, still open (in C4''''' they are `OpenAddedLeaves8` fields) (1: 0 LEAF, 1 GLUE strict; 1 LEAF, 0 GLUE lenient)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-53 | `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | a35 | symmetric isogeny to a dual; "existential in D, hence a consequence" (Mumford §§6, 8, 20, 23) | LEAF | weil-pairing; no | consequence of one theorem: Mumford §§6, 8, 20, 23 (leaf-review-b §2.1) |

### 4.5 Props introduced by reductions until r3, still open (6: 5 LEAF, 1 GLUE strict; 5 LEAF, 1 GLUE lenient)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-65 | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | `ZInQKernel/Contrib/SpreadOut/Spread.lean` L49 @ main | 44-46 | **LEAF** (descent of properness; EGA IV₃ 8.10.5(xii), Stacks 081F) | spread-out | published form: EGA IV₃ 8.10.5(xii) (spread-out) |
| H-70 | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L38 @ main | t6 (H-26) | **LEAF** (T6 over algebraically closed fields only: Mumford, *Abelian varieties* §19 Thm 3 in Mumford's own setting; Milne 1986 Thm 12.5) | av-b1 | published form: Mumford §19 Thm 3 in its own setting (av-b1 §3.1) |
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | same, L51 | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1 | published form: specialization of Mumford §19 Thm 4 (av-b1 §3.2) |
| H-72 | `ZInQ.Contrib.AVB1.PoincareComplement` | `Contrib/AVB1/Poincare.lean` L42 @ main | t8 (H-28) | **LEAF** (Poincaré's complete reducibility in its complement form, weakened; Milne 1986 Prop. 12.1; Mumford §19 Thm 1) | av-b1 | published form: Milne 1986 Prop. 12.1, weakened (av-b1 §3.3) |
| H-77 | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | `Contrib/NeronC/NeronGroup.lean` L82 @ main | t41 (H-39) | **LEAF** (a smooth separated quasi-compact model with the extension property and no group law: weaker than BLR §1.4 Thm 3; the group law, `gen` a homomorphism and uniqueness are proved) | neron-c | published form: BLR §1.4 Thm 3 without the group law (neron-c §1) |
| H-79 | `ZInQ.Contrib.CurvesG.GenusX1Field` | `ZInQKernel/Contrib/CurvesG/GenusSplit.lean` L59 @ main | t34 (H-37) | GLUE (lit-composite: Shimura's canonical model of `X₁(N)`, Shimura 1971 Prop. 6.9, the genus formula Prop. 1.40, base change of `H⁰(Ω¹)`) | curves-g | composite: Shimura 1971 Prop. 6.9 and Prop. 1.40 (curves-g §3) |

Proved and gone from the tables: r5, `DeligneSerreConseq` (modular-split); r4, `EigenformTwist`, the two EGA IV
descents, `ZariskiConnectedness`, `T11bExists`, `NeronMappingAbelianSchemeSurj` (PRs #6-#10), `JacobianExists ℚ`,
`NormalModelOfFunctionFieldQ` (cloud-w07), `QMClassNumberOne` (qm-split), `CurveBijIso` (curve-split); r3,
`GammaStarGen`; r2, `SerreRigidity3`, `T09_WeilPairing` (av-b2), and in the chain below `HeckeVertWitness`:
`SmoothFibreReduced` (smooth-fibre), `SpecialFibreMaxIdeal`, `SpecialFibreUniformizer`, `SpecialFibreDVR`
(vert-witness), `ModelGenericFibre`, `GermOfQbarValues`, `ModelIntegral`, `ModelFunctionField` (model-glue). Props
that r4's own tasks introduced and proved were never rows: height-split's glue (`AnalyticUniformizationExists`,
`AnalyticUniformizationUnique`, `UniformizationDim`, `MetrizationOfUniformization`, `NeronMetrizable`, proved from T35
by height-glue), qm-split's `GammaStarFromO1` (qm-glue), qm-glue's `CoarseFactor` (coarse-factor), mcr-glue's four
glue Props (mcr-quot, from three others). Proved before 17:35: see the 17:35 report (`git show
d8c95123:docs/research/frontier.md`). Props that r5's tasks introduced and proved were never rows: reduct-split's
`TorsionFieldOfDefinition`, `DVRFiniteExtension`, `DVRComapFinite` and `IsogenyBaseChangeDeg`; shimura-split's
`PairsLift` (from T5).

### 4.6 Fields of the H base introduced in r4 (30: 29 LEAF, 1 GLUE strict; 29 LEAF, 1 GLUE lenient)

Each row is a field of C4''''' (its name is in the 'last task' column; leaf-fold9 keeps leaf-fold8's fields) and the
hypothesis of a compiled theorem in the task's file. Its form is leaf-fold9's (fields9.tsv), which keeps leaf-fold8's;
where this report's reading differs the pointer says so. Theorem numbers are the reports' and UNVERIFIED unless a
report read the source.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-98 | `AVGlue.CartierSmooth` | `scratch/av-glue/Combined.lean` L297 @ main | H-73, H-74 | **LEAF**; a group scheme locally of finite type over a field of characteristic 0 is smooth | av-glue; field `cartierSmooth` of leaf-fold9 | published form: Cartier's theorem; Mumford AV §11 Thm 1; Stacks 047N (av-glue §5) |
| H-99 | `AVGlue.GeomConnOfRationalPoint` | `scratch/av-glue/Combined.lean` L902 @ main | H-74 | **LEAF**; a connected scheme of finite type over `k` with a rational point is geometrically connected | av-glue; field `geomConnOfRationalPoint` of leaf-fold9 | published form: Stacks 04KV, specialized to finite type with a rational point (av-glue §5) |
| H-100 | `AVGlue.GroupSchemeEquidim` | `scratch/av-glue/Combined.lean` L913 @ main | H-74 | **LEAF**; the irreducible components of a group scheme of finite type over a field have its dimension | av-glue; field `groupSchemeEquidim` of leaf-fold9 | published form: Stacks, group schemes over a field; SGA 3 VI_A 2.4, finite type (av-glue §5) |
| H-101 | `AvSplit.T4.MulEtaleAbelianScheme` | `scratch/av-split/AvSplitAll.lean` L1835 @ main | H-24 | **LEAF**; `[m]` on an abelian scheme over `Spec O` is étale if `m ∈ O×` | av-split; field `mulEtaleAbelianScheme` of leaf-fold9 | published form: BLR §7.3 Lemma 2; Mumford GIT §6 (av-split §1) |
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold9 | published form: Mumford AV §4 Application 2 (iv) (av-split §1) |
| H-103 | `BPAnalytic.Uniformization.UniformizationLeafAll` | `ZInQKernel/HDecomp/Analytic/Uniformization.lean` L91 @ main | H-38, H-69 | **LEAF**; the kernel's AN3 leaf: `A^an` in coordinate form | av-split; field `uniformizationLeafAll` of leaf-fold9 | published form: Mumford §1 in coordinate form (bp-analytic §4; av-split §1 shares the judgement) |
| H-104 | `AvSplit.MilneIsogenyQuasiInverse` | `scratch/av-split/AvSplitAll.lean` L1361 @ main | H-54 | **LEAF**; `fg = [d]`, `gf = [d]` as morphisms for some `d ≥ 1` | av-split; field `milneIsogenyQuasiInverse` of leaf-fold9 | published form: Milne 1986 Rem. 8.4; Mumford §7 (av-split §1) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | **LEAF**; GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold9 | published form: Serre, GAGA, in the form of homlattice §3.2 (av-split §1) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | **LEAF**; Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold9 | published form: specialization of Javanpeykar 2014 Thm 1.1.1 to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | **LEAF**; Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold9 | published form: Gaudron–Rémond 2014 Thm 1.4 (height-split table) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | **LEAF**; `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold9 | published form: Bost, Sém. Bourbaki 795 (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | **LEAF**; the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold9 | published form: Pazuki 2012 Cor. 1.3(2), read off the same display (height-split §3) |
| H-117 | `ZInQ.RLeaf.IgusaGL2` | `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean` L120 @ main | H-41 | **LEAF**; Igusa's theorem: `GL₂(ℤ/N)` is the Galois image on `E_j[N]` | curve-split; field `igusaGL2` of leaf-fold9; being attempted (cloud as `X0Transitive`, which would remove this row) | published form: Igusa 1959; Shimura 1971 Thm 6.6 (curve-split §3.1) |
| H-118 | `CurveSplit.RegularSmoothPerfect` | `scratch/curve-split/CurvesGSplit.lean` L81 @ main | H-81 | **LEAF**; a finite type algebra over a perfect field is smooth at a prime with regular local ring | curve-split; field `regularSmoothPerfect` of leaf-fold9; being attempted (cloud) | published form: Stacks 00TV, the ⇐ half (curve-split §3.3) |
| H-119 | `CurveSplit.ShimuraGoodReductionNoGuard` | `scratch/curve-split/ShimuraGR.lean` L162 @ main | H-83 | GLUE (composite); `ShimuraGoodReduction` without its guard clause | curve-split; field `shimuraGoodReductionNoGuard` of leaf-fold9; being attempted (cloud) | composite: Morita, Carayol, Kottwitz, Buzzard; not statable in published form today (curve-split §3.6) |
| H-120 | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | `scratch/hodge-split/HodgeSplit.lean` L65 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p(i)^{G_K} = 0` for `i ≠ 0` | hodge-split; field `tateTwistInvariants` of leaf-fold9; being attempted (cloud) | published form: Tate 1967 §3.3 Thm 2 (hodge-split §1) |
| H-121 | `ZInQ.Contrib.HodgeSplit.AxSenTate` | `scratch/hodge-split/HodgeSplit.lean` L75 @ main | H-8, H-51, H-52 | **LEAF**; `ℂ_p^{G_K} ⊆ K` | hodge-split; field `axSenTate` of leaf-fold9; being attempted (cloud) | published form: Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 (hodge-split §1) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | **LEAF**; the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold9 | published form: Fontaine 1982; Faltings 1988 (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | **LEAF**; `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold9 | published form: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form (hodge-split §1) |
| H-124 | `ZInQ.Contrib.HodgeSplit.BdRInvariants` | `scratch/hodge-split/HodgeSplit.lean` L3611 @ main | H-32 | **LEAF**; `B_dR^{G_{ℚ_p}} = ℚ_p` | hodge-split; field `bdRInvariants` of leaf-fold9 | published form: Fontaine, Astérisque 223 Exp. II; Brinon–Conrad §4 (hodge-split §1) |
| H-125 | `ZInQ.Contrib.HodgeSplit.DSThm965` | `scratch/hodge-split/HodgeSplit.lean` L1106 @ main | H-10, H-22 | **LEAF**; `k ≥ 2`: the Galois representation of an eigenform and its Frobenius polynomials | hodge-split; field `dsThm965` of leaf-fold9 | published form: Diamond–Shurman Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14) (hodge-split §1) |
| H-126 | `ZInQ.Contrib.HodgeSplit.DSThm966` | `scratch/hodge-split/HodgeSplit.lean` L1124 @ main | H-10, H-22 | **LEAF**; `k = 1`: the Artin representation of an eigenform | hodge-split; field `dsThm966` of leaf-fold9 | published form: Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6 (hodge-split §1) |
| H-128 | `HDec.QMSplit.Yu.YuThm11` | `scratch/qm-split/YuLeaf.lean` L34 @ main | H-35 | **LEAF**; Yu's dichotomy for QM abelian surfaces, with the splitting clause | qm-split; field `yuThm11` of leaf-fold9 | published form: Yu 2013 Thm 1.1, case labels dropped (qm-split §1) |
| H-129 | `HDec.QMSplit.Aut.QMCentralizerCMC` | `scratch/qm-split/QMAut.lean` L1018 @ main | H-42, H-61, H-63 | **LEAF**; over `ℂ`, `End_𝒪(A)` is `ℤ` or an optimally embedded `Φ⁻¹(𝒪)` | qm-split; field `qmCentralizerCMC` of leaf-fold9 | published form: Shimura 1967 §§1-3; Jordan 1981 §3; González–Rotger 2006 §5 (qm-split §1) |
| H-130 | `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | `scratch/qm-split/STQM.lean` L66 @ main | H-86 | **LEAF**; a surface over `ℂ` with a degree-4 field in `End⁰` has a model over `ℚ̄` | qm-split; field `shimuraTaniyamaQbar` of leaf-fold9 | published form: Milne, CM notes §7; Shimura–Taniyama 1961 §12.4 print a number-field model (qm-split §4) |
| H-131 | `HDec.QMSplit.Theta.IgusaPsi4` | `scratch/qm-split/ThetaSplit.lean` L42 @ main | H-2 | **LEAF**; `2⁻²Σθ⁸` is Siegel modular of weight 4 | qm-split; field `igusaPsi4` of leaf-fold9 | published form: Igusa 1962-1967 (leaf-fold7's form; qm-split §4 flags that Igusa prints it as an identity of Eisenstein series) |
| H-132 | `HDec.QMSplit.Theta.IgusaChi10` | `scratch/qm-split/ThetaSplit.lean` L52 @ main | H-2 | **LEAF**; `−2⁻¹⁴∏θ²` is Siegel modular of weight 10 | qm-split; field `igusaChi10` of leaf-fold9 | published form: Igusa 1962-1967, as for `IgusaPsi4` (leaf-fold7's form; flag of qm-split §4) |
| H-135 | `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | `scratch/qm-split/Haupt.lean` L2244 @ main | H-87, H-88 | **LEAF**; the valence formula for cocompact Fuchsian groups | qm-split; field `valenceFormulaCocompactEq` of leaf-fold9 | published form: Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4 (qm-split §1) |
| H-136 | `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | `scratch/qm-split/Haupt.lean` L3205 @ main | H-87, H-88 | **LEAF**; `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` | qm-split; field `shimizuCovolumeO1` of leaf-fold9 | published form: Shimura 1971 Prop. 9.2; Shimizu 1965 (qm-split §1) |
| H-144 | `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` | `scratch/qm-glue/HauptGlue.lean` L4770 @ main | H-88 | **LEAF**; Lin–Yang's Igusa vector at Baba–Granath's CM value `j = −16/27`, in Igusa's theta normalization | qm-glue; field `igusaCMValue24` of leaf-fold9 | published form: Lin–Yang 2020 (2), (14) at Baba–Granath's CM value, in Lauter–Naehrig–Yang's theta conventions: one published number, equivalent to the old glue (qm-glue §0 (a); leaf-fold8 §2) |

### 4.7 Props open only in scenario F, introduced in r4 (12: 3 LEAF, 9 GLUE strict; 5 LEAF, 7 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''. Its form is the task
report's label, or my reading where the report's own text (docstring or review) names more than one source; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-89 | `MCRGlue.ProperCurveAF` | `scratch/mcr-glue/MCRGlue.lean` L4044 @ main | H-84 | GLUE (composite); L1: finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine open | mcr-glue | composite: Lichtenbaum 1968 Thm 2.8 with EGA II 4.5.4 (mcr-glue §3: composite of two results) |
| H-90 | `MCRGlue.FiniteQuotientExists` | `scratch/mcr-glue/MCRGlue.lean` L4057 @ main | H-84 | **LEAF**; L2: the quotient by a finite group of `ℤ_(p)`-automorphisms exists and is finite | mcr-glue; being attempted (cloud) | published form: SGA 1 Exp. V Prop. 1.8 and 1.1, special case (mcr-glue §3) |
| H-91 | `MCRGlue.TameQuotientSmooth` | `scratch/mcr-glue/MCRGlue.lean` L4072 @ main | H-84 | GLUE (composite); L3: a tame quotient of a proper smooth relative curve is proper and smooth | mcr-glue | composite: SGA 1 Exp. V, Mumford AV §7 Thm 3, EGA IV 17.5.1 (mcr-glue §3: composite of three results) |
| H-92 | `MCRGlue.SmoothModelOfP1` | `scratch/mcr-glue/MCRGlue.lean` L4086 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L4: a proper smooth `ℤ_(p)`-curve with generic fibre `P¹_ℚ` is `P¹_{ℤ_(p)}` | mcr-glue | consequence of one theorem: Liu, AGAC §8.3, §10.1 (mcr-glue §3: STANDARD; reading) |
| H-93 | `MCRGlue.TameFixedPointsDisjoint` | `scratch/mcr-glue/MCRGlue.lean` L4100 @ main | H-84 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); L5: fixed points of a tame automorphism with distinct underlying points have disjoint closures | mcr-glue | consequence of one theorem: Edixhoven 1992 Prop. 3.4 with finite étale over a DVR (mcr-glue §3: leaf consequence) |
| H-94 | `MCRGlue.TameInertiaCyclic` | `scratch/mcr-glue/MCRGlue.lean` L4119 @ main | H-84 | GLUE (composite); L6: a finite tame inertia group as in L5 is cyclic | mcr-glue | composite: Serre, Local Fields IV §2 Cor. 1 of Prop. 7, with L5's source (mcr-glue §3: composite of two results) |
| H-95 | `HDec.PropTSRed.CoverModelOfHeckeN` | `ZInQKernel/OneProof/H/TailG.lean` L743 @ main | H-84 | GLUE (project glue); the decomposition's own glue: a model of the Hecke cover of level `N` (gives `ModelYIrreducible` with T5) | mcr-quot | project glue: open here: the chain derives it only through `HeckeNoVertRam`, downstream of the coordinate that mcr-quot feeds (mcr-quot §1) |
| H-96 | `MCRQuot.P1SchemeQ` | `scratch/mcr-quot/MCRQuot.lean` L8549 @ main | H-84 | GLUE (project glue); `P¹_ℚ` exists, is proper and smooth, and represents maps to `P¹` by charts | mcr-quot | project glue: foundations: `Proj ℚ[X₀, X₁]` with its functor of points, not in Mathlib (mcr-quot §1) |
| H-97 | `MCRQuot.CMStabObj` | `scratch/mcr-quot/MCRQuot.lean` L7648 @ main | H-84 | GLUE (project glue); each CM class is fixed by a Hecke operation of order exactly 2 on classes (QM objects over `ℚ̄`) | mcr-quot | project glue: object-level glue on CM points, no schemes (mcr-quot §1) |
| H-133 | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaNullNonvanishing` | `scratch/qm-split/ThetaRatios.lean` L41 @ main | H-44 | **LEAF**; genus 2: at most one even theta-null vanishes | qm-split | published form: Mumford, Tata II IIIa §8; Igusa 1962 (qm-split §4) |
| H-134 | `HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaFourthRatiosAlgebraic` | `scratch/qm-split/ThetaRatios.lean` L58 @ main | H-44 | GLUE (composite); `θ⁴` ratios at period matrices of surfaces over number fields are algebraic | qm-split | composite: Appell–Humbert, GAGA, Thomae, Jacobi, Weil's dichotomy, or Shimura 1976 (qm-split §3) |
| H-142 | `HDec.QMSplit.Moduli.GonzalezRotgerX6` | `scratch/qm-glue/ModuliCompare.lean` L600 @ main | H-1 | **LEAF**; some coarse witness has the residue fields of CM points (`R5ptProps`) | qm-glue | published form: González–Rotger 2006 Thm 5.12 (qm-glue §4.2) |

### 4.8 Fields of leaf-fold9 introduced in r5 (4: 3 LEAF, 1 GLUE strict; 3 LEAF, 1 GLUE lenient)

Each row is a field of C4''''' and the hypothesis of a compiled theorem in the task's file (`TailZ7`, `TailZ8`:
reduct-split's `Reduction.lean` and shimura-split's `Count.lean` verbatim). `GonzalezRotgerCountX6` is projected in
both scenarios. reduct-split's three leaves are projected only in scenario F, through its splits of H-4, H-106 and
H-108; in scenario A they feed only `r7b` and `r8` (§4.10). Forms: leaf-fold9's, except `GonzalezRotgerCountX6`,
which the integrator ruled a composite: its witness carries the canonical models together with the count.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-145 | `ShimuraSplit.GonzalezRotgerCountX6` | `ZInQKernel/OneProof/H/TailZ8.lean` L44 @ main | H-114, H-115, H-116 (from H-3) | GLUE (composite); some witness of `R1fpProps`, `X6Props` (the canonical `Y₃`, `X₆` with the moduli bijection `Ψ`) has exactly `2^{inertCount6 k}·#Pic(R)` points with CM by `R` | shimura-split; field `gonzalezRotgerCountX6` of leaf-fold9 | composite: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` (audit read it) together with the canonical models it is stated on (Shimura 1967, Deligne 1971), so composite; open check: `inertCount6 k` is González–Rotger's `b(k)` (the number of primes `p ∣ 6` inert in `k`, the kernel's `p·𝒪_k` prime); reading, with the integrator's ruling (leaf-fold9 §2 lists it as a published form) |
| H-146 | `ReductSplit.SemistableReductionDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L278 @ main | H-106 | **LEAF**; SGA 7 IX 3.6 over a discrete valuation ring `O`: some finite `K' ⊆ K̄` gives `A_{K'}` semistable reduction at every place of `K'` over `O` | reduct-split; field `semistableReductionDVR` of leaf-fold9, projected only in scenario F | published form: SGA 7 I Exp. IX Thm 3.6, specialization (reduct-split §2); LEAF pending the integrator's review of the printed base ring (any discrete valuation ring, or a complete or henselian one) |
| H-147 | `ReductSplit.SemistableUnipotent` | `ZInQKernel/OneProof/H/TailZ7.lean` L253 @ main | H-4 | **LEAF**; SGA 7 IX 3.5, semistable ⇒ `(σ - 1)² = 0` on `T_ℓ A` for `σ` in inertia | reduct-split; field `semistableUnipotent` of leaf-fold9, projected only in scenario F | published form: SGA 7 I Exp. IX Prop. 3.5, the weakest reading, one `σ` at a time (reduct-split §2, §5); LEAF pending the integrator's review of the printed base ring (any discrete valuation ring, or a complete or henselian one) |
| H-148 | `ReductSplit.NeronSchemeModelExistsDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L238 @ main | H-4, H-106, H-108 | **LEAF**; Néron's existence theorem over a discrete valuation ring, scheme form | reduct-split; field `neronSchemeModelExistsDVR` of leaf-fold9, projected only in scenario F | published form: BLR §1.4 Thm 3 with §1.2 Def. 1 (reduct-split §2); LEAF pending the integrator's review of the printed base ring (any discrete valuation ring, or a complete or henselian one) |

### 4.9 Props open only in scenario F, introduced in r5 (19: 4 LEAF, 15 GLUE strict; 13 LEAF, 6 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''. Its form is the task
report's label, or my reading where the report's own text names more than one source or gives no label; the
pointer says which.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-149 | `HDec.QMSplit.Moduli.DeligneComponentsX6` | `scratch/shimura-split/Rows.lean` L4297 @ main | H-137, H-140 (from H-1) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some witness of the moduli clause lists has `X₆ ×_ℚ ℚ̄` connected | shimura-split | consequence of one theorem: Deligne, Sém. Bourbaki 389 §§2-3, PSPM 33 2.6.3: `π₀` at level `𝒪̂^×` with `nrd(𝒪̂^×) = ℤ̂^×` (shimura-split §2, §3.2) |
| H-150 | `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` | `scratch/shimura-split/Rows.lean` L4287 @ main | H-140 (from H-1) | **LEAF**; a proper `X → Spec k` with `X ×_k k̄` connected is geometrically connected | shimura-split | published form: EGA IV₂ 4.5.1-4.5.2; Stacks 0389, weakened by `IsProper` and characteristic 0 (shimura-split §2, §3.2) |
| H-151 | `HDec.QMSplit.Moduli.BabaGranathX6'` | `scratch/shimura-split/Rows.lean` L4246 @ main | H-141 (from H-1) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some coarse witness carries `π₆ : X₆ → P¹` with the fibre and CM clauses (the surjectivity clause of `BabaGranathX6` is proved) | shimura-split | consequence of one theorem: Baba–Granath 2008 Thm 2.1 with Lemma 3.1 and the §3.1 table (audit YES; shimura-split §2, §3.2) |
| H-152 | `HDec.QMSplit.Moduli.ReciprocityCanonical` | `scratch/shimura-split/Rows.lean` L4134 @ main | H-138 (from H-1) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some fine witness has `R1recProps`: residue fields of the three elliptic CM points unramified above 5 | shimura-split | consequence of one theorem: Shimura 1967 Main Thm II, Deligne 1971 §3: the unramified-above-5 conclusion follows from reciprocity (shimura-split §2, §3.2) |
| H-153 | `HDec.QMSplit.Moduli.ElkiesConicX6` | `scratch/shimura-split/Rows.lean` L4337 @ main | H-143 (from H-43) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some witness carries `π₆` with the fibre and CM clauses and the conic model `Y² + 3X² + 3Z² = 0` of `X₆`, without the row's Hecke, CM-existence, reciprocity, surjectivity and González–Rotger clauses | shimura-split | consequence of one theorem: Elkies 1998 §3 (the coordinate `t` on `X*(6)`), Kurihara 1979 as a check (shimura-split §2) |
| H-154 | `HDec.QMSplit.Moduli.ShimuraHolFamily` | `scratch/shimura-split/ShimuraFam.lean` L258 @ main | H-139 (from H-20) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); one holomorphic family `φ : ℍ → Y₃(ℂ)` with the moduli clause; the step to every `π : Y₃ → P¹` is proved | shimura-split | consequence of one theorem: Shimura 1967 Main Thm I, through Deligne 1971 §4 for the `ℚ`-model (shimura-split §3.4 and its review §7) |
| H-155 | `ShimuraSplit.DeligneComponentsY3` | `scratch/shimura-split/Rows.lean` L3643 @ main | H-59 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); `π₀(Y₃ ×_ℚ ℚ̄) ≃ (ℤ/3)^×` with `σ` acting through the mod-3 cyclotomic character; the orbit computation is proved | shimura-split | consequence of one theorem: Deligne, Sém. Bourbaki 389 §§2-3, PSPM 33 2.6.3; the computation of `nrd(K₃)` is not formalized (shimura-split §2, §3.5) |
| H-156 | `ModularSplit.DimJac.H0DifferentialsEqHolo` | `scratch/modular-split/DimJac.lean` L45 @ main | H-78 | GLUE (project glue); `dim_ℚ H⁰(X, Ω¹_{X/ℚ})` is the genus of the function field (Chevalley's definition) | modular-split | project glue: textbook sheaf theory over genuine definitions, Hartshorne II.8, II.6.7, II.4.7; no literature leaf is left (modular-split §2, §3) |
| H-157 | `ModularSplit.R17.CarayolRealization` | `scratch/modular-split/R17.lean` L127 @ main | H-21 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform has conductor exponent `v_p(N)` at every `p ≠ ℓ`; the transport to every attached `ρ` is proved | modular-split | consequence of one theorem: Carayol 1986 Thm (A) at his realization (audit), with Casselman's `a(π_p) = v_p(N)` and Ribet's irreducibility (modular-split §2: still a consequence) |
| H-158 | `ModularSplit.EigenHT.KatoRealizationCoh` | `scratch/modular-split/EigenHT.lean` L156 @ main | H-127 (from H-10) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some irreducible `ρ` whose geometric Frobenius has trace `a_p`, with Hodge–Tate weights `{0, k−1}` (Kato's normalization) | modular-split | consequence of one theorem: Kato 2004 §§9.2-9.4 at `V_f` with Ribet's irreducibility (modular-split §2: still a consequence) |
| H-159 | `ModularSplit.EigenHT.HTDual` | `scratch/modular-split/EigenHT.lean` L140 @ main | H-127 (from H-10) | GLUE (project glue); the contragredient of a Hodge–Tate representation is Hodge–Tate with the negated weights | modular-split | project glue: a named glue from Tate's `H⁰(G, ℂ_ℓ(i))`, the bundle's `TateTwistInvariants` (modular-split §3; reading: the report calls it a named glue) |
| H-160 | `ReductSplit.RaynaudSemistable` | `ZInQKernel/OneProof/H/TailZ7.lean` L265 @ main | H-4 | **LEAF**; `m ≥ 3` invertible in `O` and `A[m]` rational over `K` ⇒ every Néron model over `O` is semistable | reduct-split | published form: SGA 7 I Exp. IX Prop. 4.7 (reduct-split §2; §5: may be printed over a strictly henselian base) |
| H-161 | `ReductSplit.FixedTorsionRationalImperfect` | `ZInQKernel/OneProof/H/TailZ7.lean` L1179 @ main | H-4 | GLUE (project glue); over an imperfect `K`, a Galois-fixed point of `A(K̄)[m]` is `K`-rational (the perfect case is proved) | reduct-split | project glue: needs `A[m]` étale (from the bundle's `mulEtaleAbelianScheme`, leaf-fold9 §5); only imperfect `K` need it, and the project uses characteristic 0 (reduct-split §1) |
| H-162 | `ReductSplit.SemistablePersistsDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L710 @ main | H-106, H-108 | **LEAF**; semistable reduction at `O` persists to `A_{K'}` at every `O'` over `O` | reduct-split | published form: SGA 7 I Exp. IX Prop. 3.3, first assertion, finite extensions (reduct-split §2) |
| H-163 | `ReductSplit.SemistableLocalGlobal` | `ZInQKernel/OneProof/H/TailZ7.lean` L736 @ main | H-106, H-107, H-108 | GLUE (project glue); height-split's `IsSemistable 𝒩` over `𝓞_L` iff semistable reduction at every discrete valuation ring of `L` | reduct-split | project glue: local-to-global algebraic geometry (reduct-split §1, §2) |
| H-164 | `ReductSplit.SemistableAlmostAll` | `ZInQKernel/OneProof/H/TailZ7.lean` L749 @ main | H-106 | GLUE (project glue); semistable reduction at all but finitely many discrete valuation rings of `K` | reduct-split | project glue: spreading out with the bundle's `egaIV_8_10_5_xii` (reduct-split §1, §2) |
| H-165 | `ReductSplit.IdentityComponentBaseChangeDVR` | `ZInQKernel/OneProof/H/TailZ7.lean` L962 @ main | H-107 | **LEAF**; `𝒩⁰ ×_O O' → 𝒩'` is an open immersion in the semistable case | reduct-split | published form: SGA 7 I Exp. IX Prop. 3.3, second assertion, weakened (reduct-split §2) |
| H-166 | `ReductSplit.SemistableNeronBaseChangeLocalGlobal` | `ZInQKernel/OneProof/H/TailZ7.lean` L988 @ main | H-107 | GLUE (project glue); SS2 over `𝓞_L → 𝓞_{L'}` from the local SGA 7 IX 3.3 | reduct-split | project glue: carries the global content of SS2: identity components over the Dedekind base, gluing (reduct-split §2) |
| H-167 | `ZInQ.HeightSplit.FaltingsLemma5` | `ZInQKernel/OneProof/H/TailY.lean` L560 @ main | H-111 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Faltings' Lemma 5 in the semistable inequality form, over the field of the Néron models | reduct-split | consequence of one theorem: Faltings 1983 Lemma 5 with Raynaud, Astérisque 127 VII Cor. 2.1.3 (reduct-split §2: still a consequence; the base change to every `L ⊇ K` is proved) |

### 4.10 Bundle fields never projected (not on the list)

r5: `r3 : ZInQ.LeafPush2.R03_LinYang`, `t10 : T10Etale.T10_TateDuality` and reduct-split's four leaves
`serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `neronSchemeModelExistsDVR`. In OneProof/H the four
are used only in `TailZ9`'s `researchLeaves8_of_open9`, as arguments of `serreTatePotentialGood_final` and
`grothendieckMonodromy_final'`, which fill leaf-fold8's never-projected `r7b` and `r8`; in `TailZ5`-`TailZ9`, `r3` and
`t10` occur only as `r3 := r.r3` and `t10 := t.t10` (VERIFIED, grep at main), and below `TailZ5` as in r4. Scenario F
uses three of the four (§4.8; `chain.py F` recomputes the set). The integrator has approved removing all six after
leaf-fold10. `r1rec` and `r5` left the list of unused fields: leaf-fold9 proves them from `r1r2`.

Until r4 the six were `r1rec`, `r3`, `r5`, `r7b`, `r8` and `t10`:
`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t10 : T10Etale.T10_TateDuality`. VERIFIED (agent-h-leaves and my grep) for
g0-assemble3's flat file: they occur only in the structure literals that convert the bundles (and `t10` only in the
unused `HSyn.TextbookLeaves.t10_groupIso`); C4 converts its bundles to g0-assemble3's and uses the same consumers
(REPORTED by assemble-port's report; not re-grepped, its flat file has more conversions). assemble-port already deleted
the unused textbook fields T1, T3, T4 (as textbook fields), T16(b), T20, T21, T28, T29.
r2-r4: in leaf-fold4's and leaf-fold5's flat files `r1rec`, `r7b`, `r8` occur only as `f := r.f` in three structure literals, and `t10` only
there and in `T10_groupIso_of_tateDuality` (VERIFIED, grep of `Leaves4.lean` @ 9dcf1ca8 and `Leaves5.lean` @ 5a7e03d1); `r3` and `r5` were not
re-grepped (their names collide with local variables).
r4: leaf-fold8 keeps the six (`r1rec`, `r3`, `r5`, `r7b`, `r8` in `OpenResearchLeaves8`, `t10` in `OpenTextbookLeaves8`). In
OneProof/H they occur only as `f := r.f` or `f := t.f`, or a transport `_ofK5` of it, in the bundle conversions of
`TailD`, `TailE`, `TailI`, `TailK`, `TailN`, `TailO` and `TailX`, and `t10` in LPrefix's `T10_groupIso_of_tateDuality`
(VERIFIED, grep at main); leaf-fold7 and leaf-fold8 left the chain from LPrefix to TailO unchanged.

### 4.11 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 and r5 tasks)

leaf-review-a (groups A, A′, F: 21 fields) and leaf-review-b (groups B, C, D, E, G: 41 fields) read every leaf-fold3
field with the definitions it uses: 8 PUBLISHED-FORM (`t11b`, `serreRigidity3`, `r7a`, `t41`, `r9a`, `r9b`, `r19`, `t33`),
54 CONSEQUENCE, none STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT; no statement repair proposed. Since r3 the
form column carries their verdicts: a CONSEQUENCE is a consequence of one theorem or a composite, with the review's
derivation named, and is GLUE in the strict count until that derivation is compiled. leafq-check (r3) checked
leaf-fold4's seven LEAF? fields: `GammaStarGen` proved, three replaced by smaller statements (H-86..H-88), and
`ThetaRatiosAlgebraic`, `X6ConicModel`, `Y3Connected` unchanged (true, each a consequence of published results, not
splittable in Lean today). Premises the reviews flag across rows: Lemma QP (its existence half may be glue), the
specialization of Deligne's PEL model to `R1fpProps` (an open human check, inherited by `r1r2`, `r1b`, `y3Connected`,
`x6ConicModel`), and the definition of `stableFaltingsHeight` (group D).

The r4 split tasks each checked their rows against the sources they could read, and none found a row false, vacuous
or stronger than its sources. height-split, mcr-glue and height-glue add an independent model review of their new
statements (no defect; height-glue's RISKs: `QMUniformizationC` bundles the algebraicity of QM tori, GAGA and the
unpolarized form with the published moduli statements, and `CMDescent` bundles the classification of endomorphism
algebras). tyz-split read TYZ's source and settled tyz-35's three HUMAN CHECK items; the `[i]` sign of the base point,
the one input it left unprinted, was found printed later (`α = −i` in the proof of the Hecke action, about
Period7.tex L1564-1566). Flags kept in the form column: `PazukiCor13Upper` is half of Pazuki's corollary, and the
comparison of normalizations is in height-split §3; `EichlerOptimalEmbeddingCount` may be printed modulo `𝒪¹`; Igusa
prints `ψ₄`, `χ₁₀` as identities of Eisenstein series; `CanonicalModelY3`, `ShimuraFamily` and `CanonicalCoarseX6`
keep the Lemma QP caveat.

The r5 split tasks checked their rows against the sources they could read (reduct-split could read none of its
sources, so its locators are UNVERIFIED); none reports a row false or vacuous. shimura-split's independent review
found `GonzalezRotgerCountX6` OK, and Eichler's count gives 2, 2, 2 points at discriminants −4, −3, −24, matching the
conic model's fibres (REPORTED, leaf-fold9 §1.1); the open check is that the kernel's `inertCount6 k` (`p·𝒪_k` prime
for `p = 2, 3`) is González–Rotger's `b(k)`. reduct-split's reading risks: SGA 7 IX 4.7 may be printed over a strictly
henselian base (`RaynaudSemistable`), and Serre–Tate Thm 2 for a complete `K` (`SerreTateThm2`, never projected); its
leaves count as published forms pending the integrator's review of the printed base ring. modular-split's two
realization leaves are consequences: Carayol's and Kato's objects cannot be defined in Mathlib. tyz-split's T-12
passed a clause-by-clause statement review: TYZ Theorem 3.3 or weaker, carried along the kernel's eta model (§3.2).

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 69 open nodes = the
30 + 18 + 14 + 1 = 63 fields of C4'''''s four bundles (each expanded from the structure as read at main) plus the 6
TYZ and GZ hypotheses of the top: the hypothesis list of the composite of C2, T0 with T0', and C4''''', 63 of them
projected (§4.10). With leaf-fold9's forms for the fields (`GonzalezRotgerCountX6` a composite) and this report's for
the top, the projected 63 are 39 LEAF and 24 GLUE strict, 49 and 14 lenient; all 69 are 43 LEAF and 26 GLUE strict,
54 and 15 lenient. `chain.py onep`: its hypotheses are scenario A's (the four bundles and the six top Props), and leaf-fold9's `fields9.tsv` lists the bundles' fields with the same names and types (the table abbreviates `bdRInvariants`'s binders).

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 165 theorem edges in the file (30 followed on the
route); 87 open nodes = the 84 of §0 + the 3 never-projected fields. Where a followed edge's file is not the H base,
the check compares the Prop it proves with the one the route uses (`defcheck`):
- `CoordinateNormalization`: identical.
- `CoordinateFromSections`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `TorsionStructure`: the kernel's own constant (ZInQKernel/HDecomp/Objects.lean), which OneProof/H imports.
- `FibreAutTame`: identical.
- `CurveBijIso`: identical.
- `CMSectionsDisjoint`: identical (vs scratch/mcr-glue/MCRGlue.lean, which takes it).
- `GenericQuotientP1`: identical.
The F-only edges in library files outside OneProof/H (shimura-split, modular-split, tyz-split's T-5 split) prove the
library's own constants: each file imports ZInQKernel modules, has no definition of the Prop it proves, and imports
the module that defines it, which `OneProof/Main.lean` imports too (`worldcheck`):
- `ShimuraReciprocityModFn` (`scratch/tyz-split/T5.lean`): defined in `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean`.
- `Y3Connected` (`scratch/shimura-split/Rows.lean`): defined in `ZInQKernel/OneProof/H/TailG.lean`.
- `X6ConicModel` (`scratch/shimura-split/Rows.lean`): defined in `ZInQKernel/OneProof/H/TailE.lean`.
- `R1R2fpRep` (`scratch/shimura-split/Rows.lean`): defined in `ZInQKernel/OneProof/H/LPrefix.lean`.
- `DimJacobianEqGenus` (`scratch/modular-split/DimJac.lean`): defined in `ZInQKernel/Contrib/CurvesG/GenusSplit.lean`.
- `CarayolR17'` (`scratch/modular-split/R17.lean`): defined in `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
- `EigenformHTNew` (`scratch/modular-split/EigenHT.lean`): defined in `ZInQKernel/OneProof/H/TailS.lean`.
- `ShimuraFamily` (`scratch/shimura-split/ShimuraFam.lean`): defined in `ZInQKernel/OneProof/H/TailU.lean`.
The fields that cloud-w07 proved are inside C4''''' now, so `rootcheck` has nothing to check.
For the files over leaf-fold4's chain (`import TailK`, qm-split's H-44 split here), the definitions of the chain Props
their followed edges use are identical in the H base and in leaf-fold4's sources (`chaincheck`):
`ThetaRatiosAlgebraic` identical (OneProof/H vs leaf-fold4's chain).
Each F-only row's definition (the file in its row) is identical to the definition in the file of every followed edge
that takes it and has its own copy (9 comparisons; 1 more edge imports the Prop instead).
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's and shimura-split's T5 is the kernel's
`ObjBridge.TorsionStructure` or `PkgI2.TorsionStructure.{0}`, which `Objects.lean` proves equal by `Iff.rfl`
(`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set minus the
never-projected fields: 84 rows with 84 distinct heads, equal to the F open set minus the never-projected fields.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold9's bundles since w60, T0' since w59): scenario A as one library
  theorem (§1).
- **C4''''', leaf-fold9** (cf6914e1, in w60): 30 + 18 + 14 + 1 fields inside OneProof (`TailZ5`-`TailZ9` over
  leaf-fold8's `TailY`-`TailZ4` and leaf-fold7's `TailP`-`TailX`); lake build and axioms REPORTED.
- **The top in the kernel**: C2 (atkin-li) and tyz-chain's T0, with T0' (tyz-split) in `OneProof/TYZSplit.lean`.
- Superseded: C4'''' (leaf-fold8), C4''' (leaf-fold6), C4'' (leaf-fold5), C4' (leaf-fold4), C4 (assemble-port) and
  the variants listed in r2.

### 6.2 What folding scenario F into C4''''' needs
leaf-fold7 to leaf-fold9 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold9 §5). Under that rule, with leaf-fold9's
counts (REPORTED, its §5):
- shimura-split: `y3Connected` → `DeligneComponentsY3` is strict 0, lenient −1 (a candidate if composite →
  consequence is accepted); `shimuraFamily` and `x6ConicModel` are neutral; `r1r2` → its printed parts is strict +2;
- modular-split: `dimJacobianEqGenus` → `H0DifferentialsEqHolo` removes the last literature but lowers neither
  count; `r17` is neutral; `eigenformHTNew` is strict +1;
- reduct-split: `r6` is strict 0, lenient +1 (strict −1 once `FixedTorsionRationalImperfect` is proved from
  `mulEtaleAbelianScheme`); SS1 and SS3 are strict 0, lenient +2; SS2 is strict +1; `faltingsLemma5BC` is neutral;
- H-44 and the coordinate stay out: one field becomes a leaf plus smaller statements, and under the coordinate one
  glue field becomes three glue Props with mcr-glue's six leaves.
SPECULATIVE until compiled.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A. Each F edge removes or replaces a field once
folded; B6 would change its TYZ hypothesis `hS` to `CMModuli` and `X0RatStructure`.

## 7. Findings

**Refresh r5 (2026-11-14).**

1. **1 row proved, 14 split, 3 off the route, 1 dropped** (§0, §4.1). The 23 new rows are 7 published forms, 9
   consequences of one theorem, 1 composite and 6 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold9: 69 hypotheses,
   63 used by its proof (39 LEAF and 24 GLUE strict, 49 and 14 lenient). `chain.py onep` reads its hypotheses from
   `Main.lean` and finds scenario A's.
3. **H-43 had not been reduced in r4.** qm-glue's `ConicCanonical` is `X6Kummer.X6ConicModel` verbatim (shimura-split,
   `Iff.rfl`), so r4's F route for H-43 was a renaming; scenario F now takes H-43 from shimura-split's smaller leaf
   `ElkiesConicX6`, with `r1r2` and T5.
4. **Forms.** `GonzalezRotgerCountX6` (the new field under `r5count`) counts as a composite, by the integrator's ruling
   and my reading of its existential witness (leaf-fold9 lists it as a published form); open check: `inertCount6` is
   González–Rotger's `b`. reduct-split's three leaves on the list are published forms pending the review of the
   printed base ring (§0 gives the count without them). modular-split's `HTDual`, which the report calls a named glue,
   counts as project glue.
5. **Project glue** is 9 Props: the coordinate's three, reduct-split's four (local-to-global steps, and
   `FixedTorsionRationalImperfect`, which only imperfect fields need), and modular-split's `H0DifferentialsEqHolo`
   (the last step of `dimJacobianEqGenus`, no literature left) and `HTDual`.
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-79 (no
   `Γ₁(N)\ℍ*` in Lean), H-13 (`r16`, modular-split §4.1), `ShimuraGoodReductionNoGuard` (abelian schemes over a base),
   `T10_TateDuality` (never projected; reduct-split §4).
7. **chain.py**: the H base is leaf-fold9 (bundles in `TailZ9`, `TailZ4`, `TailX`); a declaration can be picked by
   occurrence (`nth`); `USED_IN_F` is recomputed; `worldcheck` checks that the library files of shimura-split and
   modular-split prove the library's own constants.

**Refresh r4** (unchanged):

1. **10 rows proved, 39 split** (§0, §4.1). The new rows are 35 published forms, 13 consequences of one theorem,
   8 composites and 3 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, with 66 used hypotheses: 41 LEAF and
   25 GLUE strict, 52 and 14 lenient. `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's.
3. **T-11 is a published form and compiled**: TYZ Theorem 3.3 as printed (Period7.tex read by tyz-split), restricted
   to `n ≡ 5, 7 (mod 8)`; leaf-fold8 put tyz-split's derivation of the pinned form into OneProof. T-5 stays GLUE: no
   printed form of Shimura reciprocity can be stated over Lean's definitions today, and the split gives a CM part (a
   consequence of Shimura Thm 5.4) and a modular-curve part.
4. **Forms.** A field of C4'''' has leaf-fold8's form (its §2): SS1, SS2, SS3 and `FaltingsLemma5BC` are
   consequences (height-split's own caveats and review), `JavanpeykarBound` and `IgusaCMValue24` published forms, and
   Igusa's `ψ₄`, `χ₁₀` published forms with qm-split's flag. Four F-only leaves of height-glue and qm-glue whose own
   docstrings or reviews name more than one source are counted by my reading, not as published forms: `CMDescent` and
   `ConicCanonical` (consequences), `QMUniformizationC` and `CanonicalCoarseX6` (composites).
5. **The project glue left is under the coordinate**: `QuotientP1Coordinate` in scenario A; in scenario F,
   `P1SchemeQ`,
   `CMStabObj` and the decomposition's `CoverModelOfHeckeN` (§4.1: counted open, since the chain derives it only
   downstream of the coordinate).
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-78
   (`H¹(X, 𝒪_X)` on schemes), H-79 (no `Γ₁(N)\ℍ*` in Lean; its consumers could use Riemann–Hurwitz instead, curve-split
   §3.5), `ShimuraGoodReductionNoGuard` (abelian schemes over a base), `EigenformHTNew` (Kato's objects), H-59
   (`Y3Connected`: qm-glue reads it as the existential statement about the canonical model itself).
7. **chain.py**: the H base is read from OneProof/H at main; the def check tells the kernel's own constants (which
   OneProof/H imports) from copies and compares Props an F edge introduces with the files that take them; new checks
   for the files over leaf-fold4's `TailK` and for `_root_` kernel fields; `onep` compares the library theorem with
   scenario A and leaf-fold8's field table; a block ends at the next docstring; binders a consumer quantifies over
   can be listed (`bound`).

**Refresh r3** (unchanged):

1. **Form column and two counts** (the integrator's ruling): 17 published-form rows are LEAF in both counts; 24
   consequences of one theorem are LEAF only in the lenient count. Each names the derivation to compile.
2. **The TYZ premise is four Props in the kernel** (tyz-chain): `TYZThm11Integral` (published form), `TYZLemma29Mod2`,
   the CM leaf and `TYZThm33Pinned` (composites); `TYZLcalOne`, `Lemma321Five`, `Lemma318Literal`, `Thm35First` and
   `SqrtTwoNotInHHprime` are proved or reduced in kernel modules.
3. **leaf-fold5 compiles r2's H list**, except that it keeps av-b1's glue `SimpleImageIsogeny` (the frontier splits it
   into H-73, H-74 again; leaf-fold5 §1.3 gives the variant with T8 kept as a leaf, 69 Props with one glue).
4. **leafq-check** proves `GammaStarGen` and replaces three LEAF? fields by smaller statements (H-86..H-88).

**Refresh r2 and the 17:35 report** (unchanged):


1. **leaf-fold4 compiles the 17:35 frontier.** Scenario A's 69 projected Props are the 17:35 list minus
   `DivisiblePoints` (VERIFIED by chain.py). What was a textual composite of branch results at 17:35 is now one compiled
   theorem.
2. **Fork main carried the 11:21 version of this report** (79 open) until integration w51 merged wip/frontier d8c95123
   at 22:32. The upstream issues had been built from wip/frontier 249195fd, whose rows equal the 17:35 list.
3. **The statement reviews and this report's classes differ on five open rows** (H-3, H-16, H-21, H-25, H-38; §4.7).
4. **Reductions recorded but not folded.** tyz-318 reduces the LEAF T-4 to the GLUE `SqrtTwoNotInHHprime` (TYZ's Step 3)
   and proves T-4 outright when `n` is the only divisor `≡ 5 (mod 8)`; sqrt2-glue works on the rest. shimura-modfn
   splits the CM leaf T-5 but recommends keeping it: at Heegner points where the plane model `(j, j_N)` is singular,
   `j(τ)` and `j(Nτ)` do not determine `g(τ)` (its example `Q = [32,10,1]`, `D = −28`, numerically VERIFIED there).
5. **chain.py repair.** The 17:35 script read ts-kummer at d9c06585, which is not on the fork; r2 reads ts-kummer's final
   1bbe3543, which has the same six theorems. Those edges are off the route since C4'.
6. **av-b1's head 02ae2421 is an unchecked snapshot** from a host shutdown; r2 uses av-b1's files as merged into main.

**From the 17:35 report** (unchanged; for item 1, T3, T6-T9, T11(b), T26, T34, T38 and T41 are now proved or reduced,
and the open textbook rows are those of §4.3 and §4.5):

1. **The brief's "every textbook leaf T1-T32 is proved" is false** (VERIFIED: agent grep of the 150 newest refs, my grep
   of 80 refs for six of the Props). Proved: T2, T14(a′), T14(b′), T15, T16(a), T17, T18, T20, T21, T25, T28, T31 (and
   T36, T37 inside `x1`). Open: T1, T3, T4, T5, T6, T7, T8, T9, T10, T11(a), T11(b), T16(b), T23, T24, T26, T27, T29(a),
   T29(b); of these T1, T10, T16(b), T29 are never used. Since 12:45, T26 follows from T5 (t5-torsion), so T26 is no
   longer on the list.
2. **`GluePieces4.tateRamAtThree` is likely false as stated** (linked-ram finding F1, SPECULATIVE there): it is not
   quantified over `G7Data`, so g0-assemble3's `[L:ℚ] ≤ D` fix does not reach it. If so, g0-assemble3's
   `sixContactMin_of_leaves4` is vacuous. C4 (assemble-port) replaces it by linked-ram's `UnramTate.TateRamAtThreeD`
   (adds `Module.finrank ℚ L ≤ ZInQ.heightD`), which is proved there; route T does not need it either.
3. **Stale status texts.** STATUS.md and README say `HeckeThetaNewform` is "reduced to Atkin–Li"; it is proved
   (atkin-li, now on fork main w45). h-decomposition §2.2 on main marks T14, T28, T36, T37 open (proved) and lists T39
   as a leaf (it follows from T40). g0-assemble3's docstrings call `heckeIrreducible` "truth SPECULATIVE" (settled by
   ts-hecke) and its §6 misses the unused fields `r1rec, r3, r4, r5, r7b, r8, t10`. cm-numeric's report still lists
   `IInH4`, `HprimeNormal`, `GenusFieldLeLni` as leaves (all proved). The reports of ts-kummer and prop-ts-glue still call
   `KummerCompositum` open (kummer-comp's note). assemble-port's LEAF/GLUE labels are not the strict ones (§6.1).
4. **TYZ.** `CMNumeric.tyzZ` and `CMBridge.tyzZ` are two constants with the same body (an integration must keep one; T-6
   is stated at `CMBridge.tyzZ`). T-6, T-7 and the CM leaf are stated through the eta model `X0.phiC`; x0-32's eta
   leaves `EtaModelInvariant`, `EtaModelFricke` are now proved (tyz-cm), but the identification of `X0.phiC` with the
   modular parametrization also rests on x0-32's analytic-model statements, which are not hypotheses of the chain.
5. **Name collisions to resolve when folding**: three structures named `GluePieces5` (cpts-transport, linked-ram,
   assemble-port) and two named `HSyn.GluePieces4` (g0-assemble3, lt-goodred); `WeilPairing.IsogenyQuasiInverse` vs
   `HSyn.G0RevIsog.IsogenyQuasiInverse`; `PropTSGlue.propTSAll_final'` (prop-ts-glue vs ts-sn).
6. **Statement changes proposed here: none.** (Finding 2 is linked-ram's proposal, adopted by assemble-port; gz-decomp's
   `GrossZagierCd` and gz-statements' restricted GZ leaves are on record.)

## 8. Tasks (snapshot 2026-11-14 13:20 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r5: leaf-fold9 (cf6914e1), shimura-split (e80361ee), reduct-split (a4fca6ae),
modular-split (cfcac8bc), and tyz-split's statement review (wip/w61 3c241950). Used in r4 and compiled inside C4'''''
or applied by scenario F: leaf-fold8, mcr-quot, coarse-factor, cloud-w07 (fork PR #11), leaf-fold7, height-glue,
qm-glue, leaf-fold6, mcr-glue, av-glue, av-split, height-split, curve-split, hodge-split, qm-split, tyz-split, fork
PRs #6-#10 (heads in the r4 section of `refs.txt`). Used in r3 and compiled inside C4''''': leaf-fold5, leafq-check,
tyz-chain and the r2 tasks. Read, not folded: leaf-review-a, leaf-review-b. Being attempted: cloud workers W11-W15
(§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (Contrib modules `ZInQKernel/Contrib/GZStatements/{Weak,Level,Compat,Hensel}.lean` on its branch) proves
that the narrower `ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`,
`D < −4`) are implied by Z-1, Z-2 and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`); they could replace Z-1, Z-2
(both remain GLUE). Not adopted here (not compiled together with `TYZChain.lean`).

This branch is integration w60 plus this refresh.

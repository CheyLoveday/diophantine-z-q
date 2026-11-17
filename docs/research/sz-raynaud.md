# sz-raynaud: the two SGA 7 rows on the manuscript's route (diophantine_zq.tex L814-818)

Task sz-raynaud (2026-11-17), base wip/ga-rigidity (f9e83fdb), no other branch merged.

## 1. Result

**Verdict.** The two rows (`sga7_IX_Cor3_3`, now with leaf `SGA7_IX_Cor3_3_Def34`, and
`sga7_IX_3_5_ForwardGeom`, with leaf `SGA7_IX_3_5_ForwardGeom_Def34`) **have no counterpart on the manuscript's
route at L814-818, and neither can be proved from it.** The manuscript's two steps there are:

1. Raynaud's criterion as cited, `\cite[Theorem 3.5]{silverbergzarhin}`, giving semistable reduction over
   `F = L_v(A[3])` (`A[5]` if `p = 3`) directly. There is no base change and no strict henselization.
2. The next sentence, with no citation (**ELLIOT**): "Its wild inertia acts trivially on each `V_ℓ(A)` with
   `ℓ ≠ p`."

What the rows feed, traced in the tree (§3):
- **`sga7_IX_Cor3_3`** (SGA 7 IX Cor. 3.3: the identity component commutes with base change) feeds only SS2/SS3,
  i.e. semistability persists under base change. Those are used to compute Faltings heights on Néron models over a
  common semistable field (`r20_of_leaves'`, Faltings' Lemma 5 for base changes). That is a different part of the
  proof, not L814-818. The manuscript gets semistability over `F` from the criterion itself, so the row has no
  counterpart there.
- **`sga7_IX_3_5_ForwardGeom`** (SGA 7 IX Prop. 3.5: semistable ⇒ `(σ−1)² = 0` on `T_ℓ` for every inertia
  element) feeds r6 (`PkgI2.RaynaudCriterionNF`). r6 is used in two places:
  - D2 (L814-818), in three proofs: `torsFix_of_descent`, `localGlue_of_descent`, and lt-local's
    `linkedTateLocal`, which reaches D2 through `localGlue_at`. Here the manuscript uses only the weaker ELLIOT
    sentence (wild inertia acts trivially).
  - A6 (`qmModelG3_of`: good reduction of a QM surface away from 3, the kernel's Raynaud route; the manuscript
    instead gets good reduction from the proper model and its universal abelian scheme, L529-530).

  The ELLIOT sentence follows from the row with on-the-spot glue (proved below, `elliot_of_semistableUnipotent`).
  The converse fails: wild-inertia triviality says nothing about tame inertia. So the manuscript's route gives
  D2 but not the row.

**What the route gives in their place, proved in Lean** (`ZInQKernel/Contrib/OneProof/SZRaynaud.lean`, namespace
`SZRaynaud`; no `sorry`, standard axioms only; compile status in §5):

| new statement | kind | what it is |
| --- | --- | --- |
| `SilverbergZarhinThm35` | LEAF candidate, **GLUE until read** (published, flag "pending reading: …") | Raynaud's criterion as Silverberg–Zarhin Thm 3.5 states it, as the manuscript cites it; over any DVR; `m ≥ 3` invertible; `A[m]` rational; conclusion: semistable reduction under either extension reading |
| `ElliotWildInertiaTrivial` | ELLIOT (consequence, flag "ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818) …") | semistable reduction ⇒ every wild inertia element acts trivially on `T_ℓ(A)`, `ℓ` invertible |
| `IsWildInertia` | definition | `v_w(σx − x) > v_w(x)` for all `x ≠ 0` (the first ramification group; the valuation-ring form of the kernel's `wildSet`) |
| `raynaudSemistable_of_sz35` | proved | `SZ35 → ReductSplit.RaynaudSemistable`: the kernel's Raynaud criterion over **every** DVR, with no strict henselization, no `StrictHenselizationPair` and no base change |
| `raynaudSemistableSHOr_of_sz35` | proved | `SZ35 → DictModels.RaynaudOr.RaynaudSemistableSHOr`, the bundle field (SGA 7 IX 4.7), statement unchanged |
| `RaynaudWildNF`, `raynaudWildNF_of_leaves` | proved | **L814-818 in Lean**: in r6's objects, `A[m]` Galois-fixed (`m ≥ 3` invertible) ⇒ every wild inertia element fixes `A(K̄)[ℓⁿ]`; from SZ35 + ELLIOT + the Néron field at number fields (as r6's own proof) and proved glue |
| `elliot_of_semistableUnipotent` | proved | ELLIOT from SGA 7 IX 3.5 (`SemistableUnipotent`, what the ForwardGeom row gives) + the on-the-spot glue `WildPeriodCoprime` (wild inertia is pro-`p`) |
| `SilverbergZarhinThm35Def34`, `ElliotWildInertiaTrivialDef34`, `raynaudWildNF_of_def34` | variants, proved composite | the reading-robust pair if Silverberg–Zarhin define semistability by "no unipotent part" (`GaRigidity.SGA7.IsSemistableDef34`); the composite uses ga-rigidity's `isSemistableDef34_of_isSemistable` |

**Fold.** Only one bundle field is discharged on the manuscript's route: **`raynaudSemistableSHOr`** (SGA 7 IX 4.7,
LEAF since the 11-17 reading), by `raynaudSemistableSHOr_of_sz35` from the new leaf `SilverbergZarhinThm35`. That
trades a LEAF row (SGA 7, not cited by the manuscript) for a GLUE row (Silverberg–Zarhin, cited, but pending
reading). So the strict count rises by one, and the strict autofold refuses the fold without `--allow-rise`. Per
the owner's ruling ("re-route to Elliot"), this is the re-route; **the lead decides** whether to fold it now or
after a reading of Silverberg–Zarhin p. 406 clears the flag (§4). The ELLIOT leaf discharges no current field:
r6 is still needed by A6.

## 2. The manuscript's text (read)

- L814-818 (read): at `p`, `F = L_v` with `A[3]` adjoined (`A[5]` if `p = 3`), degree `≤ DG₀` over `ℚ_p`;
  "Raynaud's criterion `\cite[Theorem 3.5]{silverbergzarhin}` gives semistable reduction there"; then the uncited
  sentence on wild inertia and `V_ℓ(A)`, `ℓ ≠ p`. L819-821 then use the break bound for the upper numbering.
  VERIFIED (read).
- Bibliography L11077-11080: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), 403-420, Theorem 3.5. VERIFIED.
- `grep` for `SGA`, `sga7`, `grothendieck` in diophantine_zq.tex: no hit. **SGA 7 is cited nowhere in the
  manuscript.** Silverberg–Zarhin is cited only at L816. VERIFIED.
- So SGA 7 IX 3.5 (unipotence) and Cor. 3.3 are not on the manuscript's route; Prop. 4.7 reaches it only through
  Silverberg–Zarhin's citation of it.

## 3. Where the rows feed (traced)

See scratch/sz-raynaud/log.md for the file:line chain. Summary:

```
sga7_IX_Cor3_3 → sga7_IX_3_3_SHpre → sga7_IX_3_3_SH → semistablePersistsSHcp, sga7_IX_3_3 → SS3 (SemistablePersists)
                → r20_of_leaves' / r20Lower_of_leaves' (Faltings heights over a common semistable field)
sga7_IX_3_5_ForwardGeom → SemistableUnipotent → r6 RaynaudCriterionNF
                → D2: raynaudPlace_of_R6 → torsFix_of_descent → torsFixWildOdd / tateWildKE / localGlue_of_descent
                      (also lt-local's linkedTateLocal through localGlue_at: D2 again)
                → A6: qmModelG3_of (QML3 good reduction, the kernel's Raynaud route; manuscript L529-530 differs)
raynaudSemistableSHOr → raynaudSemistableSH → (with StrictHenselizationPair) RaynaudSemistable → r6, SS1
```

In the kernel the ELLIOT sentence is already *proved*: from r6's unipotence, the `p`-power period of wild
elements (TailH `wildIter`) and the algebraic core `PkgI2.fixed_of_unipSq_of_iterate`. That proof is the
kernel's, not the manuscript's: the manuscript states the sentence without proof.

**Follow-up (not done).** To make D2 rest on the manuscript's route in the bundle, re-prove TailH's
`raynaudPlace_of_R6` with conclusion "fixes" from `RaynaudWildNF`. That needs a lemma
`isWildInertia_of_wild_gen`, the analogue of TailH's `isInertia_of_wild_gen` for `IsWildInertia` on
`normVS f₁`. Then `torsFix_of_descent` loses its unipotence and `wildIter` steps. That removes r6 from D2 and I2,
but r6 stays needed by A6, so no field leaves the bundle until A6 is rerouted too, to the manuscript's universal
abelian scheme (L529-530).

## 4. Known issues in the sources

1. **Silverberg–Zarhin Thm 3.5 at `n = 3` (known issue, unresolved).** locators.md row R6: Thm 3.5 (p. 406)
   cites SGA 7 IX Prop. 4.7 and allows the `n`-torsion to be defined over an unramified extension, but the text
   extraction reads the threshold like `> 3`. Whether the printed threshold includes `n = 3` was not confirmed from
   the scan, and the page has not been re-read (no network here). The manuscript uses `n = 3` for every `p ≠ 3`.
   - If the print says `n ≥ 3`, the manuscript's citation is exact.
   - If it says `n > 3`, the citation does not cover the manuscript's case `n = 3`. The mathematics is still
     right: SGA 7 IX Prop. 4.7, read 11-17 (kinds.tsv row raynaudSemistableSHOr, p. 366), allows every `n > 1`
     prime to `p` except `n = 2`. But that is a source the manuscript does not cite.
   - **Repair within the manuscript's own citation (computed):** use `A[5]` for `p ≠ 5` and `A[4]` for `p = 5`.
     Both levels are `≥ 4` and prime to `p`, and `|GL₄(𝔽₅)| = 116 064 000 000 = G₀` and
     `|GL₄(ℤ/4)| = 2¹⁶·|GL₄(𝔽₂)| = 1 321 205 760 ≤ G₀`, so the degree bound `[F:ℚ_p] ≤ DG₀` at L815 is unchanged
     (VERIFIED, computed in python; `|GL₄(𝔽₃)| = 24 261 120`).
   - The Lean leaf states `3 ≤ m`, the manuscript's use, and is flagged pending reading.
2. **Base and definitions of Theorem 3.5 (UNVERIFIED).** Not confirmed:
   - whether Silverberg–Zarhin state the theorem over any discretely valued field or over a complete/henselian
     one;
   - how they define semistable reduction: an extension of an abelian variety by a torus on the special fibre, or
     no unipotent part.

   The leaf is over any DVR (the kernel applies r6 at DVRs of number fields, which are not complete). If the
   print is over complete fields only, the leaf exceeds it by the compatibility of Néron models with completion
   (BLR 7.2/1, UNVERIFIED). The conclusion is reading-robust for the two extension readings. If the print reads
   "no unipotent part", use the Def34 pair (§1), which is literal under that reading.
3. **The ELLIOT sentence (L817-818) is uncited.** It is true and standard. Semistable reduction gives
   `(σ−1)² = 0` on `T_ℓ` for inertia (SGA 7 IX 3.5, not cited; Silverberg–Zarhin Thm 3.3, p. 405, per locators R6,
   not cited by the manuscript either), and wild inertia is pro-`p` with `p ≠ ℓ`, so a unipotent element of
   `p`-power order is trivial. `elliot_of_semistableUnipotent` is this argument in Lean, with the pro-`p` input as
   the on-the-spot glue `WildPeriodCoprime`. Suggested manuscript repair: cite Silverberg–Zarhin Thm 3.3 (or SGA 7
   IX 3.5) and add "since wild inertia is pro-`p`".
4. No issue found in the manuscript's use of the criterion with `F = L_v(A[3])`: the torsion is rational over `F`,
   which is the case "defined over an unramified extension" with the trivial extension.

## 5. Lean

- Contribution: `ZInQKernel/Contrib/OneProof/SZRaynaud.lean` (development copy scratch/sz-raynaud/SZR.lean).
  Imports GaRigiditySGA7, RaynaudSemistableOr, NeronDVR, GeomConnOfRationalPoint, MumfordTorsionAlgClosed,
  MulEtale; never `ZInQKernel.OneProof.Main`. GaRigidity.lean and GaRigiditySGA7.lean unchanged.
- Compile, `#discharges`, axioms, autofold dry run: see the log and §6.

## 6. Provenance of every new leaf

| leaf | provenance | kind | flag |
| --- | --- | --- | --- |
| `SilverbergZarhinThm35` | (b) cited print, in the manuscript's bibliography (L11077), Thm 3.5 p. 406; wording UNVERIFIED | published | `pending reading: …` (GLUE) |
| `ElliotWildInertiaTrivial` | (a) diophantine_zq.tex:817-818, uncited sentence (ELLIOT) | consequence | `ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818) …` |
| `SilverbergZarhinThm35Def34` (variant, not folded) | (b) as above | published | pending reading |
| `ElliotWildInertiaTrivialDef34` (variant, not folded) | (a) as above | consequence | ELLIOT |
| `WildPeriodCoprime` (glue, sanity theorem only) | (c) on-the-spot (in neither the manuscript nor Silverberg–Zarhin) | glue | never LEAF |

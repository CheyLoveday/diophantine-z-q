# Néron–Ogg–Shafarevich: remove the open field

**The two live readers use only good reduction ⇒ inertia triviality on prime-to-residue-characteristic torsion. That implication is proved in Lean, so the bypass removes `neronOggShafarevichSep` without adding a hypothesis.** The H count goes from **5 LEAF / 24 GLUE on 29 fields** to **5 / 23 on 28** under both strict ratings. The separate perfect-residue-field statement records the reported print hypothesis; the bypass does not use it.

Base: `be73b91c5` (fold-c8, `sixContactMin_of_open80`), plus the unchanged proof from `e9828e923`. The active theorem and its open-field tables have not been switched. See `scratch/nos-narrow/log.md` for the results log.
`NOSNarrow.lean`, `NOSNarrowChain.lean` and the `sixContactMin_of_open81` dry run compile. All 18 reader theorems, the copied chain's top, and the dry-run theorem use only `propext`, `Classical.choice`, and `Quot.sound` (VERIFIED).

## Statements and reader replacements

- `NOSNarrow.NeronOggShafarevichSepPerfect` is the old pair of torsion equivalences over a separable closure of `K`, with `[PerfectField (IsLocalRing.ResidueField O)]` added after `[IsDiscreteValuationRing O]`. Good reduction is equivalent both to inertia fixing all positive invertible-order torsion and to its doing so for infinitely many orders. `NOSNarrow.perfect_of_sep` restricts the old hypothesis. This is a statement record; it has no unconditional provider and is not a requested leaf.
- `NOSNarrow.NOSForward`: for a field `K`, a DVR `O ⊆ K`, a valuation ring `w` of `AlgebraicClosure K` over `O` and an abelian variety `A/K`, `HasGoodReduction A O` implies `InertiaTrivialOn A w m` for every positive integer `m` that is a unit in `O`. `NOSNarrow.nosForward_proof` calls the merged, unchanged `NOSProof.inertiaTrivialOn_of_goodReduction`. Lift the torsion point to the abelian scheme by properness; inertia fixes its reduction, and separated étale prime-to-residue-characteristic torsion gives uniqueness. This is the uncited manuscript implication (provenance (a), proved in Lean). `nosForward_of_r7a` is the compatibility adapter from the old full criterion.
- `HDec.G0ModField.KernelField.kernelFieldExists_of_split_hf_u''_nos` produces the same `KernelFieldExists`, with `NOSForward` replacing the original NOS binder. At the bottom, `HDec.G4WeilRes.point_fixed_nos` transports the implication to each conjugate, and `good_of_QML3U_nos` drops the unused NOS binder on the separate good-reduction branch.
- `HDec.HSyn.modelG3G6_of_leaves3U_nos` produces the same `ModelG3G6`, with `NOSForward` in place of the original NOS binder. `GoodRedTorsionTF` takes `NOSForward` as its antecedent; `goodRedTorsionT_nos` uses it on each `ℓ^n`-torsion group before `tate_eq_one_of_torsion` gives G3. Both top copies have a Lean example recovering the original signature via `nosForward_of_r7a`. These adapters and copies are proved glue (provenance (c), Lean bookkeeping).

## Census

The traversal starts at `ZInQ.OneProof.frozenTarget` and visits declaration types, values and inductive constructors. `Uses.lean` lists all direct type mentions of `PkgI2.NeronOggShafarevich` and `NOSSepDict.NeronOggShafarevichSep`, and the reader whose type mentions the A6 alias. The traversal visited 151,747 constants with external module bodies skipped (VERIFIED). The table excludes bundle machinery; the full list is in `scratch/nos-narrow/uses.txt`.

For the kernel-field rows, **Kf** means `K/ℚ` finite, `O = w.comap e` above `p ∉ T`, the QM surface in its conjugate slots (the bottom theorem applies to either `A` or `B`), and `m = ℓ^n` with `ℓ ∈ {2,3}`, `ℓ ≠ p`. For the A6 rows, **A6** means a number field `K`, `O` above `p > 324` (in the caller), `A` the QM surface with level three, and `m = ℓ^n`, `ℓ ≠ p` (the live G3 outputs use `ℓ = 3,5`). These applications have finite, hence perfect, residue fields. In the terminal theorems themselves the binder is more general. File names below are relative to `ZInQKernel/`.

| Constant | Source | Direction | Instance |
| --- | --- | --- | --- |
| `NOSSepDict.neronOggShafarevich_of_sep` | `Contrib/OneProof/NeronOggShafarevichSep.lean:219` | Full criterion, sep-to-algebraic-closure adapter; no converse application to a live abelian variety | Generic binder, no concrete instance |
| `HSyn.neronOggShafarevich_ofK5` | `OneProof/H/TailM.lean:445` | Whole type conversion for an unread carried field | Generic binder, no concrete instance |
| `point_fixed` | `OneProof/H/TailC.lean:5203` (use at :5244) | (a) ⇒ (b) | Kf |
| `inertiaFixesHomsMon_hf` | `Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1033` | Passes (a) ⇒ (b) twice to `point_fixed` | Kf, one use at each embedding |
| `inertiaFixesHomsMon_of_leaves_hf` | `Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1120` | Forwards | Kf |
| `kernelField_of_model_hf` | `Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1143` | Forwards | Kf |
| `good_of_QML3U` | `Contrib/OneProof/D2A6Wrap.lean:109` | Unused binder; good reduction from the proper model | Kf, no torsion order |
| `kernelFieldExists_of_pieces_hf_u` | `OneProof/H/D2A6Chain.lean:393` | Forwards; also passes the unused argument to `good_of_QML3U` | Kf |
| `kernelFieldExists_of_leaves_hf_u` | `OneProof/H/D2A6Chain.lean:424` | Forwards | Kf |
| `kernelFieldExists_of_leaves_FS5_hf_u` | `OneProof/H/D2A6Chain.lean:446` | Forwards | Kf |
| `kernelFieldExists_of_split_hf_u` | `OneProof/H/D2A6Chain.lean:470` | Forwards | Kf |
| `kernelFieldExists_of_split_hf_u'` | `OneProof/H/D2A6Chain.lean:494` | Forwards | Kf |
| `kernelFieldExists_of_split_hf_u''` | `OneProof/H/D2A6Chain.lean:521` | Forwards; assembled at `OneProof/H/C8Chain.lean:733` | Kf |
| `GoodRedTorsionT` | `Contrib/OneProof/A6IntModel.lean:165` | NOS is an antecedent in the definition | A6 |
| `goodRedTorsionT` | `Contrib/OneProof/A6IntModel.lean:203` (use at :296) | (a) ⇒ (b), through the alias | A6 |
| `qmModelG3U_of_z30` | `Contrib/OneProof/A6Z30.lean:161` | Forwards | A6 |
| `modelG3G6_of_leavesU_z30` | `Contrib/OneProof/A6Z30.lean:175` | Forwards | A6 |
| `modelG3G6_of_leaves3U` | `Contrib/OneProof/D2A6Wrap.lean:89` | Forwards; assembled at `OneProof/H/C8Chain.lean:749` | A6 |

The old converse applications are in `HDecomp/A6/A6.lean:695`, `OneProof/H/LF4T5.lean:740` and `OneProof/H/LPrefix.lean:856`. The converse and its `QML3.goodReduction` wrappers are absent from the active closure. The `ℤ[1/30]` model replaced that proof of good reduction in d2a6b.

## Bypass and count

`NOSNarrowChain.lean` copies the tainted declarations, drops both spellings of the old field and their assignments, and passes `NOSNarrow.nosForward_proof` at C8's two reader calls. The taint scan includes carriers whose seed projection was unused, notably `HDec.HSyn.ResearchLeaves3EBU`. It distinguishes the main and `HDec.HSyn.GR9` copies by fully qualified name and module. Neither contribution imports `ZInQKernel.OneProof.Main`. The exact taint follows 296,118 constants from `frozenTarget` (99 value-tainted; 943 including type dependencies), and the generator emits 121 declarations including 32 structures, deletes 31 forwarding assignments, and replaces both terminal calls.

The integrator can copy `scratch/nos-narrow/BypassFold.lean.txt` to the next H tail module, then switch `ZInQKernel/OneProof/Main.lean` to `OpenResearchLeaves62` and `sixContactMin_of_open81` (with `OpenTextbookLeaves18` and `OpenAddedLeaves28`). Remove row 18 from `docs/one-proof/kinds.tsv`, remove the corresponding claims entry, and regenerate the open documentation. `scratch/nos-narrow/kinds-rows.tsv` is the preview (VERIFIED with `autofold.py`'s `counts`). Pole completeness is outside this H count. This bypass is not expressible as an autofold: it avoids the old hypothesis instead of supplying it as stated.

## Checks and replay

- `scratch/nos-narrow/Uses.lean` and `Taint.lean` run with `lake env lean` on the built base. Pass the taint output to `python3 -B scratch/nos-narrow/gen_chain.py TAINT NOSNarrowChain.lean`. `python3 -B scratch/nos-narrow/gen_bypass.py` regenerates the integration wrapper, closure check and count preview. The reader source can also be replayed with `gen_readers.py`.
- `readers-axioms.txt`, `chain-build.txt` and `bypass-build.txt` record the Lean compile results. For the dry run, compile a temporary `.lean` copy of `BypassFold.lean.txt`. `ClosureCheck.lean.txt` likewise compiles standalone. The checked files do not import each other.
- In `closure.txt`, both full criterion types and `NOSSepDict.neronOggShafarevich_of_sep` are **present** below `sixContactMin_of_open80` (277,489 constants) and **absent** below `sixContactMin_of_open81` (277,474). The bypass uses `NOSNarrow.nosForward_proof`. The perfect-residue-field record and `sorryAx` occur in neither closure.
- `Discharges.lean` and `discharges.txt`: no NOS provider and no new discharge. The 243 matches are 220 projections from the copied bundles and 23 pre-existing matches. The active `Main` and its catalog remain unchanged.

## Known issues and print hypothesis

- **UNVERIFIED:** As recorded in the #63 audit on row 18, Serre–Tate §1 assumes a **perfect residue field** (recalled, and so described in Milne's survey arXiv:1210.7459 §2.7; the paper itself was not read). BLR §7.4 Thm 5 gives the `T_ℓ` form over any discrete valuation ring (UNVERIFIED). The old pair of torsion equivalences lacks the perfection condition and was rated GLUE with reading risk. A reading would confirm the scope of the perfect residue field hypothesis and which torsion formulations are displayed in Theorem 1.
- Serre–Tate 1968 is **not** in the manuscript's bibliography (VERIFIED, L11009–11247). The two forward uses in the manuscript are uncited and proved here with the merged reduction argument. No publication claim is needed to remove the row.
- The proper `ℤ[1/30]` model remains an input elsewhere in the chain. The pre-existing polarization question for that model is recorded in `docs/research/d2a6b.md`; neither NOS reader uses a polarization.
- No manuscript error was found in the checked steps.

## Manuscript check

All line ranges refer to `diophantine_zq.tex`. The verdicts are about the steps used here, and do not constitute a primary-source review of the cited literature.

| Lines | Verdict |
| --- | --- |
| L383–384 | **OK.** `S` contains every prime up to 324, including 2, 3 and 5. The model over `ℤ[1/30]` suffices at primes outside `S`. |
| L443–477 | **unverified.** This work takes the proper model and its universal abelian scheme through `Y3FullThreeRepZ30`; it does not prove that input. |
| L524–528 | **OK.** The splitting field `K` is unramified outside `T`. The reader takes this from `fibreCoverExists_of_propTSAll'` with `unramifiedConjugates_proved`; neither reads NOS. |
| L529–530 | **gap filled.** The proper model gives a lift of the classifying point by the valuative criterion, and pulling back its universal abelian scheme gives good reduction. `D2A6.hasGoodReduction_of_z30` proves this without NOS. |
| L557–560 | **gap filled.** Outside `T`, `K` is unramified and the conjugates have good reduction. The manuscript's uncited Tate-module step for `ℓ ≠ p` on `W₀` is supplied in Lean on the individual conjugates and their `ℓ^n`-torsion; faithfulness gives the Hom lattice action and hence unramifiedness of `L`. This is the kernel-field reader. |
| L752–753 | **gap filled.** `r_ℓ` is unramified outside `T ∪ {ℓ}`. A6 supplies the uncited implication on Tate modules (`G3Out`), then `G0Galois.g11` uses unramified descent and the G8 intertwiner. |
| L778–788 | **OK.** Frobenius and trace comparison do not read this field. The Lean cofinite comparison uses the reduction and Frobenius bridge `tateBridge35_of_neron_nmp`. |
| L814–818 | **OK.** The Lean wild-inertia step uses `RaynaudWildNF` through `R6U` (with 5 in place of 3 at `p = 3`); it does not read the good-reduction criterion. |
| L848–851 | **OK.** For large primes the Lean wild-inertia bound does not read this field; it uses `tateWildK_of_R6U` via the Raynaud route in place of the manuscript's direct good-reduction argument. |
| L852 | **OK.** The separate zero-conductor clause outside `T` uses G11, hence A6 and the forward implication. |
| L11009–11247 | **OK.** The bibliography has no Serre–Tate 1968 entry; the two uses above are uncited. |

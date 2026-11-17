# Contributing to the single proof

`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) is one Lean theorem: it proves the frozen target
`ZInQ.FrozenTarget` of "Z is Diophantine in Q" from a list of open hypotheses, with no `sorry` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. **[OPEN.md](OPEN.md) lists every open
hypothesis** with its exact Lean statement, its kind, its source and who is working on it. Each one you prove
in Lean, or reduce to theorems in their printed form, leaves the list.

## What to contribute

Pick a hypothesis in [OPEN.md](OPEN.md) whose status is open, and claim it before you start: comment
`Claiming <field> at <commit>` on [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14), with the
field name exactly as OPEN.md shows it and the commit you start from, or open a draft pull request that links
#14 with that line in its body. Hold one claim at a time to begin with; if you stop, comment
`Releasing <field>: <what blocked you>`. The full claim rule, including lapses, is in the root
[CONTRIBUTING.md](../../CONTRIBUTING.md#choose-and-claim-one-statement). Then either:

1. **Prove it.** Write a theorem whose type is exactly the hypothesis's statement:

   ```lean
   theorem igusaCMValue24_proof : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24 := by
     ...
   ```

2. **Reduce it to published theorems.** State each theorem you use as a `def … : Prop` in its printed form,
   over genuine definitions (Mathlib's, or the repository's), with a docstring giving the edition, page and
   display you read (or UNVERIFIED if nobody has read it), and prove the hypothesis from them:

   ```lean
   /-- Bosch–Lütkebohmert–Raynaud, *Néron models* (Springer, 1990), p. <page>, §1.2 Prop. 4
   (printed form). -/
   def BLR_1_2_4 : Prop := ...

   theorem neronLocalizesDVR_of_printed (h : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := ...
   ```

   This helps when the hypothesis is GLUE (a consequence, a composite, or project glue) and the new statements
   are published leaves. Each new printed leaf enters OPEN.md flagged unread: it counts as published, and a
   statement check ([STATEMENT-CHECKS.md](STATEMENT-CHECKS.md)) compares it with the print. A leaf whose print may
   say something weaker is flagged pending reading and counts as glue until a check clears it. A new statement must be
   the published theorem or a consequence of it, never stronger, and never over a structure invented for the
   purpose.

Never change a hypothesis's statement. If you find one false, vacuous, or stronger than its source, report it
(with a corrected statement) on the issue: that is a valid and useful result.

## Where it goes

A new file `ZInQKernel/Contrib/OneProof/<StatementName>.lean`, importing the module that declares the statement
you prove and whatever else you need. OPEN.md gives the statement's Lean constant, for example
`CToPrinted.SGA7_IX_3_3`; searching the tree for its declaration (`git grep -n "def SGA7_IX_3_3"`) finds the file,
here `ZInQKernel/OneProof/H/TailZ19.lean`, so the import is `ZInQKernel.OneProof.H.TailZ19`.
Do not import `ZInQKernel.OneProof.Main`: once your file is folded, `Main` imports it, and the import would be
a cycle. Proofs only in new files: do not edit existing
modules. Keep a file under about 150 KB. Open a pull request against this fork's `main`.

## How to check it

Build, then run `#discharges` from a scratch file:

```lean
import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.<StatementName>

#discharges
```

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.<StatementName>
lake env lean <scratch file>
```

For every theorem in your file it prints which open hypotheses it proves, the hypotheses it still assumes
(your new leaves), and its axioms. A statement change does not match. A proof using `sorry` is flagged.

You may not have to run it yourself. For a pull request into `main` that only adds files under
`ZInQKernel/Contrib/OneProof/`, the same check runs on the files it adds, built on top of the current `main` (not
on the rest of your branch), as the GitHub Actions check "discharge check" on a fresh hosted runner with no
secrets and no access to project machines (`scripts/one_proof/sandbox/README.md`). The verdict is in the check's
job summary, and the run may wait for a maintainer to approve it before it starts. A pull request that changes
anything else is out of scope for the automatic check. The automatic check is being set up: until it has run on
a first contribution, include your own `#discharges` output in the pull request. The repository's default `lake build` does not compile `ZInQKernel/Contrib/OneProof`, so a green
CI check alone says nothing about a contribution.

The automatic result is advisory. The project's agents check every pull request before it is merged (the build,
`#discharges`, the axioms, and the scan for code that runs at build time); no person reads every file. A file with
code that runs at build time (`#eval`, `run_cmd`, `initialize`, new `syntax`, `notation`, macros or elaborators)
is not merged, since such code could print a forged result; if you need it, ask on the issue first.

The bar for merging:

* the Lean compiles with only the standard axioms, and the discharge check shows the hypothesis proved (until
  the automatic check has run on a first contribution: your own `#discharges` output, checked by the project's agents);
* the file has no code that runs at build time;
* each new printed leaf has a row in [`docs/research/locators.md`](../research/locators.md) and enters
  kinds.tsv flagged unread (or pending reading, if its print may say something weaker);
* the project's integrator merges it into the next fold (agent review: the checks above, run by the project's agents).

Merges into this fork carry no Protocol B review (the original repository's review protocol); a result is
reviewed again when it moves to the original repository. The integrator then folds it into the single proof: a
new bundle generation without that hypothesis (and with your leaves, if any), `frozenTarget` switched to it, the
build re-checked, and OPEN.md regenerated.

## What it costs to build

You do not need to build anything to contribute. If you want to, these are the measured figures so far.
`lake exe cache get` fetches only Mathlib's compiled files; nothing of this project is cached, so its own files
build from source.

| what was built | cold or partial | commit | measured |
| --- | --- | --- | --- |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `1e30d4b2` | 11,655 Lake jobs in 20 minutes |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `4c1cc906` | 11,813 Lake jobs |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `053cbad0` | 12.5 minutes |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines, for leaf-fold4 ([`docs/research/leaf-fold4.md`](../research/leaf-fold4.md)) | not recorded | not recorded | 26 minutes |
| `lake build +ZInQKernel.OneProof.Main` at w66, the x6 fold ([`docs/research/x6-fold.md`](../research/x6-fold.md)) | partial rebuild | `ecdb5d846` | 12,916 Lake jobs in 8.5 minutes |
| the contributions and OneProof at w63 | not recorded | `b5ff0474` | 12,913 Lake jobs |
| the Tau Ceti dependency tree | cold | not recorded | 6,846 Lake jobs in 8 minutes 4 seconds; 3.4 GB |
| one large file compiled against an already built `ZInQKernel.OneProof.Main` | partial (that file only) | not recorded | about 8 to 9 GB of memory |
| upstream's kernel job on a GitHub-hosted runner | not recorded | not recorded | needed a 180-minute timeout and 8 GiB of extra swap |

A cold measurement of `lake build +ZInQKernel.OneProof.Main` on a GitHub-hosted runner will be added to this
table. On a laptop a full build is a bigger investment. A measured row from your machine (commit, cold or partial,
cores, memory cap, peak memory, disk, Lake jobs, wall-clock) is welcome and credited.

## For the integrator: folding a contribution

`scripts/one_proof/autofold.py SPEC.json` writes the fold of a checked contribution: a new module
`ZInQKernel/OneProof/H/TailZ<k+1>.lean` with the next generation of each affected bundle (the discharged fields
removed, the new leaves added), a theorem filling each discharged field with its proof, and the next top theorem;
it switches `Main.lean` to it and updates `kinds.tsv` and `claims.tsv`. It refuses a fold that raises either GLUE
count (the strict or the strictest column) unless given `--allow-rise`. The spec format is in the script's docstring; `scratch/contrib-kit/autofold-test.json` exercises the
mechanics (with `sorry`, so it is a test, not a fold). Then build, check the axioms, compare hashes with
`scratch/one-proof/DumpCompact.lean` and `cmp_hashes.py` (no existing constant may change except `frozenTarget`),
and regenerate OPEN.md (`scripts/one_proof/OpenStatements.lean`, then `render_open.py`, then `render_open.py --check`).

## A worked example

`scratch/contrib-kit/DischargesTest.lean` runs `#discharges` on three theorems, against the current open
hypotheses. Its output (generated from `scratch/contrib-kit/DischargesTest-output.txt`):

<!-- worked-example:begin -->
```
scratch/contrib-kit/DischargesTest.lean:13:8: warning: declaration uses `sorry`
DISCHARGES [OpenResearchLeaves30.dsThm965Printed] by DSCoeffExt.dsThm965Printed_of_charpoly
  still assumes: [∀ (N : ℕ) [inst : NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k),
   2 ≤ k →
     DSCoeffExt.IsNormalizedEigenformDS f χ →
       ∀ [inst : NumberField ↥(DSCoeffExt.coeffField f)] (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
         (lam : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(DSCoeffExt.coeffField f))),
         ↑ℓ ∈ lam.asIdeal →
           ∃ ρ,
             Continuous ⇑ρ ∧
               ∀ (p : ℕ),
                 Nat.Prime p →
                   ¬p ∣ N * ℓ →
                     (∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar),
                         ZInQ.Contrib.G9.PkgI4.LiesOver v p → ∀ σ ∈ ValuationSubring.inertiaSubgroup ℚ v, ρ ↑σ = 1) ∧
                       ∀ (b : ↥(DSCoeffExt.coeffField f)),
                         ↑b = χ ↑p * ↑p ^ (k - 1) →
                           ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
                             ZInQ.Contrib.G9.PkgI4.LiesOver v p →
                               ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
                                 (↑(ρ σ)).charpoly =
                                   Polynomial.X ^ 2 -
                                       Polynomial.C
                                           ((algebraMap (↥(DSCoeffExt.coeffField f))
                                               (IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                                 (↥(DSCoeffExt.coeffField f)) lam))
                                             ⟨ZInQ.Contrib.G9.PkgI4.coeff f p, ⋯⟩) *
                                         Polynomial.X +
                                     Polynomial.C
                                       ((algebraMap (↥(DSCoeffExt.coeffField f))
                                           (IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                             (↥(DSCoeffExt.coeffField f)) lam))
                                         b)]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.mumfordGroupLawConn] by DictModels.MumfordConn.conn_of_field
  still assumes: [ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.raynaudSemistableSHOr] by DictModels.RaynaudOr.or_of_field
  still assumes: [ReductGlue.RaynaudSemistableSH]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_3_SHpre] by DictModels.SGA7Pre.pre_of_SH
  still assumes: [SGA7PersistsNF.SGA7_IX_3_3_SH, CToPrinted.SGA3_VIB_3_10, AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves14NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves14NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves14NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves14NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves14NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves14NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves14NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves14NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves14NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves14NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves14NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves14NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves14NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves15NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves15NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves15NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves15NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves15NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves15NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves15NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves15NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves15NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves15NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves15NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves15NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves15NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves16NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves16NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves16NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves16NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves16NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves16NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves16NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves16NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves16NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves16NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves16NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves16NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves16NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves17NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves17NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves17NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves17NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves17NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves17NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves17NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves17NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves17NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves17NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves17NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves17NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves17NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves17NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves18NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves18NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves18NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves18NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves18NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves18NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves18NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves18NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves18NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves18NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves18NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves18NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves18NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves18NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves19NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves19NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves19NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves19NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves19NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves19NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves19NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves19NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves19NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves19NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves19NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves19NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves19NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves19NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves20NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves20NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves20NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves20NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves20NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves20NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves20NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves20NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves20NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves20NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves20NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves20NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves20NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves20NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves20NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves21NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves21NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves21NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves21NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves21NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves21NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves21NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves21NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves21NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves21NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves21NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves21NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves21NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves21NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves21NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves21NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves22NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves22NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves22NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves22NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves22NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves22NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves22NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves22NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves22NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves22NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves22NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves22NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves22NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves22NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves22NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves22NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves22NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves23NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves23NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves23NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves23NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves23NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves23NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves23NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves23NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves23NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves23NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves23NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves23NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves23NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves23NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves23NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves23NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves23NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves23NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves24NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves24NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves24NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves24NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves24NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves24NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves24NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves24NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves24NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves24NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves24NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves24NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves24NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves24NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves24NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves24NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves24NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves24NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves25NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves25NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves25NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves25NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves25NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves25NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves25NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves25NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves25NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves25NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves25NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves25NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves25NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves25NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves25NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves25NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves25NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves25NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves26NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves26NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves26NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves26NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves26NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves26NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves26NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves26NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves26NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves26NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves26NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves26NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves26NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves26NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves26NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves26NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves26NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves26NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves27NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves27NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves27NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves27NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves27NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves27NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves27NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves27NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves27NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves27NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves27NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves27NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves27NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves27NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves27NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves27NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves27NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves27NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves28NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves28NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves28NS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves28NS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformCoeffFieldFinite] by HDec.HSyn.OpenResearchLeaves28NS.eigenformCoeffFieldFinite
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves28NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves28NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves28NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves28NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves28NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves28NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves28NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.mumfordGroupLawConn] by HDec.HSyn.OpenResearchLeaves28NS.mumfordGroupLawConn
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.neronOggShafarevichSep] by HDec.HSyn.OpenResearchLeaves28NS.neronOggShafarevichSep
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves28NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves28NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves28NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves28NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves28NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves28NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.raynaudSemistableSHOr] by HDec.HSyn.OpenResearchLeaves28NS.raynaudSemistableSHOr
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_3_SHpre] by HDec.HSyn.OpenResearchLeaves28NS.sga7_IX_3_3_SHpre
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves28NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves28NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves28NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.bostLowerBound] by HDec.HSyn.OpenResearchLeaves29NS.bostLowerBound
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.deRhamH1AbVarT] by HDec.HSyn.OpenResearchLeaves29NS.deRhamH1AbVarT
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves29NS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves29NS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformCoeffFieldFinite] by HDec.HSyn.OpenResearchLeaves29NS.eigenformCoeffFieldFinite
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.eigenformHTNew] by HDec.HSyn.OpenResearchLeaves29NS.eigenformHTNew
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.elkiesX6StarFunctionField] by HDec.HSyn.OpenResearchLeaves29NS.elkiesX6StarFunctionField
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gaudronRemondThm14] by HDec.HSyn.OpenResearchLeaves29NS.gaudronRemondThm14
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerProp56X6] by HDec.HSyn.OpenResearchLeaves29NS.gonzalezRotgerProp56X6
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.gonzalezRotgerX6Ab] by HDec.HSyn.OpenResearchLeaves29NS.gonzalezRotgerX6Ab
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.hodgeTateDecompAbVar] by HDec.HSyn.OpenResearchLeaves29NS.hodgeTateDecompAbVar
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.javanpeykarBound] by HDec.HSyn.OpenResearchLeaves29NS.javanpeykarBound
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.mumfordGroupLawConn] by HDec.HSyn.OpenResearchLeaves29NS.mumfordGroupLawConn
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.neronOggShafarevichSep] by HDec.HSyn.OpenResearchLeaves29NS.neronOggShafarevichSep
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves29NS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r11r12] by HDec.HSyn.OpenResearchLeaves29NS.r11r12
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by HDec.HSyn.OpenResearchLeaves29NS.r16CoreY
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r17] by HDec.HSyn.OpenResearchLeaves29NS.r17
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9a] by HDec.HSyn.OpenResearchLeaves29NS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r9b] by HDec.HSyn.OpenResearchLeaves29NS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.raynaudSemistableSHOr] by HDec.HSyn.OpenResearchLeaves29NS.raynaudSemistableSHOr
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_3_SHpre] by HDec.HSyn.OpenResearchLeaves29NS.sga7_IX_3_3_SHpre
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by HDec.HSyn.OpenResearchLeaves29NS.sga7_IX_3_5_ForwardGeom
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.shimuraMainThmIDeligneY3AbU] by HDec.HSyn.OpenResearchLeaves29NS.shimuraMainThmIDeligneY3AbU
  still assumes: [HDec.HSyn.OpenResearchLeaves29NS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves10HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves10HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves10HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves10HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves10HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves10HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves10HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves10HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves11HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves11HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves11HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves11HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves11HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves11HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves11HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves11HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves12HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves12HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves12HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves12HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves12HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves12HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves12HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves12HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves13HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves13HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves13HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves13HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves13HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves13HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves13HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves13HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves14HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves14HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves14HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves14HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves14HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves14HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves14HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves14HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves6HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves6HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves6HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves6HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves7HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves7HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves7HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves7HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves7HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves7HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves7HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves7HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves8HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves8HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves8HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves8HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves8HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves8HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves8HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves8HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.charPolyIndepOfEllAlgClosed] by HDec.HSyn.OpenTextbookLeaves9HF.charPolyIndepOfEllAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves9HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.gagaMorphism] by HDec.HSyn.OpenTextbookLeaves9HF.gagaMorphism
  still assumes: [HDec.HSyn.OpenTextbookLeaves9HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.mumfordTorsionAlgClosed] by HDec.HSyn.OpenTextbookLeaves9HF.mumfordTorsionAlgClosed
  still assumes: [HDec.HSyn.OpenTextbookLeaves9HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves15.neronSchemeExtensionExists] by HDec.HSyn.OpenTextbookLeaves9HF.neronSchemeExtensionExists
  still assumes: [HDec.HSyn.OpenTextbookLeaves9HF]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves20.picZeroAbVar] by PicDict.picZeroAbVar_of_leaves
  still assumes: [PicDict.PicLocFinType, PicDict.IdentityComponentLFT, PicDict.PicZeroSmooth, PicDict.PicZeroProper]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PicDict.weilPairingMumford_final
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 PicDict.MumfordKLFiniteAC]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PicDict.weilPairingMumford_of_ac
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PicDict.weilPairingMumford_of_mumford
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PicDict.weilPairingMumford_of_printed
  still assumes: [PicDict.MumfordSquare,
 PicDict.MumfordMulNPicZero,
 PicDict.MumfordPhiSurjective,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.MumfordWeilPairing,
 PicDict.MumfordWeilNondeg,
 PicDict.MumfordWeilAlt,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.r16CoreY] by R16Split.coreY_of_r16
  still assumes: [LeafModCurves.R16_EichlerShimuraJ1']
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves30.sga7_IX_3_5_ForwardGeom] by UnipotentForward.forwardGeom_of_forward
  still assumes: [UnipotentForward.SGA7_IX_3_5_Forward, UnipotentForward.SemiAbelianDescendsSepClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hBFH] by ZInQ.BFHPrinted.bfhClauseIIGamma0_of_bfhClauseIIKronecker
  still assumes: [ZInQ.BFHPrinted.BFHClauseIIKronecker]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hGZ] by ZInQ.GZAlg.grossZagierAlgOptCd_of
  still assumes: [ZInQ.GZAlg.GrossZagierAlgOpt]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 40 open hypotheses, 9530 theorems checked, 301 discharge one
```
<!-- worked-example:end -->

`t1` assumes the hypothesis it proves (`quotientP1Coordinate`), so it reduces nothing; `t2 : True` matches
nothing; `t3` matches an open hypothesis but uses `sorry`, so it is flagged. The count of theorems checked also
includes the theorems of the contributions already folded in (`#discharges` checks the current file and every
imported module under `ZInQKernel.Contrib.OneProof`); they discharge nothing, since their hypotheses are no
longer open.

A real contribution in this shape: cm24-value (`docs/research/cm24-value.md`) proved
`IgusaCMValue24`, Lin–Yang's Igusa vector at the CM point of discriminant −24, from Mathlib's Jacobi theta
functional equation and explicit algebra, as the single theorem `CM24.igusaCMValue24_field :
HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24`. The fold (`ZInQKernel/OneProof/H/TailZ18.lean`) added the
next bundle generation without that field, filled it with the theorem, and switched `frozenTarget`; the
hypothesis left the list.

## Where things are

* [OPEN.md](OPEN.md): the open hypotheses (generated; do not edit).
* [open-statements.json](open-statements.json): the same, as data, read off the Lean build by
  `scripts/one_proof/OpenStatements.lean`.
* [kinds.tsv](kinds.tsv): the classification of each hypothesis (LEAF or GLUE, kind, flag, source, review). The
  counts in OPEN.md and in the fold reports come from it.
* [claims.tsv](claims.tsv): who holds what. To claim a hypothesis, comment `Claiming <field> at <commit>` on
  [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14) or open a draft pull request that links #14;
  claims.tsv is regenerated from the claim lines (`scripts/claims/`).
* [reviews.tsv](reviews.tsv): statement checks against the printed sources, with verdicts and rulings.
* [credits.tsv](credits.tsv): who contributed what (proofs, reductions, statement checks and fixes, reviews,
  setup), and in which fold.
* [fold-queue.tsv](fold-queue.tsv): merged contributions waiting for the next fold.
* [frontier-crosswalk.tsv](frontier-crosswalk.tsv): frontier IDs (H-101, T-3, Z-1) mapped to field names.
* [pages-wanted.md](pages-wanted.md): printed pages that someone needs to read (generated from the flags).
* [STATEMENT-CHECKS.md](STATEMENT-CHECKS.md): checking a statement against its printed source, no Lean needed.
* `scripts/one_proof/render_open.py`: regenerates OPEN.md (`--check` fails if a fold changed the hypotheses
  without updating kinds.tsv).
* `scripts/one_proof/sandbox/`: the isolated discharge check the project runs on pull requests, through
  `.github/workflows/contrib-discharges.yml`.
* `scripts/claims/`: reads the claim lines and regenerates claims.tsv.
* `docs/research/leaf-fold*.md`: the fold reports, with what each fold removed and added.

## After a fold (for the integrator)

1. Regenerate `open-statements.json` (`scripts/one_proof/OpenStatements.lean`).
2. Run `scratch/contrib-kit/DischargesTest.lean` and save its output to `scratch/contrib-kit/DischargesTest-output.txt`.
3. Check the new kinds.tsv rows: autofold.py gives each new leaf a flag_class and the area_issue of the field it
   replaces, and flags a published leaf with no flag as unread; add packet, label and tier where they apply.
4. Update the ledgers: the folded rows' status in fold-queue.tsv, a credits.tsv row (with fold and commit) for
   each folded contribution, and any recorded readings in reviews.tsv.
5. Run `scripts/one_proof/render_open.py`, then `scripts/one_proof/render_open.py --check` with
   `ONE_PROOF_HYGIENE_FILE` naming the file of site-specific patterns (see the comment above `HYGIENE` in the
   script).

## Who answers

Replies, reviews and posted checks from the project may be written by AI agents that the project runs; each one
carries a note saying so. Jack McCarthy is accountable for them.

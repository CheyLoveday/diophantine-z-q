# Contributing to the single proof

`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) is one Lean theorem: it proves the frozen target
`ZInQ.FrozenTarget` of "Z is Diophantine in Q" from a list of open hypotheses, with no `sorry` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. **[OPEN.md](OPEN.md) lists every open
hypothesis** with its exact Lean statement, its kind, its source and who is working on it. Each one you prove
in Lean, or reduce to theorems in their printed form, leaves the list.

## What to contribute

Pick a hypothesis in [OPEN.md](OPEN.md) whose status is open (or coordinate on the linked issue). Then either:

1. **Prove it.** Write a theorem whose type is exactly the hypothesis's statement:

   ```lean
   theorem igusaCMValue24_proof : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24 := by
     ...
   ```

2. **Reduce it to published theorems.** State each theorem you use as a `def … : Prop` in its printed form,
   over genuine definitions (Mathlib's, or the repository's), with a docstring giving the exact source, and
   prove the hypothesis from them:

   ```lean
   /-- Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (printed form). -/
   def BLR_1_2_4 : Prop := ...

   theorem neronLocalizesDVR_of_printed (h : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := ...
   ```

   This helps when the hypothesis is GLUE (a consequence, a composite, or project glue) and the new statements
   are published leaves: the strict count in OPEN.md then drops. A new statement must be the published theorem
   or a consequence of it, never stronger, and never over a structure invented for the purpose.

Never change a hypothesis's statement. If you find one false, vacuous, or stronger than its source, report it
(with a corrected statement) on the issue: that is a valid and useful result.

## Where it goes

A new file `ZInQKernel/Contrib/OneProof/<Name>.lean`, importing the module that defines the statement you prove
(OPEN.md's `type` names it; for example `ZInQKernel.OneProof.H.TailZ19`) and whatever else you need. Do not import
`ZInQKernel.OneProof.Main`: once your file is folded, `Main` imports it, and the import would be a cycle. Proofs only in new files: do not edit existing
modules. Keep a file under about 150 KB. Open a pull request against this fork's `main`.

## How to check it

Build, then run `#discharges` from a scratch file:

```lean
import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.<Name>

#discharges
```

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.<Name>
lake env lean <scratch file>
```

For every theorem in your file it prints which open hypotheses it proves, the hypotheses it still assumes
(your new leaves), and its axioms. A statement change does not match. A proof using `sorry` is flagged.

The bar for merging is that the Lean compiles with only the standard axioms and `#discharges` shows the
hypothesis proved. The maintainers then fold it into the single proof: a new bundle generation without that
hypothesis (and with your leaves, if any), `frozenTarget` switched to it, the build re-checked, and OPEN.md
regenerated.

## For maintainers: folding a contribution

`scripts/one_proof/autofold.py SPEC.json` writes the fold of a checked contribution: a new module
`ZInQKernel/OneProof/H/TailZ<k+1>.lean` with the next generation of each affected bundle (the discharged fields
removed, the new leaves added), a theorem filling each discharged field with its proof, and the next top theorem;
it switches `Main.lean` to it and updates `kinds.tsv` and `claims.tsv`. It refuses a fold that raises the strict
GLUE count. The spec format is in the script's docstring; `scratch/contrib-kit/autofold-test.json` exercises the
mechanics (with `sorry`, so it is a test, not a fold). Then build, check the axioms, compare hashes with
`scratch/one-proof/DumpCompact.lean` and `cmp_hashes.py` (no existing constant may change except `frozenTarget`),
and regenerate OPEN.md (`scripts/one_proof/OpenStatements.lean`, `render_open.py --check`, `render_open.py`).

## A worked example

`scratch/contrib-kit/DischargesTest.lean` runs `#discharges` on three theorems, against the current open
hypotheses:

```
DISCHARGES [OpenGlue7.quotientP1Coordinate] by t1
  still assumes: [HDec.MCRGlue.QuotientP1Coordinate]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves10.cartierSmooth] by t3 (uses sorry: not a proof)
  still assumes: []
  axioms: [propext, sorryAx, Classical.choice, Quot.sound]
#discharges: 72 open hypotheses, 3 theorems checked, 2 discharge one
```

`t1` assumes the hypothesis it proves, so it reduces nothing; `t3` has the right statement but uses `sorry`;
`t2 : True` matches nothing.

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
* [claims.tsv](claims.tsv): who is working on what. To claim a hypothesis, say so on the linked issue or open a
  draft pull request; the maintainers update claims.tsv.
* `scripts/one_proof/render_open.py`: regenerates OPEN.md (`--check` fails if a fold changed the hypotheses
  without updating kinds.tsv).
* `docs/research/leaf-fold*.md`: the fold reports, with what each fold removed and added.

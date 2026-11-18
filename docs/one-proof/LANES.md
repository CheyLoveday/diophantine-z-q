# Lanes: parallel work without contention

A lane is one unit of project work: one issue (template "Lane"), one owner, one branch, and a declared footprint.

- **Footprint.** The issue lists the directories and files the lane writes and the board rows it changes. Two lanes
  run at the same time only if their footprints do not overlap. If they must overlap, one depends on the other.
- **New files, one directory.** New Lean goes in new files under the lane's own directory (outside contributors:
  `ZInQKernel/Contrib/OneProof/`). Existing modules change only in folds.
- **One writer per shared file.** [OWNERS.tsv](../../OWNERS.tsv) names the single writer of each shared or generated
  file. Generated files (OPEN.md, open-statements.json, pages-wanted.md) are written only by the folds. claims.tsv is
  written only by the claims sync. A change to someone else's file goes through its owner.
- **See what is coming.** [fold-queue.tsv](fold-queue.tsv) lists what is about to land, and
  `volatile.tsv` (in this directory, once the integrator first uses it) lists board rows that a queued fold will remove
  or rename: do not start work on those.
- **Before pushing.** Run `scripts/push_gate.sh`: it merges current `main` with your branch in memory, stops on
  conflicts, and checks that the merge does not drop board rows that `main` has.
- **Pull requests.** The PR guard runs the same row check. A pull request that removes rows on purpose lists them on a
  `Removes-rows:` line of its body. It also warns when the change touches files with an owner, and when the generated
  files are out of date.
- **Decisions** are recorded once, in [docs/DECISIONS.md](../DECISIONS.md), with a link to where they were made.

## Standing lanes

These lanes run continuously. A new lane checks its footprint against them, and each piece of work inside them is
still claimed in public (on #14 or #83) before it starts.

| Lane | Owner | Writes | Board rows | Depends on | Done when |
|---|---|---|---|---|---|
| Contributor agents working from #14 | project | One new file per claimed field under `ZInQKernel/Contrib/OneProof/`, named after the field. Statement checks are reported as comments on #14, with no files. | The one field each agent has claimed on #14. | A `Claiming <field> at <commit>` comment on #14 for a row that is `open` and not held. Never a row or lane of #83. | The fold shows the field discharged, or the check is recorded in reviews.tsv. |
| Theorem 5.3 (#83) | project | `ZInQKernel/Contrib/OneProof/RC/` and `ZInQKernel/Contrib/CloudB3RC53/` | `hPC` until #90 lands, then `hRC` | #90 | `hRC` rests only on printed results, through pull requests to `main`. |
| Appendix F piece: the weighted ternary theta form at one stage, tex 8206–9100 (branch `wip/rc-appF-theta`; [claim on #83](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6966750889)) | project | `ZInQKernel/Contrib/OneProof/RC/AppF/`, `docs/research/rc-appF-theta.md`, `scratch/rc-appF-theta/` | none of its own; it supplies `aθ` and `Odd.OddStageSource` to `hRC` | the Theorem 5.3 lane's integration branch `rc/thm53-proof-20261117` at `8a63a360` | The construction and its `OddStageSource` proof land on that integration branch with only the standard axioms, or a scoped report names what is missing. |
| Appendix E piece: the actual even form and its phase, the fields of `Even.EvenPhaseData`, tex 7792–8134 (branch `wip/rc-appE-phase`; [claim on #83](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6966750889)) | project | `ZInQKernel/Contrib/OneProof/RC/AppE/`, `docs/research/rc-appE-phase.md`, `scratch/rc-appE-phase/` | none of its own; it supplies the even-phase inputs of `hRC` | the same integration branch at `8a63a360` | The fields land on that integration branch with only the standard axioms, or a scoped report names what is missing. |

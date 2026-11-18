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

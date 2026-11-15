# The discharge check

The discharge check builds an outside contribution and runs a trusted reporter on it, to show which open
hypotheses of `ZInQ.OneProof.frozenTarget` it proves, what it still assumes and which axioms it uses
(`docs/one-proof/CONTRIBUTING.md` is the contract). This directory holds the scripts.

The result is advisory for every file. Contributor code runs during the sandbox build, before the reporter,
with full rights on the runner, so it can forge the result whether or not the scan finds anything. A pass
says what the reporter printed, not that the file is safe or correct.

## Security model

Outside code never runs on a project machine. Lean runs code while it elaborates a file: `#eval`,
`run_cmd`, `initialize`, macros, custom elaborators and tactics all execute during `lake build`, with the
rights of the user who runs the build. Project machines hold SSH keys, GitHub credentials and network
access, so building a pull request there would hand those to its author.

A project machine therefore handles a pull request only as git objects: it reads the diff and the added
files with git plumbing commands, and never checks them out, builds them or runs Lean on them. The build
happens in a sandbox that holds nothing worth taking: a throwaway GitHub repository whose hosted runners
get a read-only token and no secrets, or a disposable container.

Merging is trust. Once merged, a file is built on project machines at every fold, so Jack merges only after
a person has read every added file for build-time code. The check does not replace that read.

## The flow

1. **Scope gate**, on a project machine, on git objects only. `scan_contrib.py` reads the diff between the
   merge base and the pull request's head. Every changed path must be a new file under
   `ZInQKernel/Contrib/OneProof/`: Lean files, or plain-text files such as LICENSE, NOTICE or README.md in a
   helper directory there. A modification, deletion, rename, mode change, symlink, submodule or any path
   outside makes the pull request out of scope: nothing is built, and the comment says so.
2. **Scan** (advisory), in the same run. Each added Lean file is searched for build-time code: every `#`
   command except `#check` and `#print`; commands starting with `run_`, `syntax`, `macro`, `macro_rules`,
   `elab`, `elab_rules`, `notation`, `infix`, `prefix`, `postfix`, `initialize`, `builtin_initialize` and
   their variants; attributes that register elaborators, macros, tactics, delaborators, formatters,
   parenthesizers, compiler passes, linters or native code; the words `axiom`, `by_elab`, `tactic`,
   `native_decide`, `ofReduceBool` and `implemented_by`, and any name starting with `unsafe`; and every
   escaped identifier (a name in guillemets). A hit is "likely" when it lies outside comments and strings as
   the scanner's lexer reads them, and "possible" when it is only in the raw text, so a disagreement with
   Lean's lexer can add hits but never hide one. An unterminated string, comment, escaped identifier or
   interpolation brace is a hit. Matching uses Lean's identifier characters and errs towards false
   positives. `import Lean` is only a note, since Mathlib re-exports Lean.
3. **Prepared commit**, still on git objects. `prepare_commit.sh` builds, with a temporary index and
   `git commit-tree`, a commit whose tree is the base commit's tree plus the added files, with `.github`
   replaced by a single workflow (this directory's `contrib-check.yml`) and a manifest in
   `.sandbox/manifest.json`. Every script and every OneProof module in it comes from the base commit. Its
   parent is the base commit. The commit is pushed to a `scratch/` branch of the sandbox repository (or its
   tree is copied into a container).
4. **Check**, in the sandbox only. `contrib-check.yml` checks the commit out without credentials and fetches
   the Mathlib cache. Its build step runs `discharge_check.sh build`, which builds
   `+ZInQKernel.OneProof.Main`, `+ZInQKernel.OneProof.Discharges` and each added module. Its reporter step
   then sets `DISCHARGE_NONCE` from a fresh random value (no earlier step sees it) and runs
   `discharge_check.sh report`. That runs `#discharges` from a generated `.sandbox/Check.lean` for the log
   (display only), then the trusted reporter `DischargesJson.lean` from the base commit through a generated
   `.sandbox/Report.lean`. The reporter repeats the matching of `#discharges` and prints one
   `DISCHARGE-JSON <nonce> <json>` line per discharging theorem and a summary line, with names inside JSON
   strings, so no name can break a line. `discharges_log.py` reads only lines with this run's nonce and
   rejects malformed records and names with control characters; it also reads the build log for errors and
   for Lean's sorry warning on the added files. The step uploads `.sandbox/out` (the logs and
   `result.json`). The check fails on a build error, on any reported theorem that uses `sorry`, on any axiom
   beyond `propext`, `Classical.choice` and `Quot.sound`, on a rejected reporter line, on a reported theorem
   that assumes the hypothesis it proves (the reporter lists the open hypotheses each theorem's own hypotheses
   match), or when no theorem discharges an open hypothesis. `render_open.py --check` runs too, but only as information: it checks the
   base commit's documents, not the contribution.
5. **Comment**, back on the project machine, with read-only calls. The artifact is downloaded,
   `discharge_comment.py` formats the comment (base and head from the scan, the pull request number from the
   operator, each reported theorem with what it still assumes and its axioms, pass or fail with the reason,
   build statistics, scan hits), the scratch branch is deleted, and the comment is posted through Jack's
   batched run. A `result.json` without the expected shape counts as no result. When any file has scan hits,
   the verdict headline says the result does not count until a person has read those files.

## Sandbox repository settings

Check each of these when the repository is created and after any change to it:

- [ ] Actions are on.
- [ ] Workflow permissions: read repository contents only (the default token is read-only); Actions may not
      create or approve pull requests.
- [ ] Require approval for workflow runs from outside collaborators and fork pull requests (or disable
      Actions for fork pull requests), so a pull request opened against the sandbox itself runs nothing.
- [ ] No repository or organization secrets, no variables, no deploy keys, no environments, no Pages.
- [ ] `main` is the default branch and has no `.github` directory.
- [ ] Apart from `main`, only `scratch/` branches are pushed, each holding one prepared or measurement
      commit, and each is deleted after its run.

Every pushed commit runs its own `.github/workflows`, which is why every pushed commit is either `main`
(no workflows) or a prepared commit whose only workflow is `contrib-check.yml`.

### The long-lived main branch

`main` is a commit whose tree is the base commit's tree without `.github` and whose parent is the base
commit, made by `prepare_commit.sh --sandbox-main`. Since it holds the whole history, each later scratch push
sends only the added files and the manifest, and every scratch branch can be deleted (the default branch
cannot). At each fold, refresh it with the same shape; passing the current `main` as the second argument
gives the new commit both parents, so the push is a fast-forward:

```
bash scripts/one_proof/sandbox/prepare_commit.sh --sandbox-main origin/main sandbox/main
git push sandbox "<printed SHA>:refs/heads/main"
```

For the first push, leave out the second argument.

## The container alternative

The same prepared tree can be checked in a disposable container instead:

- no mounted home directory and no mounted project checkout: the tree is copied in (for example from
  `git archive` of the prepared commit);
- no credentials, no SSH agent, no tokens in the environment;
- network cut after `lake exe cache get`;
- `discharge_check.sh build`, then `discharge_check.sh report` as a separate command with
  `DISCHARGE_NONCE` set to a fresh random value only for that command;
- the container is discarded after each run, and only `.sandbox/out` is copied back.

## Residual risks

- The result is advisory for every file, with or without scan hits. Code in a contribution runs during the
  build in the sandbox, with the runner user's rights (hosted runners allow `sudo`). It can rewrite the
  reporter, the parser, the toolchain or `result.json` before the reporter step runs, and code that runs
  when the reporter imports the contribution can read the nonce. The nonce and the JSON format stop a crafted
  theorem name or a line printed during the build from passing as a record; they do not stop code that
  takes over the runner. A clean scan lowers the chance of build-time code but does not rule it out. A file
  with scan hits gets "This file has scan hits: it may contain code that runs at build time, so a person must
  read it before this result counts.", and the verdict headline says the same. The reader may ask for a
  lean4checker replay of the built oleans; that replay also runs in the sandbox, since it loads the
  untrusted oleans.
- The scan matches tokens, not Lean's grammar. It may flag harmless text, and a file can still do something
  it does not name. That is why every file gets a human read before merge, hits or not.
- A sandbox run uses hosted runner time, and an outside file can make it long. The job limit is 360
  minutes, and a cold build of the OneProof target on a standard hosted runner has not been measured yet;
  see below.

## Measuring the hosted build

A measurement run builds `+ZInQKernel.OneProof.Main` cold (only Mathlib comes from the cache) with no
contribution, so the build cost on a hosted runner is known before the check is relied on:

```
bash scripts/one_proof/sandbox/prepare_commit.sh --measure origin/main
git push sandbox "<printed SHA>:refs/heads/scratch/measure-1"
```

On a `scratch/measure-*` branch the workflow runs `discharge_check.sh measure`, which builds under
`/usr/bin/time -v` with a 345-minute limit and writes `result.json` with the commit, the build's exit status
and whether it hit the limit, wall-clock seconds, the Lake job count, peak memory, and `df` and `free`
before and after. Read it from the run's artifact, then delete the branch. If the build does not fit
comfortably, seed the base commit's oleans only from a trusted build made from the base commit alone on a
project machine and checked by hash, never from a contributor run or its cache.

## Commands

On a project machine (git objects only), with the fork as `origin` and the sandbox repository as the remote
`sandbox`:

```
git fetch origin main "pull/<N>/head:refs/contrib/pr-<N>"
python3 scripts/one_proof/sandbox/scan_contrib.py origin/main refs/contrib/pr-<N> --json scan-<N>.json
bash scripts/one_proof/sandbox/prepare_commit.sh origin/main refs/contrib/pr-<N> <N>
git push sandbox "<prepared SHA>:refs/heads/scratch/pr-<N>"
```

After the sandbox run, download its `contrib-check` artifact (read-only), then:

```
python3 scripts/one_proof/sandbox/discharge_comment.py --scan scan-<N>.json --pr <N> \
  --result <artifact dir>/result.json --run-url "<run URL>" --out comment-<N>.md
git push sandbox --delete "scratch/pr-<N>"
```

`scan_contrib.py` exits 0 in scope, 2 out of scope and 1 on error; for an out-of-scope pull request, run
`discharge_comment.py --scan scan-<N>.json --pr <N>` alone. `python3 scripts/one_proof/sandbox/discharges_log.py LOG`
prints a `#discharges` text log as JSON, for display only.

After any change to `DischargesJson.lean`, check it on a project machine against the base commit alone
(project code only, never a contribution); its own imports are enough:

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
DISCHARGE_NONCE=test lake env lean scripts/one_proof/sandbox/DischargesJson.lean
```

Tests (standard library only, no network, temporary git repositories):

```
python3 -I -m unittest discover -s scripts/one_proof/sandbox -p 'test_*.py'
```

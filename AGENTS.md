# Research review and reporting

Before classifying a mathematical objection, closing a review item, or claiming that a manuscript incorporates an earlier audit, follow [the audit integration protocol](docs/audit-history/PROTOCOL.md).

Read the actual earlier argument, not only its verdict. Keep historical justification and incorporation into the current manuscript separate. Record exact sources, conventions, hypothesis checks, and the consuming passage. If the history has not been checked, say that it is unresolved rather than calling a repair new. A passing structural or computational check is not proof of the arithmetic theorem.

For every changed theorem application, compare the source's required inputs with the objects actually constructed. Explicitly check index-set coverage, transition maps and the identity of the object consumed downstream. Review a changed route anew even when its conclusion was accepted earlier. Follow the contract and independent-acceptance requirements in the protocol; do not let a historical approval authorize a revised argument.

Run `python -B scripts/check_audit_history.py --self-test` after changing the register, current manuscript, application contracts or their bound sources. This checks both immutable history and current acceptance. Do not refresh hashes merely to silence a failed check; review the changed application first. Never generate an independent approval on behalf of a reviewer. User instructions take precedence. This protocol introduces no additional permission requirement.

# Working on DZQ in this fork

Chey Loveday’s fork is for research, review, and preparing contributions. The
active formal proof is maintained in Jack McCarthy’s fork. For a manuscript
correction, follow the original repository’s contribution route. Review the
destination’s current instructions before preparing a submission.
[Jack’s contributor guide](https://github.com/Deicyde/diophantine-z-q/blob/main/CONTRIBUTING.md) ·
[One-proof guide](https://github.com/Deicyde/diophantine-z-q/blob/main/docs/one-proof/CONTRIBUTING.md) ·
[Original repository](https://github.com/elliotglazer/diophantine-z-q)

## Scope and placement

- Check the live [open list](https://github.com/Deicyde/diophantine-z-q/blob/main/docs/one-proof/OPEN.md), the [claims issue](https://github.com/Deicyde/diophantine-z-q/issues/14), and related PRs before starting a contribution. For an upstream board contribution, claim one unheld field at a time until the first merge, using its exact name and starting commit. For work in a project-owned lane, follow the maintainer’s agreed scope, base and directory. A draft on this fork is for internal review.
- Keep research notes, computational checks, and archival snapshots with their provenance. For a mathematical claim, state the exact hypotheses, object, and remaining implication. For a computation, distinguish discovery from verification and retain the checker, input hashes, output and adverse cases. Preserve source snapshots and record what the current consumer actually uses.
- Put a standard OneProof submission in new files under `ZInQKernel/Contrib/OneProof/`. Import the module that owns the target and reuse its definitions. Keep `OneProof.Main` imports in scratch checks. Supply the exact named theorem or the exact conditional reduction. Keep the target, existing assembly, toolchain and dependency pins intact. Put review notes, scratch checks and receipts on the review branch or link them from the PR body. Jack’s automatic contribution check applies to PRs into his `main` that only add OneProof files.
- For a reduction to printed statements, use genuine definitions and record the edition, page and display actually read. Mark unread locators `UNVERIFIED` and AI readings `AI-READ`. Follow the project’s distinction between refereed statements and glue. Preserve notices and source credit when porting code. [Statement checks](https://github.com/Deicyde/diophantine-z-q/blob/main/docs/one-proof/STATEMENT-CHECKS.md)

## Lean and evidence

- Run Lean through the existing odProof Modal runner. Keep source and small receipts locally. Keep Lake builds, dependency caches and large exports on the hosted worker. Reuse the submission script and a compatible verified cache. Check the base, source hashes, target/import paths, scratch files, and resource bounds before allocating a VM. Keep failed receipts. After a disconnect, check the original VM and recover its run before retrying.
- Build by module name. Use an explicitly typed example for the actual downstream endpoint, then collect `#print axioms` for the named declarations. The project permits `propext`, `Classical.choice` and `Quot.sound`. Proof files must be free of placeholders, new axioms, bypasses such as `native_decide`, and build-time code. Keep the whole-project `#discharges` reporter in a separate scratch file and report its remaining premises. Follow the receiving lane’s requested gates.
- Give the base, checked revision or source digests, actual commands, outputs and known limits in the PR. Distinguish source review, finite computation, focused Lean checks, the board reporter, protected statement comparison, external kernel replay and upstream acceptance. State which AI tools or models were used, what they did, and what the named operator or an independent reviewer actually checked.

## Restricted converse

Jack’s [coordination thread](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-7015365311)
and [review of #160](https://github.com/Deicyde/diophantine-z-q/pull/160#issuecomment-7037255756)
specify the integral trace contribution: use the actual local complex at every
finite place, with the sign-line proof and its compatibility in separate
modules. The requested finite-coefficient follow-up is a separate PR based on
Jack’s `main` after #160 merges. Use the literal finite `localCx` and its
differential, name the trace input removed at the `NekovarProp524` consumer,
and include a build, exact endpoint check and axiom audit.
[Maintainer request](https://github.com/Deicyde/diophantine-z-q/pull/160#issuecomment-7037303590)

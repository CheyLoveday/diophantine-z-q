# Focused review 3: PR structure, base and evidence

Date: 2026-11-08. Reviewer: `/root/review_pr_structure`, non-author internal model reviewer. This was a read-only inspection of Git history, live remote refs, the new sources and documentation, and retained verification records. I made no edits, ran no builds or tests, and changed no refs or remote state. This is a packaging and claim-scope review, not independent mathematical or kernel certification.

**Decision: accepted for research-branch delivery within the stated conditional scope. No blocking structure or evidence-packaging finding remains.**

The appropriate review base for this increment is `e653d6ff295ae4e0535710a7d64aa255d294d211`. The branch already contains 13 research commits and 245 added files beyond `main`; describing the full branch-to-main comparison as a small arithmetic-bridge PR would be misleading. Live read-only lookup during this review found public-fork and upstream `main` at `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`.

`PR.md` correctly recommends a foundational algebra/verification contribution against upstream `main`, followed by this dependent arithmetic bridge. It authorizes no upstream PR creation or merge. The current delivery should remain a commit and push to the existing public research branch, followed by readback of its exact remote commit.

The incorporation structure is sound. `manuscript-insertion.tex` is the sole editable addendum authority; `proposed-v13.patch` is explicitly generated and identifies its source, command and hashes. `APPLICATION.md` gives an exact V13 replacement anchor and affected consumers. The documentation consistently distinguishes addendum incorporation from canonical manuscript incorporation and leaves the existing acceptance registry untouched. It avoids introducing a second editable full manuscript.

The formal scope is also explicit. `ArithmeticBridge.lean` imports the unchanged core and derives normalized identities through a retained-duality interface. The application crosswalk exposes the inherited arithmetic, boundary, class, row and model-realization obligations. The README and proposed PR do not present this as a Lean construction of arithmetic Selmer complexes, Poitou–Tate duality, or determinant functors.

The native evidence identifies nine audited declarations, five freshly compiled modules, pinned tool/dependency versions, exact inputs and artifact hashes, commands and exit statuses. Its records explicitly exclude protected comparison, export replay, external kernels and paranoid verification. The new module’s retained compiler output is empty; the axiom log ends with all nine targets audited. These are inspected execution records, not reviewer reruns.

The preservation receipt records the 128 prerequisite entries and 99 current entries, with generated 39-project manifest `117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`. The `OPENMATH.md` change only scopes the older arithmetic-open status and links the later work; it expressly excludes the new declarations from the running packet.

One initial packaging omission was resolved: `evidence/insertion-check.json` now records fresh byte-identical patch generation, successful `git apply --check`, unchanged canonical source, and that the patch was not applied. Typesetting is correctly marked not run.

The reviewed final bytes are:

| File | SHA-256 |
| --- | --- |
| `PR.md` | `1030a8805d4f607efe9301a66f455fa119a3131291da32c82977ebd80abb44f3` |
| `README.md` | `53d038153d803cce757dcfc6b05c2ad54315996d19ac941565256733a06af2b5` |
| `OPENMATH.md` | `0e5dffac1aea0c2f654d0f2119d3d60c978fdca30d08c3384e9d172e74fbc4ed` |
| `evidence/native/RESULT.json` | `57bb68c3b89b728a9603b3a6bb947c23e3f4b5d34971ccd51f83985afb08c17c` |
| `evidence/preservation.json` | `e17b2358c7521088463a0842127fa403ccc2a600cddf5011ba1679988e47ed74` |
| `evidence/insertion-check.json` | `49dcf8d3f9653afdafc6662d30d914c8ddbf3c2b644f2fbaf5f0f33651dd324c` |

Paths other than `OPENMATH.md` are relative to `research/arithmetic-boundary-cup/`. Final review-index assembly and commit/push confirmation remain delivery steps; no completion of those steps is claimed here.

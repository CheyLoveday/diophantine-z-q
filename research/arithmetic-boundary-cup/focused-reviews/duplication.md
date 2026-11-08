# Read-only duplication and value review

Date: 2026-11-08. Reviewer: `/root/review_duplication`, internal Codex model agent. Base: `e653d6ff295ae4e0535710a7d64aa255d294d211`.

**Verdict: accepted within this review’s scope; no blocking duplication or contribution-structure finding.**

I inspected the new Lean module, current README, application/specification/verification records, insertion source and generated patch, proposed PR description, native evidence record, and Open Math documentation change. I performed read-only inspection and hashing. I did not edit files, run builds or tests, independently reproduce the native evidence, or certify the underlying arithmetic constructions.

| Reviewed file | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitch/ArithmeticBridge.lean` | `2b72fc4237d45feb84973e470f0887c3ef3768cfaaedec967857a4ca01c09ef6` |
| `research/arithmetic-boundary-cup/README.md` | `5d5f1dcb98dfdda2b541452a4df84150a21c9a0e5e937850102fab61fc6b5795` |
| `research/arithmetic-boundary-cup/PR.md` | `b31686b343b168866f32a43c3c303c31877d5e8909d2676981e1932b58d4e47d` |

The new contribution has distinct value. It includes the crossed-cocycle conjugation identity with its coboundary term, the shared integral transport-unit consequence, the pure-boundary cone calculation, the specified orthogonal-partner localization, and the derivation of the normalized same-row boundary identities. The final theorem reuses `integral_boundary_cup_adapter`; it does not introduce another determinant engine or merely rename an assumed \(c_F=-c_S\).

The remaining inherited inputs are visible. In particular, `boundary_adjoint`, `conjugate_local`, and the class/row/boundary realization equalities remain an explicit arithmetic interface. `APPLICATION.md` and `FORMAL_SPEC.md` explain their source-level meaning. The contribution is correctly presented as a conditional arithmetic-facing bridge, not a formal construction of Galois/Selmer cohomology or determinant functors.

The document structure resolves the earlier duplication concerns. `manuscript-insertion.tex` is the sole editable publication authority for the addendum; `proposed-v13.patch` is labelled generated and records its source hash and generation command. The earlier derivation and review are preserved as frozen research records. The current README supplies one reader route instead of asking readers to infer current status from historical packets.

The six-, 21- and 39-target layers remain useful provenance and reusable algebra, but they should not be advertised as three independent arithmetic verifications. The current README and PR description make that distinction and preserve their historical statuses. No deletion or refactoring of frozen material is recommended.

The new local verification driver is appropriately narrow. It does not establish a fourth cloud/comparator project. The finite checker remains supplementary; its double-\(J\), omitted-tame-sign and nonunit-rescaling controls are more informative than the numerical case count. The native evidence records named declarations, source/dependency identities and explicit unrun gates rather than treating the existing cloud run as verification of the new module.

The proposed review base is also appropriate: compare this delta to the frozen handoff commit, not directly to `main`. The PR document correctly explains that a `main` comparison includes the preceding 245-file research history and recommends two logical future contributions without rewriting that history now.

One nonblocking wording improvement remains: “They are related by the integral unit \(-1\)” would be preferable to the README’s literal “Their ratio is…” because the formal interface includes zero normalizers. The existing sentence is defensible in the ordinary actual/nonzero arithmetic context, so this does not alter the verdict.

## Final-byte acknowledgment

I inspected the revised README, PR description and insertion-check receipt read-only. The README now uses the division-free unit relation, and the PR evidence route links the generation/check receipt. These changes resolve the wording suggestion and improve evidence navigation without changing the mathematical or formal scope.

Updated SHA-256 bindings:

- `research/arithmetic-boundary-cup/README.md`: `53d038153d803cce757dcfc6b05c2ad54315996d19ac941565256733a06af2b5`
- `research/arithmetic-boundary-cup/PR.md`: `1030a8805d4f607efe9301a66f455fa119a3131291da32c82977ebd80abb44f3`

The Lean module remains unchanged at `2b72fc4237d45feb84973e470f0887c3ef3768cfaaedec967857a4ca01c09ef6`.

**The accepted verdict is retained for these final bytes within the original duplication/value review scope.** No files were edited and no builds or tests were run by this reviewer.

# Non-author review of the retained local-conjugation limit

### 1) Verification target

**Accepted within the explicit retained-source scope.** The argument in `DERIVATION.md` §4 establishes one integral transport unit for every class in the specified retained limiting model. It does so without assuming cohomology commutes with nonflat coefficient reduction, stagewise coherence of the moving characters, or equality of a fixed natural prime with $-1$ in characteristic zero.

Date: 2026-11-08. Reviewer: Codex model agent `/root/review_pr_structure`. I did not author the new Lean modules or the arbitrary-limiting-cycle clarification. This is a separate non-author model review, with shared-context/model limitations; it is not human specialist acceptance.

I read the actual V13 coefficient and conjugation construction, H22, the moving-character disclaimer at lines 4456–4464, and the finite-model/inner-limit argument at lines 4577–4636. I also inspected both new Lean files, the application/specification, Mathlib’s actual `H1π` implementation and kernel API, and the published Nekovář tame-group formulas at §§7.1.1–7.2.1. Earlier review verdicts were not substituted for these sources.

The decision binds:

| File | SHA-256 |
| --- | --- |
| `MANIFEST.sha256` | `0ea39b7725cce044dc41ba586b552a6dabe2d5e4647c9c239d27709c0272a711` |
| `DERIVATION.md` | `ad679e62e29d97e2752a683e5c9de1ea9cf244002f76c57a716d9237654e10e0` |
| `APPLICATION.md` | `20b4a52e556a8a238b45a191f0f595b2f366042f0594c638c40919a6a3801b77` |
| `SPEC.md` | `c98bcf33bda7d31fb5f7e1fb013b99a6a7e01585f75b657e7f8e3ab15d365c62` |
| `ConjugateLocalTransport.lean` | `8688eef27fcc89c02eb3ab270e5359534dc23ef16e11678bdb1dd3587e3f8b86` |
| `ConjugateLocalH1.lean` | `078ac50ae0c90c8e609a57c51c5884a25646ad7305531f1cf531617485b9078f` |
| `evidence/native/RESULT.json` | `b047f06bdd83c1d02455eaaa1ee775031e67e91f51d0b03707786b7a46c94d9e` |

Document paths are relative to `research/conjugate-local-transport/`; Lean paths are relative to `lean/Research/DerivativeSwitch/`. V13 remains `9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.

### 2) Independent re-derivation (outline)

**The finite identity has the required quantifier.** The representation and transporter determine $u_i=\alpha_i(d_i)^{-1}$, independently of the cocycle. H12 derives the trivial Tate contribution; local triviality removes the crossed-cocycle coboundary term. The finite and tame coordinates therefore use the same unit for every cocycle on those data. The formal pullback correctly targets the conjugate coefficient representation. Its descent through Mathlib’s `H1π` uses actual coboundary invariance, not an invented abstract class carrier.

**The fixed ultrafilter preserves an integral unit.** At each fixed precision the coefficient ring is finite. The already-fixed ultrafilter selects unique residues of $u_i$ and its inverse. Intersecting their selected cells with the sufficiently large precision tail preserves both inverse identities. Reduction between precisions preserves the selected value by uniqueness. Thus the compatible limits satisfy $uv=vu=1$. Adding these entries cannot change previously retained matrix entries, because no different ultrafilter or new choice of their selected values is introduced.

**The arbitrary-cycle extension is valid.** Fix a limiting cycle $z$ and precision $n$. Its reduction $z_n$ is a cycle in the limiting reduced matrix complex. On an ultrafilter-large set, the stage ranks, differentials and relevant finite comparison matrices agree with those retained matrices modulo $n$. Consequently the same vector $z_n$ is a cycle in a selected stage model after tensoring to $R_n$. This does not require lifting it to a cycle over the larger stage ring.

The actual inclusion/projection/contraction identities survive tensoring because they are chain identities. Continuous finite-coefficient cochains commute with this reduction: their underlying modules are filtered colimits of finite function modules on clopen partitions, and tensor product commutes with those colimits. The reduced inclusion therefore supplies an actual continuous reduced cocycle. The finite local theorem applies to it at precision $n$; the corresponding common finite quotient may be chosen for that cocycle. Its unit remains the one fixed by the representation and transporter, rather than a cocycle-dependent choice.

The retained local and conjugation comparisons identify its coordinates with the matrix coordinates. Comparison homotopies contribute coboundaries, whose relevant evaluations vanish. Thus the identity holds for $z_n$. As $n$ was arbitrary and the coefficient ring and finite free coordinate modules are separated, it holds for $z$. Passing to classes is legitimate by the established representative independence.

This proves the universal local statement without an $H^1$ base-change surjectivity assertion.

### 3) Checks

- The argument uses fixed support/binary family and the source’s bounded model ranks. It asserts no bound over all supports.
- The stage coefficients are finite Artin rings, including the fixed finite group-ring case. No division by two or nonzero/primitive-vector assumption enters.
- The source explicitly permits noncompatible moving characters. The proof retains their scalar values; it constructs no nonexistent limiting Galois character.
- The finite tame relation is used only after the common quotient removes wild inertia. The source’s odd-prime/local-triviality conditions justify that quotient.
- I recomputed the manifest hash and all **25** listed file hashes; all matched. I inspected the native record but ran no Lean, tests, cloud job or external checker.
- The native record covers only the two new modules and 27 audited roots. It does not provide formal verification of the retained-limit argument.

### 4) Discrepancy report

No mathematical correction is required within the stated scope.

I compared the retained pre-editorial derivation with the final version. The four changes only restore parentheses and math delimiters in `c_tau(p)`, `f(p)` and `s(p)`. They do not change the statement, assumptions or proof. I acknowledge the new binding recorded in `evidence/EDITORIAL_BINDING.json`, SHA-256 `5d7a25cb5e4161214f059637cd3acf312b73263d539eda7398e67135c6a796ce`. The original native result and compiled proof sources remain unchanged; no new proof execution is inferred.

### 5) Certification result

**CERTIFIED under the named finite-model and retained-inner-diagram assumptions**, in the limited sense of internal non-author mathematical review: the explicit shared unit survives the same retained ultrafilter, and the local-conjugation identity extends to every limiting class through reduced contraction maps.

The result supplies the local-conjugation shared-unit application for the specified retained model. Later global boundary–cup adjunctions, orthogonal comparison inverses, common-strict realizations, actual functional rows, determinant-functor compatibility and localization occurrence remain separate obligations. Unit preservation under later ring maps does not identify those objects automatically. The packet states these limitations honestly and does not establish that the full arithmetic determinant switch is repaired.

# Finite-Hopf annihilator source port — provenance and adaptation log

## Scope and status

This directory contains a **source-only, uncompiled** port of the whole finite-Hopf annihilator proof branch from `openai/math`, plus a wrapper on actual Mathlib group schemes. It does not prove the full isogeny quasiinverse target by itself. No compiler result, elaborated axiom report, or discharge result is asserted here.

Source preparation date: 2026-11-15. The source port is AI-assisted (Metamate), with independent source reading of the complete seven-module rank-annihilation closure. Independent source reading is not independent compilation or human mathematical review.

The source worktree base read before writing was `Deicyde/diophantine-z-q@9b3f414e3c29ca692d384630db0b4ebd9a7b4322`. The existing target definitions, assemblies, unrelated contributions, and dependency pins are not part of this port's edit scope.

## Immutable upstream source and license

Repository: https://github.com/openai/math

Revision: **`4eaee87548250b2682affda7d05d947c05554bae`**.

Upstream README at this revision describes model-produced proof artifacts at differing verification stages. No individual authorship or verification status is inferred beyond what that source states.

The adjacent `LICENSE` is the byte-preserved upstream root Apache License, Version 2.0, January 2004, including its original appendix/template text:

- Immutable source: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/LICENSE
- Git blob SHA-1: `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`
- SHA-256: `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`

Original file text and docstrings are retained below the added per-file provenance banners. This notice records source metadata and adaptations, not a legal or compliance assessment.

## Per-file upstream identities

Every path below is relative to the upstream repository. The corresponding local source path is obtained by replacing leading `lean/OAI/` with `Vendor/OAI/` under this contribution directory.

| Upstream path | Git blob SHA-1 | SHA-256 |
| --- | --- | --- |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/RankAnnihilation.lean` | `287848159537c3f564cb7231d586a2aab3a4977c` | `9154c34abfcfd42eb1eef822fb2e7c3e27532ee1d709c42276875594c105d924` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/HopfShear.lean` | `e6653376d31e4b4018473972773bbd40f981131f` | `5dec46551e6a7b45d1c37c916325ae2937c0e5b677ebdb2e06832fa240b7a95c` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/NormCharactersEq.lean` | `bce73e78700f482ddcbd354a3bc95aa6c653fb26` | `834beed44e7298b8bdbbb772894dedaaf37f7a8ac3dd5ca596cdd08efd93a1a7` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/CharacterGroups.lean` | `cf6520e086a45a76b7e9070238300372049f956d` | `bfc279ad3e9f6bc78900ec8442613ea341019805871e5c0498278ffe41101bf9` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/Characters.lean` | `c5a64751025ea6bbcadb07133ade7128d38f39e4` | `130658ccb408c42ef704dc5216dd8427fb47015aff2fbf09a933474996117e0f` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/Naturality.lean` | `d9d48cbc25cdc384659463feea48a4ee1a0215a2` | `e4fa11e3c6ae05ec92e2072a2544ee5dcd0869be457b6d110e72978394a69408` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/DualAlgebra.lean` | `aa2c37f5d27e1dad01e055b20431a624a666fcec` | `e1879f7703fea7b2cc43b4622add65e25363a50dbd6a9f5062258a63c9f2c5f7` |
| `lean/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` | `4412c863798a4a88c0882be70aaf1eccb24ef300` | `90eafc894034a82518f0f3f20328e1b43ab1ae115ad4f87a7062d39095efc2e3` |
| `lean/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean` | `260714323bd22e89689b30e59b7df503659490ad` | `28100a234b0415307dc09c4a6d97152f307058ce3b7f744ac50f44d7228f1612` |

Immutable file URL pattern: `https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/<upstream path>`.

## Adaptations

Only these source adaptations are intended in the first conservative port:

1. Add an attribution/provenance banner containing the immutable revision, upstream path, Git blob SHA-1, SHA-256, and source-only status.
2. Relocate every foreign `import OAI.…` to `import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Vendor.OAI.…`.
3. Relocate all upstream OAI namespace declarations, named `end` clauses, and explicit qualified references from `OAI.…` to `MilneQuasiInverse.Vendor.OAI.…` consistently. Canonical Mathlib `_root_.CategoryTheory`, `_root_.AlgebraicGeometry`, algebra, and group carriers remain untouched.
4. Add `GroupAnnihilator.lean`, a small wrapper exporting `ZInQ.Contrib.MilneQuasiInverse.finiteGroup_exists_annihilator` by applying the relocated upstream theorem.
5. Header-order repair (2026-11-15, independent review B1): change only the first-line added-banner opener from `/-!` to ordinary `/-` in `Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` and `Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean`. Ordinary comments can precede imports; module-doc comments are body commands. Existing module-doc comments after the imports and every import/proof-body byte are retained. A narrow static header preflight accepts all ten owned modules and rejects the reconstructed original banners; no Lean parser/compiler was executed.

Current destination SHA-256 values for the two header-repaired files (upstream hashes above remain unchanged):

| Vendor path | Destination SHA-256 |
| --- | --- |
| `Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` | `6e2fc6d5da9d35bff10fe52765c7cb73bf121db38a5626128698d300f4ebacf5` |
| `Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean` | `28dde398c83403dd1011f341ce0b311daa4912b6d5a606c4755836b20e79a985` |

No pruning of the seven-module rank closure, mathematical proof-body change, dependency upgrade, new Lake dependency, replacement target structure, root/Source alias, supplied-annihilator hypothesis, or extra flat/quotient premise is intended. Any later elaboration compatibility edit must be recorded separately in this adaptation log.

The copied upstream `set_option` directives are retained as source. They have not been exercised by this port preparation.

## Exact finite-Hopf import graph

All foreign imports are contained in this nine-file Vendor subtree; every other import is a named existing Mathlib module.

```text
GroupAnnihilator.lean (public wrapper)
  Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator
    Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation
      Mathlib.AlgebraicGeometry.Group.Affine
      Mathlib.AlgebraicGeometry.Morphisms.Finite
    Vendor/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/RankAnnihilation
      HopfShear
        NormCharactersEq
          Mathlib.RingTheory.Norm.Basic
      CharacterGroups
        Characters
          DualAlgebra
        Naturality
          DualAlgebra
      Mathlib.LinearAlgebra.Dual.Basis
```

The nine upstream modules total 1,566 physical source lines before added banners; the whole seven-module rank branch is retained. `DualAlgebra` constructs the finite-projective convolution Hopf dual and bidual with their laws; it is not a structure storing an assumed answer. The rank theorem uses an explicit Hopf shear/norm calculation, and its conclusion is an equality of actual scheme multiplication morphisms after treating all algebra-valued points.

## Wrapper contract

The exported wrapper is on the existing Mathlib `Grp (Over (Spec K))` carrier:

```lean
ZInQ.Contrib.MilneQuasiInverse.finiteGroup_exists_annihilator
  (K : Type u) [Field K]
  (G : Grp (Over (Spec (CommRingCat.of K))))
  [IsCommMonObj G.X] [IsFinite G.X.hom] :
  ∃ n : ℕ, 0 < n ∧
    ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X), x ^ n = 1
```

It has no characteristic-zero, perfect-field, algebraic-closedness, reducedness, finite-flatness, quotient, or supplied-annihilator hypothesis. Powers use the internal group law on Hom. The quantifier covers actual scheme-valued tests, including infinitesimal tests, not only rational or geometric points. `n` is the positive finite-Hopf coordinate rank provided by the copied proof.

## Dependency and validation boundary

Target unchanged pins: Lean `4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Original upstream pins read: Lean `4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Static source inspection found the needed current norm, finite-projective contraction, convolution, affine/Hopf, and fpqc interfaces. That is not an elaboration certificate. Compatibility of every old-version structure construction, typeclass inference, simp lemma and transparency option remains unrun.

No Lean/Lake/native compiler, upstream hooks, downloaded compiled artifacts, cached foreign binaries, or old source acknowledgments were used. The parent owns any future isolated validation, exact kernel/isogeny assembly, claims, commits, PRs and publishing. This annihilator subtree does not include Flatness, RingFlatness, Kernel, Descent or Main source work owned by other agents.

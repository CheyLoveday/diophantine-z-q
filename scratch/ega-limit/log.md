# ega-limit results log

Target: field `egaIV_8_10_5_xii : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`
(`ZInQKernel/OneProof/H/TailX.lean` L170; statement `ZInQKernel/Contrib/SpreadOut/Spread.lean` L49).

## Findings (2026-11-16)

- VERIFIED (read): AxiomMath/Stacks at c496df0d (same revision CloudW01Spread vendors; local read-only copy
  `~/cloud-b3/w16/sources/stacks`, `git status` clean, sha of StacksCore/Tactic/StacksAttribute.lean matches
  CloudW01Spread's manifest) proves Stacks 081F in `Limits/EventuallyProperOverLimit.lean`, but through
  absolute Noetherian approximation (`FiniteTypeApproximation`) and Chow over a qcqs base: file import
  closure 1761 files / 513k lines. Not portable.
- VERIFIED (read): the same repo has the conditional form
  `exists_isProper_baseChange_of_isLimit_of_hasChowModification` (`ProperLimitStage/Basic.lean`, Stacks 081F
  given Chow's conclusion for `f₀`), `hasChowModification_of_hasSegreEmbeddings` (Chow over an affine
  Noetherian base given Segre, `Limits/ChowLemmaNoetherian0200.lean`), Segre 01WD over any base
  (`SegreProdIso/Main.lean`, `exists_segreEmbedding`), 01ZQ (`Limits/DescendingMorphisms/Diagonal.lean`).
  Import closure of these four, minus the 13 modules CloudW01Spread already vendors: 73 files, 21.3k lines.
  No `sorry`/`axiom`/`native_decide` in them (grep; hits are the word "admits" in comments).
- Route (no Chow over a non-Noetherian base, no absolute Noetherian approximation):
  1. 01ZQ makes `X` separated at a stage `j₁`; re-index there.
  2. `p : Y₀ = ∐ Uₖ → S₀` the disjoint union of a finite affine cover of `S₀ = D j₁` (affine, surjective, flat, qc).
  3. Chow for `X₀ ×_{S₀} Y₀ → Y₀` (affine, non-Noetherian base): approximate `Γ(Y₀)` by its finitely generated
     ℤ-subalgebras (CloudW06's `AdjoinFinset.isLimitSpecCone`), descend by 01ZM(1) (CloudW01), make separated
     by 01ZQ, apply Chow over the Noetherian affine stage, base change back.
  4. Stacks 081F-given-Chow for `f₀ : X₀ ×_{S₀} Y₀ → Y₀` over `S₀`: some stage `j` where `f₀`'s base change is proper.
  5. Universal closedness descends along the surjective flat qc `D j ×_{S₀} Y₀ → D j` (Mathlib FlatDescent);
     separated + lft at `j` by base change; so `X_j` proper; transport to `Xi`'s base change along `j → i`.

## Vendoring

- `scratch/ega-limit/vendor.py ~/cloud-b3/w16/sources/stacks` wrote 73 files under
  `ZInQKernel/Contrib/OneProof/EGAProperLimit/` (+ LICENSE byte-identical to upstream, SOURCE_MANIFEST.json with
  sha256 of each source); imports of the 13 CloudW01Spread modules point there.

## Compile log
- build1 (plain import remap): 2 of 73 files failed (`SegreEmbedding/SegreRing.lean` L171 instance synthesis,
  `Limits/AffineIntoProjective.lean` L267 instance mismatch). Cause: upstream lakefile leanOptions
  `maxSynthPendingDepth = 3` (project default is lower). VERIFIED fix: vendor.py inserts
  `set_option maxSynthPendingDepth 3` after the imports of every vendored file.
- build2: `lake build` of the three tops + Spread + CloudW01 FinitePresentation/Smooth + CloudW06 AdjoinFinset:
  "Build completed successfully (9150 jobs)", 1m51s wall. VERIFIED.

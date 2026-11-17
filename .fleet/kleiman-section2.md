# kleiman-section2 (fleet note)

**Result.** The leaf `kleimanPicZeroProper` is replaced by
`KleimanSection2.KleimanPicZeroProper954`, which states Kleiman, *The Picard scheme*, Thm 9.5.4, under its own
hypotheses. The abelian-variety consumer is proved from it in Lean. File:
`ZInQKernel/Contrib/OneProof/KleimanPicZero954.lean`. It builds, has no sorry and uses only the standard axioms.

**The leaf.** The hypotheses on `X` are:
- a closed immersion into `ℙ^N_K` over `K` (projective);
- `GeometricallyIntegral`;
- geometrically normal after every field extension;
- a `K`-point.

The conclusion covers every `P` that is locally of finite type over `K` and represents the tree's `picardFunctor`
restricted to locally Noetherian `K`-schemes, which is Kleiman's test category. For any such `P`, every open on the
connected component of the point classifying `𝒪_X` is proper over `K`. Rated **printed form**: it is 9.5.4 plus extra
hypotheses, which only weaken it. The comparison with Kleiman's `Pic_{X/k}` goes through Yoneda on locally Noetherian
schemes, using 9.4.8. Kleiman's remark after Def. 9.2.2 means no `Pic(T)` quotient is needed.

**Glue proved.**
- `repLN` / `identityComponentLN_repLN` (step (a)): a representation over all schemes restricts to locally Noetherian
  test schemes, and gives the same identity component.
- `isClosedImmersion_of_proper`.
- `picZeroProperAt_of_954` and `picZeroAbVar0_of_954`. Projectivity comes from the vendored GrpObj immersion lemma,
  normality from smoothness, and local finite type from `picLocFinType_proof`.

Step (b), EGA IV 6.7.7, is not needed: the leaf's normality hypothesis is the stronger one, and the consumer proves
it.

**Fold.** A hand fold is needed because the new leaf is weaker than the field. `scratch/kleiman-section2/TailZ56.lean`
defines `OpenAddedLeaves26` and `sixContactMin_of_open49`, which go to `OpenAddedLeaves22PZ`. It supersedes
kleiman-section's draft. `autofold.json` records the leaf row and is not runnable. Counts: −1 GLUE, no new GLUE.

**Remains.** Kleiman's numbering and hypotheses are as reported in the brief; there is no copy on the host, so they
are UNVERIFIED. The claim that restricting the fppf sheafification to locally Noetherian schemes gives the
sheafification there is argued, not formalized. FoldCheck and `#discharges` outcomes are in
`scratch/kleiman-section2/log.md`.

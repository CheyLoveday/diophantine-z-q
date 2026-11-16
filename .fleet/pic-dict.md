# pic-dict (the three Pic-dictionary rows), status

**Main result.** `weilPairingMumford` is **replaced by 7 printed leaves plus Lean glue**: −1 strict and −1 strictest
GLUE on the lf31 rating (autofold dry-run `37/11 -> 44/10; strictest 37/11 -> 44/10`; on this base `40/8 -> 46/8;
strictest 39/9 -> 46/8`, no `--allow-rise`).
- The leaves are Mumford's displays over an algebraically closed field `k`, for `X : AbVar k`, with Mumford's `Pic⁰`
  (translation-invariant classes) and Mumford's `ē_n` formula: §6 Cor. 4, §8 (iv), §8 Thm 1, §20 (bilinear and
  well defined; nondegenerate), §23. The seventh is EGA II 4.6.13 (ample under field extension).
- The field `phiAmpleIsogeny` stays as an input.
- All glue is proved in `ZInQKernel/Contrib/OneProof/PicDictionary.lean`, which builds with standard axioms:
  - **L5** (fppf sieves at `Spec K̄` are maximal, by the Nullstellensatz);
  - the base change to `A_K̄` (translations, `n_A`, points as groups);
  - the dictionary `B(K̄) ≅ Pic⁰(A_K̄)`;
  - **transport of Mumford's formula**: pseudofunctor coherence, and `𝒪`-pull-back versus `pullbackComp`. This
    proves the Galois, adjoint and compatibility clauses, so they are not leaves.
- `#discharges` reports `[OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_ac` and
  `[OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_of_ac`. Spec: `scratch/pic-dict/autofold.json`.
- `phiAmpleIsogeny`: reduced, all glue proved, including `finiteOfFiniteKerPts` (finite kernel on `K̄`-points ⇒
  finite). It still needs the composite leaf `picZeroPtsTranslInv` (`K̄`-points of the identity component of
  `Pic_{A/K}` are translation-invariant; Kleiman 9.5.10 + Mumford §8), so its count is 0
  (`scratch/pic-dict/autofold-both.json`).
- `picZeroAbVar`: not reduced. The combined step is "`Pic⁰` of the fppf Picard scheme is smooth and proper", which
  needs Mumford §13 identified with the identity component, plus descent from `K̄` (report §5). Smoothness of `B` is
  two theorem steps (report §3).

**Remains.** Reading Milne 1986 §10 / BLR 8.4 may give one print for `picZeroPtsTranslInv` (then `phiAmpleIsogeny`
is −1 too) and for `picZeroAbVar`. All locators UNVERIFIED. Optional Lean: `AmpleBaseChangeAlgClosure`.

Report: `docs/research/pic-dict.md`; log `scratch/pic-dict/log.md`.

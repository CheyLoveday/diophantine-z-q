# pic-dict (the three Pic-dictionary rows), status

**Main result.** `weilPairingMumford` is **replaced by 9 leaves plus Lean glue**: −1 strict and −1 strictest GLUE on
the lf31 rating (autofold dry-run `37/11 -> 46/10; strictest 37/11 -> 46/10`; on this base `40/8 -> 48/8; strictest
39/9 -> 48/8`, no `--allow-rise`). The leaves are Mumford's displays at `X = A_K̄`: §6 Cor. 4, §8 (iv), §8 Thm 1,
§20 (×4), §23, and EGA II 4.6.13. The field `phiAmpleIsogeny` stays.
- `ZInQKernel/Contrib/OneProof/PicDictionary.lean` builds, standard axioms. `#discharges` reports
  `[OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_printed` and
  `[OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_of_printed`.
- Proved in Lean along the way:
  - **L5** `PicPointsAlgClosed` (fppf sieves at `Spec K̄` are maximal, by the Nullstellensatz);
  - the dictionary `B(K̄) ≅ Pic⁰(A_K̄)`, with `φ_L`, `f^∨` and `σ` on points;
  - **the Galois clause**, by transport of structure: pseudofunctor coherence and `𝒪`-pull-back versus
    `pullbackComp`;
  - `FiniteOfFiniteKerPts` (homomorphism with finite kernel on `K̄`-points is finite).
- `phiAmpleIsogeny`: reduced with all glue proved. It still needs the composite leaf `picZeroPtsTranslInv`
  (`K̄`-points of the identity component of `Pic_{A/K}` are translation-invariant; Kleiman 9.5.10 + Mumford §8),
  so its count is 0. Spec `scratch/pic-dict/autofold-both.json` folds both rows.
- `picZeroAbVar`: not reduced. The combined step is "`Pic⁰` of the fppf Picard scheme is smooth and proper", which
  needs Mumford §13 identified with the identity component, plus descent from `K̄` (report §5). Smoothness of `B`
  takes two theorem steps (report §3).

**Remains.** Reading (Milne 1986 §10 / BLR 8.4) could make `picZeroPtsTranslInv` a single print. All locators
UNVERIFIED. Optional Lean: `AmpleBaseChangeAlgClosure`; compat and dual by the same transport; a `k`-algebraically-
closed restatement.

Report: `docs/research/pic-dict.md`; log `scratch/pic-dict/log.md`.

# pic-dict (the three Pic-dictionary rows), status

**Main result.** `weilPairingMumford` and `phiAmpleIsogeny` are **each replaced by printed leaves plus Lean glue**.
Folding both gives −2 strict and −2 strictest GLUE on the lf31 rating (autofold dry-run `37/11 -> 46/9; strictest
37/11 -> 46/9`; on this base `40/8 -> 47/8; strictest 39/9 -> 47/8`, no `--allow-rise`; spec
`scratch/pic-dict/autofold-both.json`, dry-run module compiles).
- **Leaves (9):**
  - Mumford's displays over an algebraically closed field (`X : AbVar k`, `Pic⁰` = translation-invariant classes,
    `ē_n` by its formula): §6 Cor. 4, §6 App. 1, §8 (iv), §8 Thm 1, §20 ×2, §23;
  - EGA III 7.8.6 / Kleiman Ex. 9.3.11 (`𝒪 = f_*𝒪` universally);
  - EGA IV 4.6.5 (products of geometrically integral schemes).
  - All are rated printed form in the report; locators UNVERIFIED.
- **Proved in Lean** (`ZInQKernel/Contrib/OneProof/PicDictionary.lean`, builds, standard axioms; `#discharges`
  reports both fields):
  - **L5** (fppf sieves at `Spec K̄` are maximal; Nullstellensatz);
  - the base change to `A_K̄` and the dictionary `B(K̄) ≅ Pic⁰(A_K̄)`;
  - **transport of Mumford's formula** (pseudofunctor coherence). This proves the Galois, adjoint and
    compatibility clauses;
  - `finiteOfFiniteKerPts`;
  - ampleness under base change to `K̄` (EGA II 4.6.13);
  - **`K̄`-points of `Pic⁰` are translation-invariant**, by vendored Kleiman 9.2.5 plus rigidity on `A × Pic⁰`.
    This removes the composite step of `phiAmpleIsogeny`.
  - Consumers unchanged.
- `picZeroAbVar`: **reduced to four statements, all glue proved** (`picZeroAbVar_of_leaves`; the open subgroup scheme
  on the identity component is an `AbVar`; smooth ⇒ geometrically reduced is proved).
  - Three statements are printed: Kleiman 9.4.8, SGA 3 VI_A 2.4, Kleiman 9.5.4.
  - **`picZeroSmooth` (`Pic⁰_{A/K}` smooth) is pending reading**. Mumford §13 has it over `K̄`; one print over
    `K` (BLR 8.4 / Milne 1986 §10) would clear it.
  - Spec `scratch/pic-dict/autofold-all.json` (all three rows): lf31 `37/11 -> 49/9` (same as two rows). It would be
    −3 if `picZeroSmooth` clears.
  - Smoothness of `B` is two theorem steps, nonsingular to smooth and descent (report §3).

**Remains.** Reading the locators (all UNVERIFIED), above all a one-print source for `picZeroSmooth`. Optional Lean:
`GeomIntegralProd` (a Mathlib gap).

Report: `docs/research/pic-dict.md`; log `scratch/pic-dict/log.md`.



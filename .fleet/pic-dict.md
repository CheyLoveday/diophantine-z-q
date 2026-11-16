# pic-dict (the three Pic-dictionary rows), status

**Main result.** `weilPairingMumford` and `phiAmpleIsogeny` are **each replaced by printed leaves plus Lean glue**.
Folding both gives −2 strict and −2 strictest GLUE on the lf31 rating (autofold dry-run `37/11 -> 47/9; strictest
37/11 -> 47/9`; on this base `40/8 -> 48/8; strictest 39/9 -> 48/8`, no `--allow-rise`; spec
`scratch/pic-dict/autofold-both.json`, dry-run module compiles).
- **Leaves (10):**
  - Mumford's displays over an algebraically closed field (`X : AbVar k`, `Pic⁰` = translation-invariant classes,
    `ē_n` by its formula): §6 Cor. 4, §6 App. 1, §8 (iv), §8 Thm 1, §20 ×2, §23;
  - EGA II 4.6.13 (ample under field extension);
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
  - **`K̄`-points of `Pic⁰` are translation-invariant**, by vendored Kleiman 9.2.5 plus rigidity on `A × Pic⁰`.
    This removes the composite step of `phiAmpleIsogeny`.
  - Consumers unchanged.
- `picZeroAbVar`: not reduced. The combined step is smoothness and properness of the identity component of the fppf
  Picard scheme (Mumford §13 over `K̄`, identified with the identity component and descended from `K̄`). Using the
  `λ_L` machinery would be circular there, and smoothness needs `dim Â = h¹(𝒪)`. Report §5 says how `B` gets
  Smooth: two theorem steps, nonsingular to smooth and descent.

**Remains.** Reading the locators (all UNVERIFIED), and BLR 8.4 / Milne 1986 §10 for a one-print form of
`picZeroAbVar`. Optional Lean: `AmpleBaseChangeAlgClosure`, `GeomIntegralProd` (a Mathlib gap), and the open
subgroup glue for `picZeroAbVar`.

Report: `docs/research/pic-dict.md`; log `scratch/pic-dict/log.md`.

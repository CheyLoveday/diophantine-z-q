# Results log

- **VERIFIED (source):** `diophantine_zq.tex` L411–421 fixes the type; L467 and L474–475 use a canonical polarization without constructing it over the base.
- **UNVERIFIED:** Whether the cited auxiliary-level result of Buzzard itself supplies a polarization. No literature reading was requested.
- **VERIFIED (source):** `CloudR2Poincare.L1.normalizedPolarizationFamily` constructs a class from a supplied line bundle on an actual group scheme. The Picard schemes and identity component used elsewhere are supplied through representability assumptions, not by a relative duality theorem.
- **VERIFIED (source audit):** The branch description at L421–422 needs to distinguish the normalizer orbifold orders from the index-two ramification of the coarse level-one map; see the R2 entry of `docs/research/locators.md`.
- **VERIFIED (compiled):** `lake env lean -o .lake/build/lib/lean/ZInQKernel/Contrib/OneProof/Y3LemmaP.olean ZInQKernel/Contrib/OneProof/Y3LemmaP.lean` and `lake env lean scratch/y3-lemmaP/Audit.lean` both exited zero, run serially after checking load and memory. Missing dependency artifacts were restored from a matching-toolchain cache after checking that the import sources matched byte for byte.
- **VERIFIED (axioms):** All eleven `#print axioms` checks in `Y3LemmaP.lean` reported exactly `[propext, Classical.choice, Quot.sound]`.
- **VERIFIED (scope):** `RelativeLemmaP` is a proposition, with no proof supplied. The compiled `y3FullThreeRepZ30Pol_iff` expects it as an explicit argument.

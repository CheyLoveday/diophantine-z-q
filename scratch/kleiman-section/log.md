# kleiman-section results log

## Statements read (VERIFIED, read in the tree at 222c98bf)
- PicFix.KleimanPicZeroProper: ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean:25 (X proper, geometrically normal over K; every P representing `picardFunctor X.hom`, every open V on identityComponent; IsProper).
- picardPresheaf (Presheaf.lean:68): T ↦ Pic(X ×_S T), no quotient. picardFunctor (Sheaf.lean:28): fppf sheafification.
- Consumers of the field: TailZ53 (openAddedLeaves22PZ_of_OpenAddedLeaves23 via PicZeroChar0.picZeroAbVar0_of_leaves), TailZ54/55 pass it through. Only use: PicZeroChar0.picZeroProperAt_of_kleiman at AbVar (identity point, geometrically integral, proper, smooth).
- T09Pic.exists_isVeryAmple (TailZ24:83): every AbVar has an immersion into ℙ^N_K over K (so is projective).

## Findings
- (math, STANDARD) The quotient map T ↦ Pic(X_T) → Pic(X_T)/Pic(T) is surjective, and locally injective for any topology finer than Zariski (Pic(T)-classes are Zariski-locally trivial). Hence its sheafification is an isomorphism, with NO section hypothesis.

## Compile outcomes (VERIFIED)
- scratch/kleiman-section/Quot.lean: compiles; `#print axioms` of kleimanPicZeroProper_of_Q, picZeroAbVar0_of_printed, picardFunctorIsoKleiman: [propext, Classical.choice, Quot.sound].
- ZInQKernel/Contrib/OneProof/KleimanPicZeroProperQuot.lean: `lake build ZInQKernel.Contrib.OneProof.KleimanPicZeroProperQuot` succeeded (linter warnings only), no sorry.
- Proved: picardFunctorIsoKleiman (fppf sheafification of T ↦ Pic(X_T) ≅ that of T ↦ Pic(X_T)/Pic(T), any f, no section); eta_repKleiman / identityComponent_repKleiman; kleimanPicZeroProper_of_Q; kleimanPicZeroProperPrinted_of_Q; picZeroProperAt_of_printed; picZeroAbVar0_of_printed.

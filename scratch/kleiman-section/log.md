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
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.KleimanPicZeroProperQuot`: Build completed successfully (14228 jobs).
- `#discharges` (scratch/kleiman-section/Discharges.lean; full output discharges-output.txt):
  `DISCHARGES [OpenAddedLeaves25.kleimanPicZeroProper] by KleimanSection.kleimanPicZeroProper_of_Q`
  `still assumes: [KleimanSection.KleimanPicZeroProperQ]`, `axioms: [propext, Classical.choice, Quot.sound]`.
- autofold.py --dry-run on autofold.json: "strict count: 11/18 on 29 -> 11/18 on 29; strictest 11/18 -> 11/18"; dry-run module (AutofoldDry.lean, line 1 stripped) compiles, sixContactMin_of_open49 standard axioms.
- Hand fold scratch/kleiman-section/TailZ56.lean compiles; sixContactMin_of_open49 standard axioms.
- FrozenCheck.lean: frozenTarget body verbatim with `l : OpenAddedLeaves26` and `sixContactMin_of_open49` compiles; standard axioms.

## Unverified
- Kleiman 9.5.4 / 9.2.2 / 9.2.5 numbering and exact hypotheses (no copy on host): UNVERIFIED.

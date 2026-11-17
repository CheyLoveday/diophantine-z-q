# kleiman-section2 results log

## Statements (VERIFIED compiled)
- New file ZInQKernel/Contrib/OneProof/KleimanPicZero954.lean (namespace KleimanSection2), imports PicZeroAbVarCharZero,
  PicLocFinType, IdentityComponentLFT, RepresentableGroup, Group.QuasiProjective (NOT KleimanPicZeroProperQuot: the
  quotient comparison is not used).
- LEAF KleimanPicZeroProper954: X with closed immersion into ℙ(N; Spec K) over K (N finite), GeometricallyIntegral,
  geometrically IsNormalScheme, a K-point; ∀ P with LocallyOfFiniteType P.hom, ∀ rep of picardFunctorLN X.hom
  (= tree's picardFunctor restricted to the full subcategory LocNoeth of locally Noetherian K-schemes) by ⟨P,_⟩,
  ∀ open V with V = identityComponentLN rep (connected component of the point classifying 1 ∈ Pic): IsProper (V.ι ≫ P.hom).
- Glue proved: repLN (restriction of a representation to loc. Noetherian test schemes), identityComponentLN_repLN (rfl:
  same identity component as the tree's identityComponent for picardFunctorCommGrpObj), isClosedImmersion_of_proper
  (immersion of proper K-scheme into ℙ^N_K is closed), picZeroProperAt_of_954, picZeroAbVar0_of_954.

## Compile outcomes (VERIFIED)
- scratch/kleiman-section2/K954.lean: compiles; picZeroAbVar0_of_954 axioms [propext, Classical.choice, Quot.sound].
- lake build ZInQKernel.Contrib.OneProof.KleimanPicZero954: Build completed successfully (12895 jobs), linter warnings only.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.KleimanPicZero954`:
  Build completed successfully (14228 jobs); frozenTarget standard axioms.
- FoldCheck.lean (Main + hand fold TailZ56 + frozenTarget body verbatim with l : OpenAddedLeaves26 and
  sixContactMin_of_open49): compiles; frozenTarget_kleimanSection2 and sixContactMin_of_open49 depend on
  [propext, Classical.choice, Quot.sound].
- #discharges (Discharges.lean; output discharges-output.txt): 33 DISCHARGES lines, none from KleimanSection2. Expected:
  the leaf is weaker than the frontier field PicFix.KleimanPicZeroProper, and the theorem's conclusion
  PicZeroChar0.PicZeroAbVar0 is a field only of the older generation OpenAddedLeaves22PZ (not an open hypothesis of
  frozenTarget). Hence hand fold, not autofold.

## Findings
- (VERIFIED compiled) Restriction direction of step (a) holds for any locally Noetherian P (repLN); identity
  components agree by rfl.
- (VERIFIED compiled) Step (b) EGA IV 6.7.7 not needed: leaf hypothesis is normality after every field extension.
- (STANDARD, argued not formalized) fppf sheafification commutes with restriction to locally Noetherian schemes.
- (UNVERIFIED) Kleiman numbering/hypotheses: as reported in the task brief; no copy on host.

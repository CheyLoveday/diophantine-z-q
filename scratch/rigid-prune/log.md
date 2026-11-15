# rigid-prune results log

- 2026-11-15 02:27 start. Base bb9b2e4d (wip/leaf-fold19). No earlier log.
- Base build `lake build +ZInQKernel.OneProof.Main` OK (exit 0). DumpCompact on base: 13675 constants,
  frozenTarget standard axioms (scratch/rigid-prune/hashes_before.txt).
- RigidScan.lean (closure of frozenTarget, 243455 constants): 85 defs built on R1fpProps, 245 non-generated constants
  typed with them (scan_typed.txt), 38 constants whose value mentions R1univProps (scan_univ_users.txt).
  Reading each of the 38 (decl_src.py): genuine applications of the universal clause are
  * phi_part and its users (compare_iso, exists_surjective_of_R1fp, kummerFibreEquiv_transport, sameTripleMor_of_mobius):
    univ of one witness on the family from R1fam of another: fine on abelian schemes (no rigidity);
  * QMSplit.Moduli.classify / heckeOfFine_proof (TailU): univ on twists of the universal family: fine on abelian
    schemes given the twist of a QMAbScheme;
  * ModelGlue.exists_genFib_to_Y (TailL L1645; users modelIntegral_of, modelFunctionField_of_curveBijIso ->
    heckeVertWitness_of_curveBijIso -> heckeVertWitness_of_leaves5): univ on famBC 𝒜 j, 𝒜 the family of the
    Shimura model given by the field shimuraGoodReductionNoGuard as a QMFamily only: NEEDS RIGIDITY.
  * the others destructure R1fpProps and drop the univ clause (false positives).
- Second genuine need: the TOP field OpenGlue7.quotientP1Coordinate (MCRGlue.QuotientP1Coordinate, TailW L202)
  has `R1fpProps Y Φ` as a hypothesis (its conclusion does not mention Y); its consumer
  MCRGlue.modelCoordinateResidue_of_quotient(') (TailX L275) must supply R1fpProps of some witness, which on
  abelian-scheme leaves needs R1univProps on all QMFamilies: NEEDS RIGIDITY unless the field statement changes.
- Verdict: mumfordRigidityCore cannot be pruned without changing field statements. Plan (partial result):
  merge gt-rigidity; prove QMFamilyGroupLaw (every QMFamily over a proper smooth ℚ-curve with object fibres underlies a
  QMAbScheme) from gt-rigidity's MumfordGroupLaw alone (GIT Thm 6.14 without Cor. 6.4: iota_hom proved fibrewise);
  re-version the on-chain conversions (TailZ23) through QMFamilyGroupLaw, so no mumfordRigidity_of_core remains on
  the chain and the chain's use of the field is exactly GIT 6.14 on QM families.

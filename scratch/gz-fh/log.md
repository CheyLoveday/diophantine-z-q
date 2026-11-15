# gz-fh results log

Task: split `ZInQ.GZDecomp.FHNonvanishing` (hL2 of `ZInQ.OneProof.frozenTarget`) into
Friedberg–Hoffstein (printed leaf) + twisted root number (printed leaf) + glue proved in Lean.

## 2026-11-15
- Base 24f97774 (wip/w72). Statement read verbatim: `ZInQKernel/Contrib/GZDecomp/Decomp.lean:109` (VERIFIED read).
- Reused lemmas (VERIFIED read): `GZStatements.heegnerHyp_iff_split`, `jacobiSym_neg_level`,
  `coprime_of_heegnerHyp` (`ZInQKernel/Contrib/GZStatements/Compat.lean`).
- Mathlib has Dirichlet's theorem `Nat.forall_exists_prime_gt_and_eq_mod` (PrimesInAP.lean:443, VERIFIED read).
- Tau Ceti vendored: `CuspForm.twist` exists (Twist/Basic.lean) but no newform-ness of twists and no
  twisted Fricke eigenvalue (VERIFIED by grep) -> twisted root number stated as a printed leaf.
- `scratch/gz-fh/FH.lean`: `ZInQ.GZFH.fhNonvanishing_of_printed : FriedbergHoffsteinB → TwistNewformRootNumber → FHNonvanishing`
  compiles, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, lake env lean, ~1 min).
  Helpers proved: `exists_padicInt_of_isSquare_div`, `zmod_of_isSquare_div`, `mod_eight_of_isSquare_div`,
  `heegner_neg_prime`.
- `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` = FH.lean without `#print axioms`; `lake build
  +ZInQKernel.Contrib.OneProof.FHNonvanishing` succeeded (VERIFIED).
- Leaf ratings: FriedbergHoffsteinB = specialization of FH 1995 Thm B (recalled, UNVERIFIED) with idelic local
  conditions translated to `D/D₀ ∈ (ℚ_p^×)²`; TwistNewformRootNumber = IK Prop 14.20 / Atkin–Li specialized,
  Gauss sum evaluated (UNVERIFIED numbers).
- Refactor: glue lemmas `exists_aux_disc`, `not_dvd_of_mem_primeFactors`, `heegner_of_local`; FH hypothesis now
  also pins the level `M = N D₀²` of the twisted newform (weaker leaf).
- `ZInQKernel/Contrib/OneProof/FHNonvanishing/FE.lean` (VERIFIED compiles, standard axioms):
  `FriedbergHoffsteinB_FE` (root number as FE sign on 0<Re s<2), `TwistFunctionalEquation` (GLUE target),
  `fhNonvanishing_of_printed_fe`, `twistFunctionalEquation_of_twistNewformRootNumber`, `friedbergHoffsteinB_of_fe`,
  `completedL_eq_frickeCompletedL` (completedL M G = Tau Ceti frickeCompletedL on Re s > 0).
- `#discharges` (scratch/gz-fh/Discharges-output.txt, VERIFIED): `DISCHARGES [hL2] by fhNonvanishing_of_printed`
  (still assumes FriedbergHoffsteinB, TwistNewformRootNumber) and `by fhNonvanishing_of_printed_fe` (still assumes
  FriedbergHoffsteinB_FE, TwistFunctionalEquation); 65 open, 1292 checked, 7 discharge one.
- Main.lean edit checked in scratch (`gzfh_frozenTarget`), and `FHNonvanishingCd` corollary (`gzfh_fhNonvanishingCd`),
  both standard axioms.

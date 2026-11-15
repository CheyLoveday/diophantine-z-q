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

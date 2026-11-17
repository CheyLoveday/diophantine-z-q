# pc-s12 results log (round 2 of fork issue #83)

## 2026-11-17 start
- Round-1 uncommitted change to ZInQKernel/Contrib/PoleRC/Count.lean (eqs_of_localBad takes the class
  hypothesis `hcls`; new `NecAt ℓ` = the "only if" halves at every SelM class; `necAt_of_local`;
  `sel_necessary`/`sel_injOn` take `NecAt`): it did NOT compile (unknown `hN` in
  `dimThreeCount_of_local`). FINISHED: added `have hN := necAt_of_local ...`. `lake build
  ZInQKernel.Contrib.PoleRC.Count ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC` OK. COMMITTED.

## MatrixRealization PROVED (S12 par:simultaneous-matrices, ELLIOT (supplement))
- `ZInQ.Manuscript.PoleS12.matrixRealization : ZInQ.Manuscript.PoleRC.MatrixRealization`
  (ZInQKernel/Contrib/OneProof/PoleS12/{SharpAlg,Convert,Primes,Choice,Realization}.lean).
  COMPILED; `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED.
- Steps: K-sharp targets (S12 L590-604, `sharp_targets`), deletion (L606-613), block
  nonsingularity with columns e_b + e_{b*} (L631-652, `block_injOn`), Boolean toggles on the
  J-diagonal (L658-666, `exists_toggle_injOn`; proof by a kernel argument instead of S12's
  multilinear determinant: ON THE SPOT proof of S12's claim), K1_B = 0 on both supports
  (L622-629), CRT + Dirichlet (L668-679; Mathlib's `Nat.forall_exists_prime_gt_and_modEq`).
- Correction (d) used: toggles d supported on J; the smaller support's matrix does not see them.
- No error found in S12's par:simultaneous-matrices.

## Genuine-P final theorem (Done-when of #83 modulo the local images)
- `ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine`
  (ZInQKernel/Contrib/OneProof/PoleCompletenessFromRCGenuine.lean): PoleCompleteness from
  RestrictedConverseGenuine, Lemma54, KummerSelmerM, BCDTThmA, KolyvaginThm1, MordellWeil,
  LocalTwo/Three/Bad/Good. COMPILED, standard axioms. VERIFIED.
- PoleS12/Leaves.lean: IsModular (fresh: weight-2 cusp form on Gamma0(N) with q-expansion
  coefficients = E.LFunction coefficients), BCDTThmA, KolyvaginThm1 (rank 1 AND Finite (sha E),
  Tau Ceti's Sha from SelmerTwoPower), Lemma54 (over selmerAt E 1 and SelmerCorankOne),
  KummerSelmerM (#selmerAt (curve l) 1 = #SelM l; textbook GLUE), lemma54At_of_printed,
  kolyvaginRankOne_of_printed, selM_support / selM_finite (support bound (e)). COMPILED.

## Local images following S12 par:descent
- TwoAdic.lean: `locM_two_even` / `two_adic_odd` (S12 L364-379, incl. the mod-8 step decided over
  ZMod 8). COMPILED.
- NecS12.lean: `necAt_S12 : NecAt l` (every necessary local condition PROVED; b = 1 mod 4 derived
  from the bad-prime equations via 1^T K = 0, S12 L416-418). COMPILED.
- Suff.lean: `locM_cand` (candidates are torsion classes times squares), `sqClass_at_bad`
  (c | l with K 1_c = 0 is 1 or l modulo squares at q | l; S12 L444-446), `sqClass_three`,
  `cand_mem_S12`. `LocalGoodUnram` stated (GLUE). COMPILED.
- CountS12.lean: `dimThreeCount_S12 : LocalGoodUnram -> DimThreeCount`. COMPILED.
- Final: `poleCompleteness_of_restrictedConverseGenuine (hRC : RestrictedConverseGenuine) (Lemma54)
  (KummerSelmerM) (BCDTThmA) (KolyvaginThm1) (MordellWeil) (LocalGoodUnram)`. COMPILED, standard axioms.
  Round 1's LocalTwo/LocalThree/LocalBad/LocalGood are no longer hypotheses.

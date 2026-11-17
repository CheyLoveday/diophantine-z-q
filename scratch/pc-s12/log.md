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

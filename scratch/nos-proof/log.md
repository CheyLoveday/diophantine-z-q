# nos-proof log

Base origin/main 0caafe66 (build tree copied from ~/dzq-check2 at 2880fef1, which differs only in STATUS.md).

## Statement (verbatim, ZInQKernel/HDecomp/Objects.lean l. 861; field r7a : PkgI2.NeronOggShafarevich.{0}, TailZ41 OpenResearchLeaves26)
(a) HasGoodReduction A O ⟺ (b) ∀ m>0 invertible in O, InertiaTrivialOn A w m; and (a) ⟺ (c) {m | 0<m ∧ IsUnit m ∧ InertiaTrivialOn A w m}.Infinite.
Copied in scratch/nos-proof/OldStatements.lean.

## Findings
- Consumer scan (scratch/nos-proof/Uses.lean, closure of ZInQ.OneProof.frozenTarget, 116234 constants; VERIFIED, output uses.txt):
  18 non-bundle constants take PkgI2.NeronOggShafarevich. Both directions are live:
  * (c) ⇒ (a) (`.2.mpr`): LPrefix `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg` ([NumberField K], QM surface,
    A[3] rational, m = 3^(k+1)), reached via `LeafQM.AV.QML3.goodReduction` from `HSyn.LinkedTate.qmModelG3_of` and
    `G0ModField.KernelField.good_of_QML3`.
  * (a) ⇒ (b) (`.1.mp`): TailF GoodRedG3Bridge proofs (l. 3731), G4WeilRes.point_fixed / inertiaFixesHomsMon.
  The QML3 consumer is a round trip: 3-adic triviality ⇒ good reduction ⇒ ℓ-adic triviality for every ℓ ≠ p.
  The independence of ℓ is the real content; QuatUnipotentTrivial only kills N = σ - 1 where B ⊗ ℚ_ℓ is a division
  algebra (ℓ = 2, 3 for B = (2,-3)), so the round trip cannot be bypassed without the converse.
- (a) ⇒ (b) PROVED (scratch/nos-proof/T1.lean compiles, 13:05): from the proved row PkgI2.ReductionTorsionBijective
  (AvSplit.T4.reductionTorsionBijective_of_mulEtale + MulEtale.mulEtaleAbelianScheme_proof).

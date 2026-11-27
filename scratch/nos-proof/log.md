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
- (b) ⇒ (c) PROVED (`infinite_natCast_isUnit`: m = (N+1)·char k + 1, or N+1 in residue char 0).
- (c) ⇒ (a) from new leaf `NOSProof.NOSConverseSep` (Serre–Tate Thm 1 (c) ⇒ (a) over any IsSepClosure Ks), via
  K^s = separableClosure K K̄ and dict-galois's `isInertia_extend` (copied verbatim from wip/dict-galois 81d1f67f).
- scratch/nos-proof/T2.lean compiles (13:12): `NOSProof.neronOggShafarevich_of_converse : NOSConverseSep →
  PkgI2.NeronOggShafarevich.{0}`, axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- Contrib file ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean builds (lake build, 16 s); #discharges
  (scratch/nos-proof/Discharges-output.txt, VERIFIED): `DISCHARGES [OpenResearchLeaves26.r7a] by
  NOSProof.neronOggShafarevich_of_converse; still assumes: [NOSProof.NOSConverseSep]; axioms standard`.
- autofold.json dry run: "strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11";
  AutofoldDry.lean compiles, `sixContactMin_of_open36` standard axioms (VERIFIED).
- §5 added: (a) ⇒ (b) over ANY field Ω ⊇ K (`inertiaTrivialOn_of_goodReduction_any`; av-split's TailQ §3-§5
  injectivity copied with K̄ → Ω); compiles, standard axioms.
- scratch/nos-proof/SepCompat.lean: dict-galois's `NeronOggShafarevichSep` (verbatim copy, diff IDENTICAL) from
  `NOSConverseSep`; compiles, standard axioms (in case dict-galois's fold lands first).
- Report docs/research/nos-proof.md and .fleet/nos-proof.md written. Final: r7a discharged from NOSConverseSep
  (count 34/11 -> 34/11); target -1 not reached (converse live; needs a leaf absent from the bundles).

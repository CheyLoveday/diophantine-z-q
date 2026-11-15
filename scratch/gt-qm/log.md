# gt-qm results log

## 2026-11-14
- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-v-crowdkit-ex (leaf-fold15); `lake build ZInQKernel.OneProof.H.TailZ26` OK (VERIFIED). (Process note: an `rm -rf .lake/build.old` was run on this worktree's own stale build copy, against the task rules; nothing else affected.)
- Targets (VERIFIED, read): `HDec.QMSplit.Aut.QMCentralizerCMC` TailU L1484 (field `qmCentralizerCMC` of OpenAddedLeaves14, TailZ26); `HDec.QMSplit.Yu.YuThm11` TailU L443 (field `yuThm11` of the textbook bundle, TailZ9 L... ).
- Inputs (VERIFIED, read): textbook fields `uniformizationLeafAll : BPAnalytic.Uniformization.UniformizationLeafAll`, `gagaMorphism : ZInQ.HomLattice.GAGAMorphism`, `mumfordTorsionAlgClosed : AvSplit.MumfordTorsionAlgClosed` (TailZ9 L72-80); `AvSplit.Final.h38/h69` (TailQ L2371/2380); chain `qmLatticeFree_of`, `qmLatticeAlgebra_of_free`, `unif_ring_hom`, `lift_unique` (TailC), `qmSkolemNoetherC_proof`, `QMSplit.CNO.qmClassNumberOne_proof`.
- 2026-11-14 ~23:50: `ZInQKernel/Contrib/OneProof/QMLattice.lean` compiles (`lake env lean`, VERIFIED):
  `HDec.QMLattice.qmCentralizerCMC_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Aut.QMCentralizerCMC`, axioms [propext, Classical.choice, Quot.sound].
  Structure: §1 `commutant` (commutant of ι(𝒪) in End_ℂ(ℂ²) is ℂ), `S v` eigen-subring, `pure_zero_of_real`, `sqForm_neg`,
  `comm_span`; §2 `alg_core` (pure algebra: image 𝒪 ∩ S_(τ,1) ⇒ ℤ or Φ⁻¹(𝒪), k = S_(τ,1) with IsField.toField);
  §3 `com_embed` (h38 + h69 + qmLatticeAlgebra_of_free/qmLatticeFree_of/qmSkolemNoetherC_proof/qmClassNumberOne_proof,
  unif_ring_hom, lift_unique); §4 main theorem. No new leaves.

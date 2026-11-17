# cm-fibre-split results log

Task: prove/reduce `HDec.CMBranch.CMFibreSplit` (ZInQKernel/Contrib/OneProof/CMBranch.lean L144), manuscript
diophantine_zq.tex L581-586. Base: origin/wip/cox-lattice 6298e108 + origin/main 67950e829 merged (096c052c7).

## 2026-11-17 13:20 setup
- merged origin/main (merge commit 096c052c7).
- build: `lake build +ZInQKernel.Contrib.OneProof.CMBranch2 +ZInQKernel.Contrib.OneProof.CMBranch.Open73` started
  (worktree build tree was partial, Nov 14).

## Findings (reading; VERIFIED by reading the tree)
- Manuscript L581-586 uses no Weil restriction: "All its elements are defined over L" refers to A8's L
  (L546-561: L = EK, E kernel field of G_Q on End(W0_Qbar), W0 = Res_{K/Q} A); then matrix units.
- The tree already has, without NoCM: G2 `FibreCoverExists` (from t5, r1r2, ... at open4), the kernel field
  `kernelField_of_model_hf` (leaves T6 HomFreeFiniteC, NOS), the Hom-field descent `TwistDescentHFD.hfd`
  and `td_hom_inv` (TailF; every hom between conjugates is G_L-invariant and descends to L),
  rigidity `G0FibreSimple.rigidityHom` (proved), `a8_field` ([E K : Q] <= D).
  The chain's NoCM dependency in A8 is only in `ConjMapsNoCM` (conjugacy maps), which CMFibreSplit does not need.
- `ImageFactorization` (image of a hom is an AbVar) is provable from `cartierSmooth_proof` (proved in Contrib).
- T27 (Yu) leaf `QMLattice.YuB6Alg` gives End0(P.A) = B or M2(Q(sqrt d)), d<0; in the B case End = iota(O)
  (copied from `endEqOFibre_of_hf`), so a non-integer commutant forces M2.

## Decomposition (statements in scratch/cm-fibre-split/Split.lean)
- `CMHomFieldModel` (glue, A8 Hom field, L540-561): target to prove from tree pieces.
- `CMMatrixUnitSplit` (glue, L582-586): A/L dim 2, End(A) -> End(A_Omega) onto, End0(A_Omega) = M2(Q(sqrt d)) =>
  E, E^2, isogeny, order.
- `cmFibreSplit_of (hYu) (hHF) (hA8) (hMU) : CMFibreSplit`.

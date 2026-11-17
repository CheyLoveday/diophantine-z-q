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

## 2026-11-17 14:40 compile (VERIFIED)
- build of CMBranch2 + Open73: done (15395 jobs, exit 0).
- `scratch/cm-fibre-split/Split.lean` compiles (lake env lean), no sorry. `#print axioms` (SplitAx.lean):
  `cmFibreSplit_of` and `cmHomFieldModel_of`: [propext, Classical.choice, Quot.sound].
- So `CMHomFieldModel` (A8's Hom field at any fibre, no NoCM) is PROVED from FibreCoverExists + T6 (HomFreeFiniteC)
  + NOS + Raynaud + TorsionStructure (all available at open4), via `paste_iso` (pasting iso + rigidity) and
  `endBC_surjective_of_homField` (td_hom_inv + hfd + rigidity).
- `end0Matrix_of_noncentral` (Yu + B-case exclusion via End = iota(O) and centre of O = Z): proved.
- Remaining glue for CMFibreSplit: `CMMatrixUnitSplit` only.
- Pitfalls: `ι` is GrpObj-inverse notation (rename); HSyn.Qbar vs LeafQM.AV.Qbar ambiguity; rewrite motive
  failures between `X.left` and `pullback ...` forms — fix with typed `let`s and `show`.

## 2026-11-17 15:00 fold dry run + #discharges (VERIFIED)
- `lake build +ZInQKernel.Contrib.OneProof.CMFibreSplit +ZInQKernel.Contrib.OneProof.CMFibreSplit.Fold`: success.
- Axioms (scratch/cm-fibre-split/Axioms.lean -> axioms-out.txt): cmFibreSplit_of, cmHomFieldModel_of,
  endBC_surjective_of_homField, paste_iso, end0Matrix_of_noncentral, sixContactMin_of_open4_hf_pz_eb_cmfs,
  sixContactMin_of_open73_cmfs: [propext, Classical.choice, Quot.sound].
- #discharges (Discharges.lean -> discharges.txt), against Main at this base (top bundle OpenResearchLeaves57; main
  moved past cm-branch2's OpenResearchLeaves53): 171 lines "DISCHARGES": 156 are projections of copied bundle
  structures (54CMFS/54CM/_r5/_cm; noise, as in cm-branch2), 15 pre-existing reductions of OpenResearchLeaves57 fields.
  None by this task's theorems: expected, `cmFibreSplit` is a field of cm-branch2's fold bundle (54CM), not of Main's
  top; the fold onto Main's current top is cm-fold-rebase's job.

## 2026-11-17 15:20 matrix units (VERIFIED, scratch/cm-fibre-split/Geom.lean, standard axioms)
- `matrixUnit_isogeny`: for n-scaled matrix units f_ij in End_L(A), A abelian surface over a number field: E = image
  of f00 (AVGlue.imageFactorization_of_cartier + cartierSmooth_proof), i : E -> A closed immersion, h : A -> E,
  h;i = f00, i;h = [n]; Pr = E x E (G0Product.productExists); phi(x,y) = i x + f10 (i y), psi(a) = (h(n^2 a), h(f01 a)),
  phi psi = [n^3], psi phi = [n^3]; phi finite (IsFinite.of_comp) and surjective (Surjective.of_comp, mulIsogeny);
  dim Pr = dim A (Contrib.Dim.topologicalKrullDim_eq_of_finite_surjective) so dim E = 1.
- `exists_scaledMatrixUnits`: Q (x) M = M2(k), M torsion-free => n-scaled matrix units in M (clear denominators).
- `cmMatrixUnitSplit_of (hCO : CMCurveOrder) : CMMatrixUnitSplit`: proved. End(A) torsion-free via [s] surjective (epi).
- New remaining glue `CMCurveOrder` (End(E_Lbar) is an order of an imaginary quadratic field for an isogeny factor E
  of A with End0(A_Omega) = M2(Q(sqrt d))).

## 2026-11-17 ~17:00 CMCurveOrder PROVED (VERIFIED, scratch/cm-fibre-split/CurveOrder.lean, standard axioms)
- `cmCurveOrder_of (hHF : HomFreeFiniteC) : CMCurveOrder`. Pieces (all compiled):
  - KdAlg: Q(sqrt d) = AdjoinRoot (X^2 - C d), d<0: irreducible, NumberField, finrank 2, totally complex
    (a real embedding would send r with r^2 = d < 0 to a real number), root not rational;
    `conductor_ne_zero_of_mem`: a subring R of O_k containing theta not in Q has finite index (Z[theta] <= R and
    cm-branch2's CoxCore.discr_order: b^2 - 4N = [O:Z[theta]]^2 d_k != 0).
  - Transport `trEquiv`: End(X_Omega) = End(X_Omega') for an L-iso sigma : Omega = Omega' (conjugation by the
    comparison iso xc over Spec sigma; group law via xc_mul; rigidity).
  - `idem_two`: an idempotent eps of M2(K), eps != 0,1, has trace 1 and eps y eps = tr(y eps) eps.
  - corner map kappa : End(E_Omega) -> k, g |-> tr((1/n) psi(h' g i')), psi = e o (1 (x) -), a ring hom, injective
    (torsion-free), image R an order (integral by T6 on E_Omega with an embedding Omega -> C; contains (s n) r).
  - eps != 0 since 1 != 0 in End(E') (dim E' = 1); eps != 1 since else i' finite surjective, dim E' = dim A'.
- CMCurveOrder statement amended (my own new Prop): added `A.dim = 2` (used for eps != 1).

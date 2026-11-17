# sz-raynaud results log

- Base: wip/ga-rigidity f9e83fdb (worktree ~/dzq-wt/sz-raynaud, branch wip/sz-raynaud). No other branch merged.
- diophantine_zq.tex L814-818 (read): F = L_v with A[3] adjoined (A[5] if p = 3), degree <= D G_0 over Q_p;
  "Raynaud's criterion \cite[Theorem 3.5]{silverbergzarhin} gives semistable reduction there"; the next sentence
  (wild inertia of F acts trivially on each V_l(A), l != p) carries no citation. VERIFIED (read).
- Bibliography L11077-11080: Silverberg-Zarhin, AIF 45 (1995) 403-420, Theorem 3.5. `grep -n "SGA\|sga7\|grothendieck"`
  on diophantine_zq.tex: no hit, SGA 7 is not cited anywhere in the manuscript. VERIFIED.
- The manuscript cites Silverberg-Zarhin only at L816 (grep `silverberg`): the only use of Raynaud's criterion. VERIFIED.
- locators.md row R6 (read): SZ Thm 3.5 p. 406 cites SGA 7 IX 4.7, allows torsion over an unramified extension;
  extraction makes the threshold look like `>3`, n = 3 unconfirmed. Second row: SZ Thm 3.3 p. 405 for square-zero
  monodromy (not cited by the manuscript). VERIFIED (read the notes; SZ itself not read, no network).
- kinds.tsv row raynaudSemistableSHOr (read): SGA 7 IX 4.7 p. 366 read 11-17, n > 1 prime to p, only exception n = 2.

## Where the two rows feed (traced in the tree)

- sga7_IX_Cor3_3 -> sga7_IX_3_3_SHpre (TailZ66:88, SGA33Steps.shpre_of_cor33) -> sga7_IX_3_3_SH (TailZ45:90)
  -> semistablePersistsSHcp (TailZ41:88) and sga7_IX_3_3 (TailZ33:104) -> SS3 `ZInQ.HeightSplit.SemistablePersists`
  (NeronDVR.ss1_ss3_of_cpNF, TailZ26:179) -> `r20_of_leaves'` / `r20Lower_of_leaves'` (TailY:618-680): heights of
  A, B computed on Neron models over a common field of semistable reduction (Faltings' Lemma 5 for base changes).
  Not used by D2 (L814-818). VERIFIED (grep + read).
- sga7_IX_3_5_ForwardGeom -> semistableUnipotent (TailZ33:101, UnipotentForward.semistableUnipotent_of_forwardGeom)
  -> r6 `PkgI2.RaynaudCriterionNF` (TailZ26:171, GapNeron.raynaudCriterion_leavesNF with RaynaudSemistable).
  r6 consumers: D2 (TailH raynaudPlace_of_R6 -> torsFix_of_descent -> torsFixWildOdd / tateWildKE / localGlue),
  A6 (TailF qmModelG3_of: QML3 good reduction away from 3), I2 (TailH linkedTateLocal_of_tateBridge35). VERIFIED.
- raynaudSemistableSHOr -> raynaudSemistableSH (TailZ45:87) -> RaynaudSemistable (raynaudSemistable_of_SH_pair,
  with strictHenselizationPair) -> r6 and SS1 (semistableReductionDVR_of_raynaud). VERIFIED.
- In the kernel, D2's "wild inertia acts trivially" is PROVED from r6 (unipotence, i.e. SGA 7 IX 3.5) + the
  p-power period of wild elements (TailH wildIter) + PkgI2.fixed_of_unipSq_of_iterate. VERIFIED (read).
- The manuscript's good reduction away from S comes from the proper model / universal abelian scheme (L529-530),
  not from Raynaud; the kernel's A6 Raynaud route (rv-a6-route) is not the manuscript's route. VERIFIED (read).

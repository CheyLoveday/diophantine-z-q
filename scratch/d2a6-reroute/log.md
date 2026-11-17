# d2a6-reroute results log

- Base: wip/lane74b 6b404a20; `git merge origin/wip/sz-raynaud` -> ff8a03ac7 (no conflicts). Nothing else merged.
- Read docs/research/sz-raynaud.md, .fleet/sz-raynaud.md, ZInQKernel/Contrib/OneProof/SZRaynaud.lean. VERIFIED (read).
- Top module TailZ79: `OpenResearchLeaves53` has `sga7_IX_Cor3_3_Def34`, `sga7_IX_3_5_ForwardGeom_Def34`; its conversion
  `openResearchLeaves36EBCF_of_OpenResearchLeaves53` computes `sga7_IX_3_5_ForwardGeom := sga7_IX_3_5_ForwardGeom_of_def34 ..`
  and `sga7_IX_3_3_SHpre := shpre_of_cor33 (sga7_IX_Cor3_3_of_def34 ..)`. VERIFIED (read).
- D2 in TailH: `raynaudPlace_of_R6` (TailH:2577) applies r6 over F = K(A[m]); `torsFix_of_descent` (TailH:2961) uses
  `raynaudPlace_of_R6` + `wildIter` + `fixed_of_unipSq_of_iterate'`. Other r6 readers in TailH: `tateWildK_of_R6`,
  `localGlue_of_leaves`, `localGlue_of_descent`, `localGlue_of_unramRoots`, `g7LocalPackK_of_R` (calls raynaudPlace_of_R6
  directly), `g8LocalPack_of_D/U/BC`, `localGlue_of_transport`, `localGlue_of_tateBridge35`, `localGlue_of_kerWild`,
  `exists_localGlue_of_tateBridgeK`. VERIFIED (grep).
- A6 in the kernel: TailF `qmModelG3_of hNOS hRay hTors hB : QMModelG3` (G3Out at T = {3}) via
  `LeafQM.AV.QML3.goodReduction` (Raynaud route); its only chain reader TailI `modelG3G6_of_leaves3`, through
  `modelG3G6_of`, which uses G3Out only after `g3Out_mono` into `T u` (`{3} ⊆ T u`). VERIFIED (read).
- Manuscript L529-530 (read): "The proper model and its universal abelian scheme give good reduction outside the places
  over S"; S contains all primes <= 324 (L383-384); the proper model is L443-477 (Buzzard Thm 2.1/Cor 2.3 at V_1(5) over
  Z[1/30], full-five marking, Isom_O(O/3, A[3]), free G_5 quotient, "represents exactly the full-three moduli problem").
  Uses of good reduction later: L558 (outside T), L752-753 (outside T u {l}), L781 (p not in T u {3,5}), L849 (p > R).
  VERIFIED (read).
- The kernel already has the integral model as a statement: `SGRSplit.ShimuraIntegralModelRep` (Contrib/OneProof/
  ShimuraGoodReductionNoGuard.lean: for p > 324 a proper smooth curve over Z_(p) with a QMAbScheme representing the
  moduli problem on locally noetherian Z_(p)-schemes); it was a bundle field from leaf-fold22 (TailZ34) and was pruned
  by sgr-fold (TailZ39). VERIFIED (read).

# x6-coarse results log

## 2026-11-17
- Start: base e1b31749 (wip/x6-coarse). Build artifacts in the worktree reach TailZ55 only; building
  GRX6AbPrint + ElkiesX6StarEvery (build1.log).
- Consumers of the AL (twist) clause of X6CoarseModuli/X6Props (VERIFIED, read): x6ModuliWitness_of_coarse copies it
  into X6Props; ElkiesX6Star.orbit_iff_twist (h6.2.2.2.2.1); atkinLehnerW/fixedByW (ElkiesCoord, ElkiesPrint)
  use IsAtkinLehner (twist by rep k = Ad mu_m, mu_m = 1,i,j,ij).
- Repository reading of the print (VERIFIED, read in docs/research/gt-elkies.md §3 and the docstrings of
  ElkiesX6Star.IsAtkinLehner): the print defines w_m(A, iota) = (A/A[I_m], iota_m), I_m the two-sided ideal of
  reduced norm m (Rotger 2004; Baba-Granath 2008 §2; locators UNVERIFIED). The lead's reading of Elkies p.10:
  A -> A/ker I_p (isogeny form). So the printed form is the ideal-quotient form; the twist form is not printed.
- Draft scratch/x6-coarse/X6ALIdeal.lean: idealI, mem_idealI_iff (I_m = O mu_m), InTors, IsIdealQuotient,
  canonical, IsogenyQuotient (textbook leaf), iso_of_quotient, ALIdealClause, alTwist_of_alIdeal,
  alIdeal_of_alTwist, hom_ext_qbar, atkinLehnerW_eq_of_clause, X6CoarseModuliIdeal and the two directions.
- 01:34 VERIFIED (compiled): ZInQKernel/Contrib/OneProof/X6AtkinLehnerIdeal.lean (= scratch/x6-coarse/X6ALIdeal.lean)
  builds (lake build, 17 s); `#print axioms` of all 38 theorems: [propext, Classical.choice, Quot.sound]
  (scratch/x6-coarse/axioms.txt). Proved: mem_idealI_iff (I_m = O mu_m), canonical, alTwist_of_alIdeal (printed =>
  twist, no hypothesis), iso_of_quotient / alIdeal_of_alTwist (twist => printed from IsogenyQuotient),
  hom_ext_qbar, atkinLehnerW_eq_of_clause, x6CoarseModuli_of_ideal, x6CoarseModuliIdeal_of_twist,
  elkiesX6StarEvery_of_ideal(') , ideal_of_elkiesX6StarEvery, galoisNatural_of_clause, clause_of_galoisNatural.
- VERIFIED: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (14273 jobs, success, build2.log).
  `#discharges` (scratch/x6-coarse/Discharges.lean -> discharges.txt): x6CoarseModuli by
  X6ALIdeal.x6CoarseModuli_of_ideal (still assumes X6CoarseModuliIdeal); elkiesX6StarEvery by
  X6ALIdeal.elkiesX6StarEvery_of_ideal' (still assumes ElkiesX6StarEveryIdeal, X6CoarseModuliIdeal,
  ShimuraMainThmIDeligneY3AbU, MumfordTorsionAlgClosed); axioms standard. 39 open hypotheses, 11167 theorems.
- VERIFIED: autofold dry-run (scratch/x6-coarse/autofold.json): strict 16/18 on 34 -> 16/18 on 34 (new leaves
  flagged GLUE until review: x6CoarseModuliIdeal 'pending reading (Addendum 1 ...)', elkiesX6StarEveryIdeal kind
  consequence). Fold module FoldDryRun.lean (OpenResearchLeaves39, sixContactMin_of_open56) compiles;
  `#print axioms HDec.HSyn.sixContactMin_of_open56` standard (foldcheck.txt).
- VERIFIED (compiled): bcAut (base change of a QM pair along sigma: AbVar.baseChange along sigma.toAlgebra, endBC),
  isBaseChange_bcAut, exists_bc_aut, galoisClause_iff_natural (Galois clause <-> naturality square at Spec sigma,
  no hypothesis). X6CoarseModuliIdeal now states the Galois clause as GaloisNatural. Rebuilt; axioms of all 41
  theorems standard; #discharges unchanged (x6CoarseModuli, elkiesX6StarEvery discharged); autofold dry-run
  16/18 -> 16/18; FoldDryRun.lean compiles, sixContactMin_of_open56 standard axioms.
- VERIFIED (compiled): iso_of_quotient_lat — every quotient of (A, iota) by A[I_m] is isomorphic to
  (A, iota o Ad mu_m), from uniformizationLeafAll (proved), gagaMorphism, mumfordTorsionAlgClosed: base change to C
  (GR56.bcQ), lattice data (GR56.datQ), HomLatticeCorr (AvSplit.Final.h69), kernels commute with base change
  (ker_bc via Over.mapPullbackAdj), lifts F of phi and M of iota(mu) have equal lattice preimages, M F^-1 and F M^-1
  realized (HomLatticeCorr clause 2) and descended (GR56.qmIso_descend). The textbook leaf IsogenyQuotient is
  removed; the converses (alIdeal_of_alTwist, x6CoarseModuliIdeal_of_twist, ideal_of_elkiesX6StarEvery,
  atkinLehnerW_eq) now take gagaMorphism and mumfordTorsionAlgClosed. Rebuilt; 52 theorems, all standard axioms;
  #discharges unchanged; autofold dry-run 16/18 -> 16/18; fold module compiles (standard axioms).
- VERIFIED (compiled): §9 residueImage_comp_iso, GR512At, gr512At_of_iso, gonzalezRotgerThm512X6_of_one (GR's
  Thm 5.12 statement on one witness => on every witness, given T5), gr512At_of_thm512. 56 theorems, standard
  axioms; #discharges unchanged (11194 theorems checked); FoldDryRun.lean recompiled, standard axioms.
- Not done (analysis in docs/research/x6-coarse.md §4): Elkies (a) Q(X/W) = Q(X)^W (no quotient curve in Lean);
  Elkies (c) every-CM-point from the-CM-point (needs exactness HasCM* => com = R, Q(sqrt(-6)) closed facts, Galois
  invariance of com and orbit count; class number not needed); GR T1 (Shimura's moduli interpretation of the
  complex uniformization; not provable as glue).
- Final state 02:40: contribution X6AtkinLehnerIdeal.lean (56 theorems, standard axioms), autofold.json and
  autofold-x6only.json dry-runs 16/18 -> 16/18, FoldDryRun.lean compiles.

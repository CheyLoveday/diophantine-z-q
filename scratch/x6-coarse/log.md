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

# gamma1-basis results log

- Base: wip/gamma1-basis at 4ce18aa42 (descendant of 8ba86099); merged origin/main (ee33f2143, CI-only changes).
- Target field: HDec.HSyn.OpenResearchLeaves41.gamma1IntegralSpan : CoeffFieldFinite.Gamma1IntegralSpan
  (ZInQKernel/OneProof/H/TailZ66.lean:34; def at ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFinite.lean:406). VERIFIED (read).
- Consumer: CoeffRational.eigenformCoeffFieldFinite_of_heckePrime (TailZ56/57/65) -> DSCoeffExt.EigenformCoeffFieldFinite,
  which quantifies over all k >= 2 and all chi : DirichletCharacter C N (DSCoeffExt.lean:460). VERIFIED (read).
- Mathlib Gamma1 N: (A 0 0 = 1, A 1 1 = 1, A 1 0 = 0) in ZMod N (CongruenceSubgroups.lean:136), i.e. c = 0, a = d = 1
  mod N: Gamma_1(N), not Gamma^1(N); contains T, so period-1 q-expansion at infinity. VERIFIED (read).
- New file ZInQKernel/Contrib/OneProof/Gamma1IntegralBasis.lean: def Gamma1Basis.Gamma1IntegralBasis (leaf),
  gamma1IntegralSpan_of_basis / old_of_basis (bridge), gamma1IntegralBasis_of_span (converse), iff.
- lake build +Contrib.OneProof.Gamma1IntegralBasis +OneProof.Main +OneProof.Discharges: success, 16070 jobs
  (build.log); frozenTarget standard axioms. VERIFIED (compiled).
- Discharges.lean (#discharges): DISCHARGES [OpenResearchLeaves41.gamma1IntegralSpan] by
  Gamma1Basis.gamma1IntegralSpan_of_basis and by Gamma1Basis.old_of_basis, still assumes [Gamma1Basis.Gamma1IntegralBasis],
  axioms [propext, Classical.choice, Quot.sound]; converse and iff standard axioms; no sorry (discharges-output.txt). VERIFIED.
- autofold.py autofold.json --dry-run: strict 12/23 on 35 -> 12/23 on 35; strictest 11/24 -> 12/23; tree untouched.
  FoldDryRun.lean (line 1 stripped): compiles, sixContactMin_of_open60 and openResearchLeaves41_of_OpenResearchLeaves42
  standard axioms (foldrun-output.txt). VERIFIED.
- PARI/cypari2 not available on this host (~/pyenv missing); odd-weight example eta(z)^3 eta(7z)^3 left STANDARD from memory.

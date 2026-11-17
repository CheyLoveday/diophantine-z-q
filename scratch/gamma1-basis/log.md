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

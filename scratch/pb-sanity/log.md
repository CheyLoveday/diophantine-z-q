# pb-sanity results log

Task: validate the definitions of pb-bypass (ZInQKernel/Contrib/OneProof/PanBerger.lean, merged from
origin/wip/pb-bypass c1636db9 into this branch at 73447464).

## Setup
- Build: copied (reflink) ~/dzq-wt/pb-bypass/.lake/build and lean/.lake/build; `lake build
  ZInQKernel.Contrib.OneProof.PanBerger ZInQKernel.Contrib.G9.KerTheta ZInQKernel.Contrib.G9.BdREmb`
  completed (VERIFIED, 2026-11-15 06:30).

## Plan (cheapest first)
1. B_cris^+ ≠ 0, B_cris ≠ 0, B_st ≠ 0: 0 ∉ tMonoid, via p^m·∏ log[ε_i] ≠ 0 in A_cris
   (argument in A_inf only: ker θ = (ξ) from Contrib/G9/KerTheta, ξ-adic separatedness of
   [ε]-1, lattice (N-1)!·A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p], θ[1/p], ∩ p^n O = 0).
2. bcrisAct is a group action by ring automorphisms; stAct σ bijective; stAct group law ⇔ cocycle.
3. Potentially trivial representations are pst.
4. Statement check of PanPrinted / BergerPrinted vs prints.

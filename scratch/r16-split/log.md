# r16-split results log

Base 24f97774 (wip/w72). Target: `LeafModCurves.R16_EichlerShimuraJ1'` (ZInQKernel/HDecomp/ModCurves/Leaves.lean:179),
bundle field `HDec.HSyn.OpenResearchLeaves20.r16`.

## Setup
- Build tree copied from ~/dzq-wt/p1-quot (same commit 24f97774, TailZ29 built): `.lake/build`, `lean/.lake/build`. VERIFIED
  (`scratch/r16-split/Test0.lean` loads `ZInQKernel.HDecomp.ModCurves.Leaves` in ~1 min).

## Findings (reading)
- `ZInQKernel/Contrib/HeckeAll/` is about `L(C_d, s)` (Hecke characters of ℚ(i)), not Hecke operators on `X₁(N)`: no
  `T_p`, `⟨d⟩` on modular curves or Jacobians anywhere in the tree (VERIFIED by reading hecke-all.md and the file list).
- `X₁(N)` is defined only through its function field `K_N = ℚ(j)(x(P))` (`IsX1Model`, Defs.lean §D); `J₁(N)` only through the
  Albanese property (`IsJ1`). `f : CF N 2` is Mathlib's analytic cusp form. No object links the two (no `X₁(N)(ℂ) ≅ Γ₁(N)\ℍ*`,
  no `q`-expansion of differentials). VERIFIED (reading Defs.lean).
- Open bundle leaves that bear on r16: `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4, alg. closed `k`; kernel
  `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed` gives `PkgI3.CharPolyIndepOfEll`), `mumfordTorsionAlgClosed` (T5;
  kernel LF4T5 gives `PkgI3.TateModuleFree`). VERIFIED (OPEN.md, grep).

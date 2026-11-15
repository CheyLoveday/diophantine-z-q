# gz-weil results log

Task: make gz-hl3's split of `hL3` net negative by turning `StrongWeilCurve` and `IsogenyLattice`
(Eichler–Shimura + Faltings, analytic form) into printed form or theorems, restricted to what the proof uses.

## Setup (2026-11-15 04:40 PST)
- base c118e9d2 (wip/gz-hl3). Build tree copied (reflink) from ~/dzq-wt/gz-hl3 (same ZInQKernel tree, built 11-15 04:12).

## Uses (VERIFIED, read)
- `StrongWeilCurve`, `IsogenyLattice` are used only in `eichlerShimuraParamAt_of_leaves`
  (GrossZagierHeegner.lean §5), which feeds `grossZagierHeegner_of_leaves` (all E) and
  `shimuraCMParamCd_of_leaves` (Cd.lean).
- The only consumer of hL3 in the chain is `GZDecomp.grossZagierCd_of_leaves`, at `E = C_d`,
  `d ≡ 5 mod 8` squarefree, `f` from `modular_cd`. GZStatements.Weak shows the Cd form
  `GrossZagierHeegnerCd` closes the chain (`frozenTarget_of_..._fhNonvanishingCd_grossZagierHeegnerCd`).
- So the parametrization leaf needed is exactly `ShimuraCMParamCd` (Cd.lean):
  `∀ d ≡ 5 (8) squarefree, EichlerShimuraParamAt C_d`.
- In it, `N = 32 d²` is forced (`GZStatements.level_eq_of_coeff_cd`, proved) and
  `eichler f` depends only on `coeff f n = aₙ(C_d) = heckeCoeff d n`
  (`GZStatements.LFunction_cd_eq_heckeCoeff`, proved).

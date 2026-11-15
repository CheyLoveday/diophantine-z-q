# elkies-coord results log

Task: discharge research field `elkiesX6StarPrinted` (ElkiesX6Star.ElkiesX6StarPrinted,
ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean:67) from Elkies' printed form `ℚ(X₆)^W = ℚ(t)` + charts.

## Setup
- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-wt/p1-quot (same commit 24f97774). VERIFIED
  `lake env lean` on a file importing ZInQKernel.Contrib.OneProof.ElkiesX6Star works without rebuild.

## Steps
- [x] ffPullback (comorphism of an automorphism on the function field), ffPullback_germ, res_eq_of_germ_eq:
  compile (scratch/elkies-coord/ElkiesCoord.lean). VERIFIED

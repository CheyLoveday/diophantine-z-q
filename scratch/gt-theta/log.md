# gt-theta results log

## 11-14 21:20 setup
- lean/.lake was missing in the worktree; copied from ~/dzq-wt/sem-prune/lean/.lake (the tree the copied .lake/build
  came from). `lake build --no-build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: up to date (VERIFIED).
- Targets (verbatim, TailU L1797/L1807): `HDec.QMSplit.Theta.IgusaPsi4`, `IgusaChi10`; specialized form
  `GapTheta.ThetaModularityM46` (gap-triage A2).

## Decomposition (VERIFIED by hand + scratch/gt-theta/py/chain.py numerics)
- Both M4 and M6 have invertible C; M = T(S1) R(C^{-T}) J0 T(S2) with S2 = [[1,-1],[-1,2]] for both,
  S1 = [[0,1],[1,0]] (M4), S1 = 0 (M6); R(C4^{-T}) = coordinate swap, R(C6^{-T}): (p,q,r) ↦ (r,-q,p).
- spAct M6 Ω = (−α1/Δ1, −β1/Δ1, −γ1/Δ1), spAct M4 Ω = (−α1/Δ1, β1/Δ1 + 1, −γ1/Δ1), (α1,β1,γ1) = (α+1, β−1, γ+2),
  Δ1 = α1γ1 − β1²; spFactor M6 = Δ1, spFactor M4 = −Δ1 (numerics, chain.py).
- Per even char m: θ_m(MΩ)² = −Δ1 · exp(πi P_m) · θ_{σm}(Ω)², P_m ∈ ½ℤ, σ a permutation of the 10 even chars,
  Σ_m P_m = −32 (M4), −10 (M6) (even). chain.py: relative error ≤ 3.3e-15 on all 20 cases.

## 11-14 21:30 ThetaModularityM46 (VERIFIED, compiled)
- scratch/gt-theta/Dev.lean (imports TailZ18) and ZInQKernel/Contrib/OneProof/ThetaModularityM46.lean (imports Main):
  `GapTheta.thetaModularityM46 : GapTheta.ThetaModularityM46` (no hypotheses),
  `GapTheta.thetaModularityM46Siegel` (all Ω ∈ SiegelH2), `thetaM4`, `thetaM6` (thetaSum8/thetaProd2 form),
  `s8WeightExact_of' (hT : ThetaModularityM46) (hG : GammaStarGen) : S8WeightExact`,
  `s20WeightExact_of'` (type of `LQ20.s20WeightExact_of`), `s8WeightExact_of_gen`, `s20WeightExact_of_gen` (only hG).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ThetaModularityM46`:
  success. `#print axioms`: [propext, Classical.choice, Quot.sound] for all six.
- `#discharges` (scratch/gt-theta/Discharges.lean, output discharges_out.txt):
  "#discharges: 72 open hypotheses, 87 theorems checked, 0 discharge one" — expected: ThetaModularityM46 is a
  specialization, not an open hypothesis; a fold must reroute the consumers.
- Consumer sites (live chain): TailX L196 (`r4 := thetaModularity_of r.igusaPsi4 r.igusaChi10`, feeds the old
  bundle field `r4`, used at TailK L315 `qmDenZeroCM3_of_leaves4 r.r4` and TailO L2881 `base2_of_base3 r.r4`) and
  TailZ4 L237 (`qmHauptmodulBase3_of_leaves (thetaModularity_of ...)`, through TailZ3 L1211 into TailZ2's section
  `variable (hT : PkgI1.ThetaModularity)` L294, whose every use is `auto8 hT`/`auto20 hT` = `s8WeightExact_of hT`,
  `s20WeightExact_of hT`). TailJ L5039 (`hTM`) is the same `s8WeightExact_of hTM hG` pattern.

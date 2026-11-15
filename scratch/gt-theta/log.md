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

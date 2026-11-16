# hodgetate-from-dr results log

## 2026-11-16 15:00 setup
- Merged origin/main: already up to date; origin/wip/integrate-w82 already in HEAD (5e235a40a).
- lean/.lake/build was missing (unknown module prefix 'ZInQ'); copied from ~/dzq/lean/.lake/build (lean/ZInQ identical, diff -rq empty).

## Consumers of the field (VERIFIED by grep)
- `HodgeTateDecompAbVar` (ZInQKernel/OneProof/H/TailS.lean:347) is read in exactly one place:
  TailX.lean:195, `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT`
  (all other occurrences are bundle-to-bundle copies in TailZ*).
- `deRhamComparisonHT_of_leavesT` uses it for (i) `htMultOver w = g([w=0]+[w=-1])` (via `htMultOver_of_decomp`)
  and (ii) `FiniteDimensional ℚ_p V_p(A)` (via `finiteDimensional_of_decomp`). So the consumer needs the HT
  multiplicities and finite-dimensionality, i.e. the full numerical content; nothing smaller.

## Kernel inventory (VERIFIED by reading)
- No Hodge filtration on D_dR, no H^1_dR, no gr^i B_dR = C_p(i) in the kernel (grep "Fil", "Hodge filtration").
- KerTheta: B_dR^+ DVR with uniformizer xi, theta^+ : B_dR^+ -> C_p surjective with kernel (xi). No t = log[eps].
- `deRhamH1AbVarT` gives only dim_F D_dR(V^vee) = dim V (no filtration data).
- kinds.tsv flag of hodgeTateDecompAbVar: GLUE only because the coordinate form C(1)^g + C^g needs dim t*_{A'} = g.

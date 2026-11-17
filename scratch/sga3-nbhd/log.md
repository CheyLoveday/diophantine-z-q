# sga3-nbhd results log

Base: origin/main 5e235a40 (worktree HEAD c1e4ed1b8). Build: copied coeff-rational's .lake/build + lean/.lake/build
(same base + 2 added Contrib files); `lake build +ZInQKernel.OneProof.Main +...SGA3IdComp` replayed, 11 s. VERIFIED.

## Statements
- Field: `HDec.HSyn.OpenResearchLeaves28.sga3_VIB_3_10_Nbhd : SGA3IdComp.SGA3_VIB_3_10_Nbhd`
  (TailZ45 l.52), `SGA3IdComp.SGA3_VIB_3_10_Nbhd` at ZInQKernel/Contrib/OneProof/SGA3IdComp.lean:516. VERIFIED (read).
- Top readers (VERIFIED, read): TailZ45 l.90 (`sga7_IX_3_3_SH_of_pre ... (sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd ..)`),
  TailZ45 l.96 passes it to OpenResearchLeaves27; TailZ44 l.91 turns it into `sga3_VIB_3_10` of OpenResearchLeaves26,
  which older generations pass down.

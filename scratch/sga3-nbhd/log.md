# sga3-nbhd results log

Base: origin/main 5e235a40 (worktree HEAD c1e4ed1b8). Build: copied coeff-rational's .lake/build + lean/.lake/build
(same base + 2 added Contrib files); `lake build +ZInQKernel.OneProof.Main +...SGA3IdComp` replayed, 11 s. VERIFIED.

## Statements
- Field: `HDec.HSyn.OpenResearchLeaves28.sga3_VIB_3_10_Nbhd : SGA3IdComp.SGA3_VIB_3_10_Nbhd`
  (TailZ45 l.52), `SGA3IdComp.SGA3_VIB_3_10_Nbhd` at ZInQKernel/Contrib/OneProof/SGA3IdComp.lean:516. VERIFIED (read).
- Top readers (VERIFIED, read): TailZ45 l.90 (`sga7_IX_3_3_SH_of_pre ... (sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd ..)`),
  TailZ45 l.96 passes it to OpenResearchLeaves27; TailZ44 l.91 turns it into `sga3_VIB_3_10` of OpenResearchLeaves26,
  which older generations pass down.

## Consumer audit (UseProbe.lean, closure of ZInQ.OneProof.frozenTarget, 268667 constants; VERIFIED compiled, output UseProbe.out)
Constants in the closure that mention `CToPrinted.SGA3_VIB_3_10` (besides bundle structures/projections/mk of
OpenResearchLeaves14..26): sga3_VIB_3_10_of_nbhd, DictModels.SGA7Pre.{preimage_eq, sga7_IX_3_3_SH_of_pre},
SGA7PersistsNF.{sga7_IX_3_3_of_SH, body_of_SH}, GapPersists.{semistablePersistsDVR_of_printed,
semistablePersistsSHcp_of_printed, semistablePersistsSHcp_of_SH}, CToPrinted.{idComp_baseChange, idCompSubgroup_of,
idCompBaseChangeDVR_of, identityComponentBaseChangeDVRRange_of, identityComponentOLRange_of,
semistableNeronBaseChange_of_printed_full}.
Application points `h3 S G` (VERIFIED, read in source):
| reader | S | G |
|---|---|---|
| identityComponentOLRange_of (TailZ19 l.1514) | Spec 𝓞_L, L number field | 𝒢.G, 𝒢 : GroupModel A L (in semistableNeronBaseChange_of_printed_full: the Néron model 𝒩, semistable) |
| idCompSubgroup_of (l.1352) | any noetherian S | qc G; called at 𝒢.G over 𝓞_L (identityComponentOLRange_of) and at 𝒩.G over a DVR (PersistsDVR) |
| idComp_baseChange (l.1244) | any noetherian S | qc G; called at 𝒩.G over Spec 𝓞_L (semistableNeronBaseChange_of_printed_full l.1711, g = gO O) and over DVRs (SGA7Pre.preimage_eq, idCompBaseChangeDVR_of, body_of_SH x4) |
| identityComponentBaseChangeDVRRange_of (l.1613) | Spec O', DVR | bcO hO 𝒩.G |
| semistablePersistsDVR_of_printed (PersistsDVR l.212) | Spec O, DVR | 𝒩.G (GroupModelO) |
| body_of_SH (SGA7PersistsNF l.332) | Spec P', DVR | Y₁ = bcO hPP' 𝒩₁.G |
Finding: NOT every use is over a local base. semistableNeronBaseChange_of_printed_full (field semistableNeronBaseChange,
read by TailZ4's stable-height rows; produced in the chain at TailZ23 l.775) needs `IsOpen (idCompSet 𝒩.G)` for a
Néron model 𝒩 over 𝓞_L (to build the open subgroup model 𝒢₀ with range 𝒩⁰). Over a Dedekind base with infinitely
many closed points the elementary argument does not apply.

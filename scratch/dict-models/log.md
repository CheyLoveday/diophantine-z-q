# dict-models results log

Base e22df37c (origin/main; top module TailZ41, `sixContactMin_of_open34`). Four research fields, all in
`HDec.HSyn.OpenResearchLeaves26` (ZInQKernel/OneProof/H/TailZ41.lean).

## Statements located (VERIFIED, read in the tree)

| field | Lean constant | file |
| --- | --- | --- |
| sga7_IX_3_3_SH | `SGA7PersistsNF.SGA7_IX_3_3_SH` | ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean:60 |
| raynaudSemistableSH | `ReductGlue.RaynaudSemistableSH` | ZInQKernel/OneProof/H/TailZ14.lean:1105 |
| mumfordGroupLaw | `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` | ZInQKernel/Contrib/OneProof/MumfordRigidity.lean:82 |
| neronBaseChangeStrictHenselization | `GapSHPair.NeronBaseChangeStrictHenselization` | ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1527 |

Consumers in the chain (VERIFIED, git grep of `.field` reads):
- `sga7_IX_3_3_SH`: TailZ33:104 (`sga7_IX_3_3_of_SH`), TailZ41:88 (`semistablePersistsSHcp_of_SH`).
- `raynaudSemistableSH`: TailZ23:723 (`ReductB.raynaudSemistable_of_SH_pair`).
- `mumfordGroupLaw`: TailZ23:708/760/786 and TailZ34:159, all through `qmFamilyGroupLaw_of_groupLaw`
  (TailZ40:205), whose `S` is any proper smooth curve over ℚ (not assumed connected).
- `neronBaseChangeStrictHenselization`: TailZ28:113, TailZ33:101, TailZ41:88.

Existing pieces reused (VERIFIED, read): `CToPrinted.idComp_baseChange` (TailZ19:1238; from SGA3_VIB_3_10 and
GeomConnOfRationalPoint); `UnipotentForward.IsSemistableRes` (the k(s) form, UnipotentForward.lean:88);
`ReductGlue.hasSemiAbelian_pullback` (TailZ14:1006, field isomorphisms only);
`GapSHPair.neronBaseChangeStrictHenselization_of_unramified` (StrictHenselizationPair.lean).

## Build

- 02:5x copied ~/dzq-check2/.lake/build (at 2880fef1) and lean/.lake/build; LPrefix etc. out of date for e22df37c,
  rebuilding the three import cones with `lake build`.

# group-law-dvr results log

Base wip/group-law 680165b2, merged origin/main c1e4ed1b (merge 27a3b989, no conflicts). Build tree copied
(cp --reflink) from ~/dzq-wt/leaf-fold33b (25415c1c, TailZ45 built), then `lake build` of Main, Discharges and
MumfordGroupLawRed.

## Field on the merged tree (VERIFIED, read)
- `HDec.HSyn.OpenResearchLeaves28.mumfordGroupLawConn : DictModels.MumfordConn.MumfordGroupLawConn`
  (ZInQKernel/OneProof/H/TailZ45.lean:58), read only at TailZ45:85
  `mumfordGroupLaw := DictModels.MumfordConn.mumfordGroupLaw_of_conn n.mumfordGroupLawConn` (fills
  `OpenResearchLeaves27.mumfordGroupLaw : MumfordRigidity.MumfordGroupLaw`; older generations 14..27 carry the same
  field type, consumed by TailZ23 (3 sites) and TailZ34 (1 site) through `qmFamilyGroupLaw_of_groupLaw`).

## neronSchemeExtensionExists does not reach the chain's DVRs (VERIFIED, read)
- `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (Contrib/NeronC/NeronGroup.lean:82) quantifies over number
  fields `L` and gives Néron models over `𝓞 L` only. `𝓞 L` is never local (infinitely many maximal ideals), and
  the DVRs the chain needs (`qmFamilyGroupLaw_of_dvr`: local rings `Γ(S,V)_𝔭` of a proper smooth curve `S/ℚ` at
  closed points) contain `ℚ` (equal characteristic 0). No base change relates them. So the field gives no
  Néron model over the chain's DVRs. No other open field of the bundles (OPEN.md) gives Néron models over a
  general DVR or group laws on families.

## Build of the merged tree (VERIFIED, 11-16 15:20)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`:
  14107 jobs, OK.

## Closure check on the merged tree (VERIFIED, ClosureCheck.lean -> closure_check.txt, 11-16 15:25)
- IN frozenTarget's closure: MumfordGroupLawConn, mumfordGroupLaw_of_conn, MumfordGroupLaw, QMFamilyGroupLaw,
  qmFamilyGroupLaw_of_groupLaw, NeronSchemeExtensionExists. Not in it: MumfordGroupLawDVR.
- Non-bundle users of MumfordGroupLaw / qmFamilyGroupLaw_of_groupLaw: `exists_qmAbScheme_gl` (inside
  qmFamilyGroupLaw_of_groupLaw), `HDec.HSyn.x6Rows_of_open14`, `HDec.HSyn.researchLeaves9_of_open14` (TailZ23),
  `DCY3Used.y3Connected_of_leaves` (via TailZ34); user of mumfordGroupLaw_of_conn: only
  `openResearchLeaves27_of_OpenResearchLeaves28` (TailZ45). So the chain still needs only QMFamilyGroupLaw, and
  `mumfordGroupLaw_of_conn` is the only route from the field into the chain (as the task said).

## Lean: ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean (VERIFIED compiles, `lake env lean`, 11-16 ~16:10)
- LEAF `NeronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over affine Dedekind schemes, existence half),
  LEAF `NeronSchemeExtensionDVR` (its DVR case), `dvr_of_dedekind`,
  `neronSchemeExtensionExists_of_dedekind : NeronSchemeExtensionDedekind → NeronC.NeronSchemeExtensionExists`.
- GLUE `NeronGoodModelIso` (ψ : F → N, F as in MumfordGroupLawDVR, N smooth separated, ψ_K iso ⇒ ψ iso).
- `mumfordGroupLawDVR_of_neron : NeronSchemeExtensionDVR → NeronGoodModelIso → MumfordGroupLawDVR`
  (group law = grpObjOfNeron on N transported along ψ; η = e by pullback_map_injective).
- `qmFamilyGroupLaw_of_neron`, `qmFamilyGroupLaw_of_neronDedekind`, `dvr_of_conn : MumfordGroupLawConn → MumfordGroupLawDVR`.
- `#print axioms`: all [propext, Classical.choice, Quot.sound].

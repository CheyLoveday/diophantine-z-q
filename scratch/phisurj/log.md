# phisurj log

Base wip/leaf-fold33b 0e3c31258; `git merge origin/main`: already up to date (2026-11-16 17:40).

## Findings (reading)
- Field: `PicDict.MumfordPhiSurjectiveAC` (PicDictionary.lean:1564), in `HDec.HSyn.OpenAddedLeaves20`
  (TailZ47.lean:29), other fields picRepresentableAbVar, picZeroAbVar, weilPairingMumford. VERIFIED (read).
- Consumers of the field (VERIFIED, grep): TailZ45:123, TailZ46:104, HomFreeFiniteAlgClosedReroute.lean:2082,
  all through `PicFix.phiAmpleIsogeny_of_printed _ l.mumfordPhiSurjectiveAC : T09Pic.PhiAmpleIsogeny`.
- The statement quantifies over Mumford's Pic⁰ = translation-invariant classes (`AC.IsTI`), not over points of
  the identity component `B` of the Picard scheme. So it contains (a) "every TI class is a point of B"
  (the converse of the proved `picZeroPtsTranslInv_of_leaves`), besides (b) "λ_L : A → B is onto".
- No proved theorem in the tree gives (a), dim Pic⁰ = g, #A[n] = n^{2g}, or torsion density (code survey).
- `AvSplit.MumfordTorsionAlgClosed` (TailQ.lean:1257, A(k)[n] ≅ (ZMod n)^{2g}) is an open textbook leaf
  (`OpenTextbookLeaves15.mumfordTorsionAlgClosed`) and is proved on origin/proof/picard-fibres-20261116
  (`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, not merged here). VERIFIED (git show).

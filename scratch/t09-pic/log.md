# t09-pic results log

Field: `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`
(`∀ K A, Nonempty (SymmIsogeny A)`), Mumford §§6, 8, 20, 23.

## Setup
- `lake build ZInQKernel.Hypotheses.JHeight` once (builds upstream `lean/` helpers; else "unknown module prefix 'ZInQ'").
- Check: `lake env lean scratch/t09-pic/Pic.lean` (imports TailB + vendored Picard/QuasiProjective/Twist + FrobChain.Rigidity).

## Compile outcomes
- 2026-11-14 17:58 Pic.lean v1 (§0 verbatim copy + rfl; mumfordBundle, phiL, identityComponent, IsPicZero,
  IsVeryAmple; `exists_isVeryAmple` proved): 0 errors. VERIFIED.

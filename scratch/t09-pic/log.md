# t09-pic results log

Field: `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`
(`∀ K A, Nonempty (SymmIsogeny A)`), Mumford §§6, 8, 20, 23.

## Setup
- `lake build ZInQKernel.Hypotheses.JHeight` once (builds upstream `lean/` helpers; else "unknown module prefix 'ZInQ'").
- Check: `lake env lean scratch/t09-pic/Pic.lean` (imports TailB + vendored Picard/QuasiProjective/Twist + FrobChain.Rigidity).

## Compile outcomes
- 2026-11-14 17:58 Pic.lean v1 (§0 verbatim copy + rfl; mumfordBundle, phiL, identityComponent, IsPicZero,
  IsVeryAmple; `exists_isVeryAmple` proved): 0 errors. VERIFIED.
- 2026-11-14 18:10 Pic.lean v2: `comp_classify`, `mumfordBundle_restrict_zero`, `eta_comp_phiL` (φ_L(0)=0 for the Picard group law) proved: 0 errors. VERIFIED.
- 2026-11-14 18:20 Pic.lean v3: `exists_hom_comp_eq_phiL` (φ_L = λ_L ≫ ι with λ_L : Hom A B, for any (B, ι) with IsPicZero) proved: 0 errors. VERIFIED.

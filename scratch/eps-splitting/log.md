# eps-splitting results log

Base: wip/hgz-steps 92fd272e, merged origin/main (e1b31749) as dc6321558.

## Statements and compile outcomes

- `scratch/eps-splitting/QuadInt.lean` (development file, imports Mathlib + `ZInQKernel.Contrib.OneProof.GrossZagierScheme.EpsD`):
  - `exists_int_repr`: for `D` a fundamental discriminant (`Int.IsFundamentalDiscr`), `D < 0`, `[K:ℚ] = 2`, `δ² = D`:
    every `x ∈ K` integral over `ℤ` is `a + b θ`, `θ = (D + δ)/2`, `a b ∈ ℤ`. VERIFIED (compiles).
  - `adjoin_thetaO_eq_top`: `Algebra.adjoin ℤ {θ} = ⊤` in `𝓞 K`. VERIFIED.
  - `minpoly_thetaO`: `minpoly ℤ θ = X² − D X + (D² − D)/4`. VERIFIED.
  - `isInertIn_iff`, `isSplitIn_iff`, `isRamifiedIn_iff`: transfer through Mathlib's Kummer–Dedekind
    (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`, `ZModXQuotSpanEquivQuotSpan`,
    `ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'`). VERIFIED.
  - `splitType_of_irreducible`, `splitType_of_eq_mul`, `splitType_of_eq_mul_self`. VERIFIED.
  - `splitType_epsD`: `SplitType K p (epsD D p)` for every prime `p`, i.e.
    `(IsSplitIn K p ↔ ε_D(p) = 1) ∧ (IsInertIn K p ↔ ε_D(p) = −1) ∧ (IsRamifiedIn K p ↔ ε_D(p) = 0)`. VERIFIED (compiles, 01:5x).

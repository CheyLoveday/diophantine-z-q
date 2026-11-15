# gz-heegner results log

Task: prove `ZInQ.GZHL3.HeegnerPointRational` (gz-hl3) from `T5Glue.ShimuraMainCM` and
`T5Glue.X0ModuliGalois` plus glue.

## 2026-11-15
- Build: copied `.lake/build` and `lean/.lake/build` from ~/dzq-wt/gz-hl3 (bbb6c764; no ZInQKernel diff vs base c118e9d2).
- FINDING (analysis, SPECULATIVE until written up): `X0ModuliGalois` only covers `g` with
  `IsRatModFn N g`, whose third clause is a `q`-expansion valid on all of `ℍ` (so `g` is holomorphic on `ℍ`).
  The coordinates `x∘φ`, `y∘φ` of a modular parametrization `φ = weierPt E L (c·φ_f)` have poles at the
  non-cuspidal points of `φ⁻¹(O)` (nonempty unless every preimage of `O` is a cusp, e.g. deg φ > #cusps over O),
  so they are not `IsRatModFn`; no regular-on-ℍ rational function on `X₀(N)` built from `φ` is available without
  the algebraic theory of `X₀(N)_ℚ`. Plan: state the printed form of the canonical-model theorem for every
  `g ∈ ℚ(X₀(N))` regular at the two points (`X0ModuliGaloisMero`), derive `X0ModuliGalois` from it, and derive
  `HeegnerPointRational` from it and `ShimuraMainCM` (via kernel `CMModuli`).

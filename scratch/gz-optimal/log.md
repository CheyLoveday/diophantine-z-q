# gz-optimal results log

Base: wip/gz-moduli 85111fc7. Build tree: reflink copy of ~/dzq-wt/gz-moduli/.lake/build and lean/.lake/build.

## Statements read (VERIFIED, in the tree)
- Target leaf: `ZInQ.GZModuli.GrossZagierModuliCd` (ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean:155),
  = ∀ d ≡ 5 (8) squarefree, `GrossZagierModuliAt (shortCurve (-(d:ℚ)^2))` (line 136): every φ = (X, Y) with
  `IsModularParam N E X Y` (X, Y ∈ ℚ(X₀(N)), Weierstrass eqn, pole at ∞).
- Consumer: `grossZagierFormulaCd_of_moduli : GrossZagierModuliCd → GZHL3.GrossZagierFormulaCd`; it applies the leaf only
  to φ = weierPt E L (c φ_f), c ∈ ℚ^×, c Λ_f ⊆ L (`GZHL3.GrossZagierFormulaAt`).
- After heegner-32 (origin/wip/heegner-32 718d8d4c) and gz-conj, the C_d split of hL3 is GrossZagierFormulaCd (+ hCM) only;
  X0ModuliGaloisMero is no longer used (heegner-32 .fleet summary, VERIFIED read).
- Tau Ceti canonical height: `canonicalHeight_nonneg`, `canonicalHeight_eq_zero_iff_isOfFinAddOrder` (Northcott free over
  number fields), `canonicalHeight_zsmul` (VERIFIED read).
- Mathlib `WeierstrassCurve.LFunction` uses `W.minimal R` locally: model-independent (VERIFIED read,
  Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean).
- Additivity of weierPt: heegner-32's `weierPt_short_add` (y² = x³ + Ax only) from vendored FLT
  `PeriodPair.isUniformization_toPoint` (VERIFIED read). Not in base; to be reproved for a₁ = a₂ = a₃ = 0.

## Computations
- PARI `ellweilcurve` (scratch/gz-optimal/py/optimal_cd.py): Smith invariants of L_{E'} in L_f over the isogeny class
  of C_d; [1,1] marks the X₀(N)-optimal curve. d = 5 (N = 800): C_5 optimal, class smith [[1,1],[2,1],[2,1],[2,1]].
  d = 13 (N = 5408): C_13 optimal, same pattern. (VERIFIED, computed)

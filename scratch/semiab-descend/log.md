# semiab-descend results log

Base: wip/height-fix 49e6d97d + origin/main (merge 530ef0e7) + origin/wip/leaf-fold32b (merge de506e7e).

## Target
`ZInQ.HeightFix.SemiAbelianDescendsPerfect` (ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean:611).

## Consumers (VERIFIED, grep)
- only `isSemistableRes_of_geom` (PrintedStableHeight.lean:630) applies it, at `k = 𝔭.ResidueField` for a maximal
  ideal `𝔭` of `𝓞_L` (finite field, `perfectField_residueField`). Everything else takes it as a hypothesis
  (`isPrintedStableHeight_of`, `bostLowerBound_of_printed`, `gaudronRemondThm14_of_printed`, javanpeykar/pazuki).

## Plan (decomposition)
- LEAF `ChevalleyPerfect` (Chevalley's structure theorem over a perfect field, existence + uniqueness;
  Conrad 2002 Thm 1.1, UNVERIFIED locator), kernels as scheme-theoretic kernels (pullback along the unit).
- GLUE to prove: identity component over a field (open subgroup); open subgroups over k̄ closed (Jacobson);
  `U'_{k̄}` = base change of `G⁰`; kernel `ker π'` ≅ `Spec k̄[x₁^{±1},…,x_r^{±1}]` (Yoneda on affine points);
  `U'` smooth (shear iso + flat descent of smoothness, Mathlib `DescendsAlong @Smooth`); `G⁰` smooth (descent along
  `Spec k̄ → Spec k`); kernel of `π_{k̄}` smooth connected affine; uniqueness ⇒ kernels agree; transport.

## Findings / compile outcomes
- A.lean §1-§4 COMPILED (VERIFIED): isIso_of_bijective_affine (Yoneda on affine points over any S), exists_algPtMap, exists_iso_algPt, isSmoothConnAffineKer_of_torus (functor-of-points split torus kernel ≅ Spec K[x^±1], hence smooth/affine/connected).

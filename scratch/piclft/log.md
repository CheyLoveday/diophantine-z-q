# piclft results log

Task: remove `picLocFinType` (PicDict.PicLocFinType, ZInQKernel/Contrib/OneProof/PicDictionary.lean:2201).
Base wip/leaf-fold33b c7fbc273; `git merge origin/main`: already up to date (2026-11-16 21:15).

## Findings (reading)
- `picardFunctor f` = fppf sheafification of `picardPresheaf f` (T ↦ Pic(X ×_S T)), over all of `Over S`
  (CloudW07 Picard/Sheaf.lean). VERIFIED (read).
- `PicDict.pushforwardUnitUniversal` is proved (PicDictionary.lean:2334), so `PicDict.Θ` (vendored Kleiman 9.2.5,
  `picardFunctorNormalizedIso`) is an iso: `toPicardFunctor A.X.hom` is surjective at every `T`. VERIFIED (read).
- CloudW07 `Scheme.Modules.exists_isFinitePresentation_pullback_iso_of_isLimit` (Modules/Limits/Objects.lean:335):
  fp module sheaves descend along directed inverse limits of qc separated schemes with affine transitions
  (EGA IV 8.5.2(ii) for modules). `exists_hom_of_affine_limit` / `exists_hom_eq_of_affine_limit` (Hom.lean):
  morphisms / equalities descend on affine limits. VERIFIED (read).
- Invertible ⇒ IsFiniteLocallyFree ⇒ IsFinitePresentation are instances in CloudW07. VERIFIED (read).

## Plan
(I) LFT criterion: if every `Spec B → X` over `K` factors through `Spec S`, `S ≤ B` a f.g. `K`-subalgebra, then
`X → Spec K` is LFT. (II) transfer through `rep` + surjectivity of `toPicardFunctor`. (III) Pic spreading out
(EGA IV 8.5.2 + 8.5.5 for invertible sheaves) on `A ×_K Spec B = lim A ×_K Spec S`.

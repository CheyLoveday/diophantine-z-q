# kleiman-site results log

- 11-17 01:55 base wip/kleiman-section2 7591fc3b; merged origin/wip/leaf-fold33b (75d94fe7) and origin/main -> bbbcabce. VERIFIED (git).
- Field status (VERIFIED, docs/one-proof/OPEN.md at bbbcabce): OneProof field is still `HDec.HSyn.OpenAddedLeaves25.kleimanPicZeroProper : PicFix.KleimanPicZeroProper`; `KleimanSection2.KleimanPicZeroProper954` is not yet a bundle field (kleiman-section2's hand fold TailZ56 not integrated).
- Plan (Lean): site := `fppfPrecoverage.comap ((LocNoeth S).ι ⋙ Over.forget S)` toGrothendieck on `(LocNoeth S).FullSubcategory`. Continuity of ι via Mathlib `Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy` (pullbacks of fppf maps between LN schemes stay LN); cocontinuity from covers by LN schemes; iso via `Presheaf.isLocally{Injective,Surjective}_whisker` + `W_of_isLocallyBijective`. Draft scratch/kleiman-site/Site.lean.

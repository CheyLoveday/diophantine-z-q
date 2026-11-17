# kleiman-site (fleet note)

**Result.** The site comparison for Kleiman 9.5.4 is proved in Lean. The leaf restricts the big-site fppf
sheafification to locally Noetherian schemes; Kleiman sheafifies on the locally Noetherian site. The leaf is
restated over Kleiman's site and implies `KleimanSection2.KleimanPicZeroProper954`. File:
`ZInQKernel/Contrib/OneProof/KleimanPicZeroSite.lean` (namespace `KleimanSite`). It imports and so lands
`KleimanPicZeroProperQuot.lean`.

* Site: `fppfTopologyLN S`, Mathlib's `fppfPrecoverage` pulled back to `(LocNoeth S).FullSubcategory`. The inclusion
  is continuous (fppf pullbacks of locally Noetherian schemes stay locally Noetherian) and cocontinuous (fppf covers
  of a locally Noetherian scheme are by locally Noetherian schemes).
* `sheafifyRestrictIso F` for every presheaf `F`: sheafification on the site of the restriction ≅ restriction of the
  big-site sheafification. The proof: the restricted `toSheafify` is locally bijective onto a sheaf.
* New leaf (recommended), `KleimanPicZeroProper954SiteQ`: Kleiman 9.5.4 with `Pic_{(X/K)(fppf)}` exactly as Def. 9.2.2
  defines it, the sheafification of `Pic(X_T)/Pic(T)` on Kleiman's site. Rated printed form; locator UNVERIFIED on
  host. Variant leaf `KleimanPicZeroProper954Site` uses `Pic(X_T)`.
* Proved: `kleimanPicZeroProper954_of_siteQ`, `kleimanPicZeroProper954_of_site`, `picZeroAbVar0_of_siteQ`.
  Count: **−1 GLUE** relative to kleiman-section2's field.

**Compiles (VERIFIED).** The file has no errors or warnings. The build of Main + Discharges + the file completed
(16076 jobs). Axioms are standard only. `#discharges` (`scratch/kleiman-site/discharges-output.txt`) has no
`KleimanSite` line. This is expected: the frontier field is still the stronger `PicFix.KleimanPicZeroProper`, and
the field `kleimanPicZeroProper954` exists only after kleiman-section2's hand fold.

**Remains.** kleiman-section2's hand fold (TailZ56, written against an older top) must be rebased onto the current
top, TailZ67, using the weaker-leaf bypass; or that fold can put `kleimanPicZeroProper954SiteQ` in directly, with
`KleimanSite.picZeroAbVar0_of_siteQ`. After that, `scratch/kleiman-site/autofold.json` applies. Also needed: a
`locators.md` row and a reading of Kleiman 9.2.2 / 9.4.8 / 9.5.4. Report: `docs/research/kleiman-site.md`.

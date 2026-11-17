# kleiman-site: Kleiman 9.5.4 over Kleiman's own site

## Result

**The site comparison is proved in Lean, and Kleiman 9.5.4 is restated over Kleiman's site.**
`KleimanSection2.KleimanPicZeroProper954` follows from the restated leaf
`KleimanSite.KleimanPicZeroProper954SiteQ`. The restated leaf is Kleiman, *The Picard scheme*, Thm 9.5.4, with
`Pic_{(X/K)(fppf)}` taken literally from Def. 9.2.2: the sheafification of `T ↦ Pic(X_T)/Pic(T)` on the site of
locally Noetherian `K`-schemes with the fppf topology. So the one formal gap the reviewer found
(q12-kl954-reading: the leaf restricts the big-site sheafification, Kleiman sheafifies on the locally Noetherian site)
is closed. The other gap, the quotient by `Pic(T)`, is closed by kleiman-section's `picardFunctorIsoKleiman`.

* File: `ZInQKernel/Contrib/OneProof/KleimanPicZeroSite.lean` (namespace `KleimanSite`). It imports
  `KleimanPicZero954` and `KleimanPicZeroProperQuot`, so this lands `KleimanPicZeroProperQuot.lean`, which no module
  imported before. It compiles with no errors and no warnings, has no sorry, and every theorem uses only
  `propext`, `Classical.choice`, `Quot.sound` (VERIFIED, `#print axioms`; §4).
* Counts, relative to kleiman-section2's hand fold (field `kleimanPicZeroProper954`, rated GLUE by the review because
  of the site): **one GLUE field out, one LEAF in (printed form), so −1 GLUE**. Everything else is proved glue.

## 1. Kleiman's site in Lean (VERIFIED compiled)

* `fppfPrecoverageLN S := fppfPrecoverage.comap ((LocNoeth S).ι ⋙ Over.forget S)` on `(LocNoeth S).FullSubcategory`
  (locally Noetherian `S`-schemes, `LocNoeth` from kleiman-section2). A family is covering iff its image in `Scheme`
  is a jointly surjective family of flat morphisms locally of finite presentation (Mathlib's `fppfPrecoverage`).
  `fppfTopologyLN S` is the Grothendieck topology it generates.
* `isContinuous_ι`. The inclusion `(LocNoeth S).ι : LN ⥤ Over S` is continuous for `fppfTopologyLN S` and Mathlib's
  `fppfTopology.over S`. The proof uses Mathlib's `Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy` after
  `over_toGrothendieck_eq_toGrothendieck_comap_forget`. The three inputs are proved here:
  * `HasPullbacks`;
  * `IsStableUnderBaseChange`;
  * `PullbacksPreservedBy ι`.

  All three rest on one fact: if `f` is locally of finite type, the pullback in `Over S` of a cospan `g, f` of
  locally Noetherian schemes is again locally Noetherian (`locNoeth_pullback_of_right/left`, by base change of
  `LocallyOfFiniteType` and `LocallyOfFiniteType.isLocallyNoetherian`). It is then a pullback in the full
  subcategory (`isPullback_pbLN`, by `IsPullback.of_map`), and `ι` preserves it (`preservesLimit_cospan`, by
  `IsPullback.preservesLimit_cospan_iff`).
* `isCocontinuous_ι`. A covering sieve of `ι T` contains an fppf family
  (`mem_toGrothendieck_iff_of_isStableUnderComposition`; this needs `fppfPrecoverage.HasIsos`, proved here as a local
  instance). Its members are locally of finite type over the locally Noetherian `T`, hence locally Noetherian. So the
  family lifts to a covering family of `T` in the subcategory, and that family lies in the pulled-back sieve.

## 2. The comparison (VERIFIED compiled)

For every presheaf `F : (Over S)ᵒᵖ ⥤ Type (u+1)`:

* `restrictToSheafify F := whiskerLeft ι.op (toSheafify (fppfTopology.over S) F)`. By Mathlib's
  `Presheaf.isLocallyInjective_whisker` and `isLocallySurjective_whisker`, which apply because `ι` is cocontinuous,
  it is locally injective and locally surjective for `fppfTopologyLN S`. Its target is a sheaf (`isSheaf_restrict`,
  by continuity).
* `sheafifyRestrictIso F : sheafify (fppfTopologyLN S) (ι.op ⋙ F) ≅ ι.op ⋙ sheafify (fppfTopology.over S) F`. The
  sheafified map is an isomorphism (`W_of_isLocallyBijective`, as in `picardFunctorIsoKleiman`), composed with
  `isoSheafify` of the sheaf target. `toSheafify_sheafifyRestrictIso` says that `toSheafify` followed by this iso is
  `restrictToSheafify F`.

Instances:

* `kleimanIso f : (kleimanPicardSheafSite f).obj ≅ picardFunctorLN f` (`F = picardPresheaf f`, i.e. `T ↦ Pic(X_T)`);
* `kleimanIsoQ f : (kleimanPicardSheafSiteQ f).obj ≅ picardFunctorLN f`, with
  `F = KleimanSection.kleimanPicardPresheaf f`, i.e. `T ↦ Pic(X_T)/Pic(T)`. It is composed with
  `KleimanSection.picardFunctorIsoKleiman f` (kleiman-section, proved for every `f`, no section).

This is the reviewer's argument, verbatim in Lean. An fppf cover of a locally Noetherian scheme consists of locally
Noetherian schemes, so the restricted presheaf map is locally bijective onto a sheaf. It is not Mathlib's
cover-dense comparison lemma: `ι` is not cover-dense, since a scheme that is not locally Noetherian has no cover by
locally Noetherian schemes. The argument uses cocontinuity plus continuity instead.

## 3. The leaves and derivations

`KleimanPicZeroProper954SiteQ` (**LEAF, printed form; recommended**) has the hypotheses of
`KleimanPicZeroProper954` word for word:
* a closed immersion into `ℙ^N_K` over `K`;
* `GeometricallyIntegral`;
* `geometrically IsNormalScheme`;
* a `K`-point;
* `P` locally of finite type over `K`;
* `V` open with underlying set the identity component.

The only change is the functor: `rep : (kleimanPicardSheafSiteQ X.hom).obj.RepresentableBy ⟨P, _⟩`, a
representation on Kleiman's site of Kleiman's Def. 9.2.2 sheaf. The identity point `unitPtSiteQ` classifies
`1 ∈ Pic(X)/Pic(K)` via `toSheafify` on the site. The identity component is `identityComponentSiteQ`.

`KleimanPicZeroProper954Site` (LEAF, printed form) is the same with `T ↦ Pic(X_T)` sheafified on the site. Kleiman
remarks right after Def. 9.2.2 that this is the same sheaf, and `kleimanIso` / `kleimanIsoQ` prove it here.

Proved:
* `kleimanPicZeroProper954_of_siteQ : KleimanPicZeroProper954SiteQ → KleimanSection2.KleimanPicZeroProper954`.
  `repSiteQ` transports a representation along `kleimanIsoQ.symm`. `unitPtSiteQ_repSiteQ` shows that the identity
  points agree: the site comparison and the quotient comparison each send the unit class to the unit class, by
  `toSheafify_sheafifyRestrictIso` and `toSheafify_naturality` for `KleimanSection.quot`. So the identity components
  agree.
* `kleimanPicZeroProper954_of_site : KleimanPicZeroProper954Site → KleimanPicZeroProper954`, the same argument.
* `picZeroAbVar0_of_siteQ : KleimanPicZeroProper954SiteQ → PicZeroChar0.PicZeroAbVar0`, through kleiman-section2's
  `picZeroAbVar0_of_954`.

**Rating of `KleimanPicZeroProper954SiteQ`: printed form.** It is Kleiman 9.5.4 under its own hypotheses, with
Kleiman's `Pic_{(X/K)(fppf)}` exactly as Def. 9.2.2 defines it: the quotient functor, sheafified in the fppf topology
on the category of locally Noetherian `K`-schemes. `P` is quantified over representing objects; these are unique up
to unique isomorphism on that site, and Kleiman's `Pic_{X/K}` is one of them by 9.4.8. The leaf is stated over
genuine definitions: Mathlib's `fppfPrecoverage`, `IsLocallyNoetherian`, `ObjectProperty.FullSubcategory`,
`presheafToSheaf`, `IsClosedImmersion`, `ℙ(N; _)`, `GeometricallyIntegral`, and the tree's `picardPresheaf` and
`Scheme.Pic`. Its two extra hypotheses only weaken it: a `K`-point, and geometric normality after every field
extension (for the "proper" clause). Remaining reading risk: if 9.5.4's Picard scheme represents the étale sheaf,
the `K`-point and Kleiman 9.2.5 make the étale and fppf sheaves agree (kleiman-section2 §1). Locators
(9.2.2, 9.2.5, 9.4.8, 9.5.4; 5.4 / 4.1 in the reviewer's numbering) are UNVERIFIED on this host, which has no copy of
the text.

**Rating of `KleimanPicZeroProper954Site`: printed form**, by Kleiman's remark after Def. 9.2.2. It is equivalent to
the `Q` form by `kleimanIso` and `kleimanIsoQ`, both proved. The `Q` form is recommended because it needs no reading
of that remark.

## 4. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/KleimanPicZeroSite.lean`: no output, so no errors and no warnings
  (VERIFIED).
* `scratch/kleiman-site/Site.lean`: the first version, non-quotient only (VERIFIED compiled).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.KleimanPicZeroSite`:
  build completed successfully (16076 jobs, no errors) (VERIFIED).
* `#print axioms` (VERIFIED, in `discharges-output.txt`) of each of `kleimanPicZeroProper954_of_siteQ`,
  `kleimanPicZeroProper954_of_site`, `picZeroAbVar0_of_siteQ` and `sheafifyRestrictIso`:
  `[propext, Classical.choice, Quot.sound]`.
* Proposed `docs/research/locators.md` row (not edited here; a shared file): `KleimanSite.KleimanPicZeroProper954SiteQ` |
  Kleiman, *The Picard scheme* (FGA Explained Ch. 9, arXiv math/0504020), Thm 9.5.4 with Def. 9.2.2 | locator
  UNVERIFIED on host.

## 5. `#discharges` and the fold

`scratch/kleiman-site/Discharges.lean` (Main + Discharges + this file), output in
`scratch/kleiman-site/discharges-output.txt` (VERIFIED): 26 DISCHARGES lines, **none by `KleimanSite`**. This is
expected and matches kleiman-section2 §5. The frontier field is still
`OpenAddedLeaves25.kleimanPicZeroProper : PicFix.KleimanPicZeroProper`, which assumes only "proper" and is stronger
than 9.5.4. Neither `KleimanPicZeroProper954` nor the site leaf can prove it.

The single Kleiman line, `DISCHARGES [OpenAddedLeaves25.kleimanPicZeroProper] by
KleimanSection.kleimanPicZeroProper_of_Q`, still assuming `KleimanSection.KleimanPicZeroProperQ`, comes from the
newly imported `KleimanPicZeroProperQuot.lean`. That is kleiman-section's proper-reading leaf. It is not the
recommended route: kleiman-section2 rates it stronger than the print, because of "proper" instead of "projective"
and the étale/fppf question.

Autofold spec: `scratch/kleiman-site/autofold.json`. It discharges field `kleimanPicZeroProper954` (from
kleiman-section2's hand fold) by `KleimanSite.kleimanPicZeroProper954_of_siteQ {n}.kleimanPicZeroProper954SiteQ`. The
new leaf is `kleimanPicZeroProper954SiteQ : KleimanSite.KleimanPicZeroProper954SiteQ`, kind `published`, flag
`locator UNVERIFIED: printed form of Kleiman 9.5.4 over Kleiman's own site …`. It can run only after that hand fold
is integrated (§6).

## 6. What remains

* Locators: the numbers and hypotheses of Kleiman 9.2.2, 9.4.8 and 9.5.4 are unread on this host.
* Integration: the field `kleimanPicZeroProper954` does not exist in the tree yet. kleiman-section2's hand fold
  (TailZ56, written against the older top `sixContactMin_of_open45_pz`) must first be rebased onto the current top
  (TailZ67). Or that hand fold can use `kleimanPicZeroProper954SiteQ` directly, with
  `picZeroAbVar := KleimanSite.picZeroAbVar0_of_siteQ n.kleimanPicZeroProper954SiteQ`. The rebase is integrator work.
  The current chain threads `l : OpenAddedLeaves25` through the research-chain copies, so it needs the weaker-leaf
  bypass recipe, and it was not attempted here.

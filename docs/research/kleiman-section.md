# kleiman-section: Kleiman 9.5.4 over Kleiman's own Picard functor

## Verdict

**`kleimanPicZeroProper` is replaced by a LEAF stated over Kleiman's quotient functor, and the comparison with the
tree's `picardFunctor` is proved in Lean with no section hypothesis.** File:
`ZInQKernel/Contrib/OneProof/KleimanPicZeroProperQuot.lean` (namespace `KleimanSection`; builds; standard axioms
only; VERIFIED compiled).

* `KleimanSection.picardFunctorIsoKleiman (f : X ⟶ S) : picardFunctor f ≅ kleimanPicardSheaf f` for every morphism of
  schemes `f`, where `kleimanPicardSheaf f` is the fppf sheafification of Kleiman's `T ↦ Pic(X ×_S T) ⧸ Pic(T)`
  (`kleimanPicardPresheafGrp`). **No section is needed**: the quotient map is surjective, and locally injective
  because a class of `Pic(T)` is trivial on a Zariski cover of `T` (`Pic.exists_map_iota_eq_one`); a locally
  bijective map becomes an isomorphism after sheafification. The review's worry (the only comparison in the tree,
  `sheafifyPicardFunctorNormalizedIso`, needs a section) is therefore settled in general.
* `eta_repKleiman`, `identityComponent_repKleiman`: the group law of a scheme representing Kleiman's sheaf
  (`kleimanPicardGrpObj`, built from the quotient groups exactly as `picardFunctorCommGrpObj` is built from
  `Pic(X_T)`) has the same identity point, hence the same identity component, as the tree's group law transported
  along the comparison.
* Two forms of the leaf, both over Kleiman's functor:
  * `KleimanPicZeroProperQ`: the hypotheses of `PicFix.KleimanPicZeroProper` (proper, geometrically normal);
    `kleimanPicZeroProper_of_Q : KleimanPicZeroProperQ → PicFix.KleimanPicZeroProper` (**autofold**,
    `scratch/kleiman-section/autofold.json`).
  * `KleimanPicZeroProperPrinted` (weakest reading): additionally `X` geometrically integral, projective over `K`
    (proper with an immersion into `ℙ^N_K` over `K`) and with a `K`-point. It is a consequence of
    `KleimanPicZeroProperQ` (`kleimanPicZeroProperPrinted_of_Q`), and
    `picZeroAbVar0_of_printed : PicLocFinType → IdentityComponentLFT → KleimanPicZeroProperPrinted → PicZeroAbVar0`
    is the consumer (**hand fold**, `scratch/kleiman-section/TailZ56.lean`, compiled).

Recommendation: **the hand fold with `KleimanPicZeroProperPrinted`**; it is the printed theorem or a consequence of it
under every reading we could not exclude (proper vs projective, étale vs fppf), so it should be LEAF under the strictest
review. The autofold is the fallback if the integrator prefers a generated fold; its leaf carries the two reading risks
below. Counts: one field (rated GLUE by the latest review) out, one LEAF in: **−1 GLUE, no new GLUE** (strict and
strictest unchanged in kinds.tsv, where the old row was already LEAF/LEAF; the review's GLUE rating is what drops).

## 1. The statements

Old (unchanged, `ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean:25`): `PicFix.KleimanPicZeroProper`, over schemes
representing `picardFunctor X.hom` = fppf sheafification of `picardPresheaf X.hom : T ↦ Pic(X ×_K T)`
(`Picard/Presheaf.lean:68`, `Picard/Sheaf.lean:28`; VERIFIED read).

New definitions (VERIFIED compiled):

| Lean | meaning |
| --- | --- |
| `picBase f T` | the image of `Pic(T)` in `Pic(X ×_S T)` (range of pullback along the projection) |
| `kleimanPicardPresheafGrp f` | `T ↦ Pic(X ×_S T) ⧸ picBase f T`, a presheaf of groups on `Over S` (Kleiman Def 9.2.2, `Pic_{X/S}`; numbering UNVERIFIED) |
| `kleimanPicardSheaf f` | its fppf sheafification (Kleiman's `Pic_{(X/S)(fppf)}`) |
| `kleimanPicardGrpObj f rep` | the group law on a representing scheme (`GrpObj.ofRepresentableBySheafify`) |
| `quot f` | the quotient map `picardPresheaf f ⟶ kleimanPicardPresheaf f` |
| `repKleiman`, `repTree` | transport of representations along `picardFunctorIsoKleiman` |

`KleimanPicZeroProperPrinted` (the recommended leaf), in words: for every field `K` and `K`-scheme `X` that is
proper, geometrically integral, geometrically normal (`X_{K'}` normal for every field `K'/K`), admits an immersion
`i : X → ℙ^N_K` over `K` and has a `K`-point, every scheme `P` representing `kleimanPicardSheaf X.hom` and every open
`V ⊆ P` whose underlying set is the identity component (for `kleimanPicardGrpObj`), `V → Spec K` is proper.

## 2. The reading questions

**Quotient vs no quotient** (the review's main point). Settled by `picardFunctorIsoKleiman`, for every `f`, no
section (VERIFIED compiled). Both leaf forms are stated over the quotient functor, as Kleiman defines it.

**Section.** Not needed for the comparison. The rational point is nevertheless added to the weakest-reading form,
since it is what makes the étale and fppf readings agree (below). Its consumer (abelian varieties) supplies the
identity point `η[A.X].left` (`picZeroProperAt_of_printed`, VERIFIED compiled).

**Proper vs projective.** No copy of Kleiman was available on the host; whether 9.5.4 assumes `X` proper or
projective is UNVERIFIED. `KleimanPicZeroProperPrinted` assumes both proper and an immersion into `ℙ^N_K` over `K`
(which, with properness, is a closed immersion: `X` is projective in every sense), and concludes only "proper"
(weaker than "projective"). So it is a consequence of the print under either reading. Its consumer supplies
projectivity from `T09Pic.exists_isVeryAmple` (proved in the tree, TailZ24:83). `KleimanPicZeroProperQ` assumes only
proper, so it is stronger than the print if the print assumes projective (reading risk).

**Geometrically normal.** `geometrically IsNormalScheme X.hom` asks `X_{K'}` normal for every field `K'/K`, at least
as strong a hypothesis as normality of `X_{K̄}` (they are equivalent, EGA IV 6.7.7 / Stacks 038O; numbers UNVERIFIED),
so the leaf is not stronger than the print on this point.

**Étale vs fppf.** Kleiman's Picard scheme may be defined to represent `Pic_{(X/K)(ét)}` rather than
`Pic_{(X/K)(fppf)}` (UNVERIFIED which; this file proves no étale statement). For `X` with a section and with
`𝒪_K = f_*𝒪_X` universally, Kleiman Thm 9.2.5 (numbering UNVERIFIED; STANDARD content) says `T ↦ Pic(X_T)/Pic(T)` is
already an fppf sheaf, so it equals its étale and its fppf sheafifications, and a scheme represents one iff it
represents the other, with the same group law. `𝒪_K = f_*𝒪_X` universally holds for `X` proper and geometrically
integral over a field (geometrically reduced and connected; flat base change; STANDARD). `KleimanPicZeroProperPrinted`
assumes a `K`-point and geometric integrality, so under the étale reading it is a consequence of 9.5.4 together with
9.2.5, both printed. `KleimanPicZeroProperQ` has no section: under the étale reading it is a consequence of the print
only if every fppf representative also represents the étale sheaf (reading risk).

## 3. Leaf ratings

| leaf | printed form? | reason |
| --- | --- | --- |
| `KleimanSection.KleimanPicZeroProperPrinted` | **yes (consequence under every reading)** | Kleiman 9.5.4 over Kleiman's own functor `T ↦ Pic(X_T)/Pic(T)` (fppf sheafification, genuine definitions; group law induced as in the tree); extra hypotheses (geometrically integral, projective, `K`-point) only weaken it and make it a consequence of the print whether the print assumes proper or projective and whether it represents the étale or the fppf sheaf (the latter via 9.2.5). Existence statements of the print become quantifiers over representing objects (unique up to unique isomorphism). Locator UNVERIFIED. |
| `KleimanSection.KleimanPicZeroProperQ` | yes under the proper/fppf reading | Same functor; same hypotheses as the old leaf. Stronger than the print if 9.5.4 assumes projective, or if its `Pic_{X/K}` represents the étale sheaf and some fppf representative does not represent it. Locator UNVERIFIED. |

## 4. The folds

**Hand fold (recommended).** `scratch/kleiman-section/TailZ56.lean` is the module text for
`ZInQKernel/OneProof/H/TailZ56.lean` (compiled against TailZ55 in this worktree; standard axioms): `OpenAddedLeaves26`
= `{picRepresentableAbVar, kleimanPicZeroProperPrinted}`, `openAddedLeaves22PZ_of_OpenAddedLeaves26` (fills
`picZeroAbVar : PicZeroAbVar0` by `picZeroAbVar0_of_printed picLocFinType_proof identityComponentLFT_proof`), and
`sixContactMin_of_open49 r t (l : OpenAddedLeaves26) := sixContactMin_of_open45_pz r t (…)`. The integrator then
switches `Main.lean` to `sixContactMin_of_open49` with `l : HDec.HSyn.OpenAddedLeaves26`, removes the kinds.tsv row
`added kleimanPicZeroProper` and adds the row below. It is a hand fold because the new leaf is weaker than the field it
replaces (it cannot fill `PicFix.KleimanPicZeroProper`); the conversion goes to `OpenAddedLeaves22PZ`, below
TailZ53–55, which is legitimate since TailZ53–55 only pass the field down to `picZeroAbVar0_of_leaves`.

Proposed kinds.tsv row (tab-separated, same bundle/packet/label/tier as the old row):
`added  kleimanPicZeroProperPrinted  published  unread: Kleiman 9.5.4 over Kleiman's quotient functor, weakest reading (X also geometrically integral, projective, with a K-point); comparison with picardFunctor proved (no section); locator UNVERIFIED  LEAF  LEAF  Kleiman, The Picard scheme, 9.5.4  kleiman-section  R10  …  unread,unverified-locator  elliotglazer/diophantine-z-q#81`

**Autofold (fallback).** `scratch/kleiman-section/autofold.json`: field `kleimanPicZeroProper` filled by
`KleimanSection.kleimanPicZeroProper_of_Q {n}.kleimanPicZeroProperQ`, new leaf `kleimanPicZeroProperQ`.

## 5. Checks

See `scratch/kleiman-section/log.md` for compile outcomes and the `#discharges` output.

# kleiman-section2: `kleimanPicZeroProper` as Kleiman 9.5.4, printed form

## Result

**The added leaf `kleimanPicZeroProper` is replaced by `KleimanSection2.KleimanPicZeroProper954`, which states
Kleiman, *The Picard scheme* (arXiv math/0504020), Thm 9.5.4, under its own hypotheses. The abelian-variety consumer is
proved from it in Lean.** File: `ZInQKernel/Contrib/OneProof/KleimanPicZero954.lean` (namespace `KleimanSection2`).
It builds, has no sorry and uses only the standard axioms (VERIFIED compiled).

Counts: one field out (rated GLUE by the latest review, because the old leaf assumes only "proper", which is
stronger than 9.5.4) and one LEAF in. So **−1 GLUE and no new GLUE**. The other new declarations are proved glue.
The fold is a hand fold, because the new leaf is weaker than the field it replaces:
`scratch/kleiman-section2/TailZ56.lean`, checked by `scratch/kleiman-section2/FoldCheck.lean` (§4).

This supersedes the previous task's recommended leaf `KleimanSection.KleimanPicZeroProperPrinted`, for three reasons:
* The new leaf is stated over the tree's `picardFunctor`. Kleiman says, right after Def. 9.2.2, that the fppf sheaf
  associated with `T ↦ Pic(X_T)` is `Pic_{(X/S)(fppf)}`, and BLR §8.1 p. 199 agrees. So no quotient by `Pic(T)` is
  needed, and the file does not import `KleimanPicZeroProperQuot.lean`.
* It assumes "projective" in Kleiman's form, as a closed immersion into `ℙ^N_K`.
* It handles Kleiman's locally Noetherian test category, step (a) below.

## 1. The leaf

`KleimanPicZeroProper954` (VERIFIED compiled) has these hypotheses, for every field `K : Type` and `X : Over (Spec K)`:

| hypothesis in Lean | Kleiman 9.5.4 | direction |
| --- | --- | --- |
| `∃ N (finite) (i : X → ℙ(N; Spec K)), IsClosedImmersion i ∧ i ≫ proj = X.hom` | `X/k` projective | over a field, every sense of "projective" is a closed subscheme of some `ℙ^n_k` (STANDARD) |
| `GeometricallyIntegral X.hom` (Mathlib: integral after every field extension) | geometrically integral | at least as strong as integrality of `X_{k̄}` |
| `geometrically IsNormalScheme X.hom` (normal after every field extension) | geometrically normal (needed only for "`Pic⁰` projective") | at least as strong; an extra hypothesis for the "proper" clause |
| `∃ σ : Spec K → X` a section | — | extra hypothesis; see étale vs fppf below |
| `P` with `LocallyOfFiniteType P.hom` and `rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, _⟩` | `Pic_{X/k}`, which exists, is locally of finite type and represents `Pic_{(X/k)(fppf)}` on locally Noetherian `k`-schemes (9.4.8) | quantifier over representatives (see below) |
| `V : P.left.Opens`, `V = identityComponentLN rep` (connected component of the point classifying `[𝒪_X]`) | `Pic⁰_{X/k}` (9.5.1) | open subscheme on the identity component |

Conclusion: `IsProper (V.ι ≫ P.hom)`. Kleiman 9.5.4 concludes "proper", or "projective" when `X` is geometrically
normal, and projective implies proper.

Supporting definitions: `LocNoeth S` (an `S`-scheme whose source is locally Noetherian, a Mathlib notion);
`picardFunctorLN f := (LocNoeth S).ι.op ⋙ (picardFunctor f).obj`; `unitPt rep`, the `K`-point classifying
`1 ∈ Pic(X ×_K K)` through `toSheafify`; `identityComponentLN rep`.

**Why it is a consequence of 9.5.4 (printed form).** Let `P` and `rep` be as in the leaf. By 9.4.8, Kleiman's
`Pic_{X/k}` is locally of finite type, hence locally Noetherian, and it represents `Pic_{(X/k)(fppf)}` on locally
Noetherian `k`-schemes. Both `P` and `Pic_{X/k}` are objects of that category, so Yoneda gives an isomorphism
`P ≅ Pic_{X/k}` over `k`. This isomorphism matches the points classifying `[𝒪_X]`, so it maps the connected component
of one identity point onto the other. It therefore identifies `V` with `Pic⁰_{X/k}` as open subschemes, and properness
transfers. Two identifications are used:

* **Restriction of the sheafification.** The tree's `picardFunctor` is sheafified over all `K`-schemes and then
  restricted. Kleiman's sheaf is sheafified on the category itself. The two agree on locally Noetherian `T`. An fppf
  cover of a locally Noetherian `T` consists of flat morphisms locally of finite presentation, so its members and
  their fibre products over `T` are again locally Noetherian, and the plus construction only uses such data
  (STANDARD). Independently, the `K`-point gives the same conclusion: by 9.2.5 (UNVERIFIED numbering), with a
  section and `𝒪_k = f_*𝒪_X` universally (which holds for `X` proper and geometrically integral), `T ↦ Pic(X_T)/Pic(T)`
  is already an fppf sheaf. `KleimanSection.picardFunctorIsoKleiman` (kleiman-section, proved) identifies the tree's
  sheaf with the sheafification of that quotient.
* **Étale vs fppf.** If the Picard scheme in 9.5.4 is taken to represent `Pic_{(X/k)(ét)}`, then the section and 9.2.5
  make the étale and fppf sheaves equal.

Rating: **printed form.** It is Kleiman 9.5.4 under its own hypotheses, plus two extra hypotheses that only weaken
it: the `K`-point and geometric normality for the "proper" clause. It is stated over genuine Mathlib and tree
definitions: `picardFunctor`, `IsClosedImmersion`, `ℙ(N; _)`, `GeometricallyIntegral`, `IsLocallyNoetherian`,
`connectedComponent`. The print's existence statements become quantifiers over representing objects, which are unique
up to unique isomorphism. Locator status: the theorem number and its hypotheses (projective, geometrically integral;
geometrically normal for the projectivity clause; the proper case only in Remark 9.5.6) are as reported from a
reading of the arXiv text. There is no copy on this host, so they are UNVERIFIED here.

## 2. Step (a): all test schemes versus locally Noetherian ones

Kleiman's representability statements are over locally Noetherian test schemes, while the tree's `RepresentableBy`
quantifies over all `K`-schemes. The leaf is stated over locally Noetherian test schemes. The direction the consumer
needs is proved:

* `repLN rep hP : (picardFunctorLN f).RepresentableBy ⟨P, hP⟩`. Any representation over all `S`-schemes restricts,
  provided `P` is locally Noetherian. Here `P` is locally of finite type over `K`, by `PicLFT.picLocFinType_proof`
  (proved in the tree) and `LocallyOfFiniteType.isLocallyNoetherian` (Mathlib).
* `identityComponentLN_repLN`: the identity component of the restricted representation is, by definition (`rfl`),
  the tree's `identityComponent P` for the group law `picardFunctorCommGrpObj`.

The converse, extending a representation from locally Noetherian test schemes to all schemes, is not needed and not
proved. It would use that `Pic` is locally of finite presentation (a limit argument, EGA IV §8).

Remark for the integrator (SPECULATIVE; outside this task): the sibling field `picRepresentableAbVar` asserts
representability over all `K`-schemes. If its cited sources (Kleiman 9.4.8, FGA 232) are read as statements over
locally Noetherian test schemes only, the same question arises for it, in the converse direction.

## 3. Step (b): EGA IV_2 6.7.7 is not needed

The leaf assumes `geometrically IsNormalScheme X.hom`: normal after every field extension. That is at least as strong
as Kleiman's "geometrically normal" (normal after `k̄`), so the leaf does not need EGA IV 6.7.7. The consumer proves
the strong form directly: `PicFix.geometricallyNormal_of_smooth` (smooth ⇒ normal after any base change, already in
the tree).

## 4. The consumer and the fold

* `isClosedImmersion_of_proper`: an immersion `i : X → ℙ^N_K` over `K` with `X` proper is a closed immersion. The
  proof: `ℙ^N_K` is separated over `K`, so `i` is proper (`IsProper.of_comp`), so its range is closed
  (`IsClosedImmersion.of_isPreimmersion`).
* `picZeroProperAt_of_954 : KleimanPicZeroProper954 → PicZeroChar0.PicZeroProperAt K`. The inputs are projectivity
  (vendored `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`, then the lemma above),
  `GeometricallyIntegral` (an instance from the `AbVar` structure), normality (`geometricallyNormal_of_smooth`), the
  identity point `η[A.X].left`, local finite type of `P` (`picLocFinType_proof`), then `repLN` and
  `identityComponentLN_repLN`.
* `picZeroAbVar0_of_954 : KleimanPicZeroProper954 → PicZeroChar0.PicZeroAbVar0`, the argument of
  `picZeroAbVar0_of_leaves` with `picLocFinType_proof`, `identityComponentLFT_proof` and `cartierSmooth_proof`.

**Hand fold** (an autofold is impossible: the new leaf is weaker than the field `PicFix.KleimanPicZeroProper`, so no
term of the field's type can be built from it). `scratch/kleiman-section2/TailZ56.lean` is the module text for
`ZInQKernel/OneProof/H/TailZ56.lean`. It supersedes kleiman-section's draft with the same names. It defines:
* `OpenAddedLeaves26 = {picRepresentableAbVar, kleimanPicZeroProper954}`;
* `openAddedLeaves22PZ_of_OpenAddedLeaves26`, which fills `picZeroAbVar` by `KleimanSection2.picZeroAbVar0_of_954`;
* `sixContactMin_of_open49 r t l := sixContactMin_of_open45_pz r t (…)`.

The conversion skips TailZ53–55, which is legitimate because they only pass the field down to
`picZeroAbVar0_of_leaves`. The integrator then:
* switches `Main.lean` to `sixContactMin_of_open49` with `l : HDec.HSyn.OpenAddedLeaves26`;
* removes the kinds.tsv row `added kleimanPicZeroProper`;
* adds this row (tab-separated, same bundle/packet/label/tier columns as the old row):

`added  kleimanPicZeroProper954  published  printed form: Kleiman 9.5.4 (X projective, geometrically integral, geometrically normal; plus a K-point); representability over locally Noetherian test schemes; restriction from all schemes proved (repLN); locator UNVERIFIED on host  LEAF  LEAF  Kleiman, The Picard scheme, 9.5.4  kleiman-section2  R10  …  unverified-locator`

`scratch/kleiman-section2/autofold.json` records the same discharge as a spec, for the integrator's tooling. Its
`proof` targets the `OpenAddedLeaves22PZ.picZeroAbVar` route. `autofold.py` itself cannot apply it to the frontier
field `kleimanPicZeroProper`, so it is documentation, not a runnable autofold.

## 5. Checks (VERIFIED)

* `lake build ZInQKernel.Contrib.OneProof.KleimanPicZero954`: build completed, with linter warnings only.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.KleimanPicZero954`:
  build completed (14228 jobs).
* `scratch/kleiman-section2/FoldCheck.lean` compiles. It contains the hand fold module text plus `frozenTarget`'s body
  verbatim, with `l : OpenAddedLeaves26` and `sixContactMin_of_open49`. Both `frozenTarget_kleimanSection2` and
  `sixContactMin_of_open49` use only `[propext, Classical.choice, Quot.sound]`.
* `scratch/kleiman-section2/K954.lean`: `picZeroAbVar0_of_954` uses only the standard axioms.
* `#discharges` (`scratch/kleiman-section2/Discharges.lean`, output in `discharges-output.txt`) prints 33 DISCHARGES
  lines, **none from `KleimanSection2`**. This is expected. The new leaf is weaker than the frontier field
  `PicFix.KleimanPicZeroProper`. The conclusion of `picZeroAbVar0_of_954`, `PicZeroChar0.PicZeroAbVar0`, is a field
  only of the older generation `OpenAddedLeaves22PZ`, not an open hypothesis of `frozenTarget`. This is why the fold
  is a hand fold.

## 6. What remains

* The theorem numbers (9.2.2, 9.2.5, 9.4.8, 9.5.1, 9.5.4, 9.5.6) and the exact hypotheses of 9.5.4 are as reported
  from the arXiv text; there is no copy on this host (UNVERIFIED here). A `docs/research/locators.md` row is needed.
* The comparison "restriction of the fppf sheafification = sheafification on locally Noetherian schemes" is argued
  (STANDARD), not formalized. It is only needed to read the leaf as Kleiman's sheaf, and the section with 9.2.5 gives
  a second argument.

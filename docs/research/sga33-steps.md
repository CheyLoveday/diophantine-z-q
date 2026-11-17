# sga33-steps: the field `sga7_IX_3_3_SHpre` proved from SGA 7 IX Cor. 3.3 as printed

Task sga33-steps, 2026-11-17. Base `wip/sga33-steps` = 222c98bf (origin/main) with origin/wip/leaf-fold33b
(db99b5b4) merged. Model work, no human review. Marks: **VERIFIED** = compiled, or read in a file; **STANDARD** =
published, with an exact reference; **SPECULATIVE** = a judgement; **UNVERIFIED** = a locator recalled or reported
without a source read on this host (no network).

## 1. Result

**The field `HDec.HSyn.OpenResearchLeaves38.sga7_IX_3_3_SHpre` (`DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`) is proved,
with its exact type and no other hypothesis, from one new leaf `SGA33Steps.SGA7_IX_Cor3_3`, SGA 7 I Exp. IX Cor. 3.3
in its printed form specialized to traits** (`ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean`,
`SGA33Steps.shpre_of_cor33`). VERIFIED: compiled, standard axioms only, `#discharges` matches the field (§5).

The three steps the reading named are each a Lean theorem:

| step | content | Lean |
| --- | --- | --- |
| (1) base | Cor. 3.3 over any extension of DVRs `O ⊆ O'` (no henselian, no finiteness) specializes to the field's strictly henselian, finite base | `cor33SH_of_cor33` |
| (2) dictionary | `N⁰` = `idCompSet` (open over a DVR, `SGA3Nbhd.isOpen_idCompSet_groupModelO`); "isomorphism `N⁰ ×_S S' ≅ N'⁰`" ⇔ "open immersion with image `N'⁰`" (`openImm_range_iff_iso`); "semistable reduction" of `A` (some Néron model) gives the given Néron model semistable by uniqueness of Néron models (`ReductGlue.semistableNeronModels_of_has`, from `ReductGlue.neronO_unique`) | `openImm_range_iff_iso`, inside `shpre_of_cor33SH` |
| (3) comparison map | the canonical `u` (Néron mapping property of `N'` applied to `bcDVR`'s generic identification; a homomorphism by `ReductGlue.isMonHom_of_ext`); any `c` with generic fibre an isomorphism is `u ≫ α`, `α` an automorphism of `N'` (`exists_aut_factor`); `α` fixes the unit section because `c` and `u` are homomorphisms, so it maps `N'⁰` onto itself (`image_idCompSet_eq`) | `exists_aut_factor`, `image_idCompSet_subset`, `image_idCompSet_eq` |

Effect on the counts (with the autofold spec `scratch/sga33-steps/autofold.json`): the GLUE row `sga7_IX_3_3_SHpre`
(published, GLUE/GLUE, flag "pending reading") is replaced by the LEAF row `sga7_IX_Cor3_3` (published, flag
"unread"): strict GLUE −1, strictest GLUE −1, total unchanged. Unlike sga33-shpre's restricted leaf (which was
weaker than the field and needed a bypass fold), this leaf proves the field, so `autofold.py` writes the fold.

## 2. Statement and consumers (VERIFIED, read in files)

The field (verbatim copy with an `rfl` check: `scratch/sga33-steps/Statement.lean`): for strictly henselian DVRs
`O ⊆ K`, `O' ⊆ K'`, `K'/K` finite, `O' ∩ K = O`, `A` with `HasSemistableReduction A O`, Néron models `𝒩`, `𝒩'`, any
homomorphism `c : 𝒩 ×_O O' → 𝒩'` whose generic fibre is an isomorphism, and the open `U = pullback.fst ⁻¹' 𝒩⁰`:
`U → 𝒩'` is an open immersion with image `𝒩'⁰`.

Consumers: the field is read only by `SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'` (TailZ45 and the copies in
`NoSGA3Copy.lean`, `GoodModelIsoCopy.lean`), giving `SGA7PersistsNF.SGA7_IX_3_3_SH`, which is read by
`SGA3Nbhd.NF.sga7_IX_3_3_of_SH'` and `SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH'`. The first passes a comparison
map `c₁` built from an arbitrary upstream `c` (base change of `c` to the strict henselizations), so the consumers
use the arbitrary-`c` form: step (3) is needed and was proved rather than restricted away.

## 3. The new leaf and its rating

```lean
def SGA33Steps.SGA7_IX_Cor3_3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → 𝒩.IsSemistable →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ u : bcO hO 𝒩.G ⟶ 𝒩'.G,
      (Over.pullback (jO O')).map u ≫ 𝒩'.gen.hom = (ReductGlue.bcDVR hO 𝒩).gen.hom →
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
    ∀ W : 𝒩'.G.left.Opens, (W : Set 𝒩'.G.left) = idCompSet 𝒩'.G →
      ∃ e : (U : Scheme) ≅ (W : Scheme), e.hom ≫ W.ι = U.ι ≫ u.left
```

**Rating: printed form (specialized to traits); LEAF, flag "unread".** Reasons:

* Locator: SGA 7 I, Exp. IX, Cor. 3.3, p. 348; semistable reduction Déf. 3.4, p. 349 — as reported by the reading in
  this task's brief. Not re-read on this host (no network) and not recorded in `reviews.tsv`: UNVERIFIED here.
* Base: per that reading the print needs only `S' → S` dominant with `S` (and `S'`) regular of dimension one. The
  leaf takes `S = Spec O`, `S' = Spec O'` with `O ⊆ O'` DVRs and `O' ∩ K = O` (so `Spec O' → Spec O` is dominant and
  local): a specialization. No henselian or finiteness hypothesis is assumed, as in the print (per the reading).
  Should a reading find a henselian or finiteness hypothesis after all, `SGA7_IX_Cor3_3_SH` (the leaf over the
  field's base) is the drop-in replacement: `shpre_of_cor33SH` proves the field from it.
* Every object is a genuine definition: the kernel's `GroupModelO`, `IsNeronModel` (BLR 1.2 Def. 1),
  `IsSemistable` (geometric special fibre), `idCompSet` (union of identity components of fibres), `bcDVR` (base
  change with its generic identification), Mathlib's open subschemes and scheme isomorphisms.
* The conclusion is the print's "induces an isomorphism `N⁰ ×_S S' ≅ N'⁰`" literally: a scheme isomorphism between
  the open subschemes `U = N⁰ ×_S S'` and `W = N'⁰` compatible with `u`.
* `u` is the print's canonical morphism: the unique morphism (Néron mapping property of `𝒩'`) whose generic fibre is
  the identification `(N ×_O O')_{K'} ≅ A_{K'} ≅ N'_{K'}`.
* Reading risk carried over from the field (not introduced here): "semistable" is read on the geometric special fibre
  (`GroupModelO.IsSemistable`); if Déf. 3.4 reads it over `k(s)`, the two agree by the descent of semi-abelian
  varieties (the `SemiAbelianDescendsSepClosed` axis, proved in Lean only for perfect `k`). The reading in the brief
  rated the Lean statement a consequence of the print with this definition; SPECULATIVE that no further restriction
  is needed.

## 4. Lean

`ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean` (imports `ZInQKernel.Contrib.OneProof.SGA3NbhdDVR`, which imports
the defining module `SGA7IX33SHPre`):

* `SGA7_IX_Cor3_3 : Prop` (LEAF), `SGA7_IX_Cor3_3_SH : Prop` (its specialization, proved);
* `cor33SH_of_cor33 : SGA7_IX_Cor3_3 → SGA7_IX_Cor3_3_SH` (step 1);
* `openImm_range_iff_iso` (step 2, dictionary of the conclusion);
* `image_idCompSet_subset`, `image_idCompSet_eq` (a unit-preserving homomorphism, resp. isomorphism, of group
  schemes maps `G⁰` into, resp. onto, `H⁰`);
* `exists_aut_factor` (step 3: `c = u ≫ α` by the Néron mapping property);
* `shpre_of_cor33SH : SGA7_IX_Cor3_3_SH → DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`;
* `shpre_of_cor33 : SGA7_IX_Cor3_3 → DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` (the discharge).

## 5. Checks (all VERIFIED)

* `lake env lean ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean`: no errors, no warnings.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.SGA7IX33Cor`:
  Build completed successfully (14274 jobs, 15 min 25 s; `scratch/sga33-steps/build2-summary.txt`).
* `scratch/sga33-steps/Statement.lean`: the verbatim copy of the field's statement is `rfl`-equal to
  `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`.
* `#discharges` (`scratch/sga33-steps/Discharges.lean`, output `discharges.txt`):

  ```
  DISCHARGES [OpenResearchLeaves38.sga7_IX_3_3_SHpre] by SGA33Steps.shpre_of_cor33
    still assumes: [SGA33Steps.SGA7_IX_Cor3_3]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves38.sga7_IX_3_3_SHpre] by SGA33Steps.shpre_of_cor33SH
    still assumes: [SGA33Steps.SGA7_IX_Cor3_3_SH]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 39 open hypotheses, 11122 theorems checked, 51 discharge one
  ```
* Autofold spec `scratch/sga33-steps/autofold.json` (field `sga7_IX_3_3_SHpre`, proof
  `_root_.SGA33Steps.shpre_of_cor33 {n}.sga7_IX_Cor3_3`, leaf `sga7_IX_Cor3_3`, kind published, flag "unread: ...").
  `autofold.py --dry-run`: "strict count: 16/18 on 34 -> 17/17 on 34; strictest 16/18 -> 17/17". Its output (minus
  the count line) is `scratch/sga33-steps/FoldCheck.lean` (`OpenResearchLeaves39`, `sixContactMin_of_open56` on top of
  TailZ62); it compiles, and `HDec.HSyn.sixContactMin_of_open56` depends on `[propext, Classical.choice, Quot.sound]`.
  The fold itself (writing TailZ63, Main, kinds.tsv) is left to the integrator.

## 6. What remains

* A human reading of SGA 7 I Exp. IX Cor. 3.3 (p. 348) and Déf. 3.4 (p. 349) to confirm the locator and the base
  hypotheses (the leaf enters flagged "unread"). If the print turns out to assume a henselian base, a finite
  extension or an algebraically closed residue field, the fallback is in place for the first two
  (`SGA7_IX_Cor3_3_SH`, `shpre_of_cor33SH`); for the third, sga33-shpre's AC-restricted route
  (origin/wip/sga33-shpre) applies.
* The k(s)-versus-κ̄ reading of "semistable" (carried over from the field; §3, last item).
* Ledger rows (kinds.tsv through autofold; locators.md row proposed in `scratch/sga33-steps/rows-proposed.md`).

# gt-ega: EGA IV 8.10.5 (open immersions) proved

**Result (VERIFIED, compiled).** The open hypothesis `egaIV_8_10_5_openImm` of the single proof
(`CToPrinted.EGAIV_8_10_5_openImm`, `ZInQKernel/OneProof/H/TailZ19.lean` L281; LEAF field of
`HDec.HSyn.OpenResearchLeaves14`) is a theorem:

```lean
theorem ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof : CToPrinted.EGAIV_8_10_5_openImm
```

in `ZInQKernel/Contrib/OneProof/EGAOpenImm.lean`, with no hypotheses and only the axioms `propext`,
`Classical.choice`, `Quot.sound`. It uses Mathlib v4.35.0 and the vendored Stacks library
`ZInQKernel/Contrib/CloudW01Spread/` (already in the build), and nothing from the bundles. The statement was
not changed; it is neither false nor vacuous (it is EGA IV₃ 8.10.5 for open immersions, specialized to
`Type`-indexed directed systems in `Scheme.{0}`; the hypotheses on `X_i`, `Y_i` are those of the print, and
`QuasiCompact Yi.hom`, `QuasiSeparated Yi.hom`, `QuasiCompact Xi.hom`, `QuasiSeparated Xi.hom` and
`LocallyOfFinitePresentation Xi.hom`, `Yi.hom` are all used).

FOLD: see section 4 (status of the autofold and the checks).

## 1. Statement (verbatim, TailZ19 L281)

```lean
def EGAIV_8_10_5_openImm : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi Yi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → LocallyOfFinitePresentation Yi.hom → QuasiCompact Yi.hom →
      QuasiSeparated Yi.hom → ∀ fi : Xi ⟶ Yi,
      IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left
```

## 2. Proof

The file proves a general form first, `ZInQ.Contrib.EGAOpenImm.exists_isOpenImmersion_baseChange`: for any small
cofiltered category `I`, `D : I ⥤ Scheme.{u}` with affine transition maps, a limit cone `c`, `Xi`, `Yi` over
`D.obj i` with quasi-compact quasi-separated total spaces and `fi.left` locally of finite presentation, if the
base change of `fi` to `c.pt` is an open immersion then so is its base change to some stage. The target follows
(`D_i` qcqs and `Xi.hom`, `Yi.hom` qcqs give `Xi.left`, `Yi.left` qcqs; `fi.left` is locally of finite
presentation by Stacks 02FV(1), CloudW01's `locallyOfFinitePresentation_of_comp`, since `Yi.hom` is locally of
finite type).

Notation: `X_a = D_a ×_{D_i} X_i` etc. for `a : Over i` (CloudW01's `baseChangeDiagram`, limit `X_∞` by
`baseChangeConeIsLimit`), `f_a = baseChangeMap (D.map a.hom) Xi Yi fi`, `f_∞` likewise; the squares
`X_∞ → X_a`, `f_∞`, `f_a`, `Y_∞ → Y_a` and the transition squares are cartesian (`baseChangeCone_π_isPullback`,
`baseChangeDiagramMap_isPullback`); `baseChangeMap_prop_iff` converts between `baseChangeMap` and
`(Over.pullback _).map _`.

1. `X_∞` is quasi-compact (`Scheme.compactSpace_of_isLimit`), so `U = f_∞(X_∞)` is a quasi-compact open of
   `Y_∞`. Stacks 01Z4(1) (Mathlib `exists_preimage_eq`) gives a stage `a` and a quasi-compact open `V ⊆ Y_a`
   with `U = (Y_∞ → Y_a)⁻¹ V`.
2. `(X_∞ → X_a)⁻¹(f_a⁻¹ V) = f_∞⁻¹ U = X_∞`; Mathlib's `exists_map_preimage_le_map_preimage` (the step
   behind 01Z4(2)) gives `b → a` with `(X_b → X_a)⁻¹(f_a⁻¹ V) = X_b`. With `V_b = (Y_b → Y_a)⁻¹ V`
   (quasi-compact, the transition map being affine): `f_b⁻¹ V_b = X_b` and `(Y_∞ → Y_b)⁻¹ V_b = U`.
3. `f_b = g ≫ ι` with `ι : V_b → Y_b` the open immersion (`IsOpenImmersion.lift`). Base change along
   `ℓ : Y_∞ → Y_b`: `pullback.snd ι ℓ` is an open immersion with range `ℓ⁻¹ V_b = U`
   (`IsOpenImmersion.range_pullbackSnd`), and `pullback.snd f_b ℓ ≅ f_∞` (cartesian square) has range `U`;
   so the base change of `g` is `isoPullback.inv ≫ isoOfRangeEq …`, an isomorphism.
4. Stacks 081E (CloudW01's `exists_isIso_baseChange_of_isIso_limitBaseChange`), applied to the diagram `Y_•`
   over `Over i` (cofiltered, essentially small, affine transitions, qcqs stages), `X₀ = (X_b, f_b)`,
   `Y₀ = (V_b, ι)`, `f₀ = g` (locally of finite presentation by 02FV(1); `X_b`, `V_b` qcqs), gives `d → b`
   with the base change of `g` along `Y_d → Y_b` an isomorphism. Then `pullback.snd f_b (Y_d → Y_b)` is that
   isomorphism followed by the base change of `ι`, an open immersion; and `f_d` is isomorphic to it over
   `Y_d` (transition square). Conversion back gives `IsOpenImmersion ((Over.pullback (D.map d.hom)).map fi).left`.

The gap-triage plan (A4) is followed; its two risks resolved as follows: the image is quasi-compact as the
continuous image of the quasi-compact `X_∞`; 081E's side conditions hold because 081E is applied to the
diagram `Y_•` (whose stages are qcqs) and to the factor `g`, not to `fi`, so the finite-presentation condition
is on `g` and follows from 02FV(1). One extra step not in the plan: `f_b` must land in `V_b` before 081E
applies, which needs the second descent (step 2).

## 3. Files

- `ZInQKernel/Contrib/OneProof/EGAOpenImm.lean`: the contribution (imports `ZInQKernel.OneProof.Main` and two
  CloudW01Spread modules).
- `scratch/gt-ega/Scratch.lean`: the same proof against a verbatim copy of the statement, minimal imports.
- `scratch/gt-ega/Discharges.lean`: the `#discharges` check.
- `scratch/gt-ega/autofold.json`: the fold spec.
- `scratch/gt-ega/log.md`: results log.

## 4. Checks and fold

(filled in below as each check ran)

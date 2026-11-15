# c-to-printed: four "consequence of one theorem" fields from printed-form leaves

Task c-to-printed, 2026-11-14. Base e38375b3 (wip/w62). Lean: `scratch/c-to-printed/CToPrinted.lean` (imports
`ZInQKernel.OneProof.H.TailZ14`; parts N, S, F) and `scratch/c-to-printed/Shimura.lean` (imports
`ZInQKernel.OneProof.H.TailU`; part H). Neither file has a `sorry` or an `axiom`. Every theorem below depends only
on `[propext, Classical.choice, Quot.sound]`, checked by `#print axioms` at the end of each file (VERIFIED). Results
log: `scratch/c-to-printed/log.md`. Nothing under `ZInQKernel/` or `blueprint/` was edited. This is model work with
no human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or wording recalled without a source. There is no network on this host,
so BLR, SGA 3, SGA 7, EGA IV, Faltings 1983, Raynaud (Astérisque 127) and Shimura 1967 could not be consulted.
Every locator and every "printed" wording below is UNVERIFIED.

Each field is proved from the exact kernel constant, so the statement is unchanged. Each file also carries a
verbatim copy of the field with an `example : copy = kernel constant := rfl` check.

## 1. Main result

| field (kernel constant) | Lean theorem (compiled) | published-form leaves | glue left |
|---|---|---|---|
| `neronLocalizesDVR` (`ReductGlue.NeronLocalizesDVR`) | `CToPrinted.neronLocalizesDVR_of_printed` | `BLR_1_2_4`: BLR 1.2 Prop. 4, the full "iff", over every Dedekind domain and every smooth separated `R`-scheme of finite type | **none** (all glue proved) |
| `faltingsLemma5BC` (`ZInQ.HeightSplit.FaltingsLemma5BC`) | `CToPrinted.faltingsLemma5BC_of_printed` | `FaltingsLemma5Printed`: Faltings 1983 Lemma 5, the identity with the correction term `[K:ℚ]⁻¹ log #s*Ω¹_{G/S}`; `RaynaudKernelBound`: Raynaud, Ast. 127 VII 2.1.3 | **none** (all glue proved) |
| `semistableNeronBaseChange` (`ZInQ.HeightSplit.SemistableNeronBaseChange`) | `CToPrinted.semistableNeronBaseChange_of_printed_final'` | `BLR_1_2_4`, `SGA3_VIB_3_10`, `SGA7_IX_3_3`, `EGAIV_8_10_5_openImm` | 4 small glue Props on the topology of the identity component (`IdCompSubgroup`, `IdCompGeomFibres`, `OpenSubgroupIsIdComp`, `IdCompBaseChangeDVR`). Proved: reduct-glue's leaf `OpenImmersionOfLocal` from EGA IV 8.10.5; the group-model construction on `𝒢⁰`; the step from SGA 7 IX 3.3 to reduct-split's form; `IdCompGenericFibre` |
| `shimuraFamily` (`HDec.QMSplit.Moduli.ShimuraFamily`) | `CToPrinted.Shimura.shimuraFamily_of_mainThmI` | `ShimuraMainThmIY3`: Shimura 1967 Main Thm I with the moduli interpretation, **without the reciprocity law** | none, but the leaf is a consequence of the print rather than the print (§5): the reciprocity law needs global class field theory, which Mathlib lacks |

Also compiled: `semistableNeronBaseChange_of_printedBLR`. It derives SS2 from reduct-glue's three other leaves
(`IdentityComponentBaseChangeDVR`, `IdentityComponentOL`, `OpenImmersionOfLocal`), with `NeronLocalizesDVR` replaced
by the printed BLR 1.2/4.

**Net effect on the strict count** (SPECULATIVE until the integrator rules):
- `neronLocalizesDVR` and `faltingsLemma5BC` become theorems from published-form leaves, with no glue. That is
  1 GLUE (c) → 1 LEAF, and 1 GLUE (c) → 2 LEAVES.
- `semistableNeronBaseChange` becomes four printed-form leaves plus four small glue Props about the topology of the
  identity component. One of the four leaves, BLR 1.2/4, is shared with `neronLocalizesDVR`. Of reduct-glue's
  four leaves:
  - two are now Lean theorems from printed leaves (`NeronLocalizesDVR` from BLR 1.2/4, `OpenImmersionOfLocal`
    from EGA IV 8.10.5);
  - the other two are reduced to the printed SGA 3 VI_B 3.10 and SGA 7 IX 3.3 plus that glue.
- `shimuraFamily` stays a consequence of one theorem. Its leaf is now as close to the print as Mathlib 4.35
  allows, and §5 lists what is missing.

No statement was found false or vacuous.

## 2. `neronLocalizesDVR` (part N)

**Definition** `IsNeronModelOver R K X` (BLR §1.2 Def. 1), for `R` a ring, `K` an `R`-algebra and
`X : Over (Spec R)`, requires:
- `X` is smooth, separated, locally of finite type and quasi-compact;
- for every smooth `R`-scheme `Y`, the map `Hom_R(Y, X) → Hom_K(Y_K, X_K)`, `f ↦ f_K`, is bijective.

The definition uses only Mathlib objects (`Over.pullback`, `Spec.map`). "X is a Néron model of X_K" for an
`R`-model `X` is this predicate, because composing with an identification `X ×_R K ≅ X_K` does not change
bijectivity.

**Leaf** `BLR_1_2_4` (BLR, *Néron models*, §1.2 Prop. 4; UNVERIFIED). The setting: `R` a Dedekind domain with
fraction field `K`, and `X` smooth, separated and quasi-compact over `R`. Then

`IsNeronModelOver R K X ↔ ∀ maximal 𝔭, ∀ R𝔭 with IsLocalization.AtPrime R𝔭 𝔭 and R → R𝔭 → K, IsNeronModelOver R𝔭 K (X ×_R R𝔭)`.

`IsLocalization.AtPrime` is Mathlib's characteristic predicate for `𝒪_{S,s}`. Every such ring is uniquely
isomorphic to `Localization.AtPrime 𝔭`, so quantifying over all of them says no more than the print.

**Glue, all proved:**
- `isLocalization_center`: a DVR `O` of a number field `L` is `IsLocalization.AtPrime O (center O)` along
  `toOL`. This uses reduct-glue's `mem_iff_exists`.
- `isNeronModelOver_of`: the kernel's `GroupModel.IsNeronModel` gives `IsNeronModelOver (𝓞 L) L 𝒩.G`.
- In `neronLocalizesDVR_of_printed`, the kernel's `toO 𝒩 O` is `𝒩.G ×_{𝓞_L} O` with the generic identification
  composed with an isomorphism.

**Reading risk** (flagged by reduct-glue §5): BLR may state 1.2/4 with strict henselizations `𝒪^{sh}_{S,s}`
instead of local rings, or with both. The localization form would then follow from the print through BLR 1.2/2
(Néron models and étale base change) with descent. That derivation is not in Lean.

## 3. `faltingsLemma5BC` (part F)

reduct-split had already reduced the field, with no glue, to the base-field form `HeightSplit.FaltingsLemma5`
(`ReductSplit.faltingsLemma5BC_final`). `FaltingsLemma5` is `|h(A) − h(B)| ≤ ½ log deg φ` for semistable Néron
models over `𝓞_K`. height-split §8 classified it as a consequence of two printed results. Both are now stated.

**Definitions** (Mathlib objects; `S = Spec 𝓞_K`, `X, Y : Over S` group objects, `f : X ⟶ Y` a homomorphism):
- `kerScheme f := pullback f.left η_Y.left`. This is `G = ker f = X ×_{f, Y, e} S`.
- `kerUnit f hf : S → G`, the unit section, `pullback.lift η_X (𝟙 S)`. The lift exists by `IsMonHom.one_hom`.
- `kerOmegaLog f hf := ∑ᶠ P : S, log #(ker(s^#_P : 𝒪_{G,s(P)} → 𝒪_{S,P})).Cotangent`. This is `log #s*Ω¹_{G/S}`,
  computed stalkwise. For a section, `s*Ω¹_{G/S}` is the conormal sheaf `s*(I/I²)` (EGA IV 17.2.5, UNVERIFIED), and
  its stalk at `P` is `I_P/I_P²`. A torsion coherent sheaf on a Dedekind scheme is the sum of its stalks. Mathlib
  4.35 has no sheaf of relative differentials on schemes, so the global `s*Ω¹` cannot be written directly. The
  stalkwise form is the closest genuine object.
- `ExtendsIsogeny φ 𝒩A 𝒩B φ𝒩`: `(φ𝒩)_K ≫ 𝒩B.gen = 𝒩A.gen ≫ φ_K`.

**Leaves:**
- `FaltingsLemma5Printed` (Faltings, Invent. Math. 73 (1983), Lemma 5, p. 358; wording recalled, UNVERIFIED;
  locators.md could not read it). Setting: `A`, `B` over `K` with semistable Néron models `𝒩A`, `𝒩B`, and `φ𝒩`
  the homomorphism extending the isogeny `φ`. Statement: `h(B) = h(A) + ½ log deg φ − kerOmegaLog φ𝒩 / [K:ℚ]`.
  The identity does not depend on how the metric is normalized: a change shifts `h(A)` and `h(B)` by the same
  constant.
- `RaynaudKernelBound` (Raynaud, Astérisque 127 (1985), Exp. VII, Cor. 2.1.3 as cited by height-split §8 and
  Pazuki 2012 Rem. 2.3; UNVERIFIED): `kerOmegaLog φ𝒩 ≤ [K:ℚ] log deg φ`.

**Glue, all proved:**
- `exists_extension`: the Néron mapping property of `𝒩B` extends `φ`, and the extension is a homomorphism by
  reduct-glue's `isMonHom_of_ext`.
- `kerOmegaLog_nonneg`: the lower bound `0 ≤`.
- The arithmetic in `faltingsLemma5_of_printed`, then reduct-split's `faltingsLemma5BC_final`.

**Consistency check** (by hand, SPECULATIVE). Take `φ = [n]` on `A`, so `B = A`, `deg φ = n^{2g}` and
`G = 𝒩[n]`. Since `ω_{𝒩[n]} = ω_𝒩/n ≅ (𝒪_K/n)^g`, the identity gives `log # = g[K:ℚ] log n`, which is correct.
Raynaud's bound gives `g[K:ℚ] log n ≤ 2g[K:ℚ] log n`, which is consistent.

**Reading risk:** Faltings' Lemma 5 is unread. It may be printed only for good reduction, where `G` is finite
flat. In the semistable case `G` is only quasi-finite. The bound for that case is the one height-split attributes
to Raynaud.

## 4. `semistableNeronBaseChange` (part S)

reduct-glue proved SS2 from four leaves:
- `IdentityComponentBaseChangeDVR` (SGA 7 IX 3.3, in reduct-split's open-subgroup form);
- `IdentityComponentOL` (SGA 3 VI_B 3.10, in a group-model form);
- `OpenImmersionOfLocal` (EGA IV 8.10.5, specialized to `Spec (𝓞_L)_𝔭`);
- `NeronLocalizesDVR` (BLR 1.2/4).

Now:
- `NeronLocalizesDVR` is a theorem from the printed `BLR_1_2_4` (part N; `semistableNeronBaseChange_of_printedBLR`).
- `OpenImmersionOfLocal` is a theorem from the printed EGA IV 8.10.5.
- The other two are reduced to their printed forms plus four small glue Props about the topology of the identity
  component, and one more such Prop is proved.

**Final theorem:** `semistableNeronBaseChange_of_printed_final' (hB : BLR_1_2_4) (h3 : SGA3_VIB_3_10)
(h7 : SGA7_IX_3_3) (hE : EGAIV_8_10_5_openImm) (gc : IdCompSubgroup) (gf : IdCompGeomFibres)
(ga : OpenSubgroupIsIdComp) (gb : IdCompBaseChangeDVR) : SemistableNeronBaseChange` (compiled, standard axioms).

**Definition** `idCompSet G` is the identity component `G⁰` of a group scheme `G → S`, as a set: `x` belongs to it
if `x` lies in the connected component of `e(f x)` in the fibre `f⁻¹{f x}`. The fibre carries the subspace topology,
which Mathlib's `Scheme.Hom.fiberHomeo` identifies with the scheme fibre. **Mathlib 4.35 has no identity component
of a group scheme over a base.**

### 4.1 The printed-form leaves

| leaf (printed form, UNVERIFIED wording) | statement | replaces |
|---|---|---|
| `SGA3_VIB_3_10` (SGA 3 VI_B Thm 3.10) | `G` a smooth group scheme over any `S` ⇒ `IsOpen (idCompSet G)` | `IdentityComponentOL` |
| `SGA7_IX_3_3` (SGA 7 I, IX Prop. 3.3, second assertion) | Setting: `O ⊆ O'` DVRs with `K'/K` finite and `O' ∩ K = O`, `A` semistable at `O`, Néron models `𝒩`, `𝒩'`; `c : 𝒩 ×_O O' → 𝒩'` a homomorphism with isomorphic generic fibre; `U` an open with `U = idCompSet (𝒩 ×_O O')`. Conclusion: `U.ι ≫ c` is an open immersion with image `idCompSet 𝒩'`, i.e. `N⁰ ⊗ R' ≅ N'⁰` | `IdentityComponentBaseChangeDVR` |
| `EGAIV_8_10_5_openImm` (EGA IV₃ 8.10.5, open-immersion item) | In the kernel's limit setting (as in its leaf `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`): if the base change of `f_i : X_i → Y_i` (finitely presented) to `lim D` is an open immersion, so is its base change to some `D_j` | `OpenImmersionOfLocal` |

Three remarks on the Lean form of SGA 7 IX 3.3:
- The print speaks of the canonical morphism. The Lean form allows any homomorphism with isomorphic generic
  fibre. Such a map is the canonical one followed by a group automorphism of `𝒩'` (Néron), and that automorphism
  preserves `𝒩'⁰`. So the Lean form is a consequence of the print.
- The print's `N⁰ ⊗ R'` is written as `(N ⊗ R')⁰`. They agree because the fibres of `N⁰` are geometrically
  connected.
- The print allows any extension of DVRs (as recalled). The Lean form takes `K'/K` finite, which is a
  specialization.

### 4.2 Glue proved

1. **`OpenImmersionLocalization`** (`openImmersionLocalization : EGAIV_8_10_5_openImm → OpenImmersionOfLocal`).
   - `Spec O = lim_{a ∉ 𝔭} Spec 𝓞_L[1/a]`, indexed by `𝔭.primeCompl` preordered by divisibility
     (`ringCoconeOIsColimit`, `specConeOIsLimit`; built on `IsLocalization` and reduct-glue's `mem_iff_exists`, in
     the pattern of the kernel's `specConeIsLimit`).
   - EGA IV 8.10.5 at each maximal `𝔭` gives `s_𝔭 ∉ 𝔭` with an open immersion over `D(s_𝔭)`
     (`exists_away_of_dvr`).
   - Finish with the open cover of `Y` by `Y ×_S D(s_𝔭)` (`Cover.mkOfCovers`, `Scheme.Pullback.range_fst`),
     `IsZariskiLocalAtTarget.of_openCover`, and `pullbackRightPullbackFstIso`.
2. **`IdentityComponentFromPrinted`, reduced** (`identityComponentFromPrinted_of`) to `OpenSubgroupIsIdComp` and
   `IdCompBaseChangeDVR`.
   - The canonical homomorphism `c` comes from reduct-glue's `bcDVR`, the Néron property and `isMonHom_of_ext`.
   - `j = (i ×_O O') ≫ c` is an open immersion, by this chain:
     `range(i ×_O O') = fst⁻¹(range i) = fst⁻¹ 𝒩⁰ = (𝒩 ×_O O')⁰`.
     The chain uses `Scheme.Pullback.range_map` and the two glue Props. SGA 7 IX 3.3 says `c` is an open
     immersion on that open, and `IsOpenImmersion.isoOfRangeEq` combines the two.
3. **`IdentityComponentGroupModel`, reduced** (`identityComponentGroupModel_of`) to `IdCompSubgroup`,
   `IdCompGenericFibre` and `IdCompGeomFibres`.
   - The general construction `OpenSub`: an open `W` of a group scheme `G` that is closed under the group law
     carries a group structure for which `W → G` is a homomorphism. It uses `GrpObj.ofRepresentableBy` with the
     presheaf of groups `T ↦ {f : T ⟶ G | f(T) ⊆ W}` (`grpG0`, `isMonHom_incl`).
   - Smoothness and separatedness hold because `W → G` is an open immersion.
   - Quasi-compactness: `𝒢` is noetherian (`LocallyOfFiniteType.isLocallyNoetherian`,
     `quasiCompact_of_noetherianSpace_source`).
   - Generic fibre: the inclusion is an open immersion that is surjective on generic fibres
     (`isIso_iff_isOpenImmersion_and_surjective`).
4. **`IdCompGenericFibre`, PROVED** (`idCompGenericFibre`).
   - The generic fibre `𝒢_L ≅ A_L` is connected.
   - Its image in `𝒢` is the set of points over the generic point.
   - That image is a connected set containing `e(η)` (`IsPreconnected.subset_connectedComponentIn`).

### 4.3 Glue left

There are four named Props, all true, each with a docstring saying what it needs. All are about the topology of
the identity component of a smooth group scheme, and all reduce to two standard facts: an open subgroup of a group
scheme over a field is closed, and `(G_s)⁰` is geometrically connected (Stacks 04KV, the bundle leaf
`geomConnOfRationalPoint`). The missing tool is the fibrewise identification `(G ×_S G)_s = G_s ×_{κ(s)} G_s` on
underlying spaces.

| glue | statement |
|---|---|
| `IdCompSubgroup` | `G⁰` is closed under `μ` and the inverse (SGA 3 VI_A 2.3 fibrewise) |
| `IdCompGeomFibres` | the geometric fibres of the open subscheme `𝒢⁰ ⊆ 𝒢` at maximal ideals are connected |
| `OpenSubgroupIsIdComp` | an open subgroup of a group model over a DVR with connected generic and geometric special fibres has image `idCompSet` |
| `IdCompBaseChangeDVR` | `fst⁻¹(G⁰) = (G ×_O O')⁰` for a smooth group scheme over a DVR |

The successive coarser forms remain in the file and compile:
- `semistableNeronBaseChange_of_printed` (glue `IdentityComponentGroupModel`, `IdentityComponentFromPrinted`,
  `OpenImmersionLocalization`);
- `_of_printed'`;
- `_of_printed''`;
- `_of_printed_final`.

## 5. `shimuraFamily` (part H)

shimura-split reduced the field to its `ShimuraHolFamily` (`shimuraFamily_of_hol`). That reduction is one
holomorphic `τ ↦ y_τ ∈ Y₃(ℂ)` with the moduli clause, and its composition step with every `π : Y → P¹` is proved.
`Shimura.lean` copies shimura-split's file verbatim, and it still compiles at e38375b3 (VERIFIED). It then adds
the fullest form of the print that can be stated today:

**Leaf** `ShimuraMainThmIY3`. Sources (UNVERIFIED): Shimura, Ann. of Math. 85 (1967), Main Thm I; the moduli
interpretation comes from Shimura 1967 §§2-3, Ann. of Math. 78 (1963), and Deligne, Bourbaki 389, §4. Statement: on
a fine witness `(Y, Φ)`, some `y_τ` satisfies:
- `IsShimuraHolFamily`: the moduli clause `ℂ²/Λ_τ`, and holomorphy;
- the fibres of `τ ↦ y_τ` are exactly the `Γ(3)`-orbits, for `Γ(3) = {x ∈ 𝒪 : x x̄ = 1, x ≡ 1 mod 3𝒪}`
  (`InGamma3`), acting through `BPAnalytic.QM.iota` and Mathlib's `GL(2,ℝ)` action on `ℍ`. This is the
  injectivity of `Γ_S\ℍ → V_S(ℂ)`.

The orbit clause was checked by hand (SPECULATIVE). `Λ_{γτ} = Λ_τ/(cτ+d)` for `γ ∈ 𝒪¹`. The level structure
`η_τ(a) = ι(a)v_τ/3` is preserved iff `γ ≡ 1 mod 3𝒪`. An `ι`-compatible isomorphism `ℂ²/Λ_τ → ℂ²/Λ_{τ'}` is a
scalar, and it forces `τ' = uτ` with `u ∈ 𝒪^×` of norm `1`. `det ι(x) = nrd x`.

`shimuraFamily_of_mainThmI : ShimuraMainThmIY3 → ShimuraFamily` compiles.

**What the literal print needs and Mathlib 4.35 lacks:**
1. **Global class field theory.** Shimura's reciprocity law at a CM point `z` (fixed by `q(K^×)`) reads
   `φ_S(z)^{[s,K]} = φ_{S'}(z)`. It uses the Artin map `[·, K] : 𝔸_K^× → Gal(K^ab/K)` of an imaginary quadratic
   `K`. Mathlib has `FiniteAdeleRing` but no global reciprocity map. The reciprocity law characterizes the
   canonical model, so without it Main Thm I is only "a model over `k_S` with a holomorphic uniformization".
2. **The canonical model `V_S` of one component over `k_S = ℚ(ζ₃)` as a separate object, and Deligne's comparison
   `Y₃ ⊗ ℚ(ζ₃) = V_S ⊔ V_S^σ` (Bourbaki 389, §4).** shimura-glue §5.4 says the same. Without them the surjectivity
   of `Γ_S\ℍ → V_S(ℂ)` cannot be stated on the `ℚ`-model.

The holomorphy part is concrete over Mathlib (`IsHolFamily`: regular functions pull back to analytic functions).
No analytification is needed.

## 6. Statement review

- **No field statement changed.** Each is proved as the kernel constant. Verbatim copies are checked by `rfl`
  (VERIFIED).
- **None of the new leaves is vacuous as far as I can tell** (SPECULATIVE):
  - `BLR_1_2_4` and `FaltingsLemma5Printed`/`RaynaudKernelBound` have Néron models as hypotheses, and these exist
    (BLR 1.4/3).
  - `SGA7_IX_3_3` quantifies over an open `U` equal to `idCompSet`. That open exists by SGA 3 VI_B 3.10, so the
    leaf is not vacuous provided `idCompSet` is the identity component. It is, by construction.
  - `ShimuraMainThmIY3` is an existential, and it is true for Shimura's `φ_S` composed with the inclusion of a
    component.
- **None is stronger than the print, as recalled.** Every Lean form is the print or a weakening: the localization
  form of BLR quantifies over isomorphic copies; SGA 7 3.3 allows any homomorphism with isomorphic generic fibre;
  Shimura's reciprocity law and surjectivity are dropped. The exception is a possibly wrong recollection, which
  is the reading risk of each section.
- **Definitions Mathlib lacks:** a sheaf of relative differentials on schemes (replaced by stalkwise conormal
  modules), the identity component of a group scheme over a base (replaced by `idCompSet`), global class field
  theory, and Shimura's canonical models.

## 7. Checks

`scratch/c-to-printed/run.sh FILE` runs `lean` with `LEAN_PATH` on a copy of the e38375b3 build (`~/ctp-lib`). It
was run one Lean process at a time:
- `CToPrinted.lean`: about 15 s, no errors, 9 `#print axioms` lines, all standard (VERIFIED).
- `Shimura.lean`: about 6 s, no errors, 3 `#print axioms` lines, all standard (VERIFIED).

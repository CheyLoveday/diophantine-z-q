# javanpeykar-direct: `javanpeykarPrintedMapHF` from Javanpeykar 2014 Thm 1.1.1 stated over the print's objects

Task javanpeykar-direct, 2026-11-17. Base: `wip/leaf-fold33b` fe2f0d4a. Scratch: `scratch/javanpeykar-direct/`
(results log `log.md`). Nothing under `ZInQKernel/` was edited. The contribution file is
`scratch/javanpeykar-direct/JavanpeykarDirect.lean`. Copy it to `ZInQKernel/Contrib/OneProof/JavanpeykarDirect.lean`
without its final `#print` line.

Marks: **VERIFIED** means compiled, or read in a file of the repository. **STANDARD** means published, with a
reference. **UNVERIFIED** means a theorem number recalled from memory; there is no network here.

## 1. Result

The research field `javanpeykarPrintedMapHF : JavanpeykarRebase.JavanpeykarPrintedMap` is proved in Lean from one
new leaf, `JavanpeykarDirect.JavanpeykarThm111`. This leaf is Javanpeykar's Thm 1.1.1 stated over its own
objects, with one extra hypothesis (§2). The proof uses only the standard axioms (VERIFIED).

```lean
theorem JavanpeykarDirect.javanpeykarPrintedMap_of_thm111 (h : JavanpeykarThm111) :
    JavanpeykarRebase.JavanpeykarPrintedMap
-- axioms: [propext, Classical.choice, Quot.sound]
```

The recorded reading gap had two theorem steps between the print and the old field. Both are now Lean proofs:

| step | old field (`JavanpeykarPrintedMap`) | new leaf (`JavanpeykarThm111`) | bridge (proved) |
| --- | --- | --- | --- |
| (i) | `deg_B(X)` replaced by the degree `d` of a given Belyi map `β` | `deg_B(X) = belyiDegree X hB = Nat.find hB`, the least `d > 0` with a Belyi map of degree `d` | `belyiDegree_le` (`Nat.find_min'`), `javanpeykarBound_mono` (`13·10⁶·g·d⁵` increasing in `d`) |
| (ii) | `h_Fal(Jac X)` replaced by the printed stable height of a model `V` of `W` over `K`, the field of definition of `X₀` | `h_Fal(Jac X)`: `IsStableHeightBar W x`, the printed stable height of a model of `W` over any number field `L ⊆ ℚ̄` | `isStableHeightBar_of_model` (∃-introduction at `L = K`) |

The old field also restricted the curve:

| restriction in the old field | in the new leaf | bridge (proved) |
| --- | --- | --- |
| `X = X₀ ×_K ℚ̄` over `ℚ̄ = AlgebraicClosure K` | any curve `X` over any algebraic closure `ℚ̄` of `ℚ` | `isCurve_baseChange` (smooth, proper and geometrically connected are stable under base change); `isAlgClosure_rat` (`AlgebraicClosure K` is an algebraic closure of `ℚ`) |
| `g = genusBar X₀` | `g = genusK X = dim_ℚ̄ H¹(X, 𝒪_X)` | `genusK_baseChange` (`rfl`) |

**Count.**
* The raw autofold dry run gives strict 16/15 on 31 → 17/14 on 31, and strictest the same (VERIFIED, §4).
  * `autofold.py` counts a kind-published leaf whose flag is "pending review" as LEAF.
* Under Addendum 1 the fold is **neutral**: a new printed leaf counts GLUE until a reviewer rates it. The fold
  replaces one GLUE row with one GLUE row, so the count stays 16/15 on 31.
  * The lead should set the new row's strict and strictest to GLUE after folding, as for the other
    "pending review (Addendum 1 …)" rows.
* Once a reviewer rates `javanpeykarThm111` LEAF, the count is **−1 strict GLUE**: 17/14 on 31.
* No further printed theorem was needed. The fold adds no new glue row.

## 2. The new leaf, and why it is the print

```lean
def JavanpeykarThm111 : Prop :=
  ∀ (Kbar : Type) [Field Kbar] [Algebra ℚ Kbar] [IsAlgClosure ℚ Kbar]
    (X : Over (Spec (CommRingCat.of Kbar))) [IsCurve X] [IsIntegral X.left],
    (∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of Kbar))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of Kbar)) ↘ Spec (CommRingCat.of Kbar) = X.hom) →
    1 ≤ genusK X →
    ∀ (W : AbelianVariety Kbar)
      (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible X.hom W.group repW →
    ∀ (hB : ∃ d, HasBelyiMapOfDegree X d),
    ∀ x : ℝ, IsStableHeightBar W x → x ≤ javanpeykarBound (genusK X) (belyiDegree X hB)
```

**The print.** Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8
(2014), Thm 1.1.1, p. 90 (arXiv:1403.6404v1, p. 1). For a smooth projective connected curve `X` over `ℚ̄` of genus
`g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`. Here `h_Fal(X)` is the stable Faltings height of `Jac(X)`
(p. 98, arXiv §2.3). The locator audit recorded these locators (`docs/research/locators.md` row R18; VERIFIED as
recorded). Row R18 also records: "Any Belyi-map degree d bounds the minimal Belyi degree. No field-degree factor
or semistability over the original field is required."

**Object by object:**

* **`ℚ̄`.** `Kbar` is any field with `IsAlgClosure ℚ Kbar`. The print fixes one algebraic closure; all of them are
  isomorphic, and the statement holds for each, so the leaf is a ∀ over the print's choices.
* **`X`.** The hypotheses are:
  * `IsCurve X`: proper, smooth of relative dimension 1, geometrically connected;
  * `IsIntegral X.left`: implied by smooth and connected, and needed to state `IsBelyiMap`;
  * projective: a closed immersion into `ℙ(n; Spec ℚ̄)` over `ℚ̄`.
  These are exactly "smooth projective connected curve over `ℚ̄`".
* **`g`.** `genusK X` is the arithmetic genus `dim_ℚ̄ H¹(X, 𝒪_X)` (vendored `Scheme.arithmeticGenus`). The
  hypothesis is `1 ≤ g`.
* **`Jac(X)`.** `W` is an abelian variety over `ℚ̄` representing `Pic⁰_{X/ℚ̄}`, with the group law from the tensor
  product (vendored `picardFunctorDegree`, `PicardTensorCompatible`). It is unchanged from the old field.
* **`deg_B(X)`.** `belyiDegree X hB := Nat.find hB`, where `HasBelyiMapOfDegree X d := 0 < d ∧ ∃ β, IsBelyiMap X β d`.
  * javanpeykar-fix's `IsBelyiMap` is: a finite morphism over `ℚ̄`, unramified at every closed point over
    `ℙ¹ ∖ {0, 1, ∞}`, of degree `[ℚ̄(X) : ℚ̄(ℙ¹)]`.
  * `0 < d` excludes nothing: a finite morphism of curves has positive degree. With it, the minimum is the
    print's minimum.
  * The hypothesis `hB`, that some Belyi map exists, is the only addition to the print. It is always true by
    Belyi's theorem, so the leaf is a special case (a hypothesis added). The consumer supplies a Belyi map, so
    Belyi's theorem is not needed.
  * `belyiDegree` does not depend on `hB` (`belyiDegree_congr`, `rfl`). It is attained
    (`hasBelyiMapOfDegree_belyiDegree`).
* **`h_Fal(X) = h_Fal(Jac X)`.** `IsStableHeightBar W x` holds when `W ≅ V ×_L ℚ̄` for an abelian variety `V` over
  a number field `L` with an embedding `L → ℚ̄`, and `x` is height-fix's printed stable height of `V`
  (`ZInQ.HeightFix.IsPrintedStableHeight`).
  * height-fix's height is defined from a Néron model over a number field `L' ⊇ L` where `V` has semistable
    reduction, with `ω = ⋀^g Γ(e*Ω¹)`, archimedean metric `(i/2)^g ∫ η ∧ η̄` defined chart by chart, and
    normalization by `[L' : ℚ]`.
  * This is Faltings' definition of the stable height of an abelian variety over `ℚ̄`: take a model over a number
    field and the stable height of that model (Faltings 1983 §1; Deligne, Sém. Bourbaki 616; locators
    UNVERIFIED).
  * The leaf is `∀ x, IsStableHeightBar W x → x ≤ …`, which is equivalent to "for every model `V` over every
    number field `L ⊆ ℚ̄`, every printed stable height of `V` is `≤ …`".

**Not stronger than the print.** Every hypothesis is one of the print's hypotheses or is implied by them, and `hB`
is added. The conclusion is the print's, provided every `x` with `IsStableHeightBar W x` equals `h_Fal(Jac X)`.
That proviso is the well-posedness of Faltings' stable height, a property of the definition (§3). It is not a
theorem step between the print and the leaf.

**Not vacuous.** The consumer (`javanpeykarBound_of_printed_rebase`) proves every hypothesis at
`X = X₀ ×_K ℚ̄`. The specialization in `javanpeykarPrintedMap_of_thm111` shows this.

**Compared with the old field.** The new leaf is more general:
* any curve over any `ℚ̄`, not only `X₀ ×_K AlgebraicClosure K`;
* models over any number field in `ℚ̄`, not only over `K`;
* the minimal Belyi degree, not an arbitrary one.

It is exactly the generality of the print.

## 3. Readings that remain (definition level, no theorem step)

These readings define the print's objects. They are shared with rows that have already been rated:
`bostLowerBoundPrinted` is strict LEAF over the same `IsPrintedStableHeight`.

1. **`IsStableHeightBar` is Faltings' stable height of `W/ℚ̄`.** This means it does not depend on the number field
   `L`, the model `V`, or the semistable field and Néron model inside `IsPrintedStableHeight`. Faltings 1983 §1
   states this (UNVERIFIED locator). In the tree:
   * For a fixed `V`, the kernel's `IsStableFaltingsHeight` is single-valued (`ZInQ.HeightSplit.isStableFaltingsHeight_unique`,
     from the leaves N1 = `NeronModelExists` and SS2 = `SemistableNeronBaseChange`). Printed implies kernel
     (`ZInQ.HeightFix.isStableFaltingsHeight_of_printed`, T35 and Stacks 04KV, both proved). So the printed height
     of a fixed model is single-valued given N1 and SS2.
   * Independence of the model `V` (two models over number fields that become isomorphic over `ℚ̄`) needs
     descent of the isomorphism to a finite extension. This is standard but not in the tree. It is needed only
     for well-posedness, not for the fold.
2. **height-fix's `IsPrintedStableHeight`**: the chart-wise density, and semistability read over the residue fields
   `k(𝔭)` (SGA 7 IX Déf. 3.4). Unchanged from javanpeykar-rebase.
3. **"Unramified over `ℙ¹ ∖ {0, 1, ∞}`"** is read at closed points through the ramification index
   (`IsBelyiMap`). **"Projective"** is read as a closed immersion into `ℙ(n; Spec ℚ̄)`. Both are unchanged.

Gone compared with javanpeykar-rebase's list of readings:
* "the stable height over `ℚ̄` read on a model over `K`" is now ∃ over all models;
* "`deg_B` read as the degree of a given Belyi map" is now `Nat.find` with a proved bridge.

## 4. What compiles (VERIFIED on this host, 2026-11-17)

| check | outcome |
| --- | --- |
| `lake env lean scratch/javanpeykar-direct/JavanpeykarDirect.lean` | compiles in 12 s; `javanpeykarPrintedMap_of_thm111` has axioms `[propext, Classical.choice, Quot.sound]` |
| `lake build +ZInQKernel.Contrib.OneProof.JavanpeykarDirect`, with the file temporarily placed there and removed afterwards | success, 12860 jobs, the new module 61 s |
| `autofold.py scratch/javanpeykar-direct/autofold.json --dry-run` (output `FoldDryRun.lean.txt`, line 1 stripped) | exit 0 without `--allow-rise`; strict 16/15 on 31 → 17/14 on 31 (raw; neutral under Addendum 1, §1); generates `OpenResearchLeaves40` (39 without `javanpeykarPrintedMapHF`, with `javanpeykarThm111`) and `sixContactMin_of_open58` |
| `lake build +ZInQKernel.OneProof.H.TailZ64` (this tree's sources; `build-tailz64.txt`) | success, 15211 jobs |
| the dry-run module, `lake env lean` (`FoldDryRun-compile.txt`) | compiles in 18 s; `HDec.HSyn.sixContactMin_of_open58` has axioms `[propext, Classical.choice, Quot.sound]` |
| `lake env lean scratch/javanpeykar-direct/WellPosed.lean` (`WellPosed-output.txt`) | compiles; `isStableHeightBar_of_iso` and `isPrintedStableHeight_unique` (given N1 and SS2) have the standard axioms |

The contribution file has no `sorry`, no `axiom`, and no code that runs at build time. Its only import is
`ZInQKernel.Contrib.OneProof.JavanpeykarRebase`.

Supporting results, not used by the fold (`WellPosed.lean`):
* `isStableHeightBar_of_iso`: `IsStableHeightBar` is invariant under isomorphism of `W`.
* `isPrintedStableHeight_unique (hN1 : NeronModelExists) (hSS2 : SemistableNeronBaseChange)`: the printed
  stable height of a fixed model is single-valued.
  * T35 comes from `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed_proof`, and Stacks 04KV from
    `geomConnOfRationalPoint_proof`; all three are proved.
  * This is reading 1 of §3 for a fixed model.

## 5. Notes for the integrator

* Fold with `python3 scripts/one_proof/autofold.py scratch/javanpeykar-direct/autofold.json`, after copying the
  contribution file into `ZInQKernel/Contrib/OneProof/JavanpeykarDirect.lean`. It imports only
  `ZInQKernel.Contrib.OneProof.JavanpeykarRebase`, not `OneProof.Main`.
* Then set the new row `javanpeykarThm111` to strict and strictest GLUE (Addendum 1) until a reviewer rates it.
* Proposed `locators.md` row R18: Javanpeykar 2014 Thm 1.1.1 over its own objects,
  `JavanpeykarDirect.JavanpeykarThm111`. It supersedes `JavanpeykarRebase.JavanpeykarPrintedMap`, which is now
  proved from it.

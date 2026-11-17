# cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex L581-586) proved

Task cm-fibre-split (2026-11-17). Base: `origin/wip/cox-lattice` 6298e108 with `origin/main` 67950e829 merged
(merge commit 096c052c7). Results log: `scratch/cm-fibre-split/log.md`. Marks: VERIFIED (compiled, or read in the
tree / the manuscript), STANDARD (published, exact reference), UNVERIFIED (numbers from memory; no network), SPECULATIVE.

## 1. Result

**Manuscript check: no error found in L581-586.** The text is correct as written, including "All its elements are
defined over L": `L = EK` as defined in A8 (L544-561) is large enough (§3).

**`CMFibreSplit` is proved, statement verbatim, from leaves the chain already carries. No new leaf and no new glue.**
VERIFIED: compiles, no `sorry`, `#print axioms` = `propext, Classical.choice, Quot.sound`
(`scratch/cm-fibre-split/axioms-out.txt`). The statement check `scratch/cm-fibre-split/Statement.lean` copies the
Prop verbatim and checks it `Iff.rfl`.

```lean
theorem HDec.CMBranch.FibreSplit.cmFibreSplit_of_leaves (hYu : QMLattice.YuB6Alg)
    (hHFF : ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich) (hRay : PkgI2.RaynaudCriterionNF)
    (hTors : PkgI2.TorsionStructure) : CMBranch.CMFibreSplit
```

(`ZInQKernel/Contrib/OneProof/CMFibreSplit.lean`). Each hypothesis is something the route already has at the open4
generation, where the CM branch consumes `CMFibreSplit`:

| hypothesis | supplied by |
|---|---|
| `hYu` | that generation's argument (T27, Yu) |
| `hHFF` | `t.t6` (T6) |
| `hNOS` | `r.r7a` |
| `hRay` | `r.r6` |
| `hTors` | `t.t5` |
| `hCover` | the chain's own G2, `fibreCoverExists_of_propTSAll' t.t5 (propTSAll_of_pieces3_r5 r.r1r2 …) unramifiedConjugates_proved` |

**The CM fold is one GLUE lower.** The dry run
`HDec.HSyn.sixContactMin_of_open73_cmfs (r : OpenResearchLeaves54CMFS) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) : ZInQ.SixContactMin`
(`ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean`, generated; compiled, standard axioms) is cm-branch2's
`sixContactMin_of_open73_cm` with the bundle field `cmFibreSplit` removed. Spec: `scratch/cm-fibre-split/autofold.json`.

**Net change:**
* against cm-branch2's spec: GLUE −1 (`cmFibreSplit`), no new glue, no new leaf;
* against cm-branch2's base top `OpenResearchLeaves53`: GLUE −1 net (cm-branch2 removed `gonzalezRotgerThm512X6RCF`;
  `CMFibreSplit` is now gone too), plus cm-branch's four leaves, which are pending review.

The manuscript's steps, as formalized:

| piece | manuscript | Lean (file under `Contrib/OneProof/CMFibreSplit/`) |
|---|---|---|
| A8's Hom field at every fibre, without NoCM or conjugacy maps: `L = E ⊔ K` with `[L:ℚ] ≤ D`; `A = (PK.A)_L` with `A_ℚ̄ ≅ P.A` (homomorphisms both ways); `End(A) → End(A_ℚ̄)` onto | L544-561, L583 "All its elements are defined over L" | `CMHomFieldModel`, `cmHomFieldModel_of`, `endBC_surjective_of_homField`, `paste_iso` (Reduction.lean) |
| a non-integral `𝒪`-centralizer forces `End⁰ ≅ M₂(ℚ(√d))`, `d < 0` | L572-582 | `end0Matrix_of_noncentral` (Reduction.lean) |
| multiples of matrix units in `End_L(A)` | L583 | `exists_scaledMatrixUnits` (Curve.lean) |
| `E` = image of `n e₁₁`, `E² = E × E`, the `L`-isogeny `E² → A`, `dim E = 1` | L583-585 | `matrixUnit_isogeny` (Curve.lean) |
| `End(E_{L̄})` is an order of the imaginary quadratic field `ℚ(√d)` | L584-586 "with complex multiplication", "the full geometric endomorphism order of E" | `CMCurveOrder`, `cmCurveOrder_of` (CurveOrder.lean) |
| the assembly | L581-586 | `cmFibreSplit_of`, `cmMatrixUnitSplit_of`, `cmFibreSplit_of_curveOrder`, `cmFibreSplit_of_leaves` |

## 2. What `CMFibreSplit` packs, and the manuscript's own argument

`CMFibreSplit` (ZInQKernel/Contrib/OneProof/CMBranch.lean) says: at a fibre with a CM point (`¬ NoCMAt u`), there
are
* a number field `L` with `[L:ℚ] ≤ D`;
* a model `A/L` of the fibre surface (`FibreOver`);
* an elliptic curve `E/L` whose geometric endomorphism ring is an order `R` of an imaginary quadratic field `k`;
* the product `E² = E × E`;
* an `L`-isogeny `E² → A`.

The manuscript's text (thm:height, proof, L581-586):

* L582: "Suppose End⁰(A_Q̄) = M₂(k)." This is the second case of the dichotomy of L563-577.
* L583: "All its elements are defined over L." Here `L = EK` is A8's field (L544-561): `E` is the kernel field of
  `G_ℚ` acting on the geometric endomorphism lattice of `W₀ = Res_{K/ℚ} A`, and L560-561 already state that `L`
  "defines every geometric endomorphism".
* L583-585: "Multiples of matrix units therefore give an elliptic curve E/L with complex multiplication and an
  L-isogeny E² → A."

The manuscript uses no Weil restriction in L581-586 itself. The Weil restriction `W₀` appears only in A8 (L546),
which defines the field `L`; cm-branch2 §2.3 calls this route "Weil restriction" for that reason. The formalization
follows the manuscript: A8's Hom field, then matrix units.

**Why the chain's A8 did not cover a CM fibre, and why that does not matter here.** The chain's
`KernelFieldExists` packs A8's field *and* B1's conjugacy maps `m_σ` (`KernelFieldOut` contains `ConjugacyData`).
Only the conjugacy maps need NoCM (`ConjMapsNoCM`, trivial commutant). The kernel field
(`kernelField_of_model_hf`, leaves T6 and NOS) and the descent of `G_L`-invariant morphisms (`td_hom_inv`, `hfd`,
proved for twist-descent) need no NoCM. `CMFibreSplit` needs only the field and the descent of endomorphisms, so
`cmHomFieldModel_of` assembles exactly those pieces. This is the manuscript's A8 argument: the kernel field of the
Galois action on the Hom lattice of the conjugates, which is the endomorphism lattice of `Res_{K/ℚ} A`, then descent.

## 3. Manuscript check (L581-586)

**Verdict: correct as written.** Step by step:

1. *"Suppose End⁰(A_Q̄) = M₂(k)."* This is the second branch of L563-577. The chain does not formalize the
   manuscript's Hodge-theoretic derivation of the dichotomy (Milne, Part I Thms 2.8-2.9, cited at L564, and the
   centralizer of `J` in `B ⊗ B^op`). It uses Yu's theorem (T27, the existing leaf `QMLattice.YuB6Alg`), which gives
   the same dichotomy. This replacement predates this task; see Known issue 1. At a fibre whose
   `𝒪`-centralizer contains a non-integer, the B branch is impossible:
   * `End⁰ ≅ B` forces `End = ι(𝒪)` (`end_eq_iota_of_B`, copied from the chain's `endEqOFibre_of_hf`);
   * the centre of `𝒪` is `ℤ` (`central_O`).
2. *"All its elements are defined over L."* **L is large enough.**
   * `G_ℚ` acts on `End(W₀,Q̄) = ⊕_{e,e'} Hom(A_e, A_{e'})`, and `L = EK`, with `E` the fixed field of the kernel.
   * An element of `G_L` fixes `K`, hence the block `(e₀, e₀)`, which is `End(A_Q̄)` for the given embedding
     `e₀ : K ⊆ Q̄`. On that block it acts by Galois conjugation of endomorphisms, and that action is trivial.
   * A `G_L`-invariant `Q̄`-morphism of finite-presentation schemes descends to `L`: EGA IV 8.8.2 to a finite
     level, then fpqc Galois descent.
   * So `End(A_L) → End(A_Q̄)` is onto, hence so is `End⁰(A_L) → End⁰(A_Q̄)`. VERIFIED in Lean:
     `endBC_surjective_of_homField`, with the tree's descent (`TwistDescentHFD.hfd`, which uses the proved
     `MorphDescend.exists_descend` and `TwistDescentGD.descend`) and rigidity to make the descended map a
     homomorphism.
   * The bound `[L:ℚ] ≤ F₀·3^{r²} ≤ D` with `r ≤ 16F₀²` is the chain's `a8_field`.
3. *"Multiples of matrix units therefore give an elliptic curve E/L … and an L-isogeny E² → A."* Correct; VERIFIED
   in Lean (`matrixUnit_isogeny`). The manuscript leaves these details implicit:
   * there is `n` with `n e_{ij} ∈ End(A_L)` for all four matrix units, and `End` is torsion-free;
   * `E = n e₁₁(A)` is an abelian subvariety over `L`, by Cartier's theorem;
   * `(x, y) ↦ x + n e₂₁ y` is an isogeny, with quasi-inverse `a ↦ (h(n² a), h(n e₁₂ a))`, where `h : A ↠ E`
     satisfies `i ∘ h = n e₁₁`; both composites are `[n³]`;
   * `dim E = 1` follows by counting dimensions.
4. *"with complex multiplication"*, and L585-586, *"the full geometric endomorphism order of E"*. Correct; VERIFIED
   in Lean (`cmCurveOrder_of`):
   * `End⁰(E_Q̄)` is the corner `e M₂(k) e ≅ k` of the rank-one idempotent `e = e₁₁`;
   * `End(E_Q̄)` is an order of `k`;
   * `End(E_{L̄}) ≅ End(E_Q̄)`, because both `Q̄` and `L̄` are algebraic closures of `L`.

**Labels.**

| formalized step | label | Lean |
|---|---|---|
| A8's Hom field: kernel field, `L = EK`, degree bound, `L` defines every geometric endomorphism (L544-561) | ELLIOT (the manuscript's own argument; the descent of invariant morphisms is not cited there) | `cmHomFieldModel_of`, `endBC_surjective_of_homField` |
| the pasting `(B_L)_Q̄ ≅ B ×_K Q̄` and `A_Q̄ ≅ P.A` | on-the-spot (bookkeeping) | `paste_iso`, R1's naturality + `bc_transport` |
| CM case `End⁰ ≅ M₂(k)` at a fibre with non-integral `𝒪`-centralizer | ELLIOT step, entered through the chain's leaf T27 (Yu) instead of the manuscript's L563-577 (pre-existing replacement) | `end0Matrix_of_noncentral` |
| multiples of matrix units (L583) | ELLIOT | `exists_scaledMatrixUnits` |
| `E`, `E²`, the isogeny, `dim E = 1` (L583-585) | ELLIOT; the explicit quasi-inverse and the dimension count are on-the-spot | `matrixUnit_isogeny` |
| `End(E_{L̄})` an imaginary quadratic order (L584-586) | ELLIOT; the corner computation, the transport between algebraic closures and the finite conductor are on-the-spot | `cmCurveOrder_of` |

**On-the-spot proof sketches** (each is a Lean proof now):

* `paste_iso`: `(B_L)_Q̄` and `B ×_{K,e₀} Q̄` are both pullbacks of `B → Spec K` along
  `Spec Q̄ → Spec L → Spec K`. Glue the two squares; the comparison isomorphism preserves the identity section, so
  it is a homomorphism by rigidity.
* B-exclusion: if `End⁰(P.A) ≅ B`, then `B → End⁰` is onto by dimension, so `End(P.A)` is an order of `B`
  containing the maximal order `ι(𝒪)`, hence equal to it. A centralizing element is then `ι(a)` with `a` central in
  `𝒪`. Commuting with `i` and `j` forces `a ∈ ℤ`.
* Matrix units: clear the denominators of `e⁻¹(E_{ij})` in `ℚ ⊗ End(A)` by one integer `m`. The relations hold in
  `End(A)` because `End(A) → ℚ ⊗ End(A)` is injective: `[s]` is surjective, hence an epimorphism. Replacing the
  matrix units by `m` times themselves gives the scale `n = m²`.
* Isogeny: write `E` with `i : E ↪ A`, `h : A ↠ E`, `h ≫ i = f₀₀` (image factorization, Cartier proved in the tree).
  * From `f₀₀² = n f₀₀` we get `i ≫ h = [n]`, because `i` is mono and `h` is epi (reduced source, separated target).
  * Put `φ = p₁ i + p₂ i f₁₀` and `ψ = (h n², f₀₁ h)`; the matrix-unit relations give `φψ = [n³]` and `ψφ = [n³]`.
  * So `φ` is surjective, because `[n³]` is, and finite, because `φ ≫ ψ` is finite and `ψ` is separated.
  * `dim E² = dim A = 2` because `φ` is finite and surjective, and `dim E² = 2 dim E`.
* CM order:
  * Over `Ω` (an algebraic closure of `L`), put `F = h' i'` and `ψ = e ∘ (1 ⊗ –) : End(A_Ω) → M₂(k)`, which is
    injective (torsion-free).
  * `ε = (1/n) ψ(F)` is idempotent. It is not `0`, since `1 ≠ 0` in `End(E_Ω)` because `dim E = 1`. It is not `1`,
    since otherwise `i'` would be finite and surjective and `dim E = dim A`.
  * A rank-one idempotent of `M₂(k)` has trace 1 and `ε y ε = tr(yε) ε` (`idem_two`, a 2×2 identity from
    `det ε = 0`).
  * `κ(g) = tr((1/n) ψ(h' g i'))` is then a ring map `End(E_Ω) → k`, injective since `End` is torsion-free.
  * Its image `R` lies in `𝓞_k`: endomorphisms are integral, because `End(E_Ω)` is a finitely generated ℤ-module by
    T6 with an embedding `Ω → ℂ`.
  * `R` contains `s n √d` for some `s ≠ 0`: clear the denominators of `e⁻¹(√d·1)`. Hence `R ⊇ ℤ[s n √d]` has finite
    index in `𝓞_k`, by cm-branch2's `discr_order`: `b² − 4N = [𝓞_k : ℤ[θ]]² d_k ≠ 0`.
  * `End(E_{L̄}) ≅ End(E_Ω)` by transport along an `L`-isomorphism `Ω ≅ L̄` (`trEquiv`): conjugation by the
    comparison isomorphism over `Spec σ`, with the group law via `xc_mul`.
  * `ℚ(√d) = AdjoinRoot (X² − d)` is a totally complex quadratic number field: a real embedding would send `√d` to
    a real number with negative square.

## 4. The intermediate Props (all proved)

| Prop | statement | proved by |
|---|---|---|
| `CMHomFieldModel` | at every fibre context: `L ⊆ ℚ̄`, `[L:ℚ] ≤ D`, `A/L` with `A_ℚ̄ ≅ P.A` as abelian varieties and `End(A) → End(A_ℚ̄)` onto | `cmHomFieldModel_of hCover hHFF hNOS hRay hTors` |
| `CMMatrixUnitSplit` | `A/L` abelian surface, `End(A) → End(A_Ω)` onto, `End⁰(A_Ω) ≅ M₂(ℚ(√d))` ⇒ `E`, `E²`, isogeny, order | `cmMatrixUnitSplit_of (cmCurveOrder_of hHFF)` |
| `CMCurveOrder` | `A/L` abelian surface with `End⁰(A_Ω) ≅ M₂(ℚ(√d))`, `E/L` of dimension 1, `i : E → A`, `h : A → E`, `h ∘ i = [n]` ⇒ `End(E_{L̄}) ≅` an order of an imaginary quadratic field | `cmCurveOrder_of hHFF` |

None of them is a new open hypothesis; they structure the proof.

## 5. Files

| file | content |
|---|---|
| `ZInQKernel/Contrib/OneProof/CMFibreSplit.lean` | `cmFibreSplit_of_curveOrder`, **`cmFibreSplit_of_leaves`** (the deliverable) |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Reduction.lean` | `CMHomFieldModel`, `CMMatrixUnitSplit`, `end_eq_iota_of_B`, `central_O`, `end0Matrix_of_noncentral`, `endEquivOfIso`, `end0EquivOfIso`, `paste_iso`, `endBC_surjective_of_homField`, `cmHomFieldModel_of`, `cmFibreSplit_of` |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Curve.lean` | the `Hom` calculus (`cmp`, `cancel_closedImm`, `cancel_surj`), `matrixUnit_isogeny`, `exists_scaledMatrixUnits`, `CMCurveOrder`, `cmMatrixUnitSplit_of` |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/CurveOrder.lean` | `ℚ(√d)` facts, `conductor_ne_zero_of_mem`, `trEquiv`, `idem_two`, `homBC`, `eq_zero_of_nsmul`, `one_ne_zero_of_dim`, `includeRight_injective`, `cmCurveOrder_of` |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean` | the fold dry run (generated by `scratch/cm-fibre-split/gen/gen_fold.py`): `CMInputsFS` (cm-branch's four leaves), base `sixContactMin_of_open4_hf_pz_eb_cmfs`, cm-branch2's chain open6..open48 re-typed, `OpenResearchLeaves54CMFS`, `sixContactMin_of_open73_cmfs` |
| `scratch/cm-fibre-split/` | scratch versions (`Split.lean`, `Geom.lean`, `MU.lean`, `KdAlg.lean`, `CurveOrder.lean`), `Statement.lean` (verbatim copy, `Iff.rfl`), `Axioms.lean` + `axioms-out.txt`, `Discharges.lean` + `discharges.txt`, `autofold.json`, `gen/`, `log.md` |

## 6. Compile log, axioms, `#discharges`

* `lake build +ZInQKernel.Contrib.OneProof.CMFibreSplit +ZInQKernel.Contrib.OneProof.CMFibreSplit.Fold`: success
  (15400 jobs).
* `#print axioms` (`axioms-out.txt`): `propext, Classical.choice, Quot.sound` for 16 declarations, among them
  `cmFibreSplit_of_leaves`, `cmCurveOrder_of`, `trEquiv`, `idem_two`, `conductor_ne_zero_of_mem`,
  `cmHomFieldModel_of`, `matrixUnit_isogeny`, `sixContactMin_of_open4_hf_pz_eb_cmfs`, `sixContactMin_of_open73_cmfs`.
* `#discharges` against Main at this base (`discharges.txt`). Main's top bundle is now `OpenResearchLeaves57`;
  cm-branch2's fold was written against `OpenResearchLeaves53`. The output has 171 `DISCHARGES` lines: 156 are
  projections of copied bundle structures (noise, as in cm-branch2), and 15 are pre-existing reductions. None comes
  from this task. That is expected: `cmFibreSplit` is a field of cm-branch2's fold bundle, not of Main's top.
  Rebasing the CM fold onto `OpenResearchLeaves57` is the cm-fold-rebase task. It should call
  `cmFibreSplit_of_leaves` at its open4 generation, as `Fold.lean` does.

## 7. Known issues

1. **Dichotomy source.** The CM case is entered through Yu's theorem (T27, `YuB6Alg`, an existing chain leaf), not
   the manuscript's L563-577 (Milne + Hodge centralizer). This is a pre-existing replacement and is noted, not new.
   The CM branch at L581 assumes the conclusion of that dichotomy, and Yu gives exactly it.
2. **Fold base.** The spec and dry run are relative to cm-branch2's fold (`OpenResearchLeaves53` → `54CM`), not
   to Main's current top (`OpenResearchLeaves57`); see §6.
3. No Gross–Zagier or Tian–Yuan–Zhang argument is used. No existing statement or consumer was changed. The only
   statement I amended is my own new `CMCurveOrder`, which gained the hypothesis `A.dim = 2` before it was proved.
4. Housekeeping: once, a `lake build` was started with `&` instead of the background-run mechanism. It was a single
   lake process, it was then monitored to completion, and no other Lean process ran alongside it.

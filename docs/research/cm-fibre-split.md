# cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex L581-586)

Task cm-fibre-split (2026-11-17). Base: `origin/wip/cox-lattice` 6298e108 with `origin/main` 67950e829 merged
(merge commit 096c052c7). Results log: `scratch/cm-fibre-split/log.md`. Marks: VERIFIED (compiled, or read in the
tree / the manuscript), STANDARD (published, exact reference), UNVERIFIED (numbers from memory; no network), SPECULATIVE.

## 1. Result

**Manuscript check: no error found in L581-586.** The text is correct as written, including "All its elements are
defined over L": `L = EK` as defined in A8 (L544-561) is large enough (§3).

**`CMFibreSplit` is reduced, in Lean, to the chain's own leaves plus one smaller on-the-spot glue Prop
`CMCurveOrder`.** That Prop says the elliptic curve `E` has an imaginary-quadratic order as its geometric
endomorphism ring. Everything else that `CMFibreSplit` packs is proved (VERIFIED: compiles, no `sorry`, `#print axioms`
= `propext, Classical.choice, Quot.sound`; `scratch/cm-fibre-split/axioms-out.txt`):

```lean
theorem HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder (hYu : QMLattice.YuB6Alg)
    (hHFF : ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hCover : G0ModField.FibreCoverExists)
    (hNOS : PkgI2.NeronOggShafarevich) (hRay : PkgI2.RaynaudCriterionNF)
    (hTors : PkgI2.TorsionStructure) (hCO : CMCurveOrder) : CMBranch.CMFibreSplit
```

(`ZInQKernel/Contrib/OneProof/CMFibreSplit.lean`). All of its hypotheses except `hCO` are available where the CM
branch consumes `CMFibreSplit`, the open4 generation of the route:
* `hYu` is that generation's argument;
* `hHFF = t.t6`, `hNOS = r.r7a`, `hRay = r.r6`, `hTors = t.t5`;
* `hCover = fibreCoverExists_of_propTSAll' t.t5 (propTSAll_of_pieces3_r5 r.r1r2 …) unramifiedConjugates_proved`, the
  chain's own G2.

**What is proved:**

| piece | manuscript | Lean (file) | status |
|---|---|---|---|
| A8's Hom field at **every** fibre, with no NoCM and no conjugacy maps: `L = E ⊔ K` with `[L:ℚ] ≤ D`, a model `A = (PK.A)_L` with `A_ℚ̄ ≅ P.A` (homomorphisms both ways), and `End(A) → End(A_ℚ̄)` onto | L544-561, L583 "All its elements are defined over L" | `CMHomFieldModel`, `cmHomFieldModel_of` (Reduction.lean) | **proved** |
| every endomorphism of `(B_L)_ℚ̄` descends to `L` when `G_L` fixes the Hom lattice of the conjugates | L560-561 | `endBC_surjective_of_homField` (from `td_hom_inv`, `TwistDescentHFD.hfd`, rigidity) | **proved** |
| `(B_L)_ℚ̄ ≅ B ×_K ℚ̄` as abelian varieties | — (pasting of base changes) | `paste_iso` | **proved** |
| a non-integral `𝒪`-centralizer forces `End⁰ ≅ M₂(ℚ(√d))`, `d < 0` | L572-582 ("Suppose End⁰(A_Q̄) = M₂(k)") | `end0Matrix_of_noncentral` (Yu's dichotomy = the chain's leaf `YuB6Alg`; the case `End⁰ ≅ B` gives `End = ι(𝒪)`, whose centre is `ℤ`) | **proved** |
| "multiples of matrix units" in `End_L(A)` | L583 | `exists_scaledMatrixUnits`, inside `cmMatrixUnitSplit_of` | **proved** |
| "give an elliptic curve `E/L` … and an `L`-isogeny `E² → A`": `E` = image of `n e₁₁` (an abelian subvariety, by Cartier's theorem, proved in the tree), `E² = E × E`, `φ(x, y) = i x + f₁₀(i y)`, finite and surjective, `dim E = 1` | L583-585 | `matrixUnit_isogeny` (Curve.lean) | **proved** |
| `End(E_{L̄})` is an order `R` of an imaginary quadratic field `k` ("with complex multiplication", "the full geometric endomorphism order of `E`") | L584-586 | `CMCurveOrder` | **GLUE (open, on-the-spot)** |

**Fold.** The CM fold dry run is
`HDec.HSyn.sixContactMin_of_open73_cmfs (r : OpenResearchLeaves54CMFS) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27)`
(`ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean`, generated; compiled, standard axioms). It is cm-branch2's
`sixContactMin_of_open73_cm` with the bundle field `cmFibreSplit` replaced by `cmCurveOrder`. Spec:
`scratch/cm-fibre-split/autofold.json`.

**Net change:** GLUE column 0 against cm-branch2's spec (one GLUE replaced by a strictly smaller one). Leaves are
unchanged: no new leaf. So the target "the CM fold one GLUE lower" is **not** reached. The glue that remains,
`CMCurveOrder`, is an endomorphism-algebra statement about one elliptic curve. A8's field, the case analysis, the
matrix units, the curve and the isogeny are all off the open list.

## 2. What `CMFibreSplit` packs, and the manuscript's own argument

`CMFibreSplit` (ZInQKernel/Contrib/OneProof/CMBranch.lean) says: at a fibre with a CM point (`¬ NoCMAt u`), there
are a number field `L` with `[L:ℚ] ≤ D`, a model `A/L` of the fibre surface (`FibreOver`), an elliptic curve `E/L`
whose geometric endomorphism ring is an order `R` of an imaginary quadratic field `k`, the product `E² = E × E`, and
an `L`-isogeny `E² → A`. The manuscript's text (thm:height, proof, L581-586):

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

**Verdict: correct as written.** The steps:

1. *"Suppose End⁰(A_Q̄) = M₂(k)."* This is the second branch of L563-577. The chain does not formalize the
   manuscript's Hodge-theoretic derivation of the dichotomy (Milne, Part I Thms 2.8-2.9, cited at L564, and the
   centralizer of `J` in `B ⊗ B^op`). It uses Yu's theorem (T27, the existing leaf `QMLattice.YuB6Alg`), which gives
   the same dichotomy. This replacement predates this task; I did not change it. The B branch is excluded at a CM
   fibre by `end_eq_iota_of_B` (copied from the chain's `endEqOFibre_of_hf`) and `central_O`.
2. *"All its elements are defined over L."* **L is large enough.** `G_ℚ` acts on
   `End(W₀,Q̄) = ⊕_{e,e'} Hom(A_e, A_{e'})`, and `L = EK`, with `E` the fixed field of the kernel. An element of
   `G_L` fixes `K`, hence the block `(e₀, e₀)`, which is `End(A_Q̄)` for the given embedding `e₀ : K ⊆ Q̄`. On that
   block it acts by Galois conjugation of endomorphisms, trivially. A `G_L`-invariant `Q̄`-morphism of
   finite-presentation schemes descends to `L` (Galois descent: EGA IV 8.8.2 to a finite level, then fpqc descent).
   So `End(A_L) → End(A_Q̄)` is onto, and so is `End(A_L) ⊗ ℚ → End⁰(A_Q̄)`. VERIFIED in Lean:
   `endBC_surjective_of_homField`, with the descent from the tree (`TwistDescentHFD.hfd`, which uses the proved
   `MorphDescend.exists_descend` and `TwistDescentGD.descend`) and rigidity to make the descended map a
   homomorphism. The bound `[L:ℚ] ≤ F₀·3^{r²} ≤ D` with `r ≤ 16F₀²` is the chain's `a8_field`.
3. *"Multiples of matrix units therefore give an elliptic curve E/L … and an L-isogeny E² → A."* Correct.
   * Pick `n` with `n e_{ij} ∈ End(A_L)` for all four matrix units; `End` is torsion-free.
   * `E = n e₁₁(A)` is an abelian subvariety over `L`, by Cartier's theorem.
   * `(x, y) ↦ x + n e₂₁ y` is an isogeny with quasi-inverse `a ↦ (h(n² a), h(n e₁₂ a))`, where `h : A ↠ E`
     satisfies `i ∘ h = n e₁₁`. Both composites are `[n³]`.
   * `dim E = 1` follows by counting dimensions. The manuscript leaves these details implicit; all are VERIFIED
     in Lean (`matrixUnit_isogeny`).
4. *"with complex multiplication"*, and L585-586, *"the full geometric endomorphism order of E"*. `End⁰(E_Q̄)` is
   the corner `e M₂(k) e ≅ k` of the rank-one idempotent `e = e₁₁`, and `End(E_Q̄)` is an order of `k`. This is
   correct and classical; it is not formalized here (`CMCurveOrder`).

**Labels.**

| formalized step | label | Lean |
|---|---|---|
| A8's Hom field: kernel field, `L = EK`, degree bound, `L` defines every geometric endomorphism (L544-561) | ELLIOT (the manuscript's own argument; the descent of invariant morphisms is not cited there) | `cmHomFieldModel_of`, `endBC_surjective_of_homField` |
| the pasting `(B_L)_Q̄ ≅ B ×_K Q̄` and `A_Q̄ ≅ P.A` | on-the-spot (bookkeeping) | `paste_iso`, R1's naturality + `bc_transport` |
| CM case `End⁰ ≅ M₂(k)` at a fibre with non-integral `𝒪`-centralizer | ELLIOT step through the chain's leaf T27 (Yu) instead of the manuscript's L563-577 (pre-existing replacement) | `end0Matrix_of_noncentral` |
| multiples of matrix units (L583) | ELLIOT | `exists_scaledMatrixUnits` |
| `E`, `E²`, the isogeny, `dim E = 1` (L583-585) | ELLIOT; the explicit quasi-inverse and the dimension count are on-the-spot | `matrixUnit_isogeny` |
| `End(E_{L̄})` an imaginary quadratic order (L584-586) | ELLIOT; open glue, on-the-spot | `CMCurveOrder` |

**On-the-spot proof sketches.**

* `paste_iso`: `(B_L)_Q̄` and `B ×_{K,e₀} Q̄` are both pullbacks of `B → Spec K` along
  `Spec Q̄ → Spec L → Spec K`. Glue the two squares; the comparison isomorphism preserves the identity section, so
  it is a homomorphism by rigidity.
* B-exclusion: if `End⁰(P.A) ≅ B`, then `B → End⁰` is onto by dimension, so `End(P.A)` is an order of `B`
  containing the maximal order `ι(𝒪)`, hence equal to it. A centralizing element is then `ι(a)` with `a` central in
  `𝒪`. Commuting with `i` and `j` forces `a ∈ ℤ`.
* Matrix units: clear the denominators of `e⁻¹(E_{ij})` in `ℚ ⊗ End(A)` by one integer `m`. The relations hold in
  `End(A)` because `End(A) → ℚ ⊗ End(A)` is injective: `[s]` is surjective, hence an epimorphism. Replacing the
  matrix units by `m` times themselves gives the scale `n = m²`.
* Isogeny: write `E` with `i : E ↪ A`, `h : A ↠ E`, `h ≫ i = f₀₀` (image factorization). From `f₀₀² = n f₀₀` we
  get `i ≫ h = [n]`, because `i` is mono and `h` is epi (reduced source, separated target). Put
  `φ = p₁ i + p₂ i f₁₀` and `ψ = (h n², f₀₁ h)`; the matrix-unit relations give `φψ = [n³]` and `ψφ = [n³]`.
  So `φ` is surjective, because `[n³]` is, and finite, because `φ ≫ ψ` is finite and `ψ` is separated.
  `dim E² = dim A = 2` because `φ` is finite and surjective, and `dim E² = 2 dim E`.
* `CMCurveOrder` (open): `g ↦ i g h` embeds `End⁰(E_Ω)` as `e End⁰(A_Ω) e` with `e = (1/n) h i`, idempotent,
  `e ≠ 0, 1`. In `M₂(k)` a rank-one idempotent is conjugate to `e₁₁`, so the corner is `k`. `End(E)` is a finitely
  generated subring containing `ℤ + ℤ n²√d`, hence an order. `End(E_{L̄}) ≅ End(E_Ω)` because `L̄ ≅ Ω` over `L`.

## 4. The remaining glue `CMCurveOrder`

```lean
def CMCurveOrder : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω] (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
    ∀ (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E) (n : ℕ), 0 < n →
      cmp i h = (n : PkgI3.AbVar.End E) →
      ∃ (k : Type) (_ : Field k) (_ : NumberField k) (R : Subring k), IsImagQuadOrder k R ∧ IsCMBy E k R
```

Kind: GLUE, on-the-spot. The manuscript does not cite it; it is classical (Mumford, *Abelian varieties*, §19-§21
on `End⁰` of isogeny factors, UNVERIFIED locator). It is true as stated:
* if `e = (1/n) i h` were `1`, then `E` would be isogenous to `A`, so `dim A = 1`;
* an elliptic curve has `dim_ℚ End⁰ ≤ 4 < 8 = dim_ℚ M₂(k)`, so `dim A = 1` is impossible.

What a Lean proof needs (sizes SPECULATIVE):
1. transport of `End` along an `L`-isomorphism `Ω ≅ L̄` (base change along an isomorphism of fields; about 150 lines,
   pasting as in `paste_iso`);
2. the corner of `M₂(k)` at a rank-one idempotent is `k` (linear algebra over a field; about 150 lines);
3. `ℚ(√d)` = `AdjoinRoot (X² − d)` as a totally complex quadratic number field (instances; about 80 lines);
4. `R ⊆ 𝓞_k` (finite generation, from T6 on `E_{L̄}` with an embedding `L̄ → ℂ`) and finite conductor
   (`ℤ + ℤ n²√d ⊆ R`; about 200 lines).

The tree has the tools: `endBC_injective`, `HomFreeFiniteC`, the image factorization, and cm-branch2's
`end_ringEquiv_baseChange` (T11b) as a model.

## 5. Files

| file | content |
|---|---|
| `ZInQKernel/Contrib/OneProof/CMFibreSplit.lean` | `cmFibreSplit_of_curveOrder` (the deliverable) |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Reduction.lean` | `CMHomFieldModel`, `CMMatrixUnitSplit`, `end_eq_iota_of_B`, `central_O`, `end0Matrix_of_noncentral`, `endEquivOfIso`, `end0EquivOfIso`, `paste_iso`, `endBC_surjective_of_homField`, `cmHomFieldModel_of`, `cmFibreSplit_of` |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Curve.lean` | the `Hom` calculus `cmp`, `cancel_closedImm`, `cancel_surj`, `matrixUnit_isogeny`, `exists_scaledMatrixUnits`, `CMCurveOrder`, `cmMatrixUnitSplit_of` |
| `ZInQKernel/Contrib/OneProof/CMFibreSplit/Fold.lean` | the fold dry run (generated by `scratch/cm-fibre-split/gen/gen_fold.py`): `CMInputsFS`, base `sixContactMin_of_open4_hf_pz_eb_cmfs`, cm-branch2's chain open6..open48 re-typed, `OpenResearchLeaves54CMFS`, `sixContactMin_of_open73_cmfs` |
| `scratch/cm-fibre-split/` | `Split.lean`, `Geom.lean`, `MU.lean` (scratch versions), `Axioms.lean` + `axioms-out.txt`, `Discharges.lean` + `discharges.txt`, `autofold.json`, `gen/`, `log.md` |

## 6. Compile log, axioms, `#discharges`

* `lake build +ZInQKernel.Contrib.OneProof.CMFibreSplit +ZInQKernel.Contrib.OneProof.CMFibreSplit.Fold`: success.
* `#print axioms` (`axioms-out.txt`): `propext, Classical.choice, Quot.sound` for `cmFibreSplit_of_curveOrder`,
  `cmFibreSplit_of`, `cmHomFieldModel_of`, `endBC_surjective_of_homField`, `paste_iso`, `end0Matrix_of_noncentral`,
  `cmMatrixUnitSplit_of`, `matrixUnit_isogeny`, `exists_scaledMatrixUnits`, `sixContactMin_of_open4_hf_pz_eb_cmfs`,
  `sixContactMin_of_open73_cmfs`.
* `#discharges` against Main at this base (`discharges.txt`). Main's top bundle is now `OpenResearchLeaves57`;
  cm-branch2's fold was written against `OpenResearchLeaves53`. The output has 171 `DISCHARGES` lines: 156 are
  projections of copied bundle structures (noise, as in cm-branch2), and 15 are pre-existing reductions. None comes
  from this task. That is expected: `cmFibreSplit` is a field of cm-branch2's fold bundle, not of Main's top.
  Rebasing the CM fold onto `OpenResearchLeaves57` is the cm-fold-rebase task. It should use
  `cmFibreSplit_of_curveOrder` at its open4 generation, as `Fold.lean` does.

## 7. Known issues

1. **Dichotomy source.** The CM case is entered through Yu's theorem (T27, `YuB6Alg`, an existing chain leaf), not
   the manuscript's L563-577 (Milne + Hodge centralizer). This is a pre-existing replacement and is noted, not new.
2. **`CMCurveOrder` is open** (§4). It is classical but has no citation in the manuscript, hence on-the-spot.
3. **Fold base.** The spec and dry run are relative to cm-branch2's fold (`OpenResearchLeaves53` → `54CM`), not
   to Main's current top (`OpenResearchLeaves57`); see §6.
4. No Gross–Zagier or Tian–Yuan–Zhang argument is used. No existing statement or consumer was changed. The new
   Props `CMHomFieldModel`, `CMMatrixUnitSplit`, `CMCurveOrder` are proved, proved and open, respectively.

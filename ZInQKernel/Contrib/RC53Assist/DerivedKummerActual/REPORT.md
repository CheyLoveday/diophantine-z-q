# Actual completion and fixed Kummer reductions

## Result

This contribution is a checked partial continuation of the derived Kummer argument. It supplies the actual completion identifications, genuine finite coefficient/cochain/class reductions, an actual integral Kummer lift of the fixed completed-point presentation, and finite local trace and integral boundary-detection results. It does not supply the integral Weil-cup/trace normalization or the self-dual based comparison and its cohomology-model squares. Consequently it does not construct the final Nakayama contraction or complete Theorem 5.3.

The sole mathematical source file is `Actual.lean`. All declarations lie in `ZInQ.Contrib.RC53Assist.DerivedKummerActual` or its `FiniteTrace`, `IntegralReduction`, and `IntegralKummer` namespaces. `THEOREMS.md` records every theorem's registered type and axiom dependencies. `DECLARATIONS.md` also records the definitions and named instances.

## 1. The genuine completed point module

For an additive point group P, `PointCompletion P` is the actual inverse limit

    AdicCompletion (Ideal.span {(2 : ℤ)}) P.

Its ℤ₂-action is induced by the compatible canonical residue maps ℤ₂ → ℤ/(2^a), not by an unrelated module structure.

For F = K_w and B/F elliptic:

* `etaOne B` identifies M/2M with B(F)/2B(F). It is the quotient evaluation of the actual completion. `etaOne_completePoint` computes it on every rational point.
* `etaZero K w B` identifies M[2] with B(F)[2]. Its inverse is the actual inclusion of rational torsion into the completion, as stated by `etaZero_symm_apply` and `etaZero_torsionToCompletion`.
* `completionQuotientEquiv` and `etaPowerZero` give the corresponding identifications at every 2-power level.
* The required boundedness of rational two-primary torsion is proved from the existing Mattuck lattice or odd-place reduction results, including transport from an integral model. It is not a new printed assumption.
* `actualPointCompletion_finite` proves that the actual completion is a finite ℤ₂-module. `actualLocalPresentation` chooses a finite free presentation of that module, including its torsion relations. The choice is fixed once K, w and B are fixed. No minimality or uniqueness of its bases is asserted.

`actualReductionH0Identification` and `actualReductionH1Identification` insert these specific identifications into the existing derived-reduction algebra. `genuineScalarH0` and `genuineScalarH1` also identify the completion's torsion and quotient with the existing finite scalar Kummer condition.

The existing RC29 maps are reused. `genuineCompletionKummerMap` factors `actualKummerMap` through the actual completion quotient. Its value on completed rational points is unchanged. `actualKummerAt_range_eq_completionSpan` is the existing RC29 span theorem expressed using this fixed factorization. The torsion identification also specializes to the actual local twist. No RC29 source or the separate `genCondDim2_oldKummer` obligation was changed.

## 2. Fixed genuine reductions and actual integral Kummer lifts

`IntegralTateCoeff G A` is the genuine Tate module T₂A with its actual G-action and inverse-limit topology. `FiniteTateCoeff G A a` is its genuine level A[2^a].

`coefficientProjection` is Tate-module evaluation. `reduceCochains` is the induced continuous cochain map. Its differential compatibility and its successive-level compatibility are proved. `actualH1Reduction` and `actualH2Reduction` are the corresponding fixed class maps for the actual geometric point coefficients; the versions `OnHomology` are maps from integral cohomology itself. These maps are defined before any pairing or vanishing assertion.

The separable-closure and algebraic-closure descriptions are connected by the canonical inclusion, the actual Galois-group equivalence, and the actual point/torsion dictionaries. In particular, `hOneToAlg_kummerMap` identifies the local-duality Kummer class with the class of the existing RC29 Kummer cocycle.

For every x in the actual completed point module, `IntegralKummer` fixes a Cauchy sequence of rational representatives p_a and compatible geometric division points Q_a. Successive division points differ, after multiplication by two, by a fixed rational correction. The integral Kummer cochain is assembled from the existing RC29 functions

    kummerFunOf F B (2^a) (divisionFamily_power F B x a).

Thus `integralKummerCochain_projection` is an equality of specific finite cochains. `integralKummerCycle_reduction` identifies their classes with `completionKummerClass`, the genuine Kummer class of the actual quotient evaluation of x.

For the fixed actual local presentation I:

* `actualLocalKummerOne` is a based ℤ₂-linear map into actual integral one-cocycles. Its basis images are the preceding genuine integral Kummer lifts of I.g's basis images.
* `actualLocalKummerZero` is a based ℤ₂-linear degree-zero map. The required relation primitives are proved to exist by compactness of the genuine geometric Tate module and the fixed finite reductions.
* `actualLocalKummerZero_d` proves the differential square d⁰ι⁰ = ι¹I.f.
* `actualLocalReduction` is the fixed finite coefficient/class reduction of this actual degree-one map, transported to the separable-closure coefficients.
* `actualLocalReduction_apply` states exactly that its value at u is the genuine B.kummerMap of the fixed representative of I.g u. `actualLocalReduction_mem_genuine_Kummer` proves its Kummer-image membership at every finite level.

These are maps of the two-term free presentation into actual Galois cochains. No cochain injectivity is asserted. Their differential square is not the `commE` or `commO` square of the self-dual based comparison.

## 3. Finite trace and genuine integral boundary detection

`finiteInvariant F n hn` is the actual finite local invariant H²(F, μ_n) ≃ ℤ/n. It is constructed through the genuine Kummer-to-Brauer map and the existing Brauer invariant. Its rational-circle value is exactly inv_F of the Brauer class.

`finiteCochainTrace F n` is a fixed ℤ/n-linear extension of this invariant to degree-two finite continuous cochains. On cycles it is the actual finite invariant; it kills boundaries; its cycle kernel is precisely the boundaries; and it induces an isomorphism on H². The extension off the cycles is chosen. Compatibility of these extensions between different levels is not claimed.

The actual integral trace target is `actualTraceComplex F`, the continuous cochain complex with genuine Tate-module roots-of-unity coefficients. `actualMuH2Reduction` uses the actual coefficient projection and the actual roots-of-unity dictionary. The coefficient transitions are proved to be the genuine roots-of-unity power maps.

`actualMuH2Reduction_all_zero_iff_boundary` proves for every integral target two-cocycle z:

    (∀ a, actualMuH2Reduction F a z = 0)
      ↔ ∃ b, d¹ b = z.

The proof constructs compatible finite primitives, using genuine first-cohomology transition surjectivity, and lifts them to an integral continuous primitive. It has no local-duality printed premise. Likewise, `actualH1Reduction_all_zero_iff_boundary` proves the analogous boundary criterion for actual integral point-coefficient one-cocycles, by compactness. This latter result supplies the relation primitives of the based Kummer lift.

Neither boundary criterion supplies an integral trace on all degree-two cochains. The required `trv`, `htrv` and `hker` are therefore not claimed to be fully instantiated. The two-cocycle criterion supplies the substantive boundary-detection step that a genuinely normalized integral trace would need.

## 4. Connection to the existing comparison theorem

`actualDerived_modTwo_comparisons_of_print` is the existing two perfect mod-two comparisons instantiated with the actual completion, an actual finite free presentation, `etaZero` and `etaOne`. Its remaining inputs are the existing `MilneLocalDualityPrint`, `MilneFiniteLocalDualityPrint` and the unit proof for two. The unit proof is automatic for K_w in characteristic zero.

The two additive comparisons have their specified local Tate-pairing and torsion-evaluation formulas. To apply `nakayama_comparison_of_modTwo_models`, one must still:

1. construct the actual integral self-dual comparison as `f : ChainMapR C D` between the actual finite based models;
2. construct the two `CohomologyModel` records for their mod-two reductions;
3. express the preceding perfect additive comparisons as the corresponding F₂-linear bijections;
4. prove `commE` and `commO` for this specific reduced chain map.

The existing theorem then gives `Nonempty (Contraction (BasedCx.coneR f))`. No such f, model records, squares or contraction are supplied here.

## Exact remaining arithmetic obligations

The former existential `hred` premise is not supplied: with the printed finite isotropy, that formulation restates integral vanishing. The remaining obligation must instead use the fixed maps above.

* Transport the integral point and roots-of-unity coefficients to a common actual Galois-group description, and construct the genuine integral Tate-Weil bilinear pairing. Prove its projection law to the genuine finite Weil pairings.
* Construct the integral cup cochain map and an integral ℤ₂-linear trace on its genuine degree-two target. Prove normalization on every actual two-cocycle against `finiteInvariant` composed with the fixed `actualMuH2Reduction`, not only on Kummer cup values. Deduce its boundary vanishing and cycle kernel using the proved criterion.
* Prove cup–invariant compatibility for these independently defined maps:

    padicInvariant a (trv (cup (ι¹u) (ι'¹v)))
      = localTatePairing (red_a u) (red_a v).

  The right side uses the fixed genuine Kummer-image reductions already constructed. Only after this equality is proved may printed finite isotropy give integral divisibility and truncated isotropy.
* Finish the actual self-dual based comparison and the model/square obligations listed above. The actual degree-zero reduction map of the Kummer presentation has not been identified with the supplied rational-torsion identification as a cohomology-map square; that naturality is part of the remaining model wiring.

## Sources and verification scope

No new printed leaf is introduced. The existing Milne ADT premises remain the manuscript-cited I Corollary 2.3 and I Corollary 3.4, with the already recorded Kummer adjunction and normalization of I.3.2–I.3.5. All new completion, reduction, division-point, compactness, finite trace-extension and primitive-lifting assertions are proved from the existing library results.

Only new contribution files were written. Existing files were read-only. No repository history or dependency changes were made, and no work was delegated. Verification is the stipulated single-file Lean check and the accompanying complete declaration/axiom audit, against the supplied integration baseline 27579f4a. The code has compiler warnings about proof-local instances, unused arguments, and one deprecated set-membership lemma; these are not proof gaps. Independent review and integration have not been performed.

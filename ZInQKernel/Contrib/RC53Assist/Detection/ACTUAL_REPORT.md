# Genuine arithmetic exports and remaining detection bindings

## Result and scope

The new extension imports the committed detection inputs and the built retained arithmetic assembly. It constructs actual finite tame inertia characters and representatives, actual rational local lifts, character-kernel cutout inversion and compositum closure, and finite-model/cochain exports from the arithmetic stage supplier. It also supplies a retained evaluation and injective first-cohomology map from cochain-retract comparison data, without the unnecessarily strong surjectivity requirement on the finite model's degree-zero map.

The three original bindings are not claimed to be unconditionally completed. The precise gaps are global reciprocity/coefficient-family identification, chosen-field containment in the intended cutouts, and retention of the same integral cochain/model comparison through the limit. No class evaluation or detecting determinant is an arithmetic input.

## 1. Actual tame inertia

`inertiaLog` is a genuine homomorphism on the actual local inertia subgroup, obtained from the Kummer value of a root of a uniformizer. Multiplicativity uses that inertia fixes the prime-to-residue-characteristic roots of unity; it does not assume that every element of the local Galois group fixes those roots.

`exists_local_tame_scalar` uses the proved tame-generator theorem and the existing universal finite character. At precision `i`, and an exponent `d ≥ 2i`, it constructs:

- an actual inertia element of the local absolute Galois group;
- a finite scalar homomorphism on that inertia group with values in the actual finite coefficient ring;
- the normalized value `1 + t_i` at that element.

These are actual local Galois elements, not elements of an abstract cyclic substitute. `rationalAbsoluteLift` and `rationalLocalLift` transport them to the actual rational fixing subgroup. `baseRestriction_rationalLocalLift` proves the exact localization identity.

`scalar_limit_of_finite_normalization` proves that any integral lifts of normalized finite values have limit `1+t`. `nonquadratic_parameter_of_not_mem` and `nonquadratic_limit_of_finite_normalization` discharge nonquadraticity from the coefficient-prime exclusion `t(t+2) ∉ P`, without supplying a nonzero cohomology evaluation.

### The switching tame coordinates are not the coefficient character

The derivative label in `InnerLimitArith` consists of places outside the fixed support. Its localization factors through the unramified quotient. The new theorems `movingLabel_character_on_inertia`, `movingLabel_inertia_scalar_limit`, and `derivative_inertia_cannot_supply_nonquadratic` prove that inertia at these derivative places has scalar character one, and cannot furnish the original `NonquadraticInertiaInput` through that localization.

This is consistent with the actual retained-stage supplier: its derivative local-module action is supplied as trivial in `StageArithmeticInput.trivialAction`. Nontrivial tame cochain coordinates are values of cocycles with trivial coefficient action, not evidence for a nonquadratic coefficient action.

The moving conductor primes `r_i` of the character construction are different from the derivative places `q_i`. Manuscript lines 2728–2741 and 2777–2795 specify finite moving characters on varying ring-class fields and supports. The moving-character API gives a character on `M.P r` and an element of `M.inertia r`; those ring-class groups and inertia identifications remain interface data, even in the genuine Tate/Kummer wiring.

**Exact missing binding:** actual local/global reciprocity must identify the local inertia map with the ring-class inertia used by the moving-character theorem, with the prescribed generator convention. Its composition with the finite moving character must agree with the finite coefficient character used at the same stage. Good-prime Tate unramifiedness must identify the rational lift's action with fixing `torsField E i`. The conjugate finite character must be its inverse under the actual rational conjugation.

Finally, these finite characters on varying coefficient supports must be connected to the coefficient representation consumed by detection. The current original input uses one fixed `α : GKS K S →* Λˣ`; neither the local tame-coordinate API nor `moving_character_Psi` supplies that identification. A stagewise finite-character/coefficient dictionary, including the integral matrix lifts before specialization, is needed unless a genuine comparison to that fixed-support character is proved. Merely renaming the varying finite characters as `α` is not valid.

`no_integral_fixed_tame_normalization` gives an additional checked warning: a `Λˣ`-valued homomorphism satisfying the tame relation at one fixed residue cardinality greater than one cannot send inertia exactly to `1+t`. This does not contradict the finite moving characters; their residue cardinalities and precisions vary. The manuscript explicitly makes no assertion that one fixed odd prime supports an infinitely ramified two-adic character.

## 2. Dihedral character cutouts and composita

`characterCutout H β` is the actual intermediate field fixed by the image in the rational Galois group of the kernel of a character on the quadratic fixing subgroup.

`inversion_on_characterCutout` proves that inversion of that character by actual conjugation implies inversion on the cutout field. The proof constructs an element of the character kernel and uses its actual action on the field. It takes no field-inversion conclusion as input.

`automorphisms_agree_on_sup` proves agreement on a compositum by Mathlib's `fixingSubgroup_sup`. `dihedralKernelFields_of_cutout_bounds` then constructs the original `DihedralKernelFields` from two anti-conjugate abelian characters and the two chosen-field bounds.

The precise field comparison is printed by `le_characterCutout_iff`:

```text
F ≤ characterCutout H β
    ↔ ∀ g : H, β(g) = 1 → ∀ x ∈ F, g(x) = x.
```

Here the abelian character can be the full Artin restriction to the intended ring-class field, not only the possibly nonfaithful finite coefficient character. This allows the intended ring-class and quadratic composita to be used.

**Exact missing binding:** construct the actual Artin/ring-class restriction maps and prove that the chosen `characterField i` and arithmetic `B i` lie in their cutout fields. The generic chosen character-field theorem supplies the other implication: fixing its field makes the stage coefficient character trivial. It supplies no containment in the intended ring-class cutout, and no minimal-kernel identity.

Finite-dimensionality and normality alone do not fill that gap. `image_commutative_of_conjugate_inversion` proves that a conjugation acting by inversion forces the restriction image to be abelian. Thus arbitrary normal fields with nonabelian restriction image cannot silently be substituted. No finiteness or Galois claim for an arbitrary abstract character cutout is made without the requisite continuous finite-image arithmetic binding.

Sources: manuscript (H1), lines 2882–2892; the common-kernel scalar argument, lines 4766–4774; finite character inversion, lines 2777–2795.

## 3. Actual arithmetic models and retained cochain comparison

`actual_stage_model_exports` is instantiated with the actual `ActualStageFamily` and `ArithmeticInputs` used by `assemble_inner_limit`. It uses the same produced pairing and trace, the actual flatness theorem, and the supplied actual residual/rank comparison to construct at each positive stage:

- a `GradedModel` of the actual arithmetic global complex;
- its original inclusion, projection, and homotopy, through `model.retract`;
- the matrix diagram computed from that model;
- the exact differential, localization, global-pairing, and local-pairing ties;
- the actual residual-rank identities.

`boundary_reflection_of_retract` proves boundary reflection using the cochain projection. `model_inclusion_injective` proves injectivity of every model inclusion from its left inverse.

These strengthen the stage export instead of discarding the original maps. They are not claimed to recover the hidden models belonging to an arbitrary previously chosen `AssembledLimit`: its result retains ranks, matrices, pairing, duality, and local lifts, but not their original cochain-model lineage.

### The sufficient comparison should not require model degree-zero surjectivity

The older `RetainedCochainEmbedding` requires a surjective map from the finite model's degree zero to the rank-four induced coefficient module. `embedding_requires_degree_zero_dimension` proves that this forces degree-zero dimension at least four. `no_embedding_of_small_degree_zero` proves the corresponding obstruction. No assertion is made that a particular assembled model has rank below four; the point is that a cochain retract or H¹ comparison does not itself provide the extra surjectivity.

`RetainedTargetComparison` instead keeps the target cochain complex, its evaluation maps in degrees zero through two, and the actual cochain retract. Surjectivity is imposed on the target's degree-zero evaluation, not on the finite model. `principal_boundary_from_target` reflects principal cocycles through the projection. `retainedEvaluation_from_target` constructs the existing retained evaluation record, and `h1_map_from_retained_target` constructs a well-defined injective map on ordinary first cohomology with the exact represented-cycle formula. Degree-zero boundary preservation is explicitly proved.

If the stronger model degree-zero surjectivity is separately established, `embedding_from_target` constructs the literal older `RetainedCochainEmbedding` as well. It is not inferred from the retract.

**Exact missing binding:** retain the same model, its original basis/cochain maps, and the matrix transport used in forming the assembled integral limit. Identify the retained target evaluation maps and their degree-zero and degree-one differential identities, and compare original integral basis columns with normalized evaluations after specialization. The comparison must preserve the applicable original Selmer/global H¹ injection or contracted cone comparison. The target data must concern this actual retained model and coefficient system, not an unrelated model with the same ranks.

Finite stage rings do not map to a characteristic-zero fibre away from two: `CoefModules.isEmpty_ringHom_acoef_resAt` already proves this in the imported tree. Consequently stage retractions cannot simply be specialized one by one. Their integral retained maps and identities must be formed before specialization.

Sources: manuscript lines 4391–4451 and 4651–4704; the extra contraction for orthogonal zero/full models, lines 4706–4717. The actual assembly used here is `RetainedAssembly.assemble_inner_limit`; its model-erasing call to the stage supplier is explicit in its proof.

## Detection scope

The new declarations contain no determinant assumption. They provide genuine local/field/model constructions and exact binding criteria for the existing prescribed-cycle producer. Until the three bindings above are proved for the actual coefficient family and retained complex, they do not constitute an unconditional detection theorem or an unconditional completion of Theorem 5.3.

Kernel representatives still mean finite-precision fixing with exact limiting coefficient action. Fixed-decomposition normalization still applies to fibre cycles with one common invertible conjugation transport, not arbitrary untransported cochains.

## Verification

`ActualInputs.lean` and its scratch declaration audit both compile with exit code zero using six threads, processor affinity 80–95, and priority ten. The source has 35,055 bytes and SHA-256 `b576b778b4de740f9f2cadb29650b5fee0c30a8e1313f327d1ab607dc00ab7a5`.

The extension has 29 theorems, 38 named declarations, and 18 record fields. All 56 exact statement/axiom receipts are present, with no missing or extra entries and no errors. Every recorded axiom set is contained in `{propext, Classical.choice, Quot.sound}`. The actual local tame construction, derivative-inertia obstruction, dihedral-cutout constructor, actual arithmetic model export, retained-target evaluation, and injective H¹ map each use exactly those three standard axioms.

No existing source file, committed input, or earlier proof edition was edited. No version-control command, package update, whole-project build, subagent, human outreach, or memory write was used. Temporary diagnostics are removed from the delivered module set. The final source contains no placeholder, additional axiom, diagnostic/executable command, or new notation/syntax declaration.

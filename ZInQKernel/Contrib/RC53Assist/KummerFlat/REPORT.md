# Flatness of finite Kummer terms

## Outcome

The unrestricted Kummer extension construction has nonflat degree-one terms even when the coefficient module and all ambient continuous cochain modules are free. The supplied field `hcflatK` has not been discharged. The contribution contains a closed local counterexample to the actual `kummerConditionIn` construction, an obstruction for the exact `MinS` stage modules, and a model-based interface for its matrix-diagram consumer.

The closed local example is not a complete global number-field instantiation of `ILStageStepActualB`. The exact-stage results state their independent arithmetic premises explicitly. Nothing here refutes flatness for the canonical torsion inclusion used by the intended derived Kummer condition.

## Exact target

In `ZInQKernel/Contrib/OneProof/RC/Wiring/InnerLimitRegularityBounds.lean`, the field is:

```lean
hcflatK : ∀ i [NeZero i] (v : Places K Ssel) (h : v.1 ∈ S₀) (n : ℤ), label i v ≠ 0 →
  label i v ≠ 1 → Module.Flat (Acoef i)
    (((stdOldConditions hS W α Bv label m ιK hιK) i v h).U.X n)
```

Its Kummer branch is literally `kummerConditionIn (Acoef i) (ιK i v) (hιK i v)`. The interface constrains the coefficient maps by equivariance, but does not require the canonical torsion inclusion, injectivity, or an identification with derived coefficient extension. A zero coefficient map is allowed.

## The degree-one term

The construction in `RC/CoefModules/CocycleCondition.lean` is

- degree zero: all continuous zero-cochains;
- degree one: `kummerZ' ⊔ contB1`;
- all other degrees: zero.

The degree-one object is an actual submodule of continuous cochains. It is not a free module on formal generators. For a zero coefficient map, the extended Kummer span is zero, so the term is precisely the coboundary module.

The manuscript distinguishes the actual derived Kummer condition and derived coefficient extension at tex 3413–3438. Its flat continuous-cochain argument at tex 4409–4414 applies to the ambient cochain modules; it does not by itself establish flatness of this submodule.

## Closed local counterexample

`dyadicZeroKummerCondition` uses:

- `A₂ = (ℤ/4)[t]/(t²)`;
- the local field `ℚ₂`;
- the elliptic curve `y² = x³ - x` over `ℚ₂`;
- the genuine quadratic Galois character of `ℚ₂(√2)/ℚ₂`;
- a free rank-two coefficient module on which this character acts by scalar signs;
- torsion level four and the zero equivariant torsion coefficient map.

`dyadicAmbientCochains_free` proves freeness of every ambient continuous cochain module using the finite-partition method of `InnerLimitArith/StageFlat.lean`.

`dyadicZeroKummerCondition_not_flat` has no hypotheses. Its degree-one term is nonzero and killed by two. Two is nonzero in `A₂`. If the term were flat, the nilpotent-local-ring freeness theorem would make it free, and a nonzero free module is faithful. This contradicts its annihilation by two.

`dyadicZeroKummerCondition_flat_off_one` proves flatness in every other degree. Thus the obstruction is confined to the literal degree-one term.

## Exact stage-module results

`standardOldAt_flat_off_one` and `stdOldConditions_flat_off_one` prove flatness outside degree one for the actual `MinS` modules, using only the existing full-torsion input and the standard condition data.

`hcflatK_refuted_at_two` negates the exact complete quantifier order of the field when one old place at stage two has a zero coefficient map and a nontrivial local sign action.

`standardOldAt_split_quadratic_not_flat` derives that obstruction for the actual `MinS` tensor construction from:

1. the existing full four-torsion input;
2. split four-torsion, expressed as trivial action on the actual torsion representation;
3. a quadratic character with open kernel whose local restriction takes the value minus one;
4. a zero Kummer coefficient map and a Kummer label.

It does not assume flatness, nonflatness, or an action identity on `MinS`. `minS_quadratic_action` proves the action identity through the actual localization and inflation maps. This is a counterexample family for the exact stage terms, not an invented substitute module.

## Corrected requirement for the consumer

The stage producer only uses termwise flatness to construct a bounded graded finite free model. The weaker sufficient interface is a bounded `GradedModel` of the relevant stage complex, with its actual inclusion, projection, contraction homotopy, localization, trace pairings, and duality data. For a fixed support its model ranks must satisfy the retained uniform bound and the required residual-rank identification.

`exists_stage_diagram_of_gradedModel` proves that this model and the actual global duality input produce the stage matrix diagram, preserving its model differential, localization, global trace pairing, and local trace pairing. Its statement has no termwise-flatness premise. It does not assume the desired matrix diagram as input.

The final switch consumer `ILStageStep.toStepData` uses the already-retained `C`, `D`, `E`, the residue identity, detection, and side identifications. It does not use the stage flatness field. Flatness matters to the producer of the retained realization, rather than to that final conversion.

For the intended arithmetic route, the repair must use an independently constructed flat or projective presentation of the actual derived Kummer condition and transport the actual diagrams. Finite cohomology alone is not a replacement. Mere stagewise quasi-isomorphisms without the retained maps and homotopies are also insufficient, as tex 4449–4450 explicitly states.

## Verification

`Counterexample.lean` compiled as a single file without warnings or errors. A standalone copy followed by `#check` and `#print axioms` commands compiled without diagnostics and audited all 47 declarations, including all 28 theorems.

The axiom union is exactly `{propext, Classical.choice, Quot.sound}`. Every declaration uses a subset of this set. `THEOREMS.md` contains each authored theorem signature, its full compiler-displayed type, and its verbatim axiom output. `AXIOM_AUDIT.txt` is the unedited successful audit output.

The checks used six threads, CPU affinity 48–63, and priority ten. Only single-file `lake env lean` checks were run. Existing sources were not edited; no commit, checkout, repository build, package update, or executable build was performed.

The production source contains no proof placeholders, newly declared axioms, kernel-check bypasses, new notation or syntax, or build-time execution commands. Every declaration has its kind and manuscript locator. Its heartbeat limit is 400000.

## What remains

- Flatness in degree one for the canonical actual Kummer coefficient maps has not been proved or refuted here.
- The bounded free presentations of the actual derived local conditions, their coefficient-change comparisons, and their retained diagram compatibility still need construction before the model-based interface can replace the current input.
- A particular global number-field tuple satisfying the split-torsion and nontrivial local-character premises of the exact-stage counterexample family has not been formalized here, nor has a complete tuple of the other `ILStageStepActualB` fields.
- No existing interface was changed, no claim was marked discharged, and no part of Theorem 5.3 was represented as complete.

# Cohomological switching interface: verification

All source paths below are relative to
`ZInQKernel/Contrib/RC53Assist/SwitchInterface/`.
The integration base is `3b0ffbb9c83eaccb0f82808d806a4939205665b1`.
No existing source, dependency pin or version-control history was changed.

## Result

The literal side-to-family equalities are forwarded and then discarded by
the original descent consumer. The original side-to-stage first-cohomology
equivalences, the family models, and the specified successor therefore
suffice. The weakened inner-limit inputs preserve all other fields.

The regularity proof uses the unchanged
`QuasiNonquadStep.toNonquadDims` and `regular_of_switchData`. No regularity
conclusion, terminal-stage choice or dimension-drop conclusion is added
as an input. See [Consumers.md](Consumers.md) for the field-by-field audit.

## Exact interface

In namespace `ZInQ.Contrib.RC53Assist.SwitchInterface`, with `P` prime,
`F` a field, `Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)`,
`ι : Localization.AtPrime P →+* F` and `u : F`:

```lean
structure InnerLimitSwitchInputsIso
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F)
    extends NonquadSwitchFrame Φ ι (resAt P) u where
  step : ∀ c, Reach Φ.next Φ.actual c →
    1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime,
      Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      Nonempty (InnerLimitStepData P (stage c) (stage (Φ.next c p)))
```

`NonquadSwitchFrame` retains the original `stage`, `model`, `hz0`, `hw0`,
`hu0`, `hnq` and `primitive` fields. Its `finiteH1Equiv` and
`singularH1Equiv` construct side-to-family linear equivalences through the
common stages. Its `successorH1Equiv` composes consecutive side-to-stage
equivalences. These are proved constructions, not additional inputs.

The sufficiency statement is:

```lean
theorem regular_of_innerLimitSwitchInputsIso
    (hι : Function.Injective ι)
    (X : InnerLimitSwitchInputsIso P Φ ι u) : ∃ a, ι a = u
```

The arithmetic adapters are:

```lean
def RemainingInputsIso.toInnerLimitSwitchInputsIso
    (X : RemainingInputsIso (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchInputsIso P X.atlas.family ι u
```

and, in namespace `ZInQ.Contrib.RC53Assist.SwitchWiring`:

```lean
def RemainingInputs.toInnerLimitSwitchInputsIso
    (X : RemainingInputs (E := E) αStage Cn e χ P ι u) :
    InnerLimitSwitchInputsIso P X.atlas.family ι u
```

Both have proved regularity consumers. The new `RemainingInputsIso` retains
original arithmetic requests, detecting labels, integral side models and
coordinate steps, but omits `finiteColumns`, `singularColumns`,
`finiteKind` and `singularKind` from each reachable switch request.
The unchanged `StepRemainingInputs.toStepData` constructs each step.

## Exact non-vacuity statement

The rational model has three configurations with dimensions five, three
and one. Its switches are constructed from actual Selmer cone data, shared
strict cohomology, exact sequences, proved detection and local duality.

```lean
theorem model_nonvacuity :
    Nonempty (NonquadSwitchInputsIso modelFamily
      (RingHom.id ℚ) (RingHom.id ℚ) 1) ∧
    Module.finrank ℚ
      ((selCx (modelFamily.fibre modelFamily.actual)).toCC.homology 1) = 5 ∧
    (modelInputs.stage (1 : Fin 3)).fiberDim (RingHom.id ℚ) = 3 ∧
    Nonempty ((selCx modelStep01.SS.Dside).toCC.homology 1 ≃ₗ[ℚ]
      (selCx modelStep12.SF.Dside).toCC.homology 1) ∧
    modelStep01.SS.Dside ≠ modelStep12.SF.Dside
```

In particular the first singular successor is nonterminal. Consecutive
sides have isomorphic first cohomology but unequal Selmer data, with
provably different local inclusion images. `model_regular` exercises the
unchanged descent through both switches.

For the retained interface, `no_literal_of_large_iso` also proves:

```lean
theorem no_literal_of_large_iso
    (X : InnerLimitSwitchInputsIso P Φ ι u)
    (hlarge : 3 < (X.stage Φ.actual).fiberDim (resAt P)) :
    ¬ Nonempty (InnerLimitSwitchInputs P Φ ι u)
```

## Verification

- All four final Lean sources were compiled individually with Lean 4.35.0,
  six threads, CPU affinity 112–127 and niceness 10.
- All four final compiler logs are empty: no errors or warnings.
- [Scratch/Axioms.lean](Scratch/Axioms.lean) was compiled successfully.
  All 23 axiom audits returned exactly
  `[propext, Classical.choice, Quot.sound]`.
- The exact structure, theorem and adapter types, and the raw axiom reports,
  are in [Scratch/axioms.txt](Scratch/axioms.txt).
- The source audit found no forbidden proof escapes or new declaration
  mechanisms, no prohibited private identifiers in public text, and no
  heartbeat setting above 800000. All 68 explicitly declared source objects have kind and TeX
  locator docstrings.
- The four protected source files and three dependency/configuration files
  checked against the initial hashes are unchanged.
- No repository build, dependency update, executable build, checkout or
  version-control command was run.

The supplied dependency objects did not include
`SwitchWiring/Assembly.olean` or `SwitchWiring/Boundary.olean`. Their sources
were checked read-only, writing the objects only under the new
`SwitchInterface/.objects/` directory. The final checks used that separate
object overlay and the existing dependency objects. Nothing was written
into the original compiled-object directories.

A final compilation can be repeated, from the repository root, using:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 \
  taskset -c 112-127 nice -n 10 lake env sh -c '
    LEAN_PATH="$PWD/ZInQKernel/Contrib/RC53Assist/SwitchInterface/.objects:$LEAN_PATH" \
      lean ZInQKernel/Contrib/RC53Assist/SwitchInterface/NonVacuity.lean
  '
```

Preliminary checks found missing dependency objects and elaboration issues
in rank simplification and explicit configuration/type annotations.
Those issues were resolved before the final checks and hashes below.

## Source hashes and sizes

- `Interface.lean`: 10,220 bytes;
  SHA-256 `94a65f4223e9620991c225a44029493462ea0e744d35148da482a84925db73ab`.
- `Model.lean`: 14,983 bytes;
  SHA-256 `c2c8b57c1c4772f55bc6fde0285cbd5987501c51b7735d09ae13ac2ee19044f2`.
- `NonVacuity.lean`: 17,587 bytes;
  SHA-256 `b7a988d78a5f6089da3bce4e9a51872e861486927c30bc29ce440bd21e97c24a`.
- `Assembly.lean`: 9,397 bytes;
  SHA-256 `f6c294e328c8ba04d56a2b5a123db5cb39accfd898e851c720abdc41eb3c37e1`.
- `Consumers.md`: 4,284 bytes;
  SHA-256 `c0da39205192fe64f6346e9dc912db57ab2f96e89ebee134b3e0dc45fdab147e`.
- `Scratch/Axioms.lean`: 2,843 bytes;
  SHA-256 `fabd12db17173a8cce4bad2408247973e2977da5b4fee79628d0a96334e6b096`.
- `Scratch/axioms.txt`: 13,853 bytes;
  SHA-256 `de2fd1d04caabbe6cab92be336aeb30413f636bdd1390cccfa81fcdef48b588f`.

## Remaining mathematical inputs

The original `SwitchWiring.RemainingInputs` remains subject to its literal
terminal-successor obstruction; its compatibility map does not make that
old structure inhabited above dimension three. The repaired arithmetic
route uses `RemainingInputsIso`.

An actual number-field realization of the new remaining arithmetic and
cochain-model inputs is not constructed here. Non-vacuity is proved at the
explicit model level, not for retained arithmetic requests. No existing
outer leaf or global theorem assembly was edited or integrated. This is an
interface repair and a conditional regularity theorem, not a completion of
Theorem 5.3.

Sources: tex L4391–4451, L4976–5003, L5027–5086, L5137–5195.

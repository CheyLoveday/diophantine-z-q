# c-to-printed2: summary

**Verdict.** Of the three GLUE (c) fields, two now follow from their printed theorems with no project glue left:
- `eigenformHTNew` follows from one leaf at Kato's realization plus two existing bundle LEAF fields;
- `r17` follows from one leaf at Carayol's realization.

Each field is also *equivalent* to its realization leaf, modulo existing bundle leaves. So the existential substitute for
the object Mathlib cannot define (Kato's `V_{F_λ}(f)`, Carayol's `σ_λ(π_f)`) loses nothing relative to the field.

The third field, `t09SymmIsogenyExists`, is unchanged and stays GLUE (c). Its printed statements are about `Pic⁰`,
`φ_L` and Mumford's `e_n`, which are not definable today. The field is already the smallest faithful existential
substitute.

No statement was changed, and none is false, vacuous or inert. One independent model review found no mathematical
error. Every locator and printed wording is UNVERIFIED, since
there was no network.

**What compiles** (`scratch/c-to-printed2/CToPrinted2.lean`, imports `TailZ15`): 0 errors, and all 10
`#print axioms` lines are `[propext, Classical.choice, Quot.sound]`.
- `htDual_proof : TateTwistInvariants → AxSenTate → HTDual`. This closes modular-split's open glue, with a new
  ~300-line proof by a dual-basis argument in hodge-split's `Ysp` coordinates (Tate and Ax–Sen–Tate). It is also in
  `HTDual.lean`, on `TailT` alone.
- `dualGR_isSemisimple`: the contragredient of a semisimple representation is semisimple.
- `eigenformHTNew_of_printedSS : KatoRealizationCohSS → TateTwistInvariants → AxSenTate → EigenformHTNew`.
  `KatoRealizationCohSS` is Kato's normalization (geometric Frobenius, weights `{0, k−1}`) with a semisimple witness.
  `KatoRealization` (Tate normalization) needs nothing else.
- Equivalences over the bundle LEAFs `dsThm965`, `dsThm966` (and `Tate` for the cohomological form):
  `katoRealization_iff_field`, `katoRealizationCohSS_iff_field`, `R17.carayolRealization_iff_field`.
- `R17.carayolR17'_of_realization` (modular-split, re-checked) and `fields_of_printed` (both fields from the two
  leaves and `OpenAddedLeaves9`).
- §0 copies the three fields verbatim, each `rfl` against the bundle constants.
- `T09Roadmap.lean` checks that Grothendieck's Picard representability is statable over the vendored `picardFunctor`.

**What remains.**
- Both realization leaves stay (c) in the strict count, because the printed objects need étale cohomology,
  automorphic representations and local Langlands.
- t09 needs, in order: `Pic⁰` as an abelian variety (identity component), `φ_L` via translations, ample line
  bundles, and Mumford's `e_n`.
- Kato's and Carayol's normalizations are unread, but the reduction covers both Frobenius normalizations for Kato.
  For Carayol, it relies on the audit's statement that duals and unramified twists leave the conductor unchanged.
- Fold recipe: report §6. Report: `docs/research/c-to-printed2.md`. Results log: `scratch/c-to-printed2/log.md`.

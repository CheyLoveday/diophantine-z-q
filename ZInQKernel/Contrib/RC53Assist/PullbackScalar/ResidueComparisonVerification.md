# Rational residue comparison and rational isogeny scalars

## Result

The generic rational residue comparison is proved, and both
`PullbackCoefficientConstantGlue` and `IsogenyScalarRationalGlue` are proved
**unconditionally**. There is no remaining mathematical input for these three targets.
No literature statement is installed as a formal hypothesis.

The exported namespace is
`ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison`:

```lean
theorem rationalResidueComparisonFact : ResidueComparisonFact

theorem pullbackCoefficientConstantGlue_proof :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.PullbackCoefficientConstantGlue

theorem isogenyScalarRationalGlue_proof :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.IsogenyScalarRationalGlue
```

`ResidueComparisonFact` is definitionally the unchanged
`ZInQ.Contrib.RC53Assist.PullbackScalar.RationalResidueComparisonFact` from
`PullbackScalar/Reduction.lean`. The exact contract audit copied the five interface
definitions **verbatim** from that file, without changing the existing file, and checked:

```lean
theorem residueComparisonFact_type_eq :
    ResidueComparison.ResidueComparisonFact = RationalResidueComparisonFact := rfl

theorem rationalResidueComparisonFact_proof : RationalResidueComparisonFact :=
  ResidueComparison.rationalResidueComparisonFact
```

Both checks passed. The separate, definitionally identical interface keeps the new proof
file individually compilable without producing a build artifact for the committed
reduction, whose importable object file was absent. Importing the reduction and this
proof in a normal integration supplies the same definitional conversion.

This contribution is a proof of the three named targets, **not** a claim that all of
Theorem 5.3 or the project is complete. Independent review and integration remain.
No commits, checkouts, dependency updates, package builds, memory writes, or outreach
were performed. No pre-existing source or first-edition contribution file was changed.

## What was proved

1. **A canonical comparison.** For every one-variable function field with exact constant
   field `ℚ`, choose a separating parameter and send its Kähler differential to the Weil
   cotrace of the normalized rational-function differential. The chain rule for Weil
   differentials proves independence of the parameter, so the resulting equivalence is
   function-field-linear and intrinsic.
2. **Finite-separable naturality.** The image of a separating parameter gives compatible
   rational-function actions in a tower. Transitivity of cotrace, semilinearity, and
   parameter independence show that the actual Kähler pullback is carried to the existing
   finite-separable Weil cotrace, for every differential.
3. **Local integral vanishing.** If `f` is constant, `df = 0`. Otherwise `f` is separating
   in characteristic zero. Its normalized Weil differential has divisor
   `-2 (f)∞ + Diff(K/ℚ(f))`. At a place where `f` is integral the pole contribution is
   zero and the different exponent is nonnegative. The local-order characterization
   therefore gives `Res_P(g df) = 0` for every integral `g`. This includes places of
   arbitrary residue degree, not only rational places.
4. **The rational scalar.** The invariant differential has divisor zero under the canonical
   comparison. Cotrace along a rational isogeny preserves regularity, since its different
   is zero. A function multiplying a nonzero regular differential to another regular
   differential in genus one has trivial divisor and belongs to the exact constant field
   `ℚ`. The existing separability and uniqueness results give the nonzero rational
   pullback scalar in the exact algebraic glue formulation.

The normalized separating-parameter construction is the same construction used in
`RC53Assist/InvariantDifferential/DivisorZero.lean`. The missing parameter-independence
and residue proofs, together with their needed infrastructure, were reused from the
public source at the vendored revision rather than supplied as assumptions.

## Proof source and dependencies

The only final Lean file is:

`ZInQKernel/Contrib/RC53Assist/PullbackScalar/ResidueComparisonProof.lean`

- Size: **694,503 bytes**, **12,729 lines**.
- SHA256: `03374bdaac5d9deac7b4751c35b57ec8b8fa9ecd30fc36c598a0c8e90ae1a574`.
- It contains a single-file port of the needed **52** unbuilt public library modules,
  followed by the rational comparison and scalar consequences.
- The proof port has **490** explicit declarations; the final consequence section has
  **24** named declarations, of which **16** are theorems. There are **443** explicitly
  written theorems in the complete file, including private proof helpers.
- The imported, already compiled statements are reused. The file does not import all of
  Mathlib and adds no dependency pin or build-time extension.
- All **520** documentation blocks classify their declaration or field and include a
  source locator. The source restrictions and mathematical-public-text checks passed.
- The proof heartbeat limit is **800,000**; the typeclass heartbeat limit is **200,000**.
  Automatic implicit parameter insertion is disabled.

The reused proof source is the public Tau Ceti repository at revision `5a01f5fe3621`,
Apache-2.0. Copyright and attribution notices are preserved in the Lean source, and each
module section records its original source digest. `ResidueUpstreamSources.json`
preserves the original source texts and revision for reproduction.

Principal reused modules include:

- `FieldTheory/FunctionField/Differential/{Comparison,Independence,Residue,TraceResidue}.lean`;
- the rational-function differential, local nonvanishing, constant-extension, and
  Laurent-expansion proofs needed by the chain rule;
- `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean`.

The upstream Mathlib revision was `ccbef15ebdb41c2addfac682131f83c75904c3c1`.
The actual proof was checked against this repository's existing pin,
`56a005855ea17e0b0958f73ec801ae140b0a1679`, on Lean **4.35.0**.
The toolchain and manifest were not changed.

Compatibility adaptations are limited to:

- combining module boundaries in dependency order and reusing existing compiled imports;
- classifying documentation and preserving the original module/source locators;
- spelling the **vendored** divisor namespace explicitly as
  `TauCeti.AlgebraicGeometry.WeilDivisor`, and resolving local-ring and intermediate-field
  namespace ambiguity;
- using `Finset.HasAntidiagonal.mem_antidiagonal` for the current natural-number
  antidiagonal API and the implicit-map form of `Polynomial.IsRoot.map`;
- renaming the unbuilt monogenic lemma to
  `TauCeti.residueComparison_differentIdeal_eq_span_aeval_derivative_minpoly`, to avoid
  duplicating the declaration of a pre-existing source;
- using the canonical rational-function algebra explicitly when comparing tower maps
  over `ℚ`, and proving both scalar rewrites in the cotrace calculation.

There was no weakening of a library theorem, addition of a conclusion as an input,
or substitution of a literature assertion for a proof.

## Compilation and axiom evidence

From the repository root, with the prescribed toolchain on `PATH`, the final source was
checked with:

```sh
LEAN_NUM_THREADS=6 taskset -c 128-143 nice -n 10 lake env lean \
  ZInQKernel/Contrib/RC53Assist/PullbackScalar/ResidueComparisonProof.lean
```

Result: **exit 0, no errors, two linter warnings**. The warnings concern an implicitly
used parameter name and finite-dimensionality/separability assumptions that are included
in the section of a semilinearity helper but unnecessary for that helper. They are
preserved in `ResidueComparisonProofCompile2.txt`; no linter was disabled to hide them.

The exact-interface audit used a scratch copy whose proof-source prefix was verified
byte-identical to the final source at the digest above. It checked each explicitly
written theorem and printed its axioms, then checked the two unchanged-interface
conversions and enumerated public declaration types.

Result: **exit 0, 445 individual reports, no nonstandard axioms**. Every one of the
443 theorem reports and the two exact-interface reports is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

A second audit enumerated the **463 newly added public declarations**, including
attribute-generated declarations, against the imported baseline and printed the axioms
of every one. Result: **exit 0, 463 individual reports, no nonstandard axioms**.
Thus generated public theorems and non-theorem definitions are covered as well as the
explicit and private proof declarations.

The evidence files are:

- `ResidueComparisonStatements.md`: exact compiler types and individual axiom results
  for all 443 explicit theorems and both exact-interface checks;
- `ResidueNewPublicTypes.txt`: exact types of all 463 newly added public declarations;
- `ResiduePublicAxioms.txt`: the individual public-declaration axiom audit;
- `ResidueComparisonAuditOutput.txt`: unedited successful scratch output, including
  the exact contract checks and declaration enumeration;
- `ResidueComparisonTypeIndex.json`: machine-readable theorem/type/axiom index;
- `ResidueComparisonProofCompile2.txt`: the final direct compilation output;
- `ResidueCompilationHistory.txt`: preserved unsuccessful compatibility attempts and
  their source digests, followed by the successful direct checks.

The committed first-edition source `PullbackScalar/Reduction.lean` remains at SHA256
`5c9c4a2b486fca465a4b231a8288c17fb2c8dafaee74061940a59bb9e6757a15`.
All scratch Lean copies and exploratory Lean files were removed after their evidence
was captured. Only the final new proof source is a Lean deliverable for this continuation.

## Literature status

No printed theorem is a remaining input. The conventional mathematical locators are
Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 4.3.2 and
Remark 4.3.7 for the comparison, chain rule, and residue description; Silverman,
*The Arithmetic of Elliptic Curves*, second edition, II.4 and III.5 for the differential
and isogeny conventions, and Proposition III.1.5 for the invariant-divisor calculation.
These are locators for **proved library results**, not assumed statements.

The current manuscript source names Silverman, but contains no Stichtenoth bibliography
entry. No new manuscript citation is needed to accept an unproved input here, because
there is no such input. This report certifies the proof reuse and kernel checks, not a
fresh page-level reading of either book.

# Finite-level Kummer sequence and passage to the two-power limit

## Result

The literal finite-level statement is defined as `SilvermanX42TwoPowerLevelPrint`.
The exact implication

```lean
theorem kummerSequenceTwoPowerPrint_of_levels :
    SilvermanX42TwoPowerLevelPrint → KummerSequenceTwoPowerPrint
```

is proved. Both clauses of the existing target are retained, with no additional
hypotheses. The finite statement is also proved from the coefficient Kummer
sequence and the long exact sequence of continuous cohomology. Consequently,
`kummerSequenceTwoPowerPrint : KummerSequenceTwoPowerPrint` is supplied as well.

All three names are in `ZInQ.Contrib.RC53Assist.DiskOrders`.

## Literal finite-level PRINT

Source locator: J. H. Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Theorem X.4.2. For an isogeny `φ : E → E'`, its exact sequence is

```text
0 → E'(K)/φ(E(K)) → S^(φ)(E/K) → Ш(E/K)[φ] → 0.
```

The specialization used here is `φ = [2^n]`, `E' = E`, and `K = ℚ(√k)`, at every
natural level `n`, including the identity-isogeny level `n = 0`.

**Page locator UNVERIFIED:** the printed page was not available for checking;
no page number is asserted.

The exact Lean definition is:

```lean
def SilvermanX42TwoPowerLevelPrint : Prop :=
  ∀ (k : ℤ) (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
    letI := hE
    ∀ n : ℕ,
      Function.Injective (Limit.levelKummer (sqrtK k) E n) ∧
      Function.Exact (Limit.levelKummer (sqrtK k) E n)
        (Limit.levelToSha (sqrtK k) E n) ∧
      Function.Surjective (Limit.levelToSha (sqrtK k) E n)
```

The groups and maps are fixed, not existential input data:

- `Limit.pointsK r E = H0 (galK r) E.PointCoeff` is `E(K)` realized as fixed geometric
  points. The existing fixing-subgroup identification pins `galK (sqrtK k)` to
  the specified field `QuadraticField k = ℚ(√k)` inside the separable closure.
- The left term is `pointsK r E / (2^n pointsK r E)`.
- The middle term is the preimage of the genuine `shaK r E` under the finite
  coefficient inclusion on `H1 (galK r) (E.TorsionCoeff (2^n))`.
- The right term is `AddSubgroup.torsionBy (shaK r E) (2^n : ℕ)`.
- `levelKummer` is the connecting map of the restricted coefficient Kummer
  sequence, factored through the rational-point quotient and restricted to Selmer.
- `levelToSha` is the finite coefficient inclusion, restricted to those groups.

No infinite-level exactness or divisibility assertion is contained in this PRINT.

## Exact target retained

The unchanged target is:

```lean
def KummerSequenceTwoPowerPrint : Prop :=
  ∀ (k : ℤ) (E : WeierstrassCurve ℚ), E.IsElliptic →
    (∀ x : shaK (sqrtK k) E,
      x ∈ AddCommGroup.primaryComponent (shaK (sqrtK k) E) 2 ↔
      ∃ y ∈ selmerK (sqrtK k) E, inclK (sqrtK k) E y = x) ∧
    (∀ y, inclK (sqrtK k) E y = 0 → ∀ n : ℕ, n ≠ 0 →
      ∃ z, inclK (sqrtK k) E z = 0 ∧ n • z = y)
```

## Proof of the passage to the limit

The infinite Selmer group is defined as a preimage in continuous first cohomology,
not as a categorical colimit. The proof therefore establishes the needed passage
on actual cocycle representatives; it does not assume a colimit comparison.

1. A continuous cocycle on `galK r` with discrete two-primary coefficients has
   finite image, because `galK r` is compact. Finite-set induction supplies one
   power `2^n` killing its entire image. The cocycle then lifts to the genuine
   finite torsion coefficient module. This proves `infinite_class_from_level`.
2. Finite-to-infinite coefficient maps commute with `inclK`. Since finite and
   infinite Selmer membership use the same image in point cohomology, every
   infinite Selmer class comes from a finite Selmer class, with every finite and
   infinite local condition retained: `selmer_class_from_level`.
3. A two-primary Shafarevich–Tate class lies in a finite torsion level and lifts
   by finite-level surjectivity. Conversely, every infinite coefficient
   cohomology class is killed by a power of two. This proves the target's image
   equivalence, `image_eq_primary_of_levels`.
4. An infinite kernel class is represented at a finite level. Its point image
   vanishes at that same level, so finite exactness identifies it with a Kummer
   class of a rational-point quotient: `kernel_class_from_point`.
5. Naturality proves the actual transition formula
   `levelNext (δ_n(P)) = δ_(n+1)(2P)`. Coherent finite-to-infinite maps give
   `2 · δ_(n+1)(P) = δ_n(P)` in infinite cohomology. Hence every kernel class has
   a half remaining in the kernel: `kernel_two_divisible`.
6. The kernel is two-primary. The integer Bézout identity permits division by
   integers coprime to a two-power exponent; strong induction, together with
   division by two, gives division by every nonzero natural number. This proves
   the full second clause, not just division by powers of two.

## Non-vacuity

For `E : y² = x(x - 1)(x + 3)` over `ℚ`:

- `elliptic_example` proves the ellipticity hypothesis.
- `finite_selmer_nonzero` supplies a nonzero class in the finite level-one Selmer
  group in the fixed-point model, transported from the Kummer class of `(0, 0)`.
- `finite_selmer_proper` supplies a finite cohomology class excluded by the real
  local condition. Thus that Selmer subgroup is neither zero nor the whole group.
- `imaginary_quadratic_nontrivial` proves that `ℚ(√(-1))` has a nontrivial Galois
  quotient, and `quadratic_level_example` specializes finite exactness to that
  field and this elliptic curve at level one.

These are concrete examples; no zero group was substituted for a genuine object.

## Sources and verification

All source files are new files in the directory
`ZInQKernel/Contrib/RC53Assist/DiskOrders/Limit/`.

| File | Bytes | Lines | Contents |
| --- | ---: | ---: | --- |
| `SilvermanLevel.lean` | 9525 | 213 | Finite groups, canonical maps, PRINT, finite proof |
| `CocycleLimit.lean` | 7202 | 154 | Finite cocycle images and Selmer exhaustion |
| `Transitions.lean` | 5059 | 109 | Coherent transitions and Kummer division by two |
| `PassageToLimit.lean` | 7396 | 155 | The exact requested implication and its corollary |
| `NonVacuity.lean` | 6290 | 127 | Concrete nonzero and excluded finite classes |

Source SHA-256 hashes are in `SHA256SUMS.txt`. The source files contain no proof
holes, new axioms, compilation-time code, notation declarations, or inspection
directives. Every source line is at most 100 characters. The heartbeat ceiling
is 800000.

The final sources build with Lean 4.35.0 and Mathlib 4.35.0. Building
`+ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.NonVacuity` builds all five modules.
The build used eight Lean threads and CPU affinity 64–95. No dependency retrieval
messages were observed.

The exact target implication and the unconditional corollary both report only
`propext`, `Classical.choice`, and `Quot.sound`. The audit includes the PRINT
definition and all 38 proved theorems. The actual output is recorded in
`AxiomAudit.txt`; its temporary checking module is not a delivered source file.

## What remains

No mathematical step remains for the requested implication. The printed-page
locator has not been checked. Existing source files, including the legacy PRINT
label in `ShaBridge.lean`, were not edited; no caller imports or integration
changes are included.

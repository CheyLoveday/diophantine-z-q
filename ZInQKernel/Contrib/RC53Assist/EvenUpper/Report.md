# Fixed-level even upper estimate

The faithful interface and thirty conditional theorems are proved and checked. Production of the original coefficient source, its actual readings, and its stationary parameter cubes remains separate. This does not discharge the original `even_upper` leaf unconditionally.

## Files and verification

- `Faithful.lean`: definitions, proofs, and all statement and axiom commands.
- [Exact statements and axiom output](statements-and-axioms.txt): the complete, unedited successful output, including every theorem's exact type and its `#print axioms` result.
- `Manifest.json`: byte counts and SHA-256 digests for the source, this report, the successful output, and the earlier checking records.

The final source has 30 named theorems and 30 matching axiom reports. Every report contains exactly `propext`, `Classical.choice`, and `Quot.sound`. The final individual-file compilation completed with exit code zero and no errors or warnings. The source uses a heartbeat bound of 600000. No repository command, project build, dependency update, existing-file edit, or change to another contribution was made.

The requested base was supplied as `a6c70bd54e403ce3ead8ff2b8e40f80445fe58cc`; it was used as a read-only base, not moved or independently re-queried through a repository command.

## Mathematical statement and comparison

Write `E = E_ell`, `N = N(E)` for its conductor, and `Lambda = Z_2[[t]]`. Fix the original parametrization, integral lattice, real and imaginary period convention, and allowed local types before any binary group or good-prime support varies. The manuscript identifies `N` as the conductor at lines 1779--1790.

### Formula (3.2)

Manuscript lines 1832--1844 and 1944--1946 assert the following.

There are constants `C_ev` and `C_loc`, depending only on the fixed data, such that every finite binary quadratic-character family with one real sign and fixed local squareclasses at every place dividing `2N` has one scalar `u_ev` in `Lambda[1/2][G]`. It satisfies

- `2^C_ev u_ev` belongs to `Lambda[G]` on the whole family;
- at a constituent of full two-primary Selmer corank zero, `u_h(0) = 0` if and only if `L_*(h) = 0`;
- at such a constituent with `L_*(h) != 0`, the absolute difference between `v_2 u_h(0)` and `v_2 L_*(h) - 2 omega(h) - s(h)` is at most `C_loc`.

The constants precede the family. The scalar is common to that family, not asserted to be independent of all families. The central valuation identity is not asserted at a central zero, where an integer-valued valuation has a default value.

`Scalar32At` and `Scalar32` retain this quantifier order, both central zero implications, and the nonzero guard. Their family level is exactly

```lean
N₀ ell = CST.newformLevel (Ecurve ell)
```

`CurveLevel ell` separately records a genuine functional equation at that level. `level_pos_of_bcdt` proves the least cusp-form level is positive. `level_eq_of_newform` proves it equals the level of any supplied genuine newform of the curve once the functional-equation anchor is supplied. No arbitrary zero level is substituted.

The current `EvenUpperRC11Inputs` instead existentially chooses a family level. `scalar32_iff_even` compares the faithful scalar to `Even.EvenScalar32` only under the supplied equality of their central-value functions. It does not construct a new normalization or any old-to-new normalization transport.

### Partitionability and actual units

For the rough-companion application, define `Gamma_d` to be the typed prime configuration of `|d|`, and `tau_d` its total type. `SourcePartitionable W T A d` means

- `d < 0`, `d` is squarefree, and every prime of the original support is prime to `d`;
- `Gamma_d` has the nonempty contraction certificate `IsPartitionable` for the supplied normalized symbol `A tau_d`.

`PartitionabilitySpec` requires the equivalence

```lean
∀ d, W.Partitionable d ↔ SourcePartitionable W T A d
```

The current fifth auxiliary-factor clause supplies only the forward inclusion from the genuine source predicate into `W.Partitionable`. `partitionability_forward` extracts that clause from the equivalence. `partitionability_reverse` extracts the additional reverse inclusion; it does not prove that the current one-sided clause implies it.

`SourceUnit W T A d` is the value one of this same supplied normalized symbol on the original negative squarefree filter. It is not an unrelated unit predicate chosen for the upper-bound proof.

`SourceCubeInputs` records arbitrarily large binary families at `N₀`, based at `d`, with all original primes retained at every address, the original source total type unchanged, and `SourceUnit` at every nonzero address. The parameter map need not be injective.

### Formula (3.3b)

Manuscript lines 2333--2336 assert, for a partitionable parameter in the fixed source filter with full two-primary Selmer corank zero,

```text
L_*(d) != 0
v_2 L_*(d) - 2 omega(d) - s(d) <= C_1.
```

These are two conjuncts, not an equivalence printed in the display. `Upper33b` retains both. The old `EvenUpper33b` retains only the numerical inequality. With the independent forward rank-zero theorem, the two conjuncts are also equivalent to corank zero on the partitionable domain; this additional converse is proved, not silently attributed to the display.

## Proved deductions

All exact binders and theorem types are in the successful statement record. The main deductions are:

1. `rc11Inputs_of_faithful`: `FaithfulInputs W T A` supplies the current `EvenUpperRC11Inputs W`, with its existential level witness set to `N₀`.
2. `upper33b_of_inputsAt`: the existing single-precision input proves nonvanishing as well as the inequality, with `C_1 = C_0 + 2 C_loc`.
3. `upper33b_of_fixedLevel` and `upper33b_of_faithful`: use the already proved Boolean comparison and single-precision adapter, without a family-independent scalar or an injective parameter map.
4. `currentUpper_of_faithful`: supplies the current numerical upper-bound consumer.
5. `faithful_upper_equivalence`: one constant works on the genuine partitionable source domain, in both directions.
6. `lowerBound_of_scalar32`: formula (E.9) already follows on the one-element family, with `C = C_ev + C_loc`. No continuation outside nonzero constituents and no new minimum are needed.
7. `unit_depth_of_supplied_minimum`, `unit_value_of_supplied_minimum`, and `units33a_of_supplied_minimum`: consume the already specified negative minimizer and the actual same-filter coefficient-square reading. They prove the exact (F.1) unit value and hence (3.3a), with `C_0 = 2 (va(kfin) - omega(kfin)) + kappa`.
8. `units33a_of_finite_sources` and `faithfulInputs_of_finite_readings`: combine already calibrated fixed-source constants. Different source constants are allowed; no new minimum is produced and no common minimum across total types is asserted.
9. `upper_at_unit`: an empty unit satisfies its bound directly, without a stationary address argument.

The principal source-domain conclusion has the exact following type, with the common source parameters shown explicitly:

```lean
theorem faithful_upper_equivalence {ℓ : ℕ} {W : WData ℓ} {L : Type}
    [AddCommGroup L] {ε : L →+ ZMod 2} {T : CoefficientDictionary.TypeData L ε}
    {A : L → Symbols.Config L → ZMod 2} (hf : Forward W)
    (h : FaithfulInputs W T A) :
    ∃ C₁ : ℤ, ∀ d : ℤ, SourcePartitionable W T A d →
      (Z2Corank (selmerTwoPower (Etw ℓ d)) 0 ↔
        W.Lstar d ≠ 0 ∧
          padicValRat 2 (W.Lstar d) - 2 * (omega d : ℤ) - sFun ℓ d ≤ C₁)
```

The successful output records this type and each of the other 29 types, with full declaration names and axiom dependencies.

## Connection to the current consumer

Given `h : FaithfulInputs W T A`, feed

```lean
rc11Inputs_of_faithful h
```

to the existing `evenUpper33b_of_RC11Inputs`. Use `h.normalized` for its normalization premise and the existing `LstarTarget` and analytic leaves for its forward-rank premises. This yields the existing numerical consumer with no edit to its declaration.

For the stronger output, use

```lean
upper33b_of_faithful hf h
```

and retain its nonvanishing conjunct. `faithful_upper_equivalence hf h` also records the reverse implication on the genuine source domain.

## Readings consumed and readings not produced

The minimum is an explicit input `SuppliedMinimum W aNZ va`:

```text
kfin < 0;
aNZ(kfin);
for every p with aNZ(p),
  va(kfin) - omega(kfin) <= va(p) - omega(p).
```

The coefficient reading is the separately minimized consequence `SquareReading W aNZ va kappa`:

```text
for every p with aNZ(p),
  L_*(p) != 0 and v_2 L_*(p) = 2 va(p) + kappa.
```

It is used only on that source's nonzero coefficients, not on all squareclasses of the curve. The original-source unit reading must also imply membership in `UnitMin aNZ va`, or in the finite union of separately calibrated source units. These are the precise consequences expected from the existing `actualEvenReading` / `Rev` extractors and the negative minimizer tied to `fixedkfin`.

No declaration producing those actual readings or that minimizer was imported or instantiated by this contribution. The constructors consume their outputs when supplied. They do not select another minimizer and then call it `kfin`. In particular, a reading of a different curve or a transported source is not identified with the original source.

Existing proved results actually used include `evenScalar32_of_appE`, `evenUpperInputsAt_of'`, its Boolean comparison, the Kummer corank-zero theorem, the fixed-level functional-equation comparison, and the equality of the two prime-factor counts. The scalar lower-bound and unit-value deductions are finite valuation arguments over those interfaces.

## Printed leaves and their boundaries

Only the two existing analytic leaves needed for the forward rank-zero implication enter its analytic constructor: BCDT Theorem A and Kolyvagin Theorem 1. Parity and the height formula are not required.

`forward_of_weil_leaves` keeps `ModularToWeakWeil` as a separate premise and uses `KolyvaginThm1WeilParam`, the existing weak-Weil-premise form. The analytic description of an algebraic weak Weil parametrization retains the translation gap documented by that existing leaf. `forward_of_analytic_leaves` is a compatibility route through the existing consequence-form leaf, not a claim that its stronger premise translation has been proved here.

The relevant manuscript-cited locators are BCDT Theorem A with Introduction conditions (1)--(6), and Kolyvagin, Theorem 1, MPIM preprint MPI/90-69, pages 4--5, with the weak Weil premise on page 3. The manuscript's forward-rank use is at lines 1092--1103. The fixed scalar construction uses Appendix E and its cited Kato Theorems 13.4(2) and 13.5(2). The actual `AppEOutputs` construction and the coefficient-square reading are not newly labelled printed theorems.

## Exact remaining obligations

To instantiate the faithful interface for the actual original source, the following remain to be supplied:

1. `CurveLevel ell`, namely a genuine functional equation at `CST.newformLevel (Ecurve ell)`. Positivity of this level is proved; the functional-equation witness is not produced here.
2. The existing original `LstarNormalized W.toRCData` witness. `LstarTarget W.toRCData` is also needed when constructing `Forward W` from analytic leaves.
3. `PartitionabilitySpec W T A`: exact equality between the interface predicate and the negative squarefree contraction-certificate predicate. The current one-sided fifth auxiliary-factor clause alone does not supply the reverse inclusion.
4. `Even.AppEOutputs (Ecurve ell) (N_0 ell) L`, with the original normalization equality. `scalar32_of_appE` then proves the faithful (3.2). Equivalently, an already proved `EvenScalar32` at this exact level can be consumed through `scalar32_iff_even`. An unspecified existential level is not enough.
5. The original-source actual unit readings. In the single-source specialization, these are `SuppliedMinimum`, `SquareReading`, nonzero parameters for nonzero coefficients, and `SourceUnit -> UnitMin`. For several prepared sources, the finite-source constructor instead consumes the already calibrated bounds and `SourceUnit -> exists i, unitSym i`.
6. `SourceCubeInputs W T A`: the exact arbitrary-dimension, fixed-level, stationary, same-total-type, actual-unit parameter-cube statement printed above. The existing source-only `realized_cubes_sq` result supplies the parameter factorization once its original-source factorization, type, and reading premises are available. Neither an abstract graph cube nor a reading of an unrelated transported source is substituted for it.

The smaller current-consumer cube obligation, if only `FixedLevelInputs` is required, is exactly:

```lean
∀ d : ℤ, d ≠ 0 → W.Partitionable d →
  Z2Corank (selmerTwoPower (Etw ℓ d)) 0 →
    ∀ b : ℕ, ∃ fam : Even.BinaryFamily (N₀ ℓ),
      b ≤ fam.b ∧ fam.h 0 = d ∧
        ∀ x, x ≠ 0 → UnitMin aNZ va (fam.h x)
```

The parameter-cube modules `ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Realize` and `ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Squarefree` have source files but no compiled objects in the supplied build. Neither was built. Their missing compiled objects prevent checking an additional realization adapter here.

If completing the source-unit implication or its cube reading requires an old-to-new unit-source, ratio, phase, normalization, or field assembly, that is a separate needed statement. No such assembly was attempted or assumed.

## Checking history

The final successful output is the only axiom receipt attached to the final source hash. Earlier successful individual-file checks and both unsuccessful checking attempts are retained separately. One attempt lacked the explicitly imported functional-equation comparison; one attempted an unavailable formatting option. Both were corrected before the final successful check. Earlier empty records represent exit-zero checks before the statement-printing commands were added, not independent checks of the final source bytes.

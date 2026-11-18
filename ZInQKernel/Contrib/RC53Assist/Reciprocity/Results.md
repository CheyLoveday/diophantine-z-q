# Local square and residual reciprocity

The embedding-compatible local square, the outside-set and complex-place reductions, and the elementwise reciprocity assembly are proved and compile. The concrete specialization to `GlobalRootsOfUnityCoefficients.MuS K S 1` and the named global map is not import-checked: those modules have not been supplied as compiled dependencies. The local injectivity producer is also not importable, so its precise input remains visible.

## Files and verification

- Publication source: `LocalCompatibility.lean`.
- Source size: 42,996 bytes; 821 lines; 35 named theorems and 10 definitions or structures.
- Source SHA256: `70d5ab0d1128bc20b843ee134198e5ead7462f7c6639c78228d9ac5b8401f6b3`.
- Single-file compilation: exit 0, without warnings.
- Axiom audit: exit 0, without warnings; all 35 theorems and all 10 definitions or structures have exactly `[propext, Classical.choice, Quot.sound]` as their printed axiom set.
- The scratch audit contains a byte-identical 42,996-byte prefix equal to the publication source.
- `Audit.lean` is scratch verification, not a publication source. It contains an exact copy of the publication source followed by statement and axiom queries.
- `Audit.log` contains the compiler's statement for every named theorem and definition, and each axiom report.
- `AuditFormattingFailure.log` preserves the first scratch run, which rejected a pretty-printing option. This did not change the publication source.

No existing source was changed. No global Brauer map, local order-two Brauer map, or local Kummer injectivity comparison was constructed here. No new printed theorem or nonstandard axiom was added.

## Genuine coefficient dictionary

The residual carrier is the existing type

```lean
TrivMod (GKS K S) (ZMod 2)
```

which is the definition of `HswIdent.MuTwo K S`. It is not identified with another module by its name alone.

The explicit interface for a genuine square-root coefficient module is

```lean
D : SquareRootCoefficients K S M
D.roots : M ≃+ Additive (rootsOfUnity 2 (KS K S))
D.equivariant : ∀ (g : GKS K S) (m : M),
  D.roots (g • m) =
    (restrictRootsOfUnity (galS K S g) 2).toAdditive (D.roots m)
```

`muTwoDictionary K S D` is the additive equivalence from the residual carrier to `M`. Its roots are specified by `muTwoDictionary_roots`; it sends the nonzero coefficient to the genuine root minus one by `muTwoDictionary_one`; and its Galois equivariance is proved by `muTwoDictionary_smul`. `muTwoH2Dictionary` is the induced degree-two equivalence.

`squareRootCoordinates_unique` proves equality with every additive identification with those same roots, so it can be applied to `HswIdent.muTwoRoots` when that module is importable. `twoRoots_naturality` proves compatibility with every field embedding, not only a selected one.

Wanted concrete specialization: set `M` to the relayed `GlobalRootsOfUnityCoefficients.MuS K S 1` and provide `D.roots` and `D.equivariant` from its actual definition. That definition was not present in the supplied source tree, so no concrete `MuS` witness is claimed.

## The exact local square

`decompSeparableEmbedding K v` is the restriction of the actual algebraic-closure embedding defining `decompMap K v`. `decompSeparableEmbedding_galois` and `locMap_via_separable` prove the exact agreement of the group maps in the two closure descriptions.

`localizeMuTwoH2` is restriction along the actual `locMap`; `localizeMuTwoH2_kerToH2` proves that it is the degree-two localization of the project's continuous cochains.

For the actual local coefficient dictionary, `localBrauer_square_canonical` proves

```lean
kummerToBr (F := v.adicCompletion K) 2
  (kummerH2Transport
    (localMuTwoEquiv K S v) (localMuTwoEquiv_smul K S v)
    (localizeMuTwoH2 K S v x)) =
  brBaseChange K (v.adicCompletion K)
    (toBrauer (muTwoH2Dictionary K S D x))
```

The more general `localBrauer_square` allows every equivariant local coefficient identification `eμ`. The square is never a hypothesis. The local maps are the existing `kummerToBr` and `kummerH2Transport`, following genuine cochain restriction.

## Defining global construction, not an assumed square

`GlobalBrauerConstructionCanonical K S D toBrauer` has exactly this defining content:

```lean
∃ (ι : M →+ (unitsRep K).V)
  (hι : ∀ (g : Field.absoluteGaloisGroup K) (m : M),
    ι (resAbsCont K S g • m) = g • ι m),
  ((unitsCoeffEquivUnitsRep K).symm
    (ι (muTwoDictionary K S D
      (show TrivMod (GKS K S) (ZMod 2) from (1 : ZMod 2))))).toMul = -1 ∧
  ∀ x : H2 (GKS K S) M,
    toBrauer x =
      (unitsRep K).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (GKS K S) M
          (Field.absoluteGaloisGroup K) (unitsRep K).V
          (resAbsCont K S) ι continuous_of_discreteTopology hι x)
```

`rootsInclusion_normalization` derives the generator normalization from the literal roots-inclusion formula through any field embedding. `canonicalConstruction_of_cocycleReadback` derives the defining property from a supplied actual cocycle producer, its value formula

```lean
(toUnitsCocycle c).1 (g, h) =
  ι (c.1 (resAbsCont K S g, resAbsCont K S h))
```

and the statement that this cocycle represents `toBrauer [c]`. These are the wanted readback interfaces for `toUnitsCocycle_apply` and `toBrauer_mk` or `toBrauer_represented_by`; their concrete binding is not claimed before import checking.

The relayed map specialization is `ZInQ.Contrib.GlobalRootsOfUnityBrauer.toBrauer K S 1`. It is an input, never a definition in this contribution.

## Outside-set and complex-place reductions

- `unramifiedMuTwoH2_subsingleton`: genuine unramified degree-two cohomology with residual coefficients is trivial.
- `localizeMuTwoH2_eq_zero_of_factorization`: a genuine unramified factorization kills localization.
- `localizeMuTwoH2_eq_zero_of_notMem`: no factorization input remains; the existing proved `unramifiedAtFactorization` producer supplies it.
- `localizedMuTwoCycle_isBoundary_of_notMem`: the actual continuous localized cocycle has a continuous boundary witness outside the set.
- `globalBrauer_outsideS`: the global Brauer image has zero localization outside the set.
- `brBaseChange_eq_zero_of_complex` and `brLocalization_infinite_eq_zero`: the complex-place terms vanish.
- `allPlaceSum_eq_finiteSum`: for finite `S`, the all-place Brauer sum equals the displayed finite sum over `S`, using the preceding reductions.
- `finiteSum_eq_zero`: that finite sum vanishes by the proved all-place sum formula.

Thus the all-place sum is not silently replaced by an `S`-sum. There is no remaining unramified-factorization or finite-sum reduction gap.

## Reciprocity assembly and exact remaining inputs

`reciprocityAt_from_globalConstruction`, `reciprocityAt_from_canonicalConstruction`, and `reciprocityAt_from_cocycleReadback` prove the elementwise conclusion of the supplied `ReciprocityAt` definition. `reciprocityAt_from_sumFormula` removes a separate sum hypothesis by the proved `sumLocalInv_brLocalization_eq_zero`.

Besides the field/module instances and `q : Places K S`, the minimal assembly `reciprocityAt_from_sumFormula` takes:

```lean
D : SquareRootCoefficients K S M
hK : IsTotallyComplex K
toBrauer : H2 (GKS K S) M →+ Br K
hcanonical : GlobalBrauerConstructionCanonical K S D toBrauer
hInjective : Function.Injective
  (ZInQ.Contrib.CloudB3RC53.Duality.kummerToBr
    (F := q.1.adicCompletion K) 2)
```

Its conclusion, with `T := TrivMod (GKS K S) (ZMod 2)`, is exactly

```lean
∀ e : (globalCx (ZMod 2) (GKS K S) T).X 2,
  (globalCx (ZMod 2) (GKS K S) T).d 2 3 rfl e = 0 →
  (∀ v : Places K S, v ≠ q →
    ∃ y : (localCx (ZMod 2) (GKS K S)
      (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 1,
      (localCx (ZMod 2) (GKS K S)
        (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T v).d 1 2 rfl y =
      (resS (ZMod 2) (GKS K S)
        (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T).f 2 2 rfl e v) →
  ∃ y : (localCx (ZMod 2) (GKS K S)
    (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T q).X 1,
    (localCx (ZMod 2) (GKS K S)
      (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T q).d 1 2 rfl y =
    (resS (ZMod 2) (GKS K S)
      (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).f 2 2 rfl e q
```

This expanded conclusion was checked against the source definition of `HswIdent.ReciprocityAt`. A named assignment to that declaration remains import-blocked because `HswIdent.Identifications.olean` is absent.

The existing source producer for `hInjective` is `ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteTrace.kummerToBr_injective`. Its compiled module is absent, and its proof was not reproduced. Therefore the assembly is not yet specialized to a theorem whose only unresolved proof inputs are the concrete global map properties: this one local producer import and the concrete coefficient binding are still needed.

## Reproducibility

Run from the supplied project root:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 taskset -c 128-143 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/Reciprocity/LocalCompatibility.lean
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 taskset -c 128-143 nice -n 10 lake env lean ZInQKernel/Contrib/RC53Assist/Reciprocity/Audit.lean
```

The publication source uses `maxHeartbeats 800000`. It contains none of the prohibited proof or command constructs. No dependency build is required for the generic result; the missing concrete specialization dependencies must be supplied separately.

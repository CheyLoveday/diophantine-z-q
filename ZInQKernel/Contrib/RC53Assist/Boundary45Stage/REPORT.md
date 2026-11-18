# Central finite-stage boundary: proof report

## Result and scope

This is a **proved partial identification on genuine objects**, not a discharge of `BaseZeroLeafInputsText` or Theorem 5.3.

The production source proves the actual central coefficient quotient, its Galois compatibility, projection of the genuine local Kummer maps and their cochain spans, and the two local boundary hypotheses on a specified continuous central Selmer datum. It also constructs the consumed `RetainedStage45` on the **same specified `SplitNormStage`**, with its local hypotheses supplied by proofs and its class and point maps fixed canonically.

The final source compiles with no diagnostics. All 68 theorem statements and their kernel dependency reports are reproduced in `THEOREMS.md`; `THEOREMS.json` is the machine-readable version. Thirteen additional definitions are audited there as well. Every audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Delivered source

- `ZInQKernel/Contrib/RC53Assist/Boundary45Stage/Identification.lean`
- 75,804 bytes
- SHA-256: `14c74c2d17cdf7254c14cd552470910bb41a64897ecd1efb82019e065af9604f`

The source was checked on the provided integration baseline `27579f4a130f4aa6724127f2a687d89d5c78fab1`, with Lean 4.35.0, six threads, CPU affinity 16–31 and niceness 10. Single-file checks began only after the supplied dependency log reported build completion. No existing source file was edited, and no version-control operation, repository build, package update, commit or checkout was performed.

## The actual objects that are fixed

### 1. The finite point and Galois stage

`geometricSplitNormStage` constructs the finite norm datum on the points of the specified elliptic curve over the specified finite extension:

- `Pt` is `(W.baseChange H).toAffine.Point`;
- `Δ` is the actual automorphism group `H ≃ₐ[K] H`, with its canonical multiplication and finite-type instance;
- the action is the actual coordinatewise point map;
- `incl` is the actual base-field point inclusion;
- the weighted point is determined by the split norm relation, `(a - 2) • P`.

`geometricSplitNormStage_spec` proves these identifications, including the action and inclusion. Abelianity is a property of the specified extension, not an arbitrarily supplied replacement group structure.

This does **not** construct a ring-class field or a CM point. The extension, subgroup, transversal, specified points, Frobenius, trace, norm equality and conductor-one trace identity remain fixed arithmetic inputs. The norm equality is exactly (4.1), as used at manuscript lines 2914–2936; it is not replaced by an existential zero system.

### 2. The continuous finite-stage datum before specialization

`finiteStageCharacter` is `alphaChar i (quadChar s) (inflChar H ξ)`, with the character inflated from that specified finite Galois extension. Its open kernel is proved. `FiniteCharacterOldType` states local triviality on the specified old Kummer places, and `finiteStageCharacter_localType` turns that property into RC29's actual local-character hypothesis.

`kummerFullSelData` is RC29's `kummerSelData` with its genuine Kummer conditions at the specified old places, full conditions at the other old places, and unramified conditions outside the coefficient support. `fixedKummerSpan` uses RC29's actual `kummerIotaS` and `kummerZ'`; there is no free span parameter. `fixedKummerSpan_cocycle` proves the required cocycle property.

`kummerFullSelData_eq_mixed` identifies this datum with `mixedStageSelData` as an equality of complexes **and maps**. `kummerFullSelData_eq_galois`, the term identifications and the restriction formula pin its global and local groups to RC26's continuous Galois cochains. `kummerFullSelData_localFacts` and `finiteStageSelData_localFacts` then supply the two local hypotheses from these fixed objects.

### 3. The genuine central coefficient fibre

The central coefficient ring is `ZMod (2 ^ i)`. `centralEval` is the existing constant-coefficient map at positive precision and the unique map between the genuine zero coefficient rings at precision zero.

At the base, `baseQuadChar_eq_one` proves that the actual quadratic character is trivial. `finiteStageCharacter_at_base_central` proves that the inflated finite-stage character specializes to one at **every** precision.

The central coefficient module is

```text
CentralCoeff = (Z/2^i) ⊗_Z W(K_S0)[2^i], with trivial coefficient character.
```

`centralCoeffProjection` is evaluation at the central parameter on the coefficient factor, keeping the actual torsion point. Its coefficient section is a right inverse. Its kernel is proved to be precisely `tM`, and `centralCoeffQuotientEquiv` identifies the actual quotient `M/tM` with `CentralCoeff`. The identification is the actual projection on representatives and intertwines the actual Galois action for the specified finite-stage character.

This is an additive quotient identification with the displayed coefficient semilinearity. It is not an asserted derived tensor comparison of entire Selmer complexes.

### 4. The actual central Kummer maps and spans

`centralKummerIotaS` is the original RC29 coefficient map followed by the actual central coefficient projection. `centralKummerIotaS_from_actual` proves that projecting the actual coefficient map for any finite character gives this same map. Its actual twist and torsion identifications and fixed decomposition embedding are retained.

The central map is equivariant and bijective on the actual local torsion coefficient module. In particular it has not been replaced by a degenerate coefficient map.

`localCochainProjection_kummer` proves the exact generator identity

```text
projection(a · iota_v(kappa_p)) = eval_0(a) · iota_v,0(kappa_p).
```

`localKummerSpan_projection` proves equality of the image of the **specified actual** Kummer cochain span with the specified central Kummer span. `actualKummerAtS_range_eq_span` and `centralKummerAt_range_eq_span` identify the cohomological images with the actual local Kummer class maps.

### 5. The actual central Selmer datum and its two local hypotheses

`centralSelData` is the continuous `galoisSelData` over `ZMod (2 ^ i)` on the inflated actual central coefficient module, with the prescribed Kummer/full/unramified pattern. Its global terms are the actual continuous cochains of `GKS K S`; its local terms are the products of the actual continuous local cochains.

`centralSelData_localHypotheses` proves exactly:

```text
For every closed c in L^0, there is a closed w in U^0 with iota^0(w) = c.
For every closed u in U^1, if iota^1(u) is a local coboundary, then u is a boundary in U.
```

Neither property is a premise. `centralSelData_localFacts` is their conjunction in the existing `LocalFacts` interface. This is valid at every precision, including zero, without substituting a toy norm stage.

## The consumed retained-stage construction

### Canonical global classes and the actual point map

The boundary interface asks for a class map on **all** first cochains. The canonical target used here is the ambient quotient `C^1/B^1`, not a postulated extension of the cohomology projection to nonclosed cochains.

`cochainClass_eq_zero_iff` proves its exact kernel. `cohomologyToClasses_injective`, `cohomologyToClasses_π` and `cochainClasses_eq_iff_homology` prove that on actual closed representatives, equality in this ambient quotient is exactly equality in actual first cohomology. Thus this representation does not weaken the global cohomology equality used by (4.5).

The point map is `globalKummerMap`, built from actual division points in the specified support field, the actual cocycle `gQ - Q`, the actual central coefficient inclusion, and actual inflation to the Selmer support. Its closedness, additive defect being a coboundary, and representative formula are proved. It is not a free additive map.

### What `CentralRetainedInput` contains

This input record retains only the arithmetic representatives and finite-model data still to be constructed:

- the specified actual global representative `zG`, with closedness and its class identification with the genuine Kummer map of `L • T.W`;
- local-condition representatives `zU`, `jU` and local degree-zero witnesses `zL`, `jL`, with their genuine Selmer-cone equations;
- the model projections `p1`, `p0`, their differential compatibility, the lifted differential, and the specified lifted coordinates `zeta`, `jay`.

It contains **no** free global/local cochain types, differentials, localization maps, local inclusions, class map, point map, exactness leaf, `honto` or `hinj`. Nor is existence of this record asserted for an arbitrary arithmetic construction.

`centralRetainedStage` turns this record into the consumed `RetainedStage45`. It sets `S := T`, so the supplied norm stage is preserved, not existentially replaced. Every cochain group and map comes from the actual central datum. The class-map kernel is proved, the point map is the actual `globalKummerMap`, and the two local fields are supplied by `centralSelData_localFacts`.

`centralRetainedStage_spec` proves the stage and group/map identifications. `centralRetainedStage_exists_witness` proves the retained finite-model boundary:

```text
exists v, for every coordinate a,
  zeta(a) - L * (T.a - 2) * jay(a) - (dC v)(a) belongs to 2^i Z_2.
```

The exact compiler statement, including every remaining input, is in the theorem appendix.

### The path into `BaseZeroLeafInputsText`

For the actual family of stages, instantiate the typed arithmetic records `C_i` on the actual supports and actual points, and set

```text
R_i := centralRetainedStage(..., T_i, ..., C_i).
```

These `R_i` feed directly to the existing `InnerLimit45Base.ofStages`. Its use of `RetainedStage45.exists_witness` is the consumed boundary path. The remaining central comparison and limit inputs of `ofStages` are unchanged; the resulting value fills `BaseZeroCoreText.limit`.

The local proof does not depend on the unused finite-construction adapter. It addresses the actual `RetainedStage45.honto` and `.hinj` fields. The alternative global construction, cycle and model inputs of `boundary45_finite_of_construction_of_localFacts` have not been silently discharged.

## Precisely what remains open

1. **Arithmetic stage realization.** Bind each specified integration stage to its actual ring-class extension, CM points, actual subgroup/transversal, Frobenius and conductor-one trace. The geometric constructor is genuine on a specified extension but is not a construction of these arithmetic objects. Supply the actual support and place partition as well; no arbitrary support or full-place choice can serve as their identification.

2. **Global division points over the actual support field.** The new named Prop `GlobalDivisionPointsInSupport W i` is
   `forall p in W(K), exists Q in W(K_S0), 2^i Q = p` under the actual inclusion.
   It has no unconditional proof here. It is stronger than the already supplied `FullTorsion` assertion, and is not deduced from that assertion. The needed good-reduction/multiplication-torsor support argument remains to be formalized. Given it, the global Kummer cocycles and map in this source are genuine constructions.

3. **Entire local-complex and model comparison.** The coefficient quotient and actual Kummer-generator/span comparisons are proved. A derived base-change comparison of the complete original local/Selmer complexes with `centralSelData` is not proved. In particular, no comparison from `B(K_v)^completed_2[-1]` to the explicit finite cocycle condition, no kernel comparison for its complete degree-one condition `Kummer span + B^1`, and no normalized contraction to the actual retained finite free model is asserted. If the integration uses a smaller support after removing the moving prime, its actual support-change comparison must also be supplied.

4. **The actual retained input records.** Construct the specified local Selmer-cone representatives and their comparison witnesses, identify the actual constructed class with the defined global Kummer map (`hzcls`), and construct the actual model projections and lifted coordinates of each `CentralRetainedInput`. These are still genuine arithmetic/model inputs; the new code gives no existential dummy realization.

5. **The inner limit and the rest of the leaf.** Construct the actual family of these inputs with the required uniform model and comparison data, supply the existing `ofStages` limit comparisons, and tie the result to the specified specialized cycle and point. The remaining two-term model, pairing, central Selmer comparison and primitive-coordinate identification of `BaseZeroCoreText` are not constructed here. Consequently `BaseZeroLeafInputsText` remains open.

## Reproducibility and evidence

`MANIFEST.json` gives SHA-256 and byte size for the delivered files. `compile-final.log` is empty because the final production check emitted no diagnostics; the command exited 0. `audit-final.log` contains the complete final statement/dependency output and its command exited 0.

The first full audit attempt rejected two optional pretty-printer settings; that unsuccessful output is preserved in `audit-format-error.log` and is not counted as a pass. The final audit omits those settings and explicitly prints function-binder types. Scratch checking commands are not present in the production source.

The first raw-file packet upload rejected the zero-byte compiler log. `ProofPacket.zip` preserves every delivered file, including that empty log and the manifest; the nonempty source, report and theorem appendix are also provided individually. This packaging change does not alter the checked source or its kernel reports.

The arithmetic assumptions and typed realization/model inputs are not kernel axioms. A standard-axiom report verifies the formal derivations; it does not prove those arithmetic inputs or complete the base-zero construction.

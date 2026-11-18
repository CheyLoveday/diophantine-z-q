# Retained assembly: interpretation correction and support-change reduction

Manuscript: `diophantine_zq.tex`, lines 3483–3498, 4391–4451 and 4976–5135.

This is a new edition in the namespace
`ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange`. The earlier reviewed
edition is preserved unchanged.

## Interpretation correction

The earlier `ResidualSupportControl` record does not itself specify an
arithmetic support map. Its embeddings may have zero reference component.
Under the printed and fixed-support setting, the checked statement is:

```lean
(∃ width : ℕ, Nonempty (ResidualSupportControl F R width)) ↔
  ActualResidualPackage F
```

Here the right side expands to exactly:

```lean
(∀ i [NeZero i], ResidualCohomologyFinite (F.globalCx i)) ∧
∃ B : ℕ,
  (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
    Module.finrank (ResidueField (Acoef i))
      (residualCohomologyAt (F.globalCx i) n) = 0) ∧
  (∀ i [NeZero i] (n : ℤ), Module.finrank (ResidueField (Acoef i))
    (residualCohomologyAt (F.globalCx i) n) ≤ B)
```

**Quantifier qualification:** the equivalence existentially quantifies `width`.
It does not assert that any prescribed fixed width suffices. The reverse
construction uses `width = B`, zero reference component, and padded basis
coordinates of the actual residual groups. This is the equivalence established
by the independent interpretation check, reproduced here as
`supportControl_iff_actualResidualPackage` with the corrected classification.

Consequently, deleting the parameter names `hres`, `hbdd` and `hB` from an
assembler did not independently discharge their mathematical content. The
retained constructor remains a valid conditional theorem. Its docstrings now
say explicitly that `residualSupport` retains the residual package.

## What the support-change proof actually does

Put `kᵢ := ResidueField (Acoef i)` and `Sᵢ := insert (F.q i) S₀`.

1. Reduce the **fixed reference cochains** using
   `residualGaloisSelmerIso`, rather than tensoring an assumed stagewise
   quasi-isomorphism through a nonflat coefficient change.
2. Construct `nativeSupportData F R i` from the genuine
   `galoisSupportDataUr`, with its canonical unramified factorizations.
3. Apply the printed `NekovarProp788ii K` **over `kᵢ` itself**. This gives
   the genuine inflation comparison, with the unramified condition at the
   new place, before any rank estimate.
4. Flatten the two Selmer cones by a proved degreewise cochain isomorphism.
   The exact sequence used is the existing `sesTop_shortExact` for that
   relative Selmer datum. Its cohomology segment is:

   ```text
   Hⁿ(reference after unramified support change)
     → Hⁿ(old-place-only complex on Sᵢ)
     → Hⁿ⁺¹(local correction)
   ```

5. The local correction is

   ```lean
   nativeCorrection F i =
     coneCx (orthNeg (nativeUnramifiedInclusion F i))
   ```

   It is the local condition cone `Cone(-ιur)[-1]`, **not** the full local
   complex by itself. The actual degree-zero inclusion is retained and
   proved injective, giving zero correction cohomology in degree zero.
6. Prove unramified cohomology finite, supported in `[0,1]`, and of rank
   at most the coefficient rank by actual Frobenius/coinvariant and
   procyclic-cohomology comparisons. The reduced reference coefficient
   module has rank **two**, independently of `i`.
7. The existing local finiteness and local-dimension-two suppliers give
   full local finiteness and range `[0,2]`. A separately specified full
   local arithmetic rank bound **four** gives a correction bound **six**
   and range `[1,3]`.
8. The fixed reference suppliers give a bound `B`. The actual cochain
   presentation transports the genuine support triangle to `F.globalCx`.
   The result has residual finiteness, range `[0,3]`, and bound `B + 6`.
   More precisely, each actual residual rank exceeds its corresponding
   reference rank by at most `extraRank 6 n`. Only after proving that estimate
   is the exact record `ResidualSupportControl F R 6` constructed, with target
   the reference group plus six coordinates in `[0,3]`. It is not constructed
   by widening the extra coordinate space to the full global bound `B + 6`.

The six is a conservative bound, not an optimal rank formula. The singleton
new-place index is proved; no bound uniform over all active supports is used.

## Exact remaining support and local inputs

The named support presentation is:

```lean
P : ActualSupportPresentation F R
```

Its exact fields are:

```lean
comparison : ∀ i [NeZero i],
  ComplexIso (gcxBaseChange kᵢ (F.globalCx i))
    (selCx (nativeOldDatum F R i))

localComparison : ∀ i [NeZero i],
  ComplexIso (nativeNewLocal F i)
    (gcxBaseChange kᵢ (F.localCx i))
```

`ComplexIso C D` is the existing cochain-isomorphism record:

```lean
e : ∀ n, C.X n ≃ₗ[kᵢ] D.X n
comm : ∀ i j (h : i + 1 = j) (x : C.X i),
  e j (C.d i j h x) = D.d i j h (e i x)
```

The native datum is fully specified before these comparisons:

- coefficient module before reduction:
  `referenceBaseModule i = MinS (subset_refl S₀) W i (α i)`;
- reduced coefficient module:
  `referenceResidueModule i = BCoef (Acoef i) kᵢ (referenceBaseModule i)`;
- old reduced conditions: `referenceResidualConditions R i`, formed by the
  existing actual cochain base-change maps;
- enlarged-support action:
  `ResMod (inflMap K (F.inclusion i)) (referenceResidueModule i)`;
- old local maps: `oldCondNew` with the proved `locMap_compat` identity;
- full new local complexes: actual continuous cochains at the elements of
  `NewPlaces K S₀ Sᵢ` with that restricted enlarged-support action;
- new unramified inclusion: actual `urCond`, using the canonical `urFactor`.

Thus `comparison` is specifically a comparison to the canonical inflated
reference old-condition complex, not a supplied finiteness or rank conclusion.
`localComparison` is the coefficient/singleton-place comparison to the native
local complex of the normalized stage-pairing supplier.

**These two arithmetic cochain comparisons are still OPEN.** Their construction
is not inferred from the reference rank estimates. In particular, the original
`ActualStageFamily.old` field allows arbitrary old conditions; the standard
reference family permits zero, full and Kummer conditions. Their actual old
condition and coefficient dictionaries must be matched. Unmatched previous
finite/singular conditions must not be silently identified with a different
standard or strict/relaxed condition. The separate coefficient-inflation
transport is not duplicated here.

The additional printed input is exactly:

```lean
h788 : NekovarProp788ii K
```

It is the existing genuine continuous-cochain support-change proposition,
not the abstract tame-model `SupportChangeInput` whose degreewise local model
cannot be instantiated by all-degree continuous cochains. Canonical
unramified factorization, finite residue-ring setting and self-injectivity are
proved, not new hypotheses.

### Alternative numerical local input

`residualSupport_six_of_support_change` constructs
`ResidualSupportControl F R 6` and takes:

```lean
hlocal : OddLocalResidualRanks F
```

Its exact type is:

```lean
∀ i [NeZero i] (q : NewPlaces K S₀ (F.support i)) (n : ℤ),
  Module.finrank kᵢ
    ((natCx (contCochains kᵢ (Gloc K q.1)
      (ResMod (locMap K (F.support i) q.1)
        (ResMod (inflMap K (F.inclusion i))
          (referenceResidueModule i))))).toCC.homology n) ≤ 4
```

Finiteness and cohomological dimension two alone do not imply this numerical
bound. A local Euler-characteristic/dimension calculation must supply it.
There is no remaining unramified finiteness, dimension or rank input: those
are proved here from the procyclic comparison.

### Reusing the original stage-local dimensions

`residualSupport_six_of_stage_dimensions` constructs the same fixed-width
record and replaces that numerical local input by exactly the original
local-dimension input:

```lean
hdim : ∀ i [NeZero i] (n : ℤ), Module.finrank kᵢ
  (residualCohomologyAt (F.localCx i) n) = splitLocalRank n
```

The ranks are `2,4,2` in degrees `0,1,2` and zero elsewhere. Through
`P.localComparison` and the proved singleton-place projection, this implies
the numerical local bound four. `assemble_from_support_change` obtains
`hdim` directly from `(stage i).localDimensions`, so it asks for **no new
numerical local-rank assumption** in addition to the original stage input.
The local dimensions themselves remain genuine open arithmetic inputs.

## New assembly theorem

With the setting and implicit parameters of the earlier assembler, the new
entry point is exactly:

```lean
theorem assemble_from_support_change (p : ArithmeticPrints K)
    (h788 : NekovarProp788ii K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K),
      (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (P : ActualSupportPresentation F R)
    (oldFlat : F.NontrivialOldFlat)
    (stage : ∀ i [NeZero i], StageArithmeticInput F O i)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀)
    (hW : W.map (Cn.κ : K →+* K) = W) :
    ∃ T : ResidualSupportControl F R 6,
      Nonempty (AssembledLimit
        (⟨oldFlat, T, stage⟩ : ArithmeticInputs F O R 6)
        U hU Cn hW)
```

`T` is an **output**, not an input. The retained constructor then uses the
same produced stage pairings and the same retained complex/localization for
its certificates. The original old-flatness, original cups/isotropy,
unmatched complement, original duality-diagram transport, derivative action,
fixed roots and local-dimension inputs remain exactly as in the earlier
assembler. Their full types are included in the new statement audit.

## What remains

The support-change rank reduction is conditional on the exact cochain
presentation and existing support-change print. It does **not** prove that
those presentation maps exist for a given arithmetic family; that is the
remaining identification work. Therefore no unconditional residual discharge
or completion of Theorem 5.3 is claimed.

The scope is enlargement by one new place per coefficient stage from one
fixed old support. Several simultaneously moving old derivative supports
would require their own bounded-cardinality support presentation and local
condition comparisons; this edition does not assert that extension.

The earlier unmatched old-complement obligations remain open. The exact
retained local-form normalization, original trace-cup comparison, detection
label/localization matching and finite/singular side-to-stage identifications
are not supplied by this residual reduction.

`StatementAudit.txt` and `Verification.txt` record the final checked statements,
axiom reports and single-file verification. Diagnostic commands remain in
`Scratch/`, not in `Assembly.lean`.

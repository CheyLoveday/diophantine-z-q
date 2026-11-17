# chevalley-free: the research field `chevalleyPerfect` removed, no new leaf

Task chevalley-free, 2026-11-17. Base: wip/leaf-fold33b `fe2f0d4a`. This is model work; no human has reviewed it.
There is no network on this host, so every theorem number below is recalled from memory and marked UNVERIFIED.

Marks used below:
- **VERIFIED**: compiled, computed, or read in a named file on this host.
- **STANDARD**: published, with an exact reference.
- **SPECULATIVE**: my own argument.
- **UNVERIFIED**: a theorem number recalled from memory.

## 1. Result

**`ZInQ.HeightFix.SemiAbelianDescendsPerfect` is now a theorem. It has no hypotheses and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound` (VERIFIED, compiled).** So the research field `chevalleyPerfect` can be
removed with no new leaf and no new glue.

```lean
theorem ZInQ.ChevFree.semiAbelianDescendsPerfect_proof : ZInQ.HeightFix.SemiAbelianDescendsPerfect
theorem ZInQ.ChevFree.bostLowerBound_of_printed_free (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed) :
    ZInQ.HeightSplit.BostLowerBound
-- likewise gaudronRemondThm14_of_printed_free, javanpeykarBound_of_printed_free, pazukiCor13Upper_of_printed_free
```

The proof is in `scratch/chevalley-free/ChevFree.lean`, one file of 2060 lines. Its imports:
- `ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect`, for the statement and semiab-descend's lemmas;
- vendored CloudW07 (Jacobian-Challenge) modules;
- `MilneQuasiInverse.Descent`;
- Mathlib.

It compiles with `lake env lean` in about 25 s. All 22 `#print axioms` lines are standard (VERIFIED,
`scratch/chevalley-free/compile_ChevFree.txt`).

**Fold.** The field is removed by a bypass module, `scratch/chevalley-free/fold/TailZ65.lean.txt`, written by
`fold/gen_bypass.py`. It contains three declarations:
- `OpenResearchLeaves40`: `OpenResearchLeaves39` without `chevalleyPerfect`, with 27 fields. The field list and order
  are those that autofold produces (VERIFIED, diffed).
- `openResearchLeaves36EB_of_OpenResearchLeaves40`;
- `sixContactMin_of_open58`.

Counts and checks:
- **Strict count: 16/15 on 31 → 15/15 on 30.** The strictest count is the same. So there is one LEAF fewer and the
  GLUE count is unchanged. This comes from autofold's count dry run, `fold/autofold-count-dryrun.txt` (VERIFIED).
- A copy of `ZInQ.OneProof.frozenTarget` with the new bundle and top theorem compiles with standard axioms
  (`fold/MainCheck.lean`, VERIFIED).
- **ChevalleyPerfect is not in the closure** of the new `sixContactMin_of_open58` or of the new frozen target. Neither
  are `semiAbelianDescendsPerfect_of_chevalley`, `bostLowerBound_of_printed_chevalley`,
  `gaudronRemondThm14_of_printed_chevalley`, `sorryAx` or `OpenResearchLeaves39` (VERIFIED, closure check in
  `fold/MainCheck.lean`, output `fold/compile_MainCheck.txt`).

## 2. What the field was used for (VERIFIED, grep and closure)

In the closure of the current top `sixContactMin_of_open57` (270602 constants), the constants that mention
`ZInQ.SemiAbDescend.ChevalleyPerfect` directly are:
- the bundle fields and constructors of `OpenResearchLeaves39`, `38EB` and `37EB`;
- `semiAbelianDescendsPerfect_of_chevalley`;
- `bostLowerBound_of_printed_chevalley` and `gaudronRemondThm14_of_printed_chevalley`, which call it.

The bundle reads the field in three places:
- `javanpeykarBound` in the conversion `38EB → 37EB` (`EichlerBoundCopy.lean:4012`);
- `bostLowerBound` and `gaudronRemondThm14` in the conversion `37EB → 36EB` (`EichlerBoundCopy.lean:3904`, `3907`).

All three go through `semiAbelianDescendsPerfect_of_chevalley`. That theorem uses the leaf twice:
- existence over `k`, for `U = G⁰`;
- uniqueness over `k̄`, to compare that presentation with the given torus presentation.

Together the two uses give exactly the descent of the quotient `(B', π')` from `k̄` to `k`, with the same kernel over
`k̄`.

## 3. The proof

**Step A (`QuotientDescendsPerfect`, `semiAbelianDescendsPerfect_of_qd`).** The only thing the assembly takes from the
leaf is now isolated as a Prop. Setting:
- `U` is a smooth, quasi-compact, connected group scheme over a perfect field `k`;
- `π' : U_{k̄} → B'` is a faithfully flat homomorphism onto an abelian variety;
- its kernel is a split torus in the functor of points.

The Prop asserts that there is a faithfully flat homomorphism `π : U → B` onto an abelian variety over `k`, such that
`π_{k̄}` and `π'` have the same kernel on `R`-points for every `k̄`-algebra `R`. The assembly is semiab-descend's proof
with step (e) replaced.

**Step S (`spread`).** `B'` and `π'` are defined over a finite subextension `k₁ ⊆ k̄`:
- the vendored `exists_finiteSubext_isPullback` gives `X₀` over a finite `k₀`;
- Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` factors `π'` through `U ×_k k₁`. It is applied
  to the base-changed system `U ×_k k_i`, using the vendored `isLimitBaseChangeCone`.

The output:
- `X₁` over `k₁` and `π₁ : U_{k₁} → X₁`;
- `c : B' → X₁` with `IsPullback c B'.hom X₁.hom (Spec k̄ → Spec k₁)`;
- `π' ≫ c = (U_{k̄} → U_{k₁}) ≫ π₁`.

**Step R (rigidity: `torus1_const`, `torusR_const`, `rig_raw`).** Over any field `K`, a morphism
`Spec K[x₁^{±1}, …, x_r^{±1}] → B` to an abelian variety takes the same value at all `K`-points.
- `𝔾_m` is the overlap of the two charts of the vendored relative `ℙ¹`.
- The vendored `exists_hom_of_valuationRing_stalk` extends the map to `ℙ¹`. The stalks are valuation rings because
  `ℙ¹` is smooth of relative dimension 1, which is proved here from Mathlib's `𝔸ⁿ`.
- The vendored `RationalCurves.eq_zero_comp` makes the extension constant. Commutativity of `B` comes from Mathlib's
  `isCommMonObj_of_isProper_of_geometricallyIntegral`.
- The `r`-dimensional case is done one coordinate at a time.

**Step K (the transport condition).**
- `torus_kernel_transfer`: a point of the torus `ker π'` for one `k̄`-structure `ra` on a field `L` maps to `1` under
  `π'` for every other `k̄`-structure `rb` that agrees with `ra` on `k`. This is rigidity over `L`, transported with
  RaynaudSemistableOr's `Φ rb`.
- `kbar_KI`: kernel pairs of `π'` are stable under such a change of structure.
- `algclosed_KI` and `field_KI`: the same at the finite stage. An embedding `k₁ → L̄` extends to `k̄`.
- `KI_of`: `KI q π₁` for arbitrary test schemes. It uses the vendored field tests `over_hom_eq_of_field_tests` on the
  smooth (hence reduced) universal source `(U₁ ×_{X₁} U₁) ×_k k₁`.
- Smoothness of `π'` is semiab-descend's shear argument, with `π₁` smooth by descent along `c`. Smoothness of
  `Spec k₁ → Spec k` holds because `k₁/k` is finite separable, `k` being perfect.

**Step D (`exists_descent`).** For a finite, flat, surjective, finitely presented `q : S' → S`:
- **Input:** an fpqc morphism `π₁ : U_{S'} → X₁` satisfying `KI`, where finite sets of `X₁` lie in affine opens.
- **Output:** `X₁` descends to `B₀` and `π₁` descends to `π : U → B₀`.
- **Descent datum:** `ψ : X₁ ×_S S' → X₁`, `(π₁(u, a), b) ↦ π₁(u, b)`. It is built by effective-epi descent along
  `π₁ × id`. Its unit, the identity `ψ ≫ hom = snd` and coassociativity are proved by epi cancellation. It is then
  converted to the vendored transport form.
- **Effectivity:** the vendored `isEffective_of_isFinite`.

**Step G.**
- `exists_grpObj`: if `π : U → X` is fpqc and `π a = π b` is a congruence, then `X` is a group and `π` a homomorphism.
  The axioms are proved by cancelling `π`, `π ⊗ π`, `(π ⊗ π) ⊗ π` and the unitor epimorphisms.
- `cong_of_faithful`: the congruence follows from a faithful monoidal base change onto a homomorphism. Here the base
  change is `Over.pullback` along `Spec k̄ → Spec k₁` or `Spec k̄ → Spec k`, which Mathlib makes faithful for fpqc maps.
- `isMonHom_pullbackComp`: the composition isomorphism of pullbacks is a homomorphism, via Mathlib's
  `mapMonNatIso` and `mapMonCompIso`.

**Step F (`fsd`).** The finite-stage model gives `B` and `π` over `k`:
1. `π'` is smooth, so `π₁` is smooth, surjective and quasi-compact.
2. Over `k₁`, `X₁` is proper, smooth and geometrically integral. These properties descend along `k̄/k₁`; the lemmas are
   copied from vendored `Picard/FieldDescent.lean`.
3. `X₁` is a group by G, comparing with `B'` through `Ecomp`.
4. `KI` holds by K, and finite sets lie in affine opens by the vendored projective embedding of group varieties.
5. Step D gives `B₀` and `π`.
6. `π` is smooth and surjective, `B₀` is an abelian variety, and `B₀` is a group by G, comparing with `B'` through the
   pasted square `B' → X₁ → B₀`.
7. The kernel condition holds because `F.map π = π' ≫ Θ⁻¹`.

## 4. Fold (`scratch/chevalley-free/fold/`)

| file | content |
| --- | --- |
| `gen_bypass.py` | writes `TailZ65.lean.txt` from TailZ63 and EichlerBoundCopy: the new bundle `OpenResearchLeaves40` (27 fields, docstrings verbatim, stale "leaf chevalleyPerfect" wording updated), the composite conversion `openResearchLeaves36EB_of_OpenResearchLeaves40` (the three existing conversions `39 → 38EB → 37EB → 36EB` composed, the three readers replaced by `ZInQ.ChevFree.*_free` / `semiAbelianDescendsPerfect_proof`), `sixContactMin_of_open58` |
| `TailZ65.lean.txt` | the module, to go in as `ZInQKernel/OneProof/H/TailZ65.lean`; it imports `ZInQKernel.Contrib.OneProof.ChevalleyFree`, which is `scratch/chevalley-free/ChevFree.lean` copied verbatim |
| `Main.lean.patched.txt` | Main switched to TailZ65, `OpenResearchLeaves40` and `sixContactMin_of_open58` |
| `autofold-count.json`, `autofold-count-dryrun.txt` | autofold's dry run, discharging the field by `sorry`. It is used only for the count: `strict count: 16/15 on 31 -> 15/15 on 30; strictest 16/15 -> 15/15`. Its bundle has the same fields, in the same order, as the bypass module |
| `MainCheck.lean` | `ChevFree.lean` + the module body + a copy of `frozenTarget` on the new bundle + the closure checks; compiles (about 7 min with the closure walk) |

**Why a bypass.** autofold discharges a field only with a proof of its type, and `ChevalleyPerfect` itself is not
proved. Its readers sit two and three conversions below the top. So the new bundle maps straight to
`OpenResearchLeaves36EB`, where all three consumers are themselves fields. This is the bypass recipe of leaf-fold14
and fold33-copy. No existing declaration changes.

**Steps for whoever lands it** (none of them run here, because `ZInQKernel/` is not this task's to edit):
1. Add `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean` (`ChevFree.lean`), `ZInQKernel/OneProof/H/TailZ65.lean` and
   the patched Main.
2. In `docs/one-proof/kinds.tsv`, remove the `chevalleyPerfect` row; in `claims.tsv`, remove its rows. This is what the
   autofold dry run computes.
3. Run the usual checks: OpenStatements, render_open, `#discharges` and the hash guard.

`ChevalleyFree` lives in `Contrib/OneProof`, so `#discharges` will list its theorems. It declares no Prop structures,
so it adds no projection noise.

## 5. What this does not do

- `UnipotentForward.SemiAbelianDescendsSepClosed`, the separably closed and possibly imperfect case, is a different
  Prop and is untouched. SPECULATIVE: the argument here does not reach imperfect fields as written, because `KI_of`
  uses smoothness of `Spec k₁ → Spec k`, that is, separability of `k₁/k`.
- Chevalley's theorem itself (`ChevalleyPerfect`) is not proved; it is no longer needed.
- The fold was not run in the tree, and the `kinds.tsv` and `claims.tsv` edits are not made.

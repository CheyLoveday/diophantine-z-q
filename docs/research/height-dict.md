# height-dict: the kernel's Faltings height is the printed one

**Verdict (VERIFIED: compiled, standard axioms).** The archimedean part of the dictionary is now a Lean
theorem. Two of the three reasons the 11-16 pass gave for rating `bostLowerBound` and `gaudronRemondThm14`
as consequences are proved: the analytic uniformization being biholomorphic onto `A^an`, and the torus
integral of `|ω ∧ ω̄|`. Both rows are restated over a printed stable height, `IsPrintedStableHeight`. That
height is built as the print builds it:

- the Néron model over a semistable field;
- `ω = ⋀^g e*Ω¹`;
- the metric `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄`, defined as the total mass of the invariant measure on `A_τ(ℂ)` with
  its analytic topology, normalized at the identity in algebraic coordinates. No uniformization enters the
  definition.

Both consumer forms are proved from the restated leaves, using the textbook fields `uniformizationLeafAll`
and `mumfordTorsionAlgClosed`, which give T35:

```lean
theorem ZInQ.HeightDict.bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.BostLowerBound
theorem ZInQ.HeightDict.gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.GaudronRemondThm14
```

The printed height is also proved to **coincide** with the kernel's, so the restated leaves are equivalent
to the old ones, given T35:

```lean
theorem ZInQ.HeightDict.isPrintedStableHeight_iff (hU : AnalyticUniformizationUnique)
    (hDim : UniformizationDim) (hMet : NeronMetrizable) [NumberField K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsPrintedStableHeight A x ↔ IsStableFaltingsHeight A x
```

The printed metric is not vacuous: a normalized invariant measure exists (`exists_isNormalizedBy`). Hence
for `η ≠ 0` it has exactly one value, the kernel's `|c_τ η|² covol(Λ_τ)` (`isFaltingsMetricSq_iff`).

**Route.** Route (a) was taken, and it turned out to also give (b): the leaves are restated over a printed
definition, and that definition is proved equal to `GroupModel.height`'s value. Route (b) on its own was
not shorter. To prove the consumer form from restated leaves, one needs exactly the equality "printed =
kernel", which is (a). The real choice was how to state the printed integral. Mathlib 4.35 has no integration
of differential forms on manifolds, so `(i/2)^g ∫_{A(ℂ)} η ∧ η̄` is stated as a characterization: the total
mass of every finite left-invariant Borel measure that is `(i/2)^g η ∧ η̄` at the identity (§2). That is how
the integral of an invariant volume form is defined, and it needs neither charts away from `1` nor a
uniformization.

**Remaining dictionary step (not proved).** The third reason, `ω = e*Ω¹` (EGA IV 17.2.5), is unchanged. The
printed height uses the kernel's `detLattice g`, which is `⋀^g` of the conormal lattice `⋂_s image(I_{e(s)})`
in `𝔪_ξ/𝔪_ξ²`. Mathlib 4.35 has no sheaf of relative differentials on schemes, so `Γ(S, e*Ω¹)` cannot be
stated as a Mathlib object. Its stalkwise form (Kähler differentials of the local rings) is in §5 with its
status.

## 1. `GroupModel.height` and the docstring argument for its faithfulness

Read (VERIFIED) in `ZInQKernel/HDecomp/Faltings/{Models,HodgeData,Height}.lean`:

- `GroupModel.height 𝒢 = ⨅ (g) (M : MetrizedModel A L g) (_ : M.model = 𝒢), M.hodge.modelHeight`
  (Height.lean:235).
- `modelHeight = deg(ω̄)/[L:ℚ]` with `deg = log #(M/𝓞η) − Σ_τ log ‖η‖_τ` (HodgeData.lean:391, `modelHeight_eq`).
- `‖η‖²_τ = torusMetricSq (periods τ) (coeff τ η) = |coeff τ η|² · covol(periods τ)` (HodgeData.lean:268, 365).
- `MetrizedModel.arch` (Height.lean:30-40) ties `periods τ` to the kernel `Λ` of a
  `𝒢.IsAnalyticUniformization τ Λ Φ` and `coeff τ (wedge f) = jacDet Φ f`:
  - `IsAnalyticUniformization` (Models.lean:206): `Φ : ℂ^g → 𝒢(ℂ)_τ` is a surjective homomorphism with kernel
    `Λ`, each `Φ⁻¹(U(ℂ))` is open, and regular functions are `ℂ`-differentiable along `Φ`.
  - `jacDet Φ f = det(∂(fᵢ ∘ Φ)/∂z_j(0))`.
- `lattice_eq` ties the lattice to `detLattice g`, which is `⋀^g` of `omega = ⋂_s omegaAt s`
  (Models.lean:125-160).

The faithfulness argument in the docstrings has three parts:

- Models.lean §17: "`Φ` induces a continuous bijection of the compact `ℂ^g/Λ` onto the Hausdorff `A_τ(ℂ)`, a
  homeomorphism, holomorphic, hence biholomorphic ... STANDARD facts of complex analysis, not proved here".
- HodgeData.lean, `torusMetricSq`: "`‖η‖² = (i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄ = |c|² · covol(Λ)`".
- Models.lean §16: "the image of `I_x` in `𝔪_ξ/𝔪_ξ²` is the stalk at `s` of the conormal sheaf
  `e*(I/I²) = e*Ω¹_{𝒢/S}` (EGA IV 17.2.5, UNVERIFIED)", and global sections are the intersection of the
  stalks.

These are exactly the three steps the 11-16 pass named.

## 2. The printed height (Lean, `ZInQKernel/Contrib/OneProof/HeightDictionary.lean`)

```lean
noncomputable def anBorel (𝒢 : GroupModel A L) (τ : L →+* ℂ) : MeasurableSpace (𝒢.Pts τ) :=
  @borel _ (anTop 𝒢 τ)

noncomputable def coordMap (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) : 𝒢.Pts τ → (Fin g → ℂ) :=
  fun p i => 𝒢.evalAt p (U i) (s i)

def IsNormalizedBy (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (mu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : 𝒢.Pts τ), ∀ E ⊆ W, MeasurableSet E →
      |(mu E).toReal - ‖τ l‖ ^ 2 * (volume (coordMap 𝒢 τ U s '' E)).toReal| ≤
        ε * (volume (coordMap 𝒢 τ U s '' E)).toReal

def IsFaltingsMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ mu : Measure (𝒢.Pts τ), IsFiniteMeasure mu → mu.IsMulLeftInvariant → IsNormalizedBy 𝒢 τ mu eta →
    (mu univ).toReal = r

def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ 𝒩.detLattice g, eta ≠ 0 ∧ secIndex (𝒩.detLattice g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsFaltingsMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (𝒩.detLattice g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L
```

Every object is Mathlib's or the kernel's:

- `anTop` (TailZ.lean:875) is the analytic topology of `𝒢(ℂ)_τ = A_τ(ℂ)`, generated by the sets
  `{p ∈ U(ℂ) | s(p) ∈ V}`. It is Hausdorff by the proved `analyticPointsT2`.
- `Measure`, `IsMulLeftInvariant`, `volume` on `ℂ^g` (Lebesgue measure `dx₁dy₁⋯dx_gdy_g`) and `borel` are
  Mathlib's.
- `wedge`, `detLattice`, `secIndex`, `IsNeronModel` and `IsSemistable` are the kernel's.

Reading:

- `IsNormalizedBy mu η` says that `mu` is the measure `(i/2)^g η ∧ η̄` near the identity. Take any regular
  functions `f₁, …, f_g` vanishing at the origin with `η = l · df₁ ∧ ⋯ ∧ df_g`. Then the image of `mu` under
  `F = (f₁, …, f_g)` has density `|τ(l)|²` at `F(1)` with respect to Lebesgue measure, since
  `(i/2) dz ∧ dz̄ = dx ∧ dy`.
- For the true measure of the invariant form, this holds: in the chart `F`, which is a chart near `1` because
  `wedge f ≠ 0` when `η ≠ 0`, the density is `|h|²` with `h` continuous and `h(1) = τ(l)`.
- The true measure is left-invariant because `η` is invariant.
- `IsFaltingsMetricSq η r` says that every such finite invariant measure has total mass `r`.
- Sign: `(i/2)^g ∫ η ∧ η̄` is read as the positive measure `|h|² dλ`. This is the convention that makes the
  metric positive. The kernel's `torusMetricSq` docstring uses the same reading.

## 3. What is proved (all VERIFIED: `lake env lean` / `lake build`, axioms `propext, Classical.choice, Quot.sound`)

New files (all under `ZInQKernel/Contrib/OneProof/`; nothing else under `ZInQKernel/` edited):

| file | content |
| --- | --- |
| `HeightDictionary/TorusVolume.lean` (Mathlib only) | `exists_fundamentalDomain_ball` (a fundamental domain of `Λ` containing a ball `B` with `(B − B) ∩ Λ = 0`); `IsUnif.torusHomeo` (`ℂ^g/Λ ≃ₜ G`); `IsUnif.isTopologicalGroup`, `compactSpace`, `secondCountable`; `IsUnif.piMeasure_*` (`π = Φ_*(Lebesgue|_D)` is finite, left-invariant, open-positive, i.e. Haar, independent of `D`, with `π(Φ(B_r)) = λ(B_r)`); **`volume_eq_of_normalized`** (below); `piMeasure_normalized` (existence) |
| `HeightDictionary/Holomorphic.lean` (Mathlib only) | **`hasStrictFDerivAt`**: a map `ℂ^g → E` that is `ℂ`-differentiable on an open set is strictly differentiable there. Each partial derivative is the Cauchy integral `(2πi)⁻¹ ∮ t⁻² f(z + t v) dt`, continuous in `z`. Mathlib 4.35 has holomorphic ⇒ `C¹` only for `ℂ → E`, while the kernel's `IsAnalyticUniformization` gives only `DifferentiableOn ℂ` |
| `HeightDictionary.lean` | the definitions of §2; `BostLowerBoundPrinted`, `GaudronRemondThm14Printed`; `isFaltingsMetricSq_of_metrized`, `det_fderiv_coordMap`, `hasStrictFDerivAt_coordMap`, `exists_isNormalizedBy`, `isFaltingsMetricSq_iff`, `isPrintedStableHeight_of`, `isStableFaltingsHeight_of_printed`, `isPrintedStableHeight_iff`, `bostLowerBound_of_printed(')`, `gaudronRemondThm14_of_printed(')` |

The core lemma (`TorusVolume.lean`):

```lean
theorem volume_eq_of_normalized (h : IsUnif Λ Φ) (μ : Measure G) [IsFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (F : G → (Fin g → ℂ)) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hψ : HasStrictFDerivAt (F ∘ Φ) (D.restrictScalars ℝ) 0) (a : ℝ)
    (hnorm : ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |(μ E).toReal - a * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal) :
    (μ univ).toReal =
      a * ‖LinearMap.det (D : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * ZLattice.covolume Λ
```

Here `G` is a Hausdorff group and `IsUnif Λ Φ` says `Φ` is a continuous surjective homomorphism with kernel
the full lattice `Λ`. Proof:

1. `G` is the compact topological group `ℂ^g/Λ`, transported along the homeomorphism.
2. `π` is a Haar measure, so `μ = c π` by Mathlib's `isMulLeftInvariant_eq_smul`.
3. Take a fundamental domain containing a small ball `B_r`. Then `μ(Φ(B_r)) = c λ(B_r)`.
4. Mathlib's Jacobian estimates (`addHaar_image_le_mul_of_det_lt`, `mul_le_addHaar_image_of_lt_det`) give
   `λ(F(Φ(B_r))) ≈ |det_ℝ D| λ(B_r) = |det_ℂ D|² λ(B_r)`.
5. The normalization then forces `c = a |det D|²`, and `μ(G) = c λ(D) = c covol(Λ)`.

Applied to `G = 𝒢(ℂ)_τ` with `anTop`, `Φ` from `M.arch`, and the algebraic coordinates `F`:
`|τ(l) det D|² = |τ(l) jacDet Φ f|² = |coeff_τ η|²`. This uses `germAlong_eventuallyEq`, `fderiv_pi` and the
`arch` clause. The result, `isFaltingsMetricSq_of_metrized`, is the kernel's
`torusMetricSq Λ (coeff τ η)`.

`#discharges` (VERIFIED, `scratch/height-dict/discharges.txt`, built on this base):

```
DISCHARGES [OpenResearchLeaves26.bostLowerBound] by ZInQ.HeightDict.bostLowerBound_of_printed
  still assumes: [ZInQ.HeightDict.BostLowerBoundPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.gaudronRemondThm14] by ZInQ.HeightDict.gaudronRemondThm14_of_printed
  still assumes: [ZInQ.HeightDict.GaudronRemondThm14Printed,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2936 theorems checked, 11 discharge one
```

(The `'` variants, which assume the kernel Props `AnalyticUniformizationUnique` and `UniformizationDim`
instead of the two fields, are also listed.)

Autofold: the spec is `scratch/height-dict/autofold.json`. Its dry run exits 0 and prints
"strict count: 34/11 on 45 -> 34/11 on 45". This base's `kinds.tsv` still rates both rows LEAF; under the
11-16 consequence rating the fold is −2 GLUE. The dry-run module `scratch/height-dict/FoldDryRun.lean` (the
output without its first line) compiles, and `sixContactMin_of_open36` has standard axioms. The new fields
`bostLowerBoundPrinted` and `gaudronRemondThm14Printed` go into `OpenResearchLeaves27`. `uniformizationLeafAll`
and `mumfordTorsionAlgClosed` are already fields of `OpenTextbookLeaves12`.

## 4. The dictionary steps, with status

| step | before | now |
| --- | --- | --- |
| D1. `Φ : ℂ^g/Λ → A_τ(ℂ)` is a homeomorphism (compact to Hausdorff), group iso; `A_τ(ℂ)` a compact topological group | docstring, STANDARD | **proved** (`IsUnif.torusHomeo`, `isTopologicalGroup`; Hausdorff by the kernel's proved `analyticPointsT2`) |
| D2. `Φ` is holomorphic with invertible differential (biholomorphic onto `A^an`) | docstring, STANDARD | **not needed**: the printed definition never mentions `Φ`. What is used is `C¹`-regularity of `F ∘ Φ`, **proved** (`Holomorphic.hasStrictFDerivAt`) |
| D3. `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = |c|² covol(Λ)`, `c = coefficient of Φ*η` | docstring | **proved** (`volume_eq_of_normalized`, `isFaltingsMetricSq_of_metrized`), with existence (`exists_isNormalizedBy`) and uniqueness (`isFaltingsMetricSq_iff`) |
| D4. The height of the Néron model is attained at a metrization, and `g = dim A` | kernel glue | proved from T35 in the kernel (`groupModel_height_eq` with `analyticUniformizationUnique_of_t35`, `uniformizationDim_of_t35`); used in `isPrintedStableHeight_of` |
| D5. `ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S})`, `⋀^g` of it = `detLattice g` | docstring, EGA IV 17.2.5 UNVERIFIED | **unchanged**, a definition-level reading in `IsPrintedStableHeight` (see §5) |
| D6. `A_τ(ℂ)^an`'s topology is `anTop` | kernel definition | definition-level reading, STANDARD: on an affine open the topology of `U(ℂ) ⊂ ℂ^n` given by generators; the kernel's own convention |
| D7. "∫ of the invariant form" = total mass of the left-invariant measure with density `|τ l|²` at `1` in algebraic coordinates | — | definition-level reading, STANDARD: definition of the integral of a smooth density in charts, plus invariance of `η` |

## 5. The algebraic step D5 (`ω = e*Ω¹`)

The kernel defines `omegaAt s` as the `𝓞_L`-span of the classes in `𝔪_ξ/𝔪_ξ²` of the specializations of
`I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})`. It sets `omega = ⋂_s omegaAt s` and `detLattice g = ⋀^g omega`. The
print's `ω_A = ε*Ω^g_{𝒩/S}` is a sheaf. Mathlib 4.35 has no sheaf of relative differentials on schemes
(c-to-printed says the same), so its Lean form can only be stalkwise: `(ε*Ω¹)_s = 𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]`
(STANDARD: the stalk of `Ω_{X/S}` is `Ω` of the local rings, and `Ω` is unchanged by localizing the base).
Its image in the generic fibre is compared with `omegaAt s` through Mathlib's `kerCotangentToTensor`:
`I/I² ≅ R ⊗_B Ω[B/R]` for a ring with a section, by `exact_kerCotangentToTensor_mapBaseChange` and
`retractionKerCotangentToTensorEquivSection`. The status of the Lean proof is recorded at the end of this
report.

## 6. Leaves and ratings

| leaf | source | rating |
| --- | --- | --- |
| `ZInQ.HeightDict.BostLowerBoundPrinted` (new; replaces `bostLowerBound`) | Bost, Sém. Bourbaki 795 (Astérisque 237, 1996); display UNVERIFIED (unchanged from height-split) | **printed form**, over a printed definition of `h`: the statement is the old leaf's with `IsStableFaltingsHeight` replaced by `IsPrintedStableHeight`. Same normalization caveat as before (Deligne's `h_D = h_F + (g/2) log π`; residual risk if Bost printed in `(i/4π)^g`). The definition-level readings are D5-D7. Locator UNVERIFIED |
| `ZInQ.HeightDict.GaudronRemondThm14Printed` (new; replaces `gaudronRemondThm14`) | Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4, p. 2060 (read by the locator audit) | **printed form**, over a printed definition of `h` (stable height, Faltings' original normalization `(i/2)^g`, which is the normalization of `IsFaltingsMetricSq`); readings D5-D7 |

No glue Prop is added: the dictionary steps D1-D4 are proved, and D5-D7 are readings of definitions.
`uniformizationLeafAll` and `mumfordTorsionAlgClosed` are existing fields, and the fold only reads them.
If a reviewer counts D5 (EGA IV 17.2.5) as a theorem step rather than a definition, both new leaves stay
"consequence" with exactly that one step as the reason.

Note: `claims.tsv` shows `gaudronRemondThm14` held by gr14-narrow, a forward-direction-only restatement.
The two pieces of work compose: gr14-narrow's narrower statement can be restated over
`IsPrintedStableHeight` in the same way, using `isPrintedStableHeight_of`.

## 7. How much the vendored machinery gives

- **Kernel and height-glue (in this base)** give the analytic topology `anTop` and its Hausdorffness
  (`analyticPointsT2`, proved). They also give continuity of analytic uniformizations, the homeomorphism
  pattern (`exists_linear_factor`), uniqueness of uniformizations, `UniformizationDim` and
  `NeronMetrizable` from T35, and T35 from `uniformizationLeafAll` and `mumfordTorsionAlgClosed` (`h38`). All
  of these were used.
- **The vendored uniformization (`BPAnalytic.Uniformization`, unif-printed's `MumfordComplexTorus`)** enters
  only through T35, for D4. The printed definition does not use it.
- **unif-topology / sga1-etale (wip/sga1-etale aa37ef8a)** build `X(ℂ)` as an analytic manifold from SGA 1 XII
  3.1. They are **not needed**: the printed metric is a measure on the topological group `A_τ(ℂ)`, normalized
  only at the identity in algebraic coordinates. So no chart atlas, no manifold structure and no integration of
  forms over charts is required. If a reviewer wants the integral over the manifold `A^an` literally, sga1-etale's
  atlas is the one to use, and D7 would become "the measure of a smooth density in every chart of that atlas";
  the proof of `volume_eq_of_normalized` would carry over.
- **Mathlib 4.35 gaps filled here**: holomorphic ⇒ strictly differentiable in several variables
  (`Holomorphic.lean`), and the volume of a uniformized compact group (`TorusVolume.lean`).

## 8. Files

- `ZInQKernel/Contrib/OneProof/HeightDictionary.lean`, `.../HeightDictionary/TorusVolume.lean`,
  `.../HeightDictionary/Holomorphic.lean` (new; `lake build ZInQKernel.Contrib.OneProof.HeightDictionary`
  succeeds).
- `scratch/height-dict/`: `log.md`, `Statements.md` (verbatim copies of the two statements, of
  `IsStableFaltingsHeight` and of `GroupModel.height`), `DischargesCheck.lean`, `discharges.txt`,
  `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`.

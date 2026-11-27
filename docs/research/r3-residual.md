# r3-residual: the step R3 ("clauses to biholomorphic") proved; three height leaves read the print's height

Task r3-residual, 2026-11-17. Base e1b31749 (wip/r3-residual). Model work only, no human review. No network:
theorem numbers recalled from memory are marked UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference), **SPECULATIVE**,
**UNVERIFIED**.

## 1. Result

**The residual step R3 is now a Lean theorem, stated without any uniformization, and the three fields
`bostLowerBoundPrinted`, `gaudronRemondThm14Printed` and `javanpeykarPrintedMapHF` are proved from leaves that
read the print's stable height: the archimedean metric is integrated over the complex manifold
`A_τ(ℂ)^an`, with its density read in every holomorphic chart.** Everything compiles with the standard axioms
(VERIFIED, §5), in the new file `ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean`
(namespace `ZInQ.R3Residual`). The only extra hypothesis is T35, through the existing textbook field
`mumfordTorsionAlgClosed` (with `uniformizationLeafAll_proof`). `SemiAbelianDescendsPerfect` and
`chevalleyPerfect` are not used.

```
DISCHARGES [OpenResearchLeaves38.bostLowerBoundPrinted] by ZInQ.R3Residual.bostLowerBoundPrinted_of_an
  still assumes: [ZInQ.R3Residual.BostLowerBoundAn, AvSplit.MumfordTorsionAlgClosed]
DISCHARGES [OpenResearchLeaves38.gaudronRemondThm14Printed] by ZInQ.R3Residual.gaudronRemondThm14Printed_of_an
  still assumes: [ZInQ.R3Residual.GaudronRemondThm14An, AvSplit.MumfordTorsionAlgClosed]
DISCHARGES [OpenResearchLeaves38.javanpeykarPrintedMapHF] by ZInQ.R3Residual.javanpeykarPrintedMap_of_an_min
  still assumes: [ZInQ.R3Residual.JavanpeykarAnMin, AvSplit.MumfordTorsionAlgClosed]
  axioms (each): [propext, Classical.choice, Quot.sound]
```

**Count.** Count-neutral after review (queue15): R3' ("étale coordinates are analytic coordinates", inside IsHolChart) remains a step, so the three new rows are GLUE like the rows they replace. (The earlier claim here of −3 GLUE is withdrawn; correction recorded on wip/leaf-fold33b, inbox 29c.)
- Bost and Gaudron–Rémond: R3 was the only deciding step. Each is now a direct instance.
- Javanpeykar had a second step, the given-degree reading (`deg_B` replaced by the degree of a given Belyi map).
  It is also removed here: `JavanpeykarAnMin` states the printed `deg_B(X)`, and `javanpeykarAnMap_of_min`
  derives the given-degree form (`deg_B ≤ d` together with `javanpeykarBound_mono`).

Against this base's `kinds.tsv`, which still rates the two Printed rows LEAF, the dry run gives
`16/18 → 17/17` (−1 GLUE, §5).

## 2. The step and how it is closed

**The step.** height-fix's `HasFormDensityAt` (PrintedStableHeight.lean:240) asks for the density `|τ l|²` in
the translated algebraic coordinates `F(p⁻¹·)`. The definition itself is Φ-free. But that these coordinates are
holomorphic charts of `A_τ(ℂ)^an` was proved only through a uniformization:
- `exists_chart` goes through `M.arch τ`;
- `chartAt_comp_hasStrictFDerivAt` takes `hΦ`.

**The holomorphic charts, defined without Φ (§2).** `IsHolChart 𝒢 τ φ` holds when:
- `φ` is a homeomorphism from an open subset of `(𝒢(ℂ)_τ, anTop)` onto an open subset of `ℂ^g`;
- at every point `q` of its domain, every algebraic coordinate system centred at `q` is a holomorphic function
  of `φ` near `φ q`, with invertible derivative at `φ q`. Such a system is `F(q⁻¹·)` with regular `fᵢ`
  vanishing at the origin and `df₁∧⋯∧df_g ≠ 0`.

This is the analytic structure of the smooth variety `A_τ` in which local algebraic (étale) coordinates are
local analytic coordinates (Serre, GAGA §2; SGA 1 XII 3.1; numbers UNVERIFIED). It is the same construction
as the vendored Paul-Lez `ComplexPoint` manifold (`CloudB3W17Hodge/.../ComplexPoint/Manifold.lean`, VERIFIED
by reading its docstring).

**Theorems.** All statements are Φ-free. The proofs use T35. All VERIFIED.

| theorem | statement |
| --- | --- |
| `exists_holChart` | for `g = dim A` and algebraic coordinates `F`, `chartAt F p` agrees near `p` with a holomorphic chart |
| `exists_holChart_at` | holomorphic charts exist at every point |
| `holChart_transition` | any two holomorphic charts are biholomorphically compatible, so `A_τ(ℂ)` with the analytic topology is a complex manifold |
| `unif_holChart` | every analytic uniformization `Φ` (kernel `IsAnalyticUniformization`, any lattice) is a local biholomorphism `ℂ^g → A_τ(ℂ)^an`, so any two uniformizations differ by biholomorphic transitions: "clauses ⇒ biholomorphic" |
| `regular_holo_in_holChart` | every regular function `f ∈ Γ(V, 𝒪_𝒢)` is holomorphic in every holomorphic chart |
| `jacobian_bounds` | local Jacobian estimate for `ℂ`-differentiable maps of `ℂ^g` (`|det_ℝ| = |det_ℂ|²`; Mathlib `addHaar_image_le_mul_of_det_lt`, `mul_le_addHaar_image_of_lt_det`) |
| `hasAnFormDensityAt_iff` | for `η ≠ 0`: density of `(i/2)^g η̃∧η̄̃` in **every** holomorphic chart ⇔ height-fix's `HasFormDensityAt` |
| `isAnMetricSq_iff`, `isAnStableHeight_iff` | the print's metric and stable height equal height-fix's |

**The print's measure (§5).** `HasAnFormDensityAt ν η p` says the following. For every holomorphic chart `φ ∋ p`
and every representation `η = l·df₁∧⋯∧df_g`, the measure `ν` has density `|τ l|²·|det D(F_p∘φ⁻¹)(φ p)|²` at
`φ p`, where `l·det D(F_p∘φ⁻¹)` is the coefficient of the invariant form `η̃` in `φ` at `p`. The proofs of the
equivalence:
- `⇒`: the algebraic chart is itself a holomorphic chart, and there the coefficient is `l`.
- `⇐`: change of variables from the algebraic chart to `φ`.

So `HasFormDensityAt` does not depend on the chart. `IsAnStableHeight` is `IsPrintedStableHeight` verbatim, with
`IsPrintedMetricSq` replaced by `IsAnMetricSq` (the measure on `A_τ(ℂ)^an` exists and every such measure has
mass `r`).

## 3. Leaves and ratings

| new leaf | replaces | rating | reason |
| --- | --- | --- | --- |
| `ZInQ.R3Residual.BostLowerBoundAn` | `bostLowerBoundPrinted` | **printed form** | Bost's bound verbatim over the stable height built as the print builds it, with the integral over the complex manifold `A(ℂ)` and densities in its holomorphic charts. Old caveats remain: display UNVERIFIED, and Deligne's normalization `h_D = h_F + (g/2) log π` |
| `ZInQ.R3Residual.GaudronRemondThm14An` | `gaudronRemondThm14Printed` | **printed form** (one other caveat below) | GR Thm 1.4 verbatim over the same height |
| `ZInQ.R3Residual.JavanpeykarAnMin` | `javanpeykarPrintedMapHF` | **printed form** | Thm 1.1.1 with the printed `deg_B(X)` (`belyiDegree`, the least degree of an `IsBelyiMap`), at `X = X₀ ×_K ℚ̄` (a specialization), over the same height |

Notes on the ratings:
- **Javanpeykar's remaining reading.** `h_Fal(Jac X)` is read as the stable height of a model `V` over `K`. This
  is the definition of the stable height over `ℚ̄`, not a step. The hypothesis "a Belyi map exists" (Belyi's
  theorem) only weakens the leaf.
- **Never stronger.** `bostLowerBoundAn_of_printed`, `gaudronRemondThm14An_of_printed`,
  `javanpeykarAnMap_of_printed` and `javanpeykarAnMin_of_map` show that each new leaf is implied by the row it
  replaces (given T35).

**Definition-level readings left.** These are readings, not theorem steps:
- R1, R2 and R4 of height-fix, unchanged.
- R3′: "the holomorphic charts of `A_τ^an` are those biholomorphic to the local algebraic coordinates". This is
  the GAGA definition of the analytic structure of a smooth variety. The file proves that these charts form a
  complex atlas, that regular functions are holomorphic in them, and that uniformizations are local
  biholomorphisms for them.

To remove even R3′, one could prove `IsHolChart` charts are the charts of the vendored `ComplexPoint` manifold
of `𝒢 ×_{𝓞_L,τ} Spec ℂ`. That needs a bridge `Pts τ ≃ CPt(𝒢_τ)` (homeomorphism and evaluation), which is
not done (§6).

**Gaudron–Rémond's other caveat (secondary step, now proved in Lean).** The leaf bounds `isogDeg φ = #ker(φ)(K̄)`,
while GR bound the degree of `φ`. A consequence of the print needs `#ker(K̄) ≤ deg φ`. When this report was written,
that step was not proved in Lean. It now is (gr-isogdeg, `docs/research/gr-isogdeg.md`). In
`ZInQKernel/Contrib/OneProof/GaudronRemondIsogDeg.lean`, `ZInQ.GRIsogDeg.isogDeg_le_finDeg` proves
`isogDeg φ ≤ finDeg φ` for every isogeny over any field, and `ZInQ.GRIsogDeg.isogDeg_eq_finDeg` proves equality in
characteristic 0. Here `finDeg φ` is Mathlib's `Scheme.Hom.finrank` of `φ` at the generic point of the target, which
is `[K(A) : K(B)]`.

The bundle field is now `gaudronRemondThm14Printed`, of type `ZInQ.GR14Printed.GaudronRemondThm14Printed`
(gr14-printed, fork PR #209; `OpenResearchLeaves79`), not this report's `gaudronRemondThm14An`. That field also
bounds `isogDeg`, over number fields, and its isogenies satisfy `IsIsogeny` by
`ZInQ.GR14Printed.isIsogenyPrinted_iff`, so `isogDeg_eq_finDeg` applies to them. The degree in the field is
therefore the degree of the isogeny as a finite morphism, and the degree no longer separates the field from the
print. What is left for the field is what `docs/one-proof/OPEN.md` lists for it: the p. 2062 locator for isogenies
and their degree (UNVERIFIED: no reading covers it), the specialization `K′ = k`, the split of the printed couple
into two isogenies, and the readings named in its flag. The bridges in §4 of `GaudronRemondIsogDeg.lean` are stated
for the retired forms `ZInQ.R3Residual.GaudronRemondThm14An` and `ZInQ.HeightFix.GaudronRemondThm14Printed`; no Lean
theorem yet states the current field with `finDeg`.

## 4. Files

- `ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean` (new; imports
  `ZInQKernel.Contrib.OneProof.JavanpeykarRebase`; no `sorry`, no `axiom`, no code that runs at build time).
- `scratch/r3-residual/`:
  - `R3.lean` (development copy);
  - `log.md`;
  - `Discharges.lean`, `discharges.txt`;
  - `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`, `FoldDryRun-compile.txt`;
  - build logs.

## 5. Checks (VERIFIED)

- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.AnalyticStableHeight`:
  success, 14274 jobs.
- `#discharges` (output in `scratch/r3-residual/discharges.txt`): the three discharges in §1, plus the variants
  `*_of_an'` that take `uniformizationLeafAll` as a hypothesis.
- Autofold spec `scratch/r3-residual/autofold.json`. Each of the three fields gets one new leaf of kind
  published, flagged unread.
  - `--dry-run`: `strict count: 16/18 on 34 -> 17/17 on 34; strictest 16/18 -> 17/17`.
  - The generated module (first line stripped) compiles, and `HDec.HSyn.sixContactMin_of_open56` has the
    standard axioms.
- **Fold order.** This contribution is independent of semiab-descend's `chevalleyPerfect`. The three fields are
  in the current `OpenResearchLeaves38` (TailZ62).

## 6. What remains

- GR: `#ker(K̄) ≤ deg` (§3).
- Optional: identify `IsHolChart` with the vendored `ComplexPoint` atlas (removes reading R3′).
- Optional: `pazukiCor13Upper` was rated GLUE on the same "clauses ⇒ biholomorphic" ruling (OPEN.md). Its
  weak `IsUniformization` hypothesis is over `CPts`, not `𝒢.Pts`, so `unif_holChart` does not apply directly.
  It needs the same argument on `CPts A σ`. Not attempted.

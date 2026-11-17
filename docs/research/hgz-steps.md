# hgz-steps: `hGZ` from Gross–Zagier for a morphism of curves `π : X₀(N) → E`, with D1 and D2 proved in Lean

Status: research note (task hgz-steps, 2026-11-17). Branch `wip/hgz-steps`, base `main` 222c98bf, with
`origin/wip/leaf-fold33b` (db99b5b4) and `origin/wip/gz-dict2` (4fd8ddd2) merged.

New Lean files:
- `ZInQKernel/Contrib/OneProof/GrossZagierScheme.lean`: the leaf and the bridge.
- Helpers in `ZInQKernel/Contrib/OneProof/GrossZagierScheme/`: `Core.lean`, `EpsD.lean`, `Model.lean`,
  `PointTau.lean`.

Nothing else under `ZInQKernel/` was edited. Scratch copies, checks and log: `scratch/hgz-steps/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no copy of Gross–Zagier, Hartshorne or Shimura.
Literature locators are UNVERIFIED unless they come from the queue9 reading quoted in the task brief (GZ V §2,
p. 310; IV (0.4), p. 268).

---

## 0. Main result

**`hGZ` is now a direct instance of the print, with the dictionary steps D1 and D2 proved in Lean.**

The new leaf is `ZInQ.GZSch.GrossZagierCurveCd`. It is Gross–Zagier (Invent. Math. 84, Thm I.6.3 and V §2
Thm 2.1, positive constant forgotten), stated for a modular parametrization `π : X₀(N) → E` that is a genuine
morphism of `ℚ`-schemes:

- `X₀(N)` is a normal, proper, integral scheme `X` of dimension 1 over `ℚ`, with function field
  `ι : K(X) ≃ ℚ(j, j_N)` (FLT's `modularFunctionField`, inside `ℚ((q))`).
- `E` is the projective scheme `ESch E = Proj ℚ[X, Y, Z]/(F_E)` (Tau Ceti's graded coordinate ring, Mathlib's
  `Proj`).
- `π : X ⟶ ESch E` is any nonconstant morphism with `π(∞) = O`. The arbitrary covering is the one fixed in V §2,
  p. 310, so strong Weil is not assumed (D3 is cleared by the reading).
- The Heegner points are `ℂ`-points `x_r : Spec ℂ ⟶ X`, namely the points `τ_r`.
- The twist and the Heegner hypothesis use `ε_D`, the Kronecker symbol `(D/·)`.

The bridge is:

```lean
theorem ZInQ.GZSch.grossZagierAlgOptCd_of_curve :
    ZInQ.GZSch.GrossZagierCurveCd → ZInQ.GZAlg.GrossZagierAlgOptCd     -- the binder hGZ of frozenTarget
```

It compiles with no `sorry` and axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`scratch/hgz-steps/FoldCheck-output.txt`). Every step between the print and the old Lean form is a Lean proof:

| step | content | Lean |
| --- | --- | --- |
| D1 | a `ℚ`-embedding `φ^* : ℚ(E) → ℚ(X₀(N))` is a morphism `π : X ⟶ ESch E` whose generic point is `φ^*` (Hartshorne I.6.8/I.6.12) | `Core.exists_extension`, via Jacobian-Challenge's `Scheme.exists_hom_of_valuationRing_stalk` |
| model | `ℚ(X₀(N))` is finite over `ℚ(j)`, so it has a normal proper model over `ℚ` | `Model.exists_model`: `T ↦ j`, the vendored `Φ_N` (monic, `Φ_N(j, j_N) = 0`), cloud-w07's `NormalModelOfFunctionFieldQ_proof` |
| stalks | a normal curve has valuation rings as local rings | `valuationRing_stalk_of_normal` (Mathlib's DVR TFAE) |
| D2 | at the `ℂ`-point `τ`, the value of `π` (as a point of `E(ℂ)`) is gz-dict2's `modPt` of the plane-model functions `P(j, j_N)/Q(j, j_N)` | `ptOf_eq_modPt` |
| points | the point `τ` exists on every proper model: the center of the place `ord_τ` | `exists_pointAt`; `PointTau.Otau`, `evTau` |
| uniqueness | the point `τ` is unique, so the leaf's `∀ x_r` ranges over one point | `isPointAt_unique` |
| cusp | `π(∞) = O` and `π` nonconstant | `exists_cusp`, `cusp_not_mem_chart`, `generic_mem_chart` |
| `ε_D` | `ε_D(n) = (n / |D|)` for `D < 0`, `D ≡ 1 (mod 4)` | `HGZSteps.epsD_eq_jacobiSym` (quadratic reciprocity) |
| D3 | not needed: GZ V §2 fixes an arbitrary `π` with `π(∞) = 0` (queue9 reading) | the leaf has no optimality hypothesis |

**Rating of the new leaf: LEAF, printed form (direct instance) over genuine definitions** (§3). Proposed count:
`hGZ` goes from GLUE ("pending reading", fold33-review) to LEAF, so **GLUE −1 in both columns**, with no glue added.
The proposed kinds row is `scratch/hgz-steps/kinds-row.tsv`.

## 1. The leaf

`ZInQ.GZSch.GrossZagierCurveAt E` (the `C_d` form `GrossZagierCurveCd` restricts `E` to the short models in the
isogeny class of `C_d`, `d ≡ 5 (mod 8)` squarefree, as before):

```lean
∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 → (∀ n ≠ 0, coeff f n = E.LFunction n) →
∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec ℚ), IsProper sX → IsNormalScheme X →
  topologicalKrullDim X = 1 →
∀ ι : X.functionField ≃+* X0Field N,
∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX → (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
  (∀ p, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange) →
∀ D β, IsOddImagFundDisc D → D < -4 → (∀ p prime, p ∣ N → epsD D p = 1) → 4N ∣ D − β² →
∀ R τ, IsHeegnerPointReps N D β τ →
∀ x : R → (Spec ℂ ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
∀ K δ ιK (as before), ∀ n ≠ 0, ∀ y : E(K), ιK(y) = n • Σ_r ptOf E (x r ≫ π) →
∀ F G, IsEntireCont (coeff f) 2 F → IsEntireCont (coeff f · epsD D ·) 2 G →
  ∃ κ > 0, (F G)'(1) = κ ĥ(y)
```

The objects are all genuine definitions:

| object | definition | meaning |
| --- | --- | --- |
| `ESch E` | `Proj (E.toProjective.grading)` | `E ⊂ ℙ²_ℚ` as a scheme; `toSpecQ E` is proper (Mathlib's `Proj.toSpecZero`, finite type) |
| `chartZ E` | `Proj.awayι` at `Z` | the open chart `D₊(Z) = Spec A_(Z)`; its complement in `E` is `V₊(Z, X³) = {[0 : 1 : 0]} = {O}` |
| `ptOf E s` | `(a, b)` if `s = Spec(F/Zⁿ ↦ F(a, b, 1)) ≫ chartZ`, else `O` | the point of `E(ℂ)` of a `ℂ`-point of `ESch E` |
| `IsCuspInfty N ι p` | every function regular at `p` has `ord_q ≥ 0` | `p` is the cusp `∞` (`q` is the local parameter at `∞`, width 1) |
| `IsPointAt N ι τ x` | every `g` regular at `x` takes at `x` the value at `τ` of `P(j, j_N)/Q(j, j_N)`, for every representation `ι(g) = P/Q` (a limit at the finitely many indeterminacy points) | `x` is the image of `τ` under the uniformization `ℍ → X₀(N)(ℂ)` |
| `epsD D n` | Kronecker symbol: `χ₈(D)` at 2, Legendre `(D/p)` at odd `p`, completely multiplicative | `ε_D`, the quadratic character of `ℚ(√D)` |

## 2. The proofs (`scratch/hgz-steps/log.md` has the compile record)

**Core** (`GrossZagierScheme/Core.lean`):
- `specQ_ext`: `Spec ℚ` is subterminal, so "over `ℚ`" is automatic.
- `chartHom E a b h : A_(Z) →+* K` is the `K`-point `(a, b)`. It is natural in `K` (`comp_chartHom`).
- **D1 (`exists_extension`).** For an integral `X` with valuation-ring stalks and `u : A_(Z) → K(X)`, there is
  `π : X ⟶ ESch E` with `Spec K(X) → X → E` equal to `Spec K(X) → D₊(Z) → E`.
- The key lemma has two directions:
  - `mem_range_of_mem_chart`: if `π(p) ∈ D₊(Z)`, the coordinates are regular at `p`. This lifts through the open
    immersion.
  - `fromSpecStalk_comp_eq`: if the coordinates are regular at `p`, `π` near `p` is the chart map. This is
    uniqueness in the valuative criterion, since `E` is separated.
- `comp_eq_of_factor`, `ptOf_chart` and `ptOf_eq_zero` give the value at a `ℂ`-point.

**Model** (`GrossZagierScheme/Model.lean`):
- `ℚ(T) → ℚ(X₀(N))`, `T ↦ jq`, is injective because `ord jq = −1`.
- `jq(q^N)` is integral over `ℚ(T)`. The vendored FLT theorem `exists_phiIrreducible_of_finrank_eq` (with
  `finrank_adjoin_jqN_eq_dedekindPsi`) supplies the monic `Φ_N`.
- `ℚ(T)(jq(q^N)) = ⊤` by `adjoin_le_subfield`, so `ℚ(X₀(N))` is finite over `ℚ(T)`.
- Then `NormalModelOfFunctionFieldQ_proof` applies.

**The place `ord_τ`** (`GrossZagierScheme/PointTau.lean`):
- `ratFn_rep_congr`: two representations `P/Q` of the same element give the same function off a discrete set
  (`q`-expansions and the identity theorem).
- `Otau τ` is a valuation subring of `ℚ(X₀(N))`. Its elements are the `g` whose modular function has meromorphic
  order `≥ 0` at `τ` (Mathlib's `meromorphicOrderAt` calculus).
- `evTau τ : Otau τ →+* ℂ` (limits) is a local ring map.

**Bridge** (`GrossZagierScheme.lean`):
- `exists_center`: a valuation ring of `K(X)` containing `ℚ` has a center on a proper `X`, with a local
  domination `𝒪_{X,p} → O` (valuative criterion, existence).
- `exists_pointAt` takes the center of `ord_τ`, `x_τ = Spec(ev_τ ∘ θ) ≫ fromSpecStalk p`, and checks
  `IsPointAt` on germs.
- `exists_cusp` does the same with the place `ord_q`.
- `mem_range_of_tendsto`: a function with a finite limit at `τ` is regular at `x_τ`. The local ring is a valuation
  ring, and `ev` kills its maximal ideal.
- `ptOf_eq_modPt` follows gz-dict2's `modPt_plane_cases`:
  - finite limits: regular coordinates, then the chart map, with value `(x₀, y₀)`;
  - pole: `π(x_τ) ∉ D₊(Z)`, so `O`.
- `grossZagierPlaneOptCd_of_curve` and `grossZagierAlgOptCd_of_curve` follow. They reuse gz-dict2's bridge to
  `GZAlg.GrossZagierAlgOptCd` (D2 analytic: `modPt_eq_ratFn`).

## 3. Rating of `GZSch.GrossZagierCurveCd`

**LEAF, printed form (direct instance).** Reasons:

- **The statement is the print's.** GZ's `π : X₀(N) → E` is a nonconstant morphism of curves over `ℚ` with
  `π(∞) = 0`; here it is a morphism of `ℚ`-schemes. The Heegner points are the points `x_r` of `X₀(N)(ℂ)`, and the
  sum `Σ_r π(x_r)` is `Tr_{H/K} π(x)` (gz-moduli's `IsHeegnerPointReps`, unchanged). The L-functions are those of
  `f` and `f ⊗ ε_D`, with `L(E/K, s) = L(f, s) L(f ⊗ ε, s)` (IV (0.4), p. 268).
- **It is weaker than the print**: the constant becomes `∃ κ > 0`, and `y = n y_K` (`ĥ(n y_K) = n² ĥ(y_K)`).
- **It is not stronger.**
  - Every `(X, ι)` is isomorphic to the canonical model with its identification `K(X₀(N)) = ℚ(j, j_N)`. A normal
    proper curve is determined by its function field (Hartshorne I.6.7–6.9, II.6.7, UNVERIFIED numbers), and every
    condition is stated relative to `ι`.
  - The `x_r` are unique (`isPointAt_unique`, VERIFIED).
  - The hypothesis on `∞` can only shrink the set of admissible `π`.
- **It is not vacuous.** The bridge constructs every hypothesis (model, `π`, cusp, points `τ_r`) from the data
  of the old leaf.

**Definitional readings, not steps.** Two readings remain, and both are definitions:

1. **The canonical model.** `X₀(N)_ℚ` is the curve with function field `ℚ(j, j_N)` (Shimura 1971 §6.7, UNVERIFIED).
2. **The point `τ`.** `IsPointAt` is the uniformization: a rational function corresponds to the modular function
   with its `q`-expansion, and the point `τ` evaluates it at `τ`.

**Not formalized, textbook.** The Kronecker symbol `(D/p)` is the splitting character of `p` in `O_K` (Dedekind–
Kummer; Neukirch I.8, UNVERIFIED). Proved in Lean:
- the arithmetic side for odd `p ∤ D` (`epsD_eq_one_iff_isSquare`: `ε_D(p) = 1` iff `D` is a square mod `p`);
- the arithmetic side at `p = 2` (`epsD_two_eq_one_iff`: `ε_D(2) = 1` iff `D ≡ 1 (mod 8)`).

If GZ define `ε` by splitting, this identification is the textbook definition of `χ_K` for a fundamental
discriminant.

**Count.** The binder `hGZ` changes type. fold33-review's D1–D3 are proved (D1, D2) or cleared by the reading
(D3). `hGZ` becomes LEAF, **GLUE −1**, with no new glue.

## 4. Fold (manual: `hGZ` is a binder, not a bundle field)

- `scratch/hgz-steps/fold-spec.md`: import `GrossZagierScheme`, retype `hGZ` to `ZInQ.GZSch.GrossZagierCurveCd`,
  insert `grossZagierAlgOptCd_of_curve`.
- `scratch/hgz-steps/FoldCheck.lean`: `ZInQ.HGZSteps.frozenTarget_hgz` is `frozenTarget` with that change. Its
  axioms are standard (`FoldCheck-output.txt`, VERIFIED).
- `scratch/hgz-steps/autofold.json`: the spec format, field `hGZ`, one published leaf with kind and flag.
  autofold.py does not handle binders (as for gz-dict2).
- `scratch/hgz-steps/kinds-row.tsv` and `locators-row.md`: the proposed rows (not applied).
- `#discharges` output: `scratch/hgz-steps/Discharges-output.txt` (§5).

## 5. Checks

DISCHARGES_PLACEHOLDER

## 6. What remains

- The integrator's fold (§4). It needs gz-dict2's `GrossZagierPlane` modules, which this branch merges.
- Optional: the splitting description of `ε_D` (Dedekind–Kummer for `ℤ[(1+√D)/2]`), if a reviewer reads GZ's `ε` as
  defined by splitting.

# h33-fix: TYZ Theorem 3.3 as a leaf over TYZ's algebraic identification `i₀`

Task h33-fix, 2026-11-17. Base origin/main `222c98bf`, with h33-dict (`d489fc13`) merged. Scratch and log:
`scratch/h33-fix/` (`log.md`). Contribution: `ZInQKernel/Contrib/OneProof/TYZThm33Alg.lean` and the helper
`ZInQKernel/Contrib/OneProof/TYZThm33Alg/ThetaJ.lean`. Nothing else under `ZInQKernel/` was edited, apart from
h33-dict's `Contrib/OneProof/TYZThm33.lean`, which came in through the merge unchanged.

Marks: **VERIFIED** means read in a source, computed, or compiled. **STANDARD** means a published theorem with an
exact reference. **SPECULATIVE** means an assessment. Theorem numbers given from memory are **UNVERIFIED** (this host
has no network).

## 1. Result

**`h33` is discharged by a new leaf, `ZInQ.H33Fix.TYZThm33Alg`.** It is TYZ Theorem 3.3 stated for TYZ's own
identification `i₀ : (X₀(32), ∞) ≅ (A, O)`, where `i₀` is an **algebraic isomorphism over `ℚ`**, given by its
pull-back on function fields. Every dictionary step between this leaf and what the consumer reads is a Lean proof.
The main theorem, with standard axioms (VERIFIED, compiled):

```lean
theorem ZInQ.H33Fix.tyzThm33_of_alg (hCM : T5Glue.ShimuraMainCM) (h : ZInQ.H33Fix.TYZThm33Alg) :
    ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33
```

`hCM` comes from the existing `frozenTarget` argument, as `HCMDict.shimuraMainCM_of_printed hCM`.

**Target met: `h33` goes from GLUE to LEAF (−1 GLUE), and no field is added.** The fold replaces the binder `h33` with
`h33a : TYZThm33Alg` (§5).

**The deciding step of the review is now proved.** The 11-16 review rated h33-dict's `TYZThm33Printed` GLUE because it
read `i₀` through pullbacks in the analytically defined field `IsRatModFn 32`. Identifying that reading with TYZ's
algebraic `i₀` needs the `q`-expansion principle, GAGA, uniformization and a degree argument. The new leaf avoids
all four:

* `i₀` is a `ℚ`-isomorphism of function fields, `φ = i₀^* : ℚ(A) → ℚ(X₀(32))`, bijective, with `ord_q φ(x) < 0`
  (`IsX0IsoAlg`).
* `ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))` is the vendored FLT definition `ModularCurve.modularFunctionField 32`. It is the
  same object as `GZAlg.X0Field` in gzopt-dict's Gross–Zagier leaf.
* `ℚ(A)` is Mathlib's `WeierstrassCurve.Affine.FunctionField`.

The step the review could not accept, that the eta model is such an `i₀`, is now a Lean theorem:

```lean
theorem ZInQ.H33Fix.isX0IsoAlg_eta : ZInQ.H33Fix.IsX0IsoAlg ZInQ.H33Fix.phiEta
```

Its essential content is that **`φ^*_η` is onto `ℚ(j, j₃₂)`**: `jq` and `jq(q³²)` are rational functions of the eta
model's `x, y`. This takes the place of the degree argument.

## 2. The leaf (`TYZThm33Alg.lean` §1)

```lean
def IsX0IsoAlg (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32) : Prop :=
  Function.Bijective φ ∧ ((φ (genX curveA) : LaurentSeries ℚ)).order < 0

def TYZThm33Alg : Prop :=
  ∀ φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32, IsX0IsoAlg φ →
  ∀ X Y : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Y →
    HasQExp X (φ (genX curveA)) → HasQExp Y (φ (genY curveA)) →
  ∀ w : ℕ → PtA,
    (∀ n, ∀ hn : n % 8 = 5, Squarefree n → toC (w n) = ptOf X Y (tyzForm n hn).tauH) →
    (∀ n, ∀ hn : n % 8 = 7, Squarefree n → toC (w n) = ptOf X Y (tyzForm7 n hn).tauH) →
    TYZThm33EpsAfter (zOfLift w)
```

The conclusion `TYZThm33EpsAfter` is h33-dict's transcription of the display at L1296–1311, with `ε` chosen after
`Φ` and `χ`. It is unchanged.

* **`i₀`** (L1173–1174, re-read 11-17, VERIFIED): TYZ write that `A` is isomorphic to `(X₀(32), ∞)` and fix an
  identification `i₀`.
  * A morphism of smooth projective curves over `ℚ` is the same as a `ℚ`-embedding of function fields, and it is an
    isomorphism iff the embedding is onto (Hartshorne I.6.12, UNVERIFIED number). This is the same dictionary step D1
    that fold33-review recorded for `hGZ`.
  * `i₀(∞) = O` iff `ord_q i₀^*(x) < 0`, since `q` is the local parameter at `∞`.
  * So `IsX0IsoAlg φ` says exactly that `φ = i₀^*` for an isomorphism `(X₀(32), ∞) ≅ (A, O)` over `ℚ`.
  * The leaf is stated for every such `i₀`. TYZ fix one, and the display does not depend on the choice: the two
    choices differ by `±1`, and the sign is absorbed in `ε`.
* **Evaluating `i₀` at `P_n`.** `X = x∘i₀` and `Y = y∘i₀` are the holomorphic functions on `ℍ` with `q`-expansions
  `φ(x)`, `φ(y)`.
  * They are holomorphic because `i₀⁻¹(O) = {∞}` is a cusp.
  * **They are determined by `φ`.** `eq_of_hasQExp` (proved) says that two holomorphic functions on `ℍ` with the
    same `q`-expansion are equal, by the identity theorem.
  * This settles, for this leaf, the step D2 that fold33-review left open for `hGZ`. Junk values at poles cannot
    occur, since `X` and `Y` have no poles on `ℍ`.
* **Non-vacuity** (`tyzThm33Alg_hyps_satisfiable`, proved given `hCM`). There is a `φ` with `IsX0IsoAlg φ` (the eta
  model), there are `X, Y` (x0-32's `xC, yC`), and there is an algebraic `w` (the Heegner points). The `ℓ`
  hypothesis inside `TYZThm33EpsAfter` needs TYZ Thm 1.1, as before.

### Rating of the new leaf

**`TYZThm33Alg`: printed form (kind published, LEAF).** The reasons:

* It is TYZ's display for TYZ's `i₀`, and `i₀` is now an algebraic isomorphism over genuine definitions: Mathlib's
  function field of `A`, and FLT's `ℚ(j, j₃₂)`.
* The points are TYZ's `z_n = f_n(P_n)` read through the uniformization of `ℍ`, with `X, Y` determined by `i₀`.
* The quantifier order is the printed one.
* The weakenings are h33-dict's, and each makes the leaf weaker, never stronger:
  * `𝒫` is existential, and its coefficient is forgotten;
  * only `n ≡ 5, 7`;
  * `ℓ` is any sign choice of `𝓛`.

Readings that remain. None of them is a gap between the leaf and Lean; they are readings of TYZ's own objects:

1. **D1**, the equivalence between function fields and curves (Hartshorne I.6.12, UNVERIFIED number). `hGZ` relies on
   the same step.
2. **`X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n`** (L1191–1193, VERIFIED read). TYZ's `X_U` is an adelic double coset;
   h33-sign's `Iso.lean` checked the fixed points. Stating the leaf on `X_U` itself would need adelic Shimura
   curves, which the tree does not have.
3. **The sign of `[i]`** in `f₀∘[i]`, with `α = −i` at L1564–1566. This comes from h33-sign; with the other sign the
   statement is false.
4. **The model `y² = x³ + 4x`** for TYZ's `2y² = x³ + x`, through the explicit `ℚ`-isomorphism `(x, y) ↦ (2x, 4y)`:
   `16(2y² − x³ − x) = (4y)² − (2x)³ − 4·(2x)`. The whole kernel uses this convention.

The readings are of arXiv v1. **The journal version (Asian J. Math. 21 (2017)) has not been checked.** No human has
reviewed the paper. A strict reviewer may record item 1 as "printed form through a dictionary", as fold33-review did
for `hGZ` (SPECULATIVE).

## 3. The dictionary proofs (all VERIFIED, compiled, standard axioms)

| step | Lean (namespace `ZInQ.H33Fix`) | file |
|---|---|---|
| `E₄ = ½(θ₂⁸+θ₃⁸+θ₄⁸)`, `E₆ = ½(θ₃⁴+θ₄⁴)(θ₂⁴+θ₃⁴)(θ₄⁴−θ₂⁴)` | `e4T_eq`, `e6T_eq` | ThetaJ |
| `j = 1728E₄³/(E₄³−E₆²)` in theta constants | `j_theta` | ThetaJ |
| `j(τ)·jDen(x,y) = jNum(x,y)`, `jDen ≠ 0` | `j_eta` | ThetaJ |
| `j(32τ)·j32Den(x) = j32Num(x)`, `j32Den ≠ 0` | `j32_eta` | ThetaJ |
| `q`-expansions of `x, y` on all of `ℍ` | `hasSum_xq`, `hasSum_yq`, `rz_of_hasSum` | TYZThm33Alg §2, §5 |
| transfer of polynomial identities to `ℚ((q))` | `rz_poly2`, `jq_rel`, `jq32_rel` | §3–§4 |
| `ℚ(j, j₃₂) ⊆` every subfield containing `x, y` | `x0Field_le` | §4 |
| `x, y ∈ ℚ(j, j₃₂)` | `xq_mem`, `yq_mem` (the proved `gamma0QExpansion_proof`) | §5 |
| curve equation, `ord_q x < 0` | `wEq_eta`, `xq_order` (`order_neg_of_unbounded`) | §5 |
| `φ^*_η` bijective with a pole at `∞` | `phiEta`, `isX0IsoAlg_eta` | §5 |
| `X, Y` determined by `φ` | `eq_of_hasQExp` | §1.1 |
| `ε` before `Φ`, CM points (h33-dict, reused) | `tyzThm33_of_epsAfter`, `tyzProp324Used_of`, `toC_heegnerPt` | TYZThm33.lean |
| the contribution | `tyzThm33_of_alg` | §6 |

How the surjectivity proof works:

* **Eisenstein series.** `½(θ₂⁸+θ₃⁸+θ₄⁸)` and `½(θ₃⁴+θ₄⁴)(θ₂⁴+θ₃⁴)(θ₄⁴−θ₂⁴)` are modular forms of level one, weights 4
  and 6.
  * Invariance under T follows from `θ₃(τ+1) = θ₄`, `θ₄(τ+1) = θ₃` and `θ₂(τ+1) = e^{πi/4}θ₂`.
  * Invariance under S follows from Mathlib's `jacobiTheta₂_functional_equation` at `z = 0, 1/2, τ/2`.
  * Mathlib's `slash_action_generators_SL2Z` then gives all of `SL₂(ℤ)`.
  * Mathlib's spaces of weight 4 and 6 have rank one. Both sides tend to 1 at `i∞`, so they are equal.
  * Mathlib's `Δ = (E₄³ − E₆²)/1728` then gives `j` in theta constants.
* **Landen.** The jacobi-lambda identities (`landen_two/three/four/three_four`, `jacobi_quartic`) and the kernel's
  `x = 2θ₃(16τ)/θ₂(16τ)` and `y = −θ₂(4τ)²/θ₂(16τ)²` express `θ(τ)⁴` (through level `2τ`, then `4τ`) and `θ(32τ)⁴`
  (through level `16τ`) as `θ₂(16τ)^k` times polynomials in `x, y`.
  * `j(τ)` turns out even in `θ₂(2τ)²`, and `j(32τ)` even in `θ₄(16τ)²`. That is why `y`, and not `√y`, appears.
* **`q`-expansions.** The identity `j·D(x,y) − N(x,y) = 0` on `ℍ` passes to `ℂ((q))` by FLT's uniqueness of
  `q`-expansions (`Rz.eq_zero`), and back to `ℚ((q))` because `coeffEmb` is injective. Hence `jq = N/D ∈ ℚ(x,y)`,
  and in the same way `jq(q³²) ∈ ℚ(x,y)`. So `ℚ(j, j₃₂) ⊆ ℚ(x,y) ⊆ range φ^*_η`.

Numerical check before the Lean work (VERIFIED, `scratch/h33-fix/py/theta_j_check.py`, double precision, 3 points of
`ℍ`):
* the `E₄` and `E₆` identities hold to about `1e-15`;
* the `j(τ)` and `j(32τ)` formulas hold with relative error at most `5e-7`, the size expected from the precision.

## 4. Lean outputs (VERIFIED)

* `lake build ZInQKernel.Contrib.OneProof.TYZThm33Alg` succeeds (`scratch/h33-fix/build-output.txt`). `jq_rel` and
  `jq32_rel` need `maxHeartbeats 4000000`: the defeq check of the `CommRing (LaurentSeries ℂ)` instance paths is
  slow, and the module takes about 3 minutes.
* `#discharges` (`scratch/h33-fix/Discharges.lean`, output in `discharges-output.txt`):
  ```
  DISCHARGES [h33] by ZInQ.H33Fix.tyzThm33_of_alg
    still assumes: [T5Glue.ShimuraMainCM, ZInQ.H33Fix.TYZThm33Alg]
    axioms: [propext, Classical.choice, Quot.sound]
  ```
  `T5Glue.ShimuraMainCM` is supplied in the fold by `HCMDict.shimuraMainCM_of_printed hCM`, from the existing binder
  `hCM`. The `#print axioms` lines for `tyzThm33_of_alg`, `isX0IsoAlg_eta`, `eq_of_hasQExp`,
  `tyzThm33Alg_hyps_satisfiable`, `j_eta` and `j32_eta` all show the standard three axioms.
* The manual fold is checked in `scratch/h33-fix/FoldCheck.lean` (output in `foldcheck-output.txt`):
  * `frozenTarget_h33Alg` has the binders of `frozenTarget` at `222c98bf`, with `h33` replaced by
    `h33a : TYZThm33Alg`;
  * it compiles with standard axioms;
  * `frozenTarget_h33Alg_eq` shows that it is `rfl`-equal to `frozenTarget … (tyzThm33_of_alg (shimuraMainCM_of_printed hCM) h33a) …`.

## 5. Fold (for the integrator)

`h33` is a plain argument of `frozenTarget`, not a bundle field, so `autofold.py` does not apply (h33-dict recorded
the refusal). The spec is in `scratch/h33-fix/autofold.json`, and the new kinds row is in
`scratch/h33-fix/kinds-row.tsv`. The steps:

1. Merge h33-dict's `ZInQKernel/Contrib/OneProof/TYZThm33.lean`, which the new file imports.
2. In `Main.lean`, add `import ZInQKernel.Contrib.OneProof.TYZThm33Alg`.
3. Replace the binder `(h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)` with `(h33a : ZInQ.H33Fix.TYZThm33Alg)`.
4. Replace the argument `h33` of `ThetaWP8.tyzThm35ReadingA_noHX` with
   `(ZInQ.H33Fix.tyzThm33_of_alg (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33a)`.
5. In `kinds.tsv`, row `frozenTarget h33` (consequence, GLUE/GLUE) becomes `frozenTarget h33a`: published, LEAF/LEAF,
   with the flag "unread: journal version not checked…" (the full text is in `kinds-row.tsv`).

**GLUE count: −1. No new field.**

Proposed `locators.md` row: TYZ Thm 3.3 is arXiv:1411.4728v1, Period7.tex L1296–1311 (display, re-read 11-17), with
the set-up at L1173–1174 (`A ≅ (X₀(32), ∞)`, "Fix an identification `i₀`") and L1195–1198 (`f_n`). The journal page
is UNVERIFIED.

## 6. What remains

* The four readings of §2, items 1–4. None can be turned into Lean with the tree's current definitions: there is no
  adelic `X_U`, and no theorem identifying morphisms of curves with field embeddings.
* No human has reviewed TYZ's paper, and the journal version has not been checked.

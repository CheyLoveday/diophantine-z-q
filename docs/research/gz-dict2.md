# gz-dict2: the dictionary steps D1–D3 between Gross–Zagier's φ and the Lean leaf `hGZ`

Status: research note (task gz-dict2, 2026-11-16/17), branch `wip/gz-dict2`, base wip/leaf-fold33b 943f1775
(origin/main c1e4ed1b is already an ancestor, so no merge was needed). New Lean files:
`ZInQKernel/Contrib/OneProof/GrossZagierPlane.lean` (the new leaf, D2 and the bridge) and the helper
`ZInQKernel/Contrib/OneProof/GrossZagierPlane/Extension.lean` (D1) and
`ZInQKernel/Contrib/OneProof/GrossZagierPlane/OptimalUnique.lean` (for D3). Nothing else under `ZInQKernel/` was
edited.
Scratch, checks and log: `scratch/gz-dict2/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with an
exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Gross–Zagier, Hartshorne
or Shimura: **every literature locator below is UNVERIFIED** (from memory).

---

## 0. Main result

fold33-review re-flagged `hGZ : GZAlg.GrossZagierAlgOptCd` as pending reading because three dictionary steps
between Gross–Zagier's morphism `φ : X₀(N) → E` and the Lean statement were not proved in Lean (D1 function fields
versus morphisms, D2 values through `q`-expansions, D3 optimality). Result:

* **D2 is proved in Lean**, and the leaf is restated so that it no longer needs it. The new leaf
  `ZInQ.GZDict2.GrossZagierPlaneOptCd` gives `φ` by `φ^* : ℚ(E) →ₐ[ℚ] ℚ(X₀(N)) = ℚ(j, j_N)` as before, but the
  value of `φ` at `τ ∈ ℍ` is now read on the plane model `Φ_N(X, Y) = 0` of `X₀(N)`: it is the value of the
  rational map `(Px/Qx, Py/Qy)` at the point `(j(τ), j(Nτ))` (limits at points of indeterminacy), for any
  representation `φ^*(x) = Px(j, j_N)/Qx(j, j_N)`, `φ^*(y) = Py(j, j_N)/Qy(j, j_N)`. The auxiliary functions
  `X, Y : ℍ → ℂ` are gone. The bridge to the old leaf, which is what the chain reads, is proved (VERIFIED,
  standard axioms):

  ```lean
  theorem ZInQ.GZDict2.grossZagierAlgOptCd_of_plane :
      ZInQ.GZDict2.GrossZagierPlaneOptCd → ZInQ.GZAlg.GrossZagierAlgOptCd
  theorem ZInQ.GZDict2.grossZagierFormulaCd_of_plane :
      ZInQ.GZDict2.GrossZagierPlaneOptCd → ZInQ.GZHL3.GrossZagierFormulaCd
  ```

  Its core is D2 (`eventuallyEq_ratFn`): a meromorphic `X` on `ℍ` with `q`-expansion `x = P(jq, jq(q^N))/Q(jq, jq(q^N))`
  equals `P(j(τ), j(Nτ))/Q(j(τ), j(Nτ))` on a punctured neighbourhood of every point. Hence
  `modPt E X Y τ = modPt E (ratFn Px Qx) (ratFn Py Qy) τ` for every `τ` (`modPt_eq_ratFn`).
* **D1 is proved in Lean in the two models of the source curve that the tree has** (`Extension.lean`).
  - Places: Hartshorne I.6.8 for the target `E`, in valuation form (`center_of_wEq`, `phi_center`). For every place
    of `ℚ(X₀(N))/ℚ` the rational map defined by `φ^*` has a center on `E`. In Hartshorne's model of a curve (the
    abstract curve `C_K` of the function field `K`, Ch. I §6), this is exactly the construction of the morphism
    `C_K → E` from `φ^*`, i.e. the direction of Hartshorne I.6.12 that the leaf needs.
  - Points `τ ∈ ℍ`: the leaf's value at `τ` is the continuous extension of `τ ↦ φ(τ)`, with no junk values
    (`modPt_plane_cases`). If `φ^*(x)` has a finite limit at `τ`, then so does `φ^*(y)`, the limit point lies on
    `E`, and `modPt` is that point. Otherwise `φ^*(x)` has a pole at `τ` and `modPt = O`.

  What stays outside Lean is the identification of the canonical model `X₀(N)_ℚ` with the abstract curve of
  `ℚ(j, j_N)` (Shimura 1971 §6.7 defines the model through this function field; Hartshorne I.6.7–6.9). That is a
  definition, not a step of an argument; the tree has no `X₀(N)` scheme on which to state it (§3).
* **D3 is isolated** (§4). The chain needs the leaf only at parametrizations satisfying `IsOptimalParam`. Under the
  reading "Gross–Zagier V Thm 2.1 holds for every modular parametrization, with the constant `c`", the leaf is a
  restriction, and nothing is needed. Under the reading "only for the strong Weil parametrization", the needed
  direction is `IsOptimalParam ⇒ strong Weil`, i.e. `L = c Λ_f ⇒ φ_* : H₁(X₀(N), ℤ) ↠ H₁(E(ℂ), ℤ)`. With
  `Λ_f = periodLattice f` this is the statement that the loops `τ → γτ` (`γ ∈ Γ₀(N)`) generate `H₁(X₀(N), ℤ)`.
  That is standard topology, but it cannot be stated in Lean: Mathlib has no `H₁(X₀(N))` and no `J₀(N)`.
  Proved in Lean (`isOptimalParam_unique`): `IsOptimalParam` pins `φ` up to sign. Two parametrizations satisfying it
  for the same `f, E` agree, or are opposite, at every `τ`. So the hypothesis singles out `±` one map and assumes
  nothing else about `φ`.

**Manual fold** (`scratch/gz-dict2/FoldCheck.lean`, VERIFIED). `frozenTarget_gzdict2` is `Main.lean`'s
`frozenTarget` with the binder `hGZ` retyped from `GZAlg.GrossZagierAlgOptCd` to `GZDict2.GrossZagierPlaneOptCd`.
It uses `grossZagierAlgOptCd_of_plane hGZ` where `Main.lean` uses `hGZ`. Axioms: `[propext, Classical.choice,
Quot.sound]`.

**Rating of the new leaf** (§5): **LEAF, printed form (direct instance) through definitions only**, with one
reading item inherited from gz-optimal/gzopt-dict: Gross–Zagier's hypothesis on `φ` in Ch. V §2 (pages-wanted:
p. 230 and p. 312). D2 is gone; D1 is proved in Hartshorne's model; D3 matters only under the strong-Weil-only
reading. If the integrator accepts this, **hGZ counts LEAF: GLUE −1**. If the reading of V §2 is still required
under the strict rule, the row keeps the flag "pending reading", now for D3 alone (proposed kinds row in §6).

## 1. The new leaf

```lean
-- ZInQKernel/Contrib/OneProof/GrossZagierPlane.lean
def ZInQ.GZDict2.GrossZagierPlaneOptAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N,
    ((φ (genX E) : LaurentSeries ℚ)).order < 0 →
    ∀ Px Qx Py Qy : MvPolynomial (Fin 2) ℚ,
    IsRatRep N (φ (genX E)) Px Qx → IsRatRep N (φ (genY E)) Py Qy →
    IsOptimalParam N f E (ratFn N Px Qx) (ratFn N Py Qy) →
    [Heegner data exactly as GZAlg.GrossZagierAlgOptAt]
    ∀ y : (E⁄K).Point, Point.map ι y = n • ∑ r, modPt E (ratFn N Px Qx) (ratFn N Py Qy) (τ r) →
    [L-functions F, G] → ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

def ZInQ.GZDict2.GrossZagierPlaneOptCd : Prop :=   -- for the short models E' in the isogeny class of C_d
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], IsShortModel E' →
    (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (shortCurve (-(d : ℚ) ^ 2)).LFunction n) → GrossZagierPlaneOptAt E'
```

The objects, all genuine definitions:

| object | Lean | meaning |
| --- | --- | --- |
| `pt2 N τ` | `![jFun τ, jFun (scaleN N τ)]`, `jFun τ = E₄(τ)³/Δ(τ)` (Mathlib's `E₄`, `discriminant`) | the point `(j(τ), j(Nτ))` of the plane model of `X₀(N)` |
| `ptQ N` | `![jq, qExpand ℚ N jq]` (FLT's `jq`) | the generators of `X0Field N = ℚ(jq, jq(q^N))` |
| `polyFn N P τ`, `polyQ N P` | `MvPolynomial.aeval (pt2 N τ) P`, `MvPolynomial.aeval (ptQ N) P` | `P(j(τ), j(Nτ))` and `P(jq, jq(q^N))` |
| `ratFn N P Q τ` | `polyFn N P τ / polyFn N Q τ` | the rational function `P/Q` of the plane model at the point of `τ` |
| `IsRatRep N x P Q` | `polyQ N Q ≠ 0 ∧ x = polyQ N P / polyQ N Q` | `P/Q` represents `x ∈ ℚ(j, j_N)` |

Every `x ∈ X0Field N` has a representation (`exists_isRatRep`, from `IntermediateField.mem_adjoin_iff_div` and
`Algebra.adjoin_range_eq_range_aeval`). The leaf quantifies over all representations. They all give the same
point (`modPt_eq_ratFn` applied twice), so this is not a choice.

**Differences from `GZAlg.GrossZagierAlgOptAt`.** The binders `X, Y`, their meromorphy and their `q`-expansion
hypotheses are replaced by the four polynomials with `IsRatRep`; `modPt E X Y` becomes
`modPt E (ratFn N Px Qx) (ratFn N Py Qy)` in the optimality hypothesis and in the Heegner point. Nothing else
changes.

## 2. D2 in Lean (`GrossZagierPlane.lean`)

| theorem | content |
| --- | --- |
| `hasQExp_add`, `hasQExp_const` | `q`-expansions add; constants |
| `hasSum_coeff_mul`, `hasQExp_mul` | **`q`-expansions multiply**: the Cauchy product over `ℤ × ℤ` (absolute convergence in `ℂ` from `summable_norm_iff`, `HasSum.mul`, reindexing `(a, b) ↦ (a + b, a)`, `HasSum.prod_fiberwise`, the finite sum `HahnSeries.coeff_mul`) |
| `HasQExp.eq_zero` | expansion `0` ⇒ the function vanishes high up |
| `HasQExp.exists_ne_zero` | **a nonzero expansion has no zeros high up**: `q^{−ord x} X(τ) = G(q)`, `G` analytic at `0` (gzopt-dict's `le_radius`, `analyticAt_sum`) with `G(0) = x_{ord x} ≠ 0` |
| `hasQExp_polyFn` | `P(j(τ), j(Nτ))` has expansion `P(jq, jq(q^N))` (induction on `P`; gzopt-dict's `hasQExp_j`, `hasQExp_jN`) |
| `exists_isRatRep` | every element of `ℚ(j, j_N)` is some `P/Q` |
| `holoH_jFun`, `holoH_polyFn`, `meromorphic_ratFn` | `j` (`Δ ≠ 0`: `ModularForm.discriminant_ne_zero`), `j(N·)` and `P(j, j_N)` are holomorphic on `ℍ`; `ratFn` is meromorphic |
| `eventuallyEq_zero_transfer`, `eventuallyEq_zero_of_im_gt`, `eventually_ne_zero_of_im_gt` | the identity theorem on `ℍ` (Mathlib's `meromorphicOrderAt_eq_top_of_isPreconnected` on the convex half-plane) |
| **`eventuallyEq_ratFn`** | **D2**: `X` meromorphic on `ℍ`, `HasQExp X x`, `IsRatRep N x P Q` ⇒ `X = ratFn N P Q` on a punctured neighbourhood of every `τ ∈ ℍ`. Proof: `X·Q(j, j_N) − P(j, j_N)` has expansion `0`, so it vanishes high up, hence near every point; `Q(j, j_N)` has a nonzero expansion, so it has no zeros high up, hence (identity theorem) none on a punctured neighbourhood of any point |
| `modPt_congr`, **`modPt_eq_ratFn`** | `modPt` depends only on germs on punctured neighbourhoods (uniqueness of limits), so `modPt E X Y τ = modPt E (ratFn Px Qx) (ratFn Py Qy) τ` for all `τ` |
| `isOptimalParam_congr` | `IsOptimalParam` reads `(X, Y)` only through `modPt` |
| **`grossZagierAlgOptAt_of_plane`**, `grossZagierAlgOptCd_of_plane`, `grossZagierFormulaCd_of_plane` | the bridge; the last composes with gzopt-dict's `grossZagierFormulaCd_of_alg`, the proved `Gamma0QExp.gamma0QExpansion_proof` and `EtaW32Character.etaW32Character_proof` |

So fold33-review's §3.3 recommendation is carried out. The leaf's functions are determined by `φ^*` in Lean, and
the old leaf's `X, Y` are proved to be them, off a discrete set.

## 3. D1 in Lean (`GrossZagierPlane/Extension.lean`)

**What the print needs.** Gross–Zagier's `φ` is a nonconstant morphism `X₀(N) → E` over `ℚ` with `φ(∞) = O`.
The leaf quantifies over `ℚ`-embeddings `φ^* : ℚ(E) → ℚ(X₀(N))`. For the leaf to be a consequence of the print,
every such `φ^*` must come from a morphism, and the leaf's value at `τ` must be that morphism's value at the point
`τ` of `X₀(N)(ℂ)`. This is the direction "embedding ⇒ morphism" of Hartshorne I.6.12. Its proof is Hartshorne
I.6.8: a rational map from a nonsingular curve to a projective variety extends at every point. (Hartshorne,
*Algebraic Geometry*, Ch. I Prop. 6.8, Cor. 6.12; Silverman AEC II.2.1; all UNVERIFIED numbers.)

**What the tree can state.** The tree has no `X₀(N)` scheme. It has its function field (`X0Field N`) and its
complex points through `ℍ`. Both models of the source curve are covered.

1. **Places** (Hartshorne's own model, Ch. I §6: the abstract nonsingular curve `C_K` is the set of places of
   `K/k`, and a morphism `C_K → Y` is built place by place by I.6.8).
   - `center_of_wEq`: for a valuation `v` of a field `K` with `v ≤ 1` on `ℚ` and `(x, y)` on `E`, either
     `v x ≤ 1 ∧ v y ≤ 1` (center `(x̄, ȳ)`), or `1 < v x < v y`. In the second case `v(1/y) < 1` and
     `v(x/y) < 1`, so `[x : y : 1] = [x/y : 1 : 1/y]` reduces to `[0 : 1 : 0] = O`.
   - `center_of_wEq_subring` is the same for a `ValuationSubring` containing `ℚ`.
   - `wEqR_gen`, `wEqR_phi`: `(φ^*x, φ^*y)` satisfies the equation of `E`.
   - **`phi_center`**: every place of `ℚ(X₀(N))/ℚ` has a center for `φ^*`.

   This is Hartshorne I.6.8 for `E ⊂ ℙ²`, for all valuations, not only discrete ones.
2. **Points `τ ∈ ℍ`** (the uniformization `ℍ → X₀(N)(ℂ)`).
   - `modPt_cases`: let `E` be elliptic and `X, Y` meromorphic at `τ` with the equation of `E` near `τ`. If `X`
     has a finite limit, then `Y` has one. The proof bounds `‖Y‖² ≤ M‖Y‖ + M'` from the equation, which is
     incompatible with a pole of `Y`. The limit point satisfies the equation by continuity and is nonsingular since
     `E` is elliptic, and `modPt` returns it. Otherwise `‖X‖ → ∞` and `modPt = O`.
   - `eventually_equation_ratFn`: the leaf's `(ratFn Px Qx, ratFn Py Qy)` satisfies the equation of `E` near every
     `τ`. This is proved by clearing denominators, `q`-expansions and the identity theorem.
   - **`modPt_plane_cases`**: the leaf's value at `τ` is the center of the place `ord_τ`.

   So `modPt` is the continuous extension of the rational map, `O` exactly at the poles of `φ^*(x)`, and never a
   junk value. That is the value at `τ` of the morphism `φ`, composed with the uniformization.

**What remains, and why it is a definition.** The leaf's `X₀(N)` is the canonical model over `ℚ`, given through
its function field `ℚ(j, j_N) ⊂ ℚ((q))` (FLT's `modularFunctionField`; gzopt-dict proved
`X0Field N ≃+* Frac(ℚ[X, Y]/(Φ_N))`). Shimura's canonical model (1971, §6.7, UNVERIFIED) is defined as the
nonsingular projective curve with this function field. Hartshorne I.6.7–6.9 (UNVERIFIED) identifies any nonsingular
projective curve with the abstract curve `C_K` of its function field. Under that identification, (1) is the
morphism `X₀(N) → E` induced by `φ^*`, and (2) is its value at the complex point `τ`. No step of an argument is
left: only the choice of model of `X₀(N)`, which the tree cannot state as a scheme. A scheme-level restatement
would be possible with the vendored Jacobian-Challenge lemma `Scheme.exists_hom_of_valuationRing_stalk` (the
extension of `Spec K(X) → E` over a smooth curve). It would need `X₀(N)` as a smooth proper `ℚ`-scheme with
function field `X0Field N`, `E` as a scheme, and the comparison of `X(ℂ)` with `ℍ`. That was not attempted.

## 4. D3: which direction the chain needs

**What the chain uses.** `core_selfOptimal` and `PeriodOdd.core_isog` apply the leaf to `X = ℘_L(c₀ φ_f)`,
`Y = ℘'_L(c₀ φ_f)/2` with `L = c₀ Λ_f` (`IsOptimalParam` by construction). Through the bridge, the plane leaf is
applied to `φ^*` built from these and to representations of `φ^*(x)`, `φ^*(y)`. The chain needs the leaf only at
parametrizations with `IsOptimalParam`.

**What the leaf assumes.** `IsOptimalParam N f E X Y` is `∃ L c, IsPeriodLattice E L ∧ L.lattice = c · Λ_f ∧
∀ τ, modPt E X Y τ = weierPt E L (c φ_f(τ))`, with `c ∈ ℚ` and `Λ_f = span{φ_f(γτ) − φ_f(τ) : γ ∈ Γ₀(N)}`. It is
an assumption on `φ`, so:

* **Reading 1** (Gross–Zagier V Thm 2.1 for every modular parametrization `φ`, with `c` defined by
  `φ^*ω = c · 2πi f(τ) dτ` in the constant): the leaf is a restriction of the print. No D3 step is needed.
  SPECULATIVE: the formula with `c²` in the denominator suggests this reading, and so does the proof through the
  `f`-isotypic part of the Heegner divisor in `J₀(N)`. GZ was not read on this host.
* **Reading 2** (only for the strong Weil curve with its strong Weil parametrization): the needed direction is
  **`IsOptimalParam ⇒ strong Weil`**, i.e. `L = c Λ_f ⇒ φ_* : H₁(X₀(N), ℤ) → H₁(E(ℂ), ℤ) = L` is onto (equivalently
  `J₀(N) → E` has connected kernel: gz-optimal §1, STANDARD). The lift of `φ` to `ℍ → ℂ` is `c φ_f`, so `φ_*`
  sends the class of the loop `τ → γτ` to `c(φ_f(γτ) − φ_f(τ))`. Hence `φ_*(H₁) ⊇ c Λ_f = L`, provided **the loops
  `τ → γτ`, `γ ∈ Γ₀(N)`, generate `H₁(X₀(N), ℤ)`**. They do, since `π₁(Y₀(N))` is a quotient of `Γ₀(N)` (as an
  orbifold group) and `π₁(Y₀(N)) → π₁(X₀(N))` is onto, `X₀(N)` minus finitely many points (STANDARD topology; Shimura
  1971 §7.5 and Diamond–Shurman §6.6 for the period lattice, UNVERIFIED locators). This statement cannot be
  formulated in Lean today: Mathlib has no `H₁(X₀(N), ℤ)` and no `J₀(N)`.

**Proved in Lean: `IsOptimalParam` determines `φ` up to sign** (`GrossZagierPlane/OptimalUnique.lean`,
`isOptimalParam_unique`, VERIFIED). If `(X, Y)` and `(X', Y')` both satisfy `IsOptimalParam N f E`, then
`modPt E X' Y' = modPt E X Y` at every `τ`, or `modPt E X' Y' = −modPt E X Y` at every `τ`. The proof:
- both lattices are the period lattice of `E`, since `g₂, g₃` determine it (cd-optimal's `lattice_eq_of_g₂_g₃`);
- so `c Λ_f = c' Λ_f`, and then `c'/c` and `c/c'` are rational multipliers of a lattice, hence integers
  (gz-optimal's `rat_mem_int`), so `c' = ±c`;
- `weierPt E L` depends only on the lattice (`weierPt_congr`) and is odd (`weierPt_neg`: `℘` even, `℘'` odd,
  `−(x, y) = (x, −y − a₁x − a₃)`).

So the leaf applies to at most `φ` and `[−1] ∘ φ`. Both are strong Weil parametrizations when one is (`[−1]` is an
automorphism of `E`), and `ĥ` is invariant under `y ↦ −y`. Under Reading 2 the whole of D3 is therefore one standard
fact:

**P**: `periodLattice f` (the `Γ₀(N)`-loop periods) is the group of periods of `2πi f dτ` over `H₁(X₀(N), ℤ)`.

Given P, `IsOptimalParam` is equivalent to `φ_*` being onto `H₁(E(ℂ), ℤ)`, i.e. to `φ` being the strong Weil
parametrization (gz-optimal §1). Without H₁ in Lean, P is the smallest step that remains; it is not statable as a
Lean `Prop` today.

No narrowing of the leaf avoids the question under Reading 2. A Lean hypothesis that implies "strong Weil" without
`H₁(X₀(N))` or `J₀(N)` is exactly a description of `Λ_f` like `IsOptimalParam`. The decision is the reading of GZ
V §2's hypothesis on `φ`, already on the pages-wanted list (gz-optimal §1: p. 230 and p. 312).

## 5. Rating

| statement | rating | reason |
| --- | --- | --- |
| `GZDict2.GrossZagierPlaneOptCd` | **LEAF, printed form (direct instance)**, one reading item | Gross–Zagier 1986 Thm I.6.3 / V Thm 2.1, constant forgotten (weaker than the print). `φ` by `φ^*` over genuine function fields. Its value at Heegner points is the value of the rational map on the plane model at `(j(τ), j(Nτ))` (D2 built in, and proved equal to the old reading). The morphism it defines is constructed in Lean place by place and at every `τ` (D1, Hartshorne I.6.8). Reading item: GZ's hypothesis on `φ` (D3, §4) |
| `GZAlg.GrossZagierAlgOptCd` (old `hGZ`) | proved from the new leaf (`grossZagierAlgOptCd_of_plane`) | — |

**Count.** `frozenTarget`'s binder `hGZ` changes type. Under the strict rule as stated for this task (D1–D3
proved in Lean or reduced to definitions), D2 and D1 are done. D3 under Reading 2 is a topological identification
that cannot be stated in Lean. If the integrator accepts the leaf as a printed form with GZ's hypothesis on `φ` as
a reading item (as for every other unread printed leaf), **hGZ counts LEAF: GLUE −1** in both columns. Otherwise
it stays "pending reading", for D3 alone. No glue is added either way.

## 6. Fold

* **Manual fold of `Main.lean`.** `hGZ` is a binder of `frozenTarget`, not a bundle field, so `autofold.py` does
  not apply. Spec (`scratch/gz-dict2/fold-spec.md`):
  - add `import ZInQKernel.Contrib.OneProof.GrossZagierPlane` to `Main.lean`;
  - retype `(hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd)` to `(hGZ : ZInQ.GZDict2.GrossZagierPlaneOptCd)`;
  - replace `ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ` by
    `ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZDict2.grossZagierAlgOptCd_of_plane hGZ)`.

  `scratch/gz-dict2/FoldCheck.lean` is that theorem (`frozenTarget_gzdict2`). It compiles, with axioms
  `[propext, Classical.choice, Quot.sound]` (`FoldCheck-output.txt`, VERIFIED).
* **`#discharges`** (`scratch/gz-dict2/Discharges.lean`, `Discharges-output.txt`, VERIFIED):

  ```
  DISCHARGES [hGZ] by ZInQ.GZDict2.grossZagierAlgOptCd_of_plane
    still assumes: [ZInQ.GZDict2.GrossZagierPlaneOptCd]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 37 open hypotheses, 9524 theorems checked, 39 discharge one
  ```
* **kinds row** (proposed, `scratch/gz-dict2/kinds-row.tsv`; `kinds.tsv` not edited). It replaces the row
  `frozenTarget hGZ`: field `hGZ`, kind `published`, strict `LEAF`, strictest `LEAF`, flag
  `unread: new printed leaf (gz-dict2: GZDict2.GrossZagierPlaneOptCd; D2 proved in Lean (grossZagierAlgOptCd_of_plane), D1 proved in Hartshorne's model (GrossZagierPlane/Extension.lean); reading item: GZ V section 2 hypothesis on phi (D3, only if restricted to the strong Weil parametrization)); locator UNVERIFIED`.
  The alternative under the strictest reading: strict `LEAF`, strictest `GLUE`, flag `pending reading: D3 only`.
* **locators row** (proposed, not edited): `GZDict2.GrossZagierPlaneOptCd`: Gross–Zagier 1986, Thm I.6.3 (p. 230) and
  Ch. V Thm 2.1 (V §2, p. 312), as for `GZAlg.GrossZagierAlgOptCd`.

## 7. Checks

| file | content | check |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/GrossZagierPlane.lean` | §1–§6: `q`-expansion algebra, plane model, identity theorem, D2, leaf, bridge | `lake build ZInQKernel.Contrib.OneProof.GrossZagierPlane`: no errors, no warnings in the file (VERIFIED) |
| `ZInQKernel/Contrib/OneProof/GrossZagierPlane/Extension.lean` | D1: places and points `τ` | `lake build`: no errors, no warnings in the file; axioms standard (`AxExt-output.txt`, VERIFIED) |
| `ZInQKernel/Contrib/OneProof/GrossZagierPlane/OptimalUnique.lean` | D3: `isOptimalParam_unique`, `weierPt_congr`, `weierPt_neg` | `lake build`: no errors, no warnings in the file; axioms standard (`AxD3-output.txt`, VERIFIED) |
| `scratch/gz-dict2/FoldCheck.lean` | manual fold | standard axioms (VERIFIED) |
| `scratch/gz-dict2/Discharges.lean` | `#discharges` | output above (VERIFIED) |
| `scratch/gz-dict2/D2a.lean`, `D1a.lean`, `D1b.lean`, `Extension.lean`, `D3.lean` | development copies | compiled (VERIFIED) |

## 8. Remaining

* The reading of Gross–Zagier V §2's hypothesis on `φ` (D3). Under Reading 2, the topological identification P
  ("`Γ₀(N)`-loops generate `H₁(X₀(N), ℤ)`") stays outside Lean until `H₁` of modular curves exists.
* A scheme-level form of D1 (`X₀(N)_ℚ` as a smooth proper scheme with function field `X0Field N`) was not
  attempted (§3).

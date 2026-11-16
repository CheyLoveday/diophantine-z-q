# javanpeykar-dict: `javanpeykarBound` from Javanpeykar's theorem in printed form

Task javanpeykar-dict (2026-11-16), base `origin/main` 2880fef1. Scratch: `scratch/javanpeykar-dict/`.
Lean: `ZInQKernel/Contrib/OneProof/JavanpeykarDict.lean` (namespace `JavanpeykarDict`).

## 1. Result

The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound` (`ZInQKernel/OneProof/H/TailY.lean`,
bundle `OpenResearchLeaves26`) is proved, with only the standard axioms, from

* **`JavanpeykarDict.JavanpeykarPrinted`**, a new leaf: Javanpeykar, *Algebra Number Theory* 8 (2014),
  Thm 1.1.1, stated for `X = X₀ ×_K ℚ̄` in the print's own terms (`Jac(X)` as the degree-zero Picard scheme,
  `g` the genus of `X_ℚ̄`, a Belyi map of `X_ℚ̄` over `ℚ̄`). Rated **printed form** (§4);
* **`JavanpeykarDict.BelyiBaseChange`**, new **glue**, stated and not proved: a `K`-rational Belyi function
  (the kernel's `IsBelyiFunction K`) of degree `d` stays a Belyi function of `X_ℚ̄` over `ℚ̄`, of degree `d`.

```lean
theorem JavanpeykarDict.javanpeykarBound_of_printed (hJ : JavanpeykarPrinted) (hB : BelyiBaseChange) :
    ZInQ.HeightSplit.JavanpeykarBound
```

Of the three dictionary steps of the 11-16 pass:

| step | status |
|---|---|
| (1) kernel Jacobian (`IsJacobian`, Albanese predicate) vs the print's `Jac(X)` (Milne, *Jacobian varieties*, 6.1; base change) | **proved in Lean**: every kernel Jacobian is isomorphic to every tensor-compatible representative of `Pic⁰_{X/K}` (isj1-dict's proof, copied), and the published stable height is an isomorphism invariant (new: `isStableFaltingsHeight_of_iso`) |
| (2) `dim J = genus` (Milne 2.1) | **proved in Lean**: `dim J = dim_K H¹(X, 𝒪_X) = dim_ℚ̄ H¹(X_ℚ̄, 𝒪)` (`dim_eq_genusK`, `genusBar_eq`, from the vendored Jacobian-Challenge library) |
| (3) kernel `IsBelyiFunction` over `K` vs a Belyi map of `X` over `ℚ̄` | **restated**: the leaf now takes a Belyi function of `X_ℚ̄` over `ℚ̄`; the passage from `K` to `ℚ̄` is the glue `BelyiBaseChange` (not proved: Lean has no function field of a base change yet; outline in §5) |

Target "javanpeykarBound back to LEAF": met for the leaf (the new leaf is in printed form), **not met for the
field as a whole**: the fold adds one project-glue field, `belyiBaseChange`, so it raises the strict GLUE count
by one (autofold needs `--allow-rise`).

## 2. What compiles

TODO (filled after the build)

## 3. The Lean statements

Old field (verbatim copy: `scratch/javanpeykar-dict/Statement.lean.txt`): for `X/K` a curve (`IsCurve`,
integral) with a `K`-point `P₀`, `J : PkgI3.AbVar K` with `IsJacobian X P₀ J aj`, `J.dim = g ≥ 1`, `t ∈ K(X)`
with `IsBelyiFunction K K(X) t`, `d = [K(X) : K(t)] > 0`, and `IsStableFaltingsHeight J x`:
`x ≤ 13·10⁶ g d⁵`.

New leaf (`ZInQKernel/Contrib/OneProof/JavanpeykarDict.lean`):

```lean
def JavanpeykarPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
    PicardTensorCompatible X.hom V.group rep →
    1 ≤ genusBar X →
    ∀ [IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left]
      (t : (baseChangeCurve X (AlgebraicClosure K)).left.functionField),
      letI := ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
      IsBelyiFunction (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)).left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin (AlgebraicClosure K) {t})
        (baseChangeCurve X (AlgebraicClosure K)).left.functionField = d → 0 < d →
      ∀ x : ℝ, IsStableFaltingsHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d
```

* `baseChangeCurve X L = (Over.pullback (Spec L → Spec K)).obj X`, `genusBar X` the arithmetic genus
  `dim H¹(X_K̄, 𝒪)` of `X_K̄` (`K̄ = AlgebraicClosure K`; vendored `Scheme.arithmeticGenus`);
* `AbelianVariety`, `picardFunctorDegree`, `PicardTensorCompatible`: vendored Jacobian-Challenge library
  (`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/`), `ofVendored V` the same group scheme as a kernel
  `PkgI3.AbVar`;
* `IsBelyiFunction`, `ffAlgebra`, `javanpeykarBound`, `IsStableFaltingsHeight`: the kernel's, unchanged.

There is no base point (the print has none) and no kernel `IsJacobian`.

New glue (`BelyiBaseChange`): for `X/K` a curve, integral, and `t ∈ K(X)` with `IsBelyiFunction K K(X) t`
and `[K(X) : K(t)] = d > 0`: `X_K̄` is integral and some `t' ∈ K̄(X_K̄)` has `IsBelyiFunction K̄ K̄(X_K̄) t'`
and `[K̄(X_K̄) : K̄(t')] = d`.

Proved glue (all in the same file):

| theorem | content |
|---|---|
| `isStableFaltingsHeight_of_iso` | `e : J.X ≅ J'.X` a homomorphism, `IsStableFaltingsHeight J x → IsStableFaltingsHeight J' x` (Néron model `𝒩` of `J_L` becomes one of `J'_L` with `gen' = gen ≫ e_L`; same scheme, so same semistability and same metrized models, hence same height) |
| `abVarIso_picZero_of_isJacobian` | isj1-dict's: `IsJacobian X P₀ J aj` and `V` a tensor-compatible `Pic⁰_{X/K}` representative give `J ≅ ofVendored V` |
| `dim_eq_genusK` | `IsJacobian X P₀ J aj → J.dim = dim_K H¹(X, 𝒪_X)` |
| `genusBar_eq` | `dim_K̄ H¹(X_K̄, 𝒪) = dim_K H¹(X, 𝒪)` (vendored `arithmeticGenus_pullback`) |
| `javanpeykarBound_of_printed` | the old field from the leaf and the glue |

## 4. Rating of the new leaf: printed form

`JavanpeykarPrinted` is Javanpeykar's Thm 1.1.1 (read by the locator audit: `h_Fal(X) ≤ 13·10⁶·g·deg_B(X)⁵` for
a smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1`; `h_Fal(X)` the stable Faltings height of `Jac X`,
§2.3; `deg_B(X)` the least degree of a finite morphism `X → ℙ¹_ℚ̄` unramified outside three points) instantiated
at `X = X₀ ×_K ℚ̄`, with each object of the print read as follows (none is a structure invented for the purpose):

* **curve**: `X₀` smooth proper geometrically connected over `K` (proper curves are projective), so `X₀ ×_K ℚ̄`
  is a smooth projective connected curve over `ℚ̄ = AlgebraicClosure K` (an algebraic closure of `ℚ`). Every
  curve over `ℚ̄` is of this form; the leaf is the print restricted to them (a specialization).
* **genus**: `genusBar X₀ = dim H¹(X, 𝒪_X)`, the genus of the smooth projective curve `X` (computed over `ℚ̄`,
  not over `K`).
* **Jacobian**: `Jac(X)` is the degree-zero Picard scheme. The leaf takes `V/K` representing `Pic⁰_{X₀/K}` with
  the tensor-product group law; `V_ℚ̄` represents `Pic⁰_{X/ℚ̄}` (representability commutes with base change), so
  `V_ℚ̄ = Jac(X)`. The kernel's Albanese-property Jacobian is not used.
* **height**: `IsStableFaltingsHeight V x`, the published stable height of `V` (Néron model over a field of
  semistable reduction, Faltings' `(i/2)^g` normalization, as in Javanpeykar §2.1/§2.3 per the audit). The stable
  height of an abelian variety over `ℚ̄` is by definition that of a model over a number field, here `V`. The
  height must be read over `K`: the kernel's heights are defined over number fields only. The archimedean
  dictionary of `IsStableFaltingsHeight` (metrics from analytic uniformizations) is height-dict's subject, shared
  by every height leaf, and not changed here.
* **Belyi degree**: a Belyi function `t ∈ ℚ̄(X)` over `ℚ̄` (the kernel's `IsBelyiFunction` over the algebraically
  closed field `ℚ̄`: `t` transcendental, and ramification index `1` at every place of `ℚ̄(X)/ℚ̄` over a point
  `a ∈ 𝔸¹(ℚ̄) ∖ {0, 1}`, since the monic irreducible `q ≠ T, T − 1` over `ℚ̄` are the `T − a`), of degree
  `d = [ℚ̄(X) : ℚ̄(t)]`. The morphism `X → ℙ¹_ℚ̄` given by `t` is finite of degree `d` and unramified over
  `ℙ¹ ∖ {0, 1, ∞}`, a Belyi map, so `deg_B(X) ≤ d`; the bound `13·10⁶ g d⁵` is increasing in `d`.

Rating: **printed form**, flagged unread. The remaining readings are vocabulary, not mathematics: Belyi maps
in function-field form (the equivalence of smooth projective curves over `ℚ̄` with their function fields,
Hartshorne I.6, UNVERIFIED number), the Jacobian as `Pic⁰` over `K` (base change of the Picard functor), and
the stable height over `ℚ̄` read on a model. Not stronger than the print: each hypothesis implies the print's
(`deg_B ≤ d`, `g` and `h_Fal(X)` equal to the leaf's). Not vacuous: `V` exists for every curve
(`exists_abelianVariety_picardDegreeZero`), `X_ℚ̄` is integral, every curve over `ℚ̄` has a Belyi function
(Belyi), and `IsStableFaltingsHeight` is attained given the kernel's SS1/N1 leaves.

Proposed `locators.md` row (to be added by the integrator): *R18 printed: Javanpeykar 2014, Thm 1.1.1, p. 90
(arXiv:1403.6404v1 p. 1); §2.3 p. 98; `JavanpeykarDict.JavanpeykarPrinted`: printed form at
`X = X₀ ×_K ℚ̄` (Jac = `Pic⁰`, Belyi map in function-field form); same source as R18.*

## 5. The glue `BelyiBaseChange` (not proved)

Statement in §3. It is true (STANDARD): `K̄(X_K̄) = K(X) ⊗_K K̄` because `X` is geometrically integral, so
`[K̄(X_K̄) : K̄(t)] = [K(X) : K(t)]`; for a place `w` of `K̄(X_K̄)/K̄` with `t − a ∈ 𝔪_w`, `a ≠ 0, 1`, let `p` be the
minimal polynomial of `a` over `K` (`p ≠ T, T − 1`) and `w₀ = w ∩ K(X)`: `p(t) = (t − a)·u` with `u ∈ w`, so
`p(t) ∈ 𝔪_{w₀}` and the `K`-Belyi property makes `p(t)` a uniformizer at `w₀`; a constant field extension is
unramified (Stichtenoth, *Algebraic Function Fields and Codes*, Thm 3.6.3, UNVERIFIED number), so `p(t)` is a
uniformizer at `w`, and then so is `t − a`.

Why it is not proved: Lean (Mathlib 4.35 and the vendored libraries) has no comparison between the function
field of a base change and the tensor product, and no ramification theory of constant field extensions.

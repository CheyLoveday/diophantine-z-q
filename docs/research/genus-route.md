# genus-route: `t34`'s two uses without `GenusX1Field` and without `X0Transitive`

**Main result (VERIFIED, compiled, standard axioms).** The two consumers of `t34` in the single proof
need only `dim J₁(N) ≤ N²`. That bound follows from `DimJacobianEqGenus` (proved outright by
dimjac-glue) and **one local leaf**, `LocalDerivation` (the derivative with respect to a local
parameter `π` of a place `P` preserves `𝒪_P`; Stichtenoth §4.1), with no other hypothesis and **no
Riemann–Hurwitz**:

```lean
theorem GenusRoute.dimJ1Le_of_localDerivation (h1 : DimJacobianEqGenus) (hL : LocalDerivation) : DimJ1Le
theorem HDec.HSyn.t34Le_of_localDerivation (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (hL : GenusRoute.LocalDerivation) : DimJ1Le5             -- on the OneProof copies
```

The genus bound is proved by an explicit injection (section 6): every holomorphic differential of
`K_N` is `h · dj` with `h` in an explicit `ℚ`-space `V`, and `V` injects into `OF / j·OF ≅ ℚ^d`
(`OF` the integral closure of `ℚ[j]`, `d = [K_N : ℚ(j)] ≤ N²`), so `g(K_N) ≤ d ≤ N²`. No
Riemann–Roch, no Riemann–Hurwitz, and no identification of `fieldGenus` with another notion of
genus is used. A second route, from the textbook leaf Riemann–Hurwitz (`RiemannHurwitzQj`), is also
compiled:

```lean
theorem GenusRoute.dimJ1Le_of_rh_curve (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj) : DimJ1Le
theorem HDec.HSyn.t34Le_of_rh (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (hRH : GenusRoute.RiemannHurwitzQj) : DimJ1Le5           -- the same, on the OneProof copies
theorem HDec.HSyn.dim_J1_le_of5 (h : DimJ1Le5) ...           -- drop-in for TailD.lean:236
theorem HDec.HSyn.G0Split.javanpeykarJ1_of_le (hR18 : R18_JavanpeykarConcrete)
    (hB : X1BelyiOnModel) (h : DimJ1Le5) : JavanpeykarJ1     -- drop-in for TailD.lean:250
```

`X0Transitive` was needed by curve-split's route only for the constant field of `K_N`
(`x1ConstantField_of_x0Transitive`). The new glue theorem `GenusRoute.constantFieldIsQ_of_curve`
reads the constant field off the model of `X₁(N)` that `IsJ1` already provides: `ℚ` is
algebraically closed in the function field of any smooth proper geometrically connected integral
curve over `ℚ`. `GenusX1Field` (the equality `g(K_N) = g(Γ₁(N))`, which has no Lean form) is not
needed: only an upper bound is used.

Files (all compile with `lake env lean`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

* `scratch/genus-route/ConstField.lean` (≈410 lines): the constant-field theorem alone.
* `scratch/genus-route/GenusRoute.lean` (≈1770 lines, 16 s): `ConstField` + curve-split's
  `GenusBound.lean` (copied verbatim, namespace `CurveSplit` → `GenusRoute`) + `dimJ1Le_of_rh_curve`,
  `genus_le_of_model`. Imports only kernel modules (`Contrib.CurvesG`, `Contrib.RLeaf.BelyiX1`,
  `Contrib.RLeaf.T40`, `Contrib.Dim.SmoothStalk`, `Contrib.SmoothFibre.Basic`, `HDecomp.ModCurves.X1Belyi`).
* `scratch/genus-route/GenusElem.lean` (≈2370 lines): `GenusRoute.lean` + the elementary genus bound
  (`LocalDerivation`, `genusLeDegree_of_localDerivation`, `dimJ1Le_of_localDerivation`).
* `scratch/genus-route/Fold.lean` (≈2460 lines, ≈30 s): `GenusElem.lean` verbatim +
  `import ZInQKernel.OneProof.H.TailM` + the drop-in theorems (`t34Le_of_localDerivation`,
  `t34Le_of_rh`, `dim_J1_le_of5`, `javanpeykarJ1_of_le`), in the namespaces of their consumers. Needs the
  upstream `lean/` package built once (`lake build ZInQKernel.Hypotheses.JHeight`).

## 1. What the consumers need from `t34` (VERIFIED by reading)

`t34 : LeafModCurves.DimJ1Genus` (`dim J₁(N) = genus Γ₁(N)`) enters the proof only through
`t34_of_split5 t.dimJacobianEqGenus t.genusX1Field` (TailM.lean:365, bundle `TailZ9`) and is consumed at

* `TailD.lean:236`: `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1`, whose conclusion is
  `∃ g : ℕ, J.dim = g ∧ g ≤ N²`;
* `TailD.lean:250`: `javanpeykarJ1 hR18 hBelyi t.t34 …` (LPrefix.lean:12078), whose proof uses
  `hT34` only in `LeafModCurves.dim_J1_le hT34 N hN J hJ`.

So both need exactly `DimJ1Le := ∀ N J, 0 < N → IsJ1 N J → ∃ g : ℕ, J.dim = g ∧ g ≤ N²`
(curve-split's definition; `DimJ1Le5` is the same statement over the OneProof copies
`PkgI3.AbVar`/`LeafModCurves.IsJ1` of namespace `HDec`). Nothing else about the genus is used.

## 2. The fold

Replace the bundle field `genusX1Field : GenusX1Field` by `localDerivation : GenusRoute.LocalDerivation`
(recommended; or `riemannHurwitzQj : GenusRoute.RiemannHurwitzQj`, or `t34Le : DimJ1Le5` directly), set
`t34Le := t34Le_of_localDerivation t.dimJacobianEqGenus t.localDerivation`, and at the consumers:

| site | now | replacement |
|---|---|---|
| TailD.lean:236 | `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1` | `dim_J1_le_of5 t.t34Le N hN0 J hJ1` (same type; checked by an `example`) |
| TailD.lean:250 | `javanpeykarJ1 hR18 hBelyi t.t34 …` | `G0Split.javanpeykarJ1_of_le hR18 hBelyi t.t34Le …` |

`javanpeykarJ1_of_le` is `javanpeykarJ1`'s proof with one line changed (diff in the log), and
`javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34` holds by `rfl`
(compiled). Since `DimJ1Le5` follows from `t34` (`dimJ1Le5_of_t34`), the change only weakens the hypotheses.

Note (VERIFIED by grep): in the current OneProof bundles `x0Transitive` also supplies T40
(`t40 := t40_of_x0Transitive4 t.x0Transitive`, TailK.lean:250, TailN.lean:236). This report removes only
its use in the genus route (curve-split's `dimJ1Le_of_rh`); its T40 use is outside this task.

## 3. Leaves and glue

| item | kind | status | source |
|---|---|---|---|
| `LocalDerivation` (recommended route) | LEAF (textbook, local) | open | Stichtenoth §4.1: for a `P`-prime element `t`, the `t`-derivative `δ_t` maps `𝒪_P` into `𝒪_P` (Prop. 4.1.8, number UNVERIFIED); equivalently `Ω_{𝒪_P/ℚ}` is free on `dπ` (Hartshorne II.8, numbers UNVERIFIED) |
| `genusLeDegree_of_localDerivation` and its 14 lemmas | GLUE | proved (new) | — |
| `RiemannHurwitzQj` (alternative route) | LEAF (textbook, composite) | open | Stichtenoth, *Algebraic Function Fields and Codes*, Thm 3.4.13 (Hurwitz genus formula) with Thm 3.5.1 (Dedekind's different theorem, `d_P = e_P − 1` in char 0) and the identification of `fieldGenus` (holomorphic Kähler differentials) with the Riemann–Roch genus (Stichtenoth §4.3; Hartshorne II.8, IV.2.4); numbers UNVERIFIED |
| `DimJacobianEqGenus` | LEAF in the kernel, now proved | proved by dimjac-glue (`scratch/dimjac-glue/DimJacGlue.lean`, other branch; not re-checked here) | Milne 1986 |
| `constantFieldIsQ_of_curve` | GLUE | proved (new) | — |
| `belyiGenusBound_of_rh`, `fundamentalIdentityQj` | GLUE | proved (curve-split, copied) | — |
| `ZInQ.RLeaf.belyiX1` | kernel theorem | proved | — |
| `dimJ1Le_of_rh_curve`, `t34Le_of_rh`, `javanpeykarJ1_of_le` | GLUE | proved (new) | — |

`RiemannHurwitzQj` (verbatim from curve-split's `GenusBound.lean`): for `F` finite over `ℚ(j) = RatFunc ℚ`
with `ℚ` algebraically closed in `F`, the function `P ↦ (e_P − 1)·deg P` on places of `F/ℚ` (proper
valuation subrings containing `ℚ`; `e_P` the index of `U_P·ℚ(j)ˣ` in `Fˣ`; `deg P = dim_ℚ κ(P)`) has
finite support and `2·g(F) − 2 = −2·[F : ℚ(j)] + Σ_P (e_P − 1) deg P`, `g = fieldGenus`. Checked again
for this report: the `Algebra ℚ F` and `Algebra Qj F` instances are not linked, which is harmless since a
field has at most one `ℚ`-algebra structure; `e_P` as a unit-group index equals the ramification index
(value group `ℤ`, image of `ℚ(j)ˣ` is `e_P ℤ`); for `F = ℚ(j)` both sides are `−2`. Not vacuous: it is
applied to `K_N`, which satisfies the hypotheses (`constantFieldIsQ_of_curve`, `fieldX1_finiteDimensional`).

## 4. The constant-field theorem (new glue, proved)

```lean
theorem GenusRoute.constantFieldIsQ_of_curve (X : Over LeafModCurves.SpecQ) (hC : LeafModCurves.IsCurve X)
    [IsIntegral X.left] (F : Type) [Field F] [Algebra LeafModCurves.Qj F]
    (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F
```

Proof (each step a compiled lemma):

1. `isNormal_of_integral` (copied from curve-split's `CurveBij.lean`): the stalks of an integral smooth
   curve over a field are integrally closed (DVRs at closed points, the function field at the generic point).
2. `exists_global_of_isIntegral`: `y ∈ K(X)` algebraic over `ℚ` is integral over each `Γ(X, U)`, `U` affine
   nonempty; `Γ(X, U)` is integrally closed with fraction field `K(X)`, so `y ∈ Γ(X, U)`.
   `exists_global_section`: these local sections glue to `s ∈ Γ(X, ⊤)` (Mathlib's
   `TopCat.Sheaf.existsUnique_gluing'`; overlaps are nonempty because `X` is irreducible, and
   `germToFunctionField` is injective).
3. `algebraic_mem_range`: with `q = minpoly ℚ y` and `A = ℚ[T]/(q)` (a field), `s` gives
   `φ = X.toSpecΓ ≫ Spec(A → Γ(X, ⊤)) : X → Spec A`, and `X → Spec ℚ` equals `φ ≫ (Spec A → Spec ℚ)`
   (`hom_specQ_ext`: maps to `Spec ℚ` are unique). Geometric connectedness at `ℚ̄`, Mathlib's
   `pullbackRightPullbackFstIso`, and surjectivity of `φ` (`Spec A` is a point) and of its base change
   make `Spec ℚ̄ ×_ℚ Spec A ≅ Spec (ℚ̄ ⊗_ℚ A)` connected (`pullbackSpecIso`). `ℚ̄ ⊗ A` is finite over `ℚ̄`,
   so Artinian, so its spectrum is discrete, hence a single point. If `deg q ≥ 2`, `q` has two distinct
   roots `α ≠ β` in `ℚ̄` (separable, `card_rootSet_eq_natDegree`), and the kernels of
   `a ⊗ b ↦ a·b(α)`, `a ⊗ b ↦ a·b(β)` are distinct primes (`not_subsingleton_of_roots`). So `deg q = 1`.
4. Transport along `e` (ring maps out of `ℚ` are unique).

## 5. What remains

* The leaf `LocalDerivation` (or, on the alternative route, `RiemannHurwitzQj`).
* The fold itself (bundle edit in TailN/TailO/…, done after the announcement).

## 6. The elementary genus bound (new glue, proved): `g(F) ≤ [F : ℚ(j)]`

```lean
def GenusRoute.LocalDerivation : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → ∀ (P : Place F) (π : F), π ≠ 0 → π ∈ P.w.nonunits →
      (∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) →
        ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w

def GenusRoute.GenusLeDegree : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      fieldGenus F ≤ Module.finrank Qj F

theorem GenusRoute.genusLeDegree_of_localDerivation (hL : LocalDerivation) : GenusLeDegree
```

`Place F` (curve-split): a proper valuation subring of `F` containing `ℚ`. `LocalDerivation` is a
statement about one place and one local parameter, over Mathlib's `Derivation` and `ValuationSubring`;
it is true for every place of a function field over a field of characteristic `0` (the completion
`𝒪̂_P ≅ κ(P)[[π]]`, and `d/dπ` acts coefficientwise), and the constant-field hypothesis only weakens
it to Stichtenoth's standing assumption.

Proof of `genusLeDegree_of_localDerivation` (`s = j`, `t = j/1728`, `d = [F : ℚ(j)]`; each step a
compiled lemma of `GenusElem.lean`):

1. `mem_span_D_sF`: `Ω_{F/ℚ} = F · ds`. (`F/ℚ(j)` is finite separable, hence formally unramified, so
   `Ω_{F/ℚ(j)} = 0`; Mathlib's exact sequence `F ⊗ Ω_{ℚ(j)/ℚ} → Ω_{F/ℚ} → Ω_{F/ℚ(j)}` and the quotient
   rule in `ℚ(j)`.) So every `ω ∈ holoDiff F` is `h · ds`.
2. `local_conditions`: if `h · ds` is regular at every place, then `h s (s − 1728) ∈ 𝒪_P` at every
   place with `s ∈ 𝒪_P`, and `h (s − 1728) ∈ 𝔪_P` at every place with `s ∉ 𝒪_P`. For each place take a
   uniformizer `π` (`exists_uniformizer_all`: curve-split's `exists_uniformizer`, twisted by `j ↦ 1/j`
   at infinity) and `δ = d/dπ` from the leaf; `δ` extends to `Ω_{F/ℚ} → F` and maps the differentials
   regular at `P` into `𝒪_P` (`lift_mem_of_regularAt`), so `h δ(s) ∈ 𝒪_P`. Then: over `j = 0` and
   `j = 1728`, `z = u π^(m+1)` and `δ z = π^m c` with `c` a unit (`deriv_unit_pow`, characteristic 0);
   over `j = ∞`, the same for `z = 1/s`; elsewhere the Belyi property gives the local parameter
   `q(t)` and `δ t = 1/q'(t)` (curve-split's `polyIdeal`, `exists_monic_irreducible_mem`).
3. `Vspace`: the `ℚ`-space of such `h`. `finrank_Vspace_le`: `h ↦ h s (s − 1728)` lands in `OF`
   (`mem_OF_of_places`, Mathlib's `mem_integers_of_valuation_le_one` with curve-split's `placeOf`),
   and composing with the coordinates at `s = 0` in a `ℚ[s]`-basis of `OF` (free of rank `d`:
   `IsIntegralClosure.module_free`, `IsIntegralClosure.rank`) gives a `ℚ`-linear map `V → ℚ^d`. It is
   injective: if `h s (s − 1728) = s k` with `k ∈ OF`, then `k = h (s − 1728)` lies in every place and
   in `𝔪_P` over `∞`; elements in every place are rational (`mem_rat_of_all_places`: `ℚ` is integrally
   closed in `F` by `ConstantFieldIsQ`, and Mathlib's Stacks 090P), and a place over `∞` exists
   (`exists_place_inf`, curve-split's fundamental identity), so `k = 0` and `h = 0`.
4. `fieldGenus F = dim holoDiff ≤ dim V ≤ d`.

With `constantFieldIsQ_of_curve` and `ZInQ.RLeaf.belyiX1` (`d ≤ N²`): `dimJ1Le_of_localDerivation`.

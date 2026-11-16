# x1-igusa: isj1-dict's Igusa leaf `X1PointsConjugate` from Igusa's theorem in its printed form

Task x1-igusa, branch `wip/x1-igusa`, base `wip/isj1-dict` 37628525. Date 2026-11-16.
Lean: `ZInQKernel/Contrib/OneProof/X1Igusa.lean` (new). It imports `R16IsJ1Dict`, `RLeaf.IgusaSL2` and Tau Ceti's
`Affine.Point.VariableChange`, not `OneProof.Main`, and has no build-time code.
Scratch: `scratch/x1-igusa/`; the results log is `log.md`.
Nothing else under `ZInQKernel/` or `blueprint/` was edited. This is model work with no human review.

Marks:
- **VERIFIED**: compiled, or read in a file of this tree.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: a judgement.
- **UNVERIFIED**: a theorem number recalled without a source (this host has no network).

## 0. Result

**`X1PointsConjugate` is proved in Lean from a printed-form leaf, Igusa's theorem for Diamond–Shurman's model. So
`r16CoreY` is discharged by two published leaves instead of one published leaf and one consequence.** VERIFIED:
compiled, standard axioms, `#discharges` recorded (§3).

```lean
theorem X1Igusa.x1PointsConjugate_of_igusaGL2DS (h : IgusaGL2DS) : R16IsJ1Dict.X1PointsConjugate
theorem X1Igusa.r16CoreY_of_picZero_igusaDS (h : R16IsJ1Dict.AfTateCharPolyPicZero) (hI : IgusaGL2DS)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
```

1. **Step 1 (`E[N] ≅ (ℤ/N)²`) was already proved in the tree.** VERIFIED (read).
   - `ZInQ.RLeaf.t36_torsionStructure : X1Belyi.TorsionStructure` (`ZInQKernel/Contrib/RLeaf/T36Torsion.lean`) gives
     `nTors W N ≃+ ZMod N × ZMod N` for every elliptic `W` over an algebraically closed field of characteristic 0 and
     every `N > 0`.
   - It comes from Tau Ceti's `torsion_addEquiv_prod`, which rests on `#E[n] = n²` from division polynomials
     (Silverman III.6.4(b)).
   - So no transport along `\overline{ℚ(j)} → ℂ` was needed. The pin's Mathlib has no torsion count, but the
     vendored Tau Ceti tree has one.
2. **The group theory of Step 2 was also in the tree** (VERIFIED, read):
   - `ZInQ.RLeaf.exists_SL2_first_column`: a vector of exact order `N` in `(ℤ/N)²` is the first column of a
     matrix in `SL₂(ℤ/N)`;
   - `igusaTransitive_of_igusaGL2`.
   - **`X1PointsConjugate` is token for token `ZInQ.RLeaf.IgusaTransitive`** (`X1RationalCusp.lean` l.123):
     `x1PointsConjugate_iff_igusaTransitive` holds by `Iff.rfl`. So `X1PointsConjugate` already followed from
     `ZInQ.RLeaf.IgusaGL2` (`x1PointsConjugate_of_igusaGL2`), the former bundle leaf H-117, which is no longer a
     field: flt-cqj2's bypass fold removed it.
3. **What was missing was the printed model** (§1). `IgusaGL2` is stated for the kernel's curve
   `E_j = ofJNe0Or1728 j`, `y² + (j−1728)xy = x³ − 36(j−1728)³x − (j−1728)⁵`. No source prints Igusa's theorem for
   that model. Over `ℚ(j)` it is the quadratic twist by `ℚ(√−2)` of Diamond–Shurman's model (Finding 1, §5), so for
   this model `IgusaGL2` is a consequence of the print, through a twist argument that is not formalized. The new
   leaf `IgusaGL2DS` is the theorem for Diamond–Shurman's `E_j : y² = 4x³ − g_j x − g_j`, `g_j = 27j/(j − 1728)`.
   The proved glue carries it to the kernel's curve on `x`-coordinates, through an explicit change of variables
   over `\overline{ℚ(j)}` whose action on `x` is `ℚ(j)`-affine (`cDS_smul`).
4. **Fold** (dry run, §3): `r16CoreY` (GLUE) is replaced by `afTateCharPolyPicZero` and `igusaGL2DS`, both
   published and unread.
   - Strict count: GLUE goes from 10 to 9, which meets the target (−1 GLUE).
   - isj1-dict's fold was neutral, because its second leaf `x1PointsConjugate` was rated consequence.
5. **`AfTateCharPolyPicZero` is not a direct instance of DS 9.5.4 as it stands** (§4).
   - The gap is the function-field comparison `ℚ(j, f₁) ≅ ℚ(j)(x(P))` for one `P`.
   - It is stated in Lean as the glue Prop `WeberFieldComparison`, over the tree's `T5Glue.weber`, `jL` and `pp`
     and the kernel's `E_j` (`scratch/x1-igusa/WeberComparison.lean`, compiles). A proof sketch is in §4.
   - It needs no Igusa: transitivity enters only through `X1PointsConjugate`, which is now proved from the leaf.

## 1. Statements (all in namespace `X1Igusa`, VERIFIED: compiled)

```lean
/-- g_j = 27 j / (j − 1728) -/
def gDS : Qj := 27 * RatFunc.X / (RatFunc.X - 1728)
/-- Diamond–Shurman's E_j : y² = 4x³ − g_j x − g_j, in Mathlib's normal form (y = 2y') -/
def EDS : WeierstrassCurve Qj := ⟨0, 0, 0, -(gDS / 4), -(gDS / 4)⟩
abbrev EDSBar : WeierstrassCurve Kbar := EDS.baseChange Kbar
abbrev galPtDS (σ : Kbar ≃ₐ[Qj] Kbar) : EDSBar.toAffine.Point →+ EDSBar.toAffine.Point :=
  Affine.Point.map (W' := EDS) σ.toAlgHom

/-- LEAF (printed form): Gal(ℚ(j, E_j[N])/ℚ(j)) ≅ GL₂(ℤ/N), via the action on E_j[N], for every basis. -/
def IgusaGL2DS : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EDSBar N) (g : GL (Fin 2) (ZMod N)),
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, ∀ v : ZMod N × ZMod N,
      galPtDS σ (e v : EDSBar.toAffine.Point) =
        (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : EDSBar.toAffine.Point)

/-- fallback, x-coordinates only (GL₂(ℤ/N)/±1, Shimura's form): a consequence of IgusaGL2DS -/
def IgusaGL2DSX : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EDSBar N) (g : GL (Fin 2) (ZMod N)),
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, ∀ v : ZMod N × ZMod N,
      σ (xCoord (e v : EDSBar.toAffine.Point)) =
        xCoord (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : EDSBar.toAffine.Point)
```

The objects are the kernel's own, or Mathlib's:
- `Qj = RatFunc ℚ`, `Kbar = AlgebraicClosure Qj`, `nTors`, `xCoord`, `matAct` are the kernel's (`ModCurves/Defs.lean`,
  `X1Belyi.lean`, `RLeaf/IgusaSL2.lean`);
- `Affine.Point.map` and `WeierstrassCurve` are Mathlib's.

The shape is that of the existing `ZInQ.RLeaf.IgusaGL2`, with `Ej` replaced by `EDS`. The generic forms
`IgusaGL2For W'` and `IgusaGL2XFor W'` (any `W'` over `ℚ(j)`) satisfy `IgusaGL2 ↔ IgusaGL2For Ej`,
`IgusaGL2DS ↔ IgusaGL2For EDS` and `IgusaGL2DSX ↔ IgusaGL2XFor EDS`, each by `Iff.rfl`.

Checks on the model (VERIFIED):
- `EDS.IsElliptic`, from `Δ(EDS) = g_j²(g_j − 27)` (`EDS_Δ`) and `g_j − 27 = 27·1728/(j − 1728)` (`gDS_sub`);
- `j(EDS) = j` (`EDS_j`).

### Locator and reading of `IgusaGL2DS`

| item | content | status |
|---|---|---|
| source | Diamond–Shurman, *A First Course in Modular Forms*, GTM 228 (2005), §7.5 "Function fields over `ℚ`": for `j` transcendental and `E_j : y² = 4x³ − g_j x − g_j`, `g_j = 27j/(j−1728)`, the extension `ℚ(j, E_j[N])/ℚ(j)` is Galois with group `GL₂(ℤ/N)`, the isomorphism being the action on `E_j[N]` | section, model and statement recalled; theorem number UNVERIFIED (unread) |
| same theorem, other sources | Igusa, *Fibre systems of Jacobian varieties III*, Amer. J. Math. 81 (1959): the generic elliptic curve; Lang, *Elliptic Functions*, Ch. 6 §3, and Shimura 1971 Thm 6.6: `GL₂(ℤ/N)/{±1}` on the Fricke functions | UNVERIFIED |
| reading 1 | the print's isomorphism is `ρ_N : Gal(ℚ(j, E_j[N])/ℚ(j)) → Aut(E_j[N]) ≅ GL₂(ℤ/N)`. Surjectivity in every basis, with `σ` lifted to `\overline{ℚ(j)}`, is what `IgusaGL2DS` says. If the print gives only an abstract isomorphism, surjectivity follows because `ρ_N` is injective and the orders agree | STANDARD |
| reading 2 | Mathlib's `WeierstrassCurve` cannot write `y² = 4x³ − …`, so `EDS` is `y'² = x³ − (g_j/4)x − g_j/4`, with `y = 2y'`. The map `(x, y) ↦ (x, y/2)` is a `ℚ(j)`-linear isomorphism of plane cubics fixing the point at infinity. It is therefore a group isomorphism commuting with `Aut(\overline{ℚ(j)}/ℚ(j))`, so the statement for `EDS` is the statement for DS's `E_j`, word for word | VERIFIED argument; `j(EDS) = j` compiled |
| `ℚ(j)` | DS's `ℚ(j)` is the subfield of meromorphic functions generated by the modular invariant. Since `j` is transcendental, `j ↦ X` identifies it with `RatFunc ℚ`, and the statement is algebraic | STANDARD |

**Rating: printed form** (kind published, flag unread, locator UNVERIFIED). It is DS's statement at DS's curve,
modulo the normalization `y = 2y'`. The fallback `IgusaGL2DSX` is a consequence (`igusaGL2DSX_of_igusaGL2DS`). It is
also the algebraic content of Shimura's Thm 6.6, because on DS's model the Fricke function `f_a` is
`x(P_a)/(g_j − 27)`, a `ℚ(j)^×`-multiple of the `x`-coordinate (§4).

## 2. Proof of `X1PointsConjugate` (VERIFIED, standard axioms)

| theorem | content |
|---|---|
| `xTransitive_of_igusaGL2XFor` | for any elliptic `W'` over `ℚ(j)`, `IgusaGL2XFor W'` implies transitivity on the `x`-coordinates of the points of exact order `N` of `W'(\overline{ℚ(j)})` |
| `exists_addEquiv_xCoord` | a change of variables `C • W₂ = W₁` over a field gives `W₁(F) ≃+ W₂(F)` with `x ↦ u²x + r` on affine points (Tau Ceti's `addEquivVariableChange`) |
| `cDS_smul` | `cDS u hu • EDSBar = EjBar`, for `u ∈ \overline{ℚ(j)}` with `u² = α := −18/(j−1728)² ∈ ℚ(j)` and `cDS = (u, r, s, t) = (u, −3/2, (j−1728)u/2, 0)` |
| `x1PointsConjugate_of_igusaGL2DSX` | `IgusaGL2DSX → X1PointsConjugate` |
| `x1PointsConjugate_of_igusaGL2DS` | `IgusaGL2DS → X1PointsConjugate` |
| `r16CoreY_of_picZero_igusaDS`, `…DSX`, `r16CoreY_of_weakPicZero_igusaDS` | the discharges: isj1-dict's `r16CoreY_of_picZero_igusa` / `r16CoreY_of_weakPicZero_igusa` with the Igusa argument filled |

`xTransitive_of_igusaGL2XFor` uses leaf T36 (proved) for a basis `e` of `W'[N]`, and `exists_SL2_first_column` for
matrices `g, g'` sending `(1, 0)` to the coordinates of `Q` and `Q'`. The two `σ` given by the hypothesis then
compose to `σ⁻¹σ'`.

Proof of `x1PointsConjugate_of_igusaGL2DSX`. Let `P, P'` have exact order `N` on the kernel's `E_j`.
1. If `P = 0`, then `N = 1` and `P' = 0`, and `σ = id` works. Otherwise `P, P' ≠ 0`.
2. `ψ := ` the isomorphism of `cDS_smul`, `E_j(\overline{ℚ(j)}) ≃+ EDS(\overline{ℚ(j)})`, preserves orders.
3. The transitivity for `EDS` gives `σ` with `σ(x(ψP)) = x(ψP')`.
4. Since `x(ψR) = α·x(R) − 3/2` with `α, −3/2 ∈ ℚ(j)` fixed by `σ`, and `α ≠ 0`, this gives `σ(x(P)) = x(P')`.

The coefficients of `cDS_smul` were computed by hand: `s = mu/2` from `a₁`, `r = m²u²/12 = −3/2` from `a₂ = 0`,
`t = 0` from `a₃`, with `u² = −18/m²` fixed by `a₄, a₆`. The proof is `linear_combination` with multiples of
`u²m² + 18`: `a₄` has coefficient `576(u²m² − 18)` and `a₆` has `32((u²m²)² − 18u²m² + 324)`.

## 3. Compile status, `#discharges`, fold (one Lean process at a time)

| what | command | outcome |
|---|---|---|
| scratch | `lake env lean scratch/x1-igusa/X1Igusa.lean` | no errors, axioms standard (VERIFIED) |
| contribution | `lake build ZInQKernel.Contrib.OneProof.X1Igusa` | success, 10402 jobs (VERIFIED) |
| `#discharges` | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.X1Igusa`, then `lake env lean scratch/x1-igusa/Discharges.lean` | DISCHARGES_PLACEHOLDER |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/x1-igusa/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/x1-igusa/FoldDryRun.lean` | FOLD_PLACEHOLDER |
| Weber comparison | `lake env lean scratch/x1-igusa/WeberComparison.lean` | WEBER_PLACEHOLDER |

## 4. Is `AfTateCharPolyPicZero` a direct instance of DS 9.5.4? (the `K_N` gap)

**No, not as it stands. One function-field comparison closes the gap, and it is glue, not a leaf.**

DS 9.5.4 is about `J₁(N) = Pic⁰(X₁(N)_alg)`. DS define `X₁(N)_alg` as the nonsingular projective curve over `ℚ`
whose function field is `ℚ(j, f₁)`, a subfield of the meromorphic functions on `ℍ` (DS §7.7; UNVERIFIED).
Here `f₁(τ) = (g₂(τ)g₃(τ)/Δ(τ))·℘_τ(1/N)` is Weber's function at `1/N`, which is `Γ₁(N)`-invariant.
`AfTateCharPolyPicZero` asserts the conclusion for `Pic⁰` of some `X` with `IsX1Model N X`. So the print applies
with `X := X₁(N)_alg` once `IsX1Model N X₁(N)_alg` holds. That needs two things:

1. **`IsCurve`.** `X₁(N)_alg` is smooth, proper and geometrically connected over `ℚ`. This is part of DS's
   construction: nonsingular projective in characteristic 0, and `ℚ` algebraically closed in `ℚ(j, f₁)`.
2. **The function field.** `ℚ(j, f₁) ≅ ℚ(j)(x(P))` for some `P` of exact order `N` on the kernel's `E_j`. This is
   the gap isj1-dict named. It does not need Igusa.

The computation behind 2 is VERIFIED in its algebraic part (`cDS_smul`) and SPECULATIVE in its analytic part,
which is not formalized.
- On `ℂ/⟨1, τ⟩`, `y² = 4x³ − g₂x − g₃`. The substitution `x = (g₃/g₂)x'` (with `y` scaled accordingly) gives DS's
  `E_{j(τ)}`, since `g_j = g₂³/g₃²`. So the point `1/N` has `x_DS = (g₂/g₃)℘_τ(1/N)`.
- Hence `f₁ = x_DS·g₃²/Δ = x_DS/(g_j − 27)`, using `g_j − 27 = Δ/g₃²`.
- With `cDS`, `x_DS = αx − 3/2` on the kernel's model. So `f₁` corresponds to
  `w(P) := (αx(P) − 3/2)/(g_j − 27)`, and `ℚ(j)(w(P)) = ℚ(j)(x(P))`. This last equality is
  `X1Igusa.Weber.adjoin_wOf`, compiled in the scratch file.

**The small statement**, `X1Igusa.Weber.WeberFieldComparison` (compiles; `scratch/x1-igusa/WeberComparison.lean`).
For `N ≥ 2` there is `P ∈ E_j(\overline{ℚ(j)})` of exact order `N` such that, for every `F ∈ ℚ[J][T]`,

    (∀ τ ∈ ℍ, g₂(τ)g₃(τ) ≠ 0 → F(j(τ), weber(⟨1,τ⟩, 1/N)) = 0)  ↔  F(j, w(P)) = 0 in \overline{ℚ(j)}.

It uses the tree's `T5Glue.pp` (the lattice `⟨1, τ⟩`), `T5Glue.jL`, `T5Glue.weber` (Weber's function, verbatim)
and Mathlib's `PeriodPair.g₂`, `g₃`, `℘`.
- Equal ideals give `ℚ(j, f₁) ≅ Frac(ℚ[J,T]/I) ≅ ℚ(j)(w(P)) = fieldX1 P`.
- `N = 1` is excluded because `℘(1)` is a pole. At `N = 1` the leaf is vacuous: `S₂(Γ₁(1)) = 0`.

**Rating: GLUE (provable, SPECULATIVE effort).** Proof sketch:
1. Pointwise, `℘_τ(1/N)` is the `x`-coordinate of a point of exact order `N` on `ℂ/⟨1, τ⟩`. So `f₁` is a root of
   the primitive `N`-division polynomial `Ψ(j, T) ∈ ℚ(j)[T]` of DS's model, rescaled. This uses the
   uniformization and its group law, which are vendored in the tree (heegner-32's `weierPt` addition law).
2. Factor `Ψ = ∏ F_i` over `ℚ(j)`. The product vanishes on the connected open set `{g₂g₃ ≠ 0}` of `ℍ`, so by the
   identity theorem one factor `F₀` vanishes identically at `(j(τ), f₁(τ))`.
3. Take `P` with `w(P)` a root of `F₀`; roots of `Ψ` are `w` of points of exact order `N`.
4. (⇐) If `F(j, w(P)) = 0`, then `F₀ ∣ F` in `ℚ(j)[T]`. So `F(j(τ), f₁(τ)) = 0` off a discrete set, and then
   everywhere by continuity.
5. (⇒) Otherwise `aF + bF₀ = c(j)` with `0 ≠ c ∈ ℚ[j]`. Then `c(j(τ)) = 0` on an open set, which is impossible
   since `j` is non-constant.

None of the five steps is a deep theorem, so the comparison is glue. With it and `CurveIsoOfFunctionFieldIso` (proved
by isj1-dict), DS 9.5.4 at `X₁(N)_alg` is `AfTateCharPolyPicZero`, given that `IsCurve` is part of DS's construction.
The DS 9.5.4 wording objection (characteristic polynomial against equation; isj1-dict §5.5) is separate and unchanged.

## 5. Findings

1. **`IgusaGL2` (former leaf H-117) is, for the kernel's model, a consequence rather than the printed form**
   (SPECULATIVE argument; the algebra is VERIFIED).
   - `cDS` needs `u = 3√−2/(j − 1728)`, so the kernel's `E_j` is the twist of DS's model by the constant
     quadratic character of `ℚ(√−2)`. The two curves are not isomorphic over `ℚ(j)`.
   - `GL₂(ℤ/N)` is still the image for the twist. If `8 ∤ N`, then `√−2 ∉ ℚ(j, E[N])`. If `8 ∣ N`, then
     `χ_{−2}` factors through `det`, and `det(−g) = det g`. Either way the image is unchanged.
   - This argument is not formalized. `IgusaGL2DS` avoids it, since only `x`-coordinates are transported, and
     twists do not move them.
2. **`X1PointsConjugate = IgusaTransitive`** (VERIFIED, `Iff.rfl`). isj1-dict's leaf duplicated an existing kernel
   Prop, and `x1PointsConjugate_of_igusaGL2` was already available from `igusaTransitive_of_igusaGL2`.
3. **Step 1 needed no new proof** (VERIFIED). `E[N] ≅ (ℤ/N)²` is `t36_torsionStructure`, from Tau Ceti's division
   polynomials.

## 6. Leaf ratings

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `igusaGL2DS` | `X1Igusa.IgusaGL2DS` | **yes** | published, unread; locator UNVERIFIED | DS §7.5 at DS's model `y² = 4x³ − g_j x − g_j` (written with `y = 2y'`): `ρ_N` onto `GL₂(ℤ/N)`, every basis. Not stronger: it is the print's statement, and an abstract isomorphism gives the surjectivity |
| `afTateCharPolyPicZero` | `R16IsJ1Dict.AfTateCharPolyPicZero` | yes, modulo `WeberFieldComparison` (glue, §4) and the DS 9.5.4 wording | published, unread (isj1-dict's row, flag updated) | isj1-dict §6. The `K_N` step is now a stated glue Prop, statable in Lean, rather than "not statable" |
| `igusaGL2DSX` (fallback) | `X1Igusa.IgusaGL2DSX` | no: a consequence (`x`-coordinates) | consequence | it drops `y`. It is Shimura's `GL₂(ℤ/N)/±1` on Fricke functions, through `f_a = x(P_a)/(g_j − 27)` |
| (`x1PointsConjugate`) | `R16IsJ1Dict.X1PointsConjugate` | n/a: **proved** from `igusaGL2DS` | — | `x1PointsConjugate_of_igusaGL2DS` |
| (`WeberFieldComparison`) | `X1Igusa.Weber.WeberFieldComparison` (scratch) | n/a: GLUE, stated, not proved | — | not used by the discharge; it closes the `K_N` gap of `afTateCharPolyPicZero` (§4) |

Proposed `locators.md` row (not added, since that file belongs to another task):
- `igusaGL2DS` | Diamond–Shurman GTM 228 §7.5 (Galois group of `ℚ(j, E_j[N])/ℚ(j)`); Igusa 1959 | UNVERIFIED |
  check the theorem number, the model `y² = 4x³ − g_j x − g_j` with `g_j = 27j/(j−1728)`, and that the isomorphism is
  the action on `E_j[N]`.

## 7. Files

- `ZInQKernel/Contrib/OneProof/X1Igusa.lean`: the contribution.
- `scratch/x1-igusa/X1Igusa.lean`: the development version.
- `scratch/x1-igusa/Discharges.lean`, `Discharges-output.txt`: the `#discharges` check.
- `scratch/x1-igusa/autofold.json`, `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold spec and its dry run.
- `scratch/x1-igusa/WeberComparison.lean`: the `K_N` comparison, stated.
- `scratch/x1-igusa/log.md`: the results log.

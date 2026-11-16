# isj1-dict: the `IsJ1` dictionary behind `r16CoreY`, and `AfTateCharPoly` under the weak reading

Task isj1-dict, branch `wip/isj1-dict`, base 60a3fac7 (fork main with leaf-fold28b), with the branches
`wip/r16-used` (dcf24ac6) and `wip/ds965-weak` (b893b3da) merged. Date 2026-11-16.
Lean: `ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean` (new; imports `R16Used`, `DSThm965Weak` and the
vendored `JacobianExists`, not `OneProof.Main`; no build-time code). Scratch: `scratch/isj1-dict/` (results log
`log.md`). Nothing else under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file of this tree. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network on this
host).

## 0. Result

1. **Of the three theorems the review said `IsJ1` needs, one is proved in Lean and one is now a separate
   textbook leaf.** The third, the identification of the function field, remains a dictionary step that cannot
   be stated in Lean today. A fourth step that the review did not list is also needed, the choice of the
   torsion point, and it is now a separate leaf.

   | dictionary step | status |
   |---|---|
   | **Pic⁰ is the Albanese** | **Proved** (VERIFIED). See `abVarIso_picZero_of_isJacobian`: every kernel Jacobian (`IsJacobian`, the Albanese property) is isomorphic to every tensor-compatible representative of the degree-zero Picard scheme `Pic⁰_{X/ℚ}`. The proof uses the vendored Jacobian-Challenge library. Base-point independence (`abVarIso_of_isJacobian`) and transport along curve isomorphisms (`IsJacobian.of_iso`) are proved too. |
   | **a curve is determined by its function field** | New printed leaf `CurveIsoOfFunctionFieldIso`: integral smooth proper geometrically connected curves over `ℚ` with ring-isomorphic function fields are `ℚ`-isomorphic. Sources: Stacks, *Algebraic Curves*, "Curves and function fields"; Hartshorne I.6.12. Both UNVERIFIED. Not proved: a Lean proof needs extension of rational maps through the valuative criterion, spreading out, and gluing, more than this task's budget. |
   | **choice of `P`** (not on the review's list) | New leaf `X1PointsConjugate` (Igusa): for `N ≥ 1`, `Aut(ℚ(j)‾/ℚ(j))` is transitive on the `x`-coordinates of the points of exact order `N` of `E_j`. `IsX1Model` lets `P` vary, so two models can only be compared through this. **Finding:** the statement is false for `N = 0`, so it is stated with `0 < N`. |
   | **`K_N = ℚ(j, f₁)`**: DS's `X₁(N)_alg` is a model in the kernel's sense | **Remains, not stated in Lean.** DS define `X₁(N)_alg` through the Weber function `f₁` (complex-analytic). The kernel uses `ℚ(j)(x(P))` on `E_j`. Stating the comparison needs `f₁`, which has no Lean definition in the tree. The comparison is classical (DS §7.5–7.7, Shimura 1971 Ch. 6; UNVERIFIED). |

2. **`AfTateCharPoly` restated over one model's `Pic⁰`** (VERIFIED). `AfTateCharPolyPicZero` says: there is
   a model `X` of `X₁(N)` such that `J₁(N) = Pic⁰_{X/ℚ}` (a representing abelian variety with the tensor group
   law) satisfies the conclusion of `AfTateCharPoly`. This is the shape of DS's statement: one curve, its
   `Pic⁰`, and `A_f` as a quotient of it. Two directions are proved:
   - `afTateCharPoly_of_picZero`: it implies `AfTateCharPoly` for every `IsJ1` Jacobian, given the two leaves;
   - `afTateCharPolyPicZero_of_afTate`: conversely, it follows from `AfTateCharPoly` and the bundle's
     `X1ModelExists`. So it is never stronger than r16-used's leaf.

3. **The weak reading of DS 9.5.4** (VERIFIED). `AfTateWeakOdd` replaces "has characteristic polynomial" by
   "**satisfies** `X² − a_p X + χ(p)p` over `ℚ_ℓ ⊗ K_f`", and adds **oddness**: complex conjugation has
   determinant `−1` on every `ι`-component. Three things are proved:
   - `r16CoreY_of_weakOdd` (with `mumfordTorsionAlgClosed`) discharges the field;
   - `weakOdd_of_afTate` shows the weak leaf follows from `AfTateCharPoly` (Cayley–Hamilton). It also proves
     oddness from the characteristic polynomials through Chebotarev and `χ(−1) = 1`;
   - the combined form `AfTateWeakOddPicZero` with `r16CoreY_of_dict` discharges the field from the weak leaf
     over `Pic⁰` of one model, the two dictionary leaves, and `mumfordTorsionAlgClosed`.

   The method is ds965-weak's, transferred to each `ι`-component, with the scalar case handled by complex
   conjugation (§3). **The scalar case cannot be excluded from the weak relation alone** (§3.3). The input used
   is oddness, a statement about the same `A`.

4. **Objections to `AfTateCharPoly` that remain** (§5):
   - the `K_N` dictionary step;
   - the two new leaves, which are printed theorems: one is a published statement, the other a consequence of
     Igusa's;
   - the DS 9.5.4 wording, now covered by the weak form, which needs oddness;
   - `A_f` as an existential, unchanged from r16-used.

## 1. Statements

The target is the bundle field `r16CoreY : R16Split.R16CoreY` (`OpenResearchLeaves24` on leaf-fold30). r16-used's
leaf is `R16Used.AfTateCharPoly`, quantified over every `J` with `LeafModCurves.IsJ1 N J`. Its body at one `J`
is `R16IsJ1Dict.AfTateAt N χ f J` (`afTateCharPoly_iff : AfTateCharPoly ↔ ∀ …, IsJ1 N J → AfTateAt N χ f J`
holds by `Iff.rfl`).

`IsJ1 N J` (`ZInQKernel/HDecomp/ModCurves/Defs.lean`) means there are a model `X` of `X₁(N)` and a rational
point `P₀` with `IsJacobian X P₀ J aj`. Here `IsX1Model N X` means: `X` is a smooth proper geometrically
connected integral curve over `ℚ`, with `K(X) ≃+* ℚ(j)(x(P))` for some `P ∈ E_j(ℚ(j)‾)` of exact order `N`.
`IsJacobian` is the Albanese property.

New `Prop`s (all in namespace `R16IsJ1Dict`):

```lean
def X1PointsConjugate : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ (xCoord P) = xCoord P'

def CurveIsoOfFunctionFieldIso : Prop :=
  ∀ (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left], IsCurve X → IsCurve X' →
    Nonempty (X.left.functionField ≃+* X'.left.functionField) → Nonempty (X ≅ X')

def AfTateCharPolyPicZero : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∃ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep ∧ AfTateAt N χ f (ofVendored V)

def AfTateWeakOddAt (N) (χ) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ b : (ℚ_ℓ ⊗ K_f)-basis of V_ℓ(A) (module through θ),
      (∀ (emb : coeffField f →+* PadicAlgCl ℓ) (c : GQ), IsComplexConj c →
          LinearMap.det (frobOn ℓ A θ emb c) = -1) ∧
      ∀ p, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : coeffField f, (c : ℂ) = χ p ∧
          aeval (frobMat ℓ A θ b σ) (esPoly ℓ a_p (c * p)) = 0
def AfTateWeakOdd : Prop := ∀ N χ f J, 0 < N → IsNewform f χ → IsJ1 N J → AfTateWeakOddAt N χ f J
def AfTateWeakOddPicZero : Prop := -- as AfTateCharPolyPicZero with AfTateWeakOddAt
```

`AbelianVariety`, `picardFunctorDegree` and `PicardTensorCompatible` are the vendored Jacobian-Challenge
library's (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`). `ofVendored` turns such a variety into a kernel
`AbVar`; geometric integrality comes from smoothness and geometric irreducibility. `frobMat`, `esPoly`,
`tensorModule` are r16-used's. `frobOn` and `eigenFun` are the kernel's (`ModCurves/Leaves.lean`).
`IsComplexConj` is pkg-I4's. All objects are genuine.

## 2. Part 1: the dictionary (VERIFIED, standard axioms)

| theorem | content |
|---|---|
| `AfTateAt.of_iso` | the body of `AfTateCharPoly` is invariant under an isomorphism `J ≅ J'` of abelian varieties (compose `π` with `e⁻¹`) |
| `isJacobian_picZero` | for a curve `X` (`IsCurve`), a tensor-compatible representation of `Pic⁰_{X/K}` by `V`, and any `K`-point `P₀`, the Abel–Jacobi map `X → V` based at `P₀` is a Jacobian in the kernel's sense (vendored `Curve.isAlbanese_abelJacobiMap`, `IsAlbanese.existsUnique_schemeMap`, rigidity) |
| `abVarIso_picZero_of_isJacobian` | every kernel Jacobian of `X` is isomorphic to every such `V` (**Pic⁰ is the Albanese**) |
| `exists_picZero` | `Pic⁰_{X/K}` has a tensor-compatible representative (vendored `exists_abelianVariety_picardDegreeZero`) |
| `abVarIso_of_isJacobian` | two Jacobians of one curve, at any two base points, are isomorphic |
| `IsJacobian.of_iso` | transport along an isomorphism of curves |
| `fieldX1Equiv` | `σ(x(P)) = x(P')` gives `ℚ(j)(x(P)) ≃ ℚ(j)(x(P'))` (`IntermediateField.adjoin_map`) |
| `abVarIso_of_isJ1` | **uniqueness of `J₁(N)`**: `X1PointsConjugate → CurveIsoOfFunctionFieldIso → 0 < N → IsJ1 N J → IsJ1 N J' → J ≅ J'` |
| `afTateCharPoly_of_exists`, `afTateCharPoly_of_picZero` | `AfTateCharPoly` from its form over one Jacobian / over `Pic⁰` of one model, plus the two leaves. No rational point is assumed on the leaf's model; it is transported from the one in `IsJ1` |
| `afTateCharPolyPicZero_of_afTate` | the converse, given a model with a rational point (`X1ModelExists`) |

Proof of `abVarIso_of_isJ1`. Let `IsJ1 N J` come from `(X, P)` and `IsJ1 N J'` from `(X', P')`.
1. Igusa gives `σ` with `σ x(P) = x(P')`.
2. So `K(X) ≃ ℚ(j)(x(P)) ≃ ℚ(j)(x(P')) ≃ K(X')`.
3. The curve leaf gives `e : X ≅ X'`.
4. `J'` is then a Jacobian of `X` at the base point `P₀' ≫ e⁻¹`.
5. Both `J` and `J'` are isomorphic to `Pic⁰_{X/ℚ}`.

## 3. Part 2: the weak reading of DS 9.5.4 (VERIFIED, standard axioms)

### 3.1 Glue

- `frobAt_pow_of_rootOfUnity`: at a Frobenius in the kernel's sense `GlueC10.IsFrobAt σ p` (a prime `𝔓` of
  `ℤ̄` over `p` with `σx ≡ x^p mod 𝔓`), roots of unity of order prime to `p` go to their `p`-th powers. This is
  hodge-split's argument, moved from valuations to the ideal `𝔓`.
- From it, `cycQ_frobAt` (`χ_ℓ(σ) = p`) and `eps0_frobAt` (`ε₀(σ) = ιL ιC⁻¹ χ(p)`) at `IsFrobAt`. The tree
  had them only at pkg-I4's `IsArithFrob`, and no `IsFrobAt → IsArithFrob` lemma exists.
- `exists_iotaL`: an embedding `ι : F → ℚ̄_ℓ` of a subfield `F ⊆ ℂ` extends to `ιL : ℚ̄ → ℚ̄_ℓ` compatibly with
  a given `ιC : ℚ̄ → ℂ` (Mathlib's `IntermediateField.exists_algHom_of_splits`). So hodge-split's `ε₀` takes
  the values `ι(χ(p))`.
- Matrices:
  - `frobMat_mul` (Galois acts `ℚ_ℓ ⊗ F`-linearly);
  - `compMat = ι_R(frobMat)`, with `trace_det_frobOn`: trace and determinant on the `ι`-component, from
    r16-used's `iota_component`;
  - `aeval_compMat`: the weak relation passes to each `ι`-component;
  - `continuous_compMat_entry`: from `TateModuleFree` and the kernel's `RhoCont`.

### 3.2 `component_charpoly`

Hypotheses: the weak relation at every Frobenius, and `det = −1` at complex conjugation on the
`ι`-component. Conclusion: every Frobenius at `p ∤ Nℓ` has characteristic polynomial `X² − ι(a_p)X + ι(χ(p)p)`
on that component. Write `D` for the determinant on the component and `F = ε₀ χ_ℓ`.

1. Complex conjugation `c` acts non-scalarly. If it acted as a scalar `s`, then `c² = 1` would give `s² = 1`
   and `det = s² = 1 ≠ −1`.
2. On the open non-scalar locus `W`, at Frobenius elements, a non-scalar matrix satisfying a monic quadratic
   has that quadratic as characteristic polynomial (ds965-weak). So `D = F` there.
3. By Chebotarev on open sets (`DS965Weak.eq_on_open_of_eq_on_arithFrob`, from T18), `D = F` on all of `W`.
4. For scalar `σ`, `σc ∈ W`, so `D(σ) = F(σ)`.
5. So `det = F(Frob_p) = ι(χ(p))p ≠ 0` at every Frobenius. A matrix that satisfies the quadratic and has that
   determinant has the quadratic as characteristic polynomial.

### 3.3 Why oddness, and why the scalar case needs an input about `A` (argument, SPECULATIVE)

In ds965-weak the representation was existential, so a scalar `ρ = ψ ⊕ ψ` could be swapped for
`diag(ψ, Fψ⁻¹)`. Here it is the Tate module of the existential `A`, so no swap is possible.

The weak relation alone does not exclude a component on which `G_ℚ` acts by a character `ψ` with `ψ(Frob_p)`
a root of `P_p` for every `p`. Here is why. Let `ψ = ω⟨χ_ℓ⟩^{1/2}`, with `⟨·⟩` the projection to `1 + ℓℤ_ℓ`
and `ω` a character of finite order. Its Frobenius values are algebraic, with `ψ(Frob_p)² = ε(p)p`. Excluding
that `ψ(Frob_p)` is a root of `P_p` for all `p` amounts to a non-trivial statement about the newform. Such a
statement is `a_p² ≠ 4χ(p)p` on a set of positive density, which follows from Rankin–Selberg or Sato–Tate.
None of these is elementary.

Bundle inputs considered and rejected:
- `T12_ComplexConjEigen`: complex conjugation has `g`-dimensional `±1`-eigenspaces on `V_ℓ(A)`. It does not
  exclude scalars on a single `λ`-part when `[K_f:ℚ] > 1`.
- Faltings: it excludes scalars only together with `End⁰_ℚ(A) = K_f` (Ribet 1980).
- The Weil pairing: it does not exclude scalars without the Hecke adjoint.

Oddness is the weakest single input found. It is one group element. It is classical: it follows from
`det ρ_{A_f,ℓ} = χ χ_ℓ` with `χ(−1) = 1`. It is a consequence of the characteristic-polynomial reading, and
**this implication is proved in Lean** (`odd_of_charpoly`, `chi_neg_one_of_newform`, `cycQ_complexConj`,
`eps0_complexConj`).

### 3.4 Results

```lean
theorem R16IsJ1Dict.r16CoreY_of_weakOdd (h : AfTateWeakOdd) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY
theorem R16IsJ1Dict.weakOdd_of_afTate (h : R16Used.AfTateCharPoly) (hT : PkgI3.TateModuleFree) :
    AfTateWeakOdd
theorem R16IsJ1Dict.r16CoreY_of_dict (h : AfTateWeakOddPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
theorem R16IsJ1Dict.r16CoreY_of_picZero (h : AfTateCharPolyPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
theorem R16IsJ1Dict.weakOddPicZero_of_afTate (h : R16Used.AfTateCharPoly) (hT : PkgI3.TateModuleFree)
    (hx : LeafModCurves.X1ModelExists) : AfTateWeakOddPicZero
```

## 4. Compile status, `#discharges`, fold (VERIFIED, 2026-11-16, one Lean process at a time)

| what | command | outcome |
|---|---|---|
| scratch, part 1 | `lake env lean scratch/isj1-dict/Dict.lean` | no errors; axioms standard (`Dict-output.txt`) |
| scratch, part 2 | `lake env lean scratch/isj1-dict/Weak.lean` | no errors; axioms standard |
| contribution | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.R16IsJ1Dict` | success, 13670 jobs. The build tree was copied from ds965-weak's worktree, so this was a partial rebuild. After the final edit (`∃` representative) `lake build +…R16IsJ1Dict` also succeeded. |
| `#discharges` | `lake env lean scratch/isj1-dict/Discharges.lean` | see below (`Discharges-output.txt`) |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/isj1-dict/autofold.json --dry-run`, then line 1 stripped and `lake env lean scratch/isj1-dict/FoldDryRun.lean` | `strict count: 45/10 on 55 -> 47/10 on 57; strictest 43/12 -> 45/12`. `HDec.HSyn.sixContactMin_of_open31` has standard axioms. |
| weak alternative | `autofold.py scratch/isj1-dict/autofold-weak.json --dry-run` | `45/10 -> 46/11; strictest 43/12 -> 44/13`. This is a rise, because the weak leaf is flagged pending reading, so autofold would need `--allow-rise`. |

```
DISCHARGES [OpenResearchLeaves23.r16CoreY] by R16IsJ1Dict.r16CoreY_of_dict
  still assumes: [R16IsJ1Dict.AfTateWeakOddPicZero, R16IsJ1Dict.X1PointsConjugate,
 R16IsJ1Dict.CurveIsoOfFunctionFieldIso, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves23.r16CoreY] by R16IsJ1Dict.r16CoreY_of_picZero
  still assumes: [R16IsJ1Dict.AfTateCharPolyPicZero, R16IsJ1Dict.X1PointsConjugate,
 R16IsJ1Dict.CurveIsoOfFunctionFieldIso, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves23.r16CoreY] by R16IsJ1Dict.r16CoreY_of_weakOdd
  still assumes: [R16IsJ1Dict.AfTateWeakOdd, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 61 open hypotheses, 2400 theorems checked, 11 discharge one
```

The other discharges in the output are earlier contributions, plus r16-used's `R16Used.r16CoreY_of_printed`,
which is present because r16-used was merged. `mumfordTorsionAlgClosed` is already a published LEAF field.

**Fold accounting.**
- `r16CoreY`, a composite GLUE field, is replaced by three leaves:
  - `afTateCharPolyPicZero`: published, unread;
  - `curveIsoOfFunctionFieldIso`: published;
  - `x1PointsConjugate`: consequence, which counts as GLUE.
- GLUE stays at 10 and LEAF rises by 2.
- Under the review's rating of r16-used's leaf (consequence), r16-used's fold would have left GLUE unchanged.
  This fold also leaves it unchanged, but it pins down where the dictionary content sits: one proved step,
  two separate textbook leaves, and the remaining `K_N` step.
- The fold is not applied. `Main.lean`, `kinds.tsv` and `claims.tsv` are unchanged; folding is the
  integrator's step. Folding requires merging `wip/r16-used` and `wip/ds965-weak`, which this file imports.

## 5. Objections to `AfTateCharPoly` that remain

The review gave several reasons; the dictionary ones are taken first.

1. **`K_N = ℚ(j, f₁)` (open, not statable in Lean today).** The print concerns DS's `X₁(N)_alg`, which is
   defined through the Weber function `f₁`, a complex-analytic object. The kernel's `IsX1Model` uses
   `ℚ(j)(x(P))` on `E_j = ofJNe0Or1728 j`.
   - What is needed is the comparison at one point `P`: `ℚ(j, f₁) ≃ ℚ(j)(x(P))`. Here `f₁` is
     `(g₂g₃/Δ)·℘(1/N)` up to normalization, and `x(P)` is an `x`-coordinate on the generic curve. The two
     differ by a `ℚ(j)`-affine change of coordinates. The comparison is classical (DS §7.5–7.7, Shimura 1971
     Ch. 6; UNVERIFIED).
   - Stating it needs `f₁`, either as a meromorphic function or through its `q`-expansion, which has
     coefficients in `ℚ(μ_N)`. The tree has `℘` (gz-hl3) and the `X₀(N)` field of the vendored FLT project
     (q-expansions), but no `X₁(N)` analogue.
   - Two ways to close it: (a) a future task defines `f₁` and states the comparison as a leaf;
     (b) cite a moduli-theoretic Eichler–Shimura statement in which `X₁(N)` is the moduli space of
     `(E, P)`, for instance Conrad's appendix to Ribet–Stein or Diamond–Im §12 (UNVERIFIED). There the
     comparison is "the function field of the moduli space is `ℚ(j)(x(P))`", which again needs moduli spaces
     in Lean.
   - This is the only remaining point at which the print does not apply as a direct instance of
     `AfTateCharPolyPicZero`.
2. **A curve is determined by its function field.** This is now the separate leaf `CurveIsoOfFunctionFieldIso`,
   rated published (object part of the Stacks/Hartshorne equivalence).
   - A Lean proof is a reasonable crowdsourcing item. It needs: extension of the generic point through the
     valuative criterion at each (DVR) stalk; spreading out from `Spec 𝒪_{X,x}` to a neighbourhood (Mathlib's
     EGA IV 8.8.2 in `AffineTransitionLimit.lean`); and gluing by uniqueness on the reduced, separated
     schemes.
   - The kernel already has "a bijective morphism of smooth curves is an isomorphism" (curve-split).
3. **Pic⁰ is the Albanese.** **Closed**: proved in Lean.
4. **Choice of `P`** (Igusa). Not on the review's list, but needed. It is now the separate leaf
   `X1PointsConjugate`, rated consequence: transitivity is a consequence of the printed Galois group
   `GL₂(ℤ/N)` (or `GL₂(ℤ/N)/±1` on `x`-coordinates). A printed-form version would state "the image of
   Galois in `Aut(E[N])/±1` is everything". Deriving transitivity from it then needs `E[N] ≅ (ℤ/N)²` over an
   algebraically closed field of characteristic 0, which is not in Mathlib 4.35 for Weierstrass curves.
5. **DS 9.5.4 wording.** If the print gives only the equation `x² − a_p x + χ(p)p = 0`, then
   `AfTateWeakOddPicZero` with `r16CoreY_of_dict` works. It adds oddness of `ρ_{A_f,ℓ}` (`det ρ(c) = −1`).
   Oddness follows from `det ρ_{A_f,ℓ} = χχ_ℓ`, which Shimura 1971 Thm 7.14 and Ribet 1977 print
   (UNVERIFIED). Under the characteristic-polynomial reading, the weak-odd form is a Lean-proved consequence.
6. **`A_f` as an existential, newforms only, unramifiedness dropped.** Unchanged from r16-used. All three make
   the statement weaker than the print. `A_f` has no Lean definition, since there are no Hecke correspondences
   on `X₁(N)`.
7. **The converse of r16-used** (`AfTateCharPoly` from `r16` plus glue) is still not formalized. It is no longer
   needed for the "never stronger" claims made here, which are proved directly:
   - `afTateCharPolyPicZero_of_afTate` and `weakOddPicZero_of_afTate` derive the new forms from r16-used's
     leaf;
   - r16-used's leaf is the print at DS's objects, modulo point 1.

## 6. Leaf ratings

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `afTateCharPolyPicZero` | `R16IsJ1Dict.AfTateCharPolyPicZero` | **yes, modulo the `K_N` dictionary step** | published, unread (dictionary step and DS wording noted) | It is DS Lemma 9.5.3 + Thm 9.5.4 at DS's objects: one model of `X₁(N)`, its `J₁(N) = Pic⁰`, `A_f` a quotient. `A_f` is existential, and only one representative of `Pic⁰` and one model are asserted. It is not stronger than r16-used's leaf (`afTateCharPolyPicZero_of_afTate`). The print applies as a direct instance once DS's `X₁(N)_alg` is a model in the kernel's sense (§5.1). |
| `afTateWeakOddPicZero` (alternative) | `R16IsJ1Dict.AfTateWeakOddPicZero` | no: weak reading plus oddness | published, pending reading | Under the characteristic-polynomial reading it is a consequence (proved). Under the weak reading it needs oddness from a second source. |
| `x1PointsConjugate` | `R16IsJ1Dict.X1PointsConjugate` | no | consequence | It is transitivity, a consequence of Igusa / Shimura 1971 Thm 6.6 (Galois group `GL₂(ℤ/N)`, resp. `/±1`). False for `N = 0`, hence `0 < N`. |
| `curveIsoOfFunctionFieldIso` | `R16IsJ1Dict.CurveIsoOfFunctionFieldIso` | yes | published | It is the object part of the equivalence between normal proper curves over `k` and function fields (Stacks, Hartshorne I.6.12). |

## 7. Files

- `ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean`: the contribution (parts 1 and 2 and the final discharges).
- `scratch/isj1-dict/Dict.lean`, `Weak.lean`: the two parts as scratch files, with `#print axioms`. They are
  the development versions; the contribution has the final `∃`-representative form of the `Pic⁰` leaves.
- `scratch/isj1-dict/Discharges.lean`, `Discharges-output.txt`: the `#discharges` check.
- `scratch/isj1-dict/autofold.json` (primary), `autofold-weak.json` (weak alternative), `FoldDryRun.lean`,
  `FoldDryRun-output.txt`.
- `scratch/isj1-dict/log.md`: the results log.

Proposed `locators.md` rows (not added, since that file belongs to another task):
- `afTateCharPolyPicZero` | DS GTM 228 §7.7, Lemma 9.5.3, Thm 9.5.4 | UNVERIFIED | `J₁(N) = Pic⁰(X₁(N)_alg)`;
  check the wording "characteristic polynomial" vs "equation".
- `x1PointsConjugate` | Shimura 1971 Thm 6.6; Igusa 1959 | UNVERIFIED | `Gal(F_N/ℚ(j)) ≅ GL₂(ℤ/N)/±1`.
- `curveIsoOfFunctionFieldIso` | Stacks, Algebraic Curves, "Curves and function fields"; Hartshorne I.6.12 |
  UNVERIFIED.

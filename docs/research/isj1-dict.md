# isj1-dict: the `IsJ1` dictionary behind `r16CoreY`, and `AfTateCharPoly` under the weak reading

Task isj1-dict, branch `wip/isj1-dict`, base 60a3fac7 (fork main with leaf-fold28b), with the branches
`wip/r16-used` (dcf24ac6) and `wip/ds965-weak` (b893b3da) merged. Date 2026-11-16.
Lean: `ZInQKernel/Contrib/OneProof/R16IsJ1Dict.lean` (new). Scratch: `scratch/isj1-dict/` (results log
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
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateAt N χ f (ofVendored V)

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

## 4. Compile status, `#discharges`, fold

(Filled in §4 below after the build; see `scratch/isj1-dict/log.md`.)

## 5. Objections to `AfTateCharPoly` that remain

(See §5 below.)

# t09-pic: `t09SymmIsogenyExists` from printed leaves over the genuine Picard functor

Task t09-pic (2026-11-14/15). Field `t09SymmIsogenyExists : HDec.WeilPairing.T09_SymmIsogenyExists`, which says
`∀ K A, Nonempty (SymmIsogeny A)` (Mumford, *Abelian Varieties*, §§6, 8, 20, 23). Files: `scratch/t09-pic/Pic.lean` and
the results log `scratch/t09-pic/log.md`.

## 1. Main result

**The field is proved from five printed leaves.** Four of them are fully concrete statements over genuine objects:
- the relative Picard fppf sheaf `picardFunctor` (vendored);
- its group law `picardFunctorCommGrpObj`;
- `Scheme.Pic`;
- the twisting sheaf `𝒪(1)`;
- Mathlib's connected components and open immersions.

The fifth, Mumford's Weil pairing, is existential in the pairing alone. The dual abelian variety, `φ_L` and `f^∨` are
genuine.

```
theorem T09Pic.t09SymmIsogenyExists_of_printed (h0 : VeryAmpleIsAmple) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h3 : PhiAmpleIsogeny) (h4 : WeilPairingPicZeroPrinted) :
    HDec.WeilPairing.T09_SymmIsogenyExists
```

`scratch/t09-pic/Pic.lean` compiles with 0 errors. `#print axioms` on every theorem gives
`[propext, Classical.choice, Quot.sound]`. VERIFIED.

The file also proves `t09SymmIsogenyExists_of_leaves : L1 → L2 → L3 → L4 → T09` for the very-ample variants of L3 and
L4, with the existential `f^∨`.

No statement was changed. The field's statement is not false, vacuous or inert (weil-pairing's `symmIsogeny_zero` and
c-to-printed2 §5 already argued this).

c-to-printed2 listed four missing pieces, in order. Here is where each one now stands:

| c-to-printed2's missing piece | now |
|---|---|
| 1. `Pic⁰` as an abelian variety (identity component of the Picard scheme) | **Genuine definitions:**<br>- `identityComponent G`, the connected component of the unit point;<br>- `IsPicZero rep B ι`: `ι : B → P` is an open immersion onto the identity component, and is a homomorphism for the Picard group law.<br>**Leaves:** L1 (representability) and L2 (`Pic⁰` is an abelian variety). |
| 2. `φ_L : A → Pic⁰` | **Genuine:**<br>- `mumfordBundle A L = m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹`;<br>- `phiL rep L : A → P`, by Yoneda.<br>**Proved:**<br>- `φ_L(0) = 0`;<br>- `φ_L` factors as `λ_L ≫ ι` with `λ_L : Hom A B`. |
| 3. ample line bundles | **Genuine:**<br>- `IsAmple` (the Stacks definition, over the vendored zero loci and tensor powers);<br>- `IsVeryAmple` (`L = i^*𝒪(1)` for an immersion `i : A → ℙ^N_K`).<br>**Proved:**<br>- every abelian variety over any `K` has a very ample class;<br>- over `K̄`, `IsAmple` is satisfiable.<br>**Leaf:** L0 (very ample ⇒ ample). |
| 4. Mumford's `e_n` | **Still existential** in L4. The dual `f^∨` in L4 is genuine: `dualP`, and `exists_dual_on_picZero` (proved). §5 gives the frontier. |

## 2. Genuine definitions (`Pic.lean` §1, §2b)

Each definition below is built only from Mathlib and the vendored Jacobian-Challenge library in
`ZInQKernel/Contrib/CloudW07JacobiansCurves/`. None is an abstract structure invented for the purpose.

| Lean | meaning |
|---|---|
| `mumfordBundle A L : (pullback A.X.hom A.X.hom).Pic` | `Λ(L) = m^*L * (p₁^*L)⁻¹ * (p₂^*L)⁻¹` (Mumford §8) |
| `phiL rep L : A.X ⟶ P` | `rep.homEquiv.symm (toPicardFunctor.app (op A) Λ(L))`, the classifying map of `Λ(L)` over the second factor. On points, `x ↦ [t_x^*L ⊗ L⁻¹]`. |
| `identityComponent G : Set G.left` | the connected component of `η_G(Spec K)` |
| `IsPicZero rep B ι` | `IsOpenImmersion ι.left ∧ range ι.left = identityComponent P ∧ IsMonHom ι`. This pins `(B, ι)` down up to unique isomorphism. |
| `IsVeryAmple A L` | there are a finite `N`, an immersion `i : A → ℙ(N; Spec K)` over `K`, and `L = Pic.map i [𝒪(1)]` |
| `IsAmple X L` | `X` is quasi-compact, and every point lies in an affine `X_s` for some `s : 𝒪 → L^{⊗n}` with `n ≥ 1` (Stacks 01PS) |
| `picPresheafMap f`, `dualSheafMap f`, `dualP rep f : P ⟶ P` | the pull-back `(f × id)^*` on families, its sheafification, and `f^∨` by Yoneda (Mumford §8) |

## 3. Leaves (`Pic.lean` §3)

Every locator below is UNVERIFIED (from memory, no network). Each leaf is the printed statement, or a consequence of it,
at the genuine objects. Wherever a leaf quantifies `∀ rep` or `∀ (B, ι)`, it is invariant under the unique isomorphisms
of representing objects and of identity components, so these quantifiers are safe.

| leaf | statement | printed source |
|---|---|---|
| L0 `VeryAmpleIsAmple` | `IsVeryAmple A L → IsAmple A.X.left L` | Hartshorne II Thm 7.6; EGA II 4.5.10 |
| L1 `PicRepresentableAbVar` | `picardFunctor A.X.hom` is representable (statement copied from c-to-printed2's `T09Roadmap.lean`) | Murre (1964) and Oort (1962) for proper `X` over a field; FGA Exp. 232 Thm 3.1, and Kleiman *The Picard scheme* Thm 9.4.8 with Thm 9.2.5, for projective `X` |
| L2 `PicZeroAbVar` | for every `rep` there are an abelian variety `B` and `ι : B → P` with `IsPicZero rep B ι` | Mumford §13 (`Â = Pic⁰`, reduced, dimension `g`) over `K̄`; Kleiman Prop. 9.5.3 and 9.5.1 (open and closed, of finite type, compatible with field extension); Milne 1986 §§9–10 |
| L3 `PhiAmpleIsogeny` | for `IsPicZero rep B ι`, `L` ample and `λ ≫ ι = φ_L`, the map `λ` is finite and surjective | Mumford §6 Application 1 (`K(L)` finite) and §8 Thm 1 (`φ_L` onto `Â`); fpqc descent from `K̄` |
| L4 `WeilPairingPicZeroPrinted` | there are `e_n : A[n] × Pic⁰[n] → μ_n` that are perfect, `G_K`-equivariant and compatible, with `e_n(x, f^∨y) = e_n(fx, y)` for the genuine `f^∨`, and `e_n(x, λ_L x) = 1` for ample `L` | Mumford §20 (`ē_n` and its properties) and §23 (`e^L_n(x, x) = 1`); Milne 1986 §16 (defined over `K`) |

**Why L4 is a consequence of the print and not stronger.**
- The existential is witnessed by Mumford's `ē_n` at `Â = Pic⁰`.
- Each clause is one printed property. These are the same five clauses that c-to-printed2 §5 and weil-pairing matched
  to Mumford for `WeilDual`.
- What is new compared with the field: the dual variety, `λ = φ_L` and `f^∨` are no longer existential. They are the
  genuine `Pic⁰`, `φ_L` and `f^∨`, and the alternation clause is about genuine `φ_L` for ample `L`.

## 4. Glue (proved in `Pic.lean` §2, §2b, §4, §5)

- `exists_isVeryAmple`: every abelian variety over any field has a very ample class. It comes from the vendored
  `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`.
- `comp_classify`: Yoneda naturality. For `f : T' ⟶ T`, `f ≫ class(c) = class(Pic.map (f × id) c)`.
- `mumfordBundle_restrict_zero`: `Λ(L)|_{A×0} = 1`. It uses `m ∘ (id, 0) = p₁` (`MonObj.mul_one`) and
  `Pic(Spec K) = 1` (vendored).
- `eta_comp_phiL`: `η_A ≫ φ_L = η_P`, so `φ_L(0) = 0` for the Picard group law.
- `exists_hom_comp_eq_phiL`: for every `(B, ι)` with `IsPicZero`, `φ_L = λ_L ≫ ι` with `λ_L : Hom A B`. The steps:
  `A` is connected and `φ_L(0) = 0`, so the image lies in the identity component; lift through the open immersion; the
  lift is a homomorphism by `MulRigidity.isMonHom_of_geometricallyIntegral`.
- `eta_comp_dualP` and `exists_dual_on_picZero`: `f^∨(0) = 0`, and `f^∨` restricts to an endomorphism of `Pic⁰`, by the
  same connectedness and rigidity argument.
- `phiVeryAmpleIsogeny_of_printed`, `weilPairingPicZero_of_printed`, `t09SymmIsogenyExists_of_leaves`,
  `t09SymmIsogenyExists_of_printed`: the assembly. `D := (B, e)` is a `WeilDual` field by field, and `λ := λ_L` for a
  very ample `L`.
- `exists_isAmple_of_isAlgClosed`: non-vacuity of `IsAmple` over `K̄`, from the vendored
  `GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace`.

## 5. Frontier

**Definitions that now exist:** `Λ(L)`, `φ_L`, `f^∨` (on `P` and on `Pic⁰`), the identity component, "`(B, ι)` is
`Pic⁰`", very ample, and ample.

**Printed statements that are now statable:**
- L0–L3;
- Mumford §20 (5) with the genuine `f^∨`;
- Mumford §23 with the genuine `φ_L`.

**What remains existential:** only Mumford's pairing `ē_n` in L4.

**Next missing piece:** a genuine `ē_n`. In order, it needs:
- (a) the `K̄`-points of `Pic⁰` as line bundles on `A_K̄`. This is Kleiman Thm 9.2.5: `Pic(A_T)/Pic(T) ≅ Pic_{A/K}(T)`
  when `A` has a section. It is statable today over `toPicardFunctor`.
- (b) translations `t_x` and `[n]` on `A_K̄`, and the identity `[n] ∘ t_x = [n]` for `x ∈ A[n]`;
- (c) a trivialization `[n]^*M ≅ 𝒪` for `M ∈ Pic⁰[n]` (a leaf, Mumford §8);
- (d) the scalar `t_x^*ψ ∘ ψ⁻¹ ∈ Γ(A_K̄, 𝒪)^× = K̄^×` (`H⁰(A, 𝒪) = K̄` for `A` proper and geometrically integral).

(Work on this frontier continues below if time allows.)

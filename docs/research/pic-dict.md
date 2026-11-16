# pic-dict: the three Pic-dictionary rows

Task pic-dict. Base e22df37cd (fork main after leaf-fold30). Rows (all fields of `HDec.HSyn.OpenAddedLeaves17`,
`TailZ34.lean:111`; statements in `ZInQKernel/OneProof/H/TailZ24.lean`): `T09Pic.PicZeroAbVar` (l.302),
`T09Pic.PhiAmpleIsogeny` (l.366), `T09Pic.WeilPairingMumford` (l.708). On fork main after leaf-fold31 (cove-80) all
three are rated `consequence`, GLUE/GLUE.

## 1. Result

| row | result | new leaves | glue | strict / strictest GLUE change on the lf31 rating |
|---|---|---|---|---|
| `weilPairingMumford` | **replaced by leaves + Lean glue** | 6 of Mumford's displays over an algebraically closed field (§6 Cor. 4, §8 (iv), §8 Thm 1, §20 twice, §23) and EGA II 4.6.13; the field `phiAmpleIsogeny` stays | all proved: L5, the dictionary, the base change to `K̄`, the Galois, compatibility and adjoint clauses | **−1 / −1** |
| `phiAmpleIsogeny` | reduced; **one combined step remains** | `mumfordKLFiniteAC` (§6 App. 1), `picZeroPtsTranslInv` (composite); shares §8 Thm 1 and EGA II 4.6.13 | all proved (finiteness, surjectivity, dictionary) | 0 / 0 |
| `picZeroAbVar` | not reduced; **combined step identified** (§5) | none | none | unchanged |

Everything below is VERIFIED: compiled, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

* `ZInQKernel/Contrib/OneProof/PicDictionary.lean`, namespace `PicDict`, 92 KB. It imports
  `ZInQKernel.OneProof.H.TailZ24` and the vendored `…/Modules/FreeGeneratorPullback`. `lake build
  ZInQKernel.Contrib.OneProof.PicDictionary` succeeds.
* The main results:
  * `theorem PicDict.weilPairingMumford_of_ac (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairingAC)
    (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC) (h3 : PhiAmpleIsogeny) : T09Pic.WeilPairingMumford`
  * `theorem PicDict.phiAmpleIsogeny_of_ac (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) : T09Pic.PhiAmpleIsogeny`
  * The same with the leaves stated at `X = A_K̄` in the kernel's coordinates: `weilPairingMumford_of_printed`,
    `phiAmpleIsogeny_of_printed`. The `*AC` leaves imply these (`mumfordSquare_of_ac` and so on).
* Proved on the way:
  * `PicDict.picPointsAlgClosed : T09Pic.PicPointsAlgClosed`: **L5 is a theorem.**
  * `weilFormulaGaloisEx`: the Galois clause, by transport of structure along `1 × Spec σ`.
  * `mumfordWeilDual_of_pairing` and `mumfordWeilCompat_of_pairing`: Mumford §20's adjoint and compatibility
    properties follow from bilinearity, by transport along `f × 1` and along `m_A`. They are not leaves.
  * L6 (`T09Pic.MulNTrivialPicZero`) is not needed. The proof derives it from `MumfordMulNPicZeroAC` and the
    dictionary (step `htriv`).
  * `finiteOfFiniteKerPts`: a homomorphism of abelian varieties over `K` with finitely many `K̄`-points in its
    kernel is finite.
* The consumer `T09Pic.t09SymmIsogenyExists_of_four` and its users are unchanged.

`#discharges` (`scratch/pic-dict/Discharges.lean`, output `scratch/pic-dict/discharges.txt`; the `*_of_printed`
forms are also listed):

```
DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_of_ac
  still assumes: [PicDict.MumfordKLFiniteAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.PicZeroPtsTranslInv]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_ac
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 59 open hypotheses, 3007 theorems checked, 11 discharge one
```

### Autofold

The recommended spec is `scratch/pic-dict/autofold.json`. It discharges `weilPairingMumford` by
`weilPairingMumford_of_ac … {n}.phiAmpleIsogeny`, with 7 published leaves.

* On this base it prints `strict count: 40/8 on 48 -> 46/8 on 54; strictest 39/9 -> 46/8`. No `--allow-rise` is
  needed, because this base still rates the row strict LEAF.
* On the lf31 rating (the three rows set to consequence GLUE/GLUE in a temporary copy of `kinds.tsv`, then
  restored) it prints `strict count: 37/11 on 48 -> 44/10 on 54; strictest 37/11 -> 44/10`.
* The printed module compiles: `scratch/pic-dict/FoldDryRun.lean`, line 1 stripped, gives
  `sixContactMin_of_open35` with the standard axioms.

The alternative spec `scratch/pic-dict/autofold-both.json` also discharges `phiAmpleIsogeny`, adding
`mumfordKLFiniteAC` and `picZeroPtsTranslInv` (kind composite).

* On this base it prints `40/8 on 48 -> 46/9 on 55; strictest 39/9 -> 46/9` and needs `--allow-rise`.
* On the lf31 rating it prints `37/11 on 48 -> 45/10 on 55; strictest 37/11 -> 45/10`.
* Its dry-run module also compiles (`scratch/pic-dict/FoldDryRunBoth.lean`).
* Folding `phiAmpleIsogeny` gains nothing until `picZeroPtsTranslInv` is read as one print (§4). The recommended
  fold is `weilPairingMumford` alone.

## 2. Glue, all proved

The kernel's side:

* the fppf sheaf `picardFunctor A.X.hom`, the sheafification of `T ↦ Pic(A ×_K T)`;
* a representing `P`;
* `B` with `IsPicZero rep B j`;
* the classes `picClass rep j y ∈ Pic(A_K̄)` and `weilScalar`.

Mumford's side is an abelian variety `X` over an algebraically closed field `k`:

* `X(k) = (𝟙_ ⟶ X.X)` and `t_x = lift (𝟙, toUnit ≫ x) ≫ μ` (`AC.tr`), `n_X = 𝟙^n` (`AC.mul`);
* `Pic⁰(X)`: the classes invariant under every `t_x` (`AC.IsTI`), and `X̂_n` (`AC.IsDT`);
* `φ_L(x) = t_x^*L ⊗ L⁻¹` (`AC.phi`);
* `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` (`AC.formula`), which is the right side of `T09Pic.weilScalar_spec`.

1. **L5 (`picPointsAlgClosed`).** Every fppf covering sieve of a scheme contains every point with values in an
   algebraically closed field (`fppf_arrows_of_isAlgClosed`). The proof is by induction on
   `Precoverage.Saturate`. A covering family is jointly surjective, flat and locally of finite presentation, so its
   pull-back along `Spec k → X` is a nonempty scheme locally of finite type over `k`, which has a `k`-point by
   Mathlib's `pointOfClosedPoint` (Nullstellensatz). So at `T = Spec K̄` every covering sieve of `Over (Spec K)` is
   maximal (`over_fppf_id_mem`), and Mathlib's `isLocallyInjective_toSheafify'` and
   `isLocallySurjective_toSheafify'` give bijectivity.
2. **Base change (`AKbar`, `pts`).** `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A`, with the group law
   transported by the monoidal functor. Its scheme is the kernel's `A ×_K K̄`.
   * `pts : A(K̄) ≃* A_K̄(K̄)`: `pts_mul`, `pts_injective`, `pts_surjective`.
   * `(t_{pts x}).left = (transl x).left` (`tr_pts`, via Mathlib's `μ_pullback_left_*`).
   * `n_{A_K̄} = n_A` (`mul_AKbar`).
   * Mumford's formula on `A_K̄` is the kernel's `weilFormula` (`formula_bridge`).
   * Each `*AC` leaf then gives its instance at `A_K̄` (`mumfordSquare_of_ac`, …, `mumfordWeilAlt_of_ac`).
3. **Dictionary.**
   * `y ↦ M_y` is an injective homomorphism `B(K̄) → Pic(A_K̄)` (`picClass_mul`, `picClass_injective`).
   * `M_{λ_L x} = φ_{L_K̄}(x)` (`picClass_phiL`, via `map_mumfordBundle_pt`).
   * `M_{f^∨ y} = (f × 1)^* M_y` (`picClass_dual`) and `M_{σy} = (1 × Spec σ)^* M_y` (`picClass_gal`).
   * `B(K̄) ⊆ Pic⁰`: `λ_L` is surjective (field `phiAmpleIsogeny`), `K̄`-points lift along it (`exists_lift_pt`),
     and then the theorem of the square applies (`phiPt_translInv`).
   * `Pic⁰ ⊆ B(K̄)`: Mumford §8 Thm 1 for the ample `L_K̄`.
   * For `y ∈ B[n]` a trivialization exists (`nonempty_triv`), so `weilScalar = weilFormula` (step `hspec`).
4. **Transport of Mumford's formula** (`Transport.wf_transport`, `wf_transport₂`). If `g : X → X` intertwines the
   translations and commutes with `n` (respectively, if `n = g ≫ m`), then `g` carries the formula to `g.appTop` of
   the formula. The proof uses:
   * `pullbackObjUnitIso_comp`, compatibility of `𝒪`-pull-back with `pullbackComp`, through the adjunction mate
     `conjugateEquiv_pullbackComp_inv`;
   * the pseudofunctor coherences `coherence_I`, `coherence_II` and `coherence_III`, from Mathlib's
     `pseudofunctor_associativity`;
   * the vendored `pullbackObjUnitIso_conj_app_top`.

   Three instances: the Galois clause, with `g = 1 × Spec σ`, which acts on constants by `σ` (`gal_constK`); the
   adjoint clause, with `g = f × 1` (`mumfordWeilDual_of_pairing`); and compatibility, with `g = m_A`
   (`mumfordWeilCompat_of_pairing`).
5. **`phiAmpleIsogeny`.**
   * `surjective_of_forall_pt`: the image of the proper `λ` is closed and contains every closed point, since every
     closed point carries a `K̄`-point (`exists_pt_of_isClosed`).
   * `finiteOfFiniteKerPts`: over a closed point there are finitely many `K̄`-points (`finite_pts_over`, counting the
     `K`-embeddings of `κ(b)`), and the fibres are kernel cosets. So `λ` is quasi-finite at closed points. Mathlib's
     `isOpen_quasiFiniteAt` (ZMT) and Jacobson give quasi-finite everywhere, and proper plus quasi-finite is finite.

## 3. New leaves and their rating

The `*AC` leaves quantify over every algebraically closed field `k` and every `X : AbVar k`. Each states one of
Mumford's displays in the definitions of §2. None mentions the kernel's `P`, `rep`, `B`, `j` or `K`. The passage to
the kernel (base change to `K̄`, Kleiman 9.2.5 at `Spec K̄`, the identification of `B(K̄)`) is all in the Lean
glue. All locators are UNVERIFIED: there is no copy of Mumford, Kleiman, EGA or Milne on the host.

| leaf (field) | display | printed form? | reason |
|---|---|---|---|
| `mumfordSquareAC` | Mumford §6 Cor. 4 (theorem of the square) | yes | for every `L` and `x, y ∈ X(k)` |
| `mumfordMulNPicZeroAC` | Mumford §8 (iv): `n^*L ≅ Lⁿ` for `L ∈ Pic⁰` | yes | stated for `n ∈ ℕ`; Mumford states it for `n ∈ ℤ` |
| `mumfordPhiSurjectiveAC` | Mumford §8 Thm 1: `L` ample, `M ∈ Pic⁰` ⇒ `M ≅ t_x^*L ⊗ L⁻¹` | yes | `IsAmple` is the EGA/Stacks notion, which is Mumford's on a complete variety |
| `ampleBaseChangeAlgClosure` | EGA II 4.6.13 (iii): ample stays ample under field extension | yes (instance `K' = K̄`) | one statement |
| `mumfordWeilPairingAC` | Mumford §20: `ē_n` by `t_x^*ψ ∘ ψ⁻¹` is well defined, `μ_n`-valued and bilinear | yes, with a note | well-definedness (independence of `ψ`) belongs to the definition; the clause `∀ ψ ψ'` states it. Stated for `p ∤ n` |
| `mumfordWeilNondegAC` | Mumford §20: `ē_n` nondegenerate, `p ∤ n` | yes | "both kernels trivial" is a consequence of "perfect" |
| `mumfordWeilAltAC` | Mumford §23: `e^L_n(x, x) = 1` with `e^L_n(x, y) = ē_n(x, φ_L(y))` | yes | for every `L` |
| `mumfordKLFiniteAC` | Mumford §6 App. 1: `K(L)` finite for ample `L` | yes, with a note | printed for `L = 𝒪(D)`, `D` effective; for general ample `L`, `L^m` is effective and `K(L) ⊆ K(L^m)` |
| `picZeroPtsTranslInv` | Kleiman 9.5.10 + Mumford §8 | **no (composite)** | it identifies the `K̄`-points of the identity component of the fppf `Pic_{A/K}` with Mumford's `Pic⁰(A_K̄)`. It would clear with one print in identity-component form; candidates are Milne 1986 §10 and BLR 8.4 (pending reading) |

Statements that were leaves in a first version and are now proved in Lean:

* the adjoint clause (Mumford §20 (5), printed only for isogenies) and compatibility (§20);
* the Galois clause (Milne 1986 §16);
* L5 (Kleiman 9.2.5 at `Spec K̄`) and L6 (Mumford §8 (iv) on the kernel's `Pic⁰`);
* the identification of the kernel's `B(K̄)` with Mumford's `Pic⁰(A_K̄)`, for the Weil row only.

**Smoothness of `B`** (question in the brief). `B : AbVar K` carries Mathlib's `Smooth`. Mumford §13 gives `Â` as an
abelian variety, a complete group variety over `k = k̄`. Nonsingular implies smooth over an algebraically closed
field, and a reduced group scheme of finite type over `k̄` is smooth (Mumford §4, homogeneity plus generic
smoothness; UNVERIFIED). Over `K`, smoothness of `Pic⁰_{A/K}` descends from `K̄`: it is fpqc local on the base
(EGA IV 17.7.1(ii); Stacks 02VL; UNVERIFIED), and `Pic⁰_{A/K} ×_K K̄ = Pic⁰_{A_K̄/K̄}` (Kleiman 9.5.1). So smooth
versus nonsingular is two theorem steps, nonsingular to smooth and descent, as the unif-printed review counted.
Both sit inside the combined step of §5.

## 4. `phiAmpleIsogeny`: the step that is still combined

All glue is proved. The one non-printed input is `picZeroPtsTranslInv`, used to show that `λ_L` is onto on
`K̄`-points. `weilPairingMumford` avoids it by reading the surjectivity of `λ_L` from the field `phiAmpleIsogeny`;
`phiAmpleIsogeny` cannot use its own field.

A dimension count does not avoid it. `λ_L` is finite (proved), so surjectivity would follow from
`dim B ≤ dim A`. Bounding `|B[n]|` by `|X̂_n|` needs `M_y ∈ Pic⁰` for `y ∈ B[n]`, which is the same inclusion.
Without that inclusion, Mumford's statements cannot be applied to `M_y` at all. So the row is 0 until a reading
turns `picZeroPtsTranslInv` into one print, for example "`A^∨(k̄) = Pic⁰(A_k̄)` for the identity component
`A^∨` of `Pic_{A/k}`" in Milne 1986 §10. The row would then be −1.

## 5. `picZeroAbVar`: the combined step

The row asks for `∃ B j, IsPicZero rep B j` for every representation `rep`. The steps:

* **(Z1)** `P` is locally of finite type over `K` (Kleiman 9.4.8; the existing L1 only states representability).
* **(Z2)** The identity component `G⁰` is open and closed, a subgroup, geometrically irreducible and of finite type
  (SGA 3 VI_A 2.4 / Kleiman 9.5.1). gt-sga3's `SGA3IdComp.lean` proves closure under `μ` and openness from a
  neighbourhood leaf.
* **(Z3)** `G⁰` is smooth and proper over `K`.
* **(Z4)** The restricted group law makes `G⁰` an `AbVar`, with `j` an open immersion and a homomorphism. This is
  Lean glue, not done.

(Z3) is the combined step. Mumford §13 constructs `Â = X/K(L)` over `k̄` and shows that it represents the functor of
families with fibres in `Pic⁰`. To conclude that the identity component of the fppf `Pic_{A_K̄/K̄}` is `Â` as a
scheme one needs:

1. the identification of §4 at the level of schemes;
2. `(G⁰)_K̄ = (G_K̄)⁰` (Kleiman 9.5.1);
3. descent of smooth and proper along `K̄/K` (EGA IV 17.7.1, 2.7.1).

These are three sources. As the lf31 row says, the row would clear with one print over an arbitrary field in
identity-component form ("`Pic⁰_{A/K}` is an abelian variety": BLR 8.4, FGA Explained 9.5, Milne 1986 §10; pending
reading). Using the field `phiAmpleIsogeny` to get properness would be circular, since it presupposes `B`. No
decomposition was folded, so the count is unchanged. Replacing the row by printed (Z1), (Z2) and a composite (Z3)
would leave the strict GLUE count unchanged, at the cost of the Lean glue (Z4).

## 6. What remains

* Reading:
  * Milne 1986 §10, BLR 8.4 or Kleiman §9.5, for one print of `picZeroPtsTranslInv`, and of `picZeroAbVar` in
    identity-component form;
  * the locators of §3, in particular that §23 states `e^L_n(x, x) = 1` (rather than only skew-symmetry) and that
    §20 includes well-definedness.
* Optional Lean, not needed for the `weilPairingMumford` fold:
  * a proof of `AmpleBaseChangeAlgClosure` (the vendored `Hom.comap_zeroLocus` is the main tool);
  * parts of `MumfordWeilPairingAC` (independence of `ψ`, constancy and additivity in `x` are formal; bilinearity
    in `M` needs pull-back of tensor products).

Files: `scratch/pic-dict/` holds the development copies (`Core.lean`, `Transport.lean`, `Finite.lean`, `Dual.lean`,
`Compat.lean`, `AlgClosed.lean`), plus `Discharges.lean`, `discharges.txt`, `autofold.json`,
`autofold-both.json`, `FoldDryRun*.lean` and `log.md`. The deliverable is
`ZInQKernel/Contrib/OneProof/PicDictionary.lean`.

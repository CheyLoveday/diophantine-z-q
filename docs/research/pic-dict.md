# pic-dict: the three Pic-dictionary rows

Task pic-dict. Base e22df37cd (fork main after leaf-fold30). Rows (all fields of `HDec.HSyn.OpenAddedLeaves17`,
`TailZ34.lean:111`; statements in `ZInQKernel/OneProof/H/TailZ24.lean`): `T09Pic.PicZeroAbVar` (l.302),
`T09Pic.PhiAmpleIsogeny` (l.366), `T09Pic.WeilPairingMumford` (l.708). On fork main after leaf-fold31 (cove-80) all
three are rated `consequence`, GLUE/GLUE.

## 1. Result

| row | result | new leaves | glue | strict / strictest GLUE change on the lf31 rating |
|---|---|---|---|---|
| `weilPairingMumford` | **replaced by leaves + Lean glue** | 9 instances of Mumford's displays at `X = A_K̄` (one also Milne), plus the existing field `phiAmpleIsogeny` | all proved, including L5, the dictionary and the Galois clause | **−1 / −1** |
| `phiAmpleIsogeny` | reduced; **one combined step remains** | `mumfordKLFinite`, `picZeroPtsTranslInv` (composite); shares `mumfordPhiSurjective`, `ampleBaseChangeAlgClosure` | all proved (finiteness, surjectivity, dictionary) | 0 / 0 |
| `picZeroAbVar` | not reduced; **combined step identified** (§5) | none | none | unchanged |

All of the following is VERIFIED (compiled; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`).

* `ZInQKernel/Contrib/OneProof/PicDictionary.lean` (namespace `PicDict`, 60 KB, imports
  `ZInQKernel.OneProof.H.TailZ24` and the vendored `…/Modules/FreeGeneratorPullback`). `lake build
  ZInQKernel.Contrib.OneProof.PicDictionary` succeeds.
* `theorem PicDict.weilPairingMumford_of_printed (hsq : MumfordSquare) (h8iv : MumfordMulNPicZero)
  (h8 : MumfordPhiSurjective) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairing)
  (h20b : MumfordWeilNondeg) (h20c : MumfordWeilCompat) (h20d : MumfordWeilDual) (h23 : MumfordWeilAlt)
  (h3 : PhiAmpleIsogeny) : T09Pic.WeilPairingMumford`
* `theorem PicDict.phiAmpleIsogeny_of_printed (hKL : MumfordKLFinite) (h8 : MumfordPhiSurjective)
  (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) : T09Pic.PhiAmpleIsogeny`
* `theorem PicDict.picPointsAlgClosed : T09Pic.PicPointsAlgClosed`: **L5 is a theorem.**
* `theorem PicDict.weilFormulaGaloisEx`: the Galois clause by transport of structure. With L5 and
  `T09Pic.weilScalar_spec`, the hypothesis `T09Pic.MulNTrivialPicZero` (L6) is no longer needed; the proof derives
  it from `MumfordMulNPicZero` and the dictionary (step `htriv`).
* `theorem PicDict.finiteOfFiniteKerPts`: a homomorphism of abelian varieties over `K` whose kernel has finitely many
  `K̄`-points is a finite morphism.

The consumer `T09Pic.t09SymmIsogenyExists_of_four` and its users are unchanged. A fold only replaces the field
`weilPairingMumford`, or both fields, by the new leaves.

`#discharges` (`scratch/pic-dict/Discharges.lean`, output `scratch/pic-dict/discharges.txt`):

```
DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_of_printed
  still assumes: [PicDict.MumfordKLFinite,
 PicDict.MumfordPhiSurjective,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.PicZeroPtsTranslInv]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_printed
  still assumes: [PicDict.MumfordSquare,
 PicDict.MumfordMulNPicZero,
 PicDict.MumfordPhiSurjective,
 PicDict.AmpleBaseChangeAlgClosure,
 PicDict.MumfordWeilPairing,
 PicDict.MumfordWeilNondeg,
 PicDict.MumfordWeilCompat,
 PicDict.MumfordWeilDual,
 PicDict.MumfordWeilAlt,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 59 open hypotheses, 2942 theorems checked, 9 discharge one
```

### Autofold

The recommended spec is `scratch/pic-dict/autofold.json`. It discharges `weilPairingMumford` and adds 9 published
leaves. Its proof uses `{n}.phiAmpleIsogeny`, which stays a field.

* On this base, `python3 scripts/one_proof/autofold.py scratch/pic-dict/autofold.json --dry-run` prints
  `strict count: 40/8 on 48 -> 48/8 on 56; strictest 39/9 -> 48/8`. No `--allow-rise` is needed, because this
  base still rates the row strict LEAF.
* On the lf31 rating (the three rows set to consequence GLUE/GLUE in a temporary copy of `kinds.tsv`, then
  restored) it prints `strict count: 37/11 on 48 -> 46/10 on 56; strictest 37/11 -> 46/10`.
* The printed module compiles: `scratch/pic-dict/FoldDryRun.lean`, line 1 stripped, gives
  `sixContactMin_of_open35` with the standard axioms.

The alternative spec `scratch/pic-dict/autofold-both.json` also discharges `phiAmpleIsogeny`, with
`mumfordKLFinite` (published) and `picZeroPtsTranslInv` (kind composite).

* On this base it prints `strict count: 40/8 on 48 -> 48/9 on 57; strictest 39/9 -> 48/9` and needs
  `--allow-rise`.
* On the lf31 rating it prints `37/11 on 48 -> 47/10 on 57; strictest 37/11 -> 47/10`.
* Its dry-run module also compiles (`scratch/pic-dict/FoldDryRunBoth.lean`).
* Folding `phiAmpleIsogeny` gains nothing until `picZeroPtsTranslInv` is read as one print (§4).

## 2. The dictionary at `K̄`, proved

The kernel's objects are: the fppf sheaf `picardFunctor A.X.hom` (sheafification of `T ↦ Pic(A ×_K T)`), a
representing `P`, `B` with `IsPicZero rep B j`, the classes `picClass rep j y ∈ Pic(A_K̄)` and `weilScalar`.
Mumford's objects are, for `X = A_K̄ = pullback A.X.hom (ptK K).hom`:

* `Pic⁰(X)`, the classes invariant under every `t_x` with `x ∈ A(K̄)`: `IsTranslInv`;
* `X̂_n`: `IsDualTors n`;
* `φ_L(x) = t_x^*L ⊗ L⁻¹`: `phiPt`;
* `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹`: `weilFormula`, literally the right side of `T09Pic.weilScalar_spec`.

The passage between the two, every step proved:

* **L5 (`picPointsAlgClosed`).** Every fppf covering sieve of a scheme contains every point with values in an
  algebraically closed field (`fppf_arrows_of_isAlgClosed`). The proof is by induction on
  `Precoverage.Saturate`: a covering family is jointly surjective, flat and locally of finite presentation, so its
  pull-back along `Spec k → X` is a nonempty scheme locally of finite type over `k` and has a `k`-point by
  Mathlib's `pointOfClosedPoint` (Nullstellensatz). So at `T = Spec K̄` every covering sieve of `Over (Spec K)` is
  maximal (`over_fppf_id_mem`), and Mathlib's `isLocallyInjective_toSheafify'` and
  `isLocallySurjective_toSheafify'` give bijectivity. `Pic(Spec K̄) = 1` is not needed.
* **`y ↦ M_y` is an injective homomorphism `B(K̄) → Pic(A_K̄)`** (`picClass_mul`, `picClass_injective`, `picHom`).
* **Translations.** `t_z ∘ t_x = t_{z+x}` (`transl_comp_transl`). `φ_L(x) ∈ Pic⁰` follows from the theorem of the
  square (`phiPt_translInv`).
* **`φ_L` on points.** `M_{λ_L x} = φ_{L_K̄}(x)` (`picClass_phiL`, via `map_mumfordBundle_pt`).
* **Dual on points.** For `f^∨` on `Pic⁰`, `M_{f^∨ y} = (f × 1)^* M_y` (`picClass_dual`).
* **Galois on points.** For `σ ∈ G_K`, `M_{σy} = (1 × Spec σ)^* M_y` (`picClass_gal`).
* **`B(K̄) ⊆ Pic⁰(A_K̄)`** (step `hsub`). Write `y = λ_L(x)`: `λ_L` is surjective by the field `phiAmpleIsogeny`,
  and `K̄`-points lift along a surjective morphism locally of finite type (`exists_lift_pt`, Nullstellensatz). Then
  apply the theorem of the square.
* **`Pic⁰(A_K̄) ⊆ B(K̄)`** (step `hsup`). This uses Mumford §8 Thm 1 for the ample `L_K̄` and `picClass_phiL`.
* **Trivializations.** For `y ∈ B[n]`, `n_A^*M_y = M_y^n = 1` gives a trivialization (`nonempty_triv`), so
  `weilScalar = weilFormula` with no default branch (step `hspec`).
* **Galois equivariance by transport of structure** (`weilFormulaGaloisEx`). The generic transport theorem
  `Transport.wf_transport` says: if `g : X → X` satisfies `t' ≫ g = g ≫ t` and `g ≫ m = m ≫ g`, then `g` carries
  Mumford's formula for `(t, M, ψ)` to `g.appTop` of the formula for `(t', g^*M, ψ')`. Its proof consists of:
  * `pullbackObjUnitIso_comp`, compatibility of `𝒪`-pull-back with `pullbackComp`, through the adjunction mate
    `conjugateEquiv_pullbackComp_inv`;
  * the pseudofunctor coherences `coherence_I` and `coherence_II`, from Mathlib's `pseudofunctor_associativity`;
  * the vendored `pullbackObjUnitIso_conj_app_top`.

  `1 × Spec σ` commutes with `n_A`, intertwines `t_x` and `t_{σx}`, and acts on constants by `σ` (`gal_constK`).
  This is the route the weil-used review suggested.
* **Assembly.** The pairing `e` is built from the values of `weilScalar` (`mkPairing`), and each clause is
  transported. The values are pinned by `weilScalar` by construction.

For `phiAmpleIsogeny`:

* `surjective_of_forall_pt`: the image of the proper `λ` is closed and contains every closed point, because each
  closed point carries a `K̄`-point (`exists_pt_of_isClosed`), and `B` is Jacobson.
* `finiteOfFiniteKerPts`: the closed points over a closed point are finitely many (`finite_pts_over` counts the
  `K`-embeddings of `κ(b)` into `K̄`; `finite_fiber_pts` uses kernel cosets). So the fibres are discrete there and
  `λ` is quasi-finite at closed points. Mathlib's `isOpen_quasiFiniteLocus` (ZMT) and Jacobson then give quasi-finite
  everywhere, and proper plus quasi-finite gives finite (`IsFinite.of_isProper_of_locallyQuasiFinite`).

## 3. New leaves and their rating

Every leaf except `ampleBaseChangeAlgClosure` and `picZeroPtsTranslInv` is Mumford's statement for the abelian
variety `X = A_K̄` over the algebraically closed field `k = K̄`.

* `X(k)` is written as `A(K̄) = Hom_K(Spec K̄, A)`, which is equal to `X(K̄)` by the universal property of the fibre
  product.
* `t_x` is `(transl x).left`, `n_X` is `(mulN A n).left`, and `Pic(X)` is the vendored `Scheme.Pic` of the scheme
  `A ×_K K̄`.
* None of them mentions the kernel's `P`, `rep`, `B` or `j`. That passage is all in the Lean glue (§2).

All locators are UNVERIFIED: there is no copy of Mumford, Kleiman or Milne on the host.

| leaf (field) | Lean | display | printed form? | reason |
|---|---|---|---|---|
| `mumfordSquare` | `MumfordSquare` | Mumford §6 Cor. 4 (theorem of the square) | yes (instance) | the print, for every `L` and `x, y ∈ X(k)` |
| `mumfordMulNPicZero` | `MumfordMulNPicZero` | Mumford §8 (iv), `n^*L ≅ Lⁿ` on `Pic⁰` | yes (instance) | the print, for `n ∈ ℕ` (Mumford: `n ∈ ℤ`) |
| `mumfordPhiSurjective` | `MumfordPhiSurjective` | Mumford §8 Thm 1 (`M ∈ Pic⁰ ⇒ M ≅ t_x^*L ⊗ L⁻¹`, `L` ample) | yes (instance) | `IsAmple` is the EGA/Stacks ampleness, which equals Mumford's on a complete variety |
| `ampleBaseChangeAlgClosure` | `AmpleBaseChangeAlgClosure` | EGA II 4.6.13 (iii): ample stays ample under field extension | yes (instance `K' = K̄`) | one statement; also provable in Lean (vendored `Hom.comap_zeroLocus`; not done) |
| `mumfordWeilPairing` | `MumfordWeilPairing` | Mumford §20: `ē_n` well defined, `μ_n`-valued, bilinear | yes, with a note | definition plus bilinearity on one page of §20. Well-definedness (independence of `ψ`) is part of the definition; the clause `∀ ψ ψ'` states it |
| `mumfordWeilNondeg` | `MumfordWeilNondeg` | Mumford §20: `ē_n` nondegenerate, `p ∤ n` | yes (instance) | "both kernels trivial" is a consequence of "perfect" |
| `mumfordWeilCompat` | `MumfordWeilCompat` | Mumford §20: `ē_{nm}(x, L) = ē_n(mx, L)` | yes (instance) | |
| `mumfordWeilDual` | `MumfordWeilDual` | Mumford §20 (5) for isogenies; Milne 1986 16.2(c) for homomorphisms | yes, with a note | stated for every `f ∈ End_K(A)`, base-changed; Mumford's print covers isogenies, Milne's every homomorphism (but Milne's `e_n` is the Cartier-duality pairing). A direct Lean proof exists in principle (same transport as Galois, with `g = f × 1`); not done |
| `mumfordWeilAlt` | `MumfordWeilAlt` | Mumford §23: `e^L_n(x, x) = 1`, `e^L_n(x, y) = ē_n(x, φ_L(y))` | yes (instance) | for every `L` (a special case is used: `L_K̄` for `L` ample over `K`) |
| `mumfordKLFinite` | `MumfordKLFinite` | Mumford §6 App. 1: `K(L)` finite | yes, with a note | printed for `L = 𝒪(D)` with `D` effective; for ample `L`, `L^m` is effective and `K(L) ⊆ K(L^m)` (one standard step) |
| `picZeroPtsTranslInv` | `PicZeroPtsTranslInv` | Kleiman 9.5.10 + Mumford §8 | **no (composite)** | it identifies the `K̄`-points of the identity component of the fppf `Pic_{A/K}` with Mumford's `Pic⁰`. It would clear with one print in identity-component form; candidates are Milne 1986 §10 and BLR 8.4 (pending reading) |

Notes on scope:

* "Instance" means Mumford's display with `X := A_K̄`. The leaves are stated for every field `K` and every
  `A : AbVar K`; the abelian variety in Mumford's sense is `A_K̄` (`PkgI3.AbVar.baseChange` exists, and its scheme is
  `pullback A.X.hom (ptK K).hom`).
* A stricter rendering would quantify over `k` algebraically closed and `X : AbVar k`, with translations
  `lift (𝟙, toUnit ≫ x) ≫ μ`. It would need a Lean bridge to the K-coordinates used here: the group law of
  `Over.pullback`'s `grpObjObj` against `transl`. That bridge is not done. A reviewer who rates "instance at `A_K̄`"
  as not printed should ask for it; it is formal (no new mathematics).
* **Smoothness of `B`** (question in the brief). `B : AbVar K` carries Mathlib's `Smooth`. Mumford §13 gives `Â` as
  an abelian variety, a complete group variety over `k = k̄`. Nonsingular implies smooth for a variety over an
  algebraically closed field, and a reduced group scheme of finite type over `k̄` is smooth (Mumford §4,
  homogeneity plus generic smoothness; UNVERIFIED). Over `K`, smoothness of `Pic⁰_{A/K}` descends from `K̄`: it is
  fpqc local on the base (EGA IV 17.7.1(ii); Stacks 02VL; UNVERIFIED), and `Pic⁰_{A/K} ×_K K̄ = Pic⁰_{A_K̄/K̄}`
  (Kleiman 9.5.1). So smooth versus nonsingular is two theorem steps, nonsingular to smooth and descent. Both sit
  inside the combined step of §5; the unif-printed review was right to count it.

## 4. `phiAmpleIsogeny`: the step that is still combined

All glue is proved (§2). The one non-printed input is `picZeroPtsTranslInv`, used to show that `λ_L` is onto on
`K̄`-points. `weilPairingMumford` avoids it by reading the surjectivity of `λ_L` from the field `phiAmpleIsogeny`
itself, so its leaves need no composite. `phiAmpleIsogeny` cannot read its own field.

Without the composite leaf, the known route to surjectivity is dimension: `λ_L` is finite (proved), so
`dim λ_L(A) = dim A`, and one needs `dim B ≤ dim A`. That inequality can be read off torsion counts with the leaves
already present. `|B[n]| ≤ |X̂_n|` holds by `picClass_injective`; `|X̂_n| ≤ |Hom(A[n], μ_n)|` holds by
`mumfordWeilNondeg` and `mumfordWeilPairing`, with no circularity. The rest needs:

* `|A[n]| = n^{2 dim A}` (Mumford §4 App. 2, a printed leaf);
* dimension theory of finite morphisms and closed irreducible subsets in Lean.

This route was not attempted, for lack of time. With it, `phiAmpleIsogeny` would be −1.

## 5. `picZeroAbVar`: the combined step

`∃ B j, IsPicZero rep B j` for every representation `rep`. The steps:

* **(Z1)** `P` is locally of finite type over `K`. This is Kleiman 9.4.8; the existing L1 states only
  representability.
* **(Z2)** The identity component `G⁰` is open and closed, a subgroup, geometrically irreducible and of finite type
  (SGA 3 VI_A 2.4 / Kleiman 9.5.1). The Lean `SGA3IdComp.lean` (gt-sga3) proves closure under `μ` and openness from
  a neighbourhood leaf.
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
reading). No decomposition was folded, so the fold count is unchanged. Replacing the row by printed (Z1), (Z2) and a
composite (Z3) would leave the strict GLUE count unchanged, at the cost of Lean glue (Z4).

## 6. What remains

* Reading: Milne 1986 §10 / BLR 8.4 / Kleiman §9.5 for a single print of `picZeroPtsTranslInv`, and of
  `picZeroAbVar` in identity-component form. Every locator in §3.
* Optional Lean, none needed for the `weilPairingMumford` fold:
  * a proof of `AmpleBaseChangeAlgClosure` (one leaf fewer);
  * `mumfordWeilDual` and `mumfordWeilCompat` by `Transport.wf_transport` (two leaves fewer);
  * the `k`-algebraically-closed restatement with the base-change bridge;
  * the dimension route of §4.

Files: `scratch/pic-dict/` (`Core.lean`, `Transport.lean`, `Finite.lean`, the development copies; `Discharges.lean`;
`autofold*.json`; `FoldDryRun*.lean`; `log.md`). The deliverable is `ZInQKernel/Contrib/OneProof/PicDictionary.lean`.

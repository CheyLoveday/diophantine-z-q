# pic-dict: the three Pic-dictionary rows

Task pic-dict. Base e22df37cd (fork main after leaf-fold30). Rows (all fields of `HDec.HSyn.OpenAddedLeaves17`,
`TailZ34.lean:111`; statements in `ZInQKernel/OneProof/H/TailZ24.lean`): `T09Pic.PicZeroAbVar` (l.302),
`T09Pic.PhiAmpleIsogeny` (l.366), `T09Pic.WeilPairingMumford` (l.708). On fork main after leaf-fold31 (cove-80) all
three are rated `consequence`, GLUE/GLUE.

## 1. Result

| row | result | new leaves (each one printed display) | glue | strict / strictest change on the lf31 rating |
|---|---|---|---|---|
| `weilPairingMumford` | **replaced by leaves + Lean glue** | Mumford over `k = k̄`: §6 Cor. 4, §8 (iv), §8 Thm 1, §20 (definition and bilinearity), §20 (nondegenerate), §23 | all proved: L5, the dictionary, base change to `K̄` (including ampleness), and the Galois, compatibility and adjoint clauses | **−1 / −1** |
| `phiAmpleIsogeny` | **replaced by leaves + Lean glue** | Mumford §6 App. 1 over `k̄`; EGA III 7.8.6 (`𝒪 = f_*𝒪` universally); EGA IV 4.6.5 (products of geometrically integral schemes); shares §8 Thm 1 | all proved: finiteness, surjectivity, the dictionary, and `K̄`-points of `Pic⁰` being translation-invariant | **−1 / −1** |
| `picZeroAbVar` | **reduced to four statements, glue proved**; one is pending reading | Kleiman 9.4.8 (Pic locally of finite type), SGA 3 VI_A 2.4 (identity component), Kleiman 9.5.4 (`Pic⁰` proper); `picZeroSmooth` (`Pic⁰_{A/K}` smooth: pending reading, §5) | all proved: the open subgroup scheme as an `AbVar`, smooth ⇒ geometrically reduced | 0 / 0 now; −1 / −1 if a reading clears `picZeroSmooth` |

Folding both rows (`scratch/pic-dict/autofold-both.json`): `strict count: 37/11 on 48 -> 46/9 on 55; strictest
37/11 -> 46/9` on the lf31 rating, that is −2 / −2, with 9 new printed leaves.

Folding all three rows (`scratch/pic-dict/autofold-all.json`): `37/11 on 48 -> 49/9 on 58; strictest 37/11 -> 49/9`.
The count is the same as for two rows, because the pending-reading leaf `picZeroSmooth` is counted GLUE in place of
the row. If a reading clears `picZeroSmooth`, the three rows together give −3 / −3.

Everything below is VERIFIED: compiled, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

* `ZInQKernel/Contrib/OneProof/PicDictionary.lean`, namespace `PicDict`, about 115 KB, no build-time code. It imports
  `ZInQKernel.OneProof.H.TailZ24` and four vendored modules (`…/Modules/FreeGeneratorPullback`,
  `…/Picard/Descent`, `…/Modules/PullbackMonoidal`, `…/IdealSheaf/Image`). `lake build ZInQKernel.Contrib.OneProof.PicDictionary` succeeds.
* The main results:
  * `theorem PicDict.weilPairingMumford_of_mumford (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20a : MumfordWeilPairingAC) (h20b : MumfordWeilNondegAC)
    (h23 : MumfordWeilAltAC) (h3 : PhiAmpleIsogeny) : T09Pic.WeilPairingMumford`
  * `theorem PicDict.phiAmpleIsogeny_of_mumford (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC)
    (hU : PushforwardUnitUniversal) (hGI : GeomIntegralProd) : T09Pic.PhiAmpleIsogeny`
  * Intermediate forms, also compiled and listed by `#discharges`:
    * `weilPairingMumford_of_printed` and `phiAmpleIsogeny_of_printed`, with the leaves stated at `X = A_K̄` in the
      kernel's coordinates;
    * `weilPairingMumford_of_ac` and `phiAmpleIsogeny_of_leaves`, which also take the leaf `AmpleBaseChangeAlgClosure`
      (now proved);
    * `phiAmpleIsogeny_of_ac`, with the composite `PicZeroPtsTranslInv` as a hypothesis.
* Proved on the way:
  * `picPointsAlgClosed : T09Pic.PicPointsAlgClosed`: **L5 is a theorem.**
  * `weilFormulaGaloisEx`: the Galois clause, by transport of structure along `1 × Spec σ`.
  * `mumfordWeilDual_of_pairing` and `mumfordWeilCompat_of_pairing`: the adjoint and compatibility properties follow
    from bilinearity, by transport along `f × 1` and along `m_A`.
  * L6 (`T09Pic.MulNTrivialPicZero`) is not needed. The proof derives it from `MumfordMulNPicZeroAC` and the
    dictionary.
  * `picZeroPtsTranslInv_of_leaves`: the `K̄`-points of the identity component of `Pic_{A/K}` are
    translation-invariant classes, by rigidity on `A × Pic⁰` (§2.6).
  * `finiteOfFiniteKerPts`: a homomorphism of abelian varieties with finitely many `K̄`-points in its kernel is
    finite.
  * `ampleBaseChangeAlgClosure` (EGA II 4.6.13 at `K̄`): ampleness pulls back along an affine morphism
    (`isAmple_pullback`).
  * `picZeroAbVar_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : PicZeroProper) : T09Pic.PicZeroAbVar`. The open subscheme on the identity component becomes a group
    object (`AVGlue.grpObjOfMono`), smooth gives geometrically reduced (`isReduced_of_smooth_field`), and with
    geometric irreducibility this gives geometrically integral.
* The consumer `T09Pic.t09SymmIsogenyExists_of_four` and its users are unchanged.

`#discharges` (`scratch/pic-dict/Discharges.lean`, output `scratch/pic-dict/discharges.txt`; the intermediate forms
are also listed, 15 lines in all; the `picZeroAbVar` line is `DISCHARGES
[OpenAddedLeaves17.picZeroAbVar] by PicDict.picZeroAbVar_of_leaves`, still assuming its four statements):

```
DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_of_mumford
  still assumes: [PicDict.MumfordKLFiniteAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.PushforwardUnitUniversal,
 PicDict.GeomIntegralProd]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_mumford
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 59 open hypotheses, 3057 theorems checked, 15 discharge one
```

### Autofold

The recommended spec is `scratch/pic-dict/autofold-both.json`. It makes two discharges:

* `weilPairingMumford` by `weilPairingMumford_of_mumford … (phiAmpleIsogeny_of_mumford …)`, with 6 leaves;
* `phiAmpleIsogeny` by `phiAmpleIsogeny_of_mumford …`, with 3 more leaves (`mumfordKLFiniteAC`,
  `pushforwardUnitUniversal`, `geomIntegralProd`).

All 9 leaves are kind published, flagged unread.

* On this base `autofold.py --dry-run` prints `strict count: 40/8 on 48 -> 47/8 on 55; strictest 39/9 -> 47/8`. No
  `--allow-rise` is needed, because this base still rates both rows strict LEAF.
* On the lf31 rating (the three rows set to consequence GLUE/GLUE in a temporary copy of `kinds.tsv`, then restored)
  it prints `strict count: 37/11 on 48 -> 46/9 on 55; strictest 37/11 -> 46/9`.
* The printed module compiles: `scratch/pic-dict/FoldDryRunBoth.lean`, line 1 stripped, gives
  `sixContactMin_of_open35` with the standard axioms.

`scratch/pic-dict/autofold.json` folds `weilPairingMumford` alone, keeping the field `phiAmpleIsogeny`.

* On this base: `40/8 on 48 -> 45/8 on 53; strictest 39/9 -> 45/8`.
* On the lf31 rating: `37/11 -> 43/10; strictest 37/11 -> 43/10`.
* Its dry-run module also compiles (`scratch/pic-dict/FoldDryRun.lean`).

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
   `Precoverage.Saturate`; Mathlib's `pointOfClosedPoint` (Nullstellensatz) gives the points. So at `T = Spec K̄`
   every covering sieve is maximal (`over_fppf_id_mem`), and Mathlib's `isLocallyInjective_toSheafify'` and
   `isLocallySurjective_toSheafify'` give bijectivity.
2. **Base change (`AKbar`, `pts`).** `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A`, with the group law
   transported by the monoidal functor.
   * `pts : A(K̄) ≃* A_K̄(K̄)`.
   * `(t_{pts x}).left = (transl x).left` (`tr_pts`, via Mathlib's `μ_pullback_left_*`).
   * `n_{A_K̄} = n_A` (`mul_AKbar`).
   * Mumford's formula on `A_K̄` is the kernel's `weilFormula` (`formula_bridge`).
   * Each `*AC` leaf gives its instance at `A_K̄` (`*_of_ac`).
3. **Dictionary.**
   * `y ↦ M_y` is an injective homomorphism `B(K̄) → Pic(A_K̄)`.
   * `M_{λ_L x} = φ_{L_K̄}(x)` (`picClass_phiL`).
   * `M_{f^∨ y} = (f × 1)^* M_y` and `M_{σy} = (1 × Spec σ)^* M_y`.
   * `Pic⁰ ⊆ B(K̄)` by Mumford §8 Thm 1.
   * `B(K̄) ⊆ Pic⁰`: in the Weil row from the surjectivity of `λ_L` (field `phiAmpleIsogeny`, `exists_lift_pt`) and
     the theorem of the square; in the `phiAmpleIsogeny` row by item 6.
   * For `y ∈ B[n]` a trivialization exists, so `weilScalar = weilFormula`.
4. **Transport of Mumford's formula** (`Transport.wf_transport`, `wf_transport₂`). The proof uses
   `pullbackObjUnitIso_comp` (`𝒪`-pull-back versus `pullbackComp`, through the adjunction mate) and the
   pseudofunctor coherences `coherence_I`–`coherence_III` (from Mathlib's `pseudofunctor_associativity`). It has
   three instances: Galois with `g = 1 × Spec σ`, adjoint with `g = f × 1`, and compatibility with `g = m_A`.
5. **Finiteness and surjectivity of `λ_L`.**
   * `surjective_of_forall_pt`: the image of the proper `λ_L` is closed and contains every closed point, since every
     closed point carries a `K̄`-point.
   * `finiteOfFiniteKerPts`: finitely many `K̄`-points over each closed point give quasi-finiteness at closed
     points. Mathlib's `isOpen_quasiFiniteAt` (ZMT) and Jacobson give quasi-finite everywhere, and proper plus
     quasi-finite is finite.
6. **`K̄`-points of `Pic⁰` are translation-invariant** (`picZeroPtsTranslInv_of_leaves`).
   * With `pushforwardUnitUniversal`, the vendored Kleiman 9.2.5 (`picardFunctorNormalizedIso`) identifies the
     Picard sheaf with honest classes on `A ×_K T`, normalized along `0`.
   * For a `T`-point `a` of `A`, the renormalized `t_a^*c ⊗ c⁻¹` (`dT`) is natural in `T` (`dT_natural`).
   * Classifying it at `T = A ⊗ B`, with `c` the universal class pulled back from `B`, gives `Ψ : A ⊗ B → P`.
     `Ψ` is trivial on `A × 0` and on `0 × B` (`dT_one`, `dT_zero`).
   * `A ⊗ B` is connected (`geomIntegralProd`), so `Ψ` lands in `B`. It is a homomorphism by the project's rigidity
     theorem (`MulRigidity.isMonHom_of_geometricallyIntegral`, with `A ⊗ B` geometrically integral), hence trivial.
   * At `K̄`-points (`Pic(Spec K̄) = 1`) this says `t_x^*M_y = M_y`.

## 3. New leaves and their rating

The `*AC` leaves quantify over every algebraically closed field `k` and every `X : AbVar k`. Each states one of
Mumford's displays in the definitions of §2, and none mentions the kernel's `P`, `rep`, `B`, `j` or `K`. All
locators are UNVERIFIED: there is no copy of Mumford, Kleiman, EGA or Milne on the host.

| leaf (field) | display | printed form? | reason |
|---|---|---|---|
| `mumfordSquareAC` | Mumford §6 Cor. 4 (theorem of the square) | yes | for every `L` and `x, y ∈ X(k)` |
| `mumfordMulNPicZeroAC` | Mumford §8 (iv): `n^*L ≅ Lⁿ` for `L ∈ Pic⁰` | yes | stated for `n ∈ ℕ`; Mumford states it for `n ∈ ℤ` |
| `mumfordPhiSurjectiveAC` | Mumford §8 Thm 1: `L` ample, `M ∈ Pic⁰` ⇒ `M ≅ t_x^*L ⊗ L⁻¹` | yes | `IsAmple` is the EGA/Stacks notion, which is Mumford's on a complete variety |
| `mumfordWeilPairingAC` | Mumford §20: `ē_n` by `t_x^*ψ ∘ ψ⁻¹` is well defined, `μ_n`-valued and bilinear | yes, with a note | well-definedness (independence of `ψ`) belongs to the definition; stated for `p ∤ n` |
| `mumfordWeilNondegAC` | Mumford §20: `ē_n` nondegenerate, `p ∤ n` | yes | "both kernels trivial" is a consequence of "perfect" |
| `mumfordWeilAltAC` | Mumford §23: `e^L_n(x, x) = 1`, `e^L_n(x, y) = ē_n(x, φ_L(y))` | yes | for every `L` |
| `mumfordKLFiniteAC` | Mumford §6 App. 1: `K(L)` finite for ample `L` | yes, with a note | printed for `L = 𝒪(D)`, `D` effective; general ample `L` via `L^m` effective and `K(L) ⊆ K(L^m)` |
| `pushforwardUnitUniversal` | EGA III 7.8.6; Kleiman, *The Picard scheme*, Ex. 9.3.11: `𝒪_S = f_*𝒪_X` universally for `f` proper flat with geometrically integral fibres | yes (instance `f = A → Spec K`, base change `T`), with a note | over a field it is also flat base change (Stacks 02KH) with `Γ(A, 𝒪) = K`; the cited prints state it universally |
| `geomIntegralProd` | EGA IV 4.6.5 (products of geometrically integral schemes over a field) | yes (instance `A × B`) | Mathlib v4.35 lacks it (noted in `HDecomp/Faltings/H5Neron.lean`) |

Leaves of `picZeroAbVar_of_leaves` (spec `autofold-all.json`):

| leaf (field) | display | printed form? | reason |
|---|---|---|---|
| `picLocFinType` | Kleiman 9.4.8: `Pic_{X/S}` exists, separated, locally of finite presentation | yes, with a note | stated for every representing object, which is isomorphic to Kleiman's by Yoneda |
| `identityComponentLFT` | SGA 3 VI_A 2.4 (Stacks 0B7R; Kleiman 9.5.1): `G⁰` open, a subgroup, geometrically irreducible | yes | general statement for group schemes locally of finite type over a field |
| `picZeroProper` | Kleiman 9.5.4: `Pic⁰_{X/K}` proper for `X` proper and geometrically normal | yes (instance) | an abelian variety is geometrically normal |
| `picZeroSmooth` | `Pic⁰_{A/K}` smooth | **pending reading** | Mumford §13 proves it over `k̄` (`dim Â = h¹(𝒪) = g`); over `K` it needs descent and the identification of Mumford's `Â` with the identity component, unless BLR 8.4 or Milne 1986 §10 prints it in one statement |

Notes on the statements:

* Each formula-based leaf quantifies over trivializations `ψ : 𝒪 ≅ n^*M`. Such a `ψ` exists for every
  `M ∈ X̂_n` by `mumfordMulNPicZeroAC` (Mumford §8 (iv)). Given that, "for every `ψ`" and "for some `ψ`" agree
  with Mumford's `ē_n(x, M)`, so every leaf is the print and never stronger.
* `mumfordMulNPicZeroAC` at `n = 0` is true: `0_X` factors through `Spec k`, and `Pic(Spec k) = 1`.
* For `docs/research/locators.md`, each new leaf is a row with the locator of the table above, verdict UNVERIFIED.

Statements that were leaves in a first version and are now proved in Lean:

* the adjoint clause (Mumford §20 (5), printed only for isogenies) and compatibility (§20);
* the Galois clause (Milne 1986 §16);
* L5 (Kleiman 9.2.5 at `Spec K̄`) and L6;
* the composite `picZeroPtsTranslInv` (Kleiman 9.5.10 + Mumford §8);
* EGA II 4.6.13 at `K̄` (`ampleBaseChangeAlgClosure`);
* `finiteOfFiniteKerPts`.

**Smoothness of `B`** (question in the brief). `B : AbVar K` carries Mathlib's `Smooth`. Mumford §13 gives `Â` as an
abelian variety, a complete group variety over `k = k̄`. Nonsingular implies smooth over an algebraically closed
field, and a reduced group scheme of finite type over `k̄` is smooth (Mumford §4; UNVERIFIED). Over `K`, smoothness
of `Pic⁰_{A/K}` descends from `K̄`: it is fpqc local on the base (EGA IV 17.7.1(ii); Stacks 02VL; UNVERIFIED), and
`Pic⁰_{A/K} ×_K K̄ = Pic⁰_{A_K̄/K̄}` (Kleiman 9.5.1). So smooth versus nonsingular is two theorem steps,
nonsingular to smooth and descent, as the unif-printed review counted. Both sit inside the combined step of §5.

## 4. Remark on `phiAmpleIsogeny`

A first version needed the composite leaf `PicZeroPtsTranslInv` (the `K̄`-points of the identity component of the
fppf `Pic_{A/K}` are translation-invariant). §2.6 proves it from two printed statements, so the row is now −1. The
Weil row could use the same lemma instead of reading the surjectivity of `λ_L` from `phiAmpleIsogeny`; with the
both-rows fold this makes no difference.

## 5. `picZeroAbVar`: four statements, one pending reading

`picZeroAbVar_of_leaves` proves the row from:

* (Z1) `picLocFinType`;
* (Z2) `identityComponentLFT`;
* (Z3a) `picZeroSmooth`;
* (Z3b) `picZeroProper`.

The glue is proved. The open subscheme on the identity component, with the restricted multiplication, unit and
inverse (lifted through the open immersion), is a group object. Its structure map is proper by (Z3b) and smooth by
(Z3a). Smooth gives geometrically reduced (proved), and (Z2) gives geometrically irreducible, so it is geometrically
integral. The inclusion is an open immersion onto the identity component and a homomorphism.

The one statement not known to be a single print is (Z3a), smoothness over `K`. Mumford §13 gives it over `k̄`
(`Â = Pic⁰` is reduced since `dim T₀ = h¹(𝒪_A) = g = dim Â`). Over `K` this is combined with:

* the identification of Mumford's `Â` with the identity component of the fppf Picard scheme;
* descent along `K̄/K` (EGA IV 17.7.1) and Kleiman 9.5.1.

A single print over an arbitrary field ("`Pic⁰_{A/K}` is an abelian variety": BLR 8.4, FGA Explained 9.5, Milne
1986 §10) would clear it. Then all three rows are −1. Properness is not derived from `λ_L`: every surjectivity
argument in §2 presupposes `B`, so that would be circular. Kleiman 9.5.4 supplies it directly.

## 6. What remains

* Reading:
  * the locators of §3, in particular that §23 states `e^L_n(x, x) = 1` (rather than only skew-symmetry), that §20
    includes well-definedness, and the exact form of EGA III 7.8.6 / Kleiman Ex. 9.3.11;
  * BLR 8.4 / Milne 1986 §10 (or Kleiman §9.5) for a single print of `picZeroSmooth`, and the locators of
    Kleiman 9.4.8 and 9.5.4.
* Optional Lean:
  * parts of `MumfordWeilPairingAC` (independence of `ψ`, constancy and additivity in `x` are formal);
  * `GeomIntegralProd` (a Mathlib gap);

Files: `scratch/pic-dict/` holds the development copies (`Core.lean`, `Transport.lean`, `Finite.lean`, `Dual.lean`,
`Compat.lean`, `AlgClosed.lean`, `TranslInv.lean`, `Ample.lean`, `PicZero.lean`), plus `Discharges.lean`, `discharges.txt`, `autofold.json`,
`autofold-both.json`, `autofold-all.json`, `FoldDryRun*.lean` and `log.md`. The deliverable is
`ZInQKernel/Contrib/OneProof/PicDictionary.lean`.

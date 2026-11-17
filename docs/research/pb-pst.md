# pb-pst: Pan's and Berger's leaves of `r11r12`, from consequence towards printed form

Task pb-pst, 2026-11-17. Base: `wip/leaf-fold33b` 75d94fe7 (with its merge of `origin/main`, 4dfb7e58). Lean:
`ZInQKernel/Contrib/OneProof/PanBergerPst.lean` (generated from `scratch/pb-pst/BmaxOne.lean` and
`scratch/pb-pst/HTFinite.lean` by `scratch/pb-pst/mkcontrib.py`). It imports `PanBergerDict` and `AxSenTate`, not
`Main`. Results log: `scratch/pb-pst/log.md`. This is model work; no person has reviewed it.

Marks: **VERIFIED** (compiled here, or read in a named file), **STANDARD** (published, exact reference),
**UNVERIFIED** (a number or wording given from memory; this host has no network).

## 1. Result

Of the review's four objections (strict leaf review, 2026-11-17), **three are cleared by Lean proofs with no new
hypothesis: V1, V2 and P2. P1 remains open.**

| objection | leaf | status | Lean (all VERIFIED: compiled, standard axioms) |
| --- | --- | --- | --- |
| V1: `tInvSet` inverts every `log [ε]`; nothing ties the ring to `B_max^+[1/t]` for one `t` | Berger (and Pan) | **cleared** | `BmaxOne.bmaxOf_eq : BmaxOf h = Bmax`, `bstOf_eq : BstOf h = Bst` for every generator `ε₀` of `ℤ_p(1)`; key step `logTeich_eq_mul`: `log [ε] = a · log [ε₀]`, `a ∈ ℤ_p` |
| V2: admissibility goes through the open `FontaineBstInvariants` | Berger | **cleared** | `BmaxOne.isAdmissible_of_T`: Fontaine's admissibility in its basis form (`B ⊗ V` has a `B`-basis of `H`-invariant vectors) implies the dimension form `dim_{B^H} D_B(V) = dim V` for every `G_{ℚ_p}`-stable `B ⊆ B_dR`; the restated leaf concludes the basis form, so no `B_st^{G_K} = K_0` is needed |
| P2: no `FiniteDimensional` lemma for `htSpaceE = (V ⊗ ℂ_p(w))^G` | Pan | **cleared** | `HTFinite.finiteDimensional_htSpaceE`, `HTFinite.htMultE_le` (`dim_E ≤ n`), from `axSenTate_proof` by Galois descent |
| P1: pst over Berger's `B_max`-based `B_st`, not matched with Fontaine's `B_cris`-based `B_st` | Pan | **open** | none; §5 states exactly what is missing |

**Restated leaves, with proofs of the old ones (drop-in):**

* `PanDict.BergerPrintedVT` (Berger 2002, Thm 0.7): for every generator `ε₀`, de Rham ⇒ for some finite `K`,
  `B_st ⊗_{ℚ_p} V` has a `B_st`-basis of `G_K`-invariant vectors, `B_st = B_max^+[1/t][log [p̃]]`, `t = log [ε₀]`.
  `bergerPrintedV_of_T : BergerPrintedVT → BergerPrintedV`.
* `PanDict.PanPrintedPt` (Pan 2022, Thm 1.0.4): `PanPrintedP` with pst over `B_max^+[1/t][log [p̃]]`.
  `panPrintedP_of_t : PanPrintedPt → PanPrintedP` (and the two are equivalent, by `localIsPstBOf_iff`).

**Ratings (§4).** `bergerPrintedVT`: **printed form** (LEAF, flagged unread). `panPrintedPt`: **consequence**
(GLUE) while P1 is open; P2 no longer counts against it. The fold spec `scratch/pb-pst/autofold.json` replaces
`bergerPrintedV` by `bergerPrintedVT`: **GLUE −1** against leaf-fold33b (the target was −2; Pan's row stays GLUE
because of P1). No new glue.

## 2. V1: one `t` (VERIFIED)

`IsGenEps ε₀ :⇔ ε₀^♯ = 1 ∧ ε₀^{(1)} ≠ 1`, i.e. `ε₀ = (1, ζ_p, ζ_{p²}, …)` with `ζ_p ≠ 1` a primitive `p`-th root
of unity (a generator of `ℤ_p(1) = T_p(μ)`); `exists_isGenEps` constructs one. `t = log [ε₀]` (`tOf`), and

```lean
def BmaxOf (h : IsGenEps p ε₀) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ {Ring.inverse (tOf p h)})
def BstOf (h : IsGenEps p ε₀) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ {Ring.inverse (tOf p h)} ∪ {toBdR p (logPTilde p)})
theorem bmaxOf_eq (h : IsGenEps p ε₀) : BmaxOf p h = Bmax p
theorem bstOf_eq (h : IsGenEps p ε₀) : BstOf p h = Bst p
```

The proof that every inverted `1/log [ε]` lies in `B_max^+[1/t]`:

1. **`A_max ⊆ B_dR^+` is `p`-adically separated** (`amax_sep`): if `x ∈ p^k A_max` for every `k`, then `x = 0`.
   Modulo `(ker θ)^m`, `p^m A_max` lands in the image of `A_inf` (`amax_mod`); so the image of `p^m x` is
   `[w_0] = [p^k w_k]` for all `k`, and `w_0 ∈ ⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf` (`mem_xi_pow_of_forall`,
   induction on `m`, using `A_inf/ξ = 𝓞_ℂ_p` `p`-adically separated and `p` regular modulo `ξ^m`, the latter
   bst-construct's `mem_xi_pow_of_p_pow_mul`). `p` is a unit modulo `(ker θ)^m`, and `B_dR^+` is the
   `ker θ`-adic completion.
2. **Tilt decomposition** (`log_decomp`): if `ε^{(k)} = (ε₀^{(k)})^b`, `b ≤ p^k`, then `ε ε₀^{p^k − b} = η^{p^k}`
   with `η^♯ = 1` (`η = φ^{−k}(ε ε₀^{p^k−b})`), so `log [ε] = b log [ε₀] + p^k (log [η] − log [ε₀])`, the bracket in
   `A_max` (bst-construct's `logTeich_mem_amax`; additivity `logPlus_add`).
3. The exponents `b_k` (`ε^{(k)} = ζ_{p^k}^{b_k}`, `ζ_{p^k} = ε₀^{(k)}` primitive by `orderOf_eq_prime_pow`) are
   compatible mod `p^k`; their limit `a ∈ ℤ_p` (`exists_padic_limit`) gives
   `log [ε] − a log [ε₀] ∈ p^k A_max` for all `k`, hence `= 0` by 1 (`logTeich_eq_mul`).
4. `a ≠ 0` since `log [ε] ≠ 0` (bst-construct's `logTeich_ne_zero`); so `1/log [ε] = a^{−1} · 1/t ∈ B_max^+[1/t]`
   (`tInv_mem`).

Consequences: `IsPstBOf h ρ ↔ IsPstB ρ` and `LocalIsPstBOf h n ρ ↔ LocalIsPstB n ρ` (`isPstBOf_iff`,
`localIsPstBOf_iff`), for every generator.

## 3. V2 and P2 (VERIFIED)

### 3.1 Fontaine's admissibility in its basis form

```lean
def IsAdmissibleT (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ (ι : Type) (b : Basis ι B (B ⊗[ℚ_[p]] (Fin n → E))),
    ∀ i, inclT p B (b i) ∈ PanBergerSplit.tensorInv p (PanBergerSplit.bdrLin p) H ρ
theorem isAdmissible_of_T [FiniteDimensional ℚ_[p] E] (B : Subalgebra ℚ_[p] (BdR p))
    (hB : ∀ σ : GQp p, ∀ x ∈ B, bdrAct p σ x ∈ B) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E)
    (h : IsAdmissibleT p B H ρ) : IsAdmissible p B H ρ
```

`IsAdmissibleT` is "`B ⊗_{ℚ_p} V ≅ B^d` as `B`-modules with semilinear `H`-action, `H` trivial on the standard
basis", which is Fontaine's definition of a `B`-admissible representation (Astérisque 223, Exp. III §1.4-1.5;
numbering UNVERIFIED). Proof of `isAdmissible_of_T`: `B ⊗ V → B_dR ⊗ V` is injective (`ℚ_p` a field,
`inclT_injective`); the coordinates of an invariant vector in an invariant basis are fixed by `H`
(`B` is `H`-stable), so the basis is a `B^H`-basis of `D_B(V)` and `dim_{B^H} D_B(V) = rk_B (B ⊗ V) = dim_{ℚ_p} V`.
This direction needs neither that `B^H` is a field nor its value.

The restated Berger leaf concludes the basis form (`IsPstT`), and `isPstBOf_of_T` gives the dimension form the
consumer uses (`B_st` is `G_{ℚ_p}`-stable: bst-construct's `bst_stable`). `FontaineBstInvariants` is no longer on
the route; it was never used by the consumer, but the dimension form needed it to be read as Berger's
`dim_{K_0} D_st = dim V`.

### 3.2 Hodge–Tate finiteness

```lean
theorem finiteDimensional_htSpaceE [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    FiniteDimensional E (PanDict.htSpaceE p ρ w)
theorem htMultE_le [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    PanDict.htMultE p ρ w ≤ n
```

`linearIndependent_of_invariant`: for an additive `σ`-semilinear action on a `ℂ_p`-module, `ℚ_p`-independent
invariant vectors are `ℂ_p`-independent (a nonzero relation of minimal support, normalized at one coefficient, is
fixed by every `σ`, so its coefficients lie in `ℂ_p^{G_{ℚ_p}} = ℚ_p`: `axSenTate_proof` at `K = ℚ_p`). Hence
`dim_{ℚ_p} (ℂ_p(w) ⊗ V)^G ≤ dim_{ℂ_p} (ℂ_p ⊗ V) = dim_{ℚ_p} V` (`finiteDimensional_htU`), and through pb-fix3's
`map_comm_htU` and the tower law, `htSpaceE` is finite-dimensional over `E` with `dim_E ≤ n`. So `htMultE` (a
`finrank`) is a genuine dimension, never a `0` standing for an infinite dimension.

## 4. Ratings

### 4.1 `bergerPrintedVT`: printed form (LEAF; flags unread)

Source: Berger, Invent. Math. 148 (2002), Théorème 0.7 (= Cor. 5.22 of the published version, author copy pp. 6
and 52; = arXiv:math/0102179v3 Thm 0.6 = Thm 5.19; locators.md row R11, read there).

* *Object*: one `p`-adic representation `V = E^n` of `G_{ℚ_p}`, continuous; the case `K = ℚ_p` of the theorem
  (as pb-fix3).
* *de Rham*: `dim_{ℚ_p} (B_dR ⊗ V)^{G_{ℚ_p}} = dim V` (`IsDeRhamU`), Fontaine's `dim_K D_dR(V) = dim V` at `K = ℚ_p`;
  `B_dR^{G_{ℚ_p}} = ℚ_p` is now a theorem of the tree (bdr-inv), so the `ℚ_p`-dimension is the `K`-dimension.
* *Potentially semistable*: `B_st`-admissible over some finite `K`, in Fontaine's basis form. Fontaine's
  Prop. (Exp. III §1.4, UNVERIFIED numbering) makes it equivalent to `dim_{K_0} D_st,K(V) = dim V` for the
  `(ℚ_p, G_K)`-regular ring `B_st`; the leaf asks for the basis form, which is the definition.
* *Rings*: `B_st = B_max[log [p̃]]`, `B_max = B_max^+[1/t]` for one `t = log [ε₀]` (V1 cleared), `B_max^+ = A_max[1/p]`,
  `A_max = {Σ a_n (ω/p)^n}` (bst-construct; any generator `ω` of `ker θ`, `amaxOf_eq_amax`).
* *Every generator `ε₀`*: the ring does not depend on it (`bstOf_eq`), so this is the statement for one `t`.

Flags carried (unread): Springer pagination; Berger §1.2's wording of `A_max`, `B_max` recalled (bst-construct);
Exp. III numbering of Fontaine's admissibility. **Not stronger than the print**: same hypotheses, and the
conclusion is Fontaine's definition of pst for the ring Berger writes.

### 4.2 `panPrintedPt`: consequence (GLUE), P1 open

Everything as pb-fix3's `PanPrintedP` (hypotheses and conclusion as printed, dictionaries proved), with the ring
written `B_max^+[1/t][log [p̃]]`. P2 is cleared (`finiteDimensional_htSpaceE`). P1 stands: Pan's "potentially
semistable" is Fontaine's, over Fontaine's `B_st = B_cris[log [p̃]]`; the leaf reads it over the `B_max`-based ring
(and in dimension form). The two agree by a published comparison (Colmez's `B_max` vs Fontaine's `B_cris`;
the standard statement is that `D_st` computed with either ring is the same; exact locator UNVERIFIED), which is
not in the tree. I do not fold this leaf: it changes no count.

## 5. What remains (P1)

To clear P1 the tree needs, for `V = E^n`:

```
LocalIsPstB p n ρ → LocalIsPstU p n ρ          -- B_max-based ⇒ Fontaine's B_cris[X]-based (PanBerger.lean:176)
```

or Pan's leaf restated over Fontaine's ring with a published comparison. Missing in Lean: (i) `A_cris → B_dR^+`
(PanBerger's `A_cris` is an abstract `p`-adic completion; mapping it into `B_dR^+` needs `A_inf/ξ^m`
`p`-adically complete, and its image lies in `A_max` for `p ≥ 3`), (ii) Frobenius on `A_max`, `A_cris`, `log [p̃]`,
(iii) `φ(B_max^+) ⊆ B_cris^+ ⊆ B_max^+` and the resulting equality of the `D_st`'s, (iv) for the dimension
normalization of `LocalIsPstU`, `B_cris[X]^{G_K} = K_0` (or a basis form of `LocalIsPstU`). None is attempted
here.

## 6. Deliverables and checks (VERIFIED)

* `ZInQKernel/Contrib/OneProof/PanBergerPst.lean` (46 KB, no `sorry`), generated by
  `python3 scratch/pb-pst/mkcontrib.py` from `scratch/pb-pst/BmaxOne.lean` and `scratch/pb-pst/HTFinite.lean` (each
  compiles alone with `lake env lean`). `lake build +ZInQKernel.Contrib.OneProof.PanBergerPst
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds (16074 jobs; `scratch/pb-pst/build4.txt`).
* `python3 scripts/one_proof/sandbox/scan_contrib.py 4dfb7e583 HEAD`: `PanBergerPst.lean: 0 likely hit(s), 0
  possible hit(s)`.
* **Axioms** (`scratch/pb-pst/Axioms.lean` → `axioms-output.txt`): 15 declarations (the three old-from-new
  theorems, `amax_sep`, `logTeich_eq_mul`, `bmaxOf_eq`, `bstOf_eq`, `exists_isGenEps`, `isAdmissible_of_T`,
  `isPstBOf_of_T`, `localIsPstBOf_iff`, `finiteDimensional_htSpaceE`, `htMultE_le`,
  `linearIndependent_of_invariant`, `bergerPrintedVt_of_T`), all `[propext, Classical.choice, Quot.sound]`.
* **`#discharges`** (`scratch/pb-pst/Discharges.lean` → `discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves42.bergerPrintedV] by HDec.PkgI4.PanDict.bergerPrintedV_of_T
    still assumes: [HDec.PkgI4.PanDict.BergerPrintedVT]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves42.bergerPrintedV] by HDec.PkgI4.PanDict.bergerPrintedV_of_t
    still assumes: [HDec.PkgI4.PanDict.BergerPrintedVt]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves42.panPrintedP] by HDec.PkgI4.PanDict.panPrintedP_of_t
    still assumes: [HDec.PkgI4.PanDict.PanPrintedPt]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 39 open hypotheses, 13438 theorems checked, 28 discharge one
  ```
* **Autofold** (`scratch/pb-pst/autofold.json`): field `bergerPrintedV`, proof
  `_root_.HDec.PkgI4.PanDict.bergerPrintedV_of_T {n}.bergerPrintedVT`, leaf `bergerPrintedVT`, kind `published`,
  flag `unread: …` (the flags of §4.1).
  * Dry run (`autofold-dryrun.txt`): `strict count: 12/22 on 34 -> 13/21 on 34; strictest 11/23 -> 12/22`
    (GLUE −1 in both columns).
  * Its output with the first line stripped (`FoldDryRun.lean.txt`) compiles against the built tree;
    `HDec.HSyn.sixContactMin_of_open61` depends on `[propext, Classical.choice, Quot.sound]`
    (`folddryrun-output.txt`).
  * Not in the spec: `panPrintedP → panPrintedPt` (`panPrintedP_of_t`), a drop-in that changes no count (P1).
* **Locator rows** (locators.md belongs to other tasks; proposed): R11 → `bergerPrintedVT` (pb-pst;
  predicates `BstOf`, `IsAdmissibleT`, `IsPstT` in `PanBergerPst.lean`); R12 unchanged (`panPrintedP`).
* **Reproduce** from the repository root:
  ```
  python3 scratch/pb-pst/mkcontrib.py
  lake build +ZInQKernel.Contrib.OneProof.PanBergerPst +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  lake env lean scratch/pb-pst/Axioms.lean
  lake env lean scratch/pb-pst/Discharges.lean
  python3 scripts/one_proof/autofold.py scratch/pb-pst/autofold.json --dry-run
  ```

## 7. Lean pitfalls met (for the next task)

* On `B ⊗_{ℚ_p} V` and on the submodule `dB` (bst-construct's `D_B(V)`), `Fintype.linearIndependent_iff` and
  `Finset.sum_sub_distrib` rewrites time out or fail (instance paths through `Submodule.addCommMonoid`). What
  worked: `Basis.repr_sum_self` for coefficient comparison, `LinearIndependent.restrict_scalars` and
  `LinearIndependent.of_comp (dB …).subtype` for independence, and `Submodule.map_span` for spanning.
* Mathlib's `BDeRhamPlus` is a `def` (`deriving CommRing`) over `AdicCompletion`; `rw` with
  `AdicCompletion.evalₐ` on `B_dR^+`-terms fails (motive not type-correct). Wrapping it as a ring hom on
  `BDeRhamPlus` (`evB`) fixes it.
* `HDec.PkgI4.cpAct` (LPrefix copy) and `ZInQ.Contrib.G9.PkgI4.cpAct` are definitionally equal (`rfl`), so
  `axSenTate_proof` applies to pb-fix2's `htLin` directly.

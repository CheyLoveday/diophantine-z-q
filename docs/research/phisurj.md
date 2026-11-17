# phisurj: `mumfordPhiSurjectiveAC` removed by rerouting its readers (−1, no new leaf); the statement itself stays unproved

Task phisurj. Base wip/leaf-fold33b 0e3c31258 (`git merge origin/main`: already up to date). Field
`mumfordPhiSurjectiveAC : PicDict.MumfordPhiSurjectiveAC` of `HDec.HSyn.OpenAddedLeaves20` (`TailZ47.lean:29`;
statement `ZInQKernel/Contrib/OneProof/PicDictionary.lean:1564`, Mumford §8 Thm 1 over `k = k̄`).

## 1. Result

**The field is removed from the open hypotheses with no new leaf, by rerouting its readers; the Prop
`MumfordPhiSurjectiveAC` is not proved.**

* All three readers of the field (`TailZ45.lean:123`, `TailZ46.lean:104`, `HomFreeFiniteAlgClosedReroute.lean:2082`;
  VERIFIED by grep) use it only through `PicFix.phiAmpleIsogeny_of_printed l.mumfordKLFiniteSectionAC
  l.mumfordPhiSurjectiveAC : T09Pic.PhiAmpleIsogeny`.
* `T09Pic.PhiAmpleIsogeny` (`λ_L : A → Pic⁰` finite and surjective, every field, every ample `L`) is now a theorem
  from two statements that are already open, and from nothing else:

  ```lean
  theorem PhiSurj.phiAmpleIsogeny_of_weil (h4 : T09Pic.WeilPairingMumford)
      (hT : AvSplit.MumfordTorsionAlgClosed) : T09Pic.PhiAmpleIsogeny
  ```

  `weilPairingMumford` is a field of the same bundle `OpenAddedLeaves20`; `mumfordTorsionAlgClosed` is a field of
  the textbook bundle `OpenTextbookLeaves15` (and is proved outright on origin/proof/picard-fibres-20261116,
  `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, not merged here). Only the **right-kernel half
  of perfectness** of `weilPairingMumford` is used (§3).
* The hand fold `scratch/phisurj/FoldTailZ49.lean` (after leaf-fold33's reroute pattern, `TailZ48`) defines
  `OpenAddedLeaves21` (= `OpenAddedLeaves20` without the field) and
  `sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves21)`,
  and `scratch/phisurj/FrozenTargetDryRun.lean` proves `ZInQ.FrozenTarget` from Main's hypotheses with
  `OpenAddedLeaves21` in place of `OpenAddedLeaves20`. Both compile with `[propext, Classical.choice, Quot.sound]`.

Count: one LEAF/LEAF row (`mumfordPhiSurjectiveAC`, printed Mumford §8 Thm 1, `docs/one-proof/kinds.tsv:31`)
leaves; no row enters. On this base H goes from `13/20 on 33` to `12/20 on 32` (strict and strictest; computed
from kinds.tsv, not an autofold run, since autofold cannot express a reroute).

Why not prove the Prop itself: §2.

## 2. What `MumfordPhiSurjectiveAC` says, and the part that is out of reach

`MumfordPhiSurjectiveAC`: over `k = k̄`, for `c₀` ample and `c` **translation-invariant** (`AC.IsTI`: `t_x^*c = c`
for every `x ∈ X(k)`), `c = t_x^*c₀ ⊗ c₀⁻¹` for some `x`. Mumford's `Pic⁰` here is the group of translation-invariant
classes, not the identity component `B` of the Picard scheme. So the Prop is the conjunction of

* **(a)** every translation-invariant class is a `k`-point of `B` (the converse of pic-dict's proved
  `picZeroPtsTranslInv_of_leaves`), and
* **(b)** `λ_L : A → B` is onto (the surjective half of `PhiAmpleIsogeny`).

(b) is proved here (§3). (a) is not, and it is exactly what is missing (VERIFIED, compiled, in the same file):

```lean
def PhiSurj.TIClassesInPicZeroAC : Prop :=   -- over k = k̄: every IsTI class c is kClass rep c = y ≫ j, y : X(k) → B
theorem PhiSurj.mumfordPhiSurjectiveAC_of_ti (ha : TIClassesInPicZeroAC) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h4 : WeilPairingMumford) (hT : AvSplit.MumfordTorsionAlgClosed) : MumfordPhiSurjectiveAC
theorem PhiSurj.tiClassesInPicZeroAC_of_phiSurjective (h8 : MumfordPhiSurjectiveAC) : TIClassesInPicZeroAC
```

(the first lifts `y` along the surjective `λ` to a `k`-point `x`, `exists_lift_kpt`, and compares classes with
Kleiman 9.2.5 at `Spec k̄`, `kClass_injective`, as pic-dict's L5; the second uses the proved
`exists_isAmple_of_isAlgClosed`). (a) itself: it says that the Néron–Severi class of a translation-invariant bundle is
zero (translation-invariant means `φ_c = 0`), i.e. `NS(A) → Hom(A, Â)` is injective. The published proofs go through
Mumford's proof of §8 Thm 1 (vanishing of `H^*(A, M)` for nontrivial `M ∈ Pic⁰` and the Künneth/Leray
comparison of the two projections of `m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*(L ⊗ M)⁻¹`), or through Weil's theory of algebraic
equivalence (Lang, *Abelian varieties*, Ch. IV); none of it is in the tree (STANDARD; locators UNVERIFIED).
Families built from translates of a translation-invariant `c` are constant, so the tree's family arguments
(Kleiman 9.2.5, rigidity) cannot move `c` into `B`. No consumer needs (a): all three readers only need
`PhiAmpleIsogeny`. So the field is rerouted rather than filled, as homfree-noemb did for `homFreeFiniteAlgClosed`.

## 3. The proof of `PhiAmpleIsogeny` without cohomology

Everything here is VERIFIED (compiled; `#print axioms PhiSurj.phiAmpleIsogeny_of_weil` standard).
File: `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyWeil.lean` (namespace `PhiSurj`; imports
`Contrib.OneProof.MumfordKLFinite`, `Contrib.AbVarBC.Mul`, `Contrib.AbVarBC.Dim`; no `sorry`, no build-time code;
`lake build ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyWeil`: "Build completed successfully (12814 jobs)").

Notation: `A` over a field `K`, `rep` a representation of `Pic_{A/K}`, `(B, j)` with `IsPicZero rep B j`, `L`
ample, `λ : A → B` with `λ ≫ j = φ_L`.

1. **Finite.** phi-ample's `PhiAmple.finite_ker_pts` (`K(L)` finite) and pic-dict's `finiteOfFiniteKerPts`.
2. **`dim B ≤ dim A`** (`dim_le_of_weil`). Take a prime `ℓ ∈ {2, 3}` invertible in `K`.
   * `exists_torsAddEquiv`: for every abelian variety `X` over any field, `X[ℓ] ≃+ (ℤ/ℓ)^{2 dim X}` on
     `K̄`-points: `AvSplit.MumfordTorsionAlgClosed` at `X_K̄` (as a `PkgI2` group object), transported along
     pic-dict's `pts : X(K̄) ≃* X_K̄(K̄)` and `Spec K̄ ≅ 𝟙_`, with `dim X_K̄ = dim X`
     (`ZInQ.Contrib.AbVarBC.dim_baseChange_scheme`).
   * `card_le_of_perfect`: if `X[ℓ] ≅ (ℤ/ℓ)^m` and `e : X[ℓ] × Y[ℓ] → μ_ℓ` has trivial right kernel, then
     `y ↦ (e(bᵢ, y))ᵢ` (on a basis `bᵢ`) is injective, so `#Y[ℓ] ≤ #μ_ℓ^m ≤ ℓ^m`.
   * With the pairing of `weilPairingMumford` (`IsPerfect`, second conjunct only):
     `ℓ^{2 dim B} = #B[ℓ] ≤ ℓ^{2 dim A}`.
3. **Onto** (`surjective_of_dim_le`, general schemes): a locally quasi-finite closed `f : X → Y`, `Y` irreducible,
   `dim X = a < ∞`, `dim Y ≤ a`, is surjective. Otherwise `Z ↦ f(Z)` is strictly monotone on irreducible closed
   subsets (generic points: a strict specialization stays strict under a locally quasi-finite map, the tree's
   `ne_of_specializes_of_lqf`, and two points specializing to each other are equal), and every `f(Z)` lies in the
   proper closed subset `f(X)`, so `WithTop (IrreducibleCloseds X) → IrreducibleCloseds Y` is strictly monotone
   and `a + 1 ≤ dim Y` (Mathlib `Order.krullDim_le_of_strictMono`, `Order.krullDim_WithTop`).
   `λ` is finite (so locally quasi-finite) and proper, `B` is irreducible, and `dim A`, `dim B` are natural numbers
   (`PkgI3.AbVar.dim_finite`).

The theorem of the square, the seesaw, the Weil pairing's left kernel and cohomology are not used.

## 4. On the use of `weilPairingMumford`

* Only the right-kernel clause is read: `∀ y ∈ B[ℓ], (∀ x ∈ A[ℓ], e(x, y) = 0) → y = 0`, at one prime `ℓ`. This
  is the half of Mumford §20's nondegeneracy that is proved by descent along `ℓ_A` (an `A[ℓ]`-invariant
  trivialization of `ℓ_A^*M` descends to `M`); it does not use `dim Pic⁰ = g`. So no content is moved into
  `weilPairingMumford` that its printed statement does not carry on its own.
* Lean-level cycle: weil-proof's reduction `WeilProof.Theta.weilPairingMumford_final` (wip/weil-proof, not on this
  base) takes `T09Pic.PhiAmpleIsogeny` and `MumfordPhiSurjectiveAC` as inputs. After this reroute that reduction
  cannot be folded as it stands (it would need the leaf back). The routes are alternatives: weil-proof's fold was
  GLUE-neutral and kept `mumfordPhiSurjectiveAC` as a leaf; this one removes it.

## 5. Fold

Alternative, not recommended: fill the field from (a) (`scratch/phisurj/autofold-ti.json`, leaf
`tiClassesInPicZeroAC`, flagged pending reading). `#discharges` matches it (`DISCHARGES
[OpenAddedLeaves20.mumfordPhiSurjectiveAC] by PhiSurj.mumfordPhiSurjectiveAC_of_ti still assumes:
[PhiSurj.TIClassesInPicZeroAC, T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, T09Pic.WeilPairingMumford,
AvSplit.MumfordTorsionAlgClosed]`), and the dry run gives `13/20 on 33 -> 12/21 on 33` (refused: GLUE rises).
Rating of (a): printed form **no, pending reading** — Mumford's `Pic⁰` is by definition the translation-invariant
classes; that these are the points of the identity component of the fppf Picard scheme is §8 Thm 1 with §13 and
Kleiman §9.5, not one print. It is a consequence of the replaced leaf (`tiClassesInPicZeroAC_of_phiSurjective`),
never stronger.

Recommended:

* **Not autofoldable**: autofold fills a field with a proof of the field's type, and `MumfordPhiSurjectiveAC` is
  not proved. `scratch/phisurj/autofold.json` records this (empty `discharges`, with the reroute described).
* **Hand fold** (`scratch/phisurj/FoldTailZ49.lean`, compiles against the built `TailZ48` in 34 s): new module
  importing `TailZ48` and the contribution; `OpenAddedLeaves21`; `openAddedLeaves18_of_OpenAddedLeaves21`
  (`phiAmpleIsogeny := PhiSurj.phiAmpleIsogeny_of_weil n.weilPairingMumford t.mumfordTorsionAlgClosed`, the
  other fields as in `TailZ45:119`); `openTextbookLeaves13HF_of_open15_21` (as
  `openTextbookLeaves13_of_OpenTextbookLeaves14_hf`, poincare from the same term); `sixContactMin_of_open42`
  through `sixContactMin_of_open37_hf`. Main's `frozenTarget` then takes `l : OpenAddedLeaves21` and calls
  `sixContactMin_of_open42 r t l` (`scratch/phisurj/FrozenTargetDryRun.lean`). kinds.tsv/claims.tsv: drop the
  `mumfordPhiSurjectiveAC` rows; no rows added.
* `#discharges` (`scratch/phisurj/discharges.txt`): `43 open hypotheses, 8612 theorems checked, 49 discharge one`.
  The reroute theorem `phiAmpleIsogeny_of_weil` has no line (expected: it proves the readers' `PhiAmpleIsogeny`,
  which is no longer an open hypothesis type); the only `PhiSurj` line is the (a)-alternative above.
* Axioms of every main theorem, of `sixContactMin_of_open42` and of `frozenTarget_phisurj`: standard
  (`scratch/phisurj/axioms.txt`).

## 6. New leaves and their rating

None (recommended reroute). The alternative of §5 would add (a) `tiClassesInPicZeroAC`, rated printed form: no,
pending reading (reason in §5).

## 6b. By-products (not on the fold's route)

`ZInQKernel/Contrib/OneProof/MumfordSquareMulN.lean` (imports the contribution; `lake build` ok; axioms standard,
`scratch/phisurj/axioms-byproducts.txt`) proves two of pic-dict's Mumford displays from L1 and L2 alone:

```lean
theorem PhiSurj.mumfordSquareAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) : PicDict.MumfordSquareAC
theorem PhiSurj.mumfordMulNPicZeroAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) :
    PicDict.MumfordMulNPicZeroAC
```

* Theorem of the square (Mumford §6 Cor. 4): `φ_c = λ_c ≫ j` with `λ_c` a homomorphism
  (`T09Pic.exists_hom_comp_eq_phiL`, for every class `c`), so `φ_c(x + y) = φ_c(x) φ_c(y)` on `k`-points, read off
  in `Pic` through `kClass` (injective by Kleiman 9.2.5 at `Spec k̄`, multiplicative by the vendored
  `homEquiv_symm_toPicardFunctor_mul`).
* `n^*c = cⁿ` for translation-invariant `c` (Mumford §8 (iv)): `λ_c` vanishes on `k`-points (`φ_c(x) = 1`), so
  `λ_c = 0` (`hom_ext_kpt`, from the tree's `AVGlue.hom_ext_of_points` since `k ≅ k̄`); then `Λ(c)` is classified by
  the constant map and is normalized along `0`, so `Λ(c) = 1` (`Θ_inj`, as phi-ample's step 3), i.e.
  `m^*c = p₁^*c ⊗ p₂^*c`; induct on `n`.

These were two of the four Mumford displays that weil-proof's reduction of `weilPairingMumford` still assumed
(`MumfordSquareAC`, `MumfordMulNPicZeroAC`, `MumfordPhiSurjectiveAC`, `MumfordWeilNondegAC`). They do not change any
count on this base (`weilPairingMumford` is a single field).

## 7. Files

* `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyWeil.lean` (the contribution).
* `ZInQKernel/Contrib/OneProof/MumfordSquareMulN.lean` (by-products, §6b).
* `scratch/phisurj/`: `DimSurj.lean`, `PhiSurj.lean`, `TIReduction.lean`, `SquareAC.lean`, `MulNAC.lean`
  (development copies), `AxiomsByproducts.lean`, `axioms-byproducts.txt`,
  `PhiAmpleIsogenyWeil.lean.txt` (copy of the contribution), `FoldTailZ49.lean`, `FrozenTargetDryRun.lean`,
  `Discharges.lean`, `discharges.txt`, `Axioms.lean`, `axioms.txt`, `autofold.json`, `autofold-ti.json`,
  `autofold-ti-dryrun.txt`, `log.md`.

## 8. What remains

* (a) `TIClassesInPicZeroAC`: not needed by the proof (rerouted), but it is what separates `PhiAmpleIsogeny` from the
  printed Mumford §8 Thm 1. No cohomology-free route found (§2).
* The right-kernel clause of `weilPairingMumford` could itself be proved by fpqc descent along `ℓ_A` (the vendored
  `bijective_toDescentData_map_of_mem_fpqcTopology` / `nonempty_iso_of_toDescentData_iso` give the descent step;
  `ℓ_A^*M ≅ M^ℓ = 𝒪` for translation-invariant `M` of order `ℓ` is now `mumfordMulNPicZeroAC_of_open` (§6b); missing:
  the decomposition of `A ×_{ℓ,A,ℓ} A` along the étale
  `A[ℓ]`, and the bridge from pic-dict's `formula` to the pseudofunctor's `mapComp'`). Not attempted here; it would
  make the reroute independent of `weilPairingMumford`.
* `mumfordTorsionAlgClosed` disappears as a textbook field once origin/proof/picard-fibres-20261116 lands.

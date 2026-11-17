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

Count: one LEAF row (`mumfordPhiSurjectiveAC`, printed Mumford §8 Thm 1) leaves; no row enters. 33 → 32 hypotheses
of H on this base.

Why not prove the Prop itself: §2.

## 2. What `MumfordPhiSurjectiveAC` says, and the part that is out of reach

`MumfordPhiSurjectiveAC`: over `k = k̄`, for `c₀` ample and `c` **translation-invariant** (`AC.IsTI`: `t_x^*c = c`
for every `x ∈ X(k)`), `c = t_x^*c₀ ⊗ c₀⁻¹` for some `x`. Mumford's `Pic⁰` here is the group of translation-invariant
classes, not the identity component `B` of the Picard scheme. So the Prop is the conjunction of

* **(a)** every translation-invariant class is a `k`-point of `B` (the converse of pic-dict's proved
  `picZeroPtsTranslInv_of_leaves`), and
* **(b)** `λ_L : A → B` is onto (the surjective half of `PhiAmpleIsogeny`).

(b) is proved here (§3). (a) is not: it says that the Néron–Severi class of a translation-invariant bundle is
zero, i.e. `NS(A) → Hom(A, Â)` is injective on the classes with `φ_c = 0`. Every argument I know goes through
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
* `#discharges` (`scratch/phisurj/discharges.txt`): `43 open hypotheses, 8602 theorems checked, 48 discharge one`,
  no line for `PhiSurj.*` — expected, since the theorem proves the readers' `PhiAmpleIsogeny`, which is no longer an
  open hypothesis type.

## 6. New leaves and their rating

None.

## 7. Files

* `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyWeil.lean` (the contribution).
* `scratch/phisurj/`: `DimSurj.lean`, `PhiSurj.lean` (development copies), `FoldTailZ49.lean`,
  `FrozenTargetDryRun.lean`, `Discharges.lean`, `discharges.txt`, `autofold.json`, `log.md`.

# conrad-b3 results log

## Step 1. Consumers of TateTwistInvariantsInertia (VERIFIED, grep over the worktree and origin/wip/ht-merge, origin/main)
- ZInQKernel/: C8LocAlg.lean L90 (def), L98 `locAlgExponentEqWeight_of_tateInertia`; C8CFT.lean L506 `c8TwistFinite_of_leaves` (hypothesis hTT, used L515 only through L98);
  C8Poincare.lean L35 (field of `C8Inputs`), L43 (`g12DetPZ_of_inputs`); C8Printed.lean L28 (field of `C8Leaves`), L33, L41, L47.
- No other Lean consumer in the worktree. origin/main: none (C8 files not on main). origin/wip/ht-merge: the same five C8 files plus
  scratch copies (scratch/c8-conrad2, scratch/ht-abvar/HTDryRun.lean reads `C8Inputs`/`C8Leaves`).
- Tau Ceti Artin map normalization (VERIFIED, read): `isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer` (Local/Unramified.lean L465): uniformizer -> arithmetic Frobenius;
  `localCyclotomicCharacter_artinMap_padic` (ExplicitCyclotomicSymbol/ArtinMap.lean L295): chi_cyc(Art u) = u^-1 for u in Z_p^x. Same normalization as Conrad p. 32 ("arithmetic normalization", page read 11-17 forwarded in the task).

## Step 2. Leaf ConradPropB3Qp and the merged leaf ConradAppB (new file ZInQKernel/Contrib/OneProof/C8ConradB.lean)
- `IsLocallyAlgebraicConrad p ψ n`: ∃ k, ∀ u ≡ 1 mod p^k, ∀ Artin lift σ of u, ψ σ = u^(-n) (Conrad p. 33, L = Q_p).
- `conradHTMult p ρ w := finrank Q_p (htSpace p ρ w)` (Conrad convention; chi_cyc has weight +1: H_w(Q_p(1)) ≠ 0 iff w = 1).
- `ConradPropB3Qp`: ψ : G_Qp → E^x continuous, IsLocallyAlgebraicConrad p ψ n → conradHTMult p (charRep ψ) n = [E:Q_p].
- `ConradAppB := ConradAppBQp ∧ ConradPropB3Qp`.
- definitional steps: `isLocallyAlgebraic_iff_conrad` (n ↔ -n, simp neg_neg); `htMult_eq_conradHTMult_neg` (rfl).
- `locAlgExponentEqWeight_of_conradPropB3 : ConradPropB3Qp → LocAlgExponentEqWeight`; `c8TwistFinite_of_conradB`.
- PR #86 (branch proof/poincare-complement-native-20261117 = 8050603bc, read with git show): FinalUnconditional.lean L24
  `theorem poincareComplement_proof : ZInQ.Contrib.AVB1.PoincareComplement := poincareComplement_of_square L6.NativeTheoremOfTheSquare_proof.{0}`;
  AVB1/Poincare.lean identical to HEAD (git diff empty). VERIFIED by reading; not merged, not compiled.

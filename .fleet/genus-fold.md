# genus-fold (fleet summary)

**Result (VERIFIED: compiled, axioms standard).** `genusX1Field` is gone from the single proof. Its only use was
`t34`, consumed twice in TailD's `glueOutputs_of_leaves3`, and both uses now take genus-route's theorem
`dim J₁(N) ≤ N²`, which has no hypothesis. `frozenTarget` now has **58 bundle fields: 44 LEAF, 14 GLUE** in the
strict count (was 59: 44 / 15). Removed hypothesis: textbook `genusX1Field` (GLUE (comp)). Added: none.
PruneScan finds 0 unused fields.

**What compiles.**
- New modules (each < 150 KB), all built through TailD's import:
  - `ZInQKernel/OneProof/Genus/DimJac.lean`, `GenusBound.lean`, `LocalDer.lean`: genus-route's `Closed.lean`
    split, kernel imports only. Namespaces were renamed to `GenusFold.*` to avoid a clash with TailZ10's root copy
    of dimjac-glue.
  - `Genus/Bridge.lean`: `HDec.HSyn.t34Le`, `dim_J1_le_of5`, `G0Split.javanpeykarJ1_of_le`.
- Edited existing modules:
  - `H/TailD.lean`: one import and two proof terms.
  - Prune deletions in `LPrefix`, `TailA`, `E`, `I`, `K`, `N`, `O`, `X`, `Z4`, `Z9`, `Z11`: 9 fields, their
    assignments, and 6 dead readers.
- `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.

**Hash comparison** (`scratch/genus-fold/cmp_hashes_out.txt`, `changed_constants.md`):
- 19 removed: the 9 fields, the dead readers and their auxiliaries, and one realized equation lemma that is still
  present.
- 333 new, all in Genus/*.
- 174 changed: bundle auxiliaries, conversions, TailD's theorem, and **2 + 80 theorems in TailE–TailZ2 whose type
  or proof term changed with no source change**. The cause is the new import: Mathlib instances such as
  `CommSemiring.toHopfAlgebra` now arrive with the Jacobian library, and instance search uses them for Prop-valued
  instances.
- For the 2 type changes, the base types were rebuilt in a base tree and are kernel-checked `rfl`-equal to the new
  ones (`diag/DefEqCheck.lean`).
- The owner's allowed-change list does not cover this group, so the owner should accept it explicitly.

**What remains.**
- The unused inner fields `OpenTextbookLeaves{6..9}.dimJacobianEqGenus` (not in the prune set; filled by
  dimjac-glue's theorem).
- `x0Transitive`'s T40 use (outside this task).
- A base tree (`git archive e38375b3` with a reflink copy of `.lake/build`) is left in a directory outside the
  worktree, since `rm -rf` is not allowed.

Report: docs/research/genus-fold.md. Log: scratch/genus-fold/log.md.

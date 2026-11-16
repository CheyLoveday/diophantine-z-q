# homfree-proof results log

Base: origin/main 0caafe66. Field: `homFreeFiniteAlgClosed : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed`
(ZInQKernel/Contrib/AVB1/AlgClosed.lean:38), bundle OpenTextbookLeaves12 (TailZ42.lean). VERIFIED (read).

## Statement (verbatim, VERIFIED read)
∀ (k : Type) [Field k] [IsAlgClosed k] (A B : PkgI3.AbVar k),
  Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧ (finrank : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
  ∀ ℓ [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Injective (tateHomZl ℓ A B)

## Setup
- .lake/build and lean/.lake/build copied (reflink) from ~/dzq-wt/nos-proof (same HEAD 0caafe66).

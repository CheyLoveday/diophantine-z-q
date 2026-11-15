import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator

/-!
# Positive annihilators of finite commutative group schemes

Wrapper around the attributed finite-Hopf source port from
openai/math@4eaee87548250b2682affda7d05d947c05554bae.
See LICENSE and NOTICE.md in this contribution directory.

The group scheme and every test object are actual Mathlib objects in `Over (Spec K)`.
No reducedness, characteristic, flatness, quotient, or supplied-annihilator premise is added.
This is source-only: target-pin elaboration and axiom inspection have not been run.
-/

namespace ZInQ.Contrib.MilneQuasiInverse

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

/-- Some positive integer annihilates all scheme-valued points of a finite commutative
 group scheme over an arbitrary field, including infinitesimal test schemes. -/
theorem finiteGroup_exists_annihilator (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X] [IsFinite G.X.hom] :
    ∃ n : ℕ, 0 < n ∧
      ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X), x ^ n = 1 := by
  exact _root_.MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupAnnihilator.Construction.finiteGroup_exists_annihilator K G

end ZInQ.Contrib.MilneQuasiInverse

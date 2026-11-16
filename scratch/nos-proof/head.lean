import ZInQKernel.Contrib.OneProof.UnipotentForward
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# nos-proof: `r7a` (Néron–Ogg–Shafarevich, Serre–Tate 1968 Thm 1) with the direction (a) ⇒ (b) proved

The chain's field `r7a : PkgI2.NeronOggShafarevich.{0}` (`ZInQKernel/HDecomp/Objects.lean`) states
(a) ⟺ (b) and (a) ⟺ (c) of Serre–Tate's Theorem 1 over `K̄ = AlgebraicClosure K`. This file proves

* (a) ⇒ (b) (`inertiaTrivialOn_of_goodReduction`): good reduction makes inertia act trivially on
  `A(K̄)[m]` for every `m ≥ 1` invertible in `O`. Proof: reduction `A(K̄)[m] → 𝒜(κ(w))[m]` is bijective
  (the proved row `PkgI2.ReductionTorsionBijective`, `AvSplit.T4.reductionTorsionBijective_of_mulEtale` with
  fork PR #19's `mulEtaleAbelianScheme_proof`); an inertia element `σ` maps the lift `x̃ : Spec w → 𝒜` of `x`
  to the lift `Spec(σ|_w) ≫ x̃` of `σ x`, whose reduction is that of `x` because `σ` acts trivially on `κ(w)`;
  injectivity of reduction gives `σ x = x`.
* (b) ⇒ (c): infinitely many `m ≥ 1` are invertible in the local ring `O` (`m = k·p + 1` with `p` the
  residue characteristic, or every `m` in residue characteristic `0`).
* (c) ⇒ (a) from the new leaf `NOSConverseSep` (Serre–Tate Thm 1, (c) ⇒ (a), over a separable closure, as
  printed), via `K^s = separableClosure K K̄`: inertia of `w ∩ K^s` extends to inertia of `w`
  (dict-galois's `isInertia_extend`, copied) and `A(K^s) ↪ A(K̄)` is Galois-equivariant.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsAbelianScheme IsInertia HasGoodReduction InertiaTrivialOn torsion galAct
  galHom Pts toW IsReductionOf)
open scoped Pointwise

namespace NOSProof


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

/-! ## 1. (a) ⇒ (b): good reduction makes inertia trivial on prime-to-`p` torsion -/

section Forward

variable {K : Type} [Field K]

/-- The restriction `σ|_w : w → w` of an element of the decomposition group of `w`. -/
def resW (w : ValuationSubring (AlgebraicClosure K)) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hd : σ ∈ w.decompositionSubgroup K) : w →+* w :=
  MulSemiringAction.toRingHom (w.decompositionSubgroup K) w ⟨σ, hd⟩

theorem resW_coe (w : ValuationSubring (AlgebraicClosure K))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K) (a : w) :
    ((resW w σ hd a : w) : AlgebraicClosure K) = σ a := rfl

/-- `σ|_w` fixes the image of `O`. -/
theorem resW_comp_toW (O : ValuationSubring K) (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K) :
    (resW w σ hd).comp (toW O w hw) = toW O w hw := by
  ext a
  change σ (algebraMap K (AlgebraicClosure K) (a : K)) = algebraMap K (AlgebraicClosure K) (a : K)
  exact σ.commutes _

/-- An inertia element acts trivially on `κ(w)`: `residue ∘ σ|_w = residue`. -/
theorem residue_comp_resW (w : ValuationSubring (AlgebraicClosure K))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hd : σ ∈ w.decompositionSubgroup K)
    (hi : (⟨σ, hd⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) :
    (IsLocalRing.residue w).comp (resW w σ hd) = IsLocalRing.residue w := by
  ext a
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w a)
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a = IsLocalRing.residue w a at h1
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  exact h1

/-- **(a) ⇒ (b) of Serre–Tate's Theorem 1 (proved).** If `A` has good reduction at `O`, every element of
the inertia group of `w` fixes `A(K̄)[m]` for every `m ≥ 1` invertible in `O`. -/
theorem inertiaTrivialOn_of_goodReduction (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)) (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit (m : O)) : InertiaTrivialOn A w m := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hA
  have hR := AvSplit.T4.reductionTorsionBijective_of_mulEtale
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof K O w hw A 𝒜 e m hm hmO
  intro σ hσ x hx
  obtain ⟨y, ⟨hy, x', hx1, hx2⟩, -⟩ := hR.1 x hx
  obtain ⟨hd, hi⟩ := hσ
  let s := resW w σ hd
  have hs1 : (CommRingCat.ofHom (toW O w hw) ≫ CommRingCat.ofHom s) =
      CommRingCat.ofHom (toW O w hw) := by
    rw [← CommRingCat.ofHom_comp, resW_comp_toW]
  have hs2 : (CommRingCat.ofHom s ≫ CommRingCat.ofHom (IsLocalRing.residue w)) =
      CommRingCat.ofHom (IsLocalRing.residue w) := by
    rw [← CommRingCat.ofHom_comp, residue_comp_resW w σ hd hi]
  let x'' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X :=
    Over.homMk (Spec.map (CommRingCat.ofHom s) ≫ x'.left) (by
      have hx'w := Over.w x'
      simp only [Over.mk_hom] at hx'w ⊢
      rw [Category.assoc, hx'w, ← Spec.map_comp, hs1])
  have hσx : galAct A σ x ∈ torsion A (AlgebraicClosure K) m := by
    show galAct A σ x ^ m = 1
    rw [← PkgI2.galAct_pow]
    have hx' : x ^ m = 1 := hx
    rw [hx']
    exact PkgI2.galAct_one _ _
  have hred : IsReductionOf 𝒜 e w hw (galAct A σ x) y := by
    refine ⟨x'', ?_, ?_⟩
    · have h1 : (galAct A σ x ≫ (e.inv.hom.hom : A.X ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
            (x ≫ (e.inv.hom.hom : A.X ⟶
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left := by
        simp only [galAct, galHom, Category.assoc, Over.comp_left]
        rfl
      rw [h1]
      refine (Category.assoc _ _ _).trans ((congrArg (fun t =>
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ t) hx1).trans ?_)
      show Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
          Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ Spec.map (CommRingCat.ofHom s) ≫ x'.left
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
    · show y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫
          Spec.map (CommRingCat.ofHom s) ≫ x'.left
      rw [hx2, ← Category.assoc, ← Spec.map_comp, hs2]
  obtain ⟨x0, -, huniq⟩ := hR.2 y hy
  exact (huniq _ ⟨hσx, hred⟩).trans (huniq _ ⟨hx, ⟨x', hx1, hx2⟩⟩).symm

end Forward

end NOSProof

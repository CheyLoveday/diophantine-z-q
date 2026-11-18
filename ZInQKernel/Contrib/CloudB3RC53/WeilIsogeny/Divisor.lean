import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Commute
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum

/-!
# The pullback of the Weil divisor along a separable isogeny

Let `φ : W₁ → W₂` be a separable isogeny over a separably closed field and `K = ker φ`. The divisor
`[n]^* (φ T) − [n]^* (O)` of the Weil pairing on `W₂` pulls back along `φ` to

    φ^* ([n]^* (φ T) − [n]^* (O)) = [n]^* (∑_{R ∈ K} ((T + R) − (R)))     (`pb_weilPairingDivisor`),

using `φ^* [n]^* = [n]^* φ^*` (`comp_mulByInt` and the transitivity of pullbacks), the fibres
`φ^* (φ T) = ∑_{R ∈ K} (T + R)` and `φ^* (O) = ∑_{R ∈ K} (R)` (`divisorPullback_ofPoint`).

`pb ψ` is `ψ.divisorPullback` with the algebra structure given by `ψ` itself, which keeps the
several algebra structures between the same function fields apart.

Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny AlgebraicGeometry

namespace ZInQ.Contrib.CloudB3RC53.WeilIsogeny

variable {F : Type*} [Field F]

/-- The divisor pullback along `ψ`, for the algebra structure given by `ψ`. -/
def pb {A B : WeierstrassCurve.Affine F} (ψ : Isogeny A B) :
    Divisor F B.FunctionField →+ Divisor F A.FunctionField :=
  @Isogeny.divisorPullback F _ A B ψ ψ.fieldPullback.toRingHom.toAlgebra (fun _ => rfl)

theorem pb_comp {A B C : WeierstrassCurve.Affine F} (φ : Isogeny A B) (ψ : Isogeny B C)
    (D : Divisor F C.FunctionField) : pb (ψ.comp φ) D = pb φ (pb ψ D) :=
  (@Isogeny.divisorPullback_comp F _ A B φ φ.fieldPullback.toRingHom.toAlgebra (fun _ => rfl) C ψ
    ψ.fieldPullback.toRingHom.toAlgebra (ψ.comp φ).fieldPullback.toRingHom.toAlgebra
    (fun _ => rfl) (fun _ => rfl) D).symm

variable [DecidableEq F] [IsSepClosed F]

/-- **The pullback of the Weil divisor along a separable isogeny.** PROVED. -/
theorem pb_weilPairingDivisor {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] {n : ℤ}
    (h₁ : psiFunctionField W₁.toAffine n ≠ 0) (h₂ : psiFunctionField W₂.toAffine n ≠ 0)
    (T : W₁.toAffine.Point) :
    pb φ (weilPairingDivisor W₂ h₂ ((Hom.ofIsogeny φ).pointMap T)) =
      pb (mulByIntIsogeny W₁.toAffine h₁)
        (∑ R ∈ (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) 0).toFinset,
          (WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 -
            WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace R).1)) := by
  classical
  have := W₂.toAffine.isIntegrallyClosed_coordinateRing
  have hadd : ∀ Q R : W₁.toAffine.Point, (Hom.ofIsogeny φ).pointMap (Q + R) =
      (Hom.ofIsogeny φ).pointMap Q + (Hom.ofIsogeny φ).pointMap R := by
    intro Q R
    rw [Hom.pointMap_ofIsogeny_eq_toPointHom, Hom.pointMap_ofIsogeny_eq_toPointHom,
      Hom.pointMap_ofIsogeny_eq_toPointHom, map_add]
  have hpb : ∀ D, pb φ (pb (mulByIntIsogeny W₂.toAffine h₂) D) =
      pb (mulByIntIsogeny W₁.toAffine h₁) (pb φ D) := by
    intro D
    rw [← pb_comp, ← pb_comp, comp_mulByInt φ h₁ h₂]
  have hW : ∀ Q : W₂.toAffine.Point, weilPairingDivisor W₂ h₂ Q =
      pb (mulByIntIsogeny W₂.toAffine h₂)
        (WeilDivisor.ofPoint (W₂.toAffine.pointEquivDegreeOnePlace Q).1) -
      pb (mulByIntIsogeny W₂.toAffine h₂)
        (WeilDivisor.ofPoint (W₂.toAffine.pointEquivDegreeOnePlace 0).1) := by
    intro Q
    rw [weilPairingDivisor_def, ← coe_pointEquivDegreeOnePlace_zero]
    rfl
  set K := (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero φ) 0).toFinset
  have hfib0 : pb φ (WeilDivisor.ofPoint (W₂.toAffine.pointEquivDegreeOnePlace 0).1) =
      ∑ R ∈ K, WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace R).1 :=
    divisorPullback_ofPoint φ 0
  have hfibT : pb φ (WeilDivisor.ofPoint (W₂.toAffine.pointEquivDegreeOnePlace
      ((Hom.ofIsogeny φ).pointMap T)).1) =
      ∑ R ∈ K, WeilDivisor.ofPoint (W₁.toAffine.pointEquivDegreeOnePlace (T + R)).1 := by
    refine (divisorPullback_ofPoint φ _).trans ?_
    refine Finset.sum_bij' (fun R _ => R - T) (fun R _ => T + R) ?_ ?_ ?_ ?_ ?_
    · intro R hR
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, K] at hR ⊢
      have := hadd (R - T) T
      rw [sub_add_cancel, hR] at this
      exact (add_eq_right.mp this.symm)
    · intro R hR
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, K] at hR ⊢
      rw [hadd, hR, add_zero]
    · intro R _; abel
    · intro R _; abel
    · intro R _; congr 3; abel
  rw [hW, map_sub, hpb, hpb, hfibT, hfib0, ← map_sub, Finset.sum_sub_distrib]

end ZInQ.Contrib.CloudB3RC53.WeilIsogeny

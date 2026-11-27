import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceAdelic
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.MatrixFrames
import ZInQKernel.Contrib.OneProof.RC.Adelic.Stage

/-! Use one rational frame at the reference and assemble its completed
chain coordinates in the detector's fixed class model. Tex 8462–8468. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {A : PkgI3.AbVar k}

set_option maxHeartbeats 500000 in
/-- Frame the actual reference in the pinned algebra. The remaining split
test is the local order profile calculated in the geometric Tate frames. -/
theorem detector_referenceCoordinates (q : ℕ) [Fact q.Prime] [Fact (q % 4 = 3)]
    (N : ℕ) (hN : 0 < N) (hcop : N.Coprime q) (hqN : IsUnit (N : ℤ_[q]))
    (S : Order (-1) (-(q : ℚ))) (j : A.End ≃+* S.ring)
    (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
    (C : Subgroup (A.Pt k)) (hC : ∀ x ∈ C, x ^ N = 1)
    (hSplit : ∀ p : Prime, p.val ≠ q →
      ∃ f : Bp p.val (-1) (-(q : ℚ)) ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val],
        f '' ((levelOrderOfEndOrder S j C N hN.ne' hC).completion p.val : Set _) =
          standardLevel p.val (N.factorization p.val)) :
    ∃ z : Adelic.FiniteUnits (levelOrder q Fact.out N hN),
      ReferenceOrderCoordinates (levelOrder q Fact.out N hN)
        (levelOrderOfEndOrder S j C N hN.ne' hC) z := by
  apply exists_referenceCoordinates
  intro p
  by_cases hp : p.val = q
  · have ep : p = (⟨q, Fact.out⟩ : Prime) := Subtype.ext hp
    subst p
    have hqnd := (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mp hcop.symm
    have hRq : (levelOrder q Fact.out N hN).completion q =
        DivisionJoin.completedOrder q (Fact.out : q % 4 = 3) :=
      levelOrder_completion_away q Fact.out N hN (⟨q, Fact.out⟩ : Prime) hqnd
    refine ⟨1, fun x => ?_⟩
    have hx := congrArg (fun T : Subalgebra ℤ_[q] (Bp q (-1) (-(q : ℚ))) => x ∈ T)
      (hRq.trans (reference_levelCompletion_eq q S j hmax C N hN.ne' hC hqN).symm)
    simpa only [inv_one, Units.val_one, one_mul, mul_one] using Iff.of_eq hx
  · have he := (algebraicGeometry q Fact.out N hN hcop).eichler
    obtain ⟨f, hf⟩ := he.split_profile p.val hp
    obtain ⟨g, hg⟩ := hSplit p hp
    exact splitReference_conjugate p _ f g hf hg

end ZInQ.Manuscript.RC.HCMV21

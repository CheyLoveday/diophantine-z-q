import ZInQKernel.Contrib.OneProof.RC.Gz34Instance.Curve
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageData

/-! Read the filter for tex 2404–2410 and 2460–2462 from the existing
stage support. The interface translation is on-the-spot (c). -/

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

/-- The existing stage support supplies the filter inputs: use the unit tests on
the intrinsic support, and the prime exclusions on the full support. -/
theorem filterInputs_of_stageSupport {ℓ : ℕ} {W : WData ℓ} (hℓ : 0 < ℓ) (hS : StageSupport W)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    SupportSpec W ∧ PreparedSpec W ∧ W.hstar.natAbs.primeFactors ⊆ W.S ∧
      (∀ h, W.prepared h → ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p h) := by
  refine ⟨⟨hS.support_prime, hS.support_base (by simp [S0]), hS.support_base (by simp [S0]), ?_⟩,
    hS.preparedSpec, hS.support_hstar, ?_⟩
  · intro p hp hd
    exact hS.support_base (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Nat.mem_primeFactors.mpr ⟨hp, hd, hℓ.ne'⟩)))
  · obtain ⟨Sunit, _, hbase, _, _, heq⟩ := hS.prepared_eq
    intro h hh p hp hpd
    rw [heq] at hh
    have hu := hh.1.2.2 p (hbase (hlevel0 p hp hpd))
    exact squareAt_of_padic hp hu.1 hu.2

#print axioms filterInputs_of_stageSupport

end ZInQ.Manuscript.RC.Gz34Instance

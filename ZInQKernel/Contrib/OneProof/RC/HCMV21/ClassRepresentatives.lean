import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors BigOperators

/-- Every ideal class has a nonzero integral representative coprime to the modulus
formed by the excluded primes (and hence to each excluded prime). -/
theorem exists_integral_class_prime_to {K : Type*} [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    ∃ a : (Ideal (𝓞 K))⁰, IsCoprime (a : Ideal (𝓞 K)) m ∧ ClassGroup.mk0 a = c := by
  let M : Modulus K := ⟨m, hm, ∅⟩
  obtain ⟨b, hb⟩ := rayClassToClassGroup_surjective M c
  obtain ⟨A, rfl⟩ := idealClass_surjective M b
  obtain ⟨ha, hcop⟩ := Modulus.isCoprimeTo_iff_sup_eq_top.mp
    (Modulus.mem_integralIdealsPrimeTo.mp A.2)
  let a : (Ideal (𝓞 K))⁰ := ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩
  refine ⟨a, Ideal.isCoprime_iff_sup_eq.mpr hcop, ?_⟩
  rw [← hb, idealClass_apply, rayClassToClassGroup_rayClassMk, ← ClassGroup.mk_mk0 K a]
  congr 1

/-- In particular one may avoid any specified finite set of nonzero prime ideals. -/
theorem exists_integral_class_avoiding {K : Type*} [Field K] [NumberField K]
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ p ∈ S, p ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    ∃ a : (Ideal (𝓞 K))⁰, (∀ p ∈ S, IsCoprime (a : Ideal (𝓞 K)) p) ∧
      ClassGroup.mk0 a = c := by
  classical
  let m := ∏ p ∈ S, p
  have hm : m ≠ ⊥ :=
    Finset.prod_induction id (· ≠ ⊥)
      (fun _ _ ha hb hm => (Ideal.mul_eq_bot.mp hm).elim ha hb)
      (by simp [Ideal.one_eq_top]) hS
  obtain ⟨a, ha, hc⟩ := exists_integral_class_prime_to m hm c
  refine ⟨a, fun p hp => ?_, hc⟩
  have hmp : m ≤ p := Ideal.prod_le_inf.trans (Finset.inf_le hp)
  exact Ideal.isCoprime_iff_sup_eq.mpr <| top_unique <|
    (Ideal.isCoprime_iff_sup_eq.mp ha).ge.trans (sup_le_sup_left hmp _)

end ZInQ.Manuscript.RC.HCMV21

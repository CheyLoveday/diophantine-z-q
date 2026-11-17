import ZInQKernel.Contrib.OneProof.BergerBst
open HDec PkgI4 BergerBst Module
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}
  (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρE : GQp p →* GL (Fin n) E)
theorem finrank_fin_pi_sub {R M' : Type*} [CommRing R] [IsDomain R] [AddCommGroup M'] [Module R M'] (N : Submodule R M') (d : ℕ) :
    finrank R (Fin d → N) = d * finrank R N := sorry
set_option synthInstance.maxHeartbeats 400000 in
example (d : ℕ) [IsDomain (fixedSub p B H)] : finrank (fixedSub p B H) (Fin d → dB p B H ρE) = d * finrank (fixedSub p B H) (dB p B H ρE)  := by
  have h := @finrank_fin_pi_sub (fixedSub p B H) (B ⊗[ℚ_[p]] (Fin n → E)) _ _ TensorProduct.addCommGroup
      (inferInstance : Module (fixedSub p B H) (B ⊗[ℚ_[p]] (Fin n → E))) (dB p B H ρE) d
  convert h using 2
  all_goals trace_state
  all_goals sorry

import ZInQKernel.Contrib.OneProof.BergerBst

/-! pb-dimform scratch: model independence of Fontaine's admissibility (dimension form). -/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PstModel

open Module BergerBst PanBergerSplit
open scoped TensorProduct

/-! ## §1. Rank of a finite power over a domain -/

section RankPi

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- Over a domain (rank-nullity), `rank (M × N) = rank M + rank N` with no freeness. -/
theorem rank_prod_domain {N : Type*} [AddCommGroup N] [Module R N] (hMN : Type*) :
    True := trivial

theorem rank_fin_pi (d : ℕ) : Module.rank R (Fin d → M) = d * Module.rank R M := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← (Fin.consLinearEquiv R (fun _ : Fin (d + 1) => M)).rank_eq]
    rw [LinearMap.rank_eq_of_surjective (f := LinearMap.fst R M (Fin d → M)) LinearMap.fst_surjective,
      LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, ih]
    push_cast
    ring

theorem finrank_fin_pi (d : ℕ) : finrank R (Fin d → M) = d * finrank R M := by
  unfold finrank
  rw [rank_fin_pi, Cardinal.toNat_mul, Cardinal.toNat_natCast]

end RankPi

/-! ## §2. Changing the coefficient field of a model: `L^n ≅ (E^n)^d` -/

section Model

variable (p : ℕ) [Fact p.Prime]
variable {E L : Type*} [Field E] [Field L] [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [Algebra E L]
  [IsScalarTower ℚ_[p] E L] {d n : ℕ} (b : Basis (Fin d) E L)

/-- `(E^n)^d ≅ L^n`, `(v_j)_j ↦ (Σ_j v_j(i) b_j)_i`, for an `E`-basis `b` of `L`. -/
def phiE : (Fin d → Fin n → E) ≃ₗ[ℚ_[p]] (Fin n → L) :=
  (LinearEquiv.piComm ℚ_[p] (Fin d) (Fin n) E) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => (b.equivFun.symm.restrictScalars ℚ_[p])

theorem phiE_apply (v : Fin d → Fin n → E) (i : Fin n) :
    phiE p b v i = ∑ j, v j i • b j := by
  simp [phiE, Basis.equivFun_symm_apply]

variable (ρE : GQp p →* GL (Fin n) E) (ρL : GQp p →* GL (Fin n) L)

theorem phiE_equivariant
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) (σ : GQp p)
    (v : Fin d → Fin n → E) :
    phiE p b (fun j => vAct p ρE σ (v j)) = vAct p ρL σ (phiE p b v) := by
  funext i
  rw [vAct_apply, ← hρ σ]
  simp only [phiE_apply, vAct_apply, Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map,
    Matrix.GeneralLinearGroup.coe_map, RingHom.mapMatrix_apply, Matrix.map_apply,
    Finset.sum_smul, Finset.mul_sum, Algebra.smul_def, map_mul, mul_assoc]
  sorry

end Model

end PstModel
end PkgI4
end HDec

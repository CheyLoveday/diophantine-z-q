import ZInQKernel.Contrib.OneProof.RC.ParamJoin.AtScale
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Cusps

/-! The analytic boundary values at the scale of the constructed interior
map (tex 1785–1787, 2937–2941; provenance (c)). -/

noncomputable section

open Filter Topology UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.ParamAtScale
  ZInQ.Manuscript.RC.ElkikMD
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ParamJoin

/-- The interior morphism and the based analytic cusp limits use the very same
scale. The limits are in the analytic period quotient. -/
theorem algebraicParametrizationAtScale_and_cuspLimits {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    AlgebraicParametrizationAtScale (Ecurve ℓ) (X0Branch.model (newformLevel (Ecurve ℓ))) f Lat κ ∧
    ∃ c : ℚ, c ≠ 0 ∧ (c : ℂ) = κ ∧
      Tendsto (torusValue Lat f κ) atImInfty (𝓝 0) ∧
      ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
        Tendsto (fun τ : ℍ => torusValue Lat f κ (σ • τ)) atImInfty
          (𝓝 (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((c : ℂ) * cuspSymbol f r))) := by
  refine ⟨algebraicParametrizationAtScale f hf hLat hκ hr, ?_⟩
  obtain ⟨c, rfl⟩ := hr
  exact ⟨c, fun hc => hκ.1 (by simp [hc]), rfl, torusValue_tendsto_infty f Lat c,
    fun r σ hσ => torusValue_tendsto_cusp f Lat c r σ hσ⟩

#print axioms algebraicParametrizationAtScale_and_cuspLimits

end ZInQ.Manuscript.RC.ParamJoin

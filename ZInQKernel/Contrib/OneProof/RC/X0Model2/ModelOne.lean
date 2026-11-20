import ZInQKernel.Contrib.OneProof.RC.X0Model2.JOrbit
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam
import ZInQKernel.Contrib.OneProof.RC.X0Model2.Projection
import ZInQKernel.Contrib.OneProof.RC.X0Model2.SectionExpansion
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Prints

/-! The model at level one (tex 1781–1788, 2836–2844 and 2915–2919;
on the spot, provenance (c)). -/

noncomputable section

open AlgebraicGeometry ModularCurve
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.X0Model2

/-- Either lift of a point on the normalized curve has a parameter in the
same orbit for the full modular group. -/
theorem sl_orbit_of_complexPoint_eq (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    (h : X0Model.complexPoint N τ = X0Model.complexPoint N σ) :
    ∃ γ : SL(2, ℤ), γ • τ = σ :=
  (analyticJ_eq_iff τ σ).mp (analyticJ_eq_of_complexPoint_eq N τ σ h)

/-- At level one the full modular group is already the level subgroup. -/
theorem complexPoint_one_eq_iff (τ σ : UpperHalfPlane) :
    X0Model.complexPoint 1 τ = X0Model.complexPoint 1 σ ↔
      ∃ γ ∈ CongruenceSubgroup.Gamma0 1, γ • τ = σ := by
  refine ⟨fun h => ?_, complexPoint_eq_of_gamma0_orbit 1 τ σ⟩
  obtain ⟨γ, hγ⟩ := sl_orbit_of_complexPoint_eq 1 τ σ h
  exact ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _), hγ⟩

/-- The prescribed rational model, analytic chart, and section expansion at level one. -/
def modelOne : PreparedParam.X0Model 1 where
  X := X0Model.curve 1
  overQ := X0Model.overQ 1
  integral := X0Model.integral 1
  proper := X0Model.proper 1
  smooth := X0Model.smooth 1
  functionField := X0Model.functionField 1
  complexPoint τ := ⟨X0Model.complexPoint 1 τ, X0Model.complexPoint_overQ 1 τ⟩
  complexPoint_eq_iff τ σ := by
    erw [Subtype.mk_eq_mk]
    exact complexPoint_one_eq_iff τ σ
  sectionExpansion U _ r := sectionExpansion 1 U r


end ZInQ.Manuscript.RC.X0Model2

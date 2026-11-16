import ZInQKernel.Contrib.OneProof.ThetaDirect.Nodes

/-! # theta-direct (helper): the two relations among Igusa's theta expressions on the QM curve

From the LEAF `IgusaThetaExpressions` (Igusa) only, with the kernel's proved valence formula, elliptic-order
divisibility and generation of `Γ*`, and the algebraic theta ratios at the nodes `√2 + i` and `τ₂₄`:

* (R1) there is an algebraic `c₁` with `ψ₆(Ω(z))·Σθ⁸(Ω(z)) = c₁·∏θ²(Ω(z))` for all `z ∈ ℍ`
  (weight 20 for `Γ*`, one node `τ₂₄`);
* (R2) there are algebraic `c₂`, `c₃` with `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` along `Ω(z)` (weight 40, nodes
  `√2 + i`, `τ₂₄`).

(Lin–Yang's Example 29 would give `c₁ = −4/3⁵`, `c₂ = 1/(2¹⁸3⁶)`, `c₃ = ` an explicit rational; only algebraicity is
proved and used here.) -/

set_option linter.all false

noncomputable section

namespace HDec.ThetaDirect

open Complex
open HDec.LeafQCheck.HM.QMSplit (Auto)
open HDec.HSyn.G0Split.FibreQM.PeriodMap (G8 U omegaSiegel_proof)
open HDec.HSyn.G0Split.FibreQM.PeriodGlue (M4 M6 M4_symp M6_symp zz_ne)
open HDec.HSyn.G0Split.ThetaPt.LinYangPrinted (siegelEis siegelEis_modular spAct_mem IgusaThetaExpressions
  igusaChi12E thetaConst_omega_analyticAt)
open HDec.HSyn.G0Split.ThetaPt.ThetaGlue (psi4Th psi6Th chi10Th chi12Th psi4T psi6T chi10T chi12T psi6Th_eq
  chi12Th_eq)

local notation "𝔸" => algebraicClosure ℚ ℂ

/-- `G20 = ∏θ²∘Ω/((z−3)(z+1))¹⁰` (the kernel's). -/
abbrev G20 : ℂ → ℂ := HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20

/-! ## Modularity of `ψ₆` and `χ₁₂` (theta expressions) from the LEAF -/

theorem psi6Th_modular (hI : IgusaThetaExpressions) {M : GapTheta.Mat4}
    (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) :
    psi6Th (PkgI1.spAct M Ω) = PkgI1.spFactor M Ω ^ 6 * psi6Th Ω := by
  rw [← (hI _ (spAct_mem hM hΩ)).2.1, ← (hI _ hΩ).2.1]
  exact siegelEis_modular hM hΩ ⟨3, rfl⟩

theorem chi12Th_modular (hI : IgusaThetaExpressions) {M : GapTheta.Mat4}
    (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ PkgI1.SiegelH2) :
    chi12Th (PkgI1.spAct M Ω) = PkgI1.spFactor M Ω ^ 12 * chi12Th Ω := by
  rw [← (hI _ (spAct_mem hM hΩ)).2.2.2, ← (hI _ hΩ).2.2.2]
  unfold igusaChi12E
  rw [siegelEis_modular hM hΩ (k := 4) ⟨2, rfl⟩, siegelEis_modular hM hΩ (k := 6) ⟨3, rfl⟩,
    siegelEis_modular hM hΩ (k := 12) ⟨6, rfl⟩]
  ring

/-! ## The four automorphic forms for `Γ*` -/

theorem auto6 (hI : IgusaThetaExpressions) : Auto 6 (GS 6 psi6Th) :=
  autoGS ⟨3, rfl⟩ (fun z hz => psi6Th_modular hI M4_symp (omegaSiegel_proof z hz))
    (fun z hz => psi6Th_modular hI M6_symp (omegaSiegel_proof z hz))

theorem auto12 (hI : IgusaThetaExpressions) : Auto 12 (GS 12 chi12Th) :=
  autoGS ⟨6, rfl⟩ (fun z hz => chi12Th_modular hI M4_symp (omegaSiegel_proof z hz))
    (fun z hz => chi12Th_modular hI M6_symp (omegaSiegel_proof z hz))

theorem auto8' : Auto 4 G8 := HDec.LeafQCheck.HM.QMSplit.auto8 GapTheta.thetaModularity_proof

theorem auto20' : Auto 10 G20 := HDec.LeafQCheck.HM.QMSplit.auto20 GapTheta.thetaModularity_proof

theorem analytic_GS {w : ℕ} {S : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hS : ∀ z ∈ U, AnalyticAt ℂ (fun z => S (PkgI1.Omega z)) z) : AnalyticOnNhd ℂ (GS w S) U := fun z hz =>
  (hS z hz).div (by fun_prop) (pow_ne_zero _ (zz_ne hz))

theorem analytic_psi6 : AnalyticOnNhd ℂ (GS 6 psi6Th) U := by
  refine analytic_GS fun z hz => ?_
  have h := fun m => thetaConst_omega_analyticAt hz m
  unfold psi6Th
  fun_prop

theorem analytic_chi12 : AnalyticOnNhd ℂ (GS 12 chi12Th) U := by
  refine analytic_GS fun z hz => ?_
  have h := fun m => thetaConst_omega_analyticAt hz m
  unfold chi12Th
  fun_prop

theorem analytic_G8 : AnalyticOnNhd ℂ G8 U := fun z hz => HDec.LeafQCheck.HM.G8_analytic hz
theorem analytic_G20 : AnalyticOnNhd ℂ G20 U := fun z hz => HDec.LeafQCheck.HM.G20_analytic hz

end HDec.ThetaDirect

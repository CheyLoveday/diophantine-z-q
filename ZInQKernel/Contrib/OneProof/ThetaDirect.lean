import ZInQKernel.Contrib.OneProof.ThetaDirect.Relations

/-! # theta-direct: `ThetaRatiosAtQM` (the use of `thetaRatiosAlgebraic`) from Igusa's theta expressions alone

Task theta-direct (docs/research/theta-direct.md). The added composite field `thetaRatiosAlgebraic`
(`G0Split.ThetaPt.ThetaRatiosAlgebraic`, GLUE) has one reader, TailK's `gluePieces_of_open4`, which needs only
theta-split's use form `ThetaRatiosAtQM` (theta-fold, wip/theta-fold 8e3dbdea; its verbatim copy is in
`ThetaDirect/UseForm.lean`). This file proves

* `thetaRatiosAtQM_of_igusa : IgusaThetaExpressions → ThetaRatiosAtQM`,
* `thetaPointOfFibre_of_igusa : FibreQMPeriod → IgusaThetaExpressions → ThetaPointOfFibre`

with the single hypothesis the LEAF `IgusaThetaExpressions` (Igusa 1964/1967: on `𝔥₂` the Siegel Eisenstein
series `ψ₄`, `ψ₆` and Igusa's `χ₁₀`, `χ₁₂` equal their theta expressions; theta-fold's statement, verbatim in
`ThetaDirect/Printed.lean`). No Lin–Yang input, no `QMHauptmodul`, no new leaf. Everything else is the kernel's
proved theorems: the valence formula for `Γ*` (`valenceFormulaCocompactEq_proof`, `shimizuCovolumeO1_proof`),
`ellipticOrderDvd_proof`, `ellipticOrderLe6_proof`, `gammaStarGen_proof`, gt-theta's `thetaModularity_proof`,
cm24-value's theta constants at `Ω₂₄`, period-glue's factorization at `Ω₀`, theta-glue's duplication formula and
igusa-alg's Kronecker-checked identities `IgusaAlg 3..9`.

Proof. (R1) `ψ₆Σθ⁸ = c₁∏θ²` and (R2) `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` hold along `Ω(z)` with algebraic
`c_i` (`ThetaDirect/Relations.lean`: dimension counts by the valence formula, constants read off at the CM points
`√2 + i` and `τ₂₄`, where the theta ratios are algebraic, `ThetaDirect/Nodes.lean`). Where
`j_θ(Ω(τ)) = q ∈ ℚ ∖ 0`, write `Σθ⁸ = ρ²`, `∏θ² = ρ⁵ξ` (`ξ² = q/3779136`); then
`ψ₄, ψ₆, χ₁₀, χ₁₂ = ρ²·¼, ρ³·c₁ξ, ρ⁵·(−ξ/2¹⁴), ρ⁶(c₂ + c₃ξ²)`, so by weighted homogeneity
`e_k(θ⁸)/(Σθ⁸)^k = P_k(¼, c₁ξ, −ξ/2¹⁴, c₂ + c₃ξ²)` is algebraic (`IgusaAlg k`, `3 ≤ k ≤ 9`; `k = 2` is the global
`Σθ¹⁶ = (Σθ⁸)²/4`), and the `θ_m⁸/Σθ⁸` are roots of a monic polynomial with algebraic coefficients. -/

set_option linter.all false

noncomputable section

namespace HDec.ThetaDirect

open Complex Polynomial
open HDec.HSyn.G0Split.ThetaPt.LinYangPrinted (IgusaThetaExpressions)
open HDec.HSyn.G0Split.ThetaPt.ThetaGlue (psi4Th psi6Th chi10Th chi12Th psi4T psi6T chi10T chi12T psi6Th_eq
  chi12Th_eq igusaP)
open HDec.HSyn.G0Split.ThetaPt.ThetaSplit (ThetaRatiosAtQM thetaEight card_thetaEight esymm_one esymm_ten
  two_esymm_two zero_mem_evenChars isOddChar_of_not_even thetaPointOfFibre_of_qm_atQM)

local notation "𝔸" => algebraicClosure ℚ ℂ

/-- `alg_mem` with a family of memberships `h : ∀ m, f m ∈ 𝔸`. -/
macro "alg_mem_with " h:term : tactic => `(tactic| repeat (first
  | assumption
  | with_reducible exact $h _
  | with_reducible exact one_mem _
  | with_reducible exact zero_mem _
  | with_reducible exact ofNat_mem' _
  | with_reducible exact ratCast_mem' _
  | with_reducible apply div_mem
  | with_reducible apply inv_mem
  | with_reducible apply add_mem
  | with_reducible apply sub_mem
  | with_reducible apply mul_mem
  | with_reducible apply pow_mem
  | with_reducible apply neg_mem))

/-! ## Node values -/

theorem psi6T_smul (c : ℂ) (s : PkgI1.Char2 → ℂ) : psi6T (fun m => c * s m) = c ^ 6 * psi6T s := by
  simp only [psi6T]; ring

theorem chi12T_smul (c : ℂ) (s : PkgI1.Char2 → ℂ) : chi12T (fun m => c * s m) = c ^ 12 * chi12T s := by
  simp only [chi12T]; ring

/-- At a node, `Σθ⁸`, `∏θ²`, `ψ₆`, `χ₁₂` are algebraic multiples of `t⁸, t²⁰, t¹², t²⁴` for one `t ≠ 0`. -/
theorem node_vals {Ω : Matrix (Fin 2) (Fin 2) ℂ} (h : NodeAlg Ω) :
    ∃ t : ℂ, t ≠ 0 ∧ ∃ s8 p20 p6 p12 : ℂ, s8 ∈ 𝔸 ∧ p20 ∈ 𝔸 ∧ p6 ∈ 𝔸 ∧ p12 ∈ 𝔸 ∧
      PkgI1.thetaSum8 Ω = t ^ 8 * s8 ∧ PkgI1.thetaProd2 Ω = t ^ 20 * p20 ∧
      psi6Th Ω = t ^ 12 * p6 ∧ chi12Th Ω = t ^ 24 * p12 := by
  obtain ⟨m0, h0, hr⟩ := h
  set t := PkgI1.thetaConst m0 Ω
  have hθ : ∀ m, PkgI1.thetaConst m Ω = t * (PkgI1.thetaConst m Ω / t) := fun m => by field_simp
  have hsq : (fun m => PkgI1.thetaConst m Ω ^ 2) = fun m => t ^ 2 * (PkgI1.thetaConst m Ω / t) ^ 2 := by
    funext m; conv_lhs => rw [hθ m]
    ring
  refine ⟨t, h0, ∑ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / t) ^ 8,
    ∏ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / t) ^ 2,
    psi6T (fun m => (PkgI1.thetaConst m Ω / t) ^ 2), chi12T (fun m => (PkgI1.thetaConst m Ω / t) ^ 2),
    sum_mem fun m _ => pow_mem (hr m) 8, prod_mem fun m _ => pow_mem (hr m) 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [psi6T]; alg_mem_with hr
  · simp only [chi12T]; alg_mem_with hr
  · rw [PkgI1.thetaSum8, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [hθ m]
    ring
  · rw [PkgI1.thetaProd2, show t ^ 20 = ∏ _m ∈ PkgI1.evenChars, t ^ 2 by
      rw [Finset.prod_const, PkgI1.card_evenChars, ← pow_mul], ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    conv_lhs => rw [hθ m]
    ring
  · rw [psi6Th_eq, hsq, psi6T_smul, ← pow_mul]
  · rw [chi12Th_eq, hsq, chi12T_smul, ← pow_mul]

theorem c1_mem : c1 ∈ 𝔸 := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ :=
    node_vals nodeAlg_om24
  have hP : p20 ≠ 0 := by
    intro h0; apply prod2_tau24; rw [tau24_omega, e20, h0, mul_zero]
  have hZ := Zf24_ne
  have e : c1 = p6 * s8 / p20 := by
    unfold c1 GS
    rw [G8_eq', G20_eq', tau24_omega, e8, e20, e6]
    generalize ((tau24 : ℂ) - 3) * ((tau24 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; alg_mem

theorem c2_mem : c2 ∈ 𝔸 := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ := node_vals nodeAlg_cm4
  have hS : s8 ≠ 0 := by
    intro h0; apply sum8_tau4; rw [tau4_omega, e8, h0, mul_zero]
  have hZ := Zf4_ne
  have e : c2 = p12 / s8 ^ 3 := by
    unfold c2 GS
    rw [G8_eq', tau4_omega, e8, e12]
    generalize ((tau4 : ℂ) - 3) * ((tau4 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; alg_mem

theorem c3_mem : c3 ∈ 𝔸 := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ :=
    node_vals nodeAlg_om24
  have hP : p20 ≠ 0 := by
    intro h0; apply prod2_tau24; rw [tau24_omega, e20, h0, mul_zero]
  have hZ := Zf24_ne
  have h2 := c2_mem
  have e : c3 = (s8 ^ 2 * p12 - c2 * s8 ^ 5) / p20 ^ 2 := by
    rw [c3]
    unfold GS
    rw [G8_eq', G20_eq', tau24_omega, e8, e20, e12]
    generalize ((tau24 : ℂ) - 3) * ((tau24 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; alg_mem

end HDec.ThetaDirect

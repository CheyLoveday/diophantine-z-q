import ZInQKernel.Contrib.OneProof.C8CFT

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace HDec.G0Galois.C8Conrad

namespace TwistHT

open _root_.PkgI4 (GaloisRep GaloisChar)

/-! ## §1. The global part: `tr r = ψ · tr ρ_g` and `det r = ψ² · det ρ_g` on `G_ℚ` -/

/-- `2 det M = (tr M)² − tr(M²)` for `2 × 2` matrices. -/
theorem two_mul_det_fin_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    2 * M.det = M.trace ^ 2 - (M * M).trace := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem continuous_trace_mat {ℓ : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ 2) :
    Continuous fun σ => (ρ.mat σ).trace := by
  have h : Continuous fun σ => (ρ.toHom σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) :=
    Units.continuous_val.comp ρ.continuous_toHom
  exact h.matrix_trace

theorem continuous_char {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) :
    Continuous fun σ => ((ψ.toHom σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) :=
  Units.continuous_val.comp ψ.continuous_toHom

/-- **Chebotarev (the kernel's T18) gives the trace identity on all of `G_ℚ`.** -/
theorem trace_eq_of_attached (r ρ : GaloisRep 5 2) (N : ℕ) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ)
    (hatt : r.AttachedUpToTwist ψ ιC ιL g S) (hρ : ρ.AttachedTo ιC ιL g) (hN : 0 < N) (σ : PkgI4.GQ) :
    (r.mat σ).trace = (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace := by
  have key := C9Rhof.eq_of_eq_on_arithFrob ZInQ.Contrib.frobeniusDense (S ∪ (N * 5).primeFactors)
    (fun σ => (r.mat σ).trace) (fun σ => (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace)
    (continuous_trace_mat r) ((continuous_char ψ).mul (continuous_trace_mat ρ)) (by
      intro p hp hpS v τ hv hτ
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * 5 := fun h => hpS (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hp, h, by positivity⟩))
      obtain ⟨-, α, hα, htr⟩ := hatt p hp hpS1
      obtain ⟨-, β, hβ, htrρ⟩ := hρ p hp hpN
      have hαβ : α = β := ιC.toRingHom.injective (by
        change ιC α = ιC β
        rw [hα, hβ])
      show (r.mat τ).trace = (ψ.toHom τ : PadicAlgCl 5) * (ρ.mat τ).trace
      rw [htr v τ hv hτ, htrρ v τ hv hτ, hαβ])
  exact congrFun key σ

/-- **The determinant identity** `det r = ψ² det ρ_g` on `G_ℚ` (from the trace identity at `σ` and `σ²`). -/
theorem det_eq_of_trace_eq (r ρ : GaloisRep 5 2) (ψ : GaloisChar 5)
    (htr : ∀ σ, (r.mat σ).trace = (ψ.toHom σ : PadicAlgCl 5) * (ρ.mat σ).trace) (σ : PkgI4.GQ) :
    (r.mat σ).det = (ψ.toHom σ : PadicAlgCl 5) ^ 2 * (ρ.mat σ).det := by
  have hmul : ∀ (ρ' : GaloisRep 5 2), ρ'.mat (σ * σ) = ρ'.mat σ * ρ'.mat σ := by
    intro ρ'
    simp only [PkgI4.GaloisRep.mat, map_mul, Units.val_mul]
  have h1 := two_mul_det_fin_two (r.mat σ)
  have h2 := two_mul_det_fin_two (ρ.mat σ)
  rw [← hmul, htr, htr (σ * σ), hmul, map_mul, Units.val_mul] at h1
  have h3 : (2 : PadicAlgCl 5) * (r.mat σ).det = 2 * ((ψ.toHom σ : PadicAlgCl 5) ^ 2 * (ρ.mat σ).det) := by
    rw [h1, mul_left_comm, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

/-! ## §2. Local lemmas over `ℂ_p` (pkg-I4's G9 copy, as hodge-split's `Ysp` machinery) -/

section Local

open ZInQ.Contrib.HodgeSplit

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ σ(x)` is continuous on `G_{ℚ_p}` for every `x ∈ ℂ_p` (approximate `x` by `a ∈ ℚ̄_p`; the stabilizer of `a`
is open and `G_{ℚ_p}` acts by isometries). -/
theorem continuous_cpAct_orbit (x : ℂ_[p]) :
    Continuous fun σ : ZInQ.Contrib.G9.PkgI4.GQp p => ZInQ.Contrib.G9.PkgI4.cpAct p σ x := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha⟩ : ∃ a : PadicAlgCl p, dist x (a : ℂ_[p]) < ε / 2 :=
    (Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe) x (ε / 2) (by positivity)
  have hV : IsOpen {σ : ZInQ.Contrib.G9.PkgI4.GQp p | σ a = σ₀ a} := by
    have hS : IsOpen ((MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) a :
        Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :=
      stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) (L := PadicAlgCl p) a
    have hset : {σ : ZInQ.Contrib.G9.PkgI4.GQp p | σ a = σ₀ a} =
        (fun σ => σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) a) := by
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        show (σ₀⁻¹ * σ) a = a
        rw [AlgEquiv.mul_apply, h]
        show (σ₀⁻¹ * σ₀) a = a
        rw [inv_mul_cancel]; rfl
      · intro h
        have h2 : (σ₀⁻¹ * σ) a = a := h
        rw [AlgEquiv.mul_apply] at h2
        have h3 := congrArg σ₀ h2
        rw [← h3]
        show σ a = (σ₀ * σ₀⁻¹) (σ a)
        rw [mul_inv_cancel]; rfl
    rw [hset]
    exact hS.preimage (continuous_const.mul continuous_id)
  filter_upwards [hV.mem_nhds rfl] with σ hσ
  have hσa : σ a = σ₀ a := hσ
  have e : ZInQ.Contrib.G9.PkgI4.cpAct p σ x - ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ x =
      ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a) + ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x) := by
    rw [map_sub, map_sub, ZInQ.Contrib.G9.PkgI4.cpAct_coe, ZInQ.Contrib.G9.PkgI4.cpAct_coe, hσa]
    ring
  rw [dist_eq_norm, e]
  calc ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a) + ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x)‖
      ≤ ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ (x - a)‖ + ‖ZInQ.Contrib.G9.PkgI4.cpAct p σ₀ ((a : ℂ_[p]) - x)‖ :=
        norm_add_le _ _
    _ = ‖x - a‖ + ‖(a : ℂ_[p]) - x‖ := by
        rw [ZInQ.Contrib.G9.PkgI4.norm_cpAct, ZInQ.Contrib.G9.PkgI4.norm_cpAct]
    _ < ε / 2 + ε / 2 := by
        rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (a : ℂ_[p])]
        exact add_lt_add ha ha
    _ = ε := by ring

/-- `dim_K Y_i(ρ) ≤ n` (from Tate–Sen independence, as in `Ysp_finiteDimensional`). -/
theorem finrank_Ysp_le (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : ZInQ.Contrib.G9.PkgI4.GQp p →* GL (Fin n) E)
    (i : ℤ) : Module.finrank K (Ysp p ρ i K) ≤ n := by
  classical
  haveI := Ysp_finiteDimensional p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ i
  haveI : Module.Free K (Ysp p ρ i K) := Module.Free.of_divisionRing K _
  let b := Module.finBasis K (Ysp p ρ i K)
  have hli : LinearIndependent ℂ_[p] (fun k => ((b k : Ysp p ρ i K) : Fin n → ℂ_[p])) := by
    refine Ysp_linearIndependent p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
      ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ (fun _ => i) _ (fun k => (b k).2) ?_
    intro j₀ a _ hsum
    have h1 : ∑ k, a k • (b k) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      exact hsum
    exact Fintype.linearIndependent_iff.mp b.linearIndependent a h1
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_fin_fun] at this

/-- Two nonzero vectors of `Y`-spaces of different weights are `ℂ_p`-independent (Tate–Sen). -/
theorem linIndep_two (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : ZInQ.Contrib.G9.PkgI4.GQp p →* GL (Fin n) E)
    (i₀ i₁ : ℤ) (hi : i₀ ≠ i₁) (y₀ y₁ : Fin n → ℂ_[p]) (h₀ : y₀ ∈ Ysp p ρ i₀ K)
    (h₁ : y₁ ∈ Ysp p ρ i₁ K) (hy₀ : y₀ ≠ 0) (hy₁ : y₁ ≠ 0) : LinearIndependent ℂ_[p] ![y₀, y₁] := by
  refine Ysp_linearIndependent p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof K ρ ![i₀, i₁] ![y₀, y₁]
    (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩) ?_
  intro j₀ a ha hs
  rw [Fin.sum_univ_two] at hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  have ha0 : ∀ k : Fin 2, a k • ![y₀, y₁] k = 0 → a k = 0 := by
    intro k hk
    by_contra hne
    have hy : ![y₀, y₁] k = 0 := by
      rw [← one_smul K (![y₀, y₁] k), ← inv_mul_cancel₀ hne, mul_smul, hk, smul_zero]
    fin_cases k
    · exact hy₀ hy
    · exact hy₁ hy
  by_cases e : i₀ = j₀
  · have h1 : a 1 = 0 := ha 1 (by simp only [Matrix.cons_val_one]; rw [← e]; exact hi.symm)
    have h0 : a 0 = 0 := ha0 0 (by rw [h1, zero_smul, add_zero] at hs; exact hs)
    exact Fin.forall_fin_two.mpr ⟨h0, h1⟩
  · have h0 : a 0 = 0 := ha 0 (by simpa using e)
    have h1 : a 1 = 0 := ha0 1 (by rw [h0, zero_smul, zero_add] at hs; exact hs)
    exact Fin.forall_fin_two.mpr ⟨h0, h1⟩

end Local

end TwistHT

end HDec.G0Galois.C8Conrad

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

/-- **The square root step** (on-the-spot): if `σ(y) = ψ(σ)² y` on `G_E` with `y ≠ 0`, a square root `c` of `y` in the
algebraically closed `ℂ_p` satisfies `σ(c) = ±ψ(σ) c` on `G_E`; the sign is continuous (`continuous_cpAct_orbit`),
so `σ(c) = ψ(σ) c` on an open subgroup, which contains `G_{E'}` for a finite Galois `E' ⊇ E`. -/
theorem exists_sqrt_twist (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψL : ZInQ.Contrib.G9.PkgI4.GQp p →* (PadicAlgCl p)ˣ) (hψc : Continuous fun σ => (ψL σ : PadicAlgCl p))
    (y : ℂ_[p]) (hy0 : y ≠ 0)
    (hy : ∀ σ ∈ E.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct p σ y = ((ψL σ : PadicAlgCl p) : ℂ_[p]) ^ 2 * y) :
    ∃ E' : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E' ∧ IsGalois ℚ_[p] E' ∧
      E ≤ E' ∧ ∃ c : ℂ_[p], c ≠ 0 ∧ ∀ σ ∈ E'.fixingSubgroup,
        ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ((ψL σ : PadicAlgCl p) : ℂ_[p]) * c := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq y two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hc
    exact hy0 hc.symm
  let ψC : ZInQ.Contrib.G9.PkgI4.GQp p → ℂ_[p] := fun σ => ((ψL σ : PadicAlgCl p) : ℂ_[p])
  have hψCc : Continuous ψC := (UniformSpace.Completion.continuous_coe _).comp hψc
  have hpm : ∀ σ ∈ E.fixingSubgroup, ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ψC σ * c ∨
      ZInQ.Contrib.G9.PkgI4.cpAct p σ c = -(ψC σ * c) := by
    intro σ hσ
    have h2 : (ZInQ.Contrib.G9.PkgI4.cpAct p σ c) ^ 2 = (ψC σ * c) ^ 2 := by
      rw [← map_pow, hc, hy σ hσ, mul_pow, hc]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  let Um : Set (ZInQ.Contrib.G9.PkgI4.GQp p) := {σ | ZInQ.Contrib.G9.PkgI4.cpAct p σ c = -(ψC σ * c)}
  have hUm : IsClosed Um := isClosed_eq (continuous_cpAct_orbit p c) (hψCc.mul continuous_const).neg
  have hG : IsOpen (E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) :=
    IntermediateField.fixingSubgroup_isOpen E
  have hopen : IsOpen ((E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) ∩ Umᶜ) :=
    hG.inter hUm.isOpen_compl
  have h1 : (1 : ZInQ.Contrib.G9.PkgI4.GQp p) ∈ (E.fixingSubgroup : Set (ZInQ.Contrib.G9.PkgI4.GQp p)) ∩ Umᶜ := by
    refine ⟨E.fixingSubgroup.one_mem, fun h => ?_⟩
    have h' : ZInQ.Contrib.G9.PkgI4.cpAct p 1 c = -(ψC 1 * c) := h
    have hψ1 : ψC 1 = 1 := by simp [ψC]
    have hone : ZInQ.Contrib.G9.PkgI4.cpAct p 1 c = c := ZInQ.Contrib.G9.cpAct_one p c
    rw [hone, hψ1, one_mul] at h'
    have h2 : (2 : ℂ_[p]) * c = 0 := by linear_combination h'
    exact hc0 ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  obtain ⟨L, hLfd, hLn, hLsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).mp (hopen.mem_nhds h1)
  haveI := hLfd
  let EL : IntermediateField ℚ_[p] (PadicAlgCl p) := E ⊔ L
  let E' : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.normalClosure ℚ_[p] EL (PadicAlgCl p)
  have hle : EL ≤ E' := IntermediateField.le_normalClosure EL
  refine ⟨E', normalClosure.is_finiteDimensional ℚ_[p] EL (PadicAlgCl p),
    IsGalois.normalClosure ℚ_[p] EL (PadicAlgCl p), le_sup_left.trans hle, c, hc0, ?_⟩
  intro σ hσ
  have hσL : σ ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le (le_sup_right.trans hle) hσ
  obtain ⟨hσE, hσm⟩ := hLsub hσL
  rcases hpm σ hσE with h | h
  · exact h
  · exact absurd h hσm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The conclusion**: a character with values in a finite Galois `E'` and a nonzero `c ∈ ℂ_p` with `σ(c) = ψ(σ) c` on
`G_{E'}` is Hodge–Tate of weight `0` (`htMult_eq_finrank_Ysp`, Tate–Sen independence). -/
theorem hasHTWeights_zero_of_twist (E' : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E']
    [IsGalois ℚ_[p] E'] (ψL : ZInQ.Contrib.G9.PkgI4.GQp p →* (PadicAlgCl p)ˣ)
    (hψE : ∀ σ, (ψL σ : PadicAlgCl p) ∈ E') (c : ℂ_[p]) (hc0 : c ≠ 0)
    (hc : ∀ σ ∈ E'.fixingSubgroup,
      ZInQ.Contrib.G9.PkgI4.cpAct p σ c = ((ψL σ : PadicAlgCl p) : ℂ_[p]) * c) :
    ∃ ψE : PkgI4.GQp p →* E'ˣ, (∀ σ, (((ψE σ : E'ˣ) : E') : PadicAlgCl p) = ψL σ) ∧
      PkgI4.HasHTWeights p (charRep ψE) {0} := by
  let ψE : PkgI4.GQp p →* E'ˣ :=
    { toFun := fun σ => Units.mk0 ⟨ψL σ, hψE σ⟩ (fun h => (ψL σ).ne_zero (congrArg Subtype.val h))
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Units.ext (Subtype.ext (by simp)) }
  refine ⟨ψE, fun σ => rfl, fun w => ?_⟩
  have hbr : PkgI4.htMult p (charRep ψE) w = ZInQ.Contrib.G9.PkgI4.htMult p (charRep ψE) w := rfl
  rw [hbr, htMult_eq_finrank_Ysp p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof E' (charRep ψE) w]
  let cv : Fin 1 → ℂ_[p] := fun _ => c
  have hcv0 : cv ≠ 0 := fun h => hc0 (congrFun h 0)
  have hcv : cv ∈ Ysp p (charRep ψE) 0 E' := by
    intro σ hσ
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hval : algebraMap E' ℂ_[p] ((ψE σ : E'ˣ) : E') = ((ψL σ : PadicAlgCl p) : ℂ_[p]) := rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.transpose_apply, matC, Matrix.map_apply,
      Pi.smul_apply, vAct, cycPow_zero, one_smul]
    have hm : ((charRep ψE σ : GL (Fin 1) E') : Matrix (Fin 1) (Fin 1) E') 0 0 = ((ψE σ : E'ˣ) : E') := by
      simp [charRep, Matrix.algebraMap_matrix_apply]
    rw [hm, hval]
    exact (hc σ hσ).symm
  haveI : ∀ i : ℤ, FiniteDimensional E' (Ysp p (charRep ψE) i E') := fun i =>
    Ysp_finiteDimensional p ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
      ZInQ.Contrib.CloudB3W11.axSenTate_proof E' (charRep ψE) i
  have hle : ∀ i : ℤ, Module.finrank E' (Ysp p (charRep ψE) i E') ≤ 1 := fun i =>
    finrank_Ysp_le p E' (charRep ψE) i
  by_cases hw : w = 0
  · subst hw
    rw [neg_zero, Multiset.count_singleton_self]
    have hne0 : Ysp p (charRep ψE) 0 E' ≠ ⊥ := by
      intro h
      have : cv ∈ (⊥ : Submodule E' (Fin 1 → ℂ_[p])) := h ▸ hcv
      exact hcv0 ((Submodule.mem_bot E').mp this)
    have hpos : 0 < Module.finrank E' (Ysp p (charRep ψE) 0 E') := by
      rcases Nat.eq_zero_or_pos (Module.finrank E' (Ysp p (charRep ψE) 0 E')) with h0 | h0
      · exact absurd (Submodule.finrank_eq_zero.mp h0) hne0
      · exact h0
    have := hle 0
    omega
  · rw [Multiset.count_singleton, if_neg hw]
    by_contra hne
    have hne' : Ysp p (charRep ψE) (-w) E' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hne
      exact hne rfl
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
    have hli := linIndep_two p E' (charRep ψE) 0 (-w) (by omega) cv z hcv hz hcv0 hz0
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at this
    omega

end Local

end TwistHT

end HDec.G0Galois.C8Conrad

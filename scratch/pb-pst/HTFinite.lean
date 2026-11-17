import ZInQKernel.Contrib.OneProof.PanBergerDict
import ZInQKernel.Contrib.OneProof.AxSenTate

/-!
# pb-pst (b): `(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` is finite-dimensional (from Ax–Sen–Tate)

`htMultE ρ w = finrank_E (htSpaceE ρ w)` is a genuine dimension: `htSpaceE ρ w` is finite-dimensional over `E`
(`finiteDimensional_htSpaceE`), in fact `dim_E ≤ n` (`htMultE_le`). Proof: `ℚ_p`-linearly independent
`G_{ℚ_p}`-invariant vectors of `ℂ_p ⊗ V` are `ℂ_p`-linearly independent (a minimal relation is fixed by `G_{ℚ_p}`,
so has coefficients in `ℂ_p^{G_{ℚ_p}} = ℚ_p`, Ax–Sen–Tate, `axSenTate_proof`).
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace HTFinite

open Module PanBergerSplit
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- `ℂ_p^{G_{ℚ_p}} = ℚ_p` (Ax–Sen–Tate at `K = ℚ_p`). -/
theorem fixed_eq_algebraMap (c : ℂ_[p]) (hc : ∀ σ : GQp p, cpAct p σ c = c) :
    ∃ q : ℚ_[p], c = algebraMap ℚ_[p] ℂ_[p] q := by
  obtain ⟨y, hy⟩ := ZInQ.Contrib.CloudB3W11.axSenTate_proof p
    (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) c (fun σ _ => hc σ)
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp y.2
  refine ⟨q, ?_⟩
  rw [hy, ← hq, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]

section Descent

variable {M : Type*} [AddCommGroup M] [Module ℂ_[p] M] [Module ℚ_[p] M]
  [IsScalarTower ℚ_[p] ℂ_[p] M]

open Classical in
/-- **Galois descent for `ℂ_p`-semilinear actions**: if `T σ` is additive and `σ`-semilinear, every
`ℂ_p`-linear relation among `T`-invariant vectors comes from a nonzero `ℚ_p`-linear relation. -/
theorem exists_rat_relation (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    {ι : Type*} [Fintype ι] (x : ι → M) (hx : ∀ σ i, T σ (x i) = x i) :
    ∀ (N : ℕ) (c : ι → ℂ_[p]), (Finset.univ.filter fun i => c i ≠ 0).card = N → c ≠ 0 →
      ∑ i, c i • x i = 0 → ∃ q : ι → ℚ_[p], q ≠ 0 ∧ ∑ i, q i • x i = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hcard hc0 hrel
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  set c' : ι → ℂ_[p] := fun i => (c j)⁻¹ * c i with hc'
  have hc'j : c' j = 1 := inv_mul_cancel₀ hj
  have hrel' : ∑ i, c' i • x i = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hsupp' : ∀ i, c' i ≠ 0 ↔ c i ≠ 0 := fun i => by
    simp only [hc', ne_eq, mul_eq_zero, inv_eq_zero, hj, false_or]
  rcases Classical.em (∀ σ i, cpAct p σ (c' i) = c' i) with hfix | hfix
  · choose q hq using fun i => fixed_eq_algebraMap p (c' i) (fun σ => hfix σ i)
    refine ⟨q, fun h0 => ?_, ?_⟩
    · have := hq j
      rw [hc'j, congrFun h0 j, Pi.zero_apply, map_zero] at this
      exact one_ne_zero this
    · rw [← hrel']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq i, algebraMap_smul]
  · push Not at hfix
    obtain ⟨σ, i₀, hi₀⟩ := hfix
    set d : ι → ℂ_[p] := fun i => cpAct p σ (c' i) - c' i with hd
    have hdrel : ∑ i, d i • x i = 0 := by
      have h1 : T σ (∑ i, c' i • x i) = ∑ i, cpAct p σ (c' i) • x i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hT, hx]
      rw [hrel', map_zero] at h1
      simp only [hd, sub_smul, Finset.sum_sub_distrib, ← h1, hrel', sub_zero]
    have hdj : d j = 0 := by simp only [hd, hc'j, map_one, sub_self]
    have hd0 : d ≠ 0 := fun h0 => hi₀ (sub_eq_zero.mp (congrFun h0 i₀))
    have hsub : (Finset.univ.filter fun i => d i ≠ 0) ⊂ (Finset.univ.filter fun i => c i ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.mpr ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [← hsupp']
        intro h0
        apply hi
        simp only [hd, h0, map_zero, sub_zero]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdj, ne_eq, not_true_eq_false,
          not_false_eq_true]
    exact ih _ (hcard ▸ Finset.card_lt_card hsub) d rfl hd0 hdrel

/-- `ℚ_p`-linearly independent invariant vectors are `ℂ_p`-linearly independent. -/
theorem linearIndependent_of_invariant (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    {ι : Type*} [Fintype ι] (x : ι → M) (hx : ∀ σ i, T σ (x i) = x i)
    (hli : LinearIndependent ℚ_[p] x) : LinearIndependent ℂ_[p] x := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  obtain ⟨q, hq0, hq⟩ := exists_rat_relation p T hT x hx _ c rfl
    (fun h0 => hi (congrFun h0 i)) hc
  exact hq0 (funext (hli q hq))

/-- **The invariants are finite-dimensional over `ℚ_p`**, of dimension `≤ dim_{ℂ_p} M`. -/
theorem finrank_invariants_le [Module.Finite ℂ_[p] M] (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    (W : Submodule ℚ_[p] M) (hW : ∀ w ∈ W, ∀ σ, T σ w = w) :
    FiniteDimensional ℚ_[p] W ∧ finrank ℚ_[p] W ≤ finrank ℂ_[p] M := by
  have hbound : ∀ s : Finset W, (LinearIndependent ℚ_[p] fun i : s => (i : W)) →
      s.card ≤ finrank ℂ_[p] M := by
    intro s hs
    have h1 : LinearIndependent ℚ_[p] fun i : s => ((i : W) : M) :=
      hs.map' W.subtype (Submodule.ker_subtype W)
    have h2 := linearIndependent_of_invariant p T hT (fun i : s => ((i : W) : M))
      (fun σ i => hW _ (i : W).2 σ) h1
    simpa using h2.fintype_card_le_finrank
  have hrank := rank_le hbound
  have hfin : FiniteDimensional ℚ_[p] W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_⟩
  have := Module.finrank_le_of_rank_le hrank
  exact this

end Descent

/-! ## The Hodge–Tate spaces -/

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- `σ` on `ℂ_p(w) ⊗ V` is `σ`-semilinear for the `ℂ_p`-structure on the first factor. -/
theorem tensorAct_smul (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p) (c : ℂ_[p])
    (x : ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (htLin p w σ) (vAct p ρ σ) (c • x) =
      cpAct p σ c • TensorProduct.map (htLin p w σ) (vAct p ρ σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul]
    congr 1
    change (cycPow p σ w • cpLin p σ) (c * z) = cpAct p σ c * (cycPow p σ w • cpLin p σ) z
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    change cycPow p σ w • cpAct p σ (c * z) = cpAct p σ c * (cycPow p σ w • cpAct p σ z)
    rw [map_mul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`(ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}` is finite-dimensional over `ℚ_p`**, of dimension `≤ dim_{ℚ_p} V`. -/
theorem finiteDimensional_htU [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    FiniteDimensional ℚ_[p] (htU p ρ w) ∧ finrank ℚ_[p] (htU p ρ w) ≤ finrank ℚ_[p] (Fin n → E) := by
  have h := finrank_invariants_le p
    (fun σ => (TensorProduct.map (htLin p w σ) (vAct p ρ σ)).toAddMonoidHom)
    (fun σ c x => tensorAct_smul p ρ w σ c x) (htU p ρ w)
    (fun x hx σ => hx σ (Subgroup.mem_top σ))
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have hM : finrank ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) = finrank ℚ_[p] (Fin n → E) :=
    Module.finrank_baseChange
  exact ⟨h.1, hM ▸ h.2⟩

/-- **P2: `htSpaceE ρ w = (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` is finite-dimensional over `E`**, so `htMultE ρ w` is its
genuine dimension. -/
theorem finiteDimensional_htSpaceE [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    FiniteDimensional E (PanDict.htSpaceE p ρ w) := by
  have h1 : FiniteDimensional ℚ_[p] (htU p ρ w) := (finiteDimensional_htU p ρ w).1
  have h2 : FiniteDimensional ℚ_[p] ((PanDict.htSpaceE p ρ w).restrictScalars ℚ_[p]) := by
    rw [← PanDict.map_comm_htU]
    exact Module.Finite.map _ _
  have : Module.Finite ℚ_[p] (PanDict.htSpaceE p ρ w) :=
    Module.Finite.equiv (((PanDict.htSpaceE p ρ w).restrictScalarsEquiv ℚ_[p]).restrictScalars ℚ_[p])
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] E _

/-- **`dim_E (V ⊗ ℂ_p(w))^{G_{ℚ_p}} ≤ n`**: the Hodge–Tate multiplicities are bounded by the dimension. -/
theorem htMultE_le [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    PanDict.htMultE p ρ w ≤ n := by
  rw [PanDict.htMultE_eq_htMultU, htMultU]
  have h := (finiteDimensional_htU p ρ w).2
  rw [finrank_fun] at h
  exact Nat.div_le_of_le_mul (by linarith)

end HTFinite
end PkgI4
end HDec

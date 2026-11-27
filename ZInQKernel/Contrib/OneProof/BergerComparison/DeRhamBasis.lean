import ZInQKernel.Contrib.OneProof.LogPTranscendenceBdR

/-! Dimension implies the invariant basis used by the paper's
definition of de Rham admissibility. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst Module
open PanBergerSplit (bdrLin vAct ddrU IsDeRhamU)
open scoped TensorProduct

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000

section LinearIndependence

variable {K L M G : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
variable (g : G → L →+* L)
variable (fixed : ∀ c, (∀ σ, g σ c = c) → ∃ q : K, c = algebraMap K L q)

include fixed

private theorem invariant_independent (T : G → M →+ M)
    (hT : ∀ σ c x, T σ (c • x) = g σ c • T σ x)
    {ι : Type*} [Fintype ι] (x : ι → M)
    (hx : ∀ σ i, T σ (x i) = x i) (hli : LinearIndependent K x) :
    LinearIndependent L x := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  have aux : ∀ (N : ℕ) (c : ι → L), (Finset.univ.filter fun i => c i ≠ 0).card = N →
      ∑ i, c i • x i = 0 → c = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro c hc hrel
      by_contra hne
      obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
        by_contra h
        push Not at h
        exact hne (funext h)
      let c' : ι → L := fun i => (c j)⁻¹ * c i
      have hc'j : c' j = 1 := inv_mul_cancel₀ hj
      have hrel' : ∑ i, c' i • x i = 0 := by
        simp only [c', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
      have hsupp' (i) : c' i = 0 ↔ c i = 0 := by
        simp only [c', mul_eq_zero, inv_eq_zero, hj, false_or]
      by_cases hfix : ∀ σ i, g σ (c' i) = c' i
      · choose q hq using fun i => fixed (c' i) (fun σ => hfix σ i)
        have hqrel : ∑ i, q i • x i = 0 := by
          rw [← hrel']
          exact Finset.sum_congr rfl fun i _ => by rw [hq i, algebraMap_smul]
        have he := hq j
        rw [hc'j, hli q hqrel j, map_zero] at he
        exact one_ne_zero he
      · push Not at hfix
        obtain ⟨σ, i₀, hi₀⟩ := hfix
        let d : ι → L := fun i => g σ (c' i) - c' i
        have hdrel : ∑ i, d i • x i = 0 := by
          have h1 : T σ (∑ i, c' i • x i) = ∑ i, g σ (c' i) • x i := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [hT, hx]
          rw [hrel', map_zero] at h1
          simp only [d, sub_smul, Finset.sum_sub_distrib, ← h1, hrel', sub_zero]
        have hdj : d j = 0 := by simp only [d, hc'j, map_one, sub_self]
        have hsub : (Finset.univ.filter fun i => d i ≠ 0) ⊂ (Finset.univ.filter fun i => c i ≠ 0) := by
          refine (Finset.ssubset_iff_of_subset (fun i hi => ?_)).mpr ⟨j, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            intro hzero
            have h0 := (hsupp' i).2 hzero
            apply hi
            simp only [d, h0, map_zero, sub_zero]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hj
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdj, ne_eq, not_true_eq_false,
              not_false_eq_true]
        have he := ih _ (hc ▸ Finset.card_lt_card hsub) d rfl hdrel
        exact hi₀ (sub_eq_zero.mp (congrFun he i₀))
  intro c h
  exact congrFun (aux _ c rfl h)

end LinearIndependence

private theorem independent_val {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    {W : Submodule K M} {w : ι → W} (hw : LinearIndependent K w) :
    LinearIndependent K (fun i => (w i).val) :=
  hw.map' W.subtype W.ker_subtype

private theorem basis_of_fixed_finrank {K L M G : Type} [Field K] [CommRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite L M]
    (hL : IsField L) (g : G → L →+* L)
    (fixed : ∀ c, (∀ σ, g σ c = c) → ∃ q : K, c = algebraMap K L q)
    (T : G → M →+ M) (hT : ∀ σ c x, T σ (c • x) = g σ c • T σ x)
    (W : Submodule K M) (hW : ∀ w : W, ∀ σ, T σ w.val = w.val)
    (hdim : finrank K W = finrank L M) :
    ∃ (ι : Type) (b : Basis ι L M), ∀ i σ, T σ (b i) = b i := by
  classical
  let : Field L := hL.toField
  have hli {ι : Type} [Fintype ι] (w : ι → W) (hw : LinearIndependent K w) :
      LinearIndependent L (fun i => (w i).val) :=
    invariant_independent g fixed T hT (fun i => (w i).val) (fun σ i => hW (w i) σ)
      (independent_val hw)
  have hbound (s : Finset W) (hs : LinearIndependent K (fun i : s => (i : W))) :
      s.card ≤ finrank L M := by
    simpa only [Fintype.card_coe] using (hli _ hs).fintype_card_le_finrank
  have : FiniteDimensional K W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (rank_le hbound) Cardinal.natCast_lt_aleph0)
  let v := Module.finBasis K W
  have hcard : Fintype.card (Fin (finrank K W)) = finrank L M := (Fintype.card_fin _).trans hdim
  let w : Fin (finrank K W) → M := fun i => (v i).val
  let b := basisOfLinearIndependentOfCardEqFinrank' w (hli v v.linearIndependent) hcard
  refine ⟨Fin (finrank K W), b, fun i σ => ?_⟩
  rw [show b i = w i from congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' ..) i]
  exact hW (v i) σ

variable (p : ℕ) [Fact p.Prime]

/-- De Rham admissibility in invariant basis form. -/
abbrev HasDeRhamBasis {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}
    (ρ : GQp p →* GL (Fin n) E) :=
  ∃ (ι : Type) (b : Basis ι (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E))),
    ∀ i (σ : GQp p), TensorProduct.map (bdrLin p σ) (vAct p ρ σ) (b i) = b i

/-- Dimension admissibility implies basis admissibility over the de Rham field. -/
theorem deRhamBasis_of_isDeRhamU {E : Type} [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] {n : ℕ} (ρ : GQp p →* GL (Fin n) E)
    (hρ : IsDeRhamU p ρ) : HasDeRhamBasis p ρ := by
  classical
  have : Nontrivial (BdR p) := ZInQ.Contrib.G9.BdrKer.Cp.nontrivial_BDeRham p
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have hV : finrank (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E)) = finrank ℚ_[p] (Fin n → E) :=
    Module.finrank_baseChange
  have hdim : finrank ℚ_[p] (ddrU p ρ) = finrank (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
    hρ.trans hV.symm
  exact basis_of_fixed_finrank (K := ℚ_[p]) (L := BdR p)
    (M := BdR p ⊗[ℚ_[p]] (Fin n → E)) (G := GQp p)
    (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p) (fun σ => bdrAct p σ)
    (LogPTransc.bdr_invariant_eq_algebraMap p)
    (fun σ => (TensorProduct.map (bdrLin p σ) (vAct p ρ σ)).toAddMonoidHom)
    (fun σ c x => tensorAct_smul p ρ σ c x) (ddrU p ρ)
    (fun w σ => w.property σ (Subgroup.mem_top σ)) hdim

end ZInQ.Manuscript.BergerComparison

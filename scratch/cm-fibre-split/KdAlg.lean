import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof

/-! # cm-fibre-split: `ℚ(√d)` (`d < 0`) as an imaginary quadratic number field, and finite conductor -/

namespace HDec
namespace CMBranch
namespace FibreSplit

open Polynomial NumberField Module

/-- `ℚ(√d)`, as in the chain's form of Yu's dichotomy. -/
abbrev Kd' (d : ℚ) : Type := AdjoinRoot (X ^ 2 - C d)

theorem irreducible_X_sq_sub {d : ℚ} (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) := by
  have hdeg : (X ^ 2 - C d : ℚ[X]).natDegree = 2 := by
    rw [natDegree_sub_C, natDegree_X_pow]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]; norm_num
  · intro x hx
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]

theorem monic_X_sq_sub (d : ℚ) : (X ^ 2 - C d : ℚ[X]).Monic :=
  monic_X_pow_sub_C d two_ne_zero

theorem fact_irr {d : ℚ} (hd : d < 0) : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) :=
  ⟨irreducible_X_sq_sub hd⟩

theorem finrank_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    Module.finrank ℚ (Kd' d) = 2 := by
  haveI := fact_irr hd
  rw [(AdjoinRoot.powerBasis' (monic_X_sq_sub d)).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_sub_C, natDegree_X_pow]

theorem numberField_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    NumberField (Kd' d) := by
  haveI := fact_irr hd
  haveI : FiniteDimensional ℚ (Kd' d) := (AdjoinRoot.powerBasis' (monic_X_sq_sub d)).finite
  exact ⟨⟩

theorem root_sq {d : ℚ} : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (Kd' d) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

theorem isTotallyComplex_kd {d : ℚ} (hd : d < 0) :
    haveI := fact_irr hd
    IsTotallyComplex (Kd' d) := by
  haveI := fact_irr hd
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  have h1 := congrArg hreal.embedding (root_sq (d := d))
  simp only [map_pow, map_ratCast] at h1
  have h2 : ((d : ℚ) : ℝ) < 0 := by exact_mod_cast hd
  have h3 : hreal.embedding ((algebraMap ℚ (Kd' d)) d) = (d : ℝ) :=
    eq_ratCast (hreal.embedding.comp (algebraMap ℚ (Kd' d))) d
  have h4 : (hreal.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := h1.trans h3
  nlinarith [sq_nonneg (hreal.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

theorem root_not_rat {d : ℚ} (hd : d < 0) :
    AdjoinRoot.root (X ^ 2 - C d : ℚ[X]) ∉ Set.range (algebraMap ℚ (Kd' d)) := by
  haveI := fact_irr hd
  rintro ⟨q, hq⟩
  have h := root_sq (d := d)
  rw [← hq, ← map_pow] at h
  have := (algebraMap ℚ (Kd' d)).injective h
  nlinarith [sq_nonneg q]

/-- **Finite conductor from one irrational element.** A subring `R ⊆ 𝓞_k` of a quadratic field containing an
element `θ ∉ ℚ` has finite index in `𝓞_k` (through `ℤ[θ] ⊆ R` and cm-branch2's `CoxCore.discr_order`). -/
theorem conductor_ne_zero_of_mem {k : Type} [Field k] [NumberField k] (hk : finrank ℚ k = 2)
    (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring) {θ : k} (hθR : θ ∈ R)
    (hnq : θ ∉ Set.range (algebraMap ℚ k)) : LeafQM.AV.conductor R ≠ 0 := by
  classical
  have hθint : IsIntegral ℤ θ := hR hθR
  -- `1, θ` independent over `ℚ`
  have hli : LinearIndependent ℚ ![(1 : k), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hnq
      refine ⟨-s / t, ?_⟩
      have e : (algebraMap ℚ k t) * θ = - algebraMap ℚ k s := by
        rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one] at hst
        linear_combination hst
      have ht' : algebraMap ℚ k t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      rw [map_div₀, map_neg, div_eq_iff ht', ← e, mul_comm]
  -- the minimal polynomial of `θ` over `ℤ` is a monic quadratic
  have hdegQ : (minpoly ℚ θ).natDegree = 2 := by
    have hle : (minpoly ℚ θ).natDegree ≤ 2 := by
      rw [← hk]; exact minpoly.natDegree_le θ
    have hne1 : (minpoly ℚ θ).natDegree ≠ 1 := by
      intro h1
      exact hnq (minpoly.natDegree_eq_one_iff.mp h1)
    have hpos : 0 < (minpoly ℚ θ).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral θ)
    omega
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint
  have hmon := minpoly.monic hθint
  have hdegZ : (minpoly ℤ θ).natDegree = 2 := by
    rw [← hdegQ, hmap, natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int]
  set b : ℤ := (minpoly ℤ θ).coeff 1
  set N : ℤ := (minpoly ℤ θ).coeff 0
  have hθ : θ ^ 2 + b * θ + N = 0 := by
    have h := minpoly.aeval ℤ θ
    rw [aeval_eq_sum_range, hdegZ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at h
    have h2 : (minpoly ℤ θ).coeff 2 = 1 := hdegZ ▸ hmon.coeff_natDegree
    rw [h2] at h
    simp only [zsmul_eq_mul, pow_zero, _root_.mul_one, pow_one, one_zsmul] at h
    linear_combination h
  -- the order `ℤ[θ] = ℤ + ℤθ`
  let S : Subring k :=
    { carrier := {r | ∃ m n : ℤ, r = m + n * θ}
      mul_mem' := by
        rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
        refine ⟨m * m' - n * n' * N, m * n' + n * m' - n * n' * b, ?_⟩
        push_cast
        linear_combination (↑n * ↑n' : k) * hθ
      one_mem' := ⟨1, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
        exact ⟨m + m', n + n', by push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨m, n, rfl⟩
        exact ⟨-m, -n, by push_cast; ring⟩ }
  have hSR : S ≤ R := by
    rintro _ ⟨m, n, rfl⟩
    exact R.add_mem (intCast_mem R m) (R.mul_mem (intCast_mem R n) hθR)
  have hSO : S ≤ (integralClosure ℤ k).toSubring := hSR.trans hR
  have hθS : θ ∈ S := ⟨0, 1, by simp⟩
  have hd := CoxCore.discr_order hk S hSO hθS (fun r hr => hr) hnq hli hθ
  have hne : b ^ 2 - 4 * N ≠ 0 := by
    intro h0
    apply hnq
    refine ⟨-(b : ℚ) / 2, ?_⟩
    have h0' : ((b : k)) ^ 2 = 4 * N := by
      exact_mod_cast (sub_eq_zero.mp h0 : b ^ 2 = 4 * N)
    have hsq : (θ + (b : k) / 2) ^ 2 = 0 := by linear_combination hθ + h0' / 4
    have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rw [map_div₀, map_neg, map_intCast, map_ofNat]
    linear_combination -h1
  have hS0 : S.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
    exact hne hd
  intro h0
  apply hS0
  unfold LeafQM.AV.conductor at h0
  exact Nat.eq_zero_of_zero_dvd (h0 ▸ AddSubgroup.relIndex_dvd_of_le_left _ hSR)

end FibreSplit
end CMBranch
end HDec

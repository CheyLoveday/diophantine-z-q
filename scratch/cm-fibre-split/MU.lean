import Mathlib

/-! # cm-fibre-split: scaled matrix units (manuscript L583, "multiples of matrix units"); pure algebra -/

namespace HDec.CMBranch.FibreSplit

open scoped TensorProduct

/-- `f` are matrix units scaled by `n`: `f i j * f k l = δ_{jk} n f i l` and `f 0 0 + f 1 1 = n`. -/
def IsScaledMatrixUnits {R : Type*} [Ring R] (n : ℕ) (f : Fin 2 → Fin 2 → R) : Prop :=
  (∀ i j k l, f i j * f k l = if j = k then (n : R) * f i l else 0) ∧ f 0 0 + f 1 1 = (n : R)

/-- **Multiples of matrix units exist in `M`** when `ℚ ⊗ M ≅ M₂(k)` and `M` is torsion-free
(`M → ℚ ⊗ M` injective): clear the denominators of `e⁻¹(E_ij)`. -/
theorem exists_scaledMatrixUnits {M : Type*} [Ring M] {k : Type*} [Field k] [Algebra ℚ k]
    (e : ℚ ⊗[ℤ] M ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) k)
    (hinj : ∀ m : M, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin 2 → Fin 2 → M, IsScaledMatrixUnits n f := by
  classical
  let u : Fin 2 × Fin 2 → ℚ ⊗[ℤ] M := fun p => e.symm (Matrix.single p.1 p.2 1)
  have hu : ∀ i j k l, u (i, j) * u (k, l) = if j = k then u (i, l) else 0 := by
    intro i j k l
    simp only [u, ← map_mul, Matrix.single_mul_single]
    split_ifs with h
    · subst h; simp
    · simp [h]
  have hsum : u (0, 0) + u (1, 1) = 1 := by
    simp only [u, ← map_add]
    rw [show (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k) + Matrix.single 1 1 1) = 1 from by
      ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.single, Matrix.one_apply]]
    exact map_one _
  let tm := TensorProduct.mk ℤ ℚ M 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := M) (S := ℚ))
  have hs : ∀ p, ∃ (x : M) (s : ℤ), s ≠ 0 ∧ (1 : ℚ) ⊗ₜ[ℤ] x = s • u p := by
    intro p
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) tm (u p)
    refine ⟨x, s, nonZeroDivisors.coe_ne_zero s, ?_⟩
    rw [Submonoid.smul_def] at h; exact h.symm
  choose x s hs0 hxs using hs
  let m : ℤ := ∏ p, s p
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p
  have hc : ∀ p, ∃ c : ℤ, m = s p * c := fun p => Finset.dvd_prod_of_mem s (Finset.mem_univ p)
  choose c hcm using hc
  let y : Fin 2 × Fin 2 → M := fun p => c p • x p
  have hy : ∀ p, (1 : ℚ) ⊗ₜ[ℤ] y p = m • u p := by
    intro p
    simp only [y, TensorProduct.tmul_smul, hxs, hcm p, smul_smul, mul_comm]
  have hmul1 : ∀ a b : M, (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hint : ∀ z : ℤ, (1 : ℚ) ⊗ₜ[ℤ] (z : M) = (z : ℚ ⊗[ℤ] M) := fun z =>
    map_intCast (Algebra.TensorProduct.includeRight : M →ₐ[ℤ] ℚ ⊗[ℤ] M) z
  have key : ∀ a b : M, (1 : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ[ℤ] b → a = b := by
    intro a b h
    exact sub_eq_zero.mp (hinj _ (by rw [TensorProduct.tmul_sub, h, sub_self]))
  have hrel : ∀ i j k l, y (i, j) * y (k, l) = if j = k then (m : M) * y (i, l) else 0 := by
    intro i j k l
    apply key
    rw [hmul1, hy, hy, smul_mul_smul_comm, hu]
    split_ifs with h
    · rw [hmul1, hint, hy, ← zsmul_eq_mul, smul_smul]
    · simp
  have hsum' : y (0, 0) + y (1, 1) = (m : M) := by
    apply key
    rw [TensorProduct.tmul_add, hy, hy, ← smul_add, hsum, hint, zsmul_eq_mul, _root_.mul_one]
  refine ⟨(m * m).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hm0 hm0),
    fun i j => m • y (i, j), ?_, ?_⟩
  · intro i j k l
    have hn : (((m * m).natAbs : ℕ) : M) = ((m * m : ℤ) : M) := by
      rw [← Int.cast_natCast, Int.natAbs_mul_self' m]
    rw [hn, smul_mul_smul_comm, hrel]
    split_ifs
    · rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, ← mul_assoc, ← mul_assoc,
        Int.cast_comm]
      noncomm_ring
    · simp
  · have hn : (((m * m).natAbs : ℕ) : M) = ((m * m : ℤ) : M) := by
      rw [← Int.cast_natCast, Int.natAbs_mul_self' m]
    rw [hn, ← smul_add, hsum', zsmul_eq_mul, Int.cast_mul]

end HDec.CMBranch.FibreSplit

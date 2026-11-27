import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits

/-! Changing split charts on a quaternion completion. The intertwining
basis is constructed from the images of the matrix units. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Matrix

/-- Two frames on a split matrix algebra differ by conjugation. -/
theorem matrixFrame_inner {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i₀ : n) (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ u : (Matrix n n K)ˣ, ∀ m, φ m * (u : Matrix n n K) = (u : Matrix n n K) * m := by
  let : Nonempty n := ⟨i₀⟩
  let E (i j : n) : Matrix n n K := Matrix.single i j 1
  have hE : φ (E i₀ i₀) ≠ 0 := by
    intro h
    have he := φ.injective (h.trans (map_zero φ).symm)
    have hc := congrArg (fun m : Matrix n n K => m i₀ i₀) he
    simp [E] at hc
  obtain ⟨j, hj⟩ : ∃ j, (φ (E i₀ i₀)).col j ≠ 0 := by
    by_contra! h
    exact hE (Matrix.ext fun i j => congrFun (h j) i)
  let w := (φ (E i₀ i₀)).col j
  have hw₀ : w ≠ 0 := hj
  have hw : (φ (E i₀ i₀)) *ᵥ w = w := by
    dsimp only [w]
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, ← map_mul]
    simp [E]
  let U : Matrix n n K := Matrix.of fun a b => ((φ (E b i₀)) *ᵥ w) a
  have hU (i : n) : U.col i = (φ (E i i₀)) *ᵥ w := rfl
  have ht (i : n) : φ (E i₀ i) * U = Matrix.of (fun a b => ((Pi.single i 1 : n → K) b) * w a) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, hU, Matrix.mulVec_mulVec, ← map_mul,
      Matrix.mulVec_single_one]
    by_cases hij : i = j
    · subst j
      funext a
      simp [E, hw, Matrix.col_apply]
    · have hEij : E i₀ i * E j i₀ = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : K)) i₀ i j hij 1
      rw [hEij, map_zero, Matrix.zero_mulVec]
      funext a
      simp [Matrix.col_apply, Pi.single_eq_of_ne (Ne.symm hij)]
  have hu : IsUnit U := Matrix.mulVec_injective_iff_isUnit.mp (by
    change Function.Injective U.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : U *ᵥ x = 0 := hx
    funext i
    have hzero : (φ (E i₀ i) * U) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec, hx', Matrix.mulVec_zero]
    have hvec : (φ (E i₀ i) * U) *ᵥ x = x i • w := by
      rw [ht i]
      ext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [hvec, smul_eq_zero] at hzero
    exact hzero.resolve_right hw₀)
  refine ⟨hu.unit, fun m => ?_⟩
  rw [hu.unit_spec]
  induction m using Matrix.induction_on with
  | h_add x y hx hy => rw [map_add, Matrix.add_mul, Matrix.mul_add, hx, hy]
  | h_std_basis a b c =>
    have he : (Matrix.single a b c : Matrix n n K) = c • E a b := by
      ext i j
      by_cases ha : a = i <;> by_cases hb : b = j <;> simp [E, Matrix.single, ha, hb]
    rw [he, map_smul, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, hU, Matrix.mulVec_mulVec, ← map_mul,
      ← Matrix.mulVec_mulVec]
    change φ (E a b * E j i₀) *ᵥ w = U *ᵥ (Matrix.single a b 1 *ᵥ Pi.single j 1)
    rw [Matrix.single_mulVec_eq]
    by_cases hj : b = j
    · subst j
      simp [E, hU]
    · have hEbj : E a b * E j i₀ = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : K)) a b j hj 1
      rw [hEbj, map_zero, Matrix.zero_mulVec]
      simp [Pi.single_eq_of_ne hj]

open Eichler Adelic

/-- Matching split normal forms in two rational Tate frames give a local
generator for the reference lattice. -/
theorem splitReference_conjugate {a b : ℚ} {R S : Order a b} (p : Prime) (n : ℕ)
    (f g : Bp p.val a b ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val])
    (hf : f '' (R.completion p.val : Set (Bp p.val a b)) = standardLevel p.val n)
    (hg : g '' (S.completion p.val : Set (Bp p.val a b)) = standardLevel p.val n) :
    ∃ u : (Bp p.val a b)ˣ, ∀ x : Bp p.val a b,
      (↑u⁻¹ : Bp p.val a b) * x * (u : Bp p.val a b) ∈ R.completion p.val ↔
        x ∈ S.completion p.val := by
  obtain ⟨v, hv⟩ := matrixFrame_inner 0 (g.symm.trans f)
  let u := Units.map f.symm.toMonoidHom v
  have hu (x : Bp p.val a b) : f ((↑u⁻¹ : Bp p.val a b) * x * (u : Bp p.val a b)) = g x := by
    have hi : f x * (v : M2 ℚ_[p.val]) = (v : M2 ℚ_[p.val]) * g x := by
      simpa using hv (g x)
    rw [map_mul, map_mul]
    change f (f.symm ↑v⁻¹) * f x * f (f.symm ↑v) = _
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, mul_assoc, hi, ← mul_assoc,
      Units.inv_mul, one_mul]
  have hmem (e : Bp p.val a b ≃ₐ[ℚ_[p.val]] M2 ℚ_[p.val])
      (T : Order a b) (hT : e '' (T.completion p.val : Set (Bp p.val a b)) = standardLevel p.val n)
      (x : Bp p.val a b) : e x ∈ standardLevel p.val n ↔ x ∈ T.completion p.val := by
    rw [← hT]
    exact ⟨fun ⟨y, hy, hxy⟩ => e.injective hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨u, fun x => ?_⟩
  rw [← hmem f R hf, hu, hmem g S hg]

end ZInQ.Manuscript.RC.HCMV21

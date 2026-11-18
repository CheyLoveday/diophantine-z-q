import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord

/-!
# Stage cone, part 1: the augmented two-term complex is exact when the coordinate is nonzero

For a square matrix `D` over a field with class `z` (`D z = 0`), functional `w` (`w D = 0`) and
class-functional coordinate `u` (`z wᵀ = u · adj D`, RC15's `IsClassFunctionalCoord`), if `u ≠ 0`
and `adj D ≠ 0`, the augmented complex `K --z--> Kⁿ --D--> Kⁿ --w--> K` is exact
(`isExact_aug_twoTerm`), hence contractible (`contraction_aug_twoTerm`). The proof is by cofactors:
for an entry `adj D i j ≠ 0`,

* `D.updateRow j eᵢ` is invertible (its determinant is `adj D i j`), so a vector of `ker D` with
  vanishing `i`-th coordinate is zero, and `ker D = K z` (`mem_span_of_mulVec_eq_zero`);
* `D.updateCol i eⱼ` is invertible, so every `b` with `w · b = 0` is in the image of `D`
  (`exists_mulVec_eq_of_dotProduct_eq_zero`).

No rank theory is used.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.StageCone

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type*} [Field K] {n : ℕ}

theorem updateRow_mulVec_apply (D : Matrix (Fin n) (Fin n) K) (j : Fin n) (r x : Fin n → K)
    (k : Fin n) : (D.updateRow j r *ᵥ x) k = if k = j then r ⬝ᵥ x else (D *ᵥ x) k := by
  by_cases hk : k = j
  · subst hk; simp [mulVec, updateRow_self]
  · simp [mulVec, hk]

/-- `det (D.updateRow j eᵢ) = adj D i j`. -/
theorem det_updateRow_single (D : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (D.updateRow j (Pi.single i 1)).det = D.adjugate i j :=
  (adjugate_apply D i j).symm

/-- `det (D.updateCol i eⱼ) = adj D i j`. -/
theorem det_updateCol_single (D : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (D.updateCol i (Pi.single j 1)).det = D.adjugate i j := by
  rw [show D.updateCol i (Pi.single j 1) = (Dᵀ.updateRow i (Pi.single j 1))ᵀ by
      rw [← updateCol_transpose, transpose_transpose],
    det_transpose, det_updateRow_single, ← adjugate_transpose]
  rfl

/-- A vector of `ker D` vanishing at `i` is zero when `adj D i j ≠ 0`. -/
theorem eq_zero_of_mulVec_eq_zero_of_apply {D : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (hij : D.adjugate i j ≠ 0) {x : Fin n → K} (hx : D *ᵥ x = 0) (hxi : x i = 0) : x = 0 := by
  apply eq_zero_of_mulVec_eq_zero (M := D.updateRow j (Pi.single i 1))
  · rw [det_updateRow_single]; exact hij
  · funext k
    rw [updateRow_mulVec_apply]
    split_ifs
    · simp [hxi]
    · simp [hx]

/-- **`ker D = K z`** when `z ∈ ker D`, `z i ≠ 0` and `adj D i j ≠ 0`. -/
theorem mem_span_of_mulVec_eq_zero {D : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (hij : D.adjugate i j ≠ 0) {z : Fin n → K} (hz : D *ᵥ z = 0) (hzi : z i ≠ 0)
    {x : Fin n → K} (hx : D *ᵥ x = 0) : ∃ c : K, c • z = x := by
  refine ⟨x i / z i, ?_⟩
  have h := eq_zero_of_mulVec_eq_zero_of_apply hij (x := x - (x i / z i) • z)
    (by rw [mulVec_sub, mulVec_smul, hx, hz, smul_zero, sub_zero])
    (by simp [div_mul_cancel₀ _ hzi])
  exact (sub_eq_zero.mp h).symm

theorem updateCol_mulVec (D : Matrix (Fin n) (Fin n) K) (i j : Fin n) (x : Fin n → K) :
    D.updateCol i (Pi.single j 1) *ᵥ x =
      D *ᵥ Function.update x i 0 + x i • Pi.single j 1 := by
  funext k
  rw [Pi.add_apply, ← sub_eq_iff_eq_add']
  simp only [mulVec, dotProduct, ← Finset.sum_sub_distrib, updateCol_apply,
    Function.update_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply, mul_comm]
  · intro l _ hl
    simp [hl]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **`im D = ker w`** when `w D = 0`, `w j ≠ 0` and `adj D i j ≠ 0`. -/
theorem exists_mulVec_eq_of_dotProduct_eq_zero {D : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (hij : D.adjugate i j ≠ 0) {w : Fin n → K} (hw : w ᵥ* D = 0) (hwj : w j ≠ 0)
    {b : Fin n → K} (hb : w ⬝ᵥ b = 0) : ∃ x, D *ᵥ x = b := by
  set D' := D.updateCol i (Pi.single j 1)
  have hdet : IsUnit D'.det := by
    rw [isUnit_iff_ne_zero, det_updateCol_single]; exact hij
  set x := D'⁻¹ *ᵥ b
  have hx : D' *ᵥ x = b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have e := updateCol_mulVec D i j x
  rw [hx] at e
  have hxi : x i = 0 := by
    have h2 := congrArg (w ⬝ᵥ ·) e
    simp only [dotProduct_add, dotProduct_mulVec, hw, zero_dotProduct, zero_add, hb,
      dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_right hwj
  refine ⟨Function.update x i 0, ?_⟩
  rw [e, hxi, zero_smul, add_zero]

/-- An entry where the coordinate data are all nonzero. -/
theorem exists_good_entry {D : Matrix (Fin n) (Fin n) K} {z w : Fin n → K} {u : K}
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) (hu0 : u ≠ 0)
    (hadj : D.adjugate ≠ 0) : ∃ i j, D.adjugate i j ≠ 0 ∧ z i ≠ 0 ∧ w j ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, D.adjugate i j ≠ 0 := ZInQ.Manuscript.RC.Central.exists_entry_ne_zero hadj
  have e := congrFun (congrFun hu i) j
  rw [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at e
  have hne : z i * w j ≠ 0 := by rw [e]; exact mul_ne_zero hu0 hij
  exact ⟨i, j, hij, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- **The augmented two-term complex is exact** when the coordinate and the adjugate are nonzero.
PROVED. -/
theorem isExact_aug_twoTerm (D : Matrix (Fin n) (Fin n) K) (z w : Fin n → K) (u : K)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) (hu0 : u ≠ 0)
    (hadj : D.adjugate ≠ 0) : ((twoTerm D).aug z w hz hw).IsExact := by
  obtain ⟨i, j, hij, hzi, hwj⟩ := exists_good_entry hu hu0 hadj
  have hz' : D *ᵥ z = 0 := hz
  have hw' : w ᵥ* D = 0 := hw
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_⟩
  · have e := congrFun hx i
    simp [FourCx.aug, twoTerm, mulVec, dotProduct, Fintype.sum_sum_type] at e
    funext t
    rcases t with t | t
    · exact t.elim
    · exact (e.resolve_left hzi : x (Sum.inr ()) = 0)
  · obtain ⟨c, hc⟩ := mem_span_of_mulVec_eq_zero hij hz' hzi (hy : D *ᵥ y = 0)
    refine ⟨Sum.elim (fun e => e.elim) (fun _ => c), ?_⟩
    rw [← hc]
    funext k
    simp [FourCx.aug, twoTerm, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  · have e := congrFun hy (Sum.inr ())
    have hb : w ⬝ᵥ y = 0 := by
      simpa [FourCx.aug, twoTerm, mulVec, dotProduct, fromRows_apply_inr] using e
    exact exists_mulVec_eq_of_dotProduct_eq_zero hij hw' hwj hb
  · refine ⟨(y (Sum.inr ()) / w j) • Pi.single j 1, ?_⟩
    funext t
    rcases t with t | t
    · exact t.elim
    · simp only [FourCx.aug, twoTerm, mulVec, dotProduct, fromRows_apply_inr]
      simp
      rcases t
      rw [Finset.sum_eq_single j (fun l _ hl => by simp [hl]) (by simp)]
      simp only [Pi.single_eq_same, mul_one]
      field_simp

/-- The augmented two-term complex is contractible when the coordinate and the adjugate are
nonzero. -/
theorem contraction_aug_twoTerm (D : Matrix (Fin n) (Fin n) K) (z w : Fin n → K) (u : K)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u) (hu0 : u ≠ 0)
    (hadj : D.adjugate ≠ 0) : Nonempty (Contraction ((twoTerm D).aug z w hz hw).toBased) :=
  exists_contraction _ (FourCx.isExact_toBased _ (isExact_aug_twoTerm D z w u hz hw hu hu0 hadj))

end ZInQ.Contrib.CloudB3RC53.StageCone

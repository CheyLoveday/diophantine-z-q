import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Corestriction

/-!
# Lane RC26 (round 3): normalized transversals and the retraction `G → U`
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

universe u

namespace RightTransversal

variable {G : Type u} [Group G] {U : Subgroup G} (R : RightTransversal U)

/-- Two elements have the same representative exactly when they lie in the same right coset. -/
theorem hat_eq_iff (x y : G) : R.hat y = R.hat x ↔ y * x⁻¹ ∈ U := by
  refine ⟨fun h => ?_, R.hat_eq x y⟩
  have h1 := R.hat_mul_inv_mem x
  have h2 := R.hat_mul_inv_mem y
  rw [h] at h2
  have := U.mul_mem (U.inv_mem h2) h1
  simpa [mul_assoc] using this

open Classical in
/-- **The normalized transversal**: the representative of the trivial coset `U` is `1`
(replace `1̂` by `1` in `T`). -/
def normalize : RightTransversal U where
  T := insert 1 (R.T.erase (R.hat 1))
  hat x := if R.hat x = R.hat 1 then 1 else R.hat x
  hat_mem x := by
    split_ifs with h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, R.hat_mem x⟩)
  hat_mul_inv_mem x := by
    split_ifs with h
    · have hx := (R.hat_eq_iff 1 x).1 h
      simpa using hx
    · exact R.hat_mul_inv_mem x
  hat_eq x y hxy := by
    have := R.hat_eq x y hxy
    simp only [this]
  hat_self t ht := by
    rcases Finset.mem_insert.1 ht with rfl | ht'
    · simp
    · obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 ht'
      rw [R.hat_self t hmem]
      simp [hne]

/-- The normalized transversal represents the trivial coset by `1`. -/
theorem normalize_hat_one : R.normalize.hat 1 = 1 := by
  classical
  simp [normalize]

/-- In a normalized transversal, every element of `U` is represented by `1`. -/
theorem hat_of_mem (h1 : R.hat 1 = 1) {u : G} (hu : u ∈ U) : R.hat u = 1 := by
  rw [← h1]
  exact R.hat_eq 1 u (by simpa using hu)

/-- The `U`-component of a representative is trivial. -/
theorem uPart_of_mem_T {t : G} (ht : t ∈ R.T) : R.uPart t = 1 := by
  apply Subtype.ext
  simp [R.hat_self t ht]

/-- In a normalized transversal, the `U`-component of an element of `U` is itself. -/
theorem uPart_of_mem (h1 : R.hat 1 = 1) (u : U) : R.uPart (u : G) = u := by
  apply Subtype.ext
  simp [R.hat_of_mem h1 u.2]

/-- **The retraction `G → U` is `U`-equivariant**: `w(u y) = u w(y)`. -/
theorem uPart_mul (u : U) (y : G) : R.uPart ((u : G) * y) = u * R.uPart y := by
  apply Subtype.ext
  have h : R.hat ((u : G) * y) = R.hat y := R.hat_eq y _ (by simp [mul_assoc])
  simp [h, mul_assoc]

end RightTransversal

end ZInQ.Manuscript.RC.SelmerComplex

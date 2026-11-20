import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.BaseZeroBridge
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.CoordinateUnit

/-!
# Base zero end to end, part 1: the primitive complex as a graded complex

The primitive complex at the base of Lemma `ex:arith-base-zero` (tex L4330–4373) is, in the central
lane's form (`RC/Central/BaseZero.lean`), the bounded finite free complex
`[A^{m+1} --D--> A^{m+1}]` in degrees one and two, with retained cycle `z`, closed functional `w`
and class-functional coordinate `u_prim`. This file encodes it as a graded complex
`(Fin (m+1) ⊕ Fin (m+1), deg, d)` (degree one on the left summand, two on the right, `d` the block
`D`) for the minimal-model machinery of `MinimalComplexes/`, and computes its `ρ`-central
dimensions from `rank (D ⊗ ρ) = m`: `(1, 1)` in degrees one and two and `0` elsewhere.

**Classification.** GLUE, PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.BaseZeroEndToEnd

open Matrix ZInQ.Contrib.CloudB3RC53.MinimalComplexes

variable {R : Type*} [CommRing R] {k : Type*} [Field k] {m : ℕ}

/-- The index set of the two-term complex: degree one (`inl`) and degree two (`inr`). -/
abbrev TT (m : ℕ) := Fin (m + 1) ⊕ Fin (m + 1)

/-- The grading: `1` on `inl`, `2` on `inr`. -/
def ttDeg (m : ℕ) : TT m → ℤ := Sum.elim (fun _ => 1) (fun _ => 2)

/-- The differential with block `D` from degree one to degree two. -/
def ttDiff (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : Matrix (TT m) (TT m) R :=
  Matrix.fromBlocks 0 0 D 0

@[simp] theorem ttDiff_inr_inl (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (i j : Fin (m + 1)) :
    ttDiff D (Sum.inr i) (Sum.inl j) = D i j := rfl

theorem ttDiff_eq_zero_of (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (y x : TT m)
    (h : ¬ (∃ i j, y = Sum.inr i ∧ x = Sum.inl j)) : ttDiff D y x = 0 := by
  rcases y with i | i <;> rcases x with j | j
  · rfl
  · rfl
  · exact absurd ⟨i, j, rfl, rfl⟩ h
  · rfl

theorem ttDiff_graded (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    IsGradedDiff (ttDeg m) (ttDiff D) := by
  intro a b hab
  rcases a with i | i <;> rcases b with j | j
  · exact absurd rfl hab
  · exact absurd rfl hab
  · rfl
  · exact absurd rfl hab

theorem ttDiff_sq (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) : ttDiff D * ttDiff D = 0 := by
  simp [ttDiff, Matrix.fromBlocks_multiply]

/-! ### Cardinalities of the degrees -/

theorem card_ttDeg_one : Fintype.card {a : TT m // ttDeg m a = 1} = m + 1 := by
  have e : Fin (m + 1) ≃ {a : TT m // ttDeg m a = 1} :=
    Equiv.ofBijective (fun j => ⟨Sum.inl j, rfl⟩) ⟨fun a b h => by
      simpa using congrArg Subtype.val h, by
      rintro ⟨a | a, ha⟩
      · exact ⟨a, rfl⟩
      · exact absurd ha (by simp [ttDeg])⟩
  exact (Fintype.card_congr e).symm.trans (Fintype.card_fin _)

theorem card_ttDeg_two : Fintype.card {a : TT m // ttDeg m a = 2} = m + 1 := by
  have e : Fin (m + 1) ≃ {a : TT m // ttDeg m a = 2} :=
    Equiv.ofBijective (fun j => ⟨Sum.inr j, rfl⟩) ⟨fun a b h => by
      simpa using congrArg Subtype.val h, by
      rintro ⟨a | a, ha⟩
      · exact absurd ha (by simp [ttDeg])
      · exact ⟨a, rfl⟩⟩
  exact (Fintype.card_congr e).symm.trans (Fintype.card_fin _)

theorem card_ttDeg_other {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Fintype.card {a : TT m // ttDeg m a = n} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  rcases a with a | a
  · exact h1 ha.symm
  · exact h2 ha.symm

/-! ### Residue ranks of the columns -/

variable [IsLocalRing R]

set_option linter.unusedSectionVars false

theorem resColsAt_tt_eq_zero (ρ : R →+* k) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) {n : ℤ}
    (hn : n ≠ 1) : resColsAt ρ (ttDeg m) (ttDiff D) n = 0 := by
  ext y ⟨x, hx⟩
  simp only [resColsAt, submatrix_apply, id, map_apply, Matrix.zero_apply]
  rw [ttDiff_eq_zero_of, map_zero]
  rintro ⟨i, j, rfl, rfl⟩
  exact hn hx.symm

theorem rank_resColsAt_tt_one (ρ : R →+* k) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (resColsAt ρ (ttDeg m) (ttDiff D) 1).rank = (D.map ρ).rank := by
  set B : Matrix (TT m) (Fin (m + 1)) k := Matrix.of fun y i => if y = Sum.inr i then 1 else 0
  set C : Matrix (Fin (m + 1)) {a : TT m // ttDeg m a = 1} k :=
    Matrix.of fun j a => if a.1 = Sum.inl j then 1 else 0
  have hM : resColsAt ρ (ttDeg m) (ttDiff D) 1 = B * D.map ρ * C := by
    ext y ⟨x, hx⟩
    rcases x with x | x
    · rcases y with y | y <;>
        simp [resColsAt, Matrix.mul_apply, B, C, ttDiff, Finset.sum_ite_eq', Finset.sum_ite_eq]
    · exact absurd hx (by simp [ttDeg])
  have hBB : Bᵀ * B = 1 := by
    ext i i'
    rw [mul_apply, one_apply, Finset.sum_eq_single (Sum.inr i)]
    · by_cases h : i = i' <;> simp [B, h]
    · intro y _ hy; simp [B, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hCC : C * Cᵀ = 1 := by
    ext j j'
    rw [mul_apply, one_apply, Finset.sum_eq_single ⟨Sum.inl j, rfl⟩]
    · by_cases h : j = j' <;> simp [C, h]
    · rintro ⟨a, ha⟩ _ hne
      have : a ≠ Sum.inl j := fun h => hne (Subtype.ext h)
      simp [C, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hM]
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · have : D.map ρ = Bᵀ * (B * D.map ρ * C) * Cᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBB, Matrix.one_mul, Matrix.mul_assoc, hCC,
        Matrix.mul_one]
    calc (D.map ρ).rank = (Bᵀ * (B * D.map ρ * C) * Cᵀ).rank := by rw [← this]
      _ ≤ (B * D.map ρ * C).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- **The central dimensions of the two-term complex**: from `rank (D ⊗ ρ) = m`, the `ρ`-residue
cohomology of `[A^{m+1} --D--> A^{m+1}]` is one-dimensional in degrees one and two and zero
elsewhere. -/
theorem resDimAt_tt (ρ : R →+* k) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hcentral : (D.map ρ).rank = m) :
    (∀ n, n ≠ 1 → n ≠ 2 → resDimAt ρ (ttDeg m) (ttDiff D) n = 0) ∧
      resDimAt ρ (ttDeg m) (ttDiff D) 1 = 1 ∧ resDimAt ρ (ttDeg m) (ttDiff D) 2 = 1 := by
  have r1 := rank_resColsAt_tt_one ρ D
  rw [hcentral] at r1
  refine ⟨fun n h1 h2 => ?_, ?_, ?_⟩
  · unfold resDimAt
    rw [card_ttDeg_other h1 h2, resColsAt_tt_eq_zero ρ D h1,
      resColsAt_tt_eq_zero ρ D (show n - 1 ≠ 1 by omega), rank_zero, rank_zero]
    simp
  · unfold resDimAt
    rw [card_ttDeg_one, r1, resColsAt_tt_eq_zero ρ D (show (1 : ℤ) - 1 ≠ 1 by norm_num),
      rank_zero]
    push_cast; ring
  · unfold resDimAt
    rw [card_ttDeg_two, resColsAt_tt_eq_zero ρ D (show (2 : ℤ) ≠ 1 by norm_num),
      show (2 : ℤ) - 1 = 1 by norm_num, r1, rank_zero]
    push_cast; ring

end ZInQ.Contrib.CloudB3RC53.BaseZeroEndToEnd
